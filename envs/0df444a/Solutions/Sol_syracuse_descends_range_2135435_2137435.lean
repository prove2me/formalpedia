-- Prove2me | solution 1 for syracuse_descends_range_2135435_2137435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:11.684798+00:00
-- url     : https://prove2.me/submissions/ca9834f7-1e2d-40dd-a420-c1d620605771

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

theorem B2402365 : Blo 2135435 2402365 := bbase (se 3 (by rfl) ⟨450443, by rfl⟩ : syracuseStep 2402365 = 900887) (by norm_num)
theorem B3203153 : Blo 2135435 3203153 := bstep (se 2 (by rfl) ⟨1201182, by rfl⟩ : syracuseStep 3203153 = 2402365) B2402365
theorem B2135435 : Blo 2135435 2135435 := bstep (se 1 (by rfl) ⟨1601576, by rfl⟩ : syracuseStep 2135435 = 3203153) B3203153
theorem B7207109 : Blo 2135435 7207109 := bbase (se 4 (by rfl) ⟨675666, by rfl⟩ : syracuseStep 7207109 = 1351333) (by norm_num)
theorem B4804739 : Blo 2135435 4804739 := bstep (se 1 (by rfl) ⟨3603554, by rfl⟩ : syracuseStep 4804739 = 7207109) B7207109
theorem B3203159 : Blo 2135435 3203159 := bstep (se 1 (by rfl) ⟨2402369, by rfl⟩ : syracuseStep 3203159 = 4804739) B4804739
theorem B2135439 : Blo 2135435 2135439 := bstep (se 1 (by rfl) ⟨1601579, by rfl⟩ : syracuseStep 2135439 = 3203159) B3203159
theorem B3203165 : Blo 2135435 3203165 := bbase (se 3 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 3203165 = 1201187) (by norm_num)
theorem B2135443 : Blo 2135435 2135443 := bstep (se 1 (by rfl) ⟨1601582, by rfl⟩ : syracuseStep 2135443 = 3203165) B3203165
theorem B4804757 : Blo 2135435 4804757 := bbase (se 6 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 4804757 = 225223) (by norm_num)
theorem B3203171 : Blo 2135435 3203171 := bstep (se 1 (by rfl) ⟨2402378, by rfl⟩ : syracuseStep 3203171 = 4804757) B4804757
theorem B2135447 : Blo 2135435 2135447 := bstep (se 1 (by rfl) ⟨1601585, by rfl⟩ : syracuseStep 2135447 = 3203171) B3203171
theorem B3040517 : Blo 2135435 3040517 := bbase (se 4 (by rfl) ⟨285048, by rfl⟩ : syracuseStep 3040517 = 570097) (by norm_num)
theorem B8108045 : Blo 2135435 8108045 := bstep (se 3 (by rfl) ⟨1520258, by rfl⟩ : syracuseStep 8108045 = 3040517) B3040517
theorem B5405363 : Blo 2135435 5405363 := bstep (se 1 (by rfl) ⟨4054022, by rfl⟩ : syracuseStep 5405363 = 8108045) B8108045
theorem B3603575 : Blo 2135435 3603575 := bstep (se 1 (by rfl) ⟨2702681, by rfl⟩ : syracuseStep 3603575 = 5405363) B5405363
theorem B2402383 : Blo 2135435 2402383 := bstep (se 1 (by rfl) ⟨1801787, by rfl⟩ : syracuseStep 2402383 = 3603575) B3603575
theorem B3203177 : Blo 2135435 3203177 := bstep (se 2 (by rfl) ⟨1201191, by rfl⟩ : syracuseStep 3203177 = 2402383) B2402383
theorem B2135451 : Blo 2135435 2135451 := bstep (se 1 (by rfl) ⟨1601588, by rfl⟩ : syracuseStep 2135451 = 3203177) B3203177
theorem B4109341 : Blo 2135435 4109341 := bbase (se 3 (by rfl) ⟨770501, by rfl⟩ : syracuseStep 4109341 = 1541003) (by norm_num)
theorem B5479121 : Blo 2135435 5479121 := bstep (se 2 (by rfl) ⟨2054670, by rfl⟩ : syracuseStep 5479121 = 4109341) B4109341
theorem B14610989 : Blo 2135435 14610989 := bstep (se 3 (by rfl) ⟨2739560, by rfl⟩ : syracuseStep 14610989 = 5479121) B5479121
theorem B9740659 : Blo 2135435 9740659 := bstep (se 1 (by rfl) ⟨7305494, by rfl⟩ : syracuseStep 9740659 = 14610989) B14610989
theorem B12987545 : Blo 2135435 12987545 := bstep (se 2 (by rfl) ⟨4870329, by rfl⟩ : syracuseStep 12987545 = 9740659) B9740659
theorem B34633453 : Blo 2135435 34633453 := bstep (se 3 (by rfl) ⟨6493772, by rfl⟩ : syracuseStep 34633453 = 12987545) B12987545
theorem B46177937 : Blo 2135435 46177937 := bstep (se 2 (by rfl) ⟨17316726, by rfl⟩ : syracuseStep 46177937 = 34633453) B34633453
theorem B30785291 : Blo 2135435 30785291 := bstep (se 1 (by rfl) ⟨23088968, by rfl⟩ : syracuseStep 30785291 = 46177937) B46177937
theorem B20523527 : Blo 2135435 20523527 := bstep (se 1 (by rfl) ⟨15392645, by rfl⟩ : syracuseStep 20523527 = 30785291) B30785291
theorem B13682351 : Blo 2135435 13682351 := bstep (se 1 (by rfl) ⟨10261763, by rfl⟩ : syracuseStep 13682351 = 20523527) B20523527
theorem B9121567 : Blo 2135435 9121567 := bstep (se 1 (by rfl) ⟨6841175, by rfl⟩ : syracuseStep 9121567 = 13682351) B13682351
theorem B12162089 : Blo 2135435 12162089 := bstep (se 2 (by rfl) ⟨4560783, by rfl⟩ : syracuseStep 12162089 = 9121567) B9121567
theorem B8108059 : Blo 2135435 8108059 := bstep (se 1 (by rfl) ⟨6081044, by rfl⟩ : syracuseStep 8108059 = 12162089) B12162089
theorem B10810745 : Blo 2135435 10810745 := bstep (se 2 (by rfl) ⟨4054029, by rfl⟩ : syracuseStep 10810745 = 8108059) B8108059
theorem B7207163 : Blo 2135435 7207163 := bstep (se 1 (by rfl) ⟨5405372, by rfl⟩ : syracuseStep 7207163 = 10810745) B10810745
theorem B4804775 : Blo 2135435 4804775 := bstep (se 1 (by rfl) ⟨3603581, by rfl⟩ : syracuseStep 4804775 = 7207163) B7207163
theorem B3203183 : Blo 2135435 3203183 := bstep (se 1 (by rfl) ⟨2402387, by rfl⟩ : syracuseStep 3203183 = 4804775) B4804775
theorem B2135455 : Blo 2135435 2135455 := bstep (se 1 (by rfl) ⟨1601591, by rfl⟩ : syracuseStep 2135455 = 3203183) B3203183
theorem B3203189 : Blo 2135435 3203189 := bbase (se 5 (by rfl) ⟨150149, by rfl⟩ : syracuseStep 3203189 = 300299) (by norm_num)
theorem B2135459 : Blo 2135435 2135459 := bstep (se 1 (by rfl) ⟨1601594, by rfl⟩ : syracuseStep 2135459 = 3203189) B3203189
theorem B4054045 : Blo 2135435 4054045 := bbase (se 3 (by rfl) ⟨760133, by rfl⟩ : syracuseStep 4054045 = 1520267) (by norm_num)
theorem B5405393 : Blo 2135435 5405393 := bstep (se 2 (by rfl) ⟨2027022, by rfl⟩ : syracuseStep 5405393 = 4054045) B4054045
theorem B3603595 : Blo 2135435 3603595 := bstep (se 1 (by rfl) ⟨2702696, by rfl⟩ : syracuseStep 3603595 = 5405393) B5405393
theorem B4804793 : Blo 2135435 4804793 := bstep (se 2 (by rfl) ⟨1801797, by rfl⟩ : syracuseStep 4804793 = 3603595) B3603595
theorem B3203195 : Blo 2135435 3203195 := bstep (se 1 (by rfl) ⟨2402396, by rfl⟩ : syracuseStep 3203195 = 4804793) B4804793
theorem B2135463 : Blo 2135435 2135463 := bstep (se 1 (by rfl) ⟨1601597, by rfl⟩ : syracuseStep 2135463 = 3203195) B3203195
theorem B2402401 : Blo 2135435 2402401 := bbase (se 2 (by rfl) ⟨900900, by rfl⟩ : syracuseStep 2402401 = 1801801) (by norm_num)
theorem B3203201 : Blo 2135435 3203201 := bstep (se 2 (by rfl) ⟨1201200, by rfl⟩ : syracuseStep 3203201 = 2402401) B2402401
theorem B2135467 : Blo 2135435 2135467 := bstep (se 1 (by rfl) ⟨1601600, by rfl⟩ : syracuseStep 2135467 = 3203201) B3203201
theorem B5405413 : Blo 2135435 5405413 := bbase (se 4 (by rfl) ⟨506757, by rfl⟩ : syracuseStep 5405413 = 1013515) (by norm_num)
theorem B7207217 : Blo 2135435 7207217 := bstep (se 2 (by rfl) ⟨2702706, by rfl⟩ : syracuseStep 7207217 = 5405413) B5405413
theorem B4804811 : Blo 2135435 4804811 := bstep (se 1 (by rfl) ⟨3603608, by rfl⟩ : syracuseStep 4804811 = 7207217) B7207217
theorem B3203207 : Blo 2135435 3203207 := bstep (se 1 (by rfl) ⟨2402405, by rfl⟩ : syracuseStep 3203207 = 4804811) B4804811
theorem B2135471 : Blo 2135435 2135471 := bstep (se 1 (by rfl) ⟨1601603, by rfl⟩ : syracuseStep 2135471 = 3203207) B3203207
theorem B3203213 : Blo 2135435 3203213 := bbase (se 3 (by rfl) ⟨600602, by rfl⟩ : syracuseStep 3203213 = 1201205) (by norm_num)
theorem B2135475 : Blo 2135435 2135475 := bstep (se 1 (by rfl) ⟨1601606, by rfl⟩ : syracuseStep 2135475 = 3203213) B3203213
theorem B4804829 : Blo 2135435 4804829 := bbase (se 3 (by rfl) ⟨900905, by rfl⟩ : syracuseStep 4804829 = 1801811) (by norm_num)
theorem B3203219 : Blo 2135435 3203219 := bstep (se 1 (by rfl) ⟨2402414, by rfl⟩ : syracuseStep 3203219 = 4804829) B4804829
theorem B2135479 : Blo 2135435 2135479 := bstep (se 1 (by rfl) ⟨1601609, by rfl⟩ : syracuseStep 2135479 = 3203219) B3203219
theorem B3603629 : Blo 2135435 3603629 := bbase (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) (by norm_num)
theorem B2402419 : Blo 2135435 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B3203225 : Blo 2135435 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B2135483 : Blo 2135435 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B10401925 : Blo 2135435 10401925 := bbase (se 4 (by rfl) ⟨975180, by rfl⟩ : syracuseStep 10401925 = 1950361) (by norm_num)
theorem B13869233 : Blo 2135435 13869233 := bstep (se 2 (by rfl) ⟨5200962, by rfl⟩ : syracuseStep 13869233 = 10401925) B10401925
theorem B9246155 : Blo 2135435 9246155 := bstep (se 1 (by rfl) ⟨6934616, by rfl⟩ : syracuseStep 9246155 = 13869233) B13869233
theorem B24656413 : Blo 2135435 24656413 := bstep (se 3 (by rfl) ⟨4623077, by rfl⟩ : syracuseStep 24656413 = 9246155) B9246155
theorem B32875217 : Blo 2135435 32875217 := bstep (se 2 (by rfl) ⟨12328206, by rfl⟩ : syracuseStep 32875217 = 24656413) B24656413
theorem B21916811 : Blo 2135435 21916811 := bstep (se 1 (by rfl) ⟨16437608, by rfl⟩ : syracuseStep 21916811 = 32875217) B32875217
theorem B14611207 : Blo 2135435 14611207 := bstep (se 1 (by rfl) ⟨10958405, by rfl⟩ : syracuseStep 14611207 = 21916811) B21916811
theorem B19481609 : Blo 2135435 19481609 := bstep (se 2 (by rfl) ⟨7305603, by rfl⟩ : syracuseStep 19481609 = 14611207) B14611207
theorem B12987739 : Blo 2135435 12987739 := bstep (se 1 (by rfl) ⟨9740804, by rfl⟩ : syracuseStep 12987739 = 19481609) B19481609
theorem B17316985 : Blo 2135435 17316985 := bstep (se 2 (by rfl) ⟨6493869, by rfl⟩ : syracuseStep 17316985 = 12987739) B12987739
theorem B23089313 : Blo 2135435 23089313 := bstep (se 2 (by rfl) ⟨8658492, by rfl⟩ : syracuseStep 23089313 = 17316985) B17316985
theorem B61571501 : Blo 2135435 61571501 := bstep (se 3 (by rfl) ⟨11544656, by rfl⟩ : syracuseStep 61571501 = 23089313) B23089313
theorem B41047667 : Blo 2135435 41047667 := bstep (se 1 (by rfl) ⟨30785750, by rfl⟩ : syracuseStep 41047667 = 61571501) B61571501
theorem B27365111 : Blo 2135435 27365111 := bstep (se 1 (by rfl) ⟨20523833, by rfl⟩ : syracuseStep 27365111 = 41047667) B41047667
theorem B18243407 : Blo 2135435 18243407 := bstep (se 1 (by rfl) ⟨13682555, by rfl⟩ : syracuseStep 18243407 = 27365111) B27365111
theorem B12162271 : Blo 2135435 12162271 := bstep (se 1 (by rfl) ⟨9121703, by rfl⟩ : syracuseStep 12162271 = 18243407) B18243407
theorem B16216361 : Blo 2135435 16216361 := bstep (se 2 (by rfl) ⟨6081135, by rfl⟩ : syracuseStep 16216361 = 12162271) B12162271
theorem B10810907 : Blo 2135435 10810907 := bstep (se 1 (by rfl) ⟨8108180, by rfl⟩ : syracuseStep 10810907 = 16216361) B16216361
theorem B7207271 : Blo 2135435 7207271 := bstep (se 1 (by rfl) ⟨5405453, by rfl⟩ : syracuseStep 7207271 = 10810907) B10810907
theorem B4804847 : Blo 2135435 4804847 := bstep (se 1 (by rfl) ⟨3603635, by rfl⟩ : syracuseStep 4804847 = 7207271) B7207271
theorem B3203231 : Blo 2135435 3203231 := bstep (se 1 (by rfl) ⟨2402423, by rfl⟩ : syracuseStep 3203231 = 4804847) B4804847
theorem B2135487 : Blo 2135435 2135487 := bstep (se 1 (by rfl) ⟨1601615, by rfl⟩ : syracuseStep 2135487 = 3203231) B3203231
theorem B3203237 : Blo 2135435 3203237 := bbase (se 4 (by rfl) ⟨300303, by rfl⟩ : syracuseStep 3203237 = 600607) (by norm_num)
theorem B2135491 : Blo 2135435 2135491 := bstep (se 1 (by rfl) ⟨1601618, by rfl⟩ : syracuseStep 2135491 = 3203237) B3203237
theorem B2702737 : Blo 2135435 2702737 := bbase (se 2 (by rfl) ⟨1013526, by rfl⟩ : syracuseStep 2702737 = 2027053) (by norm_num)
theorem B3603649 : Blo 2135435 3603649 := bstep (se 2 (by rfl) ⟨1351368, by rfl⟩ : syracuseStep 3603649 = 2702737) B2702737
theorem B4804865 : Blo 2135435 4804865 := bstep (se 2 (by rfl) ⟨1801824, by rfl⟩ : syracuseStep 4804865 = 3603649) B3603649
theorem B3203243 : Blo 2135435 3203243 := bstep (se 1 (by rfl) ⟨2402432, by rfl⟩ : syracuseStep 3203243 = 4804865) B4804865
theorem B2135495 : Blo 2135435 2135495 := bstep (se 1 (by rfl) ⟨1601621, by rfl⟩ : syracuseStep 2135495 = 3203243) B3203243
theorem B2402437 : Blo 2135435 2402437 := bbase (se 4 (by rfl) ⟨225228, by rfl⟩ : syracuseStep 2402437 = 450457) (by norm_num)
theorem B3203249 : Blo 2135435 3203249 := bstep (se 2 (by rfl) ⟨1201218, by rfl⟩ : syracuseStep 3203249 = 2402437) B2402437
theorem B2135499 : Blo 2135435 2135499 := bstep (se 1 (by rfl) ⟨1601624, by rfl⟩ : syracuseStep 2135499 = 3203249) B3203249
theorem B2435221 : Blo 2135435 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B3246961 : Blo 2135435 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B4329281 : Blo 2135435 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2886187 : Blo 2135435 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B3848249 : Blo 2135435 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B10261997 : Blo 2135435 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B6841331 : Blo 2135435 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B4560887 : Blo 2135435 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B3040591 : Blo 2135435 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B4054121 : Blo 2135435 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B2702747 : Blo 2135435 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B7207325 : Blo 2135435 7207325 := bstep (se 3 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 7207325 = 2702747) B2702747
theorem B4804883 : Blo 2135435 4804883 := bstep (se 1 (by rfl) ⟨3603662, by rfl⟩ : syracuseStep 4804883 = 7207325) B7207325
theorem B3203255 : Blo 2135435 3203255 := bstep (se 1 (by rfl) ⟨2402441, by rfl⟩ : syracuseStep 3203255 = 4804883) B4804883
theorem B2135503 : Blo 2135435 2135503 := bstep (se 1 (by rfl) ⟨1601627, by rfl⟩ : syracuseStep 2135503 = 3203255) B3203255
theorem B3203261 : Blo 2135435 3203261 := bbase (se 3 (by rfl) ⟨600611, by rfl⟩ : syracuseStep 3203261 = 1201223) (by norm_num)
theorem B2135507 : Blo 2135435 2135507 := bstep (se 1 (by rfl) ⟨1601630, by rfl⟩ : syracuseStep 2135507 = 3203261) B3203261
theorem B4804901 : Blo 2135435 4804901 := bbase (se 4 (by rfl) ⟨450459, by rfl⟩ : syracuseStep 4804901 = 900919) (by norm_num)
theorem B3203267 : Blo 2135435 3203267 := bstep (se 1 (by rfl) ⟨2402450, by rfl⟩ : syracuseStep 3203267 = 4804901) B4804901
theorem B2135511 : Blo 2135435 2135511 := bstep (se 1 (by rfl) ⟨1601633, by rfl⟩ : syracuseStep 2135511 = 3203267) B3203267
theorem B5405525 : Blo 2135435 5405525 := bbase (se 9 (by rfl) ⟨15836, by rfl⟩ : syracuseStep 5405525 = 31673) (by norm_num)
theorem B3603683 : Blo 2135435 3603683 := bstep (se 1 (by rfl) ⟨2702762, by rfl⟩ : syracuseStep 3603683 = 5405525) B5405525
theorem B2402455 : Blo 2135435 2402455 := bstep (se 1 (by rfl) ⟨1801841, by rfl⟩ : syracuseStep 2402455 = 3603683) B3603683
theorem B3203273 : Blo 2135435 3203273 := bstep (se 2 (by rfl) ⟨1201227, by rfl⟩ : syracuseStep 3203273 = 2402455) B2402455
theorem B2135515 : Blo 2135435 2135515 := bstep (se 1 (by rfl) ⟨1601636, by rfl⟩ : syracuseStep 2135515 = 3203273) B3203273
theorem B6841381 : Blo 2135435 6841381 := bbase (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) (by norm_num)
theorem B9121841 : Blo 2135435 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B6081227 : Blo 2135435 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B4054151 : Blo 2135435 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B10811069 : Blo 2135435 10811069 := bstep (se 3 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 10811069 = 4054151) B4054151
theorem B7207379 : Blo 2135435 7207379 := bstep (se 1 (by rfl) ⟨5405534, by rfl⟩ : syracuseStep 7207379 = 10811069) B10811069
theorem B4804919 : Blo 2135435 4804919 := bstep (se 1 (by rfl) ⟨3603689, by rfl⟩ : syracuseStep 4804919 = 7207379) B7207379
theorem B3203279 : Blo 2135435 3203279 := bstep (se 1 (by rfl) ⟨2402459, by rfl⟩ : syracuseStep 3203279 = 4804919) B4804919
theorem B2135519 : Blo 2135435 2135519 := bstep (se 1 (by rfl) ⟨1601639, by rfl⟩ : syracuseStep 2135519 = 3203279) B3203279
theorem B3203285 : Blo 2135435 3203285 := bbase (se 7 (by rfl) ⟨37538, by rfl⟩ : syracuseStep 3203285 = 75077) (by norm_num)
theorem B2135523 : Blo 2135435 2135523 := bstep (se 1 (by rfl) ⟨1601642, by rfl⟩ : syracuseStep 2135523 = 3203285) B3203285
theorem B2280469 : Blo 2135435 2280469 := bbase (se 6 (by rfl) ⟨53448, by rfl⟩ : syracuseStep 2280469 = 106897) (by norm_num)
theorem B3040625 : Blo 2135435 3040625 := bstep (se 2 (by rfl) ⟨1140234, by rfl⟩ : syracuseStep 3040625 = 2280469) B2280469
theorem B8108333 : Blo 2135435 8108333 := bstep (se 3 (by rfl) ⟨1520312, by rfl⟩ : syracuseStep 8108333 = 3040625) B3040625
theorem B5405555 : Blo 2135435 5405555 := bstep (se 1 (by rfl) ⟨4054166, by rfl⟩ : syracuseStep 5405555 = 8108333) B8108333
theorem B3603703 : Blo 2135435 3603703 := bstep (se 1 (by rfl) ⟨2702777, by rfl⟩ : syracuseStep 3603703 = 5405555) B5405555
theorem B4804937 : Blo 2135435 4804937 := bstep (se 2 (by rfl) ⟨1801851, by rfl⟩ : syracuseStep 4804937 = 3603703) B3603703
theorem B3203291 : Blo 2135435 3203291 := bstep (se 1 (by rfl) ⟨2402468, by rfl⟩ : syracuseStep 3203291 = 4804937) B4804937
theorem B2135527 : Blo 2135435 2135527 := bstep (se 1 (by rfl) ⟨1601645, by rfl⟩ : syracuseStep 2135527 = 3203291) B3203291
theorem B2402473 : Blo 2135435 2402473 := bbase (se 2 (by rfl) ⟨900927, by rfl⟩ : syracuseStep 2402473 = 1801855) (by norm_num)
theorem B3203297 : Blo 2135435 3203297 := bstep (se 2 (by rfl) ⟨1201236, by rfl⟩ : syracuseStep 3203297 = 2402473) B2402473
theorem B2135531 : Blo 2135435 2135531 := bstep (se 1 (by rfl) ⟨1601648, by rfl⟩ : syracuseStep 2135531 = 3203297) B3203297
theorem B9121909 : Blo 2135435 9121909 := bbase (se 5 (by rfl) ⟨427589, by rfl⟩ : syracuseStep 9121909 = 855179) (by norm_num)
theorem B12162545 : Blo 2135435 12162545 := bstep (se 2 (by rfl) ⟨4560954, by rfl⟩ : syracuseStep 12162545 = 9121909) B9121909
theorem B8108363 : Blo 2135435 8108363 := bstep (se 1 (by rfl) ⟨6081272, by rfl⟩ : syracuseStep 8108363 = 12162545) B12162545
theorem B5405575 : Blo 2135435 5405575 := bstep (se 1 (by rfl) ⟨4054181, by rfl⟩ : syracuseStep 5405575 = 8108363) B8108363
theorem B7207433 : Blo 2135435 7207433 := bstep (se 2 (by rfl) ⟨2702787, by rfl⟩ : syracuseStep 7207433 = 5405575) B5405575
theorem B4804955 : Blo 2135435 4804955 := bstep (se 1 (by rfl) ⟨3603716, by rfl⟩ : syracuseStep 4804955 = 7207433) B7207433
theorem B3203303 : Blo 2135435 3203303 := bstep (se 1 (by rfl) ⟨2402477, by rfl⟩ : syracuseStep 3203303 = 4804955) B4804955
theorem B2135535 : Blo 2135435 2135535 := bstep (se 1 (by rfl) ⟨1601651, by rfl⟩ : syracuseStep 2135535 = 3203303) B3203303
theorem B3203309 : Blo 2135435 3203309 := bbase (se 3 (by rfl) ⟨600620, by rfl⟩ : syracuseStep 3203309 = 1201241) (by norm_num)
theorem B2135539 : Blo 2135435 2135539 := bstep (se 1 (by rfl) ⟨1601654, by rfl⟩ : syracuseStep 2135539 = 3203309) B3203309
theorem B4804973 : Blo 2135435 4804973 := bbase (se 3 (by rfl) ⟨900932, by rfl⟩ : syracuseStep 4804973 = 1801865) (by norm_num)
theorem B3203315 : Blo 2135435 3203315 := bstep (se 1 (by rfl) ⟨2402486, by rfl⟩ : syracuseStep 3203315 = 4804973) B4804973
theorem B2135543 : Blo 2135435 2135543 := bstep (se 1 (by rfl) ⟨1601657, by rfl⟩ : syracuseStep 2135543 = 3203315) B3203315
theorem B4054205 : Blo 2135435 4054205 := bbase (se 3 (by rfl) ⟨760163, by rfl⟩ : syracuseStep 4054205 = 1520327) (by norm_num)
theorem B2702803 : Blo 2135435 2702803 := bstep (se 1 (by rfl) ⟨2027102, by rfl⟩ : syracuseStep 2702803 = 4054205) B4054205
theorem B3603737 : Blo 2135435 3603737 := bstep (se 2 (by rfl) ⟨1351401, by rfl⟩ : syracuseStep 3603737 = 2702803) B2702803
theorem B2402491 : Blo 2135435 2402491 := bstep (se 1 (by rfl) ⟨1801868, by rfl⟩ : syracuseStep 2402491 = 3603737) B3603737
theorem B3203321 : Blo 2135435 3203321 := bstep (se 2 (by rfl) ⟨1201245, by rfl⟩ : syracuseStep 3203321 = 2402491) B2402491
theorem B2135547 : Blo 2135435 2135547 := bstep (se 1 (by rfl) ⟨1601660, by rfl⟩ : syracuseStep 2135547 = 3203321) B3203321
theorem B54731861 : Blo 2135435 54731861 := bbase (se 8 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 54731861 = 641389) (by norm_num)
theorem B36487907 : Blo 2135435 36487907 := bstep (se 1 (by rfl) ⟨27365930, by rfl⟩ : syracuseStep 36487907 = 54731861) B54731861
theorem B24325271 : Blo 2135435 24325271 := bstep (se 1 (by rfl) ⟨18243953, by rfl⟩ : syracuseStep 24325271 = 36487907) B36487907
theorem B16216847 : Blo 2135435 16216847 := bstep (se 1 (by rfl) ⟨12162635, by rfl⟩ : syracuseStep 16216847 = 24325271) B24325271
theorem B10811231 : Blo 2135435 10811231 := bstep (se 1 (by rfl) ⟨8108423, by rfl⟩ : syracuseStep 10811231 = 16216847) B16216847
theorem B7207487 : Blo 2135435 7207487 := bstep (se 1 (by rfl) ⟨5405615, by rfl⟩ : syracuseStep 7207487 = 10811231) B10811231
theorem B4804991 : Blo 2135435 4804991 := bstep (se 1 (by rfl) ⟨3603743, by rfl⟩ : syracuseStep 4804991 = 7207487) B7207487
theorem B3203327 : Blo 2135435 3203327 := bstep (se 1 (by rfl) ⟨2402495, by rfl⟩ : syracuseStep 3203327 = 4804991) B4804991
theorem B2135551 : Blo 2135435 2135551 := bstep (se 1 (by rfl) ⟨1601663, by rfl⟩ : syracuseStep 2135551 = 3203327) B3203327
theorem B3203333 : Blo 2135435 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B2135555 : Blo 2135435 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B3603757 : Blo 2135435 3603757 := bbase (se 3 (by rfl) ⟨675704, by rfl⟩ : syracuseStep 3603757 = 1351409) (by norm_num)
theorem B4805009 : Blo 2135435 4805009 := bstep (se 2 (by rfl) ⟨1801878, by rfl⟩ : syracuseStep 4805009 = 3603757) B3603757
theorem B3203339 : Blo 2135435 3203339 := bstep (se 1 (by rfl) ⟨2402504, by rfl⟩ : syracuseStep 3203339 = 4805009) B4805009
theorem B2135559 : Blo 2135435 2135559 := bstep (se 1 (by rfl) ⟨1601669, by rfl⟩ : syracuseStep 2135559 = 3203339) B3203339
theorem B2402509 : Blo 2135435 2402509 := bbase (se 3 (by rfl) ⟨450470, by rfl⟩ : syracuseStep 2402509 = 900941) (by norm_num)
theorem B3203345 : Blo 2135435 3203345 := bstep (se 2 (by rfl) ⟨1201254, by rfl⟩ : syracuseStep 3203345 = 2402509) B2402509
theorem B2135563 : Blo 2135435 2135563 := bstep (se 1 (by rfl) ⟨1601672, by rfl⟩ : syracuseStep 2135563 = 3203345) B3203345
theorem B7207541 : Blo 2135435 7207541 := bbase (se 5 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 7207541 = 675707) (by norm_num)
theorem B4805027 : Blo 2135435 4805027 := bstep (se 1 (by rfl) ⟨3603770, by rfl⟩ : syracuseStep 4805027 = 7207541) B7207541
theorem B3203351 : Blo 2135435 3203351 := bstep (se 1 (by rfl) ⟨2402513, by rfl⟩ : syracuseStep 3203351 = 4805027) B4805027
theorem B2135567 : Blo 2135435 2135567 := bstep (se 1 (by rfl) ⟨1601675, by rfl⟩ : syracuseStep 2135567 = 3203351) B3203351
theorem B3203357 : Blo 2135435 3203357 := bbase (se 3 (by rfl) ⟨600629, by rfl⟩ : syracuseStep 3203357 = 1201259) (by norm_num)
theorem B2135571 : Blo 2135435 2135571 := bstep (se 1 (by rfl) ⟨1601678, by rfl⟩ : syracuseStep 2135571 = 3203357) B3203357
theorem B4805045 : Blo 2135435 4805045 := bbase (se 5 (by rfl) ⟨225236, by rfl⟩ : syracuseStep 4805045 = 450473) (by norm_num)
theorem B3203363 : Blo 2135435 3203363 := bstep (se 1 (by rfl) ⟨2402522, by rfl⟩ : syracuseStep 3203363 = 4805045) B4805045
theorem B2135575 : Blo 2135435 2135575 := bstep (se 1 (by rfl) ⟨1601681, by rfl⟩ : syracuseStep 2135575 = 3203363) B3203363
theorem B5131181 : Blo 2135435 5131181 := bbase (se 3 (by rfl) ⟨962096, by rfl⟩ : syracuseStep 5131181 = 1924193) (by norm_num)
theorem B3420787 : Blo 2135435 3420787 := bstep (se 1 (by rfl) ⟨2565590, by rfl⟩ : syracuseStep 3420787 = 5131181) B5131181
theorem B4561049 : Blo 2135435 4561049 := bstep (se 2 (by rfl) ⟨1710393, by rfl⟩ : syracuseStep 4561049 = 3420787) B3420787
theorem B12162797 : Blo 2135435 12162797 := bstep (se 3 (by rfl) ⟨2280524, by rfl⟩ : syracuseStep 12162797 = 4561049) B4561049
theorem B8108531 : Blo 2135435 8108531 := bstep (se 1 (by rfl) ⟨6081398, by rfl⟩ : syracuseStep 8108531 = 12162797) B12162797
theorem B5405687 : Blo 2135435 5405687 := bstep (se 1 (by rfl) ⟨4054265, by rfl⟩ : syracuseStep 5405687 = 8108531) B8108531
theorem B3603791 : Blo 2135435 3603791 := bstep (se 1 (by rfl) ⟨2702843, by rfl⟩ : syracuseStep 3603791 = 5405687) B5405687
theorem B2402527 : Blo 2135435 2402527 := bstep (se 1 (by rfl) ⟨1801895, by rfl⟩ : syracuseStep 2402527 = 3603791) B3603791
theorem B3203369 : Blo 2135435 3203369 := bstep (se 2 (by rfl) ⟨1201263, by rfl⟩ : syracuseStep 3203369 = 2402527) B2402527
theorem B2135579 : Blo 2135435 2135579 := bstep (se 1 (by rfl) ⟨1601684, by rfl⟩ : syracuseStep 2135579 = 3203369) B3203369
theorem B6494165 : Blo 2135435 6494165 := bbase (se 7 (by rfl) ⟨76103, by rfl⟩ : syracuseStep 6494165 = 152207) (by norm_num)
theorem B4329443 : Blo 2135435 4329443 := bstep (se 1 (by rfl) ⟨3247082, by rfl⟩ : syracuseStep 4329443 = 6494165) B6494165
theorem B2886295 : Blo 2135435 2886295 := bstep (se 1 (by rfl) ⟨2164721, by rfl⟩ : syracuseStep 2886295 = 4329443) B4329443
theorem B3848393 : Blo 2135435 3848393 := bstep (se 2 (by rfl) ⟨1443147, by rfl⟩ : syracuseStep 3848393 = 2886295) B2886295
theorem B2565595 : Blo 2135435 2565595 := bstep (se 1 (by rfl) ⟨1924196, by rfl⟩ : syracuseStep 2565595 = 3848393) B3848393
theorem B3420793 : Blo 2135435 3420793 := bstep (se 2 (by rfl) ⟨1282797, by rfl⟩ : syracuseStep 3420793 = 2565595) B2565595
theorem B4561057 : Blo 2135435 4561057 := bstep (se 2 (by rfl) ⟨1710396, by rfl⟩ : syracuseStep 4561057 = 3420793) B3420793
theorem B6081409 : Blo 2135435 6081409 := bstep (se 2 (by rfl) ⟨2280528, by rfl⟩ : syracuseStep 6081409 = 4561057) B4561057
theorem B8108545 : Blo 2135435 8108545 := bstep (se 2 (by rfl) ⟨3040704, by rfl⟩ : syracuseStep 8108545 = 6081409) B6081409
theorem B10811393 : Blo 2135435 10811393 := bstep (se 2 (by rfl) ⟨4054272, by rfl⟩ : syracuseStep 10811393 = 8108545) B8108545
theorem B7207595 : Blo 2135435 7207595 := bstep (se 1 (by rfl) ⟨5405696, by rfl⟩ : syracuseStep 7207595 = 10811393) B10811393
theorem B4805063 : Blo 2135435 4805063 := bstep (se 1 (by rfl) ⟨3603797, by rfl⟩ : syracuseStep 4805063 = 7207595) B7207595
theorem B3203375 : Blo 2135435 3203375 := bstep (se 1 (by rfl) ⟨2402531, by rfl⟩ : syracuseStep 3203375 = 4805063) B4805063
theorem B2135583 : Blo 2135435 2135583 := bstep (se 1 (by rfl) ⟨1601687, by rfl⟩ : syracuseStep 2135583 = 3203375) B3203375
theorem B3203381 : Blo 2135435 3203381 := bbase (se 5 (by rfl) ⟨150158, by rfl⟩ : syracuseStep 3203381 = 300317) (by norm_num)
theorem B2135587 : Blo 2135435 2135587 := bstep (se 1 (by rfl) ⟨1601690, by rfl⟩ : syracuseStep 2135587 = 3203381) B3203381
theorem B5405717 : Blo 2135435 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B3603811 : Blo 2135435 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B4805081 : Blo 2135435 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B3203387 : Blo 2135435 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B2135591 : Blo 2135435 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B2402545 : Blo 2135435 2402545 := bbase (se 2 (by rfl) ⟨900954, by rfl⟩ : syracuseStep 2402545 = 1801909) (by norm_num)
theorem B3203393 : Blo 2135435 3203393 := bstep (se 2 (by rfl) ⟨1201272, by rfl⟩ : syracuseStep 3203393 = 2402545) B2402545
theorem B2135595 : Blo 2135435 2135595 := bstep (se 1 (by rfl) ⟨1601696, by rfl⟩ : syracuseStep 2135595 = 3203393) B3203393
theorem B15393685 : Blo 2135435 15393685 := bbase (se 6 (by rfl) ⟨360789, by rfl⟩ : syracuseStep 15393685 = 721579) (by norm_num)
theorem B20524913 : Blo 2135435 20524913 := bstep (se 2 (by rfl) ⟨7696842, by rfl⟩ : syracuseStep 20524913 = 15393685) B15393685
theorem B13683275 : Blo 2135435 13683275 := bstep (se 1 (by rfl) ⟨10262456, by rfl⟩ : syracuseStep 13683275 = 20524913) B20524913
theorem B9122183 : Blo 2135435 9122183 := bstep (se 1 (by rfl) ⟨6841637, by rfl⟩ : syracuseStep 9122183 = 13683275) B13683275
theorem B6081455 : Blo 2135435 6081455 := bstep (se 1 (by rfl) ⟨4561091, by rfl⟩ : syracuseStep 6081455 = 9122183) B9122183
theorem B4054303 : Blo 2135435 4054303 := bstep (se 1 (by rfl) ⟨3040727, by rfl⟩ : syracuseStep 4054303 = 6081455) B6081455
theorem B5405737 : Blo 2135435 5405737 := bstep (se 2 (by rfl) ⟨2027151, by rfl⟩ : syracuseStep 5405737 = 4054303) B4054303
theorem B7207649 : Blo 2135435 7207649 := bstep (se 2 (by rfl) ⟨2702868, by rfl⟩ : syracuseStep 7207649 = 5405737) B5405737
theorem B4805099 : Blo 2135435 4805099 := bstep (se 1 (by rfl) ⟨3603824, by rfl⟩ : syracuseStep 4805099 = 7207649) B7207649
theorem B3203399 : Blo 2135435 3203399 := bstep (se 1 (by rfl) ⟨2402549, by rfl⟩ : syracuseStep 3203399 = 4805099) B4805099
theorem B2135599 : Blo 2135435 2135599 := bstep (se 1 (by rfl) ⟨1601699, by rfl⟩ : syracuseStep 2135599 = 3203399) B3203399
theorem B3203405 : Blo 2135435 3203405 := bbase (se 3 (by rfl) ⟨600638, by rfl⟩ : syracuseStep 3203405 = 1201277) (by norm_num)
theorem B2135603 : Blo 2135435 2135603 := bstep (se 1 (by rfl) ⟨1601702, by rfl⟩ : syracuseStep 2135603 = 3203405) B3203405
theorem B4805117 : Blo 2135435 4805117 := bbase (se 3 (by rfl) ⟨900959, by rfl⟩ : syracuseStep 4805117 = 1801919) (by norm_num)
theorem B3203411 : Blo 2135435 3203411 := bstep (se 1 (by rfl) ⟨2402558, by rfl⟩ : syracuseStep 3203411 = 4805117) B4805117
theorem B2135607 : Blo 2135435 2135607 := bstep (se 1 (by rfl) ⟨1601705, by rfl⟩ : syracuseStep 2135607 = 3203411) B3203411
theorem B3603845 : Blo 2135435 3603845 := bbase (se 4 (by rfl) ⟨337860, by rfl⟩ : syracuseStep 3603845 = 675721) (by norm_num)
theorem B2402563 : Blo 2135435 2402563 := bstep (se 1 (by rfl) ⟨1801922, by rfl⟩ : syracuseStep 2402563 = 3603845) B3603845
theorem B3203417 : Blo 2135435 3203417 := bstep (se 2 (by rfl) ⟨1201281, by rfl⟩ : syracuseStep 3203417 = 2402563) B2402563
theorem B2135611 : Blo 2135435 2135611 := bstep (se 1 (by rfl) ⟨1601708, by rfl⟩ : syracuseStep 2135611 = 3203417) B3203417
theorem B16217333 : Blo 2135435 16217333 := bbase (se 5 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 16217333 = 1520375) (by norm_num)
theorem B10811555 : Blo 2135435 10811555 := bstep (se 1 (by rfl) ⟨8108666, by rfl⟩ : syracuseStep 10811555 = 16217333) B16217333
theorem B7207703 : Blo 2135435 7207703 := bstep (se 1 (by rfl) ⟨5405777, by rfl⟩ : syracuseStep 7207703 = 10811555) B10811555
theorem B4805135 : Blo 2135435 4805135 := bstep (se 1 (by rfl) ⟨3603851, by rfl⟩ : syracuseStep 4805135 = 7207703) B7207703
theorem B3203423 : Blo 2135435 3203423 := bstep (se 1 (by rfl) ⟨2402567, by rfl⟩ : syracuseStep 3203423 = 4805135) B4805135
theorem B2135615 : Blo 2135435 2135615 := bstep (se 1 (by rfl) ⟨1601711, by rfl⟩ : syracuseStep 2135615 = 3203423) B3203423
theorem B3203429 : Blo 2135435 3203429 := bbase (se 4 (by rfl) ⟨300321, by rfl⟩ : syracuseStep 3203429 = 600643) (by norm_num)
theorem B2135619 : Blo 2135435 2135619 := bstep (se 1 (by rfl) ⟨1601714, by rfl⟩ : syracuseStep 2135619 = 3203429) B3203429
theorem B4054349 : Blo 2135435 4054349 := bbase (se 3 (by rfl) ⟨760190, by rfl⟩ : syracuseStep 4054349 = 1520381) (by norm_num)
theorem B2702899 : Blo 2135435 2702899 := bstep (se 1 (by rfl) ⟨2027174, by rfl⟩ : syracuseStep 2702899 = 4054349) B4054349
theorem B3603865 : Blo 2135435 3603865 := bstep (se 2 (by rfl) ⟨1351449, by rfl⟩ : syracuseStep 3603865 = 2702899) B2702899
theorem B4805153 : Blo 2135435 4805153 := bstep (se 2 (by rfl) ⟨1801932, by rfl⟩ : syracuseStep 4805153 = 3603865) B3603865
theorem B3203435 : Blo 2135435 3203435 := bstep (se 1 (by rfl) ⟨2402576, by rfl⟩ : syracuseStep 3203435 = 4805153) B4805153
theorem B2135623 : Blo 2135435 2135623 := bstep (se 1 (by rfl) ⟨1601717, by rfl⟩ : syracuseStep 2135623 = 3203435) B3203435
theorem B2402581 : Blo 2135435 2402581 := bbase (se 6 (by rfl) ⟨56310, by rfl⟩ : syracuseStep 2402581 = 112621) (by norm_num)
theorem B3203441 : Blo 2135435 3203441 := bstep (se 2 (by rfl) ⟨1201290, by rfl⟩ : syracuseStep 3203441 = 2402581) B2402581
theorem B2135627 : Blo 2135435 2135627 := bstep (se 1 (by rfl) ⟨1601720, by rfl⟩ : syracuseStep 2135627 = 3203441) B3203441
theorem B2702909 : Blo 2135435 2702909 := bbase (se 3 (by rfl) ⟨506795, by rfl⟩ : syracuseStep 2702909 = 1013591) (by norm_num)
theorem B7207757 : Blo 2135435 7207757 := bstep (se 3 (by rfl) ⟨1351454, by rfl⟩ : syracuseStep 7207757 = 2702909) B2702909
theorem B4805171 : Blo 2135435 4805171 := bstep (se 1 (by rfl) ⟨3603878, by rfl⟩ : syracuseStep 4805171 = 7207757) B7207757
theorem B3203447 : Blo 2135435 3203447 := bstep (se 1 (by rfl) ⟨2402585, by rfl⟩ : syracuseStep 3203447 = 4805171) B4805171
theorem B2135631 : Blo 2135435 2135631 := bstep (se 1 (by rfl) ⟨1601723, by rfl⟩ : syracuseStep 2135631 = 3203447) B3203447
theorem B3203453 : Blo 2135435 3203453 := bbase (se 3 (by rfl) ⟨600647, by rfl⟩ : syracuseStep 3203453 = 1201295) (by norm_num)
theorem B2135635 : Blo 2135435 2135635 := bstep (se 1 (by rfl) ⟨1601726, by rfl⟩ : syracuseStep 2135635 = 3203453) B3203453
theorem B4805189 : Blo 2135435 4805189 := bbase (se 4 (by rfl) ⟨450486, by rfl⟩ : syracuseStep 4805189 = 900973) (by norm_num)
theorem B3203459 : Blo 2135435 3203459 := bstep (se 1 (by rfl) ⟨2402594, by rfl⟩ : syracuseStep 3203459 = 4805189) B4805189
theorem B2135639 : Blo 2135435 2135639 := bstep (se 1 (by rfl) ⟨1601729, by rfl⟩ : syracuseStep 2135639 = 3203459) B3203459
theorem B2280593 : Blo 2135435 2280593 := bbase (se 2 (by rfl) ⟨855222, by rfl⟩ : syracuseStep 2280593 = 1710445) (by norm_num)
theorem B6081581 : Blo 2135435 6081581 := bstep (se 3 (by rfl) ⟨1140296, by rfl⟩ : syracuseStep 6081581 = 2280593) B2280593
theorem B4054387 : Blo 2135435 4054387 := bstep (se 1 (by rfl) ⟨3040790, by rfl⟩ : syracuseStep 4054387 = 6081581) B6081581
theorem B5405849 : Blo 2135435 5405849 := bstep (se 2 (by rfl) ⟨2027193, by rfl⟩ : syracuseStep 5405849 = 4054387) B4054387
theorem B3603899 : Blo 2135435 3603899 := bstep (se 1 (by rfl) ⟨2702924, by rfl⟩ : syracuseStep 3603899 = 5405849) B5405849
theorem B2402599 : Blo 2135435 2402599 := bstep (se 1 (by rfl) ⟨1801949, by rfl⟩ : syracuseStep 2402599 = 3603899) B3603899
theorem B3203465 : Blo 2135435 3203465 := bstep (se 2 (by rfl) ⟨1201299, by rfl⟩ : syracuseStep 3203465 = 2402599) B2402599
theorem B2135643 : Blo 2135435 2135643 := bstep (se 1 (by rfl) ⟨1601732, by rfl⟩ : syracuseStep 2135643 = 3203465) B3203465
theorem B10811717 : Blo 2135435 10811717 := bbase (se 4 (by rfl) ⟨1013598, by rfl⟩ : syracuseStep 10811717 = 2027197) (by norm_num)
theorem B7207811 : Blo 2135435 7207811 := bstep (se 1 (by rfl) ⟨5405858, by rfl⟩ : syracuseStep 7207811 = 10811717) B10811717
theorem B4805207 : Blo 2135435 4805207 := bstep (se 1 (by rfl) ⟨3603905, by rfl⟩ : syracuseStep 4805207 = 7207811) B7207811
theorem B3203471 : Blo 2135435 3203471 := bstep (se 1 (by rfl) ⟨2402603, by rfl⟩ : syracuseStep 3203471 = 4805207) B4805207
theorem B2135647 : Blo 2135435 2135647 := bstep (se 1 (by rfl) ⟨1601735, by rfl⟩ : syracuseStep 2135647 = 3203471) B3203471
theorem B3203477 : Blo 2135435 3203477 := bbase (se 6 (by rfl) ⟨75081, by rfl⟩ : syracuseStep 3203477 = 150163) (by norm_num)
theorem B2135651 : Blo 2135435 2135651 := bstep (se 1 (by rfl) ⟨1601738, by rfl⟩ : syracuseStep 2135651 = 3203477) B3203477
theorem B7697045 : Blo 2135435 7697045 := bbase (se 6 (by rfl) ⟨180399, by rfl⟩ : syracuseStep 7697045 = 360799) (by norm_num)
theorem B5131363 : Blo 2135435 5131363 := bstep (se 1 (by rfl) ⟨3848522, by rfl⟩ : syracuseStep 5131363 = 7697045) B7697045
theorem B6841817 : Blo 2135435 6841817 := bstep (se 2 (by rfl) ⟨2565681, by rfl⟩ : syracuseStep 6841817 = 5131363) B5131363
theorem B4561211 : Blo 2135435 4561211 := bstep (se 1 (by rfl) ⟨3420908, by rfl⟩ : syracuseStep 4561211 = 6841817) B6841817
theorem B12163229 : Blo 2135435 12163229 := bstep (se 3 (by rfl) ⟨2280605, by rfl⟩ : syracuseStep 12163229 = 4561211) B4561211
theorem B8108819 : Blo 2135435 8108819 := bstep (se 1 (by rfl) ⟨6081614, by rfl⟩ : syracuseStep 8108819 = 12163229) B12163229
theorem B5405879 : Blo 2135435 5405879 := bstep (se 1 (by rfl) ⟨4054409, by rfl⟩ : syracuseStep 5405879 = 8108819) B8108819
theorem B3603919 : Blo 2135435 3603919 := bstep (se 1 (by rfl) ⟨2702939, by rfl⟩ : syracuseStep 3603919 = 5405879) B5405879
theorem B4805225 : Blo 2135435 4805225 := bstep (se 2 (by rfl) ⟨1801959, by rfl⟩ : syracuseStep 4805225 = 3603919) B3603919
theorem B3203483 : Blo 2135435 3203483 := bstep (se 1 (by rfl) ⟨2402612, by rfl⟩ : syracuseStep 3203483 = 4805225) B4805225
theorem B2135655 : Blo 2135435 2135655 := bstep (se 1 (by rfl) ⟨1601741, by rfl⟩ : syracuseStep 2135655 = 3203483) B3203483
theorem B2402617 : Blo 2135435 2402617 := bbase (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) (by norm_num)
theorem B3203489 : Blo 2135435 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B2135659 : Blo 2135435 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B6081637 : Blo 2135435 6081637 := bbase (se 4 (by rfl) ⟨570153, by rfl⟩ : syracuseStep 6081637 = 1140307) (by norm_num)
theorem B8108849 : Blo 2135435 8108849 := bstep (se 2 (by rfl) ⟨3040818, by rfl⟩ : syracuseStep 8108849 = 6081637) B6081637
theorem B5405899 : Blo 2135435 5405899 := bstep (se 1 (by rfl) ⟨4054424, by rfl⟩ : syracuseStep 5405899 = 8108849) B8108849
theorem B7207865 : Blo 2135435 7207865 := bstep (se 2 (by rfl) ⟨2702949, by rfl⟩ : syracuseStep 7207865 = 5405899) B5405899
theorem B4805243 : Blo 2135435 4805243 := bstep (se 1 (by rfl) ⟨3603932, by rfl⟩ : syracuseStep 4805243 = 7207865) B7207865
theorem B3203495 : Blo 2135435 3203495 := bstep (se 1 (by rfl) ⟨2402621, by rfl⟩ : syracuseStep 3203495 = 4805243) B4805243
theorem B2135663 : Blo 2135435 2135663 := bstep (se 1 (by rfl) ⟨1601747, by rfl⟩ : syracuseStep 2135663 = 3203495) B3203495
theorem B3203501 : Blo 2135435 3203501 := bbase (se 3 (by rfl) ⟨600656, by rfl⟩ : syracuseStep 3203501 = 1201313) (by norm_num)
theorem B2135667 : Blo 2135435 2135667 := bstep (se 1 (by rfl) ⟨1601750, by rfl⟩ : syracuseStep 2135667 = 3203501) B3203501
theorem B4805261 : Blo 2135435 4805261 := bbase (se 3 (by rfl) ⟨900986, by rfl⟩ : syracuseStep 4805261 = 1801973) (by norm_num)
theorem B3203507 : Blo 2135435 3203507 := bstep (se 1 (by rfl) ⟨2402630, by rfl⟩ : syracuseStep 3203507 = 4805261) B4805261
theorem B2135671 : Blo 2135435 2135671 := bstep (se 1 (by rfl) ⟨1601753, by rfl⟩ : syracuseStep 2135671 = 3203507) B3203507
theorem B2702965 : Blo 2135435 2702965 := bbase (se 5 (by rfl) ⟨126701, by rfl⟩ : syracuseStep 2702965 = 253403) (by norm_num)
theorem B3603953 : Blo 2135435 3603953 := bstep (se 2 (by rfl) ⟨1351482, by rfl⟩ : syracuseStep 3603953 = 2702965) B2702965
theorem B2402635 : Blo 2135435 2402635 := bstep (se 1 (by rfl) ⟨1801976, by rfl⟩ : syracuseStep 2402635 = 3603953) B3603953
theorem B3203513 : Blo 2135435 3203513 := bstep (se 2 (by rfl) ⟨1201317, by rfl⟩ : syracuseStep 3203513 = 2402635) B2402635
theorem B2135675 : Blo 2135435 2135675 := bstep (se 1 (by rfl) ⟨1601756, by rfl⟩ : syracuseStep 2135675 = 3203513) B3203513
theorem B6583061 : Blo 2135435 6583061 := bbase (se 6 (by rfl) ⟨154290, by rfl⟩ : syracuseStep 6583061 = 308581) (by norm_num)
theorem B4388707 : Blo 2135435 4388707 := bstep (se 1 (by rfl) ⟨3291530, by rfl⟩ : syracuseStep 4388707 = 6583061) B6583061
theorem B5851609 : Blo 2135435 5851609 := bstep (se 2 (by rfl) ⟨2194353, by rfl⟩ : syracuseStep 5851609 = 4388707) B4388707
theorem B31208581 : Blo 2135435 31208581 := bstep (se 4 (by rfl) ⟨2925804, by rfl⟩ : syracuseStep 31208581 = 5851609) B5851609
theorem B41611441 : Blo 2135435 41611441 := bstep (se 2 (by rfl) ⟨15604290, by rfl⟩ : syracuseStep 41611441 = 31208581) B31208581
theorem B55481921 : Blo 2135435 55481921 := bstep (se 2 (by rfl) ⟨20805720, by rfl⟩ : syracuseStep 55481921 = 41611441) B41611441
theorem B36987947 : Blo 2135435 36987947 := bstep (se 1 (by rfl) ⟨27740960, by rfl⟩ : syracuseStep 36987947 = 55481921) B55481921
theorem B24658631 : Blo 2135435 24658631 := bstep (se 1 (by rfl) ⟨18493973, by rfl⟩ : syracuseStep 24658631 = 36987947) B36987947
theorem B16439087 : Blo 2135435 16439087 := bstep (se 1 (by rfl) ⟨12329315, by rfl⟩ : syracuseStep 16439087 = 24658631) B24658631
theorem B10959391 : Blo 2135435 10959391 := bstep (se 1 (by rfl) ⟨8219543, by rfl⟩ : syracuseStep 10959391 = 16439087) B16439087
theorem B14612521 : Blo 2135435 14612521 := bstep (se 2 (by rfl) ⟨5479695, by rfl⟩ : syracuseStep 14612521 = 10959391) B10959391
theorem B19483361 : Blo 2135435 19483361 := bstep (se 2 (by rfl) ⟨7306260, by rfl⟩ : syracuseStep 19483361 = 14612521) B14612521
theorem B12988907 : Blo 2135435 12988907 := bstep (se 1 (by rfl) ⟨9741680, by rfl⟩ : syracuseStep 12988907 = 19483361) B19483361
theorem B8659271 : Blo 2135435 8659271 := bstep (se 1 (by rfl) ⟨6494453, by rfl⟩ : syracuseStep 8659271 = 12988907) B12988907
theorem B23091389 : Blo 2135435 23091389 := bstep (se 3 (by rfl) ⟨4329635, by rfl⟩ : syracuseStep 23091389 = 8659271) B8659271
theorem B15394259 : Blo 2135435 15394259 := bstep (se 1 (by rfl) ⟨11545694, by rfl⟩ : syracuseStep 15394259 = 23091389) B23091389
theorem B41051357 : Blo 2135435 41051357 := bstep (se 3 (by rfl) ⟨7697129, by rfl⟩ : syracuseStep 41051357 = 15394259) B15394259
theorem B27367571 : Blo 2135435 27367571 := bstep (se 1 (by rfl) ⟨20525678, by rfl⟩ : syracuseStep 27367571 = 41051357) B41051357
theorem B18245047 : Blo 2135435 18245047 := bstep (se 1 (by rfl) ⟨13683785, by rfl⟩ : syracuseStep 18245047 = 27367571) B27367571
theorem B24326729 : Blo 2135435 24326729 := bstep (se 2 (by rfl) ⟨9122523, by rfl⟩ : syracuseStep 24326729 = 18245047) B18245047
theorem B16217819 : Blo 2135435 16217819 := bstep (se 1 (by rfl) ⟨12163364, by rfl⟩ : syracuseStep 16217819 = 24326729) B24326729
theorem B10811879 : Blo 2135435 10811879 := bstep (se 1 (by rfl) ⟨8108909, by rfl⟩ : syracuseStep 10811879 = 16217819) B16217819
theorem B7207919 : Blo 2135435 7207919 := bstep (se 1 (by rfl) ⟨5405939, by rfl⟩ : syracuseStep 7207919 = 10811879) B10811879
theorem B4805279 : Blo 2135435 4805279 := bstep (se 1 (by rfl) ⟨3603959, by rfl⟩ : syracuseStep 4805279 = 7207919) B7207919
theorem B3203519 : Blo 2135435 3203519 := bstep (se 1 (by rfl) ⟨2402639, by rfl⟩ : syracuseStep 3203519 = 4805279) B4805279
theorem B2135679 : Blo 2135435 2135679 := bstep (se 1 (by rfl) ⟨1601759, by rfl⟩ : syracuseStep 2135679 = 3203519) B3203519
theorem B3203525 : Blo 2135435 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B2135683 : Blo 2135435 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B3603973 : Blo 2135435 3603973 := bbase (se 4 (by rfl) ⟨337872, by rfl⟩ : syracuseStep 3603973 = 675745) (by norm_num)
theorem B4805297 : Blo 2135435 4805297 := bstep (se 2 (by rfl) ⟨1801986, by rfl⟩ : syracuseStep 4805297 = 3603973) B3603973
theorem B3203531 : Blo 2135435 3203531 := bstep (se 1 (by rfl) ⟨2402648, by rfl⟩ : syracuseStep 3203531 = 4805297) B4805297
theorem B2135687 : Blo 2135435 2135687 := bstep (se 1 (by rfl) ⟨1601765, by rfl⟩ : syracuseStep 2135687 = 3203531) B3203531
theorem B2402653 : Blo 2135435 2402653 := bbase (se 3 (by rfl) ⟨450497, by rfl⟩ : syracuseStep 2402653 = 900995) (by norm_num)
theorem B3203537 : Blo 2135435 3203537 := bstep (se 2 (by rfl) ⟨1201326, by rfl⟩ : syracuseStep 3203537 = 2402653) B2402653
theorem B2135691 : Blo 2135435 2135691 := bstep (se 1 (by rfl) ⟨1601768, by rfl⟩ : syracuseStep 2135691 = 3203537) B3203537
theorem B7207973 : Blo 2135435 7207973 := bbase (se 4 (by rfl) ⟨675747, by rfl⟩ : syracuseStep 7207973 = 1351495) (by norm_num)
theorem B4805315 : Blo 2135435 4805315 := bstep (se 1 (by rfl) ⟨3603986, by rfl⟩ : syracuseStep 4805315 = 7207973) B7207973
theorem B3203543 : Blo 2135435 3203543 := bstep (se 1 (by rfl) ⟨2402657, by rfl⟩ : syracuseStep 3203543 = 4805315) B4805315
theorem B2135695 : Blo 2135435 2135695 := bstep (se 1 (by rfl) ⟨1601771, by rfl⟩ : syracuseStep 2135695 = 3203543) B3203543
theorem B3203549 : Blo 2135435 3203549 := bbase (se 3 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 3203549 = 1201331) (by norm_num)
theorem B2135699 : Blo 2135435 2135699 := bstep (se 1 (by rfl) ⟨1601774, by rfl⟩ : syracuseStep 2135699 = 3203549) B3203549
theorem B4805333 : Blo 2135435 4805333 := bbase (se 7 (by rfl) ⟨56312, by rfl⟩ : syracuseStep 4805333 = 112625) (by norm_num)
theorem B3203555 : Blo 2135435 3203555 := bstep (se 1 (by rfl) ⟨2402666, by rfl⟩ : syracuseStep 3203555 = 4805333) B4805333
theorem B2135703 : Blo 2135435 2135703 := bstep (se 1 (by rfl) ⟨1601777, by rfl⟩ : syracuseStep 2135703 = 3203555) B3203555
theorem B9122645 : Blo 2135435 9122645 := bbase (se 9 (by rfl) ⟨26726, by rfl⟩ : syracuseStep 9122645 = 53453) (by norm_num)
theorem B6081763 : Blo 2135435 6081763 := bstep (se 1 (by rfl) ⟨4561322, by rfl⟩ : syracuseStep 6081763 = 9122645) B9122645
theorem B8109017 : Blo 2135435 8109017 := bstep (se 2 (by rfl) ⟨3040881, by rfl⟩ : syracuseStep 8109017 = 6081763) B6081763
theorem B5406011 : Blo 2135435 5406011 := bstep (se 1 (by rfl) ⟨4054508, by rfl⟩ : syracuseStep 5406011 = 8109017) B8109017
theorem B3604007 : Blo 2135435 3604007 := bstep (se 1 (by rfl) ⟨2703005, by rfl⟩ : syracuseStep 3604007 = 5406011) B5406011
theorem B2402671 : Blo 2135435 2402671 := bstep (se 1 (by rfl) ⟨1802003, by rfl⟩ : syracuseStep 2402671 = 3604007) B3604007
theorem B3203561 : Blo 2135435 3203561 := bstep (se 2 (by rfl) ⟨1201335, by rfl⟩ : syracuseStep 3203561 = 2402671) B2402671
theorem B2135707 : Blo 2135435 2135707 := bstep (se 1 (by rfl) ⟨1601780, by rfl⟩ : syracuseStep 2135707 = 3203561) B3203561
theorem B4329701 : Blo 2135435 4329701 := bbase (se 4 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 4329701 = 811819) (by norm_num)
theorem B2886467 : Blo 2135435 2886467 := bstep (se 1 (by rfl) ⟨2164850, by rfl⟩ : syracuseStep 2886467 = 4329701) B4329701
theorem B30788981 : Blo 2135435 30788981 := bstep (se 5 (by rfl) ⟨1443233, by rfl⟩ : syracuseStep 30788981 = 2886467) B2886467
theorem B20525987 : Blo 2135435 20525987 := bstep (se 1 (by rfl) ⟨15394490, by rfl⟩ : syracuseStep 20525987 = 30788981) B30788981
theorem B13683991 : Blo 2135435 13683991 := bstep (se 1 (by rfl) ⟨10262993, by rfl⟩ : syracuseStep 13683991 = 20525987) B20525987
theorem B18245321 : Blo 2135435 18245321 := bstep (se 2 (by rfl) ⟨6841995, by rfl⟩ : syracuseStep 18245321 = 13683991) B13683991
theorem B12163547 : Blo 2135435 12163547 := bstep (se 1 (by rfl) ⟨9122660, by rfl⟩ : syracuseStep 12163547 = 18245321) B18245321
theorem B8109031 : Blo 2135435 8109031 := bstep (se 1 (by rfl) ⟨6081773, by rfl⟩ : syracuseStep 8109031 = 12163547) B12163547
theorem B10812041 : Blo 2135435 10812041 := bstep (se 2 (by rfl) ⟨4054515, by rfl⟩ : syracuseStep 10812041 = 8109031) B8109031
theorem B7208027 : Blo 2135435 7208027 := bstep (se 1 (by rfl) ⟨5406020, by rfl⟩ : syracuseStep 7208027 = 10812041) B10812041
theorem B4805351 : Blo 2135435 4805351 := bstep (se 1 (by rfl) ⟨3604013, by rfl⟩ : syracuseStep 4805351 = 7208027) B7208027
theorem B3203567 : Blo 2135435 3203567 := bstep (se 1 (by rfl) ⟨2402675, by rfl⟩ : syracuseStep 3203567 = 4805351) B4805351
theorem B2135711 : Blo 2135435 2135711 := bstep (se 1 (by rfl) ⟨1601783, by rfl⟩ : syracuseStep 2135711 = 3203567) B3203567
theorem B3203573 : Blo 2135435 3203573 := bbase (se 5 (by rfl) ⟨150167, by rfl⟩ : syracuseStep 3203573 = 300335) (by norm_num)
theorem B2135715 : Blo 2135435 2135715 := bstep (se 1 (by rfl) ⟨1601786, by rfl⟩ : syracuseStep 2135715 = 3203573) B3203573
theorem B6081797 : Blo 2135435 6081797 := bbase (se 4 (by rfl) ⟨570168, by rfl⟩ : syracuseStep 6081797 = 1140337) (by norm_num)
theorem B4054531 : Blo 2135435 4054531 := bstep (se 1 (by rfl) ⟨3040898, by rfl⟩ : syracuseStep 4054531 = 6081797) B6081797
theorem B5406041 : Blo 2135435 5406041 := bstep (se 2 (by rfl) ⟨2027265, by rfl⟩ : syracuseStep 5406041 = 4054531) B4054531
theorem B3604027 : Blo 2135435 3604027 := bstep (se 1 (by rfl) ⟨2703020, by rfl⟩ : syracuseStep 3604027 = 5406041) B5406041
theorem B4805369 : Blo 2135435 4805369 := bstep (se 2 (by rfl) ⟨1802013, by rfl⟩ : syracuseStep 4805369 = 3604027) B3604027
theorem B3203579 : Blo 2135435 3203579 := bstep (se 1 (by rfl) ⟨2402684, by rfl⟩ : syracuseStep 3203579 = 4805369) B4805369
theorem B2135719 : Blo 2135435 2135719 := bstep (se 1 (by rfl) ⟨1601789, by rfl⟩ : syracuseStep 2135719 = 3203579) B3203579
theorem B2402689 : Blo 2135435 2402689 := bbase (se 2 (by rfl) ⟨901008, by rfl⟩ : syracuseStep 2402689 = 1802017) (by norm_num)
theorem B3203585 : Blo 2135435 3203585 := bstep (se 2 (by rfl) ⟨1201344, by rfl⟩ : syracuseStep 3203585 = 2402689) B2402689
theorem B2135723 : Blo 2135435 2135723 := bstep (se 1 (by rfl) ⟨1601792, by rfl⟩ : syracuseStep 2135723 = 3203585) B3203585
theorem B5406061 : Blo 2135435 5406061 := bbase (se 3 (by rfl) ⟨1013636, by rfl⟩ : syracuseStep 5406061 = 2027273) (by norm_num)
theorem B7208081 : Blo 2135435 7208081 := bstep (se 2 (by rfl) ⟨2703030, by rfl⟩ : syracuseStep 7208081 = 5406061) B5406061
theorem B4805387 : Blo 2135435 4805387 := bstep (se 1 (by rfl) ⟨3604040, by rfl⟩ : syracuseStep 4805387 = 7208081) B7208081
theorem B3203591 : Blo 2135435 3203591 := bstep (se 1 (by rfl) ⟨2402693, by rfl⟩ : syracuseStep 3203591 = 4805387) B4805387
theorem B2135727 : Blo 2135435 2135727 := bstep (se 1 (by rfl) ⟨1601795, by rfl⟩ : syracuseStep 2135727 = 3203591) B3203591
theorem B3203597 : Blo 2135435 3203597 := bbase (se 3 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 3203597 = 1201349) (by norm_num)
theorem B2135731 : Blo 2135435 2135731 := bstep (se 1 (by rfl) ⟨1601798, by rfl⟩ : syracuseStep 2135731 = 3203597) B3203597
theorem B4805405 : Blo 2135435 4805405 := bbase (se 3 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 4805405 = 1802027) (by norm_num)
theorem B3203603 : Blo 2135435 3203603 := bstep (se 1 (by rfl) ⟨2402702, by rfl⟩ : syracuseStep 3203603 = 4805405) B4805405
theorem B2135735 : Blo 2135435 2135735 := bstep (se 1 (by rfl) ⟨1601801, by rfl⟩ : syracuseStep 2135735 = 3203603) B3203603
theorem B3604061 : Blo 2135435 3604061 := bbase (se 3 (by rfl) ⟨675761, by rfl⟩ : syracuseStep 3604061 = 1351523) (by norm_num)
theorem B2402707 : Blo 2135435 2402707 := bstep (se 1 (by rfl) ⟨1802030, by rfl⟩ : syracuseStep 2402707 = 3604061) B3604061
theorem B3203609 : Blo 2135435 3203609 := bstep (se 2 (by rfl) ⟨1201353, by rfl⟩ : syracuseStep 3203609 = 2402707) B2402707
theorem B2135739 : Blo 2135435 2135739 := bstep (se 1 (by rfl) ⟨1601804, by rfl⟩ : syracuseStep 2135739 = 3203609) B3203609
theorem B3954421 : Blo 2135435 3954421 := bbase (se 5 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 3954421 = 370727) (by norm_num)
theorem B5272561 : Blo 2135435 5272561 := bstep (se 2 (by rfl) ⟨1977210, by rfl⟩ : syracuseStep 5272561 = 3954421) B3954421
theorem B7030081 : Blo 2135435 7030081 := bstep (se 2 (by rfl) ⟨2636280, by rfl⟩ : syracuseStep 7030081 = 5272561) B5272561
theorem B9373441 : Blo 2135435 9373441 := bstep (se 2 (by rfl) ⟨3515040, by rfl⟩ : syracuseStep 9373441 = 7030081) B7030081
theorem B12497921 : Blo 2135435 12497921 := bstep (se 2 (by rfl) ⟨4686720, by rfl⟩ : syracuseStep 12497921 = 9373441) B9373441
theorem B8331947 : Blo 2135435 8331947 := bstep (se 1 (by rfl) ⟨6248960, by rfl⟩ : syracuseStep 8331947 = 12497921) B12497921
theorem B5554631 : Blo 2135435 5554631 := bstep (se 1 (by rfl) ⟨4165973, by rfl⟩ : syracuseStep 5554631 = 8331947) B8331947
theorem B3703087 : Blo 2135435 3703087 := bstep (se 1 (by rfl) ⟨2777315, by rfl⟩ : syracuseStep 3703087 = 5554631) B5554631
theorem B4937449 : Blo 2135435 4937449 := bstep (se 2 (by rfl) ⟨1851543, by rfl⟩ : syracuseStep 4937449 = 3703087) B3703087
theorem B6583265 : Blo 2135435 6583265 := bstep (se 2 (by rfl) ⟨2468724, by rfl⟩ : syracuseStep 6583265 = 4937449) B4937449
theorem B4388843 : Blo 2135435 4388843 := bstep (se 1 (by rfl) ⟨3291632, by rfl⟩ : syracuseStep 4388843 = 6583265) B6583265
theorem B2925895 : Blo 2135435 2925895 := bstep (se 1 (by rfl) ⟨2194421, by rfl⟩ : syracuseStep 2925895 = 4388843) B4388843
theorem B3901193 : Blo 2135435 3901193 := bstep (se 2 (by rfl) ⟨1462947, by rfl⟩ : syracuseStep 3901193 = 2925895) B2925895
theorem B2600795 : Blo 2135435 2600795 := bstep (se 1 (by rfl) ⟨1950596, by rfl⟩ : syracuseStep 2600795 = 3901193) B3901193
theorem B6935453 : Blo 2135435 6935453 := bstep (se 3 (by rfl) ⟨1300397, by rfl⟩ : syracuseStep 6935453 = 2600795) B2600795
theorem B4623635 : Blo 2135435 4623635 := bstep (se 1 (by rfl) ⟨3467726, by rfl⟩ : syracuseStep 4623635 = 6935453) B6935453
theorem B3082423 : Blo 2135435 3082423 := bstep (se 1 (by rfl) ⟨2311817, by rfl⟩ : syracuseStep 3082423 = 4623635) B4623635
theorem B4109897 : Blo 2135435 4109897 := bstep (se 2 (by rfl) ⟨1541211, by rfl⟩ : syracuseStep 4109897 = 3082423) B3082423
theorem B10959725 : Blo 2135435 10959725 := bstep (se 3 (by rfl) ⟨2054948, by rfl⟩ : syracuseStep 10959725 = 4109897) B4109897
theorem B7306483 : Blo 2135435 7306483 := bstep (se 1 (by rfl) ⟨5479862, by rfl⟩ : syracuseStep 7306483 = 10959725) B10959725
theorem B9741977 : Blo 2135435 9741977 := bstep (se 2 (by rfl) ⟨3653241, by rfl⟩ : syracuseStep 9741977 = 7306483) B7306483
theorem B6494651 : Blo 2135435 6494651 := bstep (se 1 (by rfl) ⟨4870988, by rfl⟩ : syracuseStep 6494651 = 9741977) B9741977
theorem B4329767 : Blo 2135435 4329767 := bstep (se 1 (by rfl) ⟨3247325, by rfl⟩ : syracuseStep 4329767 = 6494651) B6494651
theorem B2886511 : Blo 2135435 2886511 := bstep (se 1 (by rfl) ⟨2164883, by rfl⟩ : syracuseStep 2886511 = 4329767) B4329767
theorem B3848681 : Blo 2135435 3848681 := bstep (se 2 (by rfl) ⟨1443255, by rfl⟩ : syracuseStep 3848681 = 2886511) B2886511
theorem B2565787 : Blo 2135435 2565787 := bstep (se 1 (by rfl) ⟨1924340, by rfl⟩ : syracuseStep 2565787 = 3848681) B3848681
theorem B3421049 : Blo 2135435 3421049 := bstep (se 2 (by rfl) ⟨1282893, by rfl⟩ : syracuseStep 3421049 = 2565787) B2565787
theorem B9122797 : Blo 2135435 9122797 := bstep (se 3 (by rfl) ⟨1710524, by rfl⟩ : syracuseStep 9122797 = 3421049) B3421049
theorem B12163729 : Blo 2135435 12163729 := bstep (se 2 (by rfl) ⟨4561398, by rfl⟩ : syracuseStep 12163729 = 9122797) B9122797
theorem B16218305 : Blo 2135435 16218305 := bstep (se 2 (by rfl) ⟨6081864, by rfl⟩ : syracuseStep 16218305 = 12163729) B12163729
theorem B10812203 : Blo 2135435 10812203 := bstep (se 1 (by rfl) ⟨8109152, by rfl⟩ : syracuseStep 10812203 = 16218305) B16218305
theorem B7208135 : Blo 2135435 7208135 := bstep (se 1 (by rfl) ⟨5406101, by rfl⟩ : syracuseStep 7208135 = 10812203) B10812203
theorem B4805423 : Blo 2135435 4805423 := bstep (se 1 (by rfl) ⟨3604067, by rfl⟩ : syracuseStep 4805423 = 7208135) B7208135
theorem B3203615 : Blo 2135435 3203615 := bstep (se 1 (by rfl) ⟨2402711, by rfl⟩ : syracuseStep 3203615 = 4805423) B4805423
theorem B2135743 : Blo 2135435 2135743 := bstep (se 1 (by rfl) ⟨1601807, by rfl⟩ : syracuseStep 2135743 = 3203615) B3203615
theorem B3203621 : Blo 2135435 3203621 := bbase (se 4 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 3203621 = 600679) (by norm_num)
theorem B2135747 : Blo 2135435 2135747 := bstep (se 1 (by rfl) ⟨1601810, by rfl⟩ : syracuseStep 2135747 = 3203621) B3203621
theorem B2703061 : Blo 2135435 2703061 := bbase (se 7 (by rfl) ⟨31676, by rfl⟩ : syracuseStep 2703061 = 63353) (by norm_num)
theorem B3604081 : Blo 2135435 3604081 := bstep (se 2 (by rfl) ⟨1351530, by rfl⟩ : syracuseStep 3604081 = 2703061) B2703061
theorem B4805441 : Blo 2135435 4805441 := bstep (se 2 (by rfl) ⟨1802040, by rfl⟩ : syracuseStep 4805441 = 3604081) B3604081
theorem B3203627 : Blo 2135435 3203627 := bstep (se 1 (by rfl) ⟨2402720, by rfl⟩ : syracuseStep 3203627 = 4805441) B4805441
theorem B2135751 : Blo 2135435 2135751 := bstep (se 1 (by rfl) ⟨1601813, by rfl⟩ : syracuseStep 2135751 = 3203627) B3203627
theorem B2402725 : Blo 2135435 2402725 := bbase (se 4 (by rfl) ⟨225255, by rfl⟩ : syracuseStep 2402725 = 450511) (by norm_num)
theorem B3203633 : Blo 2135435 3203633 := bstep (se 2 (by rfl) ⟨1201362, by rfl⟩ : syracuseStep 3203633 = 2402725) B2402725
theorem B2135755 : Blo 2135435 2135755 := bstep (se 1 (by rfl) ⟨1601816, by rfl⟩ : syracuseStep 2135755 = 3203633) B3203633
theorem B5131613 : Blo 2135435 5131613 := bbase (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) (by norm_num)
theorem B13684301 : Blo 2135435 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B9122867 : Blo 2135435 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B6081911 : Blo 2135435 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B4054607 : Blo 2135435 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B2703071 : Blo 2135435 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B7208189 : Blo 2135435 7208189 := bstep (se 3 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 7208189 = 2703071) B2703071
theorem B4805459 : Blo 2135435 4805459 := bstep (se 1 (by rfl) ⟨3604094, by rfl⟩ : syracuseStep 4805459 = 7208189) B7208189
theorem B3203639 : Blo 2135435 3203639 := bstep (se 1 (by rfl) ⟨2402729, by rfl⟩ : syracuseStep 3203639 = 4805459) B4805459
theorem B2135759 : Blo 2135435 2135759 := bstep (se 1 (by rfl) ⟨1601819, by rfl⟩ : syracuseStep 2135759 = 3203639) B3203639
theorem B3203645 : Blo 2135435 3203645 := bbase (se 3 (by rfl) ⟨600683, by rfl⟩ : syracuseStep 3203645 = 1201367) (by norm_num)
theorem B2135763 : Blo 2135435 2135763 := bstep (se 1 (by rfl) ⟨1601822, by rfl⟩ : syracuseStep 2135763 = 3203645) B3203645
theorem B4805477 : Blo 2135435 4805477 := bbase (se 4 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 4805477 = 901027) (by norm_num)
theorem B3203651 : Blo 2135435 3203651 := bstep (se 1 (by rfl) ⟨2402738, by rfl⟩ : syracuseStep 3203651 = 4805477) B4805477
theorem B2135767 : Blo 2135435 2135767 := bstep (se 1 (by rfl) ⟨1601825, by rfl⟩ : syracuseStep 2135767 = 3203651) B3203651
theorem B5406173 : Blo 2135435 5406173 := bbase (se 3 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 5406173 = 2027315) (by norm_num)
theorem B3604115 : Blo 2135435 3604115 := bstep (se 1 (by rfl) ⟨2703086, by rfl⟩ : syracuseStep 3604115 = 5406173) B5406173
theorem B2402743 : Blo 2135435 2402743 := bstep (se 1 (by rfl) ⟨1802057, by rfl⟩ : syracuseStep 2402743 = 3604115) B3604115
theorem B3203657 : Blo 2135435 3203657 := bstep (se 2 (by rfl) ⟨1201371, by rfl⟩ : syracuseStep 3203657 = 2402743) B2402743
theorem B2135771 : Blo 2135435 2135771 := bstep (se 1 (by rfl) ⟨1601828, by rfl⟩ : syracuseStep 2135771 = 3203657) B3203657
theorem B4054637 : Blo 2135435 4054637 := bbase (se 3 (by rfl) ⟨760244, by rfl⟩ : syracuseStep 4054637 = 1520489) (by norm_num)
theorem B10812365 : Blo 2135435 10812365 := bstep (se 3 (by rfl) ⟨2027318, by rfl⟩ : syracuseStep 10812365 = 4054637) B4054637
theorem B7208243 : Blo 2135435 7208243 := bstep (se 1 (by rfl) ⟨5406182, by rfl⟩ : syracuseStep 7208243 = 10812365) B10812365
theorem B4805495 : Blo 2135435 4805495 := bstep (se 1 (by rfl) ⟨3604121, by rfl⟩ : syracuseStep 4805495 = 7208243) B7208243
theorem B3203663 : Blo 2135435 3203663 := bstep (se 1 (by rfl) ⟨2402747, by rfl⟩ : syracuseStep 3203663 = 4805495) B4805495
theorem B2135775 : Blo 2135435 2135775 := bstep (se 1 (by rfl) ⟨1601831, by rfl⟩ : syracuseStep 2135775 = 3203663) B3203663
theorem B3203669 : Blo 2135435 3203669 := bbase (se 8 (by rfl) ⟨18771, by rfl⟩ : syracuseStep 3203669 = 37543) (by norm_num)
theorem B2135779 : Blo 2135435 2135779 := bstep (se 1 (by rfl) ⟨1601834, by rfl⟩ : syracuseStep 2135779 = 3203669) B3203669
theorem B2886565 : Blo 2135435 2886565 := bbase (se 4 (by rfl) ⟨270615, by rfl⟩ : syracuseStep 2886565 = 541231) (by norm_num)
theorem B3848753 : Blo 2135435 3848753 := bstep (se 2 (by rfl) ⟨1443282, by rfl⟩ : syracuseStep 3848753 = 2886565) B2886565
theorem B10263341 : Blo 2135435 10263341 := bstep (se 3 (by rfl) ⟨1924376, by rfl⟩ : syracuseStep 10263341 = 3848753) B3848753
theorem B6842227 : Blo 2135435 6842227 := bstep (se 1 (by rfl) ⟨5131670, by rfl⟩ : syracuseStep 6842227 = 10263341) B10263341
theorem B9122969 : Blo 2135435 9122969 := bstep (se 2 (by rfl) ⟨3421113, by rfl⟩ : syracuseStep 9122969 = 6842227) B6842227
theorem B6081979 : Blo 2135435 6081979 := bstep (se 1 (by rfl) ⟨4561484, by rfl⟩ : syracuseStep 6081979 = 9122969) B9122969
theorem B8109305 : Blo 2135435 8109305 := bstep (se 2 (by rfl) ⟨3040989, by rfl⟩ : syracuseStep 8109305 = 6081979) B6081979
theorem B5406203 : Blo 2135435 5406203 := bstep (se 1 (by rfl) ⟨4054652, by rfl⟩ : syracuseStep 5406203 = 8109305) B8109305
theorem B3604135 : Blo 2135435 3604135 := bstep (se 1 (by rfl) ⟨2703101, by rfl⟩ : syracuseStep 3604135 = 5406203) B5406203
theorem B4805513 : Blo 2135435 4805513 := bstep (se 2 (by rfl) ⟨1802067, by rfl⟩ : syracuseStep 4805513 = 3604135) B3604135
theorem B3203675 : Blo 2135435 3203675 := bstep (se 1 (by rfl) ⟨2402756, by rfl⟩ : syracuseStep 3203675 = 4805513) B4805513
theorem B2135783 : Blo 2135435 2135783 := bstep (se 1 (by rfl) ⟨1601837, by rfl⟩ : syracuseStep 2135783 = 3203675) B3203675
theorem B2402761 : Blo 2135435 2402761 := bbase (se 2 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 2402761 = 1802071) (by norm_num)
theorem B3203681 : Blo 2135435 3203681 := bstep (se 2 (by rfl) ⟨1201380, by rfl⟩ : syracuseStep 3203681 = 2402761) B2402761
theorem B2135787 : Blo 2135435 2135787 := bstep (se 1 (by rfl) ⟨1601840, by rfl⟩ : syracuseStep 2135787 = 3203681) B3203681
theorem B18246005 : Blo 2135435 18246005 := bbase (se 5 (by rfl) ⟨855281, by rfl⟩ : syracuseStep 18246005 = 1710563) (by norm_num)
theorem B12164003 : Blo 2135435 12164003 := bstep (se 1 (by rfl) ⟨9123002, by rfl⟩ : syracuseStep 12164003 = 18246005) B18246005
theorem B8109335 : Blo 2135435 8109335 := bstep (se 1 (by rfl) ⟨6082001, by rfl⟩ : syracuseStep 8109335 = 12164003) B12164003
theorem B5406223 : Blo 2135435 5406223 := bstep (se 1 (by rfl) ⟨4054667, by rfl⟩ : syracuseStep 5406223 = 8109335) B8109335
theorem B7208297 : Blo 2135435 7208297 := bstep (se 2 (by rfl) ⟨2703111, by rfl⟩ : syracuseStep 7208297 = 5406223) B5406223
theorem B4805531 : Blo 2135435 4805531 := bstep (se 1 (by rfl) ⟨3604148, by rfl⟩ : syracuseStep 4805531 = 7208297) B7208297
theorem B3203687 : Blo 2135435 3203687 := bstep (se 1 (by rfl) ⟨2402765, by rfl⟩ : syracuseStep 3203687 = 4805531) B4805531
theorem B2135791 : Blo 2135435 2135791 := bstep (se 1 (by rfl) ⟨1601843, by rfl⟩ : syracuseStep 2135791 = 3203687) B3203687
theorem B3203693 : Blo 2135435 3203693 := bbase (se 3 (by rfl) ⟨600692, by rfl⟩ : syracuseStep 3203693 = 1201385) (by norm_num)
theorem B2135795 : Blo 2135435 2135795 := bstep (se 1 (by rfl) ⟨1601846, by rfl⟩ : syracuseStep 2135795 = 3203693) B3203693
theorem B4805549 : Blo 2135435 4805549 := bbase (se 3 (by rfl) ⟨901040, by rfl⟩ : syracuseStep 4805549 = 1802081) (by norm_num)
theorem B3203699 : Blo 2135435 3203699 := bstep (se 1 (by rfl) ⟨2402774, by rfl⟩ : syracuseStep 3203699 = 4805549) B4805549
theorem B2135799 : Blo 2135435 2135799 := bstep (se 1 (by rfl) ⟨1601849, by rfl⟩ : syracuseStep 2135799 = 3203699) B3203699
theorem B6082037 : Blo 2135435 6082037 := bbase (se 5 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 6082037 = 570191) (by norm_num)
theorem B4054691 : Blo 2135435 4054691 := bstep (se 1 (by rfl) ⟨3041018, by rfl⟩ : syracuseStep 4054691 = 6082037) B6082037
theorem B2703127 : Blo 2135435 2703127 := bstep (se 1 (by rfl) ⟨2027345, by rfl⟩ : syracuseStep 2703127 = 4054691) B4054691
theorem B3604169 : Blo 2135435 3604169 := bstep (se 2 (by rfl) ⟨1351563, by rfl⟩ : syracuseStep 3604169 = 2703127) B2703127
theorem B2402779 : Blo 2135435 2402779 := bstep (se 1 (by rfl) ⟨1802084, by rfl⟩ : syracuseStep 2402779 = 3604169) B3604169
theorem B3203705 : Blo 2135435 3203705 := bstep (se 2 (by rfl) ⟨1201389, by rfl⟩ : syracuseStep 3203705 = 2402779) B2402779
theorem B2135803 : Blo 2135435 2135803 := bstep (se 1 (by rfl) ⟨1601852, by rfl⟩ : syracuseStep 2135803 = 3203705) B3203705
theorem B22219157 : Blo 2135435 22219157 := bbase (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) (by norm_num)
theorem B59251085 : Blo 2135435 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B39500723 : Blo 2135435 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B105335261 : Blo 2135435 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B70223507 : Blo 2135435 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B46815671 : Blo 2135435 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B31210447 : Blo 2135435 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B41613929 : Blo 2135435 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B27742619 : Blo 2135435 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B73980317 : Blo 2135435 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B49320211 : Blo 2135435 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B65760281 : Blo 2135435 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B43840187 : Blo 2135435 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B29226791 : Blo 2135435 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B77938109 : Blo 2135435 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B51958739 : Blo 2135435 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B34639159 : Blo 2135435 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B46185545 : Blo 2135435 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B30790363 : Blo 2135435 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B41053817 : Blo 2135435 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B27369211 : Blo 2135435 27369211 := bstep (se 1 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 27369211 = 41053817) B41053817
theorem B36492281 : Blo 2135435 36492281 := bstep (se 2 (by rfl) ⟨13684605, by rfl⟩ : syracuseStep 36492281 = 27369211) B27369211
theorem B24328187 : Blo 2135435 24328187 := bstep (se 1 (by rfl) ⟨18246140, by rfl⟩ : syracuseStep 24328187 = 36492281) B36492281
theorem B16218791 : Blo 2135435 16218791 := bstep (se 1 (by rfl) ⟨12164093, by rfl⟩ : syracuseStep 16218791 = 24328187) B24328187
theorem B10812527 : Blo 2135435 10812527 := bstep (se 1 (by rfl) ⟨8109395, by rfl⟩ : syracuseStep 10812527 = 16218791) B16218791
theorem B7208351 : Blo 2135435 7208351 := bstep (se 1 (by rfl) ⟨5406263, by rfl⟩ : syracuseStep 7208351 = 10812527) B10812527
theorem B4805567 : Blo 2135435 4805567 := bstep (se 1 (by rfl) ⟨3604175, by rfl⟩ : syracuseStep 4805567 = 7208351) B7208351
theorem B3203711 : Blo 2135435 3203711 := bstep (se 1 (by rfl) ⟨2402783, by rfl⟩ : syracuseStep 3203711 = 4805567) B4805567
theorem B2135807 : Blo 2135435 2135807 := bstep (se 1 (by rfl) ⟨1601855, by rfl⟩ : syracuseStep 2135807 = 3203711) B3203711
theorem B3203717 : Blo 2135435 3203717 := bbase (se 4 (by rfl) ⟨300348, by rfl⟩ : syracuseStep 3203717 = 600697) (by norm_num)
theorem B2135811 : Blo 2135435 2135811 := bstep (se 1 (by rfl) ⟨1601858, by rfl⟩ : syracuseStep 2135811 = 3203717) B3203717
theorem B3604189 : Blo 2135435 3604189 := bbase (se 3 (by rfl) ⟨675785, by rfl⟩ : syracuseStep 3604189 = 1351571) (by norm_num)
theorem B4805585 : Blo 2135435 4805585 := bstep (se 2 (by rfl) ⟨1802094, by rfl⟩ : syracuseStep 4805585 = 3604189) B3604189
theorem B3203723 : Blo 2135435 3203723 := bstep (se 1 (by rfl) ⟨2402792, by rfl⟩ : syracuseStep 3203723 = 4805585) B4805585
theorem B2135815 : Blo 2135435 2135815 := bstep (se 1 (by rfl) ⟨1601861, by rfl⟩ : syracuseStep 2135815 = 3203723) B3203723
theorem B2402797 : Blo 2135435 2402797 := bbase (se 3 (by rfl) ⟨450524, by rfl⟩ : syracuseStep 2402797 = 901049) (by norm_num)
theorem B3203729 : Blo 2135435 3203729 := bstep (se 2 (by rfl) ⟨1201398, by rfl⟩ : syracuseStep 3203729 = 2402797) B2402797
theorem B2135819 : Blo 2135435 2135819 := bstep (se 1 (by rfl) ⟨1601864, by rfl⟩ : syracuseStep 2135819 = 3203729) B3203729
theorem B7208405 : Blo 2135435 7208405 := bbase (se 7 (by rfl) ⟨84473, by rfl⟩ : syracuseStep 7208405 = 168947) (by norm_num)
theorem B4805603 : Blo 2135435 4805603 := bstep (se 1 (by rfl) ⟨3604202, by rfl⟩ : syracuseStep 4805603 = 7208405) B7208405
theorem B3203735 : Blo 2135435 3203735 := bstep (se 1 (by rfl) ⟨2402801, by rfl⟩ : syracuseStep 3203735 = 4805603) B4805603
theorem B2135823 : Blo 2135435 2135823 := bstep (se 1 (by rfl) ⟨1601867, by rfl⟩ : syracuseStep 2135823 = 3203735) B3203735
theorem B3203741 : Blo 2135435 3203741 := bbase (se 3 (by rfl) ⟨600701, by rfl⟩ : syracuseStep 3203741 = 1201403) (by norm_num)
theorem B2135827 : Blo 2135435 2135827 := bstep (se 1 (by rfl) ⟨1601870, by rfl⟩ : syracuseStep 2135827 = 3203741) B3203741
theorem B4805621 : Blo 2135435 4805621 := bbase (se 5 (by rfl) ⟨225263, by rfl⟩ : syracuseStep 4805621 = 450527) (by norm_num)
theorem B3203747 : Blo 2135435 3203747 := bstep (se 1 (by rfl) ⟨2402810, by rfl⟩ : syracuseStep 3203747 = 4805621) B4805621
theorem B2135831 : Blo 2135435 2135831 := bstep (se 1 (by rfl) ⟨1601873, by rfl⟩ : syracuseStep 2135831 = 3203747) B3203747
theorem B10403621 : Blo 2135435 10403621 := bbase (se 4 (by rfl) ⟨975339, by rfl⟩ : syracuseStep 10403621 = 1950679) (by norm_num)
theorem B6935747 : Blo 2135435 6935747 := bstep (se 1 (by rfl) ⟨5201810, by rfl⟩ : syracuseStep 6935747 = 10403621) B10403621
theorem B18495325 : Blo 2135435 18495325 := bstep (se 3 (by rfl) ⟨3467873, by rfl⟩ : syracuseStep 18495325 = 6935747) B6935747
theorem B24660433 : Blo 2135435 24660433 := bstep (se 2 (by rfl) ⟨9247662, by rfl⟩ : syracuseStep 24660433 = 18495325) B18495325
theorem B32880577 : Blo 2135435 32880577 := bstep (se 2 (by rfl) ⟨12330216, by rfl⟩ : syracuseStep 32880577 = 24660433) B24660433
theorem B43840769 : Blo 2135435 43840769 := bstep (se 2 (by rfl) ⟨16440288, by rfl⟩ : syracuseStep 43840769 = 32880577) B32880577
theorem B116908717 : Blo 2135435 116908717 := bstep (se 3 (by rfl) ⟨21920384, by rfl⟩ : syracuseStep 116908717 = 43840769) B43840769
theorem B155878289 : Blo 2135435 155878289 := bstep (se 2 (by rfl) ⟨58454358, by rfl⟩ : syracuseStep 155878289 = 116908717) B116908717
theorem B103918859 : Blo 2135435 103918859 := bstep (se 1 (by rfl) ⟨77939144, by rfl⟩ : syracuseStep 103918859 = 155878289) B155878289
theorem B69279239 : Blo 2135435 69279239 := bstep (se 1 (by rfl) ⟨51959429, by rfl⟩ : syracuseStep 69279239 = 103918859) B103918859
theorem B46186159 : Blo 2135435 46186159 := bstep (se 1 (by rfl) ⟨34639619, by rfl⟩ : syracuseStep 46186159 = 69279239) B69279239
theorem B61581545 : Blo 2135435 61581545 := bstep (se 2 (by rfl) ⟨23093079, by rfl⟩ : syracuseStep 61581545 = 46186159) B46186159
theorem B41054363 : Blo 2135435 41054363 := bstep (se 1 (by rfl) ⟨30790772, by rfl⟩ : syracuseStep 41054363 = 61581545) B61581545
theorem B27369575 : Blo 2135435 27369575 := bstep (se 1 (by rfl) ⟨20527181, by rfl⟩ : syracuseStep 27369575 = 41054363) B41054363
theorem B18246383 : Blo 2135435 18246383 := bstep (se 1 (by rfl) ⟨13684787, by rfl⟩ : syracuseStep 18246383 = 27369575) B27369575
theorem B12164255 : Blo 2135435 12164255 := bstep (se 1 (by rfl) ⟨9123191, by rfl⟩ : syracuseStep 12164255 = 18246383) B18246383
theorem B8109503 : Blo 2135435 8109503 := bstep (se 1 (by rfl) ⟨6082127, by rfl⟩ : syracuseStep 8109503 = 12164255) B12164255
theorem B5406335 : Blo 2135435 5406335 := bstep (se 1 (by rfl) ⟨4054751, by rfl⟩ : syracuseStep 5406335 = 8109503) B8109503
theorem B3604223 : Blo 2135435 3604223 := bstep (se 1 (by rfl) ⟨2703167, by rfl⟩ : syracuseStep 3604223 = 5406335) B5406335
theorem B2402815 : Blo 2135435 2402815 := bstep (se 1 (by rfl) ⟨1802111, by rfl⟩ : syracuseStep 2402815 = 3604223) B3604223
theorem B3203753 : Blo 2135435 3203753 := bstep (se 2 (by rfl) ⟨1201407, by rfl⟩ : syracuseStep 3203753 = 2402815) B2402815
theorem B2135835 : Blo 2135435 2135835 := bstep (se 1 (by rfl) ⟨1601876, by rfl⟩ : syracuseStep 2135835 = 3203753) B3203753
theorem B3041069 : Blo 2135435 3041069 := bbase (se 3 (by rfl) ⟨570200, by rfl⟩ : syracuseStep 3041069 = 1140401) (by norm_num)
theorem B8109517 : Blo 2135435 8109517 := bstep (se 3 (by rfl) ⟨1520534, by rfl⟩ : syracuseStep 8109517 = 3041069) B3041069
theorem B10812689 : Blo 2135435 10812689 := bstep (se 2 (by rfl) ⟨4054758, by rfl⟩ : syracuseStep 10812689 = 8109517) B8109517
theorem B7208459 : Blo 2135435 7208459 := bstep (se 1 (by rfl) ⟨5406344, by rfl⟩ : syracuseStep 7208459 = 10812689) B10812689
theorem B4805639 : Blo 2135435 4805639 := bstep (se 1 (by rfl) ⟨3604229, by rfl⟩ : syracuseStep 4805639 = 7208459) B7208459
theorem B3203759 : Blo 2135435 3203759 := bstep (se 1 (by rfl) ⟨2402819, by rfl⟩ : syracuseStep 3203759 = 4805639) B4805639
theorem B2135839 : Blo 2135435 2135839 := bstep (se 1 (by rfl) ⟨1601879, by rfl⟩ : syracuseStep 2135839 = 3203759) B3203759
theorem B3203765 : Blo 2135435 3203765 := bbase (se 5 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 3203765 = 300353) (by norm_num)
theorem B2135843 : Blo 2135435 2135843 := bstep (se 1 (by rfl) ⟨1601882, by rfl⟩ : syracuseStep 2135843 = 3203765) B3203765
theorem B5406365 : Blo 2135435 5406365 := bbase (se 3 (by rfl) ⟨1013693, by rfl⟩ : syracuseStep 5406365 = 2027387) (by norm_num)
theorem B3604243 : Blo 2135435 3604243 := bstep (se 1 (by rfl) ⟨2703182, by rfl⟩ : syracuseStep 3604243 = 5406365) B5406365
theorem B4805657 : Blo 2135435 4805657 := bstep (se 2 (by rfl) ⟨1802121, by rfl⟩ : syracuseStep 4805657 = 3604243) B3604243
theorem B3203771 : Blo 2135435 3203771 := bstep (se 1 (by rfl) ⟨2402828, by rfl⟩ : syracuseStep 3203771 = 4805657) B4805657
theorem B2135847 : Blo 2135435 2135847 := bstep (se 1 (by rfl) ⟨1601885, by rfl⟩ : syracuseStep 2135847 = 3203771) B3203771
theorem B2402833 : Blo 2135435 2402833 := bbase (se 2 (by rfl) ⟨901062, by rfl⟩ : syracuseStep 2402833 = 1802125) (by norm_num)
theorem B3203777 : Blo 2135435 3203777 := bstep (se 2 (by rfl) ⟨1201416, by rfl⟩ : syracuseStep 3203777 = 2402833) B2402833
theorem B2135851 : Blo 2135435 2135851 := bstep (se 1 (by rfl) ⟨1601888, by rfl⟩ : syracuseStep 2135851 = 3203777) B3203777
theorem B4054789 : Blo 2135435 4054789 := bbase (se 4 (by rfl) ⟨380136, by rfl⟩ : syracuseStep 4054789 = 760273) (by norm_num)
theorem B5406385 : Blo 2135435 5406385 := bstep (se 2 (by rfl) ⟨2027394, by rfl⟩ : syracuseStep 5406385 = 4054789) B4054789
theorem B7208513 : Blo 2135435 7208513 := bstep (se 2 (by rfl) ⟨2703192, by rfl⟩ : syracuseStep 7208513 = 5406385) B5406385
theorem B4805675 : Blo 2135435 4805675 := bstep (se 1 (by rfl) ⟨3604256, by rfl⟩ : syracuseStep 4805675 = 7208513) B7208513
theorem B3203783 : Blo 2135435 3203783 := bstep (se 1 (by rfl) ⟨2402837, by rfl⟩ : syracuseStep 3203783 = 4805675) B4805675
theorem B2135855 : Blo 2135435 2135855 := bstep (se 1 (by rfl) ⟨1601891, by rfl⟩ : syracuseStep 2135855 = 3203783) B3203783
theorem B3203789 : Blo 2135435 3203789 := bbase (se 3 (by rfl) ⟨600710, by rfl⟩ : syracuseStep 3203789 = 1201421) (by norm_num)
theorem B2135859 : Blo 2135435 2135859 := bstep (se 1 (by rfl) ⟨1601894, by rfl⟩ : syracuseStep 2135859 = 3203789) B3203789
theorem B4805693 : Blo 2135435 4805693 := bbase (se 3 (by rfl) ⟨901067, by rfl⟩ : syracuseStep 4805693 = 1802135) (by norm_num)
theorem B3203795 : Blo 2135435 3203795 := bstep (se 1 (by rfl) ⟨2402846, by rfl⟩ : syracuseStep 3203795 = 4805693) B4805693
theorem B2135863 : Blo 2135435 2135863 := bstep (se 1 (by rfl) ⟨1601897, by rfl⟩ : syracuseStep 2135863 = 3203795) B3203795
theorem B3604277 : Blo 2135435 3604277 := bbase (se 5 (by rfl) ⟨168950, by rfl⟩ : syracuseStep 3604277 = 337901) (by norm_num)
theorem B2402851 : Blo 2135435 2402851 := bstep (se 1 (by rfl) ⟨1802138, by rfl⟩ : syracuseStep 2402851 = 3604277) B3604277
theorem B3203801 : Blo 2135435 3203801 := bstep (se 2 (by rfl) ⟨1201425, by rfl⟩ : syracuseStep 3203801 = 2402851) B2402851
theorem B2135867 : Blo 2135435 2135867 := bstep (se 1 (by rfl) ⟨1601900, by rfl⟩ : syracuseStep 2135867 = 3203801) B3203801
theorem B6082229 : Blo 2135435 6082229 := bbase (se 5 (by rfl) ⟨285104, by rfl⟩ : syracuseStep 6082229 = 570209) (by norm_num)
theorem B16219277 : Blo 2135435 16219277 := bstep (se 3 (by rfl) ⟨3041114, by rfl⟩ : syracuseStep 16219277 = 6082229) B6082229
theorem B10812851 : Blo 2135435 10812851 := bstep (se 1 (by rfl) ⟨8109638, by rfl⟩ : syracuseStep 10812851 = 16219277) B16219277
theorem B7208567 : Blo 2135435 7208567 := bstep (se 1 (by rfl) ⟨5406425, by rfl⟩ : syracuseStep 7208567 = 10812851) B10812851
theorem B4805711 : Blo 2135435 4805711 := bstep (se 1 (by rfl) ⟨3604283, by rfl⟩ : syracuseStep 4805711 = 7208567) B7208567
theorem B3203807 : Blo 2135435 3203807 := bstep (se 1 (by rfl) ⟨2402855, by rfl⟩ : syracuseStep 3203807 = 4805711) B4805711
theorem B2135871 : Blo 2135435 2135871 := bstep (se 1 (by rfl) ⟨1601903, by rfl⟩ : syracuseStep 2135871 = 3203807) B3203807
theorem B3203813 : Blo 2135435 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B2135875 : Blo 2135435 2135875 := bstep (se 1 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 2135875 = 3203813) B3203813
theorem B2280845 : Blo 2135435 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B6082253 : Blo 2135435 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B4054835 : Blo 2135435 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B2703223 : Blo 2135435 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B3604297 : Blo 2135435 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B4805729 : Blo 2135435 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B3203819 : Blo 2135435 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B2135879 : Blo 2135435 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B2402869 : Blo 2135435 2402869 := bbase (se 5 (by rfl) ⟨112634, by rfl⟩ : syracuseStep 2402869 = 225269) (by norm_num)
theorem B3203825 : Blo 2135435 3203825 := bstep (se 2 (by rfl) ⟨1201434, by rfl⟩ : syracuseStep 3203825 = 2402869) B2402869
theorem B2135883 : Blo 2135435 2135883 := bstep (se 1 (by rfl) ⟨1601912, by rfl⟩ : syracuseStep 2135883 = 3203825) B3203825
theorem B2703233 : Blo 2135435 2703233 := bbase (se 2 (by rfl) ⟨1013712, by rfl⟩ : syracuseStep 2703233 = 2027425) (by norm_num)
theorem B7208621 : Blo 2135435 7208621 := bstep (se 3 (by rfl) ⟨1351616, by rfl⟩ : syracuseStep 7208621 = 2703233) B2703233
theorem B4805747 : Blo 2135435 4805747 := bstep (se 1 (by rfl) ⟨3604310, by rfl⟩ : syracuseStep 4805747 = 7208621) B7208621
theorem B3203831 : Blo 2135435 3203831 := bstep (se 1 (by rfl) ⟨2402873, by rfl⟩ : syracuseStep 3203831 = 4805747) B4805747
theorem B2135887 : Blo 2135435 2135887 := bstep (se 1 (by rfl) ⟨1601915, by rfl⟩ : syracuseStep 2135887 = 3203831) B3203831
theorem B3203837 : Blo 2135435 3203837 := bbase (se 3 (by rfl) ⟨600719, by rfl⟩ : syracuseStep 3203837 = 1201439) (by norm_num)
theorem B2135891 : Blo 2135435 2135891 := bstep (se 1 (by rfl) ⟨1601918, by rfl⟩ : syracuseStep 2135891 = 3203837) B3203837
theorem B4805765 : Blo 2135435 4805765 := bbase (se 4 (by rfl) ⟨450540, by rfl⟩ : syracuseStep 4805765 = 901081) (by norm_num)
theorem B3203843 : Blo 2135435 3203843 := bstep (se 1 (by rfl) ⟨2402882, by rfl⟩ : syracuseStep 3203843 = 4805765) B4805765
theorem B2135895 : Blo 2135435 2135895 := bstep (se 1 (by rfl) ⟨1601921, by rfl⟩ : syracuseStep 2135895 = 3203843) B3203843
theorem B4561733 : Blo 2135435 4561733 := bbase (se 4 (by rfl) ⟨427662, by rfl⟩ : syracuseStep 4561733 = 855325) (by norm_num)
theorem B3041155 : Blo 2135435 3041155 := bstep (se 1 (by rfl) ⟨2280866, by rfl⟩ : syracuseStep 3041155 = 4561733) B4561733
theorem B4054873 : Blo 2135435 4054873 := bstep (se 2 (by rfl) ⟨1520577, by rfl⟩ : syracuseStep 4054873 = 3041155) B3041155
theorem B5406497 : Blo 2135435 5406497 := bstep (se 2 (by rfl) ⟨2027436, by rfl⟩ : syracuseStep 5406497 = 4054873) B4054873
theorem B3604331 : Blo 2135435 3604331 := bstep (se 1 (by rfl) ⟨2703248, by rfl⟩ : syracuseStep 3604331 = 5406497) B5406497
theorem B2402887 : Blo 2135435 2402887 := bstep (se 1 (by rfl) ⟨1802165, by rfl⟩ : syracuseStep 2402887 = 3604331) B3604331
theorem B3203849 : Blo 2135435 3203849 := bstep (se 2 (by rfl) ⟨1201443, by rfl⟩ : syracuseStep 3203849 = 2402887) B2402887
theorem B2135899 : Blo 2135435 2135899 := bstep (se 1 (by rfl) ⟨1601924, by rfl⟩ : syracuseStep 2135899 = 3203849) B3203849
theorem B10813013 : Blo 2135435 10813013 := bbase (se 8 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 10813013 = 126715) (by norm_num)
theorem B7208675 : Blo 2135435 7208675 := bstep (se 1 (by rfl) ⟨5406506, by rfl⟩ : syracuseStep 7208675 = 10813013) B10813013
theorem B4805783 : Blo 2135435 4805783 := bstep (se 1 (by rfl) ⟨3604337, by rfl⟩ : syracuseStep 4805783 = 7208675) B7208675
theorem B3203855 : Blo 2135435 3203855 := bstep (se 1 (by rfl) ⟨2402891, by rfl⟩ : syracuseStep 3203855 = 4805783) B4805783
theorem B2135903 : Blo 2135435 2135903 := bstep (se 1 (by rfl) ⟨1601927, by rfl⟩ : syracuseStep 2135903 = 3203855) B3203855
theorem B3203861 : Blo 2135435 3203861 := bbase (se 6 (by rfl) ⟨75090, by rfl⟩ : syracuseStep 3203861 = 150181) (by norm_num)
theorem B2135907 : Blo 2135435 2135907 := bstep (se 1 (by rfl) ⟨1601930, by rfl⟩ : syracuseStep 2135907 = 3203861) B3203861
theorem B8660213 : Blo 2135435 8660213 := bbase (se 5 (by rfl) ⟨405947, by rfl⟩ : syracuseStep 8660213 = 811895) (by norm_num)
theorem B5773475 : Blo 2135435 5773475 := bstep (se 1 (by rfl) ⟨4330106, by rfl⟩ : syracuseStep 5773475 = 8660213) B8660213
theorem B15395933 : Blo 2135435 15395933 := bstep (se 3 (by rfl) ⟨2886737, by rfl⟩ : syracuseStep 15395933 = 5773475) B5773475
theorem B41055821 : Blo 2135435 41055821 := bstep (se 3 (by rfl) ⟨7697966, by rfl⟩ : syracuseStep 41055821 = 15395933) B15395933
theorem B27370547 : Blo 2135435 27370547 := bstep (se 1 (by rfl) ⟨20527910, by rfl⟩ : syracuseStep 27370547 = 41055821) B41055821
theorem B18247031 : Blo 2135435 18247031 := bstep (se 1 (by rfl) ⟨13685273, by rfl⟩ : syracuseStep 18247031 = 27370547) B27370547
theorem B12164687 : Blo 2135435 12164687 := bstep (se 1 (by rfl) ⟨9123515, by rfl⟩ : syracuseStep 12164687 = 18247031) B18247031
theorem B8109791 : Blo 2135435 8109791 := bstep (se 1 (by rfl) ⟨6082343, by rfl⟩ : syracuseStep 8109791 = 12164687) B12164687
theorem B5406527 : Blo 2135435 5406527 := bstep (se 1 (by rfl) ⟨4054895, by rfl⟩ : syracuseStep 5406527 = 8109791) B8109791
theorem B3604351 : Blo 2135435 3604351 := bstep (se 1 (by rfl) ⟨2703263, by rfl⟩ : syracuseStep 3604351 = 5406527) B5406527
theorem B4805801 : Blo 2135435 4805801 := bstep (se 2 (by rfl) ⟨1802175, by rfl⟩ : syracuseStep 4805801 = 3604351) B3604351
theorem B3203867 : Blo 2135435 3203867 := bstep (se 1 (by rfl) ⟨2402900, by rfl⟩ : syracuseStep 3203867 = 4805801) B4805801
theorem B2135911 : Blo 2135435 2135911 := bstep (se 1 (by rfl) ⟨1601933, by rfl⟩ : syracuseStep 2135911 = 3203867) B3203867
theorem B2402905 : Blo 2135435 2402905 := bbase (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) (by norm_num)
theorem B3203873 : Blo 2135435 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B2135915 : Blo 2135435 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B4871389 : Blo 2135435 4871389 := bbase (se 3 (by rfl) ⟨913385, by rfl⟩ : syracuseStep 4871389 = 1826771) (by norm_num)
theorem B6495185 : Blo 2135435 6495185 := bstep (se 2 (by rfl) ⟨2435694, by rfl⟩ : syracuseStep 6495185 = 4871389) B4871389
theorem B17320493 : Blo 2135435 17320493 := bstep (se 3 (by rfl) ⟨3247592, by rfl⟩ : syracuseStep 17320493 = 6495185) B6495185
theorem B11546995 : Blo 2135435 11546995 := bstep (se 1 (by rfl) ⟨8660246, by rfl⟩ : syracuseStep 11546995 = 17320493) B17320493
theorem B15395993 : Blo 2135435 15395993 := bstep (se 2 (by rfl) ⟨5773497, by rfl⟩ : syracuseStep 15395993 = 11546995) B11546995
theorem B10263995 : Blo 2135435 10263995 := bstep (se 1 (by rfl) ⟨7697996, by rfl⟩ : syracuseStep 10263995 = 15395993) B15395993
theorem B6842663 : Blo 2135435 6842663 := bstep (se 1 (by rfl) ⟨5131997, by rfl⟩ : syracuseStep 6842663 = 10263995) B10263995
theorem B4561775 : Blo 2135435 4561775 := bstep (se 1 (by rfl) ⟨3421331, by rfl⟩ : syracuseStep 4561775 = 6842663) B6842663
theorem B3041183 : Blo 2135435 3041183 := bstep (se 1 (by rfl) ⟨2280887, by rfl⟩ : syracuseStep 3041183 = 4561775) B4561775
theorem B8109821 : Blo 2135435 8109821 := bstep (se 3 (by rfl) ⟨1520591, by rfl⟩ : syracuseStep 8109821 = 3041183) B3041183
theorem B5406547 : Blo 2135435 5406547 := bstep (se 1 (by rfl) ⟨4054910, by rfl⟩ : syracuseStep 5406547 = 8109821) B8109821
theorem B7208729 : Blo 2135435 7208729 := bstep (se 2 (by rfl) ⟨2703273, by rfl⟩ : syracuseStep 7208729 = 5406547) B5406547
theorem B4805819 : Blo 2135435 4805819 := bstep (se 1 (by rfl) ⟨3604364, by rfl⟩ : syracuseStep 4805819 = 7208729) B7208729
theorem B3203879 : Blo 2135435 3203879 := bstep (se 1 (by rfl) ⟨2402909, by rfl⟩ : syracuseStep 3203879 = 4805819) B4805819
theorem B2135919 : Blo 2135435 2135919 := bstep (se 1 (by rfl) ⟨1601939, by rfl⟩ : syracuseStep 2135919 = 3203879) B3203879
theorem B3203885 : Blo 2135435 3203885 := bbase (se 3 (by rfl) ⟨600728, by rfl⟩ : syracuseStep 3203885 = 1201457) (by norm_num)
theorem B2135923 : Blo 2135435 2135923 := bstep (se 1 (by rfl) ⟨1601942, by rfl⟩ : syracuseStep 2135923 = 3203885) B3203885
theorem B4805837 : Blo 2135435 4805837 := bbase (se 3 (by rfl) ⟨901094, by rfl⟩ : syracuseStep 4805837 = 1802189) (by norm_num)
theorem B3203891 : Blo 2135435 3203891 := bstep (se 1 (by rfl) ⟨2402918, by rfl⟩ : syracuseStep 3203891 = 4805837) B4805837
theorem B2135927 : Blo 2135435 2135927 := bstep (se 1 (by rfl) ⟨1601945, by rfl⟩ : syracuseStep 2135927 = 3203891) B3203891
theorem B2703289 : Blo 2135435 2703289 := bbase (se 2 (by rfl) ⟨1013733, by rfl⟩ : syracuseStep 2703289 = 2027467) (by norm_num)
theorem B3604385 : Blo 2135435 3604385 := bstep (se 2 (by rfl) ⟨1351644, by rfl⟩ : syracuseStep 3604385 = 2703289) B2703289
theorem B2402923 : Blo 2135435 2402923 := bstep (se 1 (by rfl) ⟨1802192, by rfl⟩ : syracuseStep 2402923 = 3604385) B3604385
theorem B3203897 : Blo 2135435 3203897 := bstep (se 2 (by rfl) ⟨1201461, by rfl⟩ : syracuseStep 3203897 = 2402923) B2402923
theorem B2135931 : Blo 2135435 2135931 := bstep (se 1 (by rfl) ⟨1601948, by rfl⟩ : syracuseStep 2135931 = 3203897) B3203897
theorem B7698053 : Blo 2135435 7698053 := bbase (se 4 (by rfl) ⟨721692, by rfl⟩ : syracuseStep 7698053 = 1443385) (by norm_num)
theorem B5132035 : Blo 2135435 5132035 := bstep (se 1 (by rfl) ⟨3849026, by rfl⟩ : syracuseStep 5132035 = 7698053) B7698053
theorem B6842713 : Blo 2135435 6842713 := bstep (se 2 (by rfl) ⟨2566017, by rfl⟩ : syracuseStep 6842713 = 5132035) B5132035
theorem B9123617 : Blo 2135435 9123617 := bstep (se 2 (by rfl) ⟨3421356, by rfl⟩ : syracuseStep 9123617 = 6842713) B6842713
theorem B24329645 : Blo 2135435 24329645 := bstep (se 3 (by rfl) ⟨4561808, by rfl⟩ : syracuseStep 24329645 = 9123617) B9123617
theorem B16219763 : Blo 2135435 16219763 := bstep (se 1 (by rfl) ⟨12164822, by rfl⟩ : syracuseStep 16219763 = 24329645) B24329645
theorem B10813175 : Blo 2135435 10813175 := bstep (se 1 (by rfl) ⟨8109881, by rfl⟩ : syracuseStep 10813175 = 16219763) B16219763
theorem B7208783 : Blo 2135435 7208783 := bstep (se 1 (by rfl) ⟨5406587, by rfl⟩ : syracuseStep 7208783 = 10813175) B10813175
theorem B4805855 : Blo 2135435 4805855 := bstep (se 1 (by rfl) ⟨3604391, by rfl⟩ : syracuseStep 4805855 = 7208783) B7208783
theorem B3203903 : Blo 2135435 3203903 := bstep (se 1 (by rfl) ⟨2402927, by rfl⟩ : syracuseStep 3203903 = 4805855) B4805855
theorem B2135935 : Blo 2135435 2135935 := bstep (se 1 (by rfl) ⟨1601951, by rfl⟩ : syracuseStep 2135935 = 3203903) B3203903
theorem B3203909 : Blo 2135435 3203909 := bbase (se 4 (by rfl) ⟨300366, by rfl⟩ : syracuseStep 3203909 = 600733) (by norm_num)
theorem B2135939 : Blo 2135435 2135939 := bstep (se 1 (by rfl) ⟨1601954, by rfl⟩ : syracuseStep 2135939 = 3203909) B3203909
theorem B3604405 : Blo 2135435 3604405 := bbase (se 5 (by rfl) ⟨168956, by rfl⟩ : syracuseStep 3604405 = 337913) (by norm_num)
theorem B4805873 : Blo 2135435 4805873 := bstep (se 2 (by rfl) ⟨1802202, by rfl⟩ : syracuseStep 4805873 = 3604405) B3604405
theorem B3203915 : Blo 2135435 3203915 := bstep (se 1 (by rfl) ⟨2402936, by rfl⟩ : syracuseStep 3203915 = 4805873) B4805873
theorem B2135943 : Blo 2135435 2135943 := bstep (se 1 (by rfl) ⟨1601957, by rfl⟩ : syracuseStep 2135943 = 3203915) B3203915
theorem B2402941 : Blo 2135435 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B3203921 : Blo 2135435 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B2135947 : Blo 2135435 2135947 := bstep (se 1 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 2135947 = 3203921) B3203921
theorem B7208837 : Blo 2135435 7208837 := bbase (se 4 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 7208837 = 1351657) (by norm_num)
theorem B4805891 : Blo 2135435 4805891 := bstep (se 1 (by rfl) ⟨3604418, by rfl⟩ : syracuseStep 4805891 = 7208837) B7208837
theorem B3203927 : Blo 2135435 3203927 := bstep (se 1 (by rfl) ⟨2402945, by rfl⟩ : syracuseStep 3203927 = 4805891) B4805891
theorem B2135951 : Blo 2135435 2135951 := bstep (se 1 (by rfl) ⟨1601963, by rfl⟩ : syracuseStep 2135951 = 3203927) B3203927
theorem B3203933 : Blo 2135435 3203933 := bbase (se 3 (by rfl) ⟨600737, by rfl⟩ : syracuseStep 3203933 = 1201475) (by norm_num)
theorem B2135955 : Blo 2135435 2135955 := bstep (se 1 (by rfl) ⟨1601966, by rfl⟩ : syracuseStep 2135955 = 3203933) B3203933
theorem B4805909 : Blo 2135435 4805909 := bbase (se 6 (by rfl) ⟨112638, by rfl⟩ : syracuseStep 4805909 = 225277) (by norm_num)
theorem B3203939 : Blo 2135435 3203939 := bstep (se 1 (by rfl) ⟨2402954, by rfl⟩ : syracuseStep 3203939 = 4805909) B4805909
theorem B2135959 : Blo 2135435 2135959 := bstep (se 1 (by rfl) ⟨1601969, by rfl⟩ : syracuseStep 2135959 = 3203939) B3203939
theorem B8109989 : Blo 2135435 8109989 := bbase (se 4 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 8109989 = 1520623) (by norm_num)
theorem B5406659 : Blo 2135435 5406659 := bstep (se 1 (by rfl) ⟨4054994, by rfl⟩ : syracuseStep 5406659 = 8109989) B8109989
theorem B3604439 : Blo 2135435 3604439 := bstep (se 1 (by rfl) ⟨2703329, by rfl⟩ : syracuseStep 3604439 = 5406659) B5406659
theorem B2402959 : Blo 2135435 2402959 := bstep (se 1 (by rfl) ⟨1802219, by rfl⟩ : syracuseStep 2402959 = 3604439) B3604439
theorem B3203945 : Blo 2135435 3203945 := bstep (se 2 (by rfl) ⟨1201479, by rfl⟩ : syracuseStep 3203945 = 2402959) B2402959
theorem B2135963 : Blo 2135435 2135963 := bstep (se 1 (by rfl) ⟨1601972, by rfl⟩ : syracuseStep 2135963 = 3203945) B3203945
theorem B4561877 : Blo 2135435 4561877 := bbase (se 7 (by rfl) ⟨53459, by rfl⟩ : syracuseStep 4561877 = 106919) (by norm_num)
theorem B12165005 : Blo 2135435 12165005 := bstep (se 3 (by rfl) ⟨2280938, by rfl⟩ : syracuseStep 12165005 = 4561877) B4561877
theorem B8110003 : Blo 2135435 8110003 := bstep (se 1 (by rfl) ⟨6082502, by rfl⟩ : syracuseStep 8110003 = 12165005) B12165005
theorem B10813337 : Blo 2135435 10813337 := bstep (se 2 (by rfl) ⟨4055001, by rfl⟩ : syracuseStep 10813337 = 8110003) B8110003
theorem B7208891 : Blo 2135435 7208891 := bstep (se 1 (by rfl) ⟨5406668, by rfl⟩ : syracuseStep 7208891 = 10813337) B10813337
theorem B4805927 : Blo 2135435 4805927 := bstep (se 1 (by rfl) ⟨3604445, by rfl⟩ : syracuseStep 4805927 = 7208891) B7208891
theorem B3203951 : Blo 2135435 3203951 := bstep (se 1 (by rfl) ⟨2402963, by rfl⟩ : syracuseStep 3203951 = 4805927) B4805927
theorem B2135967 : Blo 2135435 2135967 := bstep (se 1 (by rfl) ⟨1601975, by rfl⟩ : syracuseStep 2135967 = 3203951) B3203951
theorem B3203957 : Blo 2135435 3203957 := bbase (se 5 (by rfl) ⟨150185, by rfl⟩ : syracuseStep 3203957 = 300371) (by norm_num)
theorem B2135971 : Blo 2135435 2135971 := bstep (se 1 (by rfl) ⟨1601978, by rfl⟩ : syracuseStep 2135971 = 3203957) B3203957
theorem B17320949 : Blo 2135435 17320949 := bbase (se 5 (by rfl) ⟨811919, by rfl⟩ : syracuseStep 17320949 = 1623839) (by norm_num)
theorem B11547299 : Blo 2135435 11547299 := bstep (se 1 (by rfl) ⟨8660474, by rfl⟩ : syracuseStep 11547299 = 17320949) B17320949
theorem B7698199 : Blo 2135435 7698199 := bstep (se 1 (by rfl) ⟨5773649, by rfl⟩ : syracuseStep 7698199 = 11547299) B11547299
theorem B10264265 : Blo 2135435 10264265 := bstep (se 2 (by rfl) ⟨3849099, by rfl⟩ : syracuseStep 10264265 = 7698199) B7698199
theorem B6842843 : Blo 2135435 6842843 := bstep (se 1 (by rfl) ⟨5132132, by rfl⟩ : syracuseStep 6842843 = 10264265) B10264265
theorem B4561895 : Blo 2135435 4561895 := bstep (se 1 (by rfl) ⟨3421421, by rfl⟩ : syracuseStep 4561895 = 6842843) B6842843
theorem B3041263 : Blo 2135435 3041263 := bstep (se 1 (by rfl) ⟨2280947, by rfl⟩ : syracuseStep 3041263 = 4561895) B4561895
theorem B4055017 : Blo 2135435 4055017 := bstep (se 2 (by rfl) ⟨1520631, by rfl⟩ : syracuseStep 4055017 = 3041263) B3041263
theorem B5406689 : Blo 2135435 5406689 := bstep (se 2 (by rfl) ⟨2027508, by rfl⟩ : syracuseStep 5406689 = 4055017) B4055017
theorem B3604459 : Blo 2135435 3604459 := bstep (se 1 (by rfl) ⟨2703344, by rfl⟩ : syracuseStep 3604459 = 5406689) B5406689
theorem B4805945 : Blo 2135435 4805945 := bstep (se 2 (by rfl) ⟨1802229, by rfl⟩ : syracuseStep 4805945 = 3604459) B3604459
theorem B3203963 : Blo 2135435 3203963 := bstep (se 1 (by rfl) ⟨2402972, by rfl⟩ : syracuseStep 3203963 = 4805945) B4805945
theorem B2135975 : Blo 2135435 2135975 := bstep (se 1 (by rfl) ⟨1601981, by rfl⟩ : syracuseStep 2135975 = 3203963) B3203963
theorem B2402977 : Blo 2135435 2402977 := bbase (se 2 (by rfl) ⟨901116, by rfl⟩ : syracuseStep 2402977 = 1802233) (by norm_num)
theorem B3203969 : Blo 2135435 3203969 := bstep (se 2 (by rfl) ⟨1201488, by rfl⟩ : syracuseStep 3203969 = 2402977) B2402977
theorem B2135979 : Blo 2135435 2135979 := bstep (se 1 (by rfl) ⟨1601984, by rfl⟩ : syracuseStep 2135979 = 3203969) B3203969
theorem B5406709 : Blo 2135435 5406709 := bbase (se 5 (by rfl) ⟨253439, by rfl⟩ : syracuseStep 5406709 = 506879) (by norm_num)
theorem B7208945 : Blo 2135435 7208945 := bstep (se 2 (by rfl) ⟨2703354, by rfl⟩ : syracuseStep 7208945 = 5406709) B5406709
theorem B4805963 : Blo 2135435 4805963 := bstep (se 1 (by rfl) ⟨3604472, by rfl⟩ : syracuseStep 4805963 = 7208945) B7208945
theorem B3203975 : Blo 2135435 3203975 := bstep (se 1 (by rfl) ⟨2402981, by rfl⟩ : syracuseStep 3203975 = 4805963) B4805963
theorem B2135983 : Blo 2135435 2135983 := bstep (se 1 (by rfl) ⟨1601987, by rfl⟩ : syracuseStep 2135983 = 3203975) B3203975
theorem B3203981 : Blo 2135435 3203981 := bbase (se 3 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 3203981 = 1201493) (by norm_num)
theorem B2135987 : Blo 2135435 2135987 := bstep (se 1 (by rfl) ⟨1601990, by rfl⟩ : syracuseStep 2135987 = 3203981) B3203981
theorem B4805981 : Blo 2135435 4805981 := bbase (se 3 (by rfl) ⟨901121, by rfl⟩ : syracuseStep 4805981 = 1802243) (by norm_num)
theorem B3203987 : Blo 2135435 3203987 := bstep (se 1 (by rfl) ⟨2402990, by rfl⟩ : syracuseStep 3203987 = 4805981) B4805981
theorem B2135991 : Blo 2135435 2135991 := bstep (se 1 (by rfl) ⟨1601993, by rfl⟩ : syracuseStep 2135991 = 3203987) B3203987
theorem B3604493 : Blo 2135435 3604493 := bbase (se 3 (by rfl) ⟨675842, by rfl⟩ : syracuseStep 3604493 = 1351685) (by norm_num)
theorem B2402995 : Blo 2135435 2402995 := bstep (se 1 (by rfl) ⟨1802246, by rfl⟩ : syracuseStep 2402995 = 3604493) B3604493
theorem B3203993 : Blo 2135435 3203993 := bstep (se 2 (by rfl) ⟨1201497, by rfl⟩ : syracuseStep 3203993 = 2402995) B2402995
theorem B2135995 : Blo 2135435 2135995 := bstep (se 1 (by rfl) ⟨1601996, by rfl⟩ : syracuseStep 2135995 = 3203993) B3203993
theorem B5132189 : Blo 2135435 5132189 := bbase (se 3 (by rfl) ⟨962285, by rfl⟩ : syracuseStep 5132189 = 1924571) (by norm_num)
theorem B3421459 : Blo 2135435 3421459 := bstep (se 1 (by rfl) ⟨2566094, by rfl⟩ : syracuseStep 3421459 = 5132189) B5132189
theorem B18247781 : Blo 2135435 18247781 := bstep (se 4 (by rfl) ⟨1710729, by rfl⟩ : syracuseStep 18247781 = 3421459) B3421459
theorem B12165187 : Blo 2135435 12165187 := bstep (se 1 (by rfl) ⟨9123890, by rfl⟩ : syracuseStep 12165187 = 18247781) B18247781
theorem B16220249 : Blo 2135435 16220249 := bstep (se 2 (by rfl) ⟨6082593, by rfl⟩ : syracuseStep 16220249 = 12165187) B12165187
theorem B10813499 : Blo 2135435 10813499 := bstep (se 1 (by rfl) ⟨8110124, by rfl⟩ : syracuseStep 10813499 = 16220249) B16220249
theorem B7208999 : Blo 2135435 7208999 := bstep (se 1 (by rfl) ⟨5406749, by rfl⟩ : syracuseStep 7208999 = 10813499) B10813499
theorem B4805999 : Blo 2135435 4805999 := bstep (se 1 (by rfl) ⟨3604499, by rfl⟩ : syracuseStep 4805999 = 7208999) B7208999
theorem B3203999 : Blo 2135435 3203999 := bstep (se 1 (by rfl) ⟨2402999, by rfl⟩ : syracuseStep 3203999 = 4805999) B4805999
theorem B2135999 : Blo 2135435 2135999 := bstep (se 1 (by rfl) ⟨1601999, by rfl⟩ : syracuseStep 2135999 = 3203999) B3203999
theorem B3204005 : Blo 2135435 3204005 := bbase (se 4 (by rfl) ⟨300375, by rfl⟩ : syracuseStep 3204005 = 600751) (by norm_num)
theorem B2136003 : Blo 2135435 2136003 := bstep (se 1 (by rfl) ⟨1602002, by rfl⟩ : syracuseStep 2136003 = 3204005) B3204005
theorem B2703385 : Blo 2135435 2703385 := bbase (se 2 (by rfl) ⟨1013769, by rfl⟩ : syracuseStep 2703385 = 2027539) (by norm_num)
theorem B3604513 : Blo 2135435 3604513 := bstep (se 2 (by rfl) ⟨1351692, by rfl⟩ : syracuseStep 3604513 = 2703385) B2703385
theorem B4806017 : Blo 2135435 4806017 := bstep (se 2 (by rfl) ⟨1802256, by rfl⟩ : syracuseStep 4806017 = 3604513) B3604513
theorem B3204011 : Blo 2135435 3204011 := bstep (se 1 (by rfl) ⟨2403008, by rfl⟩ : syracuseStep 3204011 = 4806017) B4806017
theorem B2136007 : Blo 2135435 2136007 := bstep (se 1 (by rfl) ⟨1602005, by rfl⟩ : syracuseStep 2136007 = 3204011) B3204011
theorem B2403013 : Blo 2135435 2403013 := bbase (se 4 (by rfl) ⟨225282, by rfl⟩ : syracuseStep 2403013 = 450565) (by norm_num)
theorem B3204017 : Blo 2135435 3204017 := bstep (se 2 (by rfl) ⟨1201506, by rfl⟩ : syracuseStep 3204017 = 2403013) B2403013
theorem B2136011 : Blo 2135435 2136011 := bstep (se 1 (by rfl) ⟨1602008, by rfl⟩ : syracuseStep 2136011 = 3204017) B3204017
theorem B4055093 : Blo 2135435 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B2703395 : Blo 2135435 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B7209053 : Blo 2135435 7209053 := bstep (se 3 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 7209053 = 2703395) B2703395
theorem B4806035 : Blo 2135435 4806035 := bstep (se 1 (by rfl) ⟨3604526, by rfl⟩ : syracuseStep 4806035 = 7209053) B7209053
theorem B3204023 : Blo 2135435 3204023 := bstep (se 1 (by rfl) ⟨2403017, by rfl⟩ : syracuseStep 3204023 = 4806035) B4806035
theorem B2136015 : Blo 2135435 2136015 := bstep (se 1 (by rfl) ⟨1602011, by rfl⟩ : syracuseStep 2136015 = 3204023) B3204023
theorem B3204029 : Blo 2135435 3204029 := bbase (se 3 (by rfl) ⟨600755, by rfl⟩ : syracuseStep 3204029 = 1201511) (by norm_num)
theorem B2136019 : Blo 2135435 2136019 := bstep (se 1 (by rfl) ⟨1602014, by rfl⟩ : syracuseStep 2136019 = 3204029) B3204029
theorem B4806053 : Blo 2135435 4806053 := bbase (se 4 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 4806053 = 901135) (by norm_num)
theorem B3204035 : Blo 2135435 3204035 := bstep (se 1 (by rfl) ⟨2403026, by rfl⟩ : syracuseStep 3204035 = 4806053) B4806053
theorem B2136023 : Blo 2135435 2136023 := bstep (se 1 (by rfl) ⟨1602017, by rfl⟩ : syracuseStep 2136023 = 3204035) B3204035
theorem B5406821 : Blo 2135435 5406821 := bbase (se 4 (by rfl) ⟨506889, by rfl⟩ : syracuseStep 5406821 = 1013779) (by norm_num)
theorem B3604547 : Blo 2135435 3604547 := bstep (se 1 (by rfl) ⟨2703410, by rfl⟩ : syracuseStep 3604547 = 5406821) B5406821
theorem B2403031 : Blo 2135435 2403031 := bstep (se 1 (by rfl) ⟨1802273, by rfl⟩ : syracuseStep 2403031 = 3604547) B3604547
theorem B3204041 : Blo 2135435 3204041 := bstep (se 2 (by rfl) ⟨1201515, by rfl⟩ : syracuseStep 3204041 = 2403031) B2403031
theorem B2136027 : Blo 2135435 2136027 := bstep (se 1 (by rfl) ⟨1602020, by rfl⟩ : syracuseStep 2136027 = 3204041) B3204041
theorem B2312129 : Blo 2135435 2312129 := bbase (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) (by norm_num)
theorem B6165677 : Blo 2135435 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B16441805 : Blo 2135435 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B10961203 : Blo 2135435 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B14614937 : Blo 2135435 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B9743291 : Blo 2135435 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B6495527 : Blo 2135435 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B4330351 : Blo 2135435 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B5773801 : Blo 2135435 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B7698401 : Blo 2135435 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B5132267 : Blo 2135435 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B3421511 : Blo 2135435 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B2281007 : Blo 2135435 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B6082685 : Blo 2135435 6082685 := bstep (se 3 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 6082685 = 2281007) B2281007
theorem B4055123 : Blo 2135435 4055123 := bstep (se 1 (by rfl) ⟨3041342, by rfl⟩ : syracuseStep 4055123 = 6082685) B6082685
theorem B10813661 : Blo 2135435 10813661 := bstep (se 3 (by rfl) ⟨2027561, by rfl⟩ : syracuseStep 10813661 = 4055123) B4055123
theorem B7209107 : Blo 2135435 7209107 := bstep (se 1 (by rfl) ⟨5406830, by rfl⟩ : syracuseStep 7209107 = 10813661) B10813661
theorem B4806071 : Blo 2135435 4806071 := bstep (se 1 (by rfl) ⟨3604553, by rfl⟩ : syracuseStep 4806071 = 7209107) B7209107
theorem B3204047 : Blo 2135435 3204047 := bstep (se 1 (by rfl) ⟨2403035, by rfl⟩ : syracuseStep 3204047 = 4806071) B4806071
theorem B2136031 : Blo 2135435 2136031 := bstep (se 1 (by rfl) ⟨1602023, by rfl⟩ : syracuseStep 2136031 = 3204047) B3204047
theorem B3204053 : Blo 2135435 3204053 := bbase (se 7 (by rfl) ⟨37547, by rfl⟩ : syracuseStep 3204053 = 75095) (by norm_num)
theorem B2136035 : Blo 2135435 2136035 := bstep (se 1 (by rfl) ⟨1602026, by rfl⟩ : syracuseStep 2136035 = 3204053) B3204053
theorem B8110277 : Blo 2135435 8110277 := bbase (se 4 (by rfl) ⟨760338, by rfl⟩ : syracuseStep 8110277 = 1520677) (by norm_num)
theorem B5406851 : Blo 2135435 5406851 := bstep (se 1 (by rfl) ⟨4055138, by rfl⟩ : syracuseStep 5406851 = 8110277) B8110277
theorem B3604567 : Blo 2135435 3604567 := bstep (se 1 (by rfl) ⟨2703425, by rfl⟩ : syracuseStep 3604567 = 5406851) B5406851
theorem B4806089 : Blo 2135435 4806089 := bstep (se 2 (by rfl) ⟨1802283, by rfl⟩ : syracuseStep 4806089 = 3604567) B3604567
theorem B3204059 : Blo 2135435 3204059 := bstep (se 1 (by rfl) ⟨2403044, by rfl⟩ : syracuseStep 3204059 = 4806089) B4806089
theorem B2136039 : Blo 2135435 2136039 := bstep (se 1 (by rfl) ⟨1602029, by rfl⟩ : syracuseStep 2136039 = 3204059) B3204059
theorem B2403049 : Blo 2135435 2403049 := bbase (se 2 (by rfl) ⟨901143, by rfl⟩ : syracuseStep 2403049 = 1802287) (by norm_num)
theorem B3204065 : Blo 2135435 3204065 := bstep (se 2 (by rfl) ⟨1201524, by rfl⟩ : syracuseStep 3204065 = 2403049) B2403049
theorem B2136043 : Blo 2135435 2136043 := bstep (se 1 (by rfl) ⟨1602032, by rfl⟩ : syracuseStep 2136043 = 3204065) B3204065
theorem B12165461 : Blo 2135435 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B8110307 : Blo 2135435 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B5406871 : Blo 2135435 5406871 := bstep (se 1 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 5406871 = 8110307) B8110307
theorem B7209161 : Blo 2135435 7209161 := bstep (se 2 (by rfl) ⟨2703435, by rfl⟩ : syracuseStep 7209161 = 5406871) B5406871
theorem B4806107 : Blo 2135435 4806107 := bstep (se 1 (by rfl) ⟨3604580, by rfl⟩ : syracuseStep 4806107 = 7209161) B7209161
theorem B3204071 : Blo 2135435 3204071 := bstep (se 1 (by rfl) ⟨2403053, by rfl⟩ : syracuseStep 3204071 = 4806107) B4806107
theorem B2136047 : Blo 2135435 2136047 := bstep (se 1 (by rfl) ⟨1602035, by rfl⟩ : syracuseStep 2136047 = 3204071) B3204071
theorem B3204077 : Blo 2135435 3204077 := bbase (se 3 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 3204077 = 1201529) (by norm_num)
theorem B2136051 : Blo 2135435 2136051 := bstep (se 1 (by rfl) ⟨1602038, by rfl⟩ : syracuseStep 2136051 = 3204077) B3204077
theorem B4806125 : Blo 2135435 4806125 := bbase (se 3 (by rfl) ⟨901148, by rfl⟩ : syracuseStep 4806125 = 1802297) (by norm_num)
theorem B3204083 : Blo 2135435 3204083 := bstep (se 1 (by rfl) ⟨2403062, by rfl⟩ : syracuseStep 3204083 = 4806125) B4806125
theorem B2136055 : Blo 2135435 2136055 := bstep (se 1 (by rfl) ⟨1602041, by rfl⟩ : syracuseStep 2136055 = 3204083) B3204083
theorem B2777725 : Blo 2135435 2777725 := bbase (se 3 (by rfl) ⟨520823, by rfl⟩ : syracuseStep 2777725 = 1041647) (by norm_num)
theorem B14814533 : Blo 2135435 14814533 := bstep (se 4 (by rfl) ⟨1388862, by rfl⟩ : syracuseStep 14814533 = 2777725) B2777725
theorem B39505421 : Blo 2135435 39505421 := bstep (se 3 (by rfl) ⟨7407266, by rfl⟩ : syracuseStep 39505421 = 14814533) B14814533
theorem B26336947 : Blo 2135435 26336947 := bstep (se 1 (by rfl) ⟨19752710, by rfl⟩ : syracuseStep 26336947 = 39505421) B39505421
theorem B35115929 : Blo 2135435 35115929 := bstep (se 2 (by rfl) ⟨13168473, by rfl⟩ : syracuseStep 35115929 = 26336947) B26336947
theorem B23410619 : Blo 2135435 23410619 := bstep (se 1 (by rfl) ⟨17557964, by rfl⟩ : syracuseStep 23410619 = 35115929) B35115929
theorem B15607079 : Blo 2135435 15607079 := bstep (se 1 (by rfl) ⟨11705309, by rfl⟩ : syracuseStep 15607079 = 23410619) B23410619
theorem B10404719 : Blo 2135435 10404719 := bstep (se 1 (by rfl) ⟨7803539, by rfl⟩ : syracuseStep 10404719 = 15607079) B15607079
theorem B6936479 : Blo 2135435 6936479 := bstep (se 1 (by rfl) ⟨5202359, by rfl⟩ : syracuseStep 6936479 = 10404719) B10404719
theorem B4624319 : Blo 2135435 4624319 := bstep (se 1 (by rfl) ⟨3468239, by rfl⟩ : syracuseStep 4624319 = 6936479) B6936479
theorem B3082879 : Blo 2135435 3082879 := bstep (se 1 (by rfl) ⟨2312159, by rfl⟩ : syracuseStep 3082879 = 4624319) B4624319
theorem B16442021 : Blo 2135435 16442021 := bstep (se 4 (by rfl) ⟨1541439, by rfl⟩ : syracuseStep 16442021 = 3082879) B3082879
theorem B10961347 : Blo 2135435 10961347 := bstep (se 1 (by rfl) ⟨8221010, by rfl⟩ : syracuseStep 10961347 = 16442021) B16442021
theorem B14615129 : Blo 2135435 14615129 := bstep (se 2 (by rfl) ⟨5480673, by rfl⟩ : syracuseStep 14615129 = 10961347) B10961347
theorem B9743419 : Blo 2135435 9743419 := bstep (se 1 (by rfl) ⟨7307564, by rfl⟩ : syracuseStep 9743419 = 14615129) B14615129
theorem B12991225 : Blo 2135435 12991225 := bstep (se 2 (by rfl) ⟨4871709, by rfl⟩ : syracuseStep 12991225 = 9743419) B9743419
theorem B17321633 : Blo 2135435 17321633 := bstep (se 2 (by rfl) ⟨6495612, by rfl⟩ : syracuseStep 17321633 = 12991225) B12991225
theorem B11547755 : Blo 2135435 11547755 := bstep (se 1 (by rfl) ⟨8660816, by rfl⟩ : syracuseStep 11547755 = 17321633) B17321633
theorem B7698503 : Blo 2135435 7698503 := bstep (se 1 (by rfl) ⟨5773877, by rfl⟩ : syracuseStep 7698503 = 11547755) B11547755
theorem B5132335 : Blo 2135435 5132335 := bstep (se 1 (by rfl) ⟨3849251, by rfl⟩ : syracuseStep 5132335 = 7698503) B7698503
theorem B6843113 : Blo 2135435 6843113 := bstep (se 2 (by rfl) ⟨2566167, by rfl⟩ : syracuseStep 6843113 = 5132335) B5132335
theorem B4562075 : Blo 2135435 4562075 := bstep (se 1 (by rfl) ⟨3421556, by rfl⟩ : syracuseStep 4562075 = 6843113) B6843113
theorem B3041383 : Blo 2135435 3041383 := bstep (se 1 (by rfl) ⟨2281037, by rfl⟩ : syracuseStep 3041383 = 4562075) B4562075
theorem B4055177 : Blo 2135435 4055177 := bstep (se 2 (by rfl) ⟨1520691, by rfl⟩ : syracuseStep 4055177 = 3041383) B3041383
theorem B2703451 : Blo 2135435 2703451 := bstep (se 1 (by rfl) ⟨2027588, by rfl⟩ : syracuseStep 2703451 = 4055177) B4055177
theorem B3604601 : Blo 2135435 3604601 := bstep (se 2 (by rfl) ⟨1351725, by rfl⟩ : syracuseStep 3604601 = 2703451) B2703451
theorem B2403067 : Blo 2135435 2403067 := bstep (se 1 (by rfl) ⟨1802300, by rfl⟩ : syracuseStep 2403067 = 3604601) B3604601
theorem B3204089 : Blo 2135435 3204089 := bstep (se 2 (by rfl) ⟨1201533, by rfl⟩ : syracuseStep 3204089 = 2403067) B2403067
theorem B2136059 : Blo 2135435 2136059 := bstep (se 1 (by rfl) ⟨1602044, by rfl⟩ : syracuseStep 2136059 = 3204089) B3204089
theorem B4871717 : Blo 2135435 4871717 := bbase (se 4 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 4871717 = 913447) (by norm_num)
theorem B3247811 : Blo 2135435 3247811 := bstep (se 1 (by rfl) ⟨2435858, by rfl⟩ : syracuseStep 3247811 = 4871717) B4871717
theorem B2165207 : Blo 2135435 2165207 := bstep (se 1 (by rfl) ⟨1623905, by rfl⟩ : syracuseStep 2165207 = 3247811) B3247811
theorem B5773885 : Blo 2135435 5773885 := bstep (se 3 (by rfl) ⟨1082603, by rfl⟩ : syracuseStep 5773885 = 2165207) B2165207
theorem B123176213 : Blo 2135435 123176213 := bstep (se 6 (by rfl) ⟨2886942, by rfl⟩ : syracuseStep 123176213 = 5773885) B5773885
theorem B82117475 : Blo 2135435 82117475 := bstep (se 1 (by rfl) ⟨61588106, by rfl⟩ : syracuseStep 82117475 = 123176213) B123176213
theorem B54744983 : Blo 2135435 54744983 := bstep (se 1 (by rfl) ⟨41058737, by rfl⟩ : syracuseStep 54744983 = 82117475) B82117475
theorem B36496655 : Blo 2135435 36496655 := bstep (se 1 (by rfl) ⟨27372491, by rfl⟩ : syracuseStep 36496655 = 54744983) B54744983
theorem B24331103 : Blo 2135435 24331103 := bstep (se 1 (by rfl) ⟨18248327, by rfl⟩ : syracuseStep 24331103 = 36496655) B36496655
theorem B16220735 : Blo 2135435 16220735 := bstep (se 1 (by rfl) ⟨12165551, by rfl⟩ : syracuseStep 16220735 = 24331103) B24331103
theorem B10813823 : Blo 2135435 10813823 := bstep (se 1 (by rfl) ⟨8110367, by rfl⟩ : syracuseStep 10813823 = 16220735) B16220735
theorem B7209215 : Blo 2135435 7209215 := bstep (se 1 (by rfl) ⟨5406911, by rfl⟩ : syracuseStep 7209215 = 10813823) B10813823
theorem B4806143 : Blo 2135435 4806143 := bstep (se 1 (by rfl) ⟨3604607, by rfl⟩ : syracuseStep 4806143 = 7209215) B7209215
theorem B3204095 : Blo 2135435 3204095 := bstep (se 1 (by rfl) ⟨2403071, by rfl⟩ : syracuseStep 3204095 = 4806143) B4806143
theorem B2136063 : Blo 2135435 2136063 := bstep (se 1 (by rfl) ⟨1602047, by rfl⟩ : syracuseStep 2136063 = 3204095) B3204095
theorem B3204101 : Blo 2135435 3204101 := bbase (se 4 (by rfl) ⟨300384, by rfl⟩ : syracuseStep 3204101 = 600769) (by norm_num)
theorem B2136067 : Blo 2135435 2136067 := bstep (se 1 (by rfl) ⟨1602050, by rfl⟩ : syracuseStep 2136067 = 3204101) B3204101
theorem B3604621 : Blo 2135435 3604621 := bbase (se 3 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 3604621 = 1351733) (by norm_num)
theorem B4806161 : Blo 2135435 4806161 := bstep (se 2 (by rfl) ⟨1802310, by rfl⟩ : syracuseStep 4806161 = 3604621) B3604621
theorem B3204107 : Blo 2135435 3204107 := bstep (se 1 (by rfl) ⟨2403080, by rfl⟩ : syracuseStep 3204107 = 4806161) B4806161
theorem B2136071 : Blo 2135435 2136071 := bstep (se 1 (by rfl) ⟨1602053, by rfl⟩ : syracuseStep 2136071 = 3204107) B3204107
theorem B2403085 : Blo 2135435 2403085 := bbase (se 3 (by rfl) ⟨450578, by rfl⟩ : syracuseStep 2403085 = 901157) (by norm_num)
theorem B3204113 : Blo 2135435 3204113 := bstep (se 2 (by rfl) ⟨1201542, by rfl⟩ : syracuseStep 3204113 = 2403085) B2403085
theorem B2136075 : Blo 2135435 2136075 := bstep (se 1 (by rfl) ⟨1602056, by rfl⟩ : syracuseStep 2136075 = 3204113) B3204113
theorem B7209269 : Blo 2135435 7209269 := bbase (se 5 (by rfl) ⟨337934, by rfl⟩ : syracuseStep 7209269 = 675869) (by norm_num)
theorem B4806179 : Blo 2135435 4806179 := bstep (se 1 (by rfl) ⟨3604634, by rfl⟩ : syracuseStep 4806179 = 7209269) B7209269
theorem B3204119 : Blo 2135435 3204119 := bstep (se 1 (by rfl) ⟨2403089, by rfl⟩ : syracuseStep 3204119 = 4806179) B4806179
theorem B2136079 : Blo 2135435 2136079 := bstep (se 1 (by rfl) ⟨1602059, by rfl⟩ : syracuseStep 2136079 = 3204119) B3204119
theorem B3204125 : Blo 2135435 3204125 := bbase (se 3 (by rfl) ⟨600773, by rfl⟩ : syracuseStep 3204125 = 1201547) (by norm_num)
theorem B2136083 : Blo 2135435 2136083 := bstep (se 1 (by rfl) ⟨1602062, by rfl⟩ : syracuseStep 2136083 = 3204125) B3204125
theorem B4806197 : Blo 2135435 4806197 := bbase (se 5 (by rfl) ⟨225290, by rfl⟩ : syracuseStep 4806197 = 450581) (by norm_num)
theorem B3204131 : Blo 2135435 3204131 := bstep (se 1 (by rfl) ⟨2403098, by rfl⟩ : syracuseStep 3204131 = 4806197) B4806197
theorem B2136087 : Blo 2135435 2136087 := bstep (se 1 (by rfl) ⟨1602065, by rfl⟩ : syracuseStep 2136087 = 3204131) B3204131
theorem B3653837 : Blo 2135435 3653837 := bbase (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) (by norm_num)
theorem B2435891 : Blo 2135435 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B6495709 : Blo 2135435 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B8660945 : Blo 2135435 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B5773963 : Blo 2135435 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B7698617 : Blo 2135435 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B5132411 : Blo 2135435 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B3421607 : Blo 2135435 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B9124285 : Blo 2135435 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B12165713 : Blo 2135435 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B8110475 : Blo 2135435 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B5406983 : Blo 2135435 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B3604655 : Blo 2135435 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B2403103 : Blo 2135435 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B3204137 : Blo 2135435 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B2136091 : Blo 2135435 2136091 := bstep (se 1 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 2136091 = 3204137) B3204137
theorem B3421613 : Blo 2135435 3421613 := bbase (se 3 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 3421613 = 1283105) (by norm_num)
theorem B9124301 : Blo 2135435 9124301 := bstep (se 3 (by rfl) ⟨1710806, by rfl⟩ : syracuseStep 9124301 = 3421613) B3421613
theorem B6082867 : Blo 2135435 6082867 := bstep (se 1 (by rfl) ⟨4562150, by rfl⟩ : syracuseStep 6082867 = 9124301) B9124301
theorem B8110489 : Blo 2135435 8110489 := bstep (se 2 (by rfl) ⟨3041433, by rfl⟩ : syracuseStep 8110489 = 6082867) B6082867
theorem B10813985 : Blo 2135435 10813985 := bstep (se 2 (by rfl) ⟨4055244, by rfl⟩ : syracuseStep 10813985 = 8110489) B8110489
theorem B7209323 : Blo 2135435 7209323 := bstep (se 1 (by rfl) ⟨5406992, by rfl⟩ : syracuseStep 7209323 = 10813985) B10813985
theorem B4806215 : Blo 2135435 4806215 := bstep (se 1 (by rfl) ⟨3604661, by rfl⟩ : syracuseStep 4806215 = 7209323) B7209323
theorem B3204143 : Blo 2135435 3204143 := bstep (se 1 (by rfl) ⟨2403107, by rfl⟩ : syracuseStep 3204143 = 4806215) B4806215
theorem B2136095 : Blo 2135435 2136095 := bstep (se 1 (by rfl) ⟨1602071, by rfl⟩ : syracuseStep 2136095 = 3204143) B3204143
theorem B3204149 : Blo 2135435 3204149 := bbase (se 5 (by rfl) ⟨150194, by rfl⟩ : syracuseStep 3204149 = 300389) (by norm_num)
theorem B2136099 : Blo 2135435 2136099 := bstep (se 1 (by rfl) ⟨1602074, by rfl⟩ : syracuseStep 2136099 = 3204149) B3204149
theorem B5407013 : Blo 2135435 5407013 := bbase (se 4 (by rfl) ⟨506907, by rfl⟩ : syracuseStep 5407013 = 1013815) (by norm_num)
theorem B3604675 : Blo 2135435 3604675 := bstep (se 1 (by rfl) ⟨2703506, by rfl⟩ : syracuseStep 3604675 = 5407013) B5407013
theorem B4806233 : Blo 2135435 4806233 := bstep (se 2 (by rfl) ⟨1802337, by rfl⟩ : syracuseStep 4806233 = 3604675) B3604675
theorem B3204155 : Blo 2135435 3204155 := bstep (se 1 (by rfl) ⟨2403116, by rfl⟩ : syracuseStep 3204155 = 4806233) B4806233
theorem B2136103 : Blo 2135435 2136103 := bstep (se 1 (by rfl) ⟨1602077, by rfl⟩ : syracuseStep 2136103 = 3204155) B3204155
theorem B2403121 : Blo 2135435 2403121 := bbase (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) (by norm_num)
theorem B3204161 : Blo 2135435 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B2136107 : Blo 2135435 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B3247885 : Blo 2135435 3247885 := bbase (se 3 (by rfl) ⟨608978, by rfl⟩ : syracuseStep 3247885 = 1217957) (by norm_num)
theorem B4330513 : Blo 2135435 4330513 := bstep (se 2 (by rfl) ⟨1623942, by rfl⟩ : syracuseStep 4330513 = 3247885) B3247885
theorem B5774017 : Blo 2135435 5774017 := bstep (se 2 (by rfl) ⟨2165256, by rfl⟩ : syracuseStep 5774017 = 4330513) B4330513
theorem B7698689 : Blo 2135435 7698689 := bstep (se 2 (by rfl) ⟨2887008, by rfl⟩ : syracuseStep 7698689 = 5774017) B5774017
theorem B5132459 : Blo 2135435 5132459 := bstep (se 1 (by rfl) ⟨3849344, by rfl⟩ : syracuseStep 5132459 = 7698689) B7698689
theorem B3421639 : Blo 2135435 3421639 := bstep (se 1 (by rfl) ⟨2566229, by rfl⟩ : syracuseStep 3421639 = 5132459) B5132459
theorem B4562185 : Blo 2135435 4562185 := bstep (se 2 (by rfl) ⟨1710819, by rfl⟩ : syracuseStep 4562185 = 3421639) B3421639
theorem B6082913 : Blo 2135435 6082913 := bstep (se 2 (by rfl) ⟨2281092, by rfl⟩ : syracuseStep 6082913 = 4562185) B4562185
theorem B4055275 : Blo 2135435 4055275 := bstep (se 1 (by rfl) ⟨3041456, by rfl⟩ : syracuseStep 4055275 = 6082913) B6082913
theorem B5407033 : Blo 2135435 5407033 := bstep (se 2 (by rfl) ⟨2027637, by rfl⟩ : syracuseStep 5407033 = 4055275) B4055275
theorem B7209377 : Blo 2135435 7209377 := bstep (se 2 (by rfl) ⟨2703516, by rfl⟩ : syracuseStep 7209377 = 5407033) B5407033
theorem B4806251 : Blo 2135435 4806251 := bstep (se 1 (by rfl) ⟨3604688, by rfl⟩ : syracuseStep 4806251 = 7209377) B7209377
theorem B3204167 : Blo 2135435 3204167 := bstep (se 1 (by rfl) ⟨2403125, by rfl⟩ : syracuseStep 3204167 = 4806251) B4806251
theorem B2136111 : Blo 2135435 2136111 := bstep (se 1 (by rfl) ⟨1602083, by rfl⟩ : syracuseStep 2136111 = 3204167) B3204167
theorem B3204173 : Blo 2135435 3204173 := bbase (se 3 (by rfl) ⟨600782, by rfl⟩ : syracuseStep 3204173 = 1201565) (by norm_num)
theorem B2136115 : Blo 2135435 2136115 := bstep (se 1 (by rfl) ⟨1602086, by rfl⟩ : syracuseStep 2136115 = 3204173) B3204173
theorem B4806269 : Blo 2135435 4806269 := bbase (se 3 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 4806269 = 1802351) (by norm_num)
theorem B3204179 : Blo 2135435 3204179 := bstep (se 1 (by rfl) ⟨2403134, by rfl⟩ : syracuseStep 3204179 = 4806269) B4806269
theorem B2136119 : Blo 2135435 2136119 := bstep (se 1 (by rfl) ⟨1602089, by rfl⟩ : syracuseStep 2136119 = 3204179) B3204179
theorem B3604709 : Blo 2135435 3604709 := bbase (se 4 (by rfl) ⟨337941, by rfl⟩ : syracuseStep 3604709 = 675883) (by norm_num)
theorem B2403139 : Blo 2135435 2403139 := bstep (se 1 (by rfl) ⟨1802354, by rfl⟩ : syracuseStep 2403139 = 3604709) B3604709
theorem B3204185 : Blo 2135435 3204185 := bstep (se 2 (by rfl) ⟨1201569, by rfl⟩ : syracuseStep 3204185 = 2403139) B2403139
theorem B2136123 : Blo 2135435 2136123 := bstep (se 1 (by rfl) ⟨1602092, by rfl⟩ : syracuseStep 2136123 = 3204185) B3204185
theorem B3849373 : Blo 2135435 3849373 := bbase (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) (by norm_num)
theorem B5132497 : Blo 2135435 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B6843329 : Blo 2135435 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B4562219 : Blo 2135435 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B3041479 : Blo 2135435 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B16221221 : Blo 2135435 16221221 := bstep (se 4 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 16221221 = 3041479) B3041479
theorem B10814147 : Blo 2135435 10814147 := bstep (se 1 (by rfl) ⟨8110610, by rfl⟩ : syracuseStep 10814147 = 16221221) B16221221
theorem B7209431 : Blo 2135435 7209431 := bstep (se 1 (by rfl) ⟨5407073, by rfl⟩ : syracuseStep 7209431 = 10814147) B10814147
theorem B4806287 : Blo 2135435 4806287 := bstep (se 1 (by rfl) ⟨3604715, by rfl⟩ : syracuseStep 4806287 = 7209431) B7209431
theorem B3204191 : Blo 2135435 3204191 := bstep (se 1 (by rfl) ⟨2403143, by rfl⟩ : syracuseStep 3204191 = 4806287) B4806287
theorem B2136127 : Blo 2135435 2136127 := bstep (se 1 (by rfl) ⟨1602095, by rfl⟩ : syracuseStep 2136127 = 3204191) B3204191
theorem B3204197 : Blo 2135435 3204197 := bbase (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) (by norm_num)
theorem B2136131 : Blo 2135435 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B4562237 : Blo 2135435 4562237 := bbase (se 3 (by rfl) ⟨855419, by rfl⟩ : syracuseStep 4562237 = 1710839) (by norm_num)
theorem B3041491 : Blo 2135435 3041491 := bstep (se 1 (by rfl) ⟨2281118, by rfl⟩ : syracuseStep 3041491 = 4562237) B4562237
theorem B4055321 : Blo 2135435 4055321 := bstep (se 2 (by rfl) ⟨1520745, by rfl⟩ : syracuseStep 4055321 = 3041491) B3041491
theorem B2703547 : Blo 2135435 2703547 := bstep (se 1 (by rfl) ⟨2027660, by rfl⟩ : syracuseStep 2703547 = 4055321) B4055321
theorem B3604729 : Blo 2135435 3604729 := bstep (se 2 (by rfl) ⟨1351773, by rfl⟩ : syracuseStep 3604729 = 2703547) B2703547
theorem B4806305 : Blo 2135435 4806305 := bstep (se 2 (by rfl) ⟨1802364, by rfl⟩ : syracuseStep 4806305 = 3604729) B3604729
theorem B3204203 : Blo 2135435 3204203 := bstep (se 1 (by rfl) ⟨2403152, by rfl⟩ : syracuseStep 3204203 = 4806305) B4806305
theorem B2136135 : Blo 2135435 2136135 := bstep (se 1 (by rfl) ⟨1602101, by rfl⟩ : syracuseStep 2136135 = 3204203) B3204203
theorem B2403157 : Blo 2135435 2403157 := bbase (se 9 (by rfl) ⟨7040, by rfl⟩ : syracuseStep 2403157 = 14081) (by norm_num)
theorem B3204209 : Blo 2135435 3204209 := bstep (se 2 (by rfl) ⟨1201578, by rfl⟩ : syracuseStep 3204209 = 2403157) B2403157
theorem B2136139 : Blo 2135435 2136139 := bstep (se 1 (by rfl) ⟨1602104, by rfl⟩ : syracuseStep 2136139 = 3204209) B3204209
theorem B2703557 : Blo 2135435 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B7209485 : Blo 2135435 7209485 := bstep (se 3 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 7209485 = 2703557) B2703557
theorem B4806323 : Blo 2135435 4806323 := bstep (se 1 (by rfl) ⟨3604742, by rfl⟩ : syracuseStep 4806323 = 7209485) B7209485
theorem B3204215 : Blo 2135435 3204215 := bstep (se 1 (by rfl) ⟨2403161, by rfl⟩ : syracuseStep 3204215 = 4806323) B4806323
theorem B2136143 : Blo 2135435 2136143 := bstep (se 1 (by rfl) ⟨1602107, by rfl⟩ : syracuseStep 2136143 = 3204215) B3204215
theorem B3204221 : Blo 2135435 3204221 := bbase (se 3 (by rfl) ⟨600791, by rfl⟩ : syracuseStep 3204221 = 1201583) (by norm_num)
theorem B2136147 : Blo 2135435 2136147 := bstep (se 1 (by rfl) ⟨1602110, by rfl⟩ : syracuseStep 2136147 = 3204221) B3204221
theorem B4806341 : Blo 2135435 4806341 := bbase (se 4 (by rfl) ⟨450594, by rfl⟩ : syracuseStep 4806341 = 901189) (by norm_num)
theorem B3204227 : Blo 2135435 3204227 := bstep (se 1 (by rfl) ⟨2403170, by rfl⟩ : syracuseStep 3204227 = 4806341) B4806341
theorem B2136151 : Blo 2135435 2136151 := bstep (se 1 (by rfl) ⟨1602113, by rfl⟩ : syracuseStep 2136151 = 3204227) B3204227
theorem B4624525 : Blo 2135435 4624525 := bbase (se 3 (by rfl) ⟨867098, by rfl⟩ : syracuseStep 4624525 = 1734197) (by norm_num)
theorem B6166033 : Blo 2135435 6166033 := bstep (se 2 (by rfl) ⟨2312262, by rfl⟩ : syracuseStep 6166033 = 4624525) B4624525
theorem B32885509 : Blo 2135435 32885509 := bstep (se 4 (by rfl) ⟨3083016, by rfl⟩ : syracuseStep 32885509 = 6166033) B6166033
theorem B43847345 : Blo 2135435 43847345 := bstep (se 2 (by rfl) ⟨16442754, by rfl⟩ : syracuseStep 43847345 = 32885509) B32885509
theorem B29231563 : Blo 2135435 29231563 := bstep (se 1 (by rfl) ⟨21923672, by rfl⟩ : syracuseStep 29231563 = 43847345) B43847345
theorem B38975417 : Blo 2135435 38975417 := bstep (se 2 (by rfl) ⟨14615781, by rfl⟩ : syracuseStep 38975417 = 29231563) B29231563
theorem B25983611 : Blo 2135435 25983611 := bstep (se 1 (by rfl) ⟨19487708, by rfl⟩ : syracuseStep 25983611 = 38975417) B38975417
theorem B17322407 : Blo 2135435 17322407 := bstep (se 1 (by rfl) ⟨12991805, by rfl⟩ : syracuseStep 17322407 = 25983611) B25983611
theorem B11548271 : Blo 2135435 11548271 := bstep (se 1 (by rfl) ⟨8661203, by rfl⟩ : syracuseStep 11548271 = 17322407) B17322407
theorem B30795389 : Blo 2135435 30795389 := bstep (se 3 (by rfl) ⟨5774135, by rfl⟩ : syracuseStep 30795389 = 11548271) B11548271
theorem B20530259 : Blo 2135435 20530259 := bstep (se 1 (by rfl) ⟨15397694, by rfl⟩ : syracuseStep 20530259 = 30795389) B30795389
theorem B13686839 : Blo 2135435 13686839 := bstep (se 1 (by rfl) ⟨10265129, by rfl⟩ : syracuseStep 13686839 = 20530259) B20530259
theorem B9124559 : Blo 2135435 9124559 := bstep (se 1 (by rfl) ⟨6843419, by rfl⟩ : syracuseStep 9124559 = 13686839) B13686839
theorem B6083039 : Blo 2135435 6083039 := bstep (se 1 (by rfl) ⟨4562279, by rfl⟩ : syracuseStep 6083039 = 9124559) B9124559
theorem B4055359 : Blo 2135435 4055359 := bstep (se 1 (by rfl) ⟨3041519, by rfl⟩ : syracuseStep 4055359 = 6083039) B6083039
theorem B5407145 : Blo 2135435 5407145 := bstep (se 2 (by rfl) ⟨2027679, by rfl⟩ : syracuseStep 5407145 = 4055359) B4055359
theorem B3604763 : Blo 2135435 3604763 := bstep (se 1 (by rfl) ⟨2703572, by rfl⟩ : syracuseStep 3604763 = 5407145) B5407145
theorem B2403175 : Blo 2135435 2403175 := bstep (se 1 (by rfl) ⟨1802381, by rfl⟩ : syracuseStep 2403175 = 3604763) B3604763
theorem B3204233 : Blo 2135435 3204233 := bstep (se 2 (by rfl) ⟨1201587, by rfl⟩ : syracuseStep 3204233 = 2403175) B2403175
theorem B2136155 : Blo 2135435 2136155 := bstep (se 1 (by rfl) ⟨1602116, by rfl⟩ : syracuseStep 2136155 = 3204233) B3204233
theorem B10814309 : Blo 2135435 10814309 := bbase (se 4 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 10814309 = 2027683) (by norm_num)
theorem B7209539 : Blo 2135435 7209539 := bstep (se 1 (by rfl) ⟨5407154, by rfl⟩ : syracuseStep 7209539 = 10814309) B10814309
theorem B4806359 : Blo 2135435 4806359 := bstep (se 1 (by rfl) ⟨3604769, by rfl⟩ : syracuseStep 4806359 = 7209539) B7209539
theorem B3204239 : Blo 2135435 3204239 := bstep (se 1 (by rfl) ⟨2403179, by rfl⟩ : syracuseStep 3204239 = 4806359) B4806359
theorem B2136159 : Blo 2135435 2136159 := bstep (se 1 (by rfl) ⟨1602119, by rfl⟩ : syracuseStep 2136159 = 3204239) B3204239
theorem B3204245 : Blo 2135435 3204245 := bbase (se 6 (by rfl) ⟨75099, by rfl⟩ : syracuseStep 3204245 = 150199) (by norm_num)
theorem B2136163 : Blo 2135435 2136163 := bstep (se 1 (by rfl) ⟨1602122, by rfl⟩ : syracuseStep 2136163 = 3204245) B3204245
theorem B3849445 : Blo 2135435 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B5132593 : Blo 2135435 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B6843457 : Blo 2135435 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B9124609 : Blo 2135435 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B12166145 : Blo 2135435 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B8110763 : Blo 2135435 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B5407175 : Blo 2135435 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B3604783 : Blo 2135435 3604783 := bstep (se 1 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 3604783 = 5407175) B5407175
theorem B4806377 : Blo 2135435 4806377 := bstep (se 2 (by rfl) ⟨1802391, by rfl⟩ : syracuseStep 4806377 = 3604783) B3604783
theorem B3204251 : Blo 2135435 3204251 := bstep (se 1 (by rfl) ⟨2403188, by rfl⟩ : syracuseStep 3204251 = 4806377) B4806377
theorem B2136167 : Blo 2135435 2136167 := bstep (se 1 (by rfl) ⟨1602125, by rfl⟩ : syracuseStep 2136167 = 3204251) B3204251
theorem B2403193 : Blo 2135435 2403193 := bbase (se 2 (by rfl) ⟨901197, by rfl⟩ : syracuseStep 2403193 = 1802395) (by norm_num)
theorem B3204257 : Blo 2135435 3204257 := bstep (se 2 (by rfl) ⟨1201596, by rfl⟩ : syracuseStep 3204257 = 2403193) B2403193
theorem B2136171 : Blo 2135435 2136171 := bstep (se 1 (by rfl) ⟨1602128, by rfl⟩ : syracuseStep 2136171 = 3204257) B3204257
theorem B13686965 : Blo 2135435 13686965 := bbase (se 5 (by rfl) ⟨641576, by rfl⟩ : syracuseStep 13686965 = 1283153) (by norm_num)
theorem B9124643 : Blo 2135435 9124643 := bstep (se 1 (by rfl) ⟨6843482, by rfl⟩ : syracuseStep 9124643 = 13686965) B13686965
theorem B6083095 : Blo 2135435 6083095 := bstep (se 1 (by rfl) ⟨4562321, by rfl⟩ : syracuseStep 6083095 = 9124643) B9124643
theorem B8110793 : Blo 2135435 8110793 := bstep (se 2 (by rfl) ⟨3041547, by rfl⟩ : syracuseStep 8110793 = 6083095) B6083095
theorem B5407195 : Blo 2135435 5407195 := bstep (se 1 (by rfl) ⟨4055396, by rfl⟩ : syracuseStep 5407195 = 8110793) B8110793
theorem B7209593 : Blo 2135435 7209593 := bstep (se 2 (by rfl) ⟨2703597, by rfl⟩ : syracuseStep 7209593 = 5407195) B5407195
theorem B4806395 : Blo 2135435 4806395 := bstep (se 1 (by rfl) ⟨3604796, by rfl⟩ : syracuseStep 4806395 = 7209593) B7209593
theorem B3204263 : Blo 2135435 3204263 := bstep (se 1 (by rfl) ⟨2403197, by rfl⟩ : syracuseStep 3204263 = 4806395) B4806395
theorem B2136175 : Blo 2135435 2136175 := bstep (se 1 (by rfl) ⟨1602131, by rfl⟩ : syracuseStep 2136175 = 3204263) B3204263
theorem B3204269 : Blo 2135435 3204269 := bbase (se 3 (by rfl) ⟨600800, by rfl⟩ : syracuseStep 3204269 = 1201601) (by norm_num)
theorem B2136179 : Blo 2135435 2136179 := bstep (se 1 (by rfl) ⟨1602134, by rfl⟩ : syracuseStep 2136179 = 3204269) B3204269
theorem B4806413 : Blo 2135435 4806413 := bbase (se 3 (by rfl) ⟨901202, by rfl⟩ : syracuseStep 4806413 = 1802405) (by norm_num)
theorem B3204275 : Blo 2135435 3204275 := bstep (se 1 (by rfl) ⟨2403206, by rfl⟩ : syracuseStep 3204275 = 4806413) B4806413
theorem B2136183 : Blo 2135435 2136183 := bstep (se 1 (by rfl) ⟨1602137, by rfl⟩ : syracuseStep 2136183 = 3204275) B3204275
theorem B2703613 : Blo 2135435 2703613 := bbase (se 3 (by rfl) ⟨506927, by rfl⟩ : syracuseStep 2703613 = 1013855) (by norm_num)
theorem B3604817 : Blo 2135435 3604817 := bstep (se 2 (by rfl) ⟨1351806, by rfl⟩ : syracuseStep 3604817 = 2703613) B2703613
theorem B2403211 : Blo 2135435 2403211 := bstep (se 1 (by rfl) ⟨1802408, by rfl⟩ : syracuseStep 2403211 = 3604817) B3604817
theorem B3204281 : Blo 2135435 3204281 := bstep (se 2 (by rfl) ⟨1201605, by rfl⟩ : syracuseStep 3204281 = 2403211) B2403211
theorem B2136187 : Blo 2135435 2136187 := bstep (se 1 (by rfl) ⟨1602140, by rfl⟩ : syracuseStep 2136187 = 3204281) B3204281
theorem B2566325 : Blo 2135435 2566325 := bbase (se 5 (by rfl) ⟨120296, by rfl⟩ : syracuseStep 2566325 = 240593) (by norm_num)
theorem B6843533 : Blo 2135435 6843533 := bstep (se 3 (by rfl) ⟨1283162, by rfl⟩ : syracuseStep 6843533 = 2566325) B2566325
theorem B18249421 : Blo 2135435 18249421 := bstep (se 3 (by rfl) ⟨3421766, by rfl⟩ : syracuseStep 18249421 = 6843533) B6843533
theorem B24332561 : Blo 2135435 24332561 := bstep (se 2 (by rfl) ⟨9124710, by rfl⟩ : syracuseStep 24332561 = 18249421) B18249421
theorem B16221707 : Blo 2135435 16221707 := bstep (se 1 (by rfl) ⟨12166280, by rfl⟩ : syracuseStep 16221707 = 24332561) B24332561
theorem B10814471 : Blo 2135435 10814471 := bstep (se 1 (by rfl) ⟨8110853, by rfl⟩ : syracuseStep 10814471 = 16221707) B16221707
theorem B7209647 : Blo 2135435 7209647 := bstep (se 1 (by rfl) ⟨5407235, by rfl⟩ : syracuseStep 7209647 = 10814471) B10814471
theorem B4806431 : Blo 2135435 4806431 := bstep (se 1 (by rfl) ⟨3604823, by rfl⟩ : syracuseStep 4806431 = 7209647) B7209647
theorem B3204287 : Blo 2135435 3204287 := bstep (se 1 (by rfl) ⟨2403215, by rfl⟩ : syracuseStep 3204287 = 4806431) B4806431
theorem B2136191 : Blo 2135435 2136191 := bstep (se 1 (by rfl) ⟨1602143, by rfl⟩ : syracuseStep 2136191 = 3204287) B3204287
theorem B3204293 : Blo 2135435 3204293 := bbase (se 4 (by rfl) ⟨300402, by rfl⟩ : syracuseStep 3204293 = 600805) (by norm_num)
theorem B2136195 : Blo 2135435 2136195 := bstep (se 1 (by rfl) ⟨1602146, by rfl⟩ : syracuseStep 2136195 = 3204293) B3204293
theorem B3604837 : Blo 2135435 3604837 := bbase (se 4 (by rfl) ⟨337953, by rfl⟩ : syracuseStep 3604837 = 675907) (by norm_num)
theorem B4806449 : Blo 2135435 4806449 := bstep (se 2 (by rfl) ⟨1802418, by rfl⟩ : syracuseStep 4806449 = 3604837) B3604837
theorem B3204299 : Blo 2135435 3204299 := bstep (se 1 (by rfl) ⟨2403224, by rfl⟩ : syracuseStep 3204299 = 4806449) B4806449
theorem B2136199 : Blo 2135435 2136199 := bstep (se 1 (by rfl) ⟨1602149, by rfl⟩ : syracuseStep 2136199 = 3204299) B3204299
theorem B2403229 : Blo 2135435 2403229 := bbase (se 3 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 2403229 = 901211) (by norm_num)
theorem B3204305 : Blo 2135435 3204305 := bstep (se 2 (by rfl) ⟨1201614, by rfl⟩ : syracuseStep 3204305 = 2403229) B2403229
theorem B2136203 : Blo 2135435 2136203 := bstep (se 1 (by rfl) ⟨1602152, by rfl⟩ : syracuseStep 2136203 = 3204305) B3204305
theorem B7209701 : Blo 2135435 7209701 := bbase (se 4 (by rfl) ⟨675909, by rfl⟩ : syracuseStep 7209701 = 1351819) (by norm_num)
theorem B4806467 : Blo 2135435 4806467 := bstep (se 1 (by rfl) ⟨3604850, by rfl⟩ : syracuseStep 4806467 = 7209701) B7209701
theorem B3204311 : Blo 2135435 3204311 := bstep (se 1 (by rfl) ⟨2403233, by rfl⟩ : syracuseStep 3204311 = 4806467) B4806467
theorem B2136207 : Blo 2135435 2136207 := bstep (se 1 (by rfl) ⟨1602155, by rfl⟩ : syracuseStep 2136207 = 3204311) B3204311
theorem B3204317 : Blo 2135435 3204317 := bbase (se 3 (by rfl) ⟨600809, by rfl⟩ : syracuseStep 3204317 = 1201619) (by norm_num)
theorem B2136211 : Blo 2135435 2136211 := bstep (se 1 (by rfl) ⟨1602158, by rfl⟩ : syracuseStep 2136211 = 3204317) B3204317
theorem B4806485 : Blo 2135435 4806485 := bbase (se 9 (by rfl) ⟨14081, by rfl⟩ : syracuseStep 4806485 = 28163) (by norm_num)
theorem B3204323 : Blo 2135435 3204323 := bstep (se 1 (by rfl) ⟨2403242, by rfl⟩ : syracuseStep 3204323 = 4806485) B4806485
theorem B2136215 : Blo 2135435 2136215 := bstep (se 1 (by rfl) ⟨1602161, by rfl⟩ : syracuseStep 2136215 = 3204323) B3204323
theorem B6083221 : Blo 2135435 6083221 := bbase (se 6 (by rfl) ⟨142575, by rfl⟩ : syracuseStep 6083221 = 285151) (by norm_num)
theorem B8110961 : Blo 2135435 8110961 := bstep (se 2 (by rfl) ⟨3041610, by rfl⟩ : syracuseStep 8110961 = 6083221) B6083221
theorem B5407307 : Blo 2135435 5407307 := bstep (se 1 (by rfl) ⟨4055480, by rfl⟩ : syracuseStep 5407307 = 8110961) B8110961
theorem B3604871 : Blo 2135435 3604871 := bstep (se 1 (by rfl) ⟨2703653, by rfl⟩ : syracuseStep 3604871 = 5407307) B5407307
theorem B2403247 : Blo 2135435 2403247 := bstep (se 1 (by rfl) ⟨1802435, by rfl⟩ : syracuseStep 2403247 = 3604871) B3604871
theorem B3204329 : Blo 2135435 3204329 := bstep (se 2 (by rfl) ⟨1201623, by rfl⟩ : syracuseStep 3204329 = 2403247) B2403247
theorem B2136219 : Blo 2135435 2136219 := bstep (se 1 (by rfl) ⟨1602164, by rfl⟩ : syracuseStep 2136219 = 3204329) B3204329
theorem B8221637 : Blo 2135435 8221637 := bbase (se 4 (by rfl) ⟨770778, by rfl⟩ : syracuseStep 8221637 = 1541557) (by norm_num)
theorem B5481091 : Blo 2135435 5481091 := bstep (se 1 (by rfl) ⟨4110818, by rfl⟩ : syracuseStep 5481091 = 8221637) B8221637
theorem B29232485 : Blo 2135435 29232485 := bstep (se 4 (by rfl) ⟨2740545, by rfl⟩ : syracuseStep 29232485 = 5481091) B5481091
theorem B19488323 : Blo 2135435 19488323 := bstep (se 1 (by rfl) ⟨14616242, by rfl⟩ : syracuseStep 19488323 = 29232485) B29232485
theorem B51968861 : Blo 2135435 51968861 := bstep (se 3 (by rfl) ⟨9744161, by rfl⟩ : syracuseStep 51968861 = 19488323) B19488323
theorem B34645907 : Blo 2135435 34645907 := bstep (se 1 (by rfl) ⟨25984430, by rfl⟩ : syracuseStep 34645907 = 51968861) B51968861
theorem B92389085 : Blo 2135435 92389085 := bstep (se 3 (by rfl) ⟨17322953, by rfl⟩ : syracuseStep 92389085 = 34645907) B34645907
theorem B61592723 : Blo 2135435 61592723 := bstep (se 1 (by rfl) ⟨46194542, by rfl⟩ : syracuseStep 61592723 = 92389085) B92389085
theorem B41061815 : Blo 2135435 41061815 := bstep (se 1 (by rfl) ⟨30796361, by rfl⟩ : syracuseStep 41061815 = 61592723) B61592723
theorem B27374543 : Blo 2135435 27374543 := bstep (se 1 (by rfl) ⟨20530907, by rfl⟩ : syracuseStep 27374543 = 41061815) B41061815
theorem B18249695 : Blo 2135435 18249695 := bstep (se 1 (by rfl) ⟨13687271, by rfl⟩ : syracuseStep 18249695 = 27374543) B27374543
theorem B12166463 : Blo 2135435 12166463 := bstep (se 1 (by rfl) ⟨9124847, by rfl⟩ : syracuseStep 12166463 = 18249695) B18249695
theorem B8110975 : Blo 2135435 8110975 := bstep (se 1 (by rfl) ⟨6083231, by rfl⟩ : syracuseStep 8110975 = 12166463) B12166463
theorem B10814633 : Blo 2135435 10814633 := bstep (se 2 (by rfl) ⟨4055487, by rfl⟩ : syracuseStep 10814633 = 8110975) B8110975
theorem B7209755 : Blo 2135435 7209755 := bstep (se 1 (by rfl) ⟨5407316, by rfl⟩ : syracuseStep 7209755 = 10814633) B10814633
theorem B4806503 : Blo 2135435 4806503 := bstep (se 1 (by rfl) ⟨3604877, by rfl⟩ : syracuseStep 4806503 = 7209755) B7209755
theorem B3204335 : Blo 2135435 3204335 := bstep (se 1 (by rfl) ⟨2403251, by rfl⟩ : syracuseStep 3204335 = 4806503) B4806503
theorem B2136223 : Blo 2135435 2136223 := bstep (se 1 (by rfl) ⟨1602167, by rfl⟩ : syracuseStep 2136223 = 3204335) B3204335
theorem B3204341 : Blo 2135435 3204341 := bbase (se 5 (by rfl) ⟨150203, by rfl⟩ : syracuseStep 3204341 = 300407) (by norm_num)
theorem B2136227 : Blo 2135435 2136227 := bstep (se 1 (by rfl) ⟨1602170, by rfl⟩ : syracuseStep 2136227 = 3204341) B3204341
theorem B5774341 : Blo 2135435 5774341 := bbase (se 4 (by rfl) ⟨541344, by rfl⟩ : syracuseStep 5774341 = 1082689) (by norm_num)
theorem B7699121 : Blo 2135435 7699121 := bstep (se 2 (by rfl) ⟨2887170, by rfl⟩ : syracuseStep 7699121 = 5774341) B5774341
theorem B5132747 : Blo 2135435 5132747 := bstep (se 1 (by rfl) ⟨3849560, by rfl⟩ : syracuseStep 5132747 = 7699121) B7699121
theorem B13687325 : Blo 2135435 13687325 := bstep (se 3 (by rfl) ⟨2566373, by rfl⟩ : syracuseStep 13687325 = 5132747) B5132747
theorem B9124883 : Blo 2135435 9124883 := bstep (se 1 (by rfl) ⟨6843662, by rfl⟩ : syracuseStep 9124883 = 13687325) B13687325
theorem B6083255 : Blo 2135435 6083255 := bstep (se 1 (by rfl) ⟨4562441, by rfl⟩ : syracuseStep 6083255 = 9124883) B9124883
theorem B4055503 : Blo 2135435 4055503 := bstep (se 1 (by rfl) ⟨3041627, by rfl⟩ : syracuseStep 4055503 = 6083255) B6083255
theorem B5407337 : Blo 2135435 5407337 := bstep (se 2 (by rfl) ⟨2027751, by rfl⟩ : syracuseStep 5407337 = 4055503) B4055503
theorem B3604891 : Blo 2135435 3604891 := bstep (se 1 (by rfl) ⟨2703668, by rfl⟩ : syracuseStep 3604891 = 5407337) B5407337
theorem B4806521 : Blo 2135435 4806521 := bstep (se 2 (by rfl) ⟨1802445, by rfl⟩ : syracuseStep 4806521 = 3604891) B3604891
theorem B3204347 : Blo 2135435 3204347 := bstep (se 1 (by rfl) ⟨2403260, by rfl⟩ : syracuseStep 3204347 = 4806521) B4806521
theorem B2136231 : Blo 2135435 2136231 := bstep (se 1 (by rfl) ⟨1602173, by rfl⟩ : syracuseStep 2136231 = 3204347) B3204347
theorem B2403265 : Blo 2135435 2403265 := bbase (se 2 (by rfl) ⟨901224, by rfl⟩ : syracuseStep 2403265 = 1802449) (by norm_num)
theorem B3204353 : Blo 2135435 3204353 := bstep (se 2 (by rfl) ⟨1201632, by rfl⟩ : syracuseStep 3204353 = 2403265) B2403265
theorem B2136235 : Blo 2135435 2136235 := bstep (se 1 (by rfl) ⟨1602176, by rfl⟩ : syracuseStep 2136235 = 3204353) B3204353
theorem B5407357 : Blo 2135435 5407357 := bbase (se 3 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 5407357 = 2027759) (by norm_num)
theorem B7209809 : Blo 2135435 7209809 := bstep (se 2 (by rfl) ⟨2703678, by rfl⟩ : syracuseStep 7209809 = 5407357) B5407357
theorem B4806539 : Blo 2135435 4806539 := bstep (se 1 (by rfl) ⟨3604904, by rfl⟩ : syracuseStep 4806539 = 7209809) B7209809
theorem B3204359 : Blo 2135435 3204359 := bstep (se 1 (by rfl) ⟨2403269, by rfl⟩ : syracuseStep 3204359 = 4806539) B4806539
theorem B2136239 : Blo 2135435 2136239 := bstep (se 1 (by rfl) ⟨1602179, by rfl⟩ : syracuseStep 2136239 = 3204359) B3204359
theorem B3204365 : Blo 2135435 3204365 := bbase (se 3 (by rfl) ⟨600818, by rfl⟩ : syracuseStep 3204365 = 1201637) (by norm_num)
theorem B2136243 : Blo 2135435 2136243 := bstep (se 1 (by rfl) ⟨1602182, by rfl⟩ : syracuseStep 2136243 = 3204365) B3204365
theorem B4806557 : Blo 2135435 4806557 := bbase (se 3 (by rfl) ⟨901229, by rfl⟩ : syracuseStep 4806557 = 1802459) (by norm_num)
theorem B3204371 : Blo 2135435 3204371 := bstep (se 1 (by rfl) ⟨2403278, by rfl⟩ : syracuseStep 3204371 = 4806557) B4806557
theorem B2136247 : Blo 2135435 2136247 := bstep (se 1 (by rfl) ⟨1602185, by rfl⟩ : syracuseStep 2136247 = 3204371) B3204371
theorem B3604925 : Blo 2135435 3604925 := bbase (se 3 (by rfl) ⟨675923, by rfl⟩ : syracuseStep 3604925 = 1351847) (by norm_num)
theorem B2403283 : Blo 2135435 2403283 := bstep (se 1 (by rfl) ⟨1802462, by rfl⟩ : syracuseStep 2403283 = 3604925) B3604925
theorem B3204377 : Blo 2135435 3204377 := bstep (se 2 (by rfl) ⟨1201641, by rfl⟩ : syracuseStep 3204377 = 2403283) B2403283
theorem B2136251 : Blo 2135435 2136251 := bstep (se 1 (by rfl) ⟨1602188, by rfl⟩ : syracuseStep 2136251 = 3204377) B3204377
theorem B12166645 : Blo 2135435 12166645 := bbase (se 5 (by rfl) ⟨570311, by rfl⟩ : syracuseStep 12166645 = 1140623) (by norm_num)
theorem B16222193 : Blo 2135435 16222193 := bstep (se 2 (by rfl) ⟨6083322, by rfl⟩ : syracuseStep 16222193 = 12166645) B12166645
theorem B10814795 : Blo 2135435 10814795 := bstep (se 1 (by rfl) ⟨8111096, by rfl⟩ : syracuseStep 10814795 = 16222193) B16222193
theorem B7209863 : Blo 2135435 7209863 := bstep (se 1 (by rfl) ⟨5407397, by rfl⟩ : syracuseStep 7209863 = 10814795) B10814795
theorem B4806575 : Blo 2135435 4806575 := bstep (se 1 (by rfl) ⟨3604931, by rfl⟩ : syracuseStep 4806575 = 7209863) B7209863
theorem B3204383 : Blo 2135435 3204383 := bstep (se 1 (by rfl) ⟨2403287, by rfl⟩ : syracuseStep 3204383 = 4806575) B4806575
theorem B2136255 : Blo 2135435 2136255 := bstep (se 1 (by rfl) ⟨1602191, by rfl⟩ : syracuseStep 2136255 = 3204383) B3204383
theorem B3204389 : Blo 2135435 3204389 := bbase (se 4 (by rfl) ⟨300411, by rfl⟩ : syracuseStep 3204389 = 600823) (by norm_num)
theorem B2136259 : Blo 2135435 2136259 := bstep (se 1 (by rfl) ⟨1602194, by rfl⟩ : syracuseStep 2136259 = 3204389) B3204389
theorem B2703709 : Blo 2135435 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B3604945 : Blo 2135435 3604945 := bstep (se 2 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 3604945 = 2703709) B2703709
theorem B4806593 : Blo 2135435 4806593 := bstep (se 2 (by rfl) ⟨1802472, by rfl⟩ : syracuseStep 4806593 = 3604945) B3604945
theorem B3204395 : Blo 2135435 3204395 := bstep (se 1 (by rfl) ⟨2403296, by rfl⟩ : syracuseStep 3204395 = 4806593) B4806593
theorem B2136263 : Blo 2135435 2136263 := bstep (se 1 (by rfl) ⟨1602197, by rfl⟩ : syracuseStep 2136263 = 3204395) B3204395
theorem B2403301 : Blo 2135435 2403301 := bbase (se 4 (by rfl) ⟨225309, by rfl⟩ : syracuseStep 2403301 = 450619) (by norm_num)
theorem B3204401 : Blo 2135435 3204401 := bstep (se 2 (by rfl) ⟨1201650, by rfl⟩ : syracuseStep 3204401 = 2403301) B2403301
theorem B2136267 : Blo 2135435 2136267 := bstep (se 1 (by rfl) ⟨1602200, by rfl⟩ : syracuseStep 2136267 = 3204401) B3204401
theorem B4330837 : Blo 2135435 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B23097797 : Blo 2135435 23097797 := bstep (se 4 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 23097797 = 4330837) B4330837
theorem B15398531 : Blo 2135435 15398531 := bstep (se 1 (by rfl) ⟨11548898, by rfl⟩ : syracuseStep 15398531 = 23097797) B23097797
theorem B10265687 : Blo 2135435 10265687 := bstep (se 1 (by rfl) ⟨7699265, by rfl⟩ : syracuseStep 10265687 = 15398531) B15398531
theorem B6843791 : Blo 2135435 6843791 := bstep (se 1 (by rfl) ⟨5132843, by rfl⟩ : syracuseStep 6843791 = 10265687) B10265687
theorem B4562527 : Blo 2135435 4562527 := bstep (se 1 (by rfl) ⟨3421895, by rfl⟩ : syracuseStep 4562527 = 6843791) B6843791
theorem B6083369 : Blo 2135435 6083369 := bstep (se 2 (by rfl) ⟨2281263, by rfl⟩ : syracuseStep 6083369 = 4562527) B4562527
theorem B4055579 : Blo 2135435 4055579 := bstep (se 1 (by rfl) ⟨3041684, by rfl⟩ : syracuseStep 4055579 = 6083369) B6083369
theorem B2703719 : Blo 2135435 2703719 := bstep (se 1 (by rfl) ⟨2027789, by rfl⟩ : syracuseStep 2703719 = 4055579) B4055579
theorem B7209917 : Blo 2135435 7209917 := bstep (se 3 (by rfl) ⟨1351859, by rfl⟩ : syracuseStep 7209917 = 2703719) B2703719
theorem B4806611 : Blo 2135435 4806611 := bstep (se 1 (by rfl) ⟨3604958, by rfl⟩ : syracuseStep 4806611 = 7209917) B7209917
theorem B3204407 : Blo 2135435 3204407 := bstep (se 1 (by rfl) ⟨2403305, by rfl⟩ : syracuseStep 3204407 = 4806611) B4806611
theorem B2136271 : Blo 2135435 2136271 := bstep (se 1 (by rfl) ⟨1602203, by rfl⟩ : syracuseStep 2136271 = 3204407) B3204407
theorem B3204413 : Blo 2135435 3204413 := bbase (se 3 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 3204413 = 1201655) (by norm_num)
theorem B2136275 : Blo 2135435 2136275 := bstep (se 1 (by rfl) ⟨1602206, by rfl⟩ : syracuseStep 2136275 = 3204413) B3204413
theorem B4806629 : Blo 2135435 4806629 := bbase (se 4 (by rfl) ⟨450621, by rfl⟩ : syracuseStep 4806629 = 901243) (by norm_num)
theorem B3204419 : Blo 2135435 3204419 := bstep (se 1 (by rfl) ⟨2403314, by rfl⟩ : syracuseStep 3204419 = 4806629) B4806629
theorem B2136279 : Blo 2135435 2136279 := bstep (se 1 (by rfl) ⟨1602209, by rfl⟩ : syracuseStep 2136279 = 3204419) B3204419
theorem B5407469 : Blo 2135435 5407469 := bbase (se 3 (by rfl) ⟨1013900, by rfl⟩ : syracuseStep 5407469 = 2027801) (by norm_num)
theorem B3604979 : Blo 2135435 3604979 := bstep (se 1 (by rfl) ⟨2703734, by rfl⟩ : syracuseStep 3604979 = 5407469) B5407469
theorem B2403319 : Blo 2135435 2403319 := bstep (se 1 (by rfl) ⟨1802489, by rfl⟩ : syracuseStep 2403319 = 3604979) B3604979
theorem B3204425 : Blo 2135435 3204425 := bstep (se 2 (by rfl) ⟨1201659, by rfl⟩ : syracuseStep 3204425 = 2403319) B2403319
theorem B2136283 : Blo 2135435 2136283 := bstep (se 1 (by rfl) ⟨1602212, by rfl⟩ : syracuseStep 2136283 = 3204425) B3204425
theorem B2566441 : Blo 2135435 2566441 := bbase (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) (by norm_num)
theorem B3421921 : Blo 2135435 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B4562561 : Blo 2135435 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B3041707 : Blo 2135435 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B4055609 : Blo 2135435 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B10814957 : Blo 2135435 10814957 := bstep (se 3 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 10814957 = 4055609) B4055609
theorem B7209971 : Blo 2135435 7209971 := bstep (se 1 (by rfl) ⟨5407478, by rfl⟩ : syracuseStep 7209971 = 10814957) B10814957
theorem B4806647 : Blo 2135435 4806647 := bstep (se 1 (by rfl) ⟨3604985, by rfl⟩ : syracuseStep 4806647 = 7209971) B7209971
theorem B3204431 : Blo 2135435 3204431 := bstep (se 1 (by rfl) ⟨2403323, by rfl⟩ : syracuseStep 3204431 = 4806647) B4806647
theorem B2136287 : Blo 2135435 2136287 := bstep (se 1 (by rfl) ⟨1602215, by rfl⟩ : syracuseStep 2136287 = 3204431) B3204431
theorem B3204437 : Blo 2135435 3204437 := bbase (se 12 (by rfl) ⟨1173, by rfl⟩ : syracuseStep 3204437 = 2347) (by norm_num)
theorem B2136291 : Blo 2135435 2136291 := bstep (se 1 (by rfl) ⟨1602218, by rfl⟩ : syracuseStep 2136291 = 3204437) B3204437
theorem B2281289 : Blo 2135435 2281289 := bbase (se 2 (by rfl) ⟨855483, by rfl⟩ : syracuseStep 2281289 = 1710967) (by norm_num)
theorem B6083437 : Blo 2135435 6083437 := bstep (se 3 (by rfl) ⟨1140644, by rfl⟩ : syracuseStep 6083437 = 2281289) B2281289
theorem B8111249 : Blo 2135435 8111249 := bstep (se 2 (by rfl) ⟨3041718, by rfl⟩ : syracuseStep 8111249 = 6083437) B6083437
theorem B5407499 : Blo 2135435 5407499 := bstep (se 1 (by rfl) ⟨4055624, by rfl⟩ : syracuseStep 5407499 = 8111249) B8111249
theorem B3604999 : Blo 2135435 3604999 := bstep (se 1 (by rfl) ⟨2703749, by rfl⟩ : syracuseStep 3604999 = 5407499) B5407499
theorem B4806665 : Blo 2135435 4806665 := bstep (se 2 (by rfl) ⟨1802499, by rfl⟩ : syracuseStep 4806665 = 3604999) B3604999
theorem B3204443 : Blo 2135435 3204443 := bstep (se 1 (by rfl) ⟨2403332, by rfl⟩ : syracuseStep 3204443 = 4806665) B4806665
theorem B2136295 : Blo 2135435 2136295 := bstep (se 1 (by rfl) ⟨1602221, by rfl⟩ : syracuseStep 2136295 = 3204443) B3204443
theorem B2403337 : Blo 2135435 2403337 := bbase (se 2 (by rfl) ⟨901251, by rfl⟩ : syracuseStep 2403337 = 1802503) (by norm_num)
theorem B3204449 : Blo 2135435 3204449 := bstep (se 2 (by rfl) ⟨1201668, by rfl⟩ : syracuseStep 3204449 = 2403337) B2403337
theorem B2136299 : Blo 2135435 2136299 := bstep (se 1 (by rfl) ⟨1602224, by rfl⟩ : syracuseStep 2136299 = 3204449) B3204449
theorem B4330901 : Blo 2135435 4330901 := bbase (se 6 (by rfl) ⟨101505, by rfl⟩ : syracuseStep 4330901 = 203011) (by norm_num)
theorem B11549069 : Blo 2135435 11549069 := bstep (se 3 (by rfl) ⟨2165450, by rfl⟩ : syracuseStep 11549069 = 4330901) B4330901
theorem B7699379 : Blo 2135435 7699379 := bstep (se 1 (by rfl) ⟨5774534, by rfl⟩ : syracuseStep 7699379 = 11549069) B11549069
theorem B20531677 : Blo 2135435 20531677 := bstep (se 3 (by rfl) ⟨3849689, by rfl⟩ : syracuseStep 20531677 = 7699379) B7699379
theorem B27375569 : Blo 2135435 27375569 := bstep (se 2 (by rfl) ⟨10265838, by rfl⟩ : syracuseStep 27375569 = 20531677) B20531677
theorem B18250379 : Blo 2135435 18250379 := bstep (se 1 (by rfl) ⟨13687784, by rfl⟩ : syracuseStep 18250379 = 27375569) B27375569
theorem B12166919 : Blo 2135435 12166919 := bstep (se 1 (by rfl) ⟨9125189, by rfl⟩ : syracuseStep 12166919 = 18250379) B18250379
theorem B8111279 : Blo 2135435 8111279 := bstep (se 1 (by rfl) ⟨6083459, by rfl⟩ : syracuseStep 8111279 = 12166919) B12166919
theorem B5407519 : Blo 2135435 5407519 := bstep (se 1 (by rfl) ⟨4055639, by rfl⟩ : syracuseStep 5407519 = 8111279) B8111279
theorem B7210025 : Blo 2135435 7210025 := bstep (se 2 (by rfl) ⟨2703759, by rfl⟩ : syracuseStep 7210025 = 5407519) B5407519
theorem B4806683 : Blo 2135435 4806683 := bstep (se 1 (by rfl) ⟨3605012, by rfl⟩ : syracuseStep 4806683 = 7210025) B7210025
theorem B3204455 : Blo 2135435 3204455 := bstep (se 1 (by rfl) ⟨2403341, by rfl⟩ : syracuseStep 3204455 = 4806683) B4806683
theorem B2136303 : Blo 2135435 2136303 := bstep (se 1 (by rfl) ⟨1602227, by rfl⟩ : syracuseStep 2136303 = 3204455) B3204455
theorem B3204461 : Blo 2135435 3204461 := bbase (se 3 (by rfl) ⟨600836, by rfl⟩ : syracuseStep 3204461 = 1201673) (by norm_num)
theorem B2136307 : Blo 2135435 2136307 := bstep (se 1 (by rfl) ⟨1602230, by rfl⟩ : syracuseStep 2136307 = 3204461) B3204461
theorem B4806701 : Blo 2135435 4806701 := bbase (se 3 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 4806701 = 1802513) (by norm_num)
theorem B3204467 : Blo 2135435 3204467 := bstep (se 1 (by rfl) ⟨2403350, by rfl⟩ : syracuseStep 3204467 = 4806701) B4806701
theorem B2136311 : Blo 2135435 2136311 := bstep (se 1 (by rfl) ⟨1602233, by rfl⟩ : syracuseStep 2136311 = 3204467) B3204467
theorem B4872293 : Blo 2135435 4872293 := bbase (se 4 (by rfl) ⟨456777, by rfl⟩ : syracuseStep 4872293 = 913555) (by norm_num)
theorem B3248195 : Blo 2135435 3248195 := bstep (se 1 (by rfl) ⟨2436146, by rfl⟩ : syracuseStep 3248195 = 4872293) B4872293
theorem B8661853 : Blo 2135435 8661853 := bstep (se 3 (by rfl) ⟨1624097, by rfl⟩ : syracuseStep 8661853 = 3248195) B3248195
theorem B11549137 : Blo 2135435 11549137 := bstep (se 2 (by rfl) ⟨4330926, by rfl⟩ : syracuseStep 11549137 = 8661853) B8661853
theorem B15398849 : Blo 2135435 15398849 := bstep (se 2 (by rfl) ⟨5774568, by rfl⟩ : syracuseStep 15398849 = 11549137) B11549137
theorem B10265899 : Blo 2135435 10265899 := bstep (se 1 (by rfl) ⟨7699424, by rfl⟩ : syracuseStep 10265899 = 15398849) B15398849
theorem B13687865 : Blo 2135435 13687865 := bstep (se 2 (by rfl) ⟨5132949, by rfl⟩ : syracuseStep 13687865 = 10265899) B10265899
theorem B9125243 : Blo 2135435 9125243 := bstep (se 1 (by rfl) ⟨6843932, by rfl⟩ : syracuseStep 9125243 = 13687865) B13687865
theorem B6083495 : Blo 2135435 6083495 := bstep (se 1 (by rfl) ⟨4562621, by rfl⟩ : syracuseStep 6083495 = 9125243) B9125243
theorem B4055663 : Blo 2135435 4055663 := bstep (se 1 (by rfl) ⟨3041747, by rfl⟩ : syracuseStep 4055663 = 6083495) B6083495
theorem B2703775 : Blo 2135435 2703775 := bstep (se 1 (by rfl) ⟨2027831, by rfl⟩ : syracuseStep 2703775 = 4055663) B4055663
theorem B3605033 : Blo 2135435 3605033 := bstep (se 2 (by rfl) ⟨1351887, by rfl⟩ : syracuseStep 3605033 = 2703775) B2703775
theorem B2403355 : Blo 2135435 2403355 := bstep (se 1 (by rfl) ⟨1802516, by rfl⟩ : syracuseStep 2403355 = 3605033) B3605033
theorem B3204473 : Blo 2135435 3204473 := bstep (se 2 (by rfl) ⟨1201677, by rfl⟩ : syracuseStep 3204473 = 2403355) B2403355
theorem B2136315 : Blo 2135435 2136315 := bstep (se 1 (by rfl) ⟨1602236, by rfl⟩ : syracuseStep 2136315 = 3204473) B3204473
theorem B17323733 : Blo 2135435 17323733 := bbase (se 7 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 17323733 = 406025) (by norm_num)
theorem B11549155 : Blo 2135435 11549155 := bstep (se 1 (by rfl) ⟨8661866, by rfl⟩ : syracuseStep 11549155 = 17323733) B17323733
theorem B15398873 : Blo 2135435 15398873 := bstep (se 2 (by rfl) ⟨5774577, by rfl⟩ : syracuseStep 15398873 = 11549155) B11549155
theorem B10265915 : Blo 2135435 10265915 := bstep (se 1 (by rfl) ⟨7699436, by rfl⟩ : syracuseStep 10265915 = 15398873) B15398873
theorem B6843943 : Blo 2135435 6843943 := bstep (se 1 (by rfl) ⟨5132957, by rfl⟩ : syracuseStep 6843943 = 10265915) B10265915
theorem B36501029 : Blo 2135435 36501029 := bstep (se 4 (by rfl) ⟨3421971, by rfl⟩ : syracuseStep 36501029 = 6843943) B6843943
theorem B24334019 : Blo 2135435 24334019 := bstep (se 1 (by rfl) ⟨18250514, by rfl⟩ : syracuseStep 24334019 = 36501029) B36501029
theorem B16222679 : Blo 2135435 16222679 := bstep (se 1 (by rfl) ⟨12167009, by rfl⟩ : syracuseStep 16222679 = 24334019) B24334019
theorem B10815119 : Blo 2135435 10815119 := bstep (se 1 (by rfl) ⟨8111339, by rfl⟩ : syracuseStep 10815119 = 16222679) B16222679
theorem B7210079 : Blo 2135435 7210079 := bstep (se 1 (by rfl) ⟨5407559, by rfl⟩ : syracuseStep 7210079 = 10815119) B10815119
theorem B4806719 : Blo 2135435 4806719 := bstep (se 1 (by rfl) ⟨3605039, by rfl⟩ : syracuseStep 4806719 = 7210079) B7210079
theorem B3204479 : Blo 2135435 3204479 := bstep (se 1 (by rfl) ⟨2403359, by rfl⟩ : syracuseStep 3204479 = 4806719) B4806719
theorem B2136319 : Blo 2135435 2136319 := bstep (se 1 (by rfl) ⟨1602239, by rfl⟩ : syracuseStep 2136319 = 3204479) B3204479
theorem B3204485 : Blo 2135435 3204485 := bbase (se 4 (by rfl) ⟨300420, by rfl⟩ : syracuseStep 3204485 = 600841) (by norm_num)
theorem B2136323 : Blo 2135435 2136323 := bstep (se 1 (by rfl) ⟨1602242, by rfl⟩ : syracuseStep 2136323 = 3204485) B3204485
theorem B3605053 : Blo 2135435 3605053 := bbase (se 3 (by rfl) ⟨675947, by rfl⟩ : syracuseStep 3605053 = 1351895) (by norm_num)
theorem B4806737 : Blo 2135435 4806737 := bstep (se 2 (by rfl) ⟨1802526, by rfl⟩ : syracuseStep 4806737 = 3605053) B3605053
theorem B3204491 : Blo 2135435 3204491 := bstep (se 1 (by rfl) ⟨2403368, by rfl⟩ : syracuseStep 3204491 = 4806737) B4806737
theorem B2136327 : Blo 2135435 2136327 := bstep (se 1 (by rfl) ⟨1602245, by rfl⟩ : syracuseStep 2136327 = 3204491) B3204491
theorem B2403373 : Blo 2135435 2403373 := bbase (se 3 (by rfl) ⟨450632, by rfl⟩ : syracuseStep 2403373 = 901265) (by norm_num)
theorem B3204497 : Blo 2135435 3204497 := bstep (se 2 (by rfl) ⟨1201686, by rfl⟩ : syracuseStep 3204497 = 2403373) B2403373
theorem B2136331 : Blo 2135435 2136331 := bstep (se 1 (by rfl) ⟨1602248, by rfl⟩ : syracuseStep 2136331 = 3204497) B3204497
theorem B7210133 : Blo 2135435 7210133 := bbase (se 6 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 7210133 = 337975) (by norm_num)
theorem B4806755 : Blo 2135435 4806755 := bstep (se 1 (by rfl) ⟨3605066, by rfl⟩ : syracuseStep 4806755 = 7210133) B7210133
theorem B3204503 : Blo 2135435 3204503 := bstep (se 1 (by rfl) ⟨2403377, by rfl⟩ : syracuseStep 3204503 = 4806755) B4806755
theorem B2136335 : Blo 2135435 2136335 := bstep (se 1 (by rfl) ⟨1602251, by rfl⟩ : syracuseStep 2136335 = 3204503) B3204503
theorem B3204509 : Blo 2135435 3204509 := bbase (se 3 (by rfl) ⟨600845, by rfl⟩ : syracuseStep 3204509 = 1201691) (by norm_num)
theorem B2136339 : Blo 2135435 2136339 := bstep (se 1 (by rfl) ⟨1602254, by rfl⟩ : syracuseStep 2136339 = 3204509) B3204509
theorem B4806773 : Blo 2135435 4806773 := bbase (se 5 (by rfl) ⟨225317, by rfl⟩ : syracuseStep 4806773 = 450635) (by norm_num)
theorem B3204515 : Blo 2135435 3204515 := bstep (se 1 (by rfl) ⟨2403386, by rfl⟩ : syracuseStep 3204515 = 4806773) B4806773
theorem B2136343 : Blo 2135435 2136343 := bstep (se 1 (by rfl) ⟨1602257, by rfl⟩ : syracuseStep 2136343 = 3204515) B3204515
theorem B2566513 : Blo 2135435 2566513 := bbase (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) (by norm_num)
theorem B3422017 : Blo 2135435 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B18250757 : Blo 2135435 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B12167171 : Blo 2135435 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B8111447 : Blo 2135435 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B5407631 : Blo 2135435 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B3605087 : Blo 2135435 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B2403391 : Blo 2135435 2403391 := bstep (se 1 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 2403391 = 3605087) B3605087
theorem B3204521 : Blo 2135435 3204521 := bstep (se 2 (by rfl) ⟨1201695, by rfl⟩ : syracuseStep 3204521 = 2403391) B2403391
theorem B2136347 : Blo 2135435 2136347 := bstep (se 1 (by rfl) ⟨1602260, by rfl⟩ : syracuseStep 2136347 = 3204521) B3204521
theorem B8111461 : Blo 2135435 8111461 := bbase (se 4 (by rfl) ⟨760449, by rfl⟩ : syracuseStep 8111461 = 1520899) (by norm_num)
theorem B10815281 : Blo 2135435 10815281 := bstep (se 2 (by rfl) ⟨4055730, by rfl⟩ : syracuseStep 10815281 = 8111461) B8111461
theorem B7210187 : Blo 2135435 7210187 := bstep (se 1 (by rfl) ⟨5407640, by rfl⟩ : syracuseStep 7210187 = 10815281) B10815281
theorem B4806791 : Blo 2135435 4806791 := bstep (se 1 (by rfl) ⟨3605093, by rfl⟩ : syracuseStep 4806791 = 7210187) B7210187
theorem B3204527 : Blo 2135435 3204527 := bstep (se 1 (by rfl) ⟨2403395, by rfl⟩ : syracuseStep 3204527 = 4806791) B4806791
theorem B2136351 : Blo 2135435 2136351 := bstep (se 1 (by rfl) ⟨1602263, by rfl⟩ : syracuseStep 2136351 = 3204527) B3204527
theorem B3204533 : Blo 2135435 3204533 := bbase (se 5 (by rfl) ⟨150212, by rfl⟩ : syracuseStep 3204533 = 300425) (by norm_num)
theorem B2136355 : Blo 2135435 2136355 := bstep (se 1 (by rfl) ⟨1602266, by rfl⟩ : syracuseStep 2136355 = 3204533) B3204533
theorem B5407661 : Blo 2135435 5407661 := bbase (se 3 (by rfl) ⟨1013936, by rfl⟩ : syracuseStep 5407661 = 2027873) (by norm_num)
theorem B3605107 : Blo 2135435 3605107 := bstep (se 1 (by rfl) ⟨2703830, by rfl⟩ : syracuseStep 3605107 = 5407661) B5407661
theorem B4806809 : Blo 2135435 4806809 := bstep (se 2 (by rfl) ⟨1802553, by rfl⟩ : syracuseStep 4806809 = 3605107) B3605107
theorem B3204539 : Blo 2135435 3204539 := bstep (se 1 (by rfl) ⟨2403404, by rfl⟩ : syracuseStep 3204539 = 4806809) B4806809
theorem B2136359 : Blo 2135435 2136359 := bstep (se 1 (by rfl) ⟨1602269, by rfl⟩ : syracuseStep 2136359 = 3204539) B3204539
theorem B2403409 : Blo 2135435 2403409 := bbase (se 2 (by rfl) ⟨901278, by rfl⟩ : syracuseStep 2403409 = 1802557) (by norm_num)
theorem B3204545 : Blo 2135435 3204545 := bstep (se 2 (by rfl) ⟨1201704, by rfl⟩ : syracuseStep 3204545 = 2403409) B2403409
theorem B2136363 : Blo 2135435 2136363 := bstep (se 1 (by rfl) ⟨1602272, by rfl⟩ : syracuseStep 2136363 = 3204545) B3204545
theorem B3041821 : Blo 2135435 3041821 := bbase (se 3 (by rfl) ⟨570341, by rfl⟩ : syracuseStep 3041821 = 1140683) (by norm_num)
theorem B4055761 : Blo 2135435 4055761 := bstep (se 2 (by rfl) ⟨1520910, by rfl⟩ : syracuseStep 4055761 = 3041821) B3041821
theorem B5407681 : Blo 2135435 5407681 := bstep (se 2 (by rfl) ⟨2027880, by rfl⟩ : syracuseStep 5407681 = 4055761) B4055761
theorem B7210241 : Blo 2135435 7210241 := bstep (se 2 (by rfl) ⟨2703840, by rfl⟩ : syracuseStep 7210241 = 5407681) B5407681
theorem B4806827 : Blo 2135435 4806827 := bstep (se 1 (by rfl) ⟨3605120, by rfl⟩ : syracuseStep 4806827 = 7210241) B7210241
theorem B3204551 : Blo 2135435 3204551 := bstep (se 1 (by rfl) ⟨2403413, by rfl⟩ : syracuseStep 3204551 = 4806827) B4806827
theorem B2136367 : Blo 2135435 2136367 := bstep (se 1 (by rfl) ⟨1602275, by rfl⟩ : syracuseStep 2136367 = 3204551) B3204551
theorem B3204557 : Blo 2135435 3204557 := bbase (se 3 (by rfl) ⟨600854, by rfl⟩ : syracuseStep 3204557 = 1201709) (by norm_num)
theorem B2136371 : Blo 2135435 2136371 := bstep (se 1 (by rfl) ⟨1602278, by rfl⟩ : syracuseStep 2136371 = 3204557) B3204557
theorem B4806845 : Blo 2135435 4806845 := bbase (se 3 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 4806845 = 1802567) (by norm_num)
theorem B3204563 : Blo 2135435 3204563 := bstep (se 1 (by rfl) ⟨2403422, by rfl⟩ : syracuseStep 3204563 = 4806845) B4806845
theorem B2136375 : Blo 2135435 2136375 := bstep (se 1 (by rfl) ⟨1602281, by rfl⟩ : syracuseStep 2136375 = 3204563) B3204563
theorem B3605141 : Blo 2135435 3605141 := bbase (se 6 (by rfl) ⟨84495, by rfl⟩ : syracuseStep 3605141 = 168991) (by norm_num)
theorem B2403427 : Blo 2135435 2403427 := bstep (se 1 (by rfl) ⟨1802570, by rfl⟩ : syracuseStep 2403427 = 3605141) B3605141
theorem B3204569 : Blo 2135435 3204569 := bstep (se 2 (by rfl) ⟨1201713, by rfl⟩ : syracuseStep 3204569 = 2403427) B2403427
theorem B2136379 : Blo 2135435 2136379 := bstep (se 1 (by rfl) ⟨1602284, by rfl⟩ : syracuseStep 2136379 = 3204569) B3204569
theorem B9250037 : Blo 2135435 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B6166691 : Blo 2135435 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B4111127 : Blo 2135435 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B2740751 : Blo 2135435 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B29234677 : Blo 2135435 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B38979569 : Blo 2135435 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B25986379 : Blo 2135435 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B34648505 : Blo 2135435 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B23099003 : Blo 2135435 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B15399335 : Blo 2135435 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B10266223 : Blo 2135435 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B13688297 : Blo 2135435 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B9125531 : Blo 2135435 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B6083687 : Blo 2135435 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B16223165 : Blo 2135435 16223165 := bstep (se 3 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 16223165 = 6083687) B6083687
theorem B10815443 : Blo 2135435 10815443 := bstep (se 1 (by rfl) ⟨8111582, by rfl⟩ : syracuseStep 10815443 = 16223165) B16223165
theorem B7210295 : Blo 2135435 7210295 := bstep (se 1 (by rfl) ⟨5407721, by rfl⟩ : syracuseStep 7210295 = 10815443) B10815443
theorem B4806863 : Blo 2135435 4806863 := bstep (se 1 (by rfl) ⟨3605147, by rfl⟩ : syracuseStep 4806863 = 7210295) B7210295
theorem B3204575 : Blo 2135435 3204575 := bstep (se 1 (by rfl) ⟨2403431, by rfl⟩ : syracuseStep 3204575 = 4806863) B4806863
theorem B2136383 : Blo 2135435 2136383 := bstep (se 1 (by rfl) ⟨1602287, by rfl⟩ : syracuseStep 2136383 = 3204575) B3204575
theorem B3204581 : Blo 2135435 3204581 := bbase (se 4 (by rfl) ⟨300429, by rfl⟩ : syracuseStep 3204581 = 600859) (by norm_num)
theorem B2136387 : Blo 2135435 2136387 := bstep (se 1 (by rfl) ⟨1602290, by rfl⟩ : syracuseStep 2136387 = 3204581) B3204581
theorem B22528469 : Blo 2135435 22528469 := bbase (se 7 (by rfl) ⟨264005, by rfl⟩ : syracuseStep 22528469 = 528011) (by norm_num)
theorem B15018979 : Blo 2135435 15018979 := bstep (se 1 (by rfl) ⟨11264234, by rfl⟩ : syracuseStep 15018979 = 22528469) B22528469
theorem B20025305 : Blo 2135435 20025305 := bstep (se 2 (by rfl) ⟨7509489, by rfl⟩ : syracuseStep 20025305 = 15018979) B15018979
theorem B13350203 : Blo 2135435 13350203 := bstep (se 1 (by rfl) ⟨10012652, by rfl⟩ : syracuseStep 13350203 = 20025305) B20025305
theorem B8900135 : Blo 2135435 8900135 := bstep (se 1 (by rfl) ⟨6675101, by rfl⟩ : syracuseStep 8900135 = 13350203) B13350203
theorem B5933423 : Blo 2135435 5933423 := bstep (se 1 (by rfl) ⟨4450067, by rfl⟩ : syracuseStep 5933423 = 8900135) B8900135
theorem B15822461 : Blo 2135435 15822461 := bstep (se 3 (by rfl) ⟨2966711, by rfl⟩ : syracuseStep 15822461 = 5933423) B5933423
theorem B10548307 : Blo 2135435 10548307 := bstep (se 1 (by rfl) ⟨7911230, by rfl⟩ : syracuseStep 10548307 = 15822461) B15822461
theorem B14064409 : Blo 2135435 14064409 := bstep (se 2 (by rfl) ⟨5274153, by rfl⟩ : syracuseStep 14064409 = 10548307) B10548307
theorem B18752545 : Blo 2135435 18752545 := bstep (se 2 (by rfl) ⟨7032204, by rfl⟩ : syracuseStep 18752545 = 14064409) B14064409
theorem B25003393 : Blo 2135435 25003393 := bstep (se 2 (by rfl) ⟨9376272, by rfl⟩ : syracuseStep 25003393 = 18752545) B18752545
theorem B133351429 : Blo 2135435 133351429 := bstep (se 4 (by rfl) ⟨12501696, by rfl⟩ : syracuseStep 133351429 = 25003393) B25003393
theorem B177801905 : Blo 2135435 177801905 := bstep (se 2 (by rfl) ⟨66675714, by rfl⟩ : syracuseStep 177801905 = 133351429) B133351429
theorem B118534603 : Blo 2135435 118534603 := bstep (se 1 (by rfl) ⟨88900952, by rfl⟩ : syracuseStep 118534603 = 177801905) B177801905
theorem B158046137 : Blo 2135435 158046137 := bstep (se 2 (by rfl) ⟨59267301, by rfl⟩ : syracuseStep 158046137 = 118534603) B118534603
theorem B105364091 : Blo 2135435 105364091 := bstep (se 1 (by rfl) ⟨79023068, by rfl⟩ : syracuseStep 105364091 = 158046137) B158046137
theorem B70242727 : Blo 2135435 70242727 := bstep (se 1 (by rfl) ⟨52682045, by rfl⟩ : syracuseStep 70242727 = 105364091) B105364091
theorem B93656969 : Blo 2135435 93656969 := bstep (se 2 (by rfl) ⟨35121363, by rfl⟩ : syracuseStep 93656969 = 70242727) B70242727
theorem B62437979 : Blo 2135435 62437979 := bstep (se 1 (by rfl) ⟨46828484, by rfl⟩ : syracuseStep 62437979 = 93656969) B93656969
theorem B166501277 : Blo 2135435 166501277 := bstep (se 3 (by rfl) ⟨31218989, by rfl⟩ : syracuseStep 166501277 = 62437979) B62437979
theorem B111000851 : Blo 2135435 111000851 := bstep (se 1 (by rfl) ⟨83250638, by rfl⟩ : syracuseStep 111000851 = 166501277) B166501277
theorem B74000567 : Blo 2135435 74000567 := bstep (se 1 (by rfl) ⟨55500425, by rfl⟩ : syracuseStep 74000567 = 111000851) B111000851
theorem B49333711 : Blo 2135435 49333711 := bstep (se 1 (by rfl) ⟨37000283, by rfl⟩ : syracuseStep 49333711 = 74000567) B74000567
theorem B65778281 : Blo 2135435 65778281 := bstep (se 2 (by rfl) ⟨24666855, by rfl⟩ : syracuseStep 65778281 = 49333711) B49333711
theorem B43852187 : Blo 2135435 43852187 := bstep (se 1 (by rfl) ⟨32889140, by rfl⟩ : syracuseStep 43852187 = 65778281) B65778281
theorem B29234791 : Blo 2135435 29234791 := bstep (se 1 (by rfl) ⟨21926093, by rfl⟩ : syracuseStep 29234791 = 43852187) B43852187
theorem B38979721 : Blo 2135435 38979721 := bstep (se 2 (by rfl) ⟨14617395, by rfl⟩ : syracuseStep 38979721 = 29234791) B29234791
theorem B51972961 : Blo 2135435 51972961 := bstep (se 2 (by rfl) ⟨19489860, by rfl⟩ : syracuseStep 51972961 = 38979721) B38979721
theorem B69297281 : Blo 2135435 69297281 := bstep (se 2 (by rfl) ⟨25986480, by rfl⟩ : syracuseStep 69297281 = 51972961) B51972961
theorem B46198187 : Blo 2135435 46198187 := bstep (se 1 (by rfl) ⟨34648640, by rfl⟩ : syracuseStep 46198187 = 69297281) B69297281
theorem B30798791 : Blo 2135435 30798791 := bstep (se 1 (by rfl) ⟨23099093, by rfl⟩ : syracuseStep 30798791 = 46198187) B46198187
theorem B20532527 : Blo 2135435 20532527 := bstep (se 1 (by rfl) ⟨15399395, by rfl⟩ : syracuseStep 20532527 = 30798791) B30798791
theorem B13688351 : Blo 2135435 13688351 := bstep (se 1 (by rfl) ⟨10266263, by rfl⟩ : syracuseStep 13688351 = 20532527) B20532527
theorem B9125567 : Blo 2135435 9125567 := bstep (se 1 (by rfl) ⟨6844175, by rfl⟩ : syracuseStep 9125567 = 13688351) B13688351
theorem B6083711 : Blo 2135435 6083711 := bstep (se 1 (by rfl) ⟨4562783, by rfl⟩ : syracuseStep 6083711 = 9125567) B9125567
theorem B4055807 : Blo 2135435 4055807 := bstep (se 1 (by rfl) ⟨3041855, by rfl⟩ : syracuseStep 4055807 = 6083711) B6083711
theorem B2703871 : Blo 2135435 2703871 := bstep (se 1 (by rfl) ⟨2027903, by rfl⟩ : syracuseStep 2703871 = 4055807) B4055807
theorem B3605161 : Blo 2135435 3605161 := bstep (se 2 (by rfl) ⟨1351935, by rfl⟩ : syracuseStep 3605161 = 2703871) B2703871
theorem B4806881 : Blo 2135435 4806881 := bstep (se 2 (by rfl) ⟨1802580, by rfl⟩ : syracuseStep 4806881 = 3605161) B3605161
theorem B3204587 : Blo 2135435 3204587 := bstep (se 1 (by rfl) ⟨2403440, by rfl⟩ : syracuseStep 3204587 = 4806881) B4806881
theorem B2136391 : Blo 2135435 2136391 := bstep (se 1 (by rfl) ⟨1602293, by rfl⟩ : syracuseStep 2136391 = 3204587) B3204587
theorem B2403445 : Blo 2135435 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B3204593 : Blo 2135435 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B2136395 : Blo 2135435 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B2703881 : Blo 2135435 2703881 := bbase (se 2 (by rfl) ⟨1013955, by rfl⟩ : syracuseStep 2703881 = 2027911) (by norm_num)
theorem B7210349 : Blo 2135435 7210349 := bstep (se 3 (by rfl) ⟨1351940, by rfl⟩ : syracuseStep 7210349 = 2703881) B2703881
theorem B4806899 : Blo 2135435 4806899 := bstep (se 1 (by rfl) ⟨3605174, by rfl⟩ : syracuseStep 4806899 = 7210349) B7210349
theorem B3204599 : Blo 2135435 3204599 := bstep (se 1 (by rfl) ⟨2403449, by rfl⟩ : syracuseStep 3204599 = 4806899) B4806899
theorem B2136399 : Blo 2135435 2136399 := bstep (se 1 (by rfl) ⟨1602299, by rfl⟩ : syracuseStep 2136399 = 3204599) B3204599
theorem B3204605 : Blo 2135435 3204605 := bbase (se 3 (by rfl) ⟨600863, by rfl⟩ : syracuseStep 3204605 = 1201727) (by norm_num)
theorem B2136403 : Blo 2135435 2136403 := bstep (se 1 (by rfl) ⟨1602302, by rfl⟩ : syracuseStep 2136403 = 3204605) B3204605
theorem B4806917 : Blo 2135435 4806917 := bbase (se 4 (by rfl) ⟨450648, by rfl⟩ : syracuseStep 4806917 = 901297) (by norm_num)
theorem B3204611 : Blo 2135435 3204611 := bstep (se 1 (by rfl) ⟨2403458, by rfl⟩ : syracuseStep 3204611 = 4806917) B4806917
theorem B2136407 : Blo 2135435 2136407 := bstep (se 1 (by rfl) ⟨1602305, by rfl⟩ : syracuseStep 2136407 = 3204611) B3204611
theorem B4055845 : Blo 2135435 4055845 := bbase (se 4 (by rfl) ⟨380235, by rfl⟩ : syracuseStep 4055845 = 760471) (by norm_num)
theorem B5407793 : Blo 2135435 5407793 := bstep (se 2 (by rfl) ⟨2027922, by rfl⟩ : syracuseStep 5407793 = 4055845) B4055845
theorem B3605195 : Blo 2135435 3605195 := bstep (se 1 (by rfl) ⟨2703896, by rfl⟩ : syracuseStep 3605195 = 5407793) B5407793
theorem B2403463 : Blo 2135435 2403463 := bstep (se 1 (by rfl) ⟨1802597, by rfl⟩ : syracuseStep 2403463 = 3605195) B3605195
theorem B3204617 : Blo 2135435 3204617 := bstep (se 2 (by rfl) ⟨1201731, by rfl⟩ : syracuseStep 3204617 = 2403463) B2403463
theorem B2136411 : Blo 2135435 2136411 := bstep (se 1 (by rfl) ⟨1602308, by rfl⟩ : syracuseStep 2136411 = 3204617) B3204617
theorem B10815605 : Blo 2135435 10815605 := bbase (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) (by norm_num)
theorem B7210403 : Blo 2135435 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B4806935 : Blo 2135435 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B3204623 : Blo 2135435 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B2136415 : Blo 2135435 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B3204629 : Blo 2135435 3204629 := bbase (se 6 (by rfl) ⟨75108, by rfl⟩ : syracuseStep 3204629 = 150217) (by norm_num)
theorem B2136419 : Blo 2135435 2136419 := bstep (se 1 (by rfl) ⟨1602314, by rfl⟩ : syracuseStep 2136419 = 3204629) B3204629
theorem B6844277 : Blo 2135435 6844277 := bbase (se 5 (by rfl) ⟨320825, by rfl⟩ : syracuseStep 6844277 = 641651) (by norm_num)
theorem B18251405 : Blo 2135435 18251405 := bstep (se 3 (by rfl) ⟨3422138, by rfl⟩ : syracuseStep 18251405 = 6844277) B6844277
theorem B12167603 : Blo 2135435 12167603 := bstep (se 1 (by rfl) ⟨9125702, by rfl⟩ : syracuseStep 12167603 = 18251405) B18251405
theorem B8111735 : Blo 2135435 8111735 := bstep (se 1 (by rfl) ⟨6083801, by rfl⟩ : syracuseStep 8111735 = 12167603) B12167603
theorem B5407823 : Blo 2135435 5407823 := bstep (se 1 (by rfl) ⟨4055867, by rfl⟩ : syracuseStep 5407823 = 8111735) B8111735
theorem B3605215 : Blo 2135435 3605215 := bstep (se 1 (by rfl) ⟨2703911, by rfl⟩ : syracuseStep 3605215 = 5407823) B5407823
theorem B4806953 : Blo 2135435 4806953 := bstep (se 2 (by rfl) ⟨1802607, by rfl⟩ : syracuseStep 4806953 = 3605215) B3605215
theorem B3204635 : Blo 2135435 3204635 := bstep (se 1 (by rfl) ⟨2403476, by rfl⟩ : syracuseStep 3204635 = 4806953) B4806953
theorem B2136423 : Blo 2135435 2136423 := bstep (se 1 (by rfl) ⟨1602317, by rfl⟩ : syracuseStep 2136423 = 3204635) B3204635
theorem B2403481 : Blo 2135435 2403481 := bbase (se 2 (by rfl) ⟨901305, by rfl⟩ : syracuseStep 2403481 = 1802611) (by norm_num)
theorem B3204641 : Blo 2135435 3204641 := bstep (se 2 (by rfl) ⟨1201740, by rfl⟩ : syracuseStep 3204641 = 2403481) B2403481
theorem B2136427 : Blo 2135435 2136427 := bstep (se 1 (by rfl) ⟨1602320, by rfl⟩ : syracuseStep 2136427 = 3204641) B3204641
theorem B8111765 : Blo 2135435 8111765 := bbase (se 6 (by rfl) ⟨190119, by rfl⟩ : syracuseStep 8111765 = 380239) (by norm_num)
theorem B5407843 : Blo 2135435 5407843 := bstep (se 1 (by rfl) ⟨4055882, by rfl⟩ : syracuseStep 5407843 = 8111765) B8111765
theorem B7210457 : Blo 2135435 7210457 := bstep (se 2 (by rfl) ⟨2703921, by rfl⟩ : syracuseStep 7210457 = 5407843) B5407843
theorem B4806971 : Blo 2135435 4806971 := bstep (se 1 (by rfl) ⟨3605228, by rfl⟩ : syracuseStep 4806971 = 7210457) B7210457
theorem B3204647 : Blo 2135435 3204647 := bstep (se 1 (by rfl) ⟨2403485, by rfl⟩ : syracuseStep 3204647 = 4806971) B4806971
theorem B2136431 : Blo 2135435 2136431 := bstep (se 1 (by rfl) ⟨1602323, by rfl⟩ : syracuseStep 2136431 = 3204647) B3204647
theorem B3204653 : Blo 2135435 3204653 := bbase (se 3 (by rfl) ⟨600872, by rfl⟩ : syracuseStep 3204653 = 1201745) (by norm_num)
theorem B2136435 : Blo 2135435 2136435 := bstep (se 1 (by rfl) ⟨1602326, by rfl⟩ : syracuseStep 2136435 = 3204653) B3204653
theorem B4806989 : Blo 2135435 4806989 := bbase (se 3 (by rfl) ⟨901310, by rfl⟩ : syracuseStep 4806989 = 1802621) (by norm_num)
theorem B3204659 : Blo 2135435 3204659 := bstep (se 1 (by rfl) ⟨2403494, by rfl⟩ : syracuseStep 3204659 = 4806989) B4806989
theorem B2136439 : Blo 2135435 2136439 := bstep (se 1 (by rfl) ⟨1602329, by rfl⟩ : syracuseStep 2136439 = 3204659) B3204659
theorem B2703937 : Blo 2135435 2703937 := bbase (se 2 (by rfl) ⟨1013976, by rfl⟩ : syracuseStep 2703937 = 2027953) (by norm_num)
theorem B3605249 : Blo 2135435 3605249 := bstep (se 2 (by rfl) ⟨1351968, by rfl⟩ : syracuseStep 3605249 = 2703937) B2703937
theorem B2403499 : Blo 2135435 2403499 := bstep (se 1 (by rfl) ⟨1802624, by rfl⟩ : syracuseStep 2403499 = 3605249) B3605249
theorem B3204665 : Blo 2135435 3204665 := bstep (se 2 (by rfl) ⟨1201749, by rfl⟩ : syracuseStep 3204665 = 2403499) B2403499
theorem B2136443 : Blo 2135435 2136443 := bstep (se 1 (by rfl) ⟨1602332, by rfl⟩ : syracuseStep 2136443 = 3204665) B3204665
theorem B2566633 : Blo 2135435 2566633 := bbase (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) (by norm_num)
theorem B3422177 : Blo 2135435 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B2281451 : Blo 2135435 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B24335477 : Blo 2135435 24335477 := bstep (se 5 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 24335477 = 2281451) B2281451
theorem B16223651 : Blo 2135435 16223651 := bstep (se 1 (by rfl) ⟨12167738, by rfl⟩ : syracuseStep 16223651 = 24335477) B24335477
theorem B10815767 : Blo 2135435 10815767 := bstep (se 1 (by rfl) ⟨8111825, by rfl⟩ : syracuseStep 10815767 = 16223651) B16223651
theorem B7210511 : Blo 2135435 7210511 := bstep (se 1 (by rfl) ⟨5407883, by rfl⟩ : syracuseStep 7210511 = 10815767) B10815767
theorem B4807007 : Blo 2135435 4807007 := bstep (se 1 (by rfl) ⟨3605255, by rfl⟩ : syracuseStep 4807007 = 7210511) B7210511
theorem B3204671 : Blo 2135435 3204671 := bstep (se 1 (by rfl) ⟨2403503, by rfl⟩ : syracuseStep 3204671 = 4807007) B4807007
theorem B2136447 : Blo 2135435 2136447 := bstep (se 1 (by rfl) ⟨1602335, by rfl⟩ : syracuseStep 2136447 = 3204671) B3204671
theorem B3204677 : Blo 2135435 3204677 := bbase (se 4 (by rfl) ⟨300438, by rfl⟩ : syracuseStep 3204677 = 600877) (by norm_num)
theorem B2136451 : Blo 2135435 2136451 := bstep (se 1 (by rfl) ⟨1602338, by rfl⟩ : syracuseStep 2136451 = 3204677) B3204677
theorem B3605269 : Blo 2135435 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B4807025 : Blo 2135435 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B3204683 : Blo 2135435 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B2136455 : Blo 2135435 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B2403517 : Blo 2135435 2403517 := bbase (se 3 (by rfl) ⟨450659, by rfl⟩ : syracuseStep 2403517 = 901319) (by norm_num)
theorem B3204689 : Blo 2135435 3204689 := bstep (se 2 (by rfl) ⟨1201758, by rfl⟩ : syracuseStep 3204689 = 2403517) B2403517
theorem B2136459 : Blo 2135435 2136459 := bstep (se 1 (by rfl) ⟨1602344, by rfl⟩ : syracuseStep 2136459 = 3204689) B3204689
theorem B7210565 : Blo 2135435 7210565 := bbase (se 4 (by rfl) ⟨675990, by rfl⟩ : syracuseStep 7210565 = 1351981) (by norm_num)
theorem B4807043 : Blo 2135435 4807043 := bstep (se 1 (by rfl) ⟨3605282, by rfl⟩ : syracuseStep 4807043 = 7210565) B7210565
theorem B3204695 : Blo 2135435 3204695 := bstep (se 1 (by rfl) ⟨2403521, by rfl⟩ : syracuseStep 3204695 = 4807043) B4807043
theorem B2136463 : Blo 2135435 2136463 := bstep (se 1 (by rfl) ⟨1602347, by rfl⟩ : syracuseStep 2136463 = 3204695) B3204695
theorem B3204701 : Blo 2135435 3204701 := bbase (se 3 (by rfl) ⟨600881, by rfl⟩ : syracuseStep 3204701 = 1201763) (by norm_num)
theorem B2136467 : Blo 2135435 2136467 := bstep (se 1 (by rfl) ⟨1602350, by rfl⟩ : syracuseStep 2136467 = 3204701) B3204701
theorem B4807061 : Blo 2135435 4807061 := bbase (se 6 (by rfl) ⟨112665, by rfl⟩ : syracuseStep 4807061 = 225331) (by norm_num)
theorem B3204707 : Blo 2135435 3204707 := bstep (se 1 (by rfl) ⟨2403530, by rfl⟩ : syracuseStep 3204707 = 4807061) B4807061
theorem B2136471 : Blo 2135435 2136471 := bstep (se 1 (by rfl) ⟨1602353, by rfl⟩ : syracuseStep 2136471 = 3204707) B3204707
theorem B2887501 : Blo 2135435 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B3850001 : Blo 2135435 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B2566667 : Blo 2135435 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B6844445 : Blo 2135435 6844445 := bstep (se 3 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 6844445 = 2566667) B2566667
theorem B4562963 : Blo 2135435 4562963 := bstep (se 1 (by rfl) ⟨3422222, by rfl⟩ : syracuseStep 4562963 = 6844445) B6844445
theorem B3041975 : Blo 2135435 3041975 := bstep (se 1 (by rfl) ⟨2281481, by rfl⟩ : syracuseStep 3041975 = 4562963) B4562963
theorem B8111933 : Blo 2135435 8111933 := bstep (se 3 (by rfl) ⟨1520987, by rfl⟩ : syracuseStep 8111933 = 3041975) B3041975
theorem B5407955 : Blo 2135435 5407955 := bstep (se 1 (by rfl) ⟨4055966, by rfl⟩ : syracuseStep 5407955 = 8111933) B8111933
theorem B3605303 : Blo 2135435 3605303 := bstep (se 1 (by rfl) ⟨2703977, by rfl⟩ : syracuseStep 3605303 = 5407955) B5407955
theorem B2403535 : Blo 2135435 2403535 := bstep (se 1 (by rfl) ⟨1802651, by rfl⟩ : syracuseStep 2403535 = 3605303) B3605303
theorem B3204713 : Blo 2135435 3204713 := bstep (se 2 (by rfl) ⟨1201767, by rfl⟩ : syracuseStep 3204713 = 2403535) B2403535
theorem B2136475 : Blo 2135435 2136475 := bstep (se 1 (by rfl) ⟨1602356, by rfl⟩ : syracuseStep 2136475 = 3204713) B3204713
theorem B9125941 : Blo 2135435 9125941 := bbase (se 5 (by rfl) ⟨427778, by rfl⟩ : syracuseStep 9125941 = 855557) (by norm_num)
theorem B12167921 : Blo 2135435 12167921 := bstep (se 2 (by rfl) ⟨4562970, by rfl⟩ : syracuseStep 12167921 = 9125941) B9125941
theorem B8111947 : Blo 2135435 8111947 := bstep (se 1 (by rfl) ⟨6083960, by rfl⟩ : syracuseStep 8111947 = 12167921) B12167921
theorem B10815929 : Blo 2135435 10815929 := bstep (se 2 (by rfl) ⟨4055973, by rfl⟩ : syracuseStep 10815929 = 8111947) B8111947
theorem B7210619 : Blo 2135435 7210619 := bstep (se 1 (by rfl) ⟨5407964, by rfl⟩ : syracuseStep 7210619 = 10815929) B10815929
theorem B4807079 : Blo 2135435 4807079 := bstep (se 1 (by rfl) ⟨3605309, by rfl⟩ : syracuseStep 4807079 = 7210619) B7210619
theorem B3204719 : Blo 2135435 3204719 := bstep (se 1 (by rfl) ⟨2403539, by rfl⟩ : syracuseStep 3204719 = 4807079) B4807079
theorem B2136479 : Blo 2135435 2136479 := bstep (se 1 (by rfl) ⟨1602359, by rfl⟩ : syracuseStep 2136479 = 3204719) B3204719
theorem B3204725 : Blo 2135435 3204725 := bbase (se 5 (by rfl) ⟨150221, by rfl⟩ : syracuseStep 3204725 = 300443) (by norm_num)
theorem B2136483 : Blo 2135435 2136483 := bstep (se 1 (by rfl) ⟨1602362, by rfl⟩ : syracuseStep 2136483 = 3204725) B3204725
theorem B4055989 : Blo 2135435 4055989 := bbase (se 5 (by rfl) ⟨190124, by rfl⟩ : syracuseStep 4055989 = 380249) (by norm_num)
theorem B5407985 : Blo 2135435 5407985 := bstep (se 2 (by rfl) ⟨2027994, by rfl⟩ : syracuseStep 5407985 = 4055989) B4055989
theorem B3605323 : Blo 2135435 3605323 := bstep (se 1 (by rfl) ⟨2703992, by rfl⟩ : syracuseStep 3605323 = 5407985) B5407985
theorem B4807097 : Blo 2135435 4807097 := bstep (se 2 (by rfl) ⟨1802661, by rfl⟩ : syracuseStep 4807097 = 3605323) B3605323
theorem B3204731 : Blo 2135435 3204731 := bstep (se 1 (by rfl) ⟨2403548, by rfl⟩ : syracuseStep 3204731 = 4807097) B4807097
theorem B2136487 : Blo 2135435 2136487 := bstep (se 1 (by rfl) ⟨1602365, by rfl⟩ : syracuseStep 2136487 = 3204731) B3204731
theorem B2403553 : Blo 2135435 2403553 := bbase (se 2 (by rfl) ⟨901332, by rfl⟩ : syracuseStep 2403553 = 1802665) (by norm_num)
theorem B3204737 : Blo 2135435 3204737 := bstep (se 2 (by rfl) ⟨1201776, by rfl⟩ : syracuseStep 3204737 = 2403553) B2403553
theorem B2136491 : Blo 2135435 2136491 := bstep (se 1 (by rfl) ⟨1602368, by rfl⟩ : syracuseStep 2136491 = 3204737) B3204737
theorem B5408005 : Blo 2135435 5408005 := bbase (se 4 (by rfl) ⟨507000, by rfl⟩ : syracuseStep 5408005 = 1014001) (by norm_num)
theorem B7210673 : Blo 2135435 7210673 := bstep (se 2 (by rfl) ⟨2704002, by rfl⟩ : syracuseStep 7210673 = 5408005) B5408005
theorem B4807115 : Blo 2135435 4807115 := bstep (se 1 (by rfl) ⟨3605336, by rfl⟩ : syracuseStep 4807115 = 7210673) B7210673
theorem B3204743 : Blo 2135435 3204743 := bstep (se 1 (by rfl) ⟨2403557, by rfl⟩ : syracuseStep 3204743 = 4807115) B4807115
theorem B2136495 : Blo 2135435 2136495 := bstep (se 1 (by rfl) ⟨1602371, by rfl⟩ : syracuseStep 2136495 = 3204743) B3204743
theorem B3204749 : Blo 2135435 3204749 := bbase (se 3 (by rfl) ⟨600890, by rfl⟩ : syracuseStep 3204749 = 1201781) (by norm_num)
theorem B2136499 : Blo 2135435 2136499 := bstep (se 1 (by rfl) ⟨1602374, by rfl⟩ : syracuseStep 2136499 = 3204749) B3204749
theorem B4807133 : Blo 2135435 4807133 := bbase (se 3 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 4807133 = 1802675) (by norm_num)
theorem B3204755 : Blo 2135435 3204755 := bstep (se 1 (by rfl) ⟨2403566, by rfl⟩ : syracuseStep 3204755 = 4807133) B4807133
theorem B2136503 : Blo 2135435 2136503 := bstep (se 1 (by rfl) ⟨1602377, by rfl⟩ : syracuseStep 2136503 = 3204755) B3204755
theorem B3605357 : Blo 2135435 3605357 := bbase (se 3 (by rfl) ⟨676004, by rfl⟩ : syracuseStep 3605357 = 1352009) (by norm_num)
theorem B2403571 : Blo 2135435 2403571 := bstep (se 1 (by rfl) ⟨1802678, by rfl⟩ : syracuseStep 2403571 = 3605357) B3605357
theorem B3204761 : Blo 2135435 3204761 := bstep (se 2 (by rfl) ⟨1201785, by rfl⟩ : syracuseStep 3204761 = 2403571) B2403571
theorem B2136507 : Blo 2135435 2136507 := bstep (se 1 (by rfl) ⟨1602380, by rfl⟩ : syracuseStep 2136507 = 3204761) B3204761
theorem B2195209 : Blo 2135435 2195209 := bbase (se 2 (by rfl) ⟨823203, by rfl⟩ : syracuseStep 2195209 = 1646407) (by norm_num)
theorem B2926945 : Blo 2135435 2926945 := bstep (se 2 (by rfl) ⟨1097604, by rfl⟩ : syracuseStep 2926945 = 2195209) B2195209
theorem B3902593 : Blo 2135435 3902593 := bstep (se 2 (by rfl) ⟨1463472, by rfl⟩ : syracuseStep 3902593 = 2926945) B2926945
theorem B5203457 : Blo 2135435 5203457 := bstep (se 2 (by rfl) ⟨1951296, by rfl⟩ : syracuseStep 5203457 = 3902593) B3902593
theorem B3468971 : Blo 2135435 3468971 := bstep (se 1 (by rfl) ⟨2601728, by rfl⟩ : syracuseStep 3468971 = 5203457) B5203457
theorem B9250589 : Blo 2135435 9250589 := bstep (se 3 (by rfl) ⟨1734485, by rfl⟩ : syracuseStep 9250589 = 3468971) B3468971
theorem B6167059 : Blo 2135435 6167059 := bstep (se 1 (by rfl) ⟨4625294, by rfl⟩ : syracuseStep 6167059 = 9250589) B9250589
theorem B32890981 : Blo 2135435 32890981 := bstep (se 4 (by rfl) ⟨3083529, by rfl⟩ : syracuseStep 32890981 = 6167059) B6167059
theorem B43854641 : Blo 2135435 43854641 := bstep (se 2 (by rfl) ⟨16445490, by rfl⟩ : syracuseStep 43854641 = 32890981) B32890981
theorem B29236427 : Blo 2135435 29236427 := bstep (se 1 (by rfl) ⟨21927320, by rfl⟩ : syracuseStep 29236427 = 43854641) B43854641
theorem B19490951 : Blo 2135435 19490951 := bstep (se 1 (by rfl) ⟨14618213, by rfl⟩ : syracuseStep 19490951 = 29236427) B29236427
theorem B12993967 : Blo 2135435 12993967 := bstep (se 1 (by rfl) ⟨9745475, by rfl⟩ : syracuseStep 12993967 = 19490951) B19490951
theorem B17325289 : Blo 2135435 17325289 := bstep (se 2 (by rfl) ⟨6496983, by rfl⟩ : syracuseStep 17325289 = 12993967) B12993967
theorem B23100385 : Blo 2135435 23100385 := bstep (se 2 (by rfl) ⟨8662644, by rfl⟩ : syracuseStep 23100385 = 17325289) B17325289
theorem B30800513 : Blo 2135435 30800513 := bstep (se 2 (by rfl) ⟨11550192, by rfl⟩ : syracuseStep 30800513 = 23100385) B23100385
theorem B20533675 : Blo 2135435 20533675 := bstep (se 1 (by rfl) ⟨15400256, by rfl⟩ : syracuseStep 20533675 = 30800513) B30800513
theorem B27378233 : Blo 2135435 27378233 := bstep (se 2 (by rfl) ⟨10266837, by rfl⟩ : syracuseStep 27378233 = 20533675) B20533675
theorem B18252155 : Blo 2135435 18252155 := bstep (se 1 (by rfl) ⟨13689116, by rfl⟩ : syracuseStep 18252155 = 27378233) B27378233
theorem B12168103 : Blo 2135435 12168103 := bstep (se 1 (by rfl) ⟨9126077, by rfl⟩ : syracuseStep 12168103 = 18252155) B18252155
theorem B16224137 : Blo 2135435 16224137 := bstep (se 2 (by rfl) ⟨6084051, by rfl⟩ : syracuseStep 16224137 = 12168103) B12168103
theorem B10816091 : Blo 2135435 10816091 := bstep (se 1 (by rfl) ⟨8112068, by rfl⟩ : syracuseStep 10816091 = 16224137) B16224137
theorem B7210727 : Blo 2135435 7210727 := bstep (se 1 (by rfl) ⟨5408045, by rfl⟩ : syracuseStep 7210727 = 10816091) B10816091
theorem B4807151 : Blo 2135435 4807151 := bstep (se 1 (by rfl) ⟨3605363, by rfl⟩ : syracuseStep 4807151 = 7210727) B7210727
theorem B3204767 : Blo 2135435 3204767 := bstep (se 1 (by rfl) ⟨2403575, by rfl⟩ : syracuseStep 3204767 = 4807151) B4807151
theorem B2136511 : Blo 2135435 2136511 := bstep (se 1 (by rfl) ⟨1602383, by rfl⟩ : syracuseStep 2136511 = 3204767) B3204767
theorem B3204773 : Blo 2135435 3204773 := bbase (se 4 (by rfl) ⟨300447, by rfl⟩ : syracuseStep 3204773 = 600895) (by norm_num)
theorem B2136515 : Blo 2135435 2136515 := bstep (se 1 (by rfl) ⟨1602386, by rfl⟩ : syracuseStep 2136515 = 3204773) B3204773
theorem B2704033 : Blo 2135435 2704033 := bbase (se 2 (by rfl) ⟨1014012, by rfl⟩ : syracuseStep 2704033 = 2028025) (by norm_num)
theorem B3605377 : Blo 2135435 3605377 := bstep (se 2 (by rfl) ⟨1352016, by rfl⟩ : syracuseStep 3605377 = 2704033) B2704033
theorem B4807169 : Blo 2135435 4807169 := bstep (se 2 (by rfl) ⟨1802688, by rfl⟩ : syracuseStep 4807169 = 3605377) B3605377
theorem B3204779 : Blo 2135435 3204779 := bstep (se 1 (by rfl) ⟨2403584, by rfl⟩ : syracuseStep 3204779 = 4807169) B4807169
theorem B2136519 : Blo 2135435 2136519 := bstep (se 1 (by rfl) ⟨1602389, by rfl⟩ : syracuseStep 2136519 = 3204779) B3204779
theorem B2403589 : Blo 2135435 2403589 := bbase (se 4 (by rfl) ⟨225336, by rfl⟩ : syracuseStep 2403589 = 450673) (by norm_num)
theorem B3204785 : Blo 2135435 3204785 := bstep (se 2 (by rfl) ⟨1201794, by rfl⟩ : syracuseStep 3204785 = 2403589) B2403589
theorem B2136523 : Blo 2135435 2136523 := bstep (se 1 (by rfl) ⟨1602392, by rfl⟩ : syracuseStep 2136523 = 3204785) B3204785
theorem B2281537 : Blo 2135435 2281537 := bbase (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) (by norm_num)
theorem B3042049 : Blo 2135435 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B4056065 : Blo 2135435 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B2704043 : Blo 2135435 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B7210781 : Blo 2135435 7210781 := bstep (se 3 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 7210781 = 2704043) B2704043
theorem B4807187 : Blo 2135435 4807187 := bstep (se 1 (by rfl) ⟨3605390, by rfl⟩ : syracuseStep 4807187 = 7210781) B7210781
theorem B3204791 : Blo 2135435 3204791 := bstep (se 1 (by rfl) ⟨2403593, by rfl⟩ : syracuseStep 3204791 = 4807187) B4807187
theorem B2136527 : Blo 2135435 2136527 := bstep (se 1 (by rfl) ⟨1602395, by rfl⟩ : syracuseStep 2136527 = 3204791) B3204791
theorem B3204797 : Blo 2135435 3204797 := bbase (se 3 (by rfl) ⟨600899, by rfl⟩ : syracuseStep 3204797 = 1201799) (by norm_num)
theorem B2136531 : Blo 2135435 2136531 := bstep (se 1 (by rfl) ⟨1602398, by rfl⟩ : syracuseStep 2136531 = 3204797) B3204797
theorem B4807205 : Blo 2135435 4807205 := bbase (se 4 (by rfl) ⟨450675, by rfl⟩ : syracuseStep 4807205 = 901351) (by norm_num)
theorem B3204803 : Blo 2135435 3204803 := bstep (se 1 (by rfl) ⟨2403602, by rfl⟩ : syracuseStep 3204803 = 4807205) B4807205
theorem B2136535 : Blo 2135435 2136535 := bstep (se 1 (by rfl) ⟨1602401, by rfl⟩ : syracuseStep 2136535 = 3204803) B3204803
theorem B5408117 : Blo 2135435 5408117 := bbase (se 5 (by rfl) ⟨253505, by rfl⟩ : syracuseStep 5408117 = 507011) (by norm_num)
theorem B3605411 : Blo 2135435 3605411 := bstep (se 1 (by rfl) ⟨2704058, by rfl⟩ : syracuseStep 3605411 = 5408117) B5408117
theorem B2403607 : Blo 2135435 2403607 := bstep (se 1 (by rfl) ⟨1802705, by rfl⟩ : syracuseStep 2403607 = 3605411) B3605411
theorem B3204809 : Blo 2135435 3204809 := bstep (se 2 (by rfl) ⟨1201803, by rfl⟩ : syracuseStep 3204809 = 2403607) B2403607
theorem B2136539 : Blo 2135435 2136539 := bstep (se 1 (by rfl) ⟨1602404, by rfl⟩ : syracuseStep 2136539 = 3204809) B3204809
theorem B8335061 : Blo 2135435 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B5556707 : Blo 2135435 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B3704471 : Blo 2135435 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B2469647 : Blo 2135435 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B6585725 : Blo 2135435 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B4390483 : Blo 2135435 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B5853977 : Blo 2135435 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B3902651 : Blo 2135435 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B41628277 : Blo 2135435 41628277 := bstep (se 5 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 41628277 = 3902651) B3902651
theorem B55504369 : Blo 2135435 55504369 := bstep (se 2 (by rfl) ⟨20814138, by rfl⟩ : syracuseStep 55504369 = 41628277) B41628277
theorem B74005825 : Blo 2135435 74005825 := bstep (se 2 (by rfl) ⟨27752184, by rfl⟩ : syracuseStep 74005825 = 55504369) B55504369
theorem B98674433 : Blo 2135435 98674433 := bstep (se 2 (by rfl) ⟨37002912, by rfl⟩ : syracuseStep 98674433 = 74005825) B74005825
theorem B65782955 : Blo 2135435 65782955 := bstep (se 1 (by rfl) ⟨49337216, by rfl⟩ : syracuseStep 65782955 = 98674433) B98674433
theorem B43855303 : Blo 2135435 43855303 := bstep (se 1 (by rfl) ⟨32891477, by rfl⟩ : syracuseStep 43855303 = 65782955) B65782955
theorem B58473737 : Blo 2135435 58473737 := bstep (se 2 (by rfl) ⟨21927651, by rfl⟩ : syracuseStep 58473737 = 43855303) B43855303
theorem B38982491 : Blo 2135435 38982491 := bstep (se 1 (by rfl) ⟨29236868, by rfl⟩ : syracuseStep 38982491 = 58473737) B58473737
theorem B25988327 : Blo 2135435 25988327 := bstep (se 1 (by rfl) ⟨19491245, by rfl⟩ : syracuseStep 25988327 = 38982491) B38982491
theorem B17325551 : Blo 2135435 17325551 := bstep (se 1 (by rfl) ⟨12994163, by rfl⟩ : syracuseStep 17325551 = 25988327) B25988327
theorem B11550367 : Blo 2135435 11550367 := bstep (se 1 (by rfl) ⟨8662775, by rfl⟩ : syracuseStep 11550367 = 17325551) B17325551
theorem B15400489 : Blo 2135435 15400489 := bstep (se 2 (by rfl) ⟨5775183, by rfl⟩ : syracuseStep 15400489 = 11550367) B11550367
theorem B20533985 : Blo 2135435 20533985 := bstep (se 2 (by rfl) ⟨7700244, by rfl⟩ : syracuseStep 20533985 = 15400489) B15400489
theorem B13689323 : Blo 2135435 13689323 := bstep (se 1 (by rfl) ⟨10266992, by rfl⟩ : syracuseStep 13689323 = 20533985) B20533985
theorem B9126215 : Blo 2135435 9126215 := bstep (se 1 (by rfl) ⟨6844661, by rfl⟩ : syracuseStep 9126215 = 13689323) B13689323
theorem B6084143 : Blo 2135435 6084143 := bstep (se 1 (by rfl) ⟨4563107, by rfl⟩ : syracuseStep 6084143 = 9126215) B9126215
theorem B4056095 : Blo 2135435 4056095 := bstep (se 1 (by rfl) ⟨3042071, by rfl⟩ : syracuseStep 4056095 = 6084143) B6084143
theorem B10816253 : Blo 2135435 10816253 := bstep (se 3 (by rfl) ⟨2028047, by rfl⟩ : syracuseStep 10816253 = 4056095) B4056095
theorem B7210835 : Blo 2135435 7210835 := bstep (se 1 (by rfl) ⟨5408126, by rfl⟩ : syracuseStep 7210835 = 10816253) B10816253
theorem B4807223 : Blo 2135435 4807223 := bstep (se 1 (by rfl) ⟨3605417, by rfl⟩ : syracuseStep 4807223 = 7210835) B7210835
theorem B3204815 : Blo 2135435 3204815 := bstep (se 1 (by rfl) ⟨2403611, by rfl⟩ : syracuseStep 3204815 = 4807223) B4807223
theorem B2136543 : Blo 2135435 2136543 := bstep (se 1 (by rfl) ⟨1602407, by rfl⟩ : syracuseStep 2136543 = 3204815) B3204815
theorem B3204821 : Blo 2135435 3204821 := bbase (se 7 (by rfl) ⟨37556, by rfl⟩ : syracuseStep 3204821 = 75113) (by norm_num)
theorem B2136547 : Blo 2135435 2136547 := bstep (se 1 (by rfl) ⟨1602410, by rfl⟩ : syracuseStep 2136547 = 3204821) B3204821
theorem B4563125 : Blo 2135435 4563125 := bbase (se 5 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 4563125 = 427793) (by norm_num)
theorem B3042083 : Blo 2135435 3042083 := bstep (se 1 (by rfl) ⟨2281562, by rfl⟩ : syracuseStep 3042083 = 4563125) B4563125
theorem B8112221 : Blo 2135435 8112221 := bstep (se 3 (by rfl) ⟨1521041, by rfl⟩ : syracuseStep 8112221 = 3042083) B3042083
theorem B5408147 : Blo 2135435 5408147 := bstep (se 1 (by rfl) ⟨4056110, by rfl⟩ : syracuseStep 5408147 = 8112221) B8112221
theorem B3605431 : Blo 2135435 3605431 := bstep (se 1 (by rfl) ⟨2704073, by rfl⟩ : syracuseStep 3605431 = 5408147) B5408147
theorem B4807241 : Blo 2135435 4807241 := bstep (se 2 (by rfl) ⟨1802715, by rfl⟩ : syracuseStep 4807241 = 3605431) B3605431
theorem B3204827 : Blo 2135435 3204827 := bstep (se 1 (by rfl) ⟨2403620, by rfl⟩ : syracuseStep 3204827 = 4807241) B4807241
theorem B2136551 : Blo 2135435 2136551 := bstep (se 1 (by rfl) ⟨1602413, by rfl⟩ : syracuseStep 2136551 = 3204827) B3204827
theorem B2403625 : Blo 2135435 2403625 := bbase (se 2 (by rfl) ⟨901359, by rfl⟩ : syracuseStep 2403625 = 1802719) (by norm_num)
theorem B3204833 : Blo 2135435 3204833 := bstep (se 2 (by rfl) ⟨1201812, by rfl⟩ : syracuseStep 3204833 = 2403625) B2403625
theorem B2136555 : Blo 2135435 2136555 := bstep (se 1 (by rfl) ⟨1602416, by rfl⟩ : syracuseStep 2136555 = 3204833) B3204833
theorem B8222933 : Blo 2135435 8222933 := bbase (se 7 (by rfl) ⟨96362, by rfl⟩ : syracuseStep 8222933 = 192725) (by norm_num)
theorem B5481955 : Blo 2135435 5481955 := bstep (se 1 (by rfl) ⟨4111466, by rfl⟩ : syracuseStep 5481955 = 8222933) B8222933
theorem B7309273 : Blo 2135435 7309273 := bstep (se 2 (by rfl) ⟨2740977, by rfl⟩ : syracuseStep 7309273 = 5481955) B5481955
theorem B9745697 : Blo 2135435 9745697 := bstep (se 2 (by rfl) ⟨3654636, by rfl⟩ : syracuseStep 9745697 = 7309273) B7309273
theorem B6497131 : Blo 2135435 6497131 := bstep (se 1 (by rfl) ⟨4872848, by rfl⟩ : syracuseStep 6497131 = 9745697) B9745697
theorem B8662841 : Blo 2135435 8662841 := bstep (se 2 (by rfl) ⟨3248565, by rfl⟩ : syracuseStep 8662841 = 6497131) B6497131
theorem B5775227 : Blo 2135435 5775227 := bstep (se 1 (by rfl) ⟨4331420, by rfl⟩ : syracuseStep 5775227 = 8662841) B8662841
theorem B3850151 : Blo 2135435 3850151 := bstep (se 1 (by rfl) ⟨2887613, by rfl⟩ : syracuseStep 3850151 = 5775227) B5775227
theorem B10267069 : Blo 2135435 10267069 := bstep (se 3 (by rfl) ⟨1925075, by rfl⟩ : syracuseStep 10267069 = 3850151) B3850151
theorem B13689425 : Blo 2135435 13689425 := bstep (se 2 (by rfl) ⟨5133534, by rfl⟩ : syracuseStep 13689425 = 10267069) B10267069
theorem B9126283 : Blo 2135435 9126283 := bstep (se 1 (by rfl) ⟨6844712, by rfl⟩ : syracuseStep 9126283 = 13689425) B13689425
theorem B12168377 : Blo 2135435 12168377 := bstep (se 2 (by rfl) ⟨4563141, by rfl⟩ : syracuseStep 12168377 = 9126283) B9126283
theorem B8112251 : Blo 2135435 8112251 := bstep (se 1 (by rfl) ⟨6084188, by rfl⟩ : syracuseStep 8112251 = 12168377) B12168377
theorem B5408167 : Blo 2135435 5408167 := bstep (se 1 (by rfl) ⟨4056125, by rfl⟩ : syracuseStep 5408167 = 8112251) B8112251
theorem B7210889 : Blo 2135435 7210889 := bstep (se 2 (by rfl) ⟨2704083, by rfl⟩ : syracuseStep 7210889 = 5408167) B5408167
theorem B4807259 : Blo 2135435 4807259 := bstep (se 1 (by rfl) ⟨3605444, by rfl⟩ : syracuseStep 4807259 = 7210889) B7210889
theorem B3204839 : Blo 2135435 3204839 := bstep (se 1 (by rfl) ⟨2403629, by rfl⟩ : syracuseStep 3204839 = 4807259) B4807259
theorem B2136559 : Blo 2135435 2136559 := bstep (se 1 (by rfl) ⟨1602419, by rfl⟩ : syracuseStep 2136559 = 3204839) B3204839
theorem B3204845 : Blo 2135435 3204845 := bbase (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) (by norm_num)
theorem B2136563 : Blo 2135435 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B4807277 : Blo 2135435 4807277 := bbase (se 3 (by rfl) ⟨901364, by rfl⟩ : syracuseStep 4807277 = 1802729) (by norm_num)
theorem B3204851 : Blo 2135435 3204851 := bstep (se 1 (by rfl) ⟨2403638, by rfl⟩ : syracuseStep 3204851 = 4807277) B4807277
theorem B2136567 : Blo 2135435 2136567 := bstep (se 1 (by rfl) ⟨1602425, by rfl⟩ : syracuseStep 2136567 = 3204851) B3204851
theorem B4056149 : Blo 2135435 4056149 := bbase (se 8 (by rfl) ⟨23766, by rfl⟩ : syracuseStep 4056149 = 47533) (by norm_num)
theorem B2704099 : Blo 2135435 2704099 := bstep (se 1 (by rfl) ⟨2028074, by rfl⟩ : syracuseStep 2704099 = 4056149) B4056149
theorem B3605465 : Blo 2135435 3605465 := bstep (se 2 (by rfl) ⟨1352049, by rfl⟩ : syracuseStep 3605465 = 2704099) B2704099
theorem B2403643 : Blo 2135435 2403643 := bstep (se 1 (by rfl) ⟨1802732, by rfl⟩ : syracuseStep 2403643 = 3605465) B3605465
theorem B3204857 : Blo 2135435 3204857 := bstep (se 2 (by rfl) ⟨1201821, by rfl⟩ : syracuseStep 3204857 = 2403643) B2403643
theorem B2136571 : Blo 2135435 2136571 := bstep (se 1 (by rfl) ⟨1602428, by rfl⟩ : syracuseStep 2136571 = 3204857) B3204857
theorem B5775269 : Blo 2135435 5775269 := bbase (se 4 (by rfl) ⟨541431, by rfl⟩ : syracuseStep 5775269 = 1082863) (by norm_num)
theorem B61602869 : Blo 2135435 61602869 := bstep (se 5 (by rfl) ⟨2887634, by rfl⟩ : syracuseStep 61602869 = 5775269) B5775269
theorem B41068579 : Blo 2135435 41068579 := bstep (se 1 (by rfl) ⟨30801434, by rfl⟩ : syracuseStep 41068579 = 61602869) B61602869
theorem B54758105 : Blo 2135435 54758105 := bstep (se 2 (by rfl) ⟨20534289, by rfl⟩ : syracuseStep 54758105 = 41068579) B41068579
theorem B36505403 : Blo 2135435 36505403 := bstep (se 1 (by rfl) ⟨27379052, by rfl⟩ : syracuseStep 36505403 = 54758105) B54758105
theorem B24336935 : Blo 2135435 24336935 := bstep (se 1 (by rfl) ⟨18252701, by rfl⟩ : syracuseStep 24336935 = 36505403) B36505403
theorem B16224623 : Blo 2135435 16224623 := bstep (se 1 (by rfl) ⟨12168467, by rfl⟩ : syracuseStep 16224623 = 24336935) B24336935
theorem B10816415 : Blo 2135435 10816415 := bstep (se 1 (by rfl) ⟨8112311, by rfl⟩ : syracuseStep 10816415 = 16224623) B16224623
theorem B7210943 : Blo 2135435 7210943 := bstep (se 1 (by rfl) ⟨5408207, by rfl⟩ : syracuseStep 7210943 = 10816415) B10816415
theorem B4807295 : Blo 2135435 4807295 := bstep (se 1 (by rfl) ⟨3605471, by rfl⟩ : syracuseStep 4807295 = 7210943) B7210943
theorem B3204863 : Blo 2135435 3204863 := bstep (se 1 (by rfl) ⟨2403647, by rfl⟩ : syracuseStep 3204863 = 4807295) B4807295
theorem B2136575 : Blo 2135435 2136575 := bstep (se 1 (by rfl) ⟨1602431, by rfl⟩ : syracuseStep 2136575 = 3204863) B3204863
theorem B3204869 : Blo 2135435 3204869 := bbase (se 4 (by rfl) ⟨300456, by rfl⟩ : syracuseStep 3204869 = 600913) (by norm_num)
theorem B2136579 : Blo 2135435 2136579 := bstep (se 1 (by rfl) ⟨1602434, by rfl⟩ : syracuseStep 2136579 = 3204869) B3204869
theorem B3605485 : Blo 2135435 3605485 := bbase (se 3 (by rfl) ⟨676028, by rfl⟩ : syracuseStep 3605485 = 1352057) (by norm_num)
theorem B4807313 : Blo 2135435 4807313 := bstep (se 2 (by rfl) ⟨1802742, by rfl⟩ : syracuseStep 4807313 = 3605485) B3605485
theorem B3204875 : Blo 2135435 3204875 := bstep (se 1 (by rfl) ⟨2403656, by rfl⟩ : syracuseStep 3204875 = 4807313) B4807313
theorem B2136583 : Blo 2135435 2136583 := bstep (se 1 (by rfl) ⟨1602437, by rfl⟩ : syracuseStep 2136583 = 3204875) B3204875
theorem B2403661 : Blo 2135435 2403661 := bbase (se 3 (by rfl) ⟨450686, by rfl⟩ : syracuseStep 2403661 = 901373) (by norm_num)
theorem B3204881 : Blo 2135435 3204881 := bstep (se 2 (by rfl) ⟨1201830, by rfl⟩ : syracuseStep 3204881 = 2403661) B2403661
theorem B2136587 : Blo 2135435 2136587 := bstep (se 1 (by rfl) ⟨1602440, by rfl⟩ : syracuseStep 2136587 = 3204881) B3204881
theorem B7210997 : Blo 2135435 7210997 := bbase (se 5 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 7210997 = 676031) (by norm_num)
theorem B4807331 : Blo 2135435 4807331 := bstep (se 1 (by rfl) ⟨3605498, by rfl⟩ : syracuseStep 4807331 = 7210997) B7210997
theorem B3204887 : Blo 2135435 3204887 := bstep (se 1 (by rfl) ⟨2403665, by rfl⟩ : syracuseStep 3204887 = 4807331) B4807331
theorem B2136591 : Blo 2135435 2136591 := bstep (se 1 (by rfl) ⟨1602443, by rfl⟩ : syracuseStep 2136591 = 3204887) B3204887
theorem B3204893 : Blo 2135435 3204893 := bbase (se 3 (by rfl) ⟨600917, by rfl⟩ : syracuseStep 3204893 = 1201835) (by norm_num)
theorem B2136595 : Blo 2135435 2136595 := bstep (se 1 (by rfl) ⟨1602446, by rfl⟩ : syracuseStep 2136595 = 3204893) B3204893
theorem B4807349 : Blo 2135435 4807349 := bbase (se 5 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 4807349 = 450689) (by norm_num)
theorem B3204899 : Blo 2135435 3204899 := bstep (se 1 (by rfl) ⟨2403674, by rfl⟩ : syracuseStep 3204899 = 4807349) B4807349
theorem B2136599 : Blo 2135435 2136599 := bstep (se 1 (by rfl) ⟨1602449, by rfl⟩ : syracuseStep 2136599 = 3204899) B3204899
theorem B12168629 : Blo 2135435 12168629 := bbase (se 5 (by rfl) ⟨570404, by rfl⟩ : syracuseStep 12168629 = 1140809) (by norm_num)
theorem B8112419 : Blo 2135435 8112419 := bstep (se 1 (by rfl) ⟨6084314, by rfl⟩ : syracuseStep 8112419 = 12168629) B12168629
theorem B5408279 : Blo 2135435 5408279 := bstep (se 1 (by rfl) ⟨4056209, by rfl⟩ : syracuseStep 5408279 = 8112419) B8112419
theorem B3605519 : Blo 2135435 3605519 := bstep (se 1 (by rfl) ⟨2704139, by rfl⟩ : syracuseStep 3605519 = 5408279) B5408279
theorem B2403679 : Blo 2135435 2403679 := bstep (se 1 (by rfl) ⟨1802759, by rfl⟩ : syracuseStep 2403679 = 3605519) B3605519
theorem B3204905 : Blo 2135435 3204905 := bstep (se 2 (by rfl) ⟨1201839, by rfl⟩ : syracuseStep 3204905 = 2403679) B2403679
theorem B2136603 : Blo 2135435 2136603 := bstep (se 1 (by rfl) ⟨1602452, by rfl⟩ : syracuseStep 2136603 = 3204905) B3204905
theorem B6084325 : Blo 2135435 6084325 := bbase (se 4 (by rfl) ⟨570405, by rfl⟩ : syracuseStep 6084325 = 1140811) (by norm_num)
theorem B8112433 : Blo 2135435 8112433 := bstep (se 2 (by rfl) ⟨3042162, by rfl⟩ : syracuseStep 8112433 = 6084325) B6084325
theorem B10816577 : Blo 2135435 10816577 := bstep (se 2 (by rfl) ⟨4056216, by rfl⟩ : syracuseStep 10816577 = 8112433) B8112433
theorem B7211051 : Blo 2135435 7211051 := bstep (se 1 (by rfl) ⟨5408288, by rfl⟩ : syracuseStep 7211051 = 10816577) B10816577
theorem B4807367 : Blo 2135435 4807367 := bstep (se 1 (by rfl) ⟨3605525, by rfl⟩ : syracuseStep 4807367 = 7211051) B7211051
theorem B3204911 : Blo 2135435 3204911 := bstep (se 1 (by rfl) ⟨2403683, by rfl⟩ : syracuseStep 3204911 = 4807367) B4807367
theorem B2136607 : Blo 2135435 2136607 := bstep (se 1 (by rfl) ⟨1602455, by rfl⟩ : syracuseStep 2136607 = 3204911) B3204911
theorem B3204917 : Blo 2135435 3204917 := bbase (se 5 (by rfl) ⟨150230, by rfl⟩ : syracuseStep 3204917 = 300461) (by norm_num)
theorem B2136611 : Blo 2135435 2136611 := bstep (se 1 (by rfl) ⟨1602458, by rfl⟩ : syracuseStep 2136611 = 3204917) B3204917
theorem B5408309 : Blo 2135435 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B3605539 : Blo 2135435 3605539 := bstep (se 1 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 3605539 = 5408309) B5408309
theorem B4807385 : Blo 2135435 4807385 := bstep (se 2 (by rfl) ⟨1802769, by rfl⟩ : syracuseStep 4807385 = 3605539) B3605539
theorem B3204923 : Blo 2135435 3204923 := bstep (se 1 (by rfl) ⟨2403692, by rfl⟩ : syracuseStep 3204923 = 4807385) B4807385
theorem B2136615 : Blo 2135435 2136615 := bstep (se 1 (by rfl) ⟨1602461, by rfl⟩ : syracuseStep 2136615 = 3204923) B3204923
theorem B2403697 : Blo 2135435 2403697 := bbase (se 2 (by rfl) ⟨901386, by rfl⟩ : syracuseStep 2403697 = 1802773) (by norm_num)
theorem B3204929 : Blo 2135435 3204929 := bstep (se 2 (by rfl) ⟨1201848, by rfl⟩ : syracuseStep 3204929 = 2403697) B2403697
theorem B2136619 : Blo 2135435 2136619 := bstep (se 1 (by rfl) ⟨1602464, by rfl⟩ : syracuseStep 2136619 = 3204929) B3204929
theorem B6938309 : Blo 2135435 6938309 := bbase (se 4 (by rfl) ⟨650466, by rfl⟩ : syracuseStep 6938309 = 1300933) (by norm_num)
theorem B18502157 : Blo 2135435 18502157 := bstep (se 3 (by rfl) ⟨3469154, by rfl⟩ : syracuseStep 18502157 = 6938309) B6938309
theorem B12334771 : Blo 2135435 12334771 := bstep (se 1 (by rfl) ⟨9251078, by rfl⟩ : syracuseStep 12334771 = 18502157) B18502157
theorem B16446361 : Blo 2135435 16446361 := bstep (se 2 (by rfl) ⟨6167385, by rfl⟩ : syracuseStep 16446361 = 12334771) B12334771
theorem B21928481 : Blo 2135435 21928481 := bstep (se 2 (by rfl) ⟨8223180, by rfl⟩ : syracuseStep 21928481 = 16446361) B16446361
theorem B14618987 : Blo 2135435 14618987 := bstep (se 1 (by rfl) ⟨10964240, by rfl⟩ : syracuseStep 14618987 = 21928481) B21928481
theorem B9745991 : Blo 2135435 9745991 := bstep (se 1 (by rfl) ⟨7309493, by rfl⟩ : syracuseStep 9745991 = 14618987) B14618987
theorem B6497327 : Blo 2135435 6497327 := bstep (se 1 (by rfl) ⟨4872995, by rfl⟩ : syracuseStep 6497327 = 9745991) B9745991
theorem B4331551 : Blo 2135435 4331551 := bstep (se 1 (by rfl) ⟨3248663, by rfl⟩ : syracuseStep 4331551 = 6497327) B6497327
theorem B5775401 : Blo 2135435 5775401 := bstep (se 2 (by rfl) ⟨2165775, by rfl⟩ : syracuseStep 5775401 = 4331551) B4331551
theorem B3850267 : Blo 2135435 3850267 := bstep (se 1 (by rfl) ⟨2887700, by rfl⟩ : syracuseStep 3850267 = 5775401) B5775401
theorem B5133689 : Blo 2135435 5133689 := bstep (se 2 (by rfl) ⟨1925133, by rfl⟩ : syracuseStep 5133689 = 3850267) B3850267
theorem B3422459 : Blo 2135435 3422459 := bstep (se 1 (by rfl) ⟨2566844, by rfl⟩ : syracuseStep 3422459 = 5133689) B5133689
theorem B9126557 : Blo 2135435 9126557 := bstep (se 3 (by rfl) ⟨1711229, by rfl⟩ : syracuseStep 9126557 = 3422459) B3422459
theorem B6084371 : Blo 2135435 6084371 := bstep (se 1 (by rfl) ⟨4563278, by rfl⟩ : syracuseStep 6084371 = 9126557) B9126557
theorem B4056247 : Blo 2135435 4056247 := bstep (se 1 (by rfl) ⟨3042185, by rfl⟩ : syracuseStep 4056247 = 6084371) B6084371
theorem B5408329 : Blo 2135435 5408329 := bstep (se 2 (by rfl) ⟨2028123, by rfl⟩ : syracuseStep 5408329 = 4056247) B4056247
theorem B7211105 : Blo 2135435 7211105 := bstep (se 2 (by rfl) ⟨2704164, by rfl⟩ : syracuseStep 7211105 = 5408329) B5408329
theorem B4807403 : Blo 2135435 4807403 := bstep (se 1 (by rfl) ⟨3605552, by rfl⟩ : syracuseStep 4807403 = 7211105) B7211105
theorem B3204935 : Blo 2135435 3204935 := bstep (se 1 (by rfl) ⟨2403701, by rfl⟩ : syracuseStep 3204935 = 4807403) B4807403
theorem B2136623 : Blo 2135435 2136623 := bstep (se 1 (by rfl) ⟨1602467, by rfl⟩ : syracuseStep 2136623 = 3204935) B3204935
theorem B3204941 : Blo 2135435 3204941 := bbase (se 3 (by rfl) ⟨600926, by rfl⟩ : syracuseStep 3204941 = 1201853) (by norm_num)
theorem B2136627 : Blo 2135435 2136627 := bstep (se 1 (by rfl) ⟨1602470, by rfl⟩ : syracuseStep 2136627 = 3204941) B3204941
theorem B4807421 : Blo 2135435 4807421 := bbase (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) (by norm_num)
theorem B3204947 : Blo 2135435 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B2136631 : Blo 2135435 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B3605573 : Blo 2135435 3605573 := bbase (se 4 (by rfl) ⟨338022, by rfl⟩ : syracuseStep 3605573 = 676045) (by norm_num)
theorem B2403715 : Blo 2135435 2403715 := bstep (se 1 (by rfl) ⟨1802786, by rfl⟩ : syracuseStep 2403715 = 3605573) B3605573
theorem B3204953 : Blo 2135435 3204953 := bstep (se 2 (by rfl) ⟨1201857, by rfl⟩ : syracuseStep 3204953 = 2403715) B2403715
theorem B2136635 : Blo 2135435 2136635 := bstep (se 1 (by rfl) ⟨1602476, by rfl⟩ : syracuseStep 2136635 = 3204953) B3204953
theorem B16225109 : Blo 2135435 16225109 := bbase (se 9 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 16225109 = 95069) (by norm_num)
theorem B10816739 : Blo 2135435 10816739 := bstep (se 1 (by rfl) ⟨8112554, by rfl⟩ : syracuseStep 10816739 = 16225109) B16225109
theorem B7211159 : Blo 2135435 7211159 := bstep (se 1 (by rfl) ⟨5408369, by rfl⟩ : syracuseStep 7211159 = 10816739) B10816739
theorem B4807439 : Blo 2135435 4807439 := bstep (se 1 (by rfl) ⟨3605579, by rfl⟩ : syracuseStep 4807439 = 7211159) B7211159
theorem B3204959 : Blo 2135435 3204959 := bstep (se 1 (by rfl) ⟨2403719, by rfl⟩ : syracuseStep 3204959 = 4807439) B4807439
theorem B2136639 : Blo 2135435 2136639 := bstep (se 1 (by rfl) ⟨1602479, by rfl⟩ : syracuseStep 2136639 = 3204959) B3204959
theorem B3204965 : Blo 2135435 3204965 := bbase (se 4 (by rfl) ⟨300465, by rfl⟩ : syracuseStep 3204965 = 600931) (by norm_num)
theorem B2136643 : Blo 2135435 2136643 := bstep (se 1 (by rfl) ⟨1602482, by rfl⟩ : syracuseStep 2136643 = 3204965) B3204965
theorem B4056293 : Blo 2135435 4056293 := bbase (se 4 (by rfl) ⟨380277, by rfl⟩ : syracuseStep 4056293 = 760555) (by norm_num)
theorem B2704195 : Blo 2135435 2704195 := bstep (se 1 (by rfl) ⟨2028146, by rfl⟩ : syracuseStep 2704195 = 4056293) B4056293
theorem B3605593 : Blo 2135435 3605593 := bstep (se 2 (by rfl) ⟨1352097, by rfl⟩ : syracuseStep 3605593 = 2704195) B2704195
theorem B4807457 : Blo 2135435 4807457 := bstep (se 2 (by rfl) ⟨1802796, by rfl⟩ : syracuseStep 4807457 = 3605593) B3605593
theorem B3204971 : Blo 2135435 3204971 := bstep (se 1 (by rfl) ⟨2403728, by rfl⟩ : syracuseStep 3204971 = 4807457) B4807457
theorem B2136647 : Blo 2135435 2136647 := bstep (se 1 (by rfl) ⟨1602485, by rfl⟩ : syracuseStep 2136647 = 3204971) B3204971
theorem B2403733 : Blo 2135435 2403733 := bbase (se 6 (by rfl) ⟨56337, by rfl⟩ : syracuseStep 2403733 = 112675) (by norm_num)
theorem B3204977 : Blo 2135435 3204977 := bstep (se 2 (by rfl) ⟨1201866, by rfl⟩ : syracuseStep 3204977 = 2403733) B2403733
theorem B2136651 : Blo 2135435 2136651 := bstep (se 1 (by rfl) ⟨1602488, by rfl⟩ : syracuseStep 2136651 = 3204977) B3204977
theorem B2704205 : Blo 2135435 2704205 := bbase (se 3 (by rfl) ⟨507038, by rfl⟩ : syracuseStep 2704205 = 1014077) (by norm_num)
theorem B7211213 : Blo 2135435 7211213 := bstep (se 3 (by rfl) ⟨1352102, by rfl⟩ : syracuseStep 7211213 = 2704205) B2704205
theorem B4807475 : Blo 2135435 4807475 := bstep (se 1 (by rfl) ⟨3605606, by rfl⟩ : syracuseStep 4807475 = 7211213) B7211213
theorem B3204983 : Blo 2135435 3204983 := bstep (se 1 (by rfl) ⟨2403737, by rfl⟩ : syracuseStep 3204983 = 4807475) B4807475
theorem B2136655 : Blo 2135435 2136655 := bstep (se 1 (by rfl) ⟨1602491, by rfl⟩ : syracuseStep 2136655 = 3204983) B3204983
theorem B3204989 : Blo 2135435 3204989 := bbase (se 3 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 3204989 = 1201871) (by norm_num)
theorem B2136659 : Blo 2135435 2136659 := bstep (se 1 (by rfl) ⟨1602494, by rfl⟩ : syracuseStep 2136659 = 3204989) B3204989
theorem B4807493 : Blo 2135435 4807493 := bbase (se 4 (by rfl) ⟨450702, by rfl⟩ : syracuseStep 4807493 = 901405) (by norm_num)
theorem B3204995 : Blo 2135435 3204995 := bstep (se 1 (by rfl) ⟨2403746, by rfl⟩ : syracuseStep 3204995 = 4807493) B4807493
theorem B2136663 : Blo 2135435 2136663 := bstep (se 1 (by rfl) ⟨1602497, by rfl⟩ : syracuseStep 2136663 = 3204995) B3204995
theorem B4563373 : Blo 2135435 4563373 := bbase (se 3 (by rfl) ⟨855632, by rfl⟩ : syracuseStep 4563373 = 1711265) (by norm_num)
theorem B6084497 : Blo 2135435 6084497 := bstep (se 2 (by rfl) ⟨2281686, by rfl⟩ : syracuseStep 6084497 = 4563373) B4563373
theorem B4056331 : Blo 2135435 4056331 := bstep (se 1 (by rfl) ⟨3042248, by rfl⟩ : syracuseStep 4056331 = 6084497) B6084497
theorem B5408441 : Blo 2135435 5408441 := bstep (se 2 (by rfl) ⟨2028165, by rfl⟩ : syracuseStep 5408441 = 4056331) B4056331
theorem B3605627 : Blo 2135435 3605627 := bstep (se 1 (by rfl) ⟨2704220, by rfl⟩ : syracuseStep 3605627 = 5408441) B5408441
theorem B2403751 : Blo 2135435 2403751 := bstep (se 1 (by rfl) ⟨1802813, by rfl⟩ : syracuseStep 2403751 = 3605627) B3605627
theorem B3205001 : Blo 2135435 3205001 := bstep (se 2 (by rfl) ⟨1201875, by rfl⟩ : syracuseStep 3205001 = 2403751) B2403751
theorem B2136667 : Blo 2135435 2136667 := bstep (se 1 (by rfl) ⟨1602500, by rfl⟩ : syracuseStep 2136667 = 3205001) B3205001
theorem B10816901 : Blo 2135435 10816901 := bbase (se 4 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 10816901 = 2028169) (by norm_num)
theorem B7211267 : Blo 2135435 7211267 := bstep (se 1 (by rfl) ⟨5408450, by rfl⟩ : syracuseStep 7211267 = 10816901) B10816901
theorem B4807511 : Blo 2135435 4807511 := bstep (se 1 (by rfl) ⟨3605633, by rfl⟩ : syracuseStep 4807511 = 7211267) B7211267
theorem B3205007 : Blo 2135435 3205007 := bstep (se 1 (by rfl) ⟨2403755, by rfl⟩ : syracuseStep 3205007 = 4807511) B4807511
theorem B2136671 : Blo 2135435 2136671 := bstep (se 1 (by rfl) ⟨1602503, by rfl⟩ : syracuseStep 2136671 = 3205007) B3205007
theorem B3205013 : Blo 2135435 3205013 := bbase (se 6 (by rfl) ⟨75117, by rfl⟩ : syracuseStep 3205013 = 150235) (by norm_num)
theorem B2136675 : Blo 2135435 2136675 := bstep (se 1 (by rfl) ⟨1602506, by rfl⟩ : syracuseStep 2136675 = 3205013) B3205013
theorem B3422549 : Blo 2135435 3422549 := bbase (se 10 (by rfl) ⟨5013, by rfl⟩ : syracuseStep 3422549 = 10027) (by norm_num)
theorem B2281699 : Blo 2135435 2281699 := bstep (se 1 (by rfl) ⟨1711274, by rfl⟩ : syracuseStep 2281699 = 3422549) B3422549
theorem B12169061 : Blo 2135435 12169061 := bstep (se 4 (by rfl) ⟨1140849, by rfl⟩ : syracuseStep 12169061 = 2281699) B2281699
theorem B8112707 : Blo 2135435 8112707 := bstep (se 1 (by rfl) ⟨6084530, by rfl⟩ : syracuseStep 8112707 = 12169061) B12169061
theorem B5408471 : Blo 2135435 5408471 := bstep (se 1 (by rfl) ⟨4056353, by rfl⟩ : syracuseStep 5408471 = 8112707) B8112707
theorem B3605647 : Blo 2135435 3605647 := bstep (se 1 (by rfl) ⟨2704235, by rfl⟩ : syracuseStep 3605647 = 5408471) B5408471
theorem B4807529 : Blo 2135435 4807529 := bstep (se 2 (by rfl) ⟨1802823, by rfl⟩ : syracuseStep 4807529 = 3605647) B3605647
theorem B3205019 : Blo 2135435 3205019 := bstep (se 1 (by rfl) ⟨2403764, by rfl⟩ : syracuseStep 3205019 = 4807529) B4807529
theorem B2136679 : Blo 2135435 2136679 := bstep (se 1 (by rfl) ⟨1602509, by rfl⟩ : syracuseStep 2136679 = 3205019) B3205019
theorem B2403769 : Blo 2135435 2403769 := bbase (se 2 (by rfl) ⟨901413, by rfl⟩ : syracuseStep 2403769 = 1802827) (by norm_num)
theorem B3205025 : Blo 2135435 3205025 := bstep (se 2 (by rfl) ⟨1201884, by rfl⟩ : syracuseStep 3205025 = 2403769) B2403769
theorem B2136683 : Blo 2135435 2136683 := bstep (se 1 (by rfl) ⟨1602512, by rfl⟩ : syracuseStep 2136683 = 3205025) B3205025
theorem B10267685 : Blo 2135435 10267685 := bbase (se 4 (by rfl) ⟨962595, by rfl⟩ : syracuseStep 10267685 = 1925191) (by norm_num)
theorem B6845123 : Blo 2135435 6845123 := bstep (se 1 (by rfl) ⟨5133842, by rfl⟩ : syracuseStep 6845123 = 10267685) B10267685
theorem B4563415 : Blo 2135435 4563415 := bstep (se 1 (by rfl) ⟨3422561, by rfl⟩ : syracuseStep 4563415 = 6845123) B6845123
theorem B6084553 : Blo 2135435 6084553 := bstep (se 2 (by rfl) ⟨2281707, by rfl⟩ : syracuseStep 6084553 = 4563415) B4563415
theorem B8112737 : Blo 2135435 8112737 := bstep (se 2 (by rfl) ⟨3042276, by rfl⟩ : syracuseStep 8112737 = 6084553) B6084553
theorem B5408491 : Blo 2135435 5408491 := bstep (se 1 (by rfl) ⟨4056368, by rfl⟩ : syracuseStep 5408491 = 8112737) B8112737
theorem B7211321 : Blo 2135435 7211321 := bstep (se 2 (by rfl) ⟨2704245, by rfl⟩ : syracuseStep 7211321 = 5408491) B5408491
theorem B4807547 : Blo 2135435 4807547 := bstep (se 1 (by rfl) ⟨3605660, by rfl⟩ : syracuseStep 4807547 = 7211321) B7211321
theorem B3205031 : Blo 2135435 3205031 := bstep (se 1 (by rfl) ⟨2403773, by rfl⟩ : syracuseStep 3205031 = 4807547) B4807547
theorem B2136687 : Blo 2135435 2136687 := bstep (se 1 (by rfl) ⟨1602515, by rfl⟩ : syracuseStep 2136687 = 3205031) B3205031
theorem B3205037 : Blo 2135435 3205037 := bbase (se 3 (by rfl) ⟨600944, by rfl⟩ : syracuseStep 3205037 = 1201889) (by norm_num)
theorem B2136691 : Blo 2135435 2136691 := bstep (se 1 (by rfl) ⟨1602518, by rfl⟩ : syracuseStep 2136691 = 3205037) B3205037
theorem B4807565 : Blo 2135435 4807565 := bbase (se 3 (by rfl) ⟨901418, by rfl⟩ : syracuseStep 4807565 = 1802837) (by norm_num)
theorem B3205043 : Blo 2135435 3205043 := bstep (se 1 (by rfl) ⟨2403782, by rfl⟩ : syracuseStep 3205043 = 4807565) B4807565
theorem B2136695 : Blo 2135435 2136695 := bstep (se 1 (by rfl) ⟨1602521, by rfl⟩ : syracuseStep 2136695 = 3205043) B3205043
theorem B2704261 : Blo 2135435 2704261 := bbase (se 4 (by rfl) ⟨253524, by rfl⟩ : syracuseStep 2704261 = 507049) (by norm_num)
theorem B3605681 : Blo 2135435 3605681 := bstep (se 2 (by rfl) ⟨1352130, by rfl⟩ : syracuseStep 3605681 = 2704261) B2704261
theorem B2403787 : Blo 2135435 2403787 := bstep (se 1 (by rfl) ⟨1802840, by rfl⟩ : syracuseStep 2403787 = 3605681) B3605681
theorem B3205049 : Blo 2135435 3205049 := bstep (se 2 (by rfl) ⟨1201893, by rfl⟩ : syracuseStep 3205049 = 2403787) B2403787
theorem B2136699 : Blo 2135435 2136699 := bstep (se 1 (by rfl) ⟨1602524, by rfl⟩ : syracuseStep 2136699 = 3205049) B3205049
theorem B27380693 : Blo 2135435 27380693 := bbase (se 7 (by rfl) ⟨320867, by rfl⟩ : syracuseStep 27380693 = 641735) (by norm_num)
theorem B18253795 : Blo 2135435 18253795 := bstep (se 1 (by rfl) ⟨13690346, by rfl⟩ : syracuseStep 18253795 = 27380693) B27380693
theorem B24338393 : Blo 2135435 24338393 := bstep (se 2 (by rfl) ⟨9126897, by rfl⟩ : syracuseStep 24338393 = 18253795) B18253795
theorem B16225595 : Blo 2135435 16225595 := bstep (se 1 (by rfl) ⟨12169196, by rfl⟩ : syracuseStep 16225595 = 24338393) B24338393
theorem B10817063 : Blo 2135435 10817063 := bstep (se 1 (by rfl) ⟨8112797, by rfl⟩ : syracuseStep 10817063 = 16225595) B16225595
theorem B7211375 : Blo 2135435 7211375 := bstep (se 1 (by rfl) ⟨5408531, by rfl⟩ : syracuseStep 7211375 = 10817063) B10817063
theorem B4807583 : Blo 2135435 4807583 := bstep (se 1 (by rfl) ⟨3605687, by rfl⟩ : syracuseStep 4807583 = 7211375) B7211375
theorem B3205055 : Blo 2135435 3205055 := bstep (se 1 (by rfl) ⟨2403791, by rfl⟩ : syracuseStep 3205055 = 4807583) B4807583
theorem B2136703 : Blo 2135435 2136703 := bstep (se 1 (by rfl) ⟨1602527, by rfl⟩ : syracuseStep 2136703 = 3205055) B3205055
theorem B3205061 : Blo 2135435 3205061 := bbase (se 4 (by rfl) ⟨300474, by rfl⟩ : syracuseStep 3205061 = 600949) (by norm_num)
theorem B2136707 : Blo 2135435 2136707 := bstep (se 1 (by rfl) ⟨1602530, by rfl⟩ : syracuseStep 2136707 = 3205061) B3205061
theorem B3605701 : Blo 2135435 3605701 := bbase (se 4 (by rfl) ⟨338034, by rfl⟩ : syracuseStep 3605701 = 676069) (by norm_num)
theorem B4807601 : Blo 2135435 4807601 := bstep (se 2 (by rfl) ⟨1802850, by rfl⟩ : syracuseStep 4807601 = 3605701) B3605701
theorem B3205067 : Blo 2135435 3205067 := bstep (se 1 (by rfl) ⟨2403800, by rfl⟩ : syracuseStep 3205067 = 4807601) B4807601
theorem B2136711 : Blo 2135435 2136711 := bstep (se 1 (by rfl) ⟨1602533, by rfl⟩ : syracuseStep 2136711 = 3205067) B3205067
theorem B2403805 : Blo 2135435 2403805 := bbase (se 3 (by rfl) ⟨450713, by rfl⟩ : syracuseStep 2403805 = 901427) (by norm_num)
theorem B3205073 : Blo 2135435 3205073 := bstep (se 2 (by rfl) ⟨1201902, by rfl⟩ : syracuseStep 3205073 = 2403805) B2403805
theorem B2136715 : Blo 2135435 2136715 := bstep (se 1 (by rfl) ⟨1602536, by rfl⟩ : syracuseStep 2136715 = 3205073) B3205073
theorem B7211429 : Blo 2135435 7211429 := bbase (se 4 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 7211429 = 1352143) (by norm_num)
theorem B4807619 : Blo 2135435 4807619 := bstep (se 1 (by rfl) ⟨3605714, by rfl⟩ : syracuseStep 4807619 = 7211429) B7211429
theorem B3205079 : Blo 2135435 3205079 := bstep (se 1 (by rfl) ⟨2403809, by rfl⟩ : syracuseStep 3205079 = 4807619) B4807619
theorem B2136719 : Blo 2135435 2136719 := bstep (se 1 (by rfl) ⟨1602539, by rfl⟩ : syracuseStep 2136719 = 3205079) B3205079
theorem B3205085 : Blo 2135435 3205085 := bbase (se 3 (by rfl) ⟨600953, by rfl⟩ : syracuseStep 3205085 = 1201907) (by norm_num)
theorem B2136723 : Blo 2135435 2136723 := bstep (se 1 (by rfl) ⟨1602542, by rfl⟩ : syracuseStep 2136723 = 3205085) B3205085
theorem B4807637 : Blo 2135435 4807637 := bbase (se 7 (by rfl) ⟨56339, by rfl⟩ : syracuseStep 4807637 = 112679) (by norm_num)
theorem B3205091 : Blo 2135435 3205091 := bstep (se 1 (by rfl) ⟨2403818, by rfl⟩ : syracuseStep 3205091 = 4807637) B4807637
theorem B2136727 : Blo 2135435 2136727 := bstep (se 1 (by rfl) ⟨1602545, by rfl⟩ : syracuseStep 2136727 = 3205091) B3205091
theorem B5482397 : Blo 2135435 5482397 := bbase (se 3 (by rfl) ⟨1027949, by rfl⟩ : syracuseStep 5482397 = 2055899) (by norm_num)
theorem B3654931 : Blo 2135435 3654931 := bstep (se 1 (by rfl) ⟨2741198, by rfl⟩ : syracuseStep 3654931 = 5482397) B5482397
theorem B4873241 : Blo 2135435 4873241 := bstep (se 2 (by rfl) ⟨1827465, by rfl⟩ : syracuseStep 4873241 = 3654931) B3654931
theorem B12995309 : Blo 2135435 12995309 := bstep (se 3 (by rfl) ⟨2436620, by rfl⟩ : syracuseStep 12995309 = 4873241) B4873241
theorem B8663539 : Blo 2135435 8663539 := bstep (se 1 (by rfl) ⟨6497654, by rfl⟩ : syracuseStep 8663539 = 12995309) B12995309
theorem B11551385 : Blo 2135435 11551385 := bstep (se 2 (by rfl) ⟨4331769, by rfl⟩ : syracuseStep 11551385 = 8663539) B8663539
theorem B7700923 : Blo 2135435 7700923 := bstep (se 1 (by rfl) ⟨5775692, by rfl⟩ : syracuseStep 7700923 = 11551385) B11551385
theorem B10267897 : Blo 2135435 10267897 := bstep (se 2 (by rfl) ⟨3850461, by rfl⟩ : syracuseStep 10267897 = 7700923) B7700923
theorem B13690529 : Blo 2135435 13690529 := bstep (se 2 (by rfl) ⟨5133948, by rfl⟩ : syracuseStep 13690529 = 10267897) B10267897
theorem B9127019 : Blo 2135435 9127019 := bstep (se 1 (by rfl) ⟨6845264, by rfl⟩ : syracuseStep 9127019 = 13690529) B13690529
theorem B6084679 : Blo 2135435 6084679 := bstep (se 1 (by rfl) ⟨4563509, by rfl⟩ : syracuseStep 6084679 = 9127019) B9127019
theorem B8112905 : Blo 2135435 8112905 := bstep (se 2 (by rfl) ⟨3042339, by rfl⟩ : syracuseStep 8112905 = 6084679) B6084679
theorem B5408603 : Blo 2135435 5408603 := bstep (se 1 (by rfl) ⟨4056452, by rfl⟩ : syracuseStep 5408603 = 8112905) B8112905
theorem B3605735 : Blo 2135435 3605735 := bstep (se 1 (by rfl) ⟨2704301, by rfl⟩ : syracuseStep 3605735 = 5408603) B5408603
theorem B2403823 : Blo 2135435 2403823 := bstep (se 1 (by rfl) ⟨1802867, by rfl⟩ : syracuseStep 2403823 = 3605735) B3605735
theorem B3205097 : Blo 2135435 3205097 := bstep (se 2 (by rfl) ⟨1201911, by rfl⟩ : syracuseStep 3205097 = 2403823) B2403823
theorem B2136731 : Blo 2135435 2136731 := bstep (se 1 (by rfl) ⟨1602548, by rfl⟩ : syracuseStep 2136731 = 3205097) B3205097
theorem B18254069 : Blo 2135435 18254069 := bbase (se 5 (by rfl) ⟨855659, by rfl⟩ : syracuseStep 18254069 = 1711319) (by norm_num)
theorem B12169379 : Blo 2135435 12169379 := bstep (se 1 (by rfl) ⟨9127034, by rfl⟩ : syracuseStep 12169379 = 18254069) B18254069
theorem B8112919 : Blo 2135435 8112919 := bstep (se 1 (by rfl) ⟨6084689, by rfl⟩ : syracuseStep 8112919 = 12169379) B12169379
theorem B10817225 : Blo 2135435 10817225 := bstep (se 2 (by rfl) ⟨4056459, by rfl⟩ : syracuseStep 10817225 = 8112919) B8112919
theorem B7211483 : Blo 2135435 7211483 := bstep (se 1 (by rfl) ⟨5408612, by rfl⟩ : syracuseStep 7211483 = 10817225) B10817225
theorem B4807655 : Blo 2135435 4807655 := bstep (se 1 (by rfl) ⟨3605741, by rfl⟩ : syracuseStep 4807655 = 7211483) B7211483
theorem B3205103 : Blo 2135435 3205103 := bstep (se 1 (by rfl) ⟨2403827, by rfl⟩ : syracuseStep 3205103 = 4807655) B4807655
theorem B2136735 : Blo 2135435 2136735 := bstep (se 1 (by rfl) ⟨1602551, by rfl⟩ : syracuseStep 2136735 = 3205103) B3205103
theorem B3205109 : Blo 2135435 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B2136739 : Blo 2135435 2136739 := bstep (se 1 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 2136739 = 3205109) B3205109
theorem B2165897 : Blo 2135435 2165897 := bbase (se 2 (by rfl) ⟨812211, by rfl⟩ : syracuseStep 2165897 = 1624423) (by norm_num)
theorem B5775725 : Blo 2135435 5775725 := bstep (se 3 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 5775725 = 2165897) B2165897
theorem B15401933 : Blo 2135435 15401933 := bstep (se 3 (by rfl) ⟨2887862, by rfl⟩ : syracuseStep 15401933 = 5775725) B5775725
theorem B10267955 : Blo 2135435 10267955 := bstep (se 1 (by rfl) ⟨7700966, by rfl⟩ : syracuseStep 10267955 = 15401933) B15401933
theorem B6845303 : Blo 2135435 6845303 := bstep (se 1 (by rfl) ⟨5133977, by rfl⟩ : syracuseStep 6845303 = 10267955) B10267955
theorem B4563535 : Blo 2135435 4563535 := bstep (se 1 (by rfl) ⟨3422651, by rfl⟩ : syracuseStep 4563535 = 6845303) B6845303
theorem B6084713 : Blo 2135435 6084713 := bstep (se 2 (by rfl) ⟨2281767, by rfl⟩ : syracuseStep 6084713 = 4563535) B4563535
theorem B4056475 : Blo 2135435 4056475 := bstep (se 1 (by rfl) ⟨3042356, by rfl⟩ : syracuseStep 4056475 = 6084713) B6084713
theorem B5408633 : Blo 2135435 5408633 := bstep (se 2 (by rfl) ⟨2028237, by rfl⟩ : syracuseStep 5408633 = 4056475) B4056475
theorem B3605755 : Blo 2135435 3605755 := bstep (se 1 (by rfl) ⟨2704316, by rfl⟩ : syracuseStep 3605755 = 5408633) B5408633
theorem B4807673 : Blo 2135435 4807673 := bstep (se 2 (by rfl) ⟨1802877, by rfl⟩ : syracuseStep 4807673 = 3605755) B3605755
theorem B3205115 : Blo 2135435 3205115 := bstep (se 1 (by rfl) ⟨2403836, by rfl⟩ : syracuseStep 3205115 = 4807673) B4807673
theorem B2136743 : Blo 2135435 2136743 := bstep (se 1 (by rfl) ⟨1602557, by rfl⟩ : syracuseStep 2136743 = 3205115) B3205115
theorem B2403841 : Blo 2135435 2403841 := bbase (se 2 (by rfl) ⟨901440, by rfl⟩ : syracuseStep 2403841 = 1802881) (by norm_num)
theorem B3205121 : Blo 2135435 3205121 := bstep (se 2 (by rfl) ⟨1201920, by rfl⟩ : syracuseStep 3205121 = 2403841) B2403841
theorem B2136747 : Blo 2135435 2136747 := bstep (se 1 (by rfl) ⟨1602560, by rfl⟩ : syracuseStep 2136747 = 3205121) B3205121
theorem B5408653 : Blo 2135435 5408653 := bbase (se 3 (by rfl) ⟨1014122, by rfl⟩ : syracuseStep 5408653 = 2028245) (by norm_num)
theorem B7211537 : Blo 2135435 7211537 := bstep (se 2 (by rfl) ⟨2704326, by rfl⟩ : syracuseStep 7211537 = 5408653) B5408653
theorem B4807691 : Blo 2135435 4807691 := bstep (se 1 (by rfl) ⟨3605768, by rfl⟩ : syracuseStep 4807691 = 7211537) B7211537
theorem B3205127 : Blo 2135435 3205127 := bstep (se 1 (by rfl) ⟨2403845, by rfl⟩ : syracuseStep 3205127 = 4807691) B4807691
theorem B2136751 : Blo 2135435 2136751 := bstep (se 1 (by rfl) ⟨1602563, by rfl⟩ : syracuseStep 2136751 = 3205127) B3205127
theorem B3205133 : Blo 2135435 3205133 := bbase (se 3 (by rfl) ⟨600962, by rfl⟩ : syracuseStep 3205133 = 1201925) (by norm_num)
theorem B2136755 : Blo 2135435 2136755 := bstep (se 1 (by rfl) ⟨1602566, by rfl⟩ : syracuseStep 2136755 = 3205133) B3205133
theorem B4807709 : Blo 2135435 4807709 := bbase (se 3 (by rfl) ⟨901445, by rfl⟩ : syracuseStep 4807709 = 1802891) (by norm_num)
theorem B3205139 : Blo 2135435 3205139 := bstep (se 1 (by rfl) ⟨2403854, by rfl⟩ : syracuseStep 3205139 = 4807709) B4807709
theorem B2136759 : Blo 2135435 2136759 := bstep (se 1 (by rfl) ⟨1602569, by rfl⟩ : syracuseStep 2136759 = 3205139) B3205139
theorem B3605789 : Blo 2135435 3605789 := bbase (se 3 (by rfl) ⟨676085, by rfl⟩ : syracuseStep 3605789 = 1352171) (by norm_num)
theorem B2403859 : Blo 2135435 2403859 := bstep (se 1 (by rfl) ⟨1802894, by rfl⟩ : syracuseStep 2403859 = 3605789) B3605789
theorem B3205145 : Blo 2135435 3205145 := bstep (se 2 (by rfl) ⟨1201929, by rfl⟩ : syracuseStep 3205145 = 2403859) B2403859
theorem B2136763 : Blo 2135435 2136763 := bstep (se 1 (by rfl) ⟨1602572, by rfl⟩ : syracuseStep 2136763 = 3205145) B3205145
theorem B2567017 : Blo 2135435 2567017 := bbase (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) (by norm_num)
theorem B13690757 : Blo 2135435 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B9127171 : Blo 2135435 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B12169561 : Blo 2135435 12169561 := bstep (se 2 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 12169561 = 9127171) B9127171
theorem B16226081 : Blo 2135435 16226081 := bstep (se 2 (by rfl) ⟨6084780, by rfl⟩ : syracuseStep 16226081 = 12169561) B12169561
theorem B10817387 : Blo 2135435 10817387 := bstep (se 1 (by rfl) ⟨8113040, by rfl⟩ : syracuseStep 10817387 = 16226081) B16226081
theorem B7211591 : Blo 2135435 7211591 := bstep (se 1 (by rfl) ⟨5408693, by rfl⟩ : syracuseStep 7211591 = 10817387) B10817387
theorem B4807727 : Blo 2135435 4807727 := bstep (se 1 (by rfl) ⟨3605795, by rfl⟩ : syracuseStep 4807727 = 7211591) B7211591
theorem B3205151 : Blo 2135435 3205151 := bstep (se 1 (by rfl) ⟨2403863, by rfl⟩ : syracuseStep 3205151 = 4807727) B4807727
theorem B2136767 : Blo 2135435 2136767 := bstep (se 1 (by rfl) ⟨1602575, by rfl⟩ : syracuseStep 2136767 = 3205151) B3205151
theorem B3205157 : Blo 2135435 3205157 := bbase (se 4 (by rfl) ⟨300483, by rfl⟩ : syracuseStep 3205157 = 600967) (by norm_num)
theorem B2136771 : Blo 2135435 2136771 := bstep (se 1 (by rfl) ⟨1602578, by rfl⟩ : syracuseStep 2136771 = 3205157) B3205157
theorem B2704357 : Blo 2135435 2704357 := bbase (se 4 (by rfl) ⟨253533, by rfl⟩ : syracuseStep 2704357 = 507067) (by norm_num)
theorem B3605809 : Blo 2135435 3605809 := bstep (se 2 (by rfl) ⟨1352178, by rfl⟩ : syracuseStep 3605809 = 2704357) B2704357
theorem B4807745 : Blo 2135435 4807745 := bstep (se 2 (by rfl) ⟨1802904, by rfl⟩ : syracuseStep 4807745 = 3605809) B3605809
theorem B3205163 : Blo 2135435 3205163 := bstep (se 1 (by rfl) ⟨2403872, by rfl⟩ : syracuseStep 3205163 = 4807745) B4807745
theorem B2136775 : Blo 2135435 2136775 := bstep (se 1 (by rfl) ⟨1602581, by rfl⟩ : syracuseStep 2136775 = 3205163) B3205163
theorem B2403877 : Blo 2135435 2403877 := bbase (se 4 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 2403877 = 450727) (by norm_num)
theorem B3205169 : Blo 2135435 3205169 := bstep (se 2 (by rfl) ⟨1201938, by rfl⟩ : syracuseStep 3205169 = 2403877) B2403877
theorem B2136779 : Blo 2135435 2136779 := bstep (se 1 (by rfl) ⟨1602584, by rfl⟩ : syracuseStep 2136779 = 3205169) B3205169
theorem B6497813 : Blo 2135435 6497813 := bbase (se 6 (by rfl) ⟨152292, by rfl⟩ : syracuseStep 6497813 = 304585) (by norm_num)
theorem B4331875 : Blo 2135435 4331875 := bstep (se 1 (by rfl) ⟨3248906, by rfl⟩ : syracuseStep 4331875 = 6497813) B6497813
theorem B5775833 : Blo 2135435 5775833 := bstep (se 2 (by rfl) ⟨2165937, by rfl⟩ : syracuseStep 5775833 = 4331875) B4331875
theorem B15402221 : Blo 2135435 15402221 := bstep (se 3 (by rfl) ⟨2887916, by rfl⟩ : syracuseStep 15402221 = 5775833) B5775833
theorem B10268147 : Blo 2135435 10268147 := bstep (se 1 (by rfl) ⟨7701110, by rfl⟩ : syracuseStep 10268147 = 15402221) B15402221
theorem B6845431 : Blo 2135435 6845431 := bstep (se 1 (by rfl) ⟨5134073, by rfl⟩ : syracuseStep 6845431 = 10268147) B10268147
theorem B9127241 : Blo 2135435 9127241 := bstep (se 2 (by rfl) ⟨3422715, by rfl⟩ : syracuseStep 9127241 = 6845431) B6845431
theorem B6084827 : Blo 2135435 6084827 := bstep (se 1 (by rfl) ⟨4563620, by rfl⟩ : syracuseStep 6084827 = 9127241) B9127241
theorem B4056551 : Blo 2135435 4056551 := bstep (se 1 (by rfl) ⟨3042413, by rfl⟩ : syracuseStep 4056551 = 6084827) B6084827
theorem B2704367 : Blo 2135435 2704367 := bstep (se 1 (by rfl) ⟨2028275, by rfl⟩ : syracuseStep 2704367 = 4056551) B4056551
theorem B7211645 : Blo 2135435 7211645 := bstep (se 3 (by rfl) ⟨1352183, by rfl⟩ : syracuseStep 7211645 = 2704367) B2704367
theorem B4807763 : Blo 2135435 4807763 := bstep (se 1 (by rfl) ⟨3605822, by rfl⟩ : syracuseStep 4807763 = 7211645) B7211645
theorem B3205175 : Blo 2135435 3205175 := bstep (se 1 (by rfl) ⟨2403881, by rfl⟩ : syracuseStep 3205175 = 4807763) B4807763
theorem B2136783 : Blo 2135435 2136783 := bstep (se 1 (by rfl) ⟨1602587, by rfl⟩ : syracuseStep 2136783 = 3205175) B3205175
theorem B3205181 : Blo 2135435 3205181 := bbase (se 3 (by rfl) ⟨600971, by rfl⟩ : syracuseStep 3205181 = 1201943) (by norm_num)
theorem B2136787 : Blo 2135435 2136787 := bstep (se 1 (by rfl) ⟨1602590, by rfl⟩ : syracuseStep 2136787 = 3205181) B3205181
theorem B4807781 : Blo 2135435 4807781 := bbase (se 4 (by rfl) ⟨450729, by rfl⟩ : syracuseStep 4807781 = 901459) (by norm_num)
theorem B3205187 : Blo 2135435 3205187 := bstep (se 1 (by rfl) ⟨2403890, by rfl⟩ : syracuseStep 3205187 = 4807781) B4807781
theorem B2136791 : Blo 2135435 2136791 := bstep (se 1 (by rfl) ⟨1602593, by rfl⟩ : syracuseStep 2136791 = 3205187) B3205187
theorem B5408765 : Blo 2135435 5408765 := bbase (se 3 (by rfl) ⟨1014143, by rfl⟩ : syracuseStep 5408765 = 2028287) (by norm_num)
theorem B3605843 : Blo 2135435 3605843 := bstep (se 1 (by rfl) ⟨2704382, by rfl⟩ : syracuseStep 3605843 = 5408765) B5408765
theorem B2403895 : Blo 2135435 2403895 := bstep (se 1 (by rfl) ⟨1802921, by rfl⟩ : syracuseStep 2403895 = 3605843) B3605843
theorem B3205193 : Blo 2135435 3205193 := bstep (se 2 (by rfl) ⟨1201947, by rfl⟩ : syracuseStep 3205193 = 2403895) B2403895
theorem B2136795 : Blo 2135435 2136795 := bstep (se 1 (by rfl) ⟨1602596, by rfl⟩ : syracuseStep 2136795 = 3205193) B3205193
theorem B4056581 : Blo 2135435 4056581 := bbase (se 4 (by rfl) ⟨380304, by rfl⟩ : syracuseStep 4056581 = 760609) (by norm_num)
theorem B10817549 : Blo 2135435 10817549 := bstep (se 3 (by rfl) ⟨2028290, by rfl⟩ : syracuseStep 10817549 = 4056581) B4056581
theorem B7211699 : Blo 2135435 7211699 := bstep (se 1 (by rfl) ⟨5408774, by rfl⟩ : syracuseStep 7211699 = 10817549) B10817549
theorem B4807799 : Blo 2135435 4807799 := bstep (se 1 (by rfl) ⟨3605849, by rfl⟩ : syracuseStep 4807799 = 7211699) B7211699
theorem B3205199 : Blo 2135435 3205199 := bstep (se 1 (by rfl) ⟨2403899, by rfl⟩ : syracuseStep 3205199 = 4807799) B4807799
theorem B2136799 : Blo 2135435 2136799 := bstep (se 1 (by rfl) ⟨1602599, by rfl⟩ : syracuseStep 2136799 = 3205199) B3205199
theorem B3205205 : Blo 2135435 3205205 := bbase (se 8 (by rfl) ⟨18780, by rfl⟩ : syracuseStep 3205205 = 37561) (by norm_num)
theorem B2136803 : Blo 2135435 2136803 := bstep (se 1 (by rfl) ⟨1602602, by rfl⟩ : syracuseStep 2136803 = 3205205) B3205205
theorem B3655061 : Blo 2135435 3655061 := bbase (se 6 (by rfl) ⟨85665, by rfl⟩ : syracuseStep 3655061 = 171331) (by norm_num)
theorem B2436707 : Blo 2135435 2436707 := bstep (se 1 (by rfl) ⟨1827530, by rfl⟩ : syracuseStep 2436707 = 3655061) B3655061
theorem B6497885 : Blo 2135435 6497885 := bstep (se 3 (by rfl) ⟨1218353, by rfl⟩ : syracuseStep 6497885 = 2436707) B2436707
theorem B4331923 : Blo 2135435 4331923 := bstep (se 1 (by rfl) ⟨3248942, by rfl⟩ : syracuseStep 4331923 = 6497885) B6497885
theorem B23103589 : Blo 2135435 23103589 := bstep (se 4 (by rfl) ⟨2165961, by rfl⟩ : syracuseStep 23103589 = 4331923) B4331923
theorem B30804785 : Blo 2135435 30804785 := bstep (se 2 (by rfl) ⟨11551794, by rfl⟩ : syracuseStep 30804785 = 23103589) B23103589
theorem B20536523 : Blo 2135435 20536523 := bstep (se 1 (by rfl) ⟨15402392, by rfl⟩ : syracuseStep 20536523 = 30804785) B30804785
theorem B13691015 : Blo 2135435 13691015 := bstep (se 1 (by rfl) ⟨10268261, by rfl⟩ : syracuseStep 13691015 = 20536523) B20536523
theorem B9127343 : Blo 2135435 9127343 := bstep (se 1 (by rfl) ⟨6845507, by rfl⟩ : syracuseStep 9127343 = 13691015) B13691015
theorem B6084895 : Blo 2135435 6084895 := bstep (se 1 (by rfl) ⟨4563671, by rfl⟩ : syracuseStep 6084895 = 9127343) B9127343
theorem B8113193 : Blo 2135435 8113193 := bstep (se 2 (by rfl) ⟨3042447, by rfl⟩ : syracuseStep 8113193 = 6084895) B6084895
theorem B5408795 : Blo 2135435 5408795 := bstep (se 1 (by rfl) ⟨4056596, by rfl⟩ : syracuseStep 5408795 = 8113193) B8113193
theorem B3605863 : Blo 2135435 3605863 := bstep (se 1 (by rfl) ⟨2704397, by rfl⟩ : syracuseStep 3605863 = 5408795) B5408795
theorem B4807817 : Blo 2135435 4807817 := bstep (se 2 (by rfl) ⟨1802931, by rfl⟩ : syracuseStep 4807817 = 3605863) B3605863
theorem B3205211 : Blo 2135435 3205211 := bstep (se 1 (by rfl) ⟨2403908, by rfl⟩ : syracuseStep 3205211 = 4807817) B4807817
theorem B2136807 : Blo 2135435 2136807 := bstep (se 1 (by rfl) ⟨1602605, by rfl⟩ : syracuseStep 2136807 = 3205211) B3205211
theorem B2403913 : Blo 2135435 2403913 := bbase (se 2 (by rfl) ⟨901467, by rfl⟩ : syracuseStep 2403913 = 1802935) (by norm_num)
theorem B3205217 : Blo 2135435 3205217 := bstep (se 2 (by rfl) ⟨1201956, by rfl⟩ : syracuseStep 3205217 = 2403913) B2403913
theorem B2136811 : Blo 2135435 2136811 := bstep (se 1 (by rfl) ⟨1602608, by rfl⟩ : syracuseStep 2136811 = 3205217) B3205217
theorem B6497909 : Blo 2135435 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B4331939 : Blo 2135435 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B11551837 : Blo 2135435 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B15402449 : Blo 2135435 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B10268299 : Blo 2135435 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B13691065 : Blo 2135435 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B18254753 : Blo 2135435 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B12169835 : Blo 2135435 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B8113223 : Blo 2135435 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B5408815 : Blo 2135435 5408815 := bstep (se 1 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 5408815 = 8113223) B8113223
theorem B7211753 : Blo 2135435 7211753 := bstep (se 2 (by rfl) ⟨2704407, by rfl⟩ : syracuseStep 7211753 = 5408815) B5408815
theorem B4807835 : Blo 2135435 4807835 := bstep (se 1 (by rfl) ⟨3605876, by rfl⟩ : syracuseStep 4807835 = 7211753) B7211753
theorem B3205223 : Blo 2135435 3205223 := bstep (se 1 (by rfl) ⟨2403917, by rfl⟩ : syracuseStep 3205223 = 4807835) B4807835
theorem B2136815 : Blo 2135435 2136815 := bstep (se 1 (by rfl) ⟨1602611, by rfl⟩ : syracuseStep 2136815 = 3205223) B3205223
theorem B3205229 : Blo 2135435 3205229 := bbase (se 3 (by rfl) ⟨600980, by rfl⟩ : syracuseStep 3205229 = 1201961) (by norm_num)
theorem B2136819 : Blo 2135435 2136819 := bstep (se 1 (by rfl) ⟨1602614, by rfl⟩ : syracuseStep 2136819 = 3205229) B3205229
theorem B4807853 : Blo 2135435 4807853 := bbase (se 3 (by rfl) ⟨901472, by rfl⟩ : syracuseStep 4807853 = 1802945) (by norm_num)
theorem B3205235 : Blo 2135435 3205235 := bstep (se 1 (by rfl) ⟨2403926, by rfl⟩ : syracuseStep 3205235 = 4807853) B4807853
theorem B2136823 : Blo 2135435 2136823 := bstep (se 1 (by rfl) ⟨1602617, by rfl⟩ : syracuseStep 2136823 = 3205235) B3205235
theorem B6845573 : Blo 2135435 6845573 := bbase (se 4 (by rfl) ⟨641772, by rfl⟩ : syracuseStep 6845573 = 1283545) (by norm_num)
theorem B4563715 : Blo 2135435 4563715 := bstep (se 1 (by rfl) ⟨3422786, by rfl⟩ : syracuseStep 4563715 = 6845573) B6845573
theorem B6084953 : Blo 2135435 6084953 := bstep (se 2 (by rfl) ⟨2281857, by rfl⟩ : syracuseStep 6084953 = 4563715) B4563715
theorem B4056635 : Blo 2135435 4056635 := bstep (se 1 (by rfl) ⟨3042476, by rfl⟩ : syracuseStep 4056635 = 6084953) B6084953
theorem B2704423 : Blo 2135435 2704423 := bstep (se 1 (by rfl) ⟨2028317, by rfl⟩ : syracuseStep 2704423 = 4056635) B4056635
theorem B3605897 : Blo 2135435 3605897 := bstep (se 2 (by rfl) ⟨1352211, by rfl⟩ : syracuseStep 3605897 = 2704423) B2704423
theorem B2403931 : Blo 2135435 2403931 := bstep (se 1 (by rfl) ⟨1802948, by rfl⟩ : syracuseStep 2403931 = 3605897) B3605897
theorem B3205241 : Blo 2135435 3205241 := bstep (se 2 (by rfl) ⟨1201965, by rfl⟩ : syracuseStep 3205241 = 2403931) B2403931
theorem B2136827 : Blo 2135435 2136827 := bstep (se 1 (by rfl) ⟨1602620, by rfl⟩ : syracuseStep 2136827 = 3205241) B3205241
theorem B6497957 : Blo 2135435 6497957 := bbase (se 4 (by rfl) ⟨609183, by rfl⟩ : syracuseStep 6497957 = 1218367) (by norm_num)
theorem B4331971 : Blo 2135435 4331971 := bstep (se 1 (by rfl) ⟨3248978, by rfl⟩ : syracuseStep 4331971 = 6497957) B6497957
theorem B23103845 : Blo 2135435 23103845 := bstep (se 4 (by rfl) ⟨2165985, by rfl⟩ : syracuseStep 23103845 = 4331971) B4331971
theorem B15402563 : Blo 2135435 15402563 := bstep (se 1 (by rfl) ⟨11551922, by rfl⟩ : syracuseStep 15402563 = 23103845) B23103845
theorem B10268375 : Blo 2135435 10268375 := bstep (se 1 (by rfl) ⟨7701281, by rfl⟩ : syracuseStep 10268375 = 15402563) B15402563
theorem B27382333 : Blo 2135435 27382333 := bstep (se 3 (by rfl) ⟨5134187, by rfl⟩ : syracuseStep 27382333 = 10268375) B10268375
theorem B36509777 : Blo 2135435 36509777 := bstep (se 2 (by rfl) ⟨13691166, by rfl⟩ : syracuseStep 36509777 = 27382333) B27382333
theorem B24339851 : Blo 2135435 24339851 := bstep (se 1 (by rfl) ⟨18254888, by rfl⟩ : syracuseStep 24339851 = 36509777) B36509777
theorem B16226567 : Blo 2135435 16226567 := bstep (se 1 (by rfl) ⟨12169925, by rfl⟩ : syracuseStep 16226567 = 24339851) B24339851
theorem B10817711 : Blo 2135435 10817711 := bstep (se 1 (by rfl) ⟨8113283, by rfl⟩ : syracuseStep 10817711 = 16226567) B16226567
theorem B7211807 : Blo 2135435 7211807 := bstep (se 1 (by rfl) ⟨5408855, by rfl⟩ : syracuseStep 7211807 = 10817711) B10817711
theorem B4807871 : Blo 2135435 4807871 := bstep (se 1 (by rfl) ⟨3605903, by rfl⟩ : syracuseStep 4807871 = 7211807) B7211807
theorem B3205247 : Blo 2135435 3205247 := bstep (se 1 (by rfl) ⟨2403935, by rfl⟩ : syracuseStep 3205247 = 4807871) B4807871
theorem B2136831 : Blo 2135435 2136831 := bstep (se 1 (by rfl) ⟨1602623, by rfl⟩ : syracuseStep 2136831 = 3205247) B3205247
theorem B3205253 : Blo 2135435 3205253 := bbase (se 4 (by rfl) ⟨300492, by rfl⟩ : syracuseStep 3205253 = 600985) (by norm_num)
theorem B2136835 : Blo 2135435 2136835 := bstep (se 1 (by rfl) ⟨1602626, by rfl⟩ : syracuseStep 2136835 = 3205253) B3205253
theorem B3605917 : Blo 2135435 3605917 := bbase (se 3 (by rfl) ⟨676109, by rfl⟩ : syracuseStep 3605917 = 1352219) (by norm_num)
theorem B4807889 : Blo 2135435 4807889 := bstep (se 2 (by rfl) ⟨1802958, by rfl⟩ : syracuseStep 4807889 = 3605917) B3605917
theorem B3205259 : Blo 2135435 3205259 := bstep (se 1 (by rfl) ⟨2403944, by rfl⟩ : syracuseStep 3205259 = 4807889) B4807889
theorem B2136839 : Blo 2135435 2136839 := bstep (se 1 (by rfl) ⟨1602629, by rfl⟩ : syracuseStep 2136839 = 3205259) B3205259
theorem B2403949 : Blo 2135435 2403949 := bbase (se 3 (by rfl) ⟨450740, by rfl⟩ : syracuseStep 2403949 = 901481) (by norm_num)
theorem B3205265 : Blo 2135435 3205265 := bstep (se 2 (by rfl) ⟨1201974, by rfl⟩ : syracuseStep 3205265 = 2403949) B2403949
theorem B2136843 : Blo 2135435 2136843 := bstep (se 1 (by rfl) ⟨1602632, by rfl⟩ : syracuseStep 2136843 = 3205265) B3205265
theorem B7211861 : Blo 2135435 7211861 := bbase (se 9 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 7211861 = 42257) (by norm_num)
theorem B4807907 : Blo 2135435 4807907 := bstep (se 1 (by rfl) ⟨3605930, by rfl⟩ : syracuseStep 4807907 = 7211861) B7211861
theorem B3205271 : Blo 2135435 3205271 := bstep (se 1 (by rfl) ⟨2403953, by rfl⟩ : syracuseStep 3205271 = 4807907) B4807907
theorem B2136847 : Blo 2135435 2136847 := bstep (se 1 (by rfl) ⟨1602635, by rfl⟩ : syracuseStep 2136847 = 3205271) B3205271
theorem B3205277 : Blo 2135435 3205277 := bbase (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) (by norm_num)
theorem B2136851 : Blo 2135435 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B4807925 : Blo 2135435 4807925 := bbase (se 5 (by rfl) ⟨225371, by rfl⟩ : syracuseStep 4807925 = 450743) (by norm_num)
theorem B3205283 : Blo 2135435 3205283 := bstep (se 1 (by rfl) ⟨2403962, by rfl⟩ : syracuseStep 3205283 = 4807925) B4807925
theorem B2136855 : Blo 2135435 2136855 := bstep (se 1 (by rfl) ⟨1602641, by rfl⟩ : syracuseStep 2136855 = 3205283) B3205283
theorem B5275309 : Blo 2135435 5275309 := bbase (se 3 (by rfl) ⟨989120, by rfl⟩ : syracuseStep 5275309 = 1978241) (by norm_num)
theorem B7033745 : Blo 2135435 7033745 := bstep (se 2 (by rfl) ⟨2637654, by rfl⟩ : syracuseStep 7033745 = 5275309) B5275309
theorem B4689163 : Blo 2135435 4689163 := bstep (se 1 (by rfl) ⟨3516872, by rfl⟩ : syracuseStep 4689163 = 7033745) B7033745
theorem B25008869 : Blo 2135435 25008869 := bstep (se 4 (by rfl) ⟨2344581, by rfl⟩ : syracuseStep 25008869 = 4689163) B4689163
theorem B66690317 : Blo 2135435 66690317 := bstep (se 3 (by rfl) ⟨12504434, by rfl⟩ : syracuseStep 66690317 = 25008869) B25008869
theorem B44460211 : Blo 2135435 44460211 := bstep (se 1 (by rfl) ⟨33345158, by rfl⟩ : syracuseStep 44460211 = 66690317) B66690317
theorem B59280281 : Blo 2135435 59280281 := bstep (se 2 (by rfl) ⟨22230105, by rfl⟩ : syracuseStep 59280281 = 44460211) B44460211
theorem B39520187 : Blo 2135435 39520187 := bstep (se 1 (by rfl) ⟨29640140, by rfl⟩ : syracuseStep 39520187 = 59280281) B59280281
theorem B26346791 : Blo 2135435 26346791 := bstep (se 1 (by rfl) ⟨19760093, by rfl⟩ : syracuseStep 26346791 = 39520187) B39520187
theorem B17564527 : Blo 2135435 17564527 := bstep (se 1 (by rfl) ⟨13173395, by rfl⟩ : syracuseStep 17564527 = 26346791) B26346791
theorem B23419369 : Blo 2135435 23419369 := bstep (se 2 (by rfl) ⟨8782263, by rfl⟩ : syracuseStep 23419369 = 17564527) B17564527
theorem B31225825 : Blo 2135435 31225825 := bstep (se 2 (by rfl) ⟨11709684, by rfl⟩ : syracuseStep 31225825 = 23419369) B23419369
theorem B41634433 : Blo 2135435 41634433 := bstep (se 2 (by rfl) ⟨15612912, by rfl⟩ : syracuseStep 41634433 = 31225825) B31225825
theorem B55512577 : Blo 2135435 55512577 := bstep (se 2 (by rfl) ⟨20817216, by rfl⟩ : syracuseStep 55512577 = 41634433) B41634433
theorem B74016769 : Blo 2135435 74016769 := bstep (se 2 (by rfl) ⟨27756288, by rfl⟩ : syracuseStep 74016769 = 55512577) B55512577
theorem B98689025 : Blo 2135435 98689025 := bstep (se 2 (by rfl) ⟨37008384, by rfl⟩ : syracuseStep 98689025 = 74016769) B74016769
theorem B65792683 : Blo 2135435 65792683 := bstep (se 1 (by rfl) ⟨49344512, by rfl⟩ : syracuseStep 65792683 = 98689025) B98689025
theorem B87723577 : Blo 2135435 87723577 := bstep (se 2 (by rfl) ⟨32896341, by rfl⟩ : syracuseStep 87723577 = 65792683) B65792683
theorem B116964769 : Blo 2135435 116964769 := bstep (se 2 (by rfl) ⟨43861788, by rfl⟩ : syracuseStep 116964769 = 87723577) B87723577
theorem B155953025 : Blo 2135435 155953025 := bstep (se 2 (by rfl) ⟨58482384, by rfl⟩ : syracuseStep 155953025 = 116964769) B116964769
theorem B103968683 : Blo 2135435 103968683 := bstep (se 1 (by rfl) ⟨77976512, by rfl⟩ : syracuseStep 103968683 = 155953025) B155953025
theorem B69312455 : Blo 2135435 69312455 := bstep (se 1 (by rfl) ⟨51984341, by rfl⟩ : syracuseStep 69312455 = 103968683) B103968683
theorem B46208303 : Blo 2135435 46208303 := bstep (se 1 (by rfl) ⟨34656227, by rfl⟩ : syracuseStep 46208303 = 69312455) B69312455
theorem B30805535 : Blo 2135435 30805535 := bstep (se 1 (by rfl) ⟨23104151, by rfl⟩ : syracuseStep 30805535 = 46208303) B46208303
theorem B20537023 : Blo 2135435 20537023 := bstep (se 1 (by rfl) ⟨15402767, by rfl⟩ : syracuseStep 20537023 = 30805535) B30805535
theorem B27382697 : Blo 2135435 27382697 := bstep (se 2 (by rfl) ⟨10268511, by rfl⟩ : syracuseStep 27382697 = 20537023) B20537023
theorem B18255131 : Blo 2135435 18255131 := bstep (se 1 (by rfl) ⟨13691348, by rfl⟩ : syracuseStep 18255131 = 27382697) B27382697
theorem B12170087 : Blo 2135435 12170087 := bstep (se 1 (by rfl) ⟨9127565, by rfl⟩ : syracuseStep 12170087 = 18255131) B18255131
theorem B8113391 : Blo 2135435 8113391 := bstep (se 1 (by rfl) ⟨6085043, by rfl⟩ : syracuseStep 8113391 = 12170087) B12170087
theorem B5408927 : Blo 2135435 5408927 := bstep (se 1 (by rfl) ⟨4056695, by rfl⟩ : syracuseStep 5408927 = 8113391) B8113391
theorem B3605951 : Blo 2135435 3605951 := bstep (se 1 (by rfl) ⟨2704463, by rfl⟩ : syracuseStep 3605951 = 5408927) B5408927
theorem B2403967 : Blo 2135435 2403967 := bstep (se 1 (by rfl) ⟨1802975, by rfl⟩ : syracuseStep 2403967 = 3605951) B3605951
theorem B3205289 : Blo 2135435 3205289 := bstep (se 2 (by rfl) ⟨1201983, by rfl⟩ : syracuseStep 3205289 = 2403967) B2403967
theorem B2136859 : Blo 2135435 2136859 := bstep (se 1 (by rfl) ⟨1602644, by rfl⟩ : syracuseStep 2136859 = 3205289) B3205289
theorem B4332037 : Blo 2135435 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B5776049 : Blo 2135435 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B15402797 : Blo 2135435 15402797 := bstep (se 3 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 15402797 = 5776049) B5776049
theorem B10268531 : Blo 2135435 10268531 := bstep (se 1 (by rfl) ⟨7701398, by rfl⟩ : syracuseStep 10268531 = 15402797) B15402797
theorem B6845687 : Blo 2135435 6845687 := bstep (se 1 (by rfl) ⟨5134265, by rfl⟩ : syracuseStep 6845687 = 10268531) B10268531
theorem B4563791 : Blo 2135435 4563791 := bstep (se 1 (by rfl) ⟨3422843, by rfl⟩ : syracuseStep 4563791 = 6845687) B6845687
theorem B3042527 : Blo 2135435 3042527 := bstep (se 1 (by rfl) ⟨2281895, by rfl⟩ : syracuseStep 3042527 = 4563791) B4563791
theorem B8113405 : Blo 2135435 8113405 := bstep (se 3 (by rfl) ⟨1521263, by rfl⟩ : syracuseStep 8113405 = 3042527) B3042527
theorem B10817873 : Blo 2135435 10817873 := bstep (se 2 (by rfl) ⟨4056702, by rfl⟩ : syracuseStep 10817873 = 8113405) B8113405
theorem B7211915 : Blo 2135435 7211915 := bstep (se 1 (by rfl) ⟨5408936, by rfl⟩ : syracuseStep 7211915 = 10817873) B10817873
theorem B4807943 : Blo 2135435 4807943 := bstep (se 1 (by rfl) ⟨3605957, by rfl⟩ : syracuseStep 4807943 = 7211915) B7211915
theorem B3205295 : Blo 2135435 3205295 := bstep (se 1 (by rfl) ⟨2403971, by rfl⟩ : syracuseStep 3205295 = 4807943) B4807943
theorem B2136863 : Blo 2135435 2136863 := bstep (se 1 (by rfl) ⟨1602647, by rfl⟩ : syracuseStep 2136863 = 3205295) B3205295
theorem B3205301 : Blo 2135435 3205301 := bbase (se 5 (by rfl) ⟨150248, by rfl⟩ : syracuseStep 3205301 = 300497) (by norm_num)
theorem B2136867 : Blo 2135435 2136867 := bstep (se 1 (by rfl) ⟨1602650, by rfl⟩ : syracuseStep 2136867 = 3205301) B3205301
theorem B5408957 : Blo 2135435 5408957 := bbase (se 3 (by rfl) ⟨1014179, by rfl⟩ : syracuseStep 5408957 = 2028359) (by norm_num)
theorem B3605971 : Blo 2135435 3605971 := bstep (se 1 (by rfl) ⟨2704478, by rfl⟩ : syracuseStep 3605971 = 5408957) B5408957
theorem B4807961 : Blo 2135435 4807961 := bstep (se 2 (by rfl) ⟨1802985, by rfl⟩ : syracuseStep 4807961 = 3605971) B3605971
theorem B3205307 : Blo 2135435 3205307 := bstep (se 1 (by rfl) ⟨2403980, by rfl⟩ : syracuseStep 3205307 = 4807961) B4807961
theorem B2136871 : Blo 2135435 2136871 := bstep (se 1 (by rfl) ⟨1602653, by rfl⟩ : syracuseStep 2136871 = 3205307) B3205307
theorem B2403985 : Blo 2135435 2403985 := bbase (se 2 (by rfl) ⟨901494, by rfl⟩ : syracuseStep 2403985 = 1802989) (by norm_num)
theorem B3205313 : Blo 2135435 3205313 := bstep (se 2 (by rfl) ⟨1201992, by rfl⟩ : syracuseStep 3205313 = 2403985) B2403985
theorem B2136875 : Blo 2135435 2136875 := bstep (se 1 (by rfl) ⟨1602656, by rfl⟩ : syracuseStep 2136875 = 3205313) B3205313
theorem B4056733 : Blo 2135435 4056733 := bbase (se 3 (by rfl) ⟨760637, by rfl⟩ : syracuseStep 4056733 = 1521275) (by norm_num)
theorem B5408977 : Blo 2135435 5408977 := bstep (se 2 (by rfl) ⟨2028366, by rfl⟩ : syracuseStep 5408977 = 4056733) B4056733
theorem B7211969 : Blo 2135435 7211969 := bstep (se 2 (by rfl) ⟨2704488, by rfl⟩ : syracuseStep 7211969 = 5408977) B5408977
theorem B4807979 : Blo 2135435 4807979 := bstep (se 1 (by rfl) ⟨3605984, by rfl⟩ : syracuseStep 4807979 = 7211969) B7211969
theorem B3205319 : Blo 2135435 3205319 := bstep (se 1 (by rfl) ⟨2403989, by rfl⟩ : syracuseStep 3205319 = 4807979) B4807979
theorem B2136879 : Blo 2135435 2136879 := bstep (se 1 (by rfl) ⟨1602659, by rfl⟩ : syracuseStep 2136879 = 3205319) B3205319
theorem B3205325 : Blo 2135435 3205325 := bbase (se 3 (by rfl) ⟨600998, by rfl⟩ : syracuseStep 3205325 = 1201997) (by norm_num)
theorem B2136883 : Blo 2135435 2136883 := bstep (se 1 (by rfl) ⟨1602662, by rfl⟩ : syracuseStep 2136883 = 3205325) B3205325
theorem B4807997 : Blo 2135435 4807997 := bbase (se 3 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 4807997 = 1802999) (by norm_num)
theorem B3205331 : Blo 2135435 3205331 := bstep (se 1 (by rfl) ⟨2403998, by rfl⟩ : syracuseStep 3205331 = 4807997) B4807997
theorem B2136887 : Blo 2135435 2136887 := bstep (se 1 (by rfl) ⟨1602665, by rfl⟩ : syracuseStep 2136887 = 3205331) B3205331
theorem B3606005 : Blo 2135435 3606005 := bbase (se 5 (by rfl) ⟨169031, by rfl⟩ : syracuseStep 3606005 = 338063) (by norm_num)
theorem B2404003 : Blo 2135435 2404003 := bstep (se 1 (by rfl) ⟨1803002, by rfl⟩ : syracuseStep 2404003 = 3606005) B3606005
theorem B3205337 : Blo 2135435 3205337 := bstep (se 2 (by rfl) ⟨1202001, by rfl⟩ : syracuseStep 3205337 = 2404003) B2404003
theorem B2136891 : Blo 2135435 2136891 := bstep (se 1 (by rfl) ⟨1602668, by rfl⟩ : syracuseStep 2136891 = 3205337) B3205337
theorem B3850757 : Blo 2135435 3850757 := bbase (se 4 (by rfl) ⟨361008, by rfl⟩ : syracuseStep 3850757 = 722017) (by norm_num)
theorem B2567171 : Blo 2135435 2567171 := bstep (se 1 (by rfl) ⟨1925378, by rfl⟩ : syracuseStep 2567171 = 3850757) B3850757
theorem B6845789 : Blo 2135435 6845789 := bstep (se 3 (by rfl) ⟨1283585, by rfl⟩ : syracuseStep 6845789 = 2567171) B2567171
theorem B4563859 : Blo 2135435 4563859 := bstep (se 1 (by rfl) ⟨3422894, by rfl⟩ : syracuseStep 4563859 = 6845789) B6845789
theorem B6085145 : Blo 2135435 6085145 := bstep (se 2 (by rfl) ⟨2281929, by rfl⟩ : syracuseStep 6085145 = 4563859) B4563859
theorem B16227053 : Blo 2135435 16227053 := bstep (se 3 (by rfl) ⟨3042572, by rfl⟩ : syracuseStep 16227053 = 6085145) B6085145
theorem B10818035 : Blo 2135435 10818035 := bstep (se 1 (by rfl) ⟨8113526, by rfl⟩ : syracuseStep 10818035 = 16227053) B16227053
theorem B7212023 : Blo 2135435 7212023 := bstep (se 1 (by rfl) ⟨5409017, by rfl⟩ : syracuseStep 7212023 = 10818035) B10818035
theorem B4808015 : Blo 2135435 4808015 := bstep (se 1 (by rfl) ⟨3606011, by rfl⟩ : syracuseStep 4808015 = 7212023) B7212023
theorem B3205343 : Blo 2135435 3205343 := bstep (se 1 (by rfl) ⟨2404007, by rfl⟩ : syracuseStep 3205343 = 4808015) B4808015
theorem B2136895 : Blo 2135435 2136895 := bstep (se 1 (by rfl) ⟨1602671, by rfl⟩ : syracuseStep 2136895 = 3205343) B3205343
theorem B3205349 : Blo 2135435 3205349 := bbase (se 4 (by rfl) ⟨300501, by rfl⟩ : syracuseStep 3205349 = 601003) (by norm_num)
theorem B2136899 : Blo 2135435 2136899 := bstep (se 1 (by rfl) ⟨1602674, by rfl⟩ : syracuseStep 2136899 = 3205349) B3205349
theorem B4563877 : Blo 2135435 4563877 := bbase (se 4 (by rfl) ⟨427863, by rfl⟩ : syracuseStep 4563877 = 855727) (by norm_num)
theorem B6085169 : Blo 2135435 6085169 := bstep (se 2 (by rfl) ⟨2281938, by rfl⟩ : syracuseStep 6085169 = 4563877) B4563877
theorem B4056779 : Blo 2135435 4056779 := bstep (se 1 (by rfl) ⟨3042584, by rfl⟩ : syracuseStep 4056779 = 6085169) B6085169
theorem B2704519 : Blo 2135435 2704519 := bstep (se 1 (by rfl) ⟨2028389, by rfl⟩ : syracuseStep 2704519 = 4056779) B4056779
theorem B3606025 : Blo 2135435 3606025 := bstep (se 2 (by rfl) ⟨1352259, by rfl⟩ : syracuseStep 3606025 = 2704519) B2704519
theorem B4808033 : Blo 2135435 4808033 := bstep (se 2 (by rfl) ⟨1803012, by rfl⟩ : syracuseStep 4808033 = 3606025) B3606025
theorem B3205355 : Blo 2135435 3205355 := bstep (se 1 (by rfl) ⟨2404016, by rfl⟩ : syracuseStep 3205355 = 4808033) B4808033
theorem B2136903 : Blo 2135435 2136903 := bstep (se 1 (by rfl) ⟨1602677, by rfl⟩ : syracuseStep 2136903 = 3205355) B3205355
theorem B2404021 : Blo 2135435 2404021 := bbase (se 5 (by rfl) ⟨112688, by rfl⟩ : syracuseStep 2404021 = 225377) (by norm_num)
theorem B3205361 : Blo 2135435 3205361 := bstep (se 2 (by rfl) ⟨1202010, by rfl⟩ : syracuseStep 3205361 = 2404021) B2404021
theorem B2136907 : Blo 2135435 2136907 := bstep (se 1 (by rfl) ⟨1602680, by rfl⟩ : syracuseStep 2136907 = 3205361) B3205361
theorem B2704529 : Blo 2135435 2704529 := bbase (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) (by norm_num)
theorem B7212077 : Blo 2135435 7212077 := bstep (se 3 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 7212077 = 2704529) B2704529
theorem B4808051 : Blo 2135435 4808051 := bstep (se 1 (by rfl) ⟨3606038, by rfl⟩ : syracuseStep 4808051 = 7212077) B7212077
theorem B3205367 : Blo 2135435 3205367 := bstep (se 1 (by rfl) ⟨2404025, by rfl⟩ : syracuseStep 3205367 = 4808051) B4808051
theorem B2136911 : Blo 2135435 2136911 := bstep (se 1 (by rfl) ⟨1602683, by rfl⟩ : syracuseStep 2136911 = 3205367) B3205367
theorem B3205373 : Blo 2135435 3205373 := bbase (se 3 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 3205373 = 1202015) (by norm_num)
theorem B2136915 : Blo 2135435 2136915 := bstep (se 1 (by rfl) ⟨1602686, by rfl⟩ : syracuseStep 2136915 = 3205373) B3205373
theorem B4808069 : Blo 2135435 4808069 := bbase (se 4 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 4808069 = 901513) (by norm_num)
theorem B3205379 : Blo 2135435 3205379 := bstep (se 1 (by rfl) ⟨2404034, by rfl⟩ : syracuseStep 3205379 = 4808069) B4808069
theorem B2136919 : Blo 2135435 2136919 := bstep (se 1 (by rfl) ⟨1602689, by rfl⟩ : syracuseStep 2136919 = 3205379) B3205379
theorem B3042613 : Blo 2135435 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B4056817 : Blo 2135435 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B5409089 : Blo 2135435 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B3606059 : Blo 2135435 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B2404039 : Blo 2135435 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B3205385 : Blo 2135435 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B2136923 : Blo 2135435 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B10818197 : Blo 2135435 10818197 := bbase (se 6 (by rfl) ⟨253551, by rfl⟩ : syracuseStep 10818197 = 507103) (by norm_num)
theorem B7212131 : Blo 2135435 7212131 := bstep (se 1 (by rfl) ⟨5409098, by rfl⟩ : syracuseStep 7212131 = 10818197) B10818197
theorem B4808087 : Blo 2135435 4808087 := bstep (se 1 (by rfl) ⟨3606065, by rfl⟩ : syracuseStep 4808087 = 7212131) B7212131
theorem B3205391 : Blo 2135435 3205391 := bstep (se 1 (by rfl) ⟨2404043, by rfl⟩ : syracuseStep 3205391 = 4808087) B4808087
theorem B2136927 : Blo 2135435 2136927 := bstep (se 1 (by rfl) ⟨1602695, by rfl⟩ : syracuseStep 2136927 = 3205391) B3205391
theorem B3205397 : Blo 2135435 3205397 := bbase (se 6 (by rfl) ⟨75126, by rfl⟩ : syracuseStep 3205397 = 150253) (by norm_num)
theorem B2136931 : Blo 2135435 2136931 := bstep (se 1 (by rfl) ⟨1602698, by rfl⟩ : syracuseStep 2136931 = 3205397) B3205397
theorem B3850829 : Blo 2135435 3850829 := bbase (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) (by norm_num)
theorem B2567219 : Blo 2135435 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B27383669 : Blo 2135435 27383669 := bstep (se 5 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 27383669 = 2567219) B2567219
theorem B18255779 : Blo 2135435 18255779 := bstep (se 1 (by rfl) ⟨13691834, by rfl⟩ : syracuseStep 18255779 = 27383669) B27383669
theorem B12170519 : Blo 2135435 12170519 := bstep (se 1 (by rfl) ⟨9127889, by rfl⟩ : syracuseStep 12170519 = 18255779) B18255779
theorem B8113679 : Blo 2135435 8113679 := bstep (se 1 (by rfl) ⟨6085259, by rfl⟩ : syracuseStep 8113679 = 12170519) B12170519
theorem B5409119 : Blo 2135435 5409119 := bstep (se 1 (by rfl) ⟨4056839, by rfl⟩ : syracuseStep 5409119 = 8113679) B8113679
theorem B3606079 : Blo 2135435 3606079 := bstep (se 1 (by rfl) ⟨2704559, by rfl⟩ : syracuseStep 3606079 = 5409119) B5409119
theorem B4808105 : Blo 2135435 4808105 := bstep (se 2 (by rfl) ⟨1803039, by rfl⟩ : syracuseStep 4808105 = 3606079) B3606079
theorem B3205403 : Blo 2135435 3205403 := bstep (se 1 (by rfl) ⟨2404052, by rfl⟩ : syracuseStep 3205403 = 4808105) B4808105
theorem B2136935 : Blo 2135435 2136935 := bstep (se 1 (by rfl) ⟨1602701, by rfl⟩ : syracuseStep 2136935 = 3205403) B3205403
theorem B2404057 : Blo 2135435 2404057 := bbase (se 2 (by rfl) ⟨901521, by rfl⟩ : syracuseStep 2404057 = 1803043) (by norm_num)
theorem B3205409 : Blo 2135435 3205409 := bstep (se 2 (by rfl) ⟨1202028, by rfl⟩ : syracuseStep 3205409 = 2404057) B2404057
theorem B2136939 : Blo 2135435 2136939 := bstep (se 1 (by rfl) ⟨1602704, by rfl⟩ : syracuseStep 2136939 = 3205409) B3205409
theorem B2281981 : Blo 2135435 2281981 := bbase (se 3 (by rfl) ⟨427871, by rfl⟩ : syracuseStep 2281981 = 855743) (by norm_num)
theorem B3042641 : Blo 2135435 3042641 := bstep (se 2 (by rfl) ⟨1140990, by rfl⟩ : syracuseStep 3042641 = 2281981) B2281981
theorem B8113709 : Blo 2135435 8113709 := bstep (se 3 (by rfl) ⟨1521320, by rfl⟩ : syracuseStep 8113709 = 3042641) B3042641
theorem B5409139 : Blo 2135435 5409139 := bstep (se 1 (by rfl) ⟨4056854, by rfl⟩ : syracuseStep 5409139 = 8113709) B8113709
theorem B7212185 : Blo 2135435 7212185 := bstep (se 2 (by rfl) ⟨2704569, by rfl⟩ : syracuseStep 7212185 = 5409139) B5409139
theorem B4808123 : Blo 2135435 4808123 := bstep (se 1 (by rfl) ⟨3606092, by rfl⟩ : syracuseStep 4808123 = 7212185) B7212185
theorem B3205415 : Blo 2135435 3205415 := bstep (se 1 (by rfl) ⟨2404061, by rfl⟩ : syracuseStep 3205415 = 4808123) B4808123
theorem B2136943 : Blo 2135435 2136943 := bstep (se 1 (by rfl) ⟨1602707, by rfl⟩ : syracuseStep 2136943 = 3205415) B3205415
theorem B3205421 : Blo 2135435 3205421 := bbase (se 3 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 3205421 = 1202033) (by norm_num)
theorem B2136947 : Blo 2135435 2136947 := bstep (se 1 (by rfl) ⟨1602710, by rfl⟩ : syracuseStep 2136947 = 3205421) B3205421
theorem B4808141 : Blo 2135435 4808141 := bbase (se 3 (by rfl) ⟨901526, by rfl⟩ : syracuseStep 4808141 = 1803053) (by norm_num)
theorem B3205427 : Blo 2135435 3205427 := bstep (se 1 (by rfl) ⟨2404070, by rfl⟩ : syracuseStep 3205427 = 4808141) B4808141
theorem B2136951 : Blo 2135435 2136951 := bstep (se 1 (by rfl) ⟨1602713, by rfl⟩ : syracuseStep 2136951 = 3205427) B3205427
theorem B2704585 : Blo 2135435 2704585 := bbase (se 2 (by rfl) ⟨1014219, by rfl⟩ : syracuseStep 2704585 = 2028439) (by norm_num)
theorem B3606113 : Blo 2135435 3606113 := bstep (se 2 (by rfl) ⟨1352292, by rfl⟩ : syracuseStep 3606113 = 2704585) B2704585
theorem B2404075 : Blo 2135435 2404075 := bstep (se 1 (by rfl) ⟨1803056, by rfl⟩ : syracuseStep 2404075 = 3606113) B3606113
theorem B3205433 : Blo 2135435 3205433 := bstep (se 2 (by rfl) ⟨1202037, by rfl⟩ : syracuseStep 3205433 = 2404075) B2404075
theorem B2136955 : Blo 2135435 2136955 := bstep (se 1 (by rfl) ⟨1602716, by rfl⟩ : syracuseStep 2136955 = 3205433) B3205433
theorem B3338437 : Blo 2135435 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B71219989 : Blo 2135435 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B94959985 : Blo 2135435 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B126613313 : Blo 2135435 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B84408875 : Blo 2135435 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B56272583 : Blo 2135435 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B150060221 : Blo 2135435 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B100040147 : Blo 2135435 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B66693431 : Blo 2135435 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B44462287 : Blo 2135435 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B237132197 : Blo 2135435 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B158088131 : Blo 2135435 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B105392087 : Blo 2135435 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B70261391 : Blo 2135435 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B46840927 : Blo 2135435 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B62454569 : Blo 2135435 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B166545517 : Blo 2135435 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B222060689 : Blo 2135435 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B148040459 : Blo 2135435 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B98693639 : Blo 2135435 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B65795759 : Blo 2135435 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B43863839 : Blo 2135435 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B29242559 : Blo 2135435 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B19495039 : Blo 2135435 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B25993385 : Blo 2135435 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B17328923 : Blo 2135435 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B11552615 : Blo 2135435 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B7701743 : Blo 2135435 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B20537981 : Blo 2135435 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B13691987 : Blo 2135435 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B9127991 : Blo 2135435 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B24341309 : Blo 2135435 24341309 := bstep (se 3 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 24341309 = 9127991) B9127991
theorem B16227539 : Blo 2135435 16227539 := bstep (se 1 (by rfl) ⟨12170654, by rfl⟩ : syracuseStep 16227539 = 24341309) B24341309
theorem B10818359 : Blo 2135435 10818359 := bstep (se 1 (by rfl) ⟨8113769, by rfl⟩ : syracuseStep 10818359 = 16227539) B16227539
theorem B7212239 : Blo 2135435 7212239 := bstep (se 1 (by rfl) ⟨5409179, by rfl⟩ : syracuseStep 7212239 = 10818359) B10818359
theorem B4808159 : Blo 2135435 4808159 := bstep (se 1 (by rfl) ⟨3606119, by rfl⟩ : syracuseStep 4808159 = 7212239) B7212239
theorem B3205439 : Blo 2135435 3205439 := bstep (se 1 (by rfl) ⟨2404079, by rfl⟩ : syracuseStep 3205439 = 4808159) B4808159
theorem B2136959 : Blo 2135435 2136959 := bstep (se 1 (by rfl) ⟨1602719, by rfl⟩ : syracuseStep 2136959 = 3205439) B3205439
theorem B3205445 : Blo 2135435 3205445 := bbase (se 4 (by rfl) ⟨300510, by rfl⟩ : syracuseStep 3205445 = 601021) (by norm_num)
theorem B2136963 : Blo 2135435 2136963 := bstep (se 1 (by rfl) ⟨1602722, by rfl⟩ : syracuseStep 2136963 = 3205445) B3205445
theorem B3606133 : Blo 2135435 3606133 := bbase (se 5 (by rfl) ⟨169037, by rfl⟩ : syracuseStep 3606133 = 338075) (by norm_num)
theorem B4808177 : Blo 2135435 4808177 := bstep (se 2 (by rfl) ⟨1803066, by rfl⟩ : syracuseStep 4808177 = 3606133) B3606133
theorem B3205451 : Blo 2135435 3205451 := bstep (se 1 (by rfl) ⟨2404088, by rfl⟩ : syracuseStep 3205451 = 4808177) B4808177
theorem B2136967 : Blo 2135435 2136967 := bstep (se 1 (by rfl) ⟨1602725, by rfl⟩ : syracuseStep 2136967 = 3205451) B3205451
theorem B2404093 : Blo 2135435 2404093 := bbase (se 3 (by rfl) ⟨450767, by rfl⟩ : syracuseStep 2404093 = 901535) (by norm_num)
theorem B3205457 : Blo 2135435 3205457 := bstep (se 2 (by rfl) ⟨1202046, by rfl⟩ : syracuseStep 3205457 = 2404093) B2404093
theorem B2136971 : Blo 2135435 2136971 := bstep (se 1 (by rfl) ⟨1602728, by rfl⟩ : syracuseStep 2136971 = 3205457) B3205457
theorem B7212293 : Blo 2135435 7212293 := bbase (se 4 (by rfl) ⟨676152, by rfl⟩ : syracuseStep 7212293 = 1352305) (by norm_num)
theorem B4808195 : Blo 2135435 4808195 := bstep (se 1 (by rfl) ⟨3606146, by rfl⟩ : syracuseStep 4808195 = 7212293) B7212293
theorem B3205463 : Blo 2135435 3205463 := bstep (se 1 (by rfl) ⟨2404097, by rfl⟩ : syracuseStep 3205463 = 4808195) B4808195
theorem B2136975 : Blo 2135435 2136975 := bstep (se 1 (by rfl) ⟨1602731, by rfl⟩ : syracuseStep 2136975 = 3205463) B3205463
theorem B3205469 : Blo 2135435 3205469 := bbase (se 3 (by rfl) ⟨601025, by rfl⟩ : syracuseStep 3205469 = 1202051) (by norm_num)
theorem B2136979 : Blo 2135435 2136979 := bstep (se 1 (by rfl) ⟨1602734, by rfl⟩ : syracuseStep 2136979 = 3205469) B3205469
theorem B4808213 : Blo 2135435 4808213 := bbase (se 6 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 4808213 = 225385) (by norm_num)
theorem B3205475 : Blo 2135435 3205475 := bstep (se 1 (by rfl) ⟨2404106, by rfl⟩ : syracuseStep 3205475 = 4808213) B4808213
theorem B2136983 : Blo 2135435 2136983 := bstep (se 1 (by rfl) ⟨1602737, by rfl⟩ : syracuseStep 2136983 = 3205475) B3205475
theorem B8113877 : Blo 2135435 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B5409251 : Blo 2135435 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B3606167 : Blo 2135435 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B2404111 : Blo 2135435 2404111 := bstep (se 1 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 2404111 = 3606167) B3606167
theorem B3205481 : Blo 2135435 3205481 := bstep (se 2 (by rfl) ⟨1202055, by rfl⟩ : syracuseStep 3205481 = 2404111) B2404111
theorem B2136987 : Blo 2135435 2136987 := bstep (se 1 (by rfl) ⟨1602740, by rfl⟩ : syracuseStep 2136987 = 3205481) B3205481
theorem B12170837 : Blo 2135435 12170837 := bbase (se 8 (by rfl) ⟨71313, by rfl⟩ : syracuseStep 12170837 = 142627) (by norm_num)
theorem B8113891 : Blo 2135435 8113891 := bstep (se 1 (by rfl) ⟨6085418, by rfl⟩ : syracuseStep 8113891 = 12170837) B12170837
theorem B10818521 : Blo 2135435 10818521 := bstep (se 2 (by rfl) ⟨4056945, by rfl⟩ : syracuseStep 10818521 = 8113891) B8113891
theorem B7212347 : Blo 2135435 7212347 := bstep (se 1 (by rfl) ⟨5409260, by rfl⟩ : syracuseStep 7212347 = 10818521) B10818521
theorem B4808231 : Blo 2135435 4808231 := bstep (se 1 (by rfl) ⟨3606173, by rfl⟩ : syracuseStep 4808231 = 7212347) B7212347
theorem B3205487 : Blo 2135435 3205487 := bstep (se 1 (by rfl) ⟨2404115, by rfl⟩ : syracuseStep 3205487 = 4808231) B4808231
theorem B2136991 : Blo 2135435 2136991 := bstep (se 1 (by rfl) ⟨1602743, by rfl⟩ : syracuseStep 2136991 = 3205487) B3205487
theorem B3205493 : Blo 2135435 3205493 := bbase (se 5 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 3205493 = 300515) (by norm_num)
theorem B2136995 : Blo 2135435 2136995 := bstep (se 1 (by rfl) ⟨1602746, by rfl⟩ : syracuseStep 2136995 = 3205493) B3205493
theorem B2282041 : Blo 2135435 2282041 := bbase (se 2 (by rfl) ⟨855765, by rfl⟩ : syracuseStep 2282041 = 1711531) (by norm_num)
theorem B3042721 : Blo 2135435 3042721 := bstep (se 2 (by rfl) ⟨1141020, by rfl⟩ : syracuseStep 3042721 = 2282041) B2282041
theorem B4056961 : Blo 2135435 4056961 := bstep (se 2 (by rfl) ⟨1521360, by rfl⟩ : syracuseStep 4056961 = 3042721) B3042721
theorem B5409281 : Blo 2135435 5409281 := bstep (se 2 (by rfl) ⟨2028480, by rfl⟩ : syracuseStep 5409281 = 4056961) B4056961
theorem B3606187 : Blo 2135435 3606187 := bstep (se 1 (by rfl) ⟨2704640, by rfl⟩ : syracuseStep 3606187 = 5409281) B5409281
theorem B4808249 : Blo 2135435 4808249 := bstep (se 2 (by rfl) ⟨1803093, by rfl⟩ : syracuseStep 4808249 = 3606187) B3606187
theorem B3205499 : Blo 2135435 3205499 := bstep (se 1 (by rfl) ⟨2404124, by rfl⟩ : syracuseStep 3205499 = 4808249) B4808249
theorem B2136999 : Blo 2135435 2136999 := bstep (se 1 (by rfl) ⟨1602749, by rfl⟩ : syracuseStep 2136999 = 3205499) B3205499
theorem B2404129 : Blo 2135435 2404129 := bbase (se 2 (by rfl) ⟨901548, by rfl⟩ : syracuseStep 2404129 = 1803097) (by norm_num)
theorem B3205505 : Blo 2135435 3205505 := bstep (se 2 (by rfl) ⟨1202064, by rfl⟩ : syracuseStep 3205505 = 2404129) B2404129
theorem B2137003 : Blo 2135435 2137003 := bstep (se 1 (by rfl) ⟨1602752, by rfl⟩ : syracuseStep 2137003 = 3205505) B3205505
theorem B5409301 : Blo 2135435 5409301 := bbase (se 6 (by rfl) ⟨126780, by rfl⟩ : syracuseStep 5409301 = 253561) (by norm_num)
theorem B7212401 : Blo 2135435 7212401 := bstep (se 2 (by rfl) ⟨2704650, by rfl⟩ : syracuseStep 7212401 = 5409301) B5409301
theorem B4808267 : Blo 2135435 4808267 := bstep (se 1 (by rfl) ⟨3606200, by rfl⟩ : syracuseStep 4808267 = 7212401) B7212401
theorem B3205511 : Blo 2135435 3205511 := bstep (se 1 (by rfl) ⟨2404133, by rfl⟩ : syracuseStep 3205511 = 4808267) B4808267
theorem B2137007 : Blo 2135435 2137007 := bstep (se 1 (by rfl) ⟨1602755, by rfl⟩ : syracuseStep 2137007 = 3205511) B3205511
theorem B3205517 : Blo 2135435 3205517 := bbase (se 3 (by rfl) ⟨601034, by rfl⟩ : syracuseStep 3205517 = 1202069) (by norm_num)
theorem B2137011 : Blo 2135435 2137011 := bstep (se 1 (by rfl) ⟨1602758, by rfl⟩ : syracuseStep 2137011 = 3205517) B3205517
theorem B4808285 : Blo 2135435 4808285 := bbase (se 3 (by rfl) ⟨901553, by rfl⟩ : syracuseStep 4808285 = 1803107) (by norm_num)
theorem B3205523 : Blo 2135435 3205523 := bstep (se 1 (by rfl) ⟨2404142, by rfl⟩ : syracuseStep 3205523 = 4808285) B4808285
theorem B2137015 : Blo 2135435 2137015 := bstep (se 1 (by rfl) ⟨1602761, by rfl⟩ : syracuseStep 2137015 = 3205523) B3205523
theorem B3606221 : Blo 2135435 3606221 := bbase (se 3 (by rfl) ⟨676166, by rfl⟩ : syracuseStep 3606221 = 1352333) (by norm_num)
theorem B2404147 : Blo 2135435 2404147 := bstep (se 1 (by rfl) ⟨1803110, by rfl⟩ : syracuseStep 2404147 = 3606221) B3606221
theorem B3205529 : Blo 2135435 3205529 := bstep (se 2 (by rfl) ⟨1202073, by rfl⟩ : syracuseStep 3205529 = 2404147) B2404147
theorem B2137019 : Blo 2135435 2137019 := bstep (se 1 (by rfl) ⟨1602764, by rfl⟩ : syracuseStep 2137019 = 3205529) B3205529
theorem B2741573 : Blo 2135435 2741573 := bbase (se 4 (by rfl) ⟨257022, by rfl⟩ : syracuseStep 2741573 = 514045) (by norm_num)
theorem B7310861 : Blo 2135435 7310861 := bstep (se 3 (by rfl) ⟨1370786, by rfl⟩ : syracuseStep 7310861 = 2741573) B2741573
theorem B4873907 : Blo 2135435 4873907 := bstep (se 1 (by rfl) ⟨3655430, by rfl⟩ : syracuseStep 4873907 = 7310861) B7310861
theorem B3249271 : Blo 2135435 3249271 := bstep (se 1 (by rfl) ⟨2436953, by rfl⟩ : syracuseStep 3249271 = 4873907) B4873907
theorem B4332361 : Blo 2135435 4332361 := bstep (se 2 (by rfl) ⟨1624635, by rfl⟩ : syracuseStep 4332361 = 3249271) B3249271
theorem B5776481 : Blo 2135435 5776481 := bstep (se 2 (by rfl) ⟨2166180, by rfl⟩ : syracuseStep 5776481 = 4332361) B4332361
theorem B3850987 : Blo 2135435 3850987 := bstep (se 1 (by rfl) ⟨2888240, by rfl⟩ : syracuseStep 3850987 = 5776481) B5776481
theorem B5134649 : Blo 2135435 5134649 := bstep (se 2 (by rfl) ⟨1925493, by rfl⟩ : syracuseStep 5134649 = 3850987) B3850987
theorem B13692397 : Blo 2135435 13692397 := bstep (se 3 (by rfl) ⟨2567324, by rfl⟩ : syracuseStep 13692397 = 5134649) B5134649
theorem B18256529 : Blo 2135435 18256529 := bstep (se 2 (by rfl) ⟨6846198, by rfl⟩ : syracuseStep 18256529 = 13692397) B13692397
theorem B12171019 : Blo 2135435 12171019 := bstep (se 1 (by rfl) ⟨9128264, by rfl⟩ : syracuseStep 12171019 = 18256529) B18256529
theorem B16228025 : Blo 2135435 16228025 := bstep (se 2 (by rfl) ⟨6085509, by rfl⟩ : syracuseStep 16228025 = 12171019) B12171019
theorem B10818683 : Blo 2135435 10818683 := bstep (se 1 (by rfl) ⟨8114012, by rfl⟩ : syracuseStep 10818683 = 16228025) B16228025
theorem B7212455 : Blo 2135435 7212455 := bstep (se 1 (by rfl) ⟨5409341, by rfl⟩ : syracuseStep 7212455 = 10818683) B10818683
theorem B4808303 : Blo 2135435 4808303 := bstep (se 1 (by rfl) ⟨3606227, by rfl⟩ : syracuseStep 4808303 = 7212455) B7212455
theorem B3205535 : Blo 2135435 3205535 := bstep (se 1 (by rfl) ⟨2404151, by rfl⟩ : syracuseStep 3205535 = 4808303) B4808303
theorem B2137023 : Blo 2135435 2137023 := bstep (se 1 (by rfl) ⟨1602767, by rfl⟩ : syracuseStep 2137023 = 3205535) B3205535
theorem B3205541 : Blo 2135435 3205541 := bbase (se 4 (by rfl) ⟨300519, by rfl⟩ : syracuseStep 3205541 = 601039) (by norm_num)
theorem B2137027 : Blo 2135435 2137027 := bstep (se 1 (by rfl) ⟨1602770, by rfl⟩ : syracuseStep 2137027 = 3205541) B3205541
theorem B2704681 : Blo 2135435 2704681 := bbase (se 2 (by rfl) ⟨1014255, by rfl⟩ : syracuseStep 2704681 = 2028511) (by norm_num)
theorem B3606241 : Blo 2135435 3606241 := bstep (se 2 (by rfl) ⟨1352340, by rfl⟩ : syracuseStep 3606241 = 2704681) B2704681
theorem B4808321 : Blo 2135435 4808321 := bstep (se 2 (by rfl) ⟨1803120, by rfl⟩ : syracuseStep 4808321 = 3606241) B3606241
theorem B3205547 : Blo 2135435 3205547 := bstep (se 1 (by rfl) ⟨2404160, by rfl⟩ : syracuseStep 3205547 = 4808321) B4808321
theorem B2137031 : Blo 2135435 2137031 := bstep (se 1 (by rfl) ⟨1602773, by rfl⟩ : syracuseStep 2137031 = 3205547) B3205547
theorem B2404165 : Blo 2135435 2404165 := bbase (se 4 (by rfl) ⟨225390, by rfl⟩ : syracuseStep 2404165 = 450781) (by norm_num)
theorem B3205553 : Blo 2135435 3205553 := bstep (se 2 (by rfl) ⟨1202082, by rfl⟩ : syracuseStep 3205553 = 2404165) B2404165
theorem B2137035 : Blo 2135435 2137035 := bstep (se 1 (by rfl) ⟨1602776, by rfl⟩ : syracuseStep 2137035 = 3205553) B3205553
theorem B4057037 : Blo 2135435 4057037 := bbase (se 3 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 4057037 = 1521389) (by norm_num)
theorem B2704691 : Blo 2135435 2704691 := bstep (se 1 (by rfl) ⟨2028518, by rfl⟩ : syracuseStep 2704691 = 4057037) B4057037
theorem B7212509 : Blo 2135435 7212509 := bstep (se 3 (by rfl) ⟨1352345, by rfl⟩ : syracuseStep 7212509 = 2704691) B2704691
theorem B4808339 : Blo 2135435 4808339 := bstep (se 1 (by rfl) ⟨3606254, by rfl⟩ : syracuseStep 4808339 = 7212509) B7212509
theorem B3205559 : Blo 2135435 3205559 := bstep (se 1 (by rfl) ⟨2404169, by rfl⟩ : syracuseStep 3205559 = 4808339) B4808339
theorem B2137039 : Blo 2135435 2137039 := bstep (se 1 (by rfl) ⟨1602779, by rfl⟩ : syracuseStep 2137039 = 3205559) B3205559
theorem B3205565 : Blo 2135435 3205565 := bbase (se 3 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 3205565 = 1202087) (by norm_num)
theorem B2137043 : Blo 2135435 2137043 := bstep (se 1 (by rfl) ⟨1602782, by rfl⟩ : syracuseStep 2137043 = 3205565) B3205565
theorem B4808357 : Blo 2135435 4808357 := bbase (se 4 (by rfl) ⟨450783, by rfl⟩ : syracuseStep 4808357 = 901567) (by norm_num)
theorem B3205571 : Blo 2135435 3205571 := bstep (se 1 (by rfl) ⟨2404178, by rfl⟩ : syracuseStep 3205571 = 4808357) B4808357
theorem B2137047 : Blo 2135435 2137047 := bstep (se 1 (by rfl) ⟨1602785, by rfl⟩ : syracuseStep 2137047 = 3205571) B3205571
theorem B5409413 : Blo 2135435 5409413 := bbase (se 4 (by rfl) ⟨507132, by rfl⟩ : syracuseStep 5409413 = 1014265) (by norm_num)
theorem B3606275 : Blo 2135435 3606275 := bstep (se 1 (by rfl) ⟨2704706, by rfl⟩ : syracuseStep 3606275 = 5409413) B5409413
theorem B2404183 : Blo 2135435 2404183 := bstep (se 1 (by rfl) ⟨1803137, by rfl⟩ : syracuseStep 2404183 = 3606275) B3606275
theorem B3205577 : Blo 2135435 3205577 := bstep (se 2 (by rfl) ⟨1202091, by rfl⟩ : syracuseStep 3205577 = 2404183) B2404183
theorem B2137051 : Blo 2135435 2137051 := bstep (se 1 (by rfl) ⟨1602788, by rfl⟩ : syracuseStep 2137051 = 3205577) B3205577
theorem B8664853 : Blo 2135435 8664853 := bbase (se 6 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 8664853 = 406165) (by norm_num)
theorem B11553137 : Blo 2135435 11553137 := bstep (se 2 (by rfl) ⟨4332426, by rfl⟩ : syracuseStep 11553137 = 8664853) B8664853
theorem B7702091 : Blo 2135435 7702091 := bstep (se 1 (by rfl) ⟨5776568, by rfl⟩ : syracuseStep 7702091 = 11553137) B11553137
theorem B5134727 : Blo 2135435 5134727 := bstep (se 1 (by rfl) ⟨3851045, by rfl⟩ : syracuseStep 5134727 = 7702091) B7702091
theorem B3423151 : Blo 2135435 3423151 := bstep (se 1 (by rfl) ⟨2567363, by rfl⟩ : syracuseStep 3423151 = 5134727) B5134727
theorem B4564201 : Blo 2135435 4564201 := bstep (se 2 (by rfl) ⟨1711575, by rfl⟩ : syracuseStep 4564201 = 3423151) B3423151
theorem B6085601 : Blo 2135435 6085601 := bstep (se 2 (by rfl) ⟨2282100, by rfl⟩ : syracuseStep 6085601 = 4564201) B4564201
theorem B4057067 : Blo 2135435 4057067 := bstep (se 1 (by rfl) ⟨3042800, by rfl⟩ : syracuseStep 4057067 = 6085601) B6085601
theorem B10818845 : Blo 2135435 10818845 := bstep (se 3 (by rfl) ⟨2028533, by rfl⟩ : syracuseStep 10818845 = 4057067) B4057067
theorem B7212563 : Blo 2135435 7212563 := bstep (se 1 (by rfl) ⟨5409422, by rfl⟩ : syracuseStep 7212563 = 10818845) B10818845
theorem B4808375 : Blo 2135435 4808375 := bstep (se 1 (by rfl) ⟨3606281, by rfl⟩ : syracuseStep 4808375 = 7212563) B7212563
theorem B3205583 : Blo 2135435 3205583 := bstep (se 1 (by rfl) ⟨2404187, by rfl⟩ : syracuseStep 3205583 = 4808375) B4808375
theorem B2137055 : Blo 2135435 2137055 := bstep (se 1 (by rfl) ⟨1602791, by rfl⟩ : syracuseStep 2137055 = 3205583) B3205583
theorem B3205589 : Blo 2135435 3205589 := bbase (se 7 (by rfl) ⟨37565, by rfl⟩ : syracuseStep 3205589 = 75131) (by norm_num)
theorem B2137059 : Blo 2135435 2137059 := bstep (se 1 (by rfl) ⟨1602794, by rfl⟩ : syracuseStep 2137059 = 3205589) B3205589
theorem B8114165 : Blo 2135435 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B5409443 : Blo 2135435 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B3606295 : Blo 2135435 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B4808393 : Blo 2135435 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B3205595 : Blo 2135435 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B2137063 : Blo 2135435 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B2404201 : Blo 2135435 2404201 := bbase (se 2 (by rfl) ⟨901575, by rfl⟩ : syracuseStep 2404201 = 1803151) (by norm_num)
theorem B3205601 : Blo 2135435 3205601 := bstep (se 2 (by rfl) ⟨1202100, by rfl⟩ : syracuseStep 3205601 = 2404201) B2404201
theorem B2137067 : Blo 2135435 2137067 := bstep (se 1 (by rfl) ⟨1602800, by rfl⟩ : syracuseStep 2137067 = 3205601) B3205601
theorem B5134765 : Blo 2135435 5134765 := bbase (se 3 (by rfl) ⟨962768, by rfl⟩ : syracuseStep 5134765 = 1925537) (by norm_num)
theorem B6846353 : Blo 2135435 6846353 := bstep (se 2 (by rfl) ⟨2567382, by rfl⟩ : syracuseStep 6846353 = 5134765) B5134765
theorem B4564235 : Blo 2135435 4564235 := bstep (se 1 (by rfl) ⟨3423176, by rfl⟩ : syracuseStep 4564235 = 6846353) B6846353
theorem B12171293 : Blo 2135435 12171293 := bstep (se 3 (by rfl) ⟨2282117, by rfl⟩ : syracuseStep 12171293 = 4564235) B4564235
theorem B8114195 : Blo 2135435 8114195 := bstep (se 1 (by rfl) ⟨6085646, by rfl⟩ : syracuseStep 8114195 = 12171293) B12171293
theorem B5409463 : Blo 2135435 5409463 := bstep (se 1 (by rfl) ⟨4057097, by rfl⟩ : syracuseStep 5409463 = 8114195) B8114195
theorem B7212617 : Blo 2135435 7212617 := bstep (se 2 (by rfl) ⟨2704731, by rfl⟩ : syracuseStep 7212617 = 5409463) B5409463
theorem B4808411 : Blo 2135435 4808411 := bstep (se 1 (by rfl) ⟨3606308, by rfl⟩ : syracuseStep 4808411 = 7212617) B7212617
theorem B3205607 : Blo 2135435 3205607 := bstep (se 1 (by rfl) ⟨2404205, by rfl⟩ : syracuseStep 3205607 = 4808411) B4808411
theorem B2137071 : Blo 2135435 2137071 := bstep (se 1 (by rfl) ⟨1602803, by rfl⟩ : syracuseStep 2137071 = 3205607) B3205607
theorem B3205613 : Blo 2135435 3205613 := bbase (se 3 (by rfl) ⟨601052, by rfl⟩ : syracuseStep 3205613 = 1202105) (by norm_num)
theorem B2137075 : Blo 2135435 2137075 := bstep (se 1 (by rfl) ⟨1602806, by rfl⟩ : syracuseStep 2137075 = 3205613) B3205613
theorem B4808429 : Blo 2135435 4808429 := bbase (se 3 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 4808429 = 1803161) (by norm_num)
theorem B3205619 : Blo 2135435 3205619 := bstep (se 1 (by rfl) ⟨2404214, by rfl⟩ : syracuseStep 3205619 = 4808429) B4808429
theorem B2137079 : Blo 2135435 2137079 := bstep (se 1 (by rfl) ⟨1602809, by rfl⟩ : syracuseStep 2137079 = 3205619) B3205619
theorem B3423197 : Blo 2135435 3423197 := bbase (se 3 (by rfl) ⟨641849, by rfl⟩ : syracuseStep 3423197 = 1283699) (by norm_num)
theorem B2282131 : Blo 2135435 2282131 := bstep (se 1 (by rfl) ⟨1711598, by rfl⟩ : syracuseStep 2282131 = 3423197) B3423197
theorem B3042841 : Blo 2135435 3042841 := bstep (se 2 (by rfl) ⟨1141065, by rfl⟩ : syracuseStep 3042841 = 2282131) B2282131
theorem B4057121 : Blo 2135435 4057121 := bstep (se 2 (by rfl) ⟨1521420, by rfl⟩ : syracuseStep 4057121 = 3042841) B3042841
theorem B2704747 : Blo 2135435 2704747 := bstep (se 1 (by rfl) ⟨2028560, by rfl⟩ : syracuseStep 2704747 = 4057121) B4057121
theorem B3606329 : Blo 2135435 3606329 := bstep (se 2 (by rfl) ⟨1352373, by rfl⟩ : syracuseStep 3606329 = 2704747) B2704747
theorem B2404219 : Blo 2135435 2404219 := bstep (se 1 (by rfl) ⟨1803164, by rfl⟩ : syracuseStep 2404219 = 3606329) B3606329
theorem B3205625 : Blo 2135435 3205625 := bstep (se 2 (by rfl) ⟨1202109, by rfl⟩ : syracuseStep 3205625 = 2404219) B2404219
theorem B2137083 : Blo 2135435 2137083 := bstep (se 1 (by rfl) ⟨1602812, by rfl⟩ : syracuseStep 2137083 = 3205625) B3205625
theorem B4168589 : Blo 2135435 4168589 := bbase (se 3 (by rfl) ⟨781610, by rfl⟩ : syracuseStep 4168589 = 1563221) (by norm_num)
theorem B11116237 : Blo 2135435 11116237 := bstep (se 3 (by rfl) ⟨2084294, by rfl⟩ : syracuseStep 11116237 = 4168589) B4168589
theorem B14821649 : Blo 2135435 14821649 := bstep (se 2 (by rfl) ⟨5558118, by rfl⟩ : syracuseStep 14821649 = 11116237) B11116237
theorem B9881099 : Blo 2135435 9881099 := bstep (se 1 (by rfl) ⟨7410824, by rfl⟩ : syracuseStep 9881099 = 14821649) B14821649
theorem B6587399 : Blo 2135435 6587399 := bstep (se 1 (by rfl) ⟨4940549, by rfl⟩ : syracuseStep 6587399 = 9881099) B9881099
theorem B17566397 : Blo 2135435 17566397 := bstep (se 3 (by rfl) ⟨3293699, by rfl⟩ : syracuseStep 17566397 = 6587399) B6587399
theorem B11710931 : Blo 2135435 11710931 := bstep (se 1 (by rfl) ⟨8783198, by rfl⟩ : syracuseStep 11710931 = 17566397) B17566397
theorem B124916597 : Blo 2135435 124916597 := bstep (se 5 (by rfl) ⟨5855465, by rfl⟩ : syracuseStep 124916597 = 11710931) B11710931
theorem B83277731 : Blo 2135435 83277731 := bstep (se 1 (by rfl) ⟨62458298, by rfl⟩ : syracuseStep 83277731 = 124916597) B124916597
theorem B222073949 : Blo 2135435 222073949 := bstep (se 3 (by rfl) ⟨41638865, by rfl⟩ : syracuseStep 222073949 = 83277731) B83277731
theorem B148049299 : Blo 2135435 148049299 := bstep (se 1 (by rfl) ⟨111036974, by rfl⟩ : syracuseStep 148049299 = 222073949) B222073949
theorem B197399065 : Blo 2135435 197399065 := bstep (se 2 (by rfl) ⟨74024649, by rfl⟩ : syracuseStep 197399065 = 148049299) B148049299
theorem B263198753 : Blo 2135435 263198753 := bstep (se 2 (by rfl) ⟨98699532, by rfl⟩ : syracuseStep 263198753 = 197399065) B197399065
theorem B175465835 : Blo 2135435 175465835 := bstep (se 1 (by rfl) ⟨131599376, by rfl⟩ : syracuseStep 175465835 = 263198753) B263198753
theorem B116977223 : Blo 2135435 116977223 := bstep (se 1 (by rfl) ⟨87732917, by rfl⟩ : syracuseStep 116977223 = 175465835) B175465835
theorem B311939261 : Blo 2135435 311939261 := bstep (se 3 (by rfl) ⟨58488611, by rfl⟩ : syracuseStep 311939261 = 116977223) B116977223
theorem B207959507 : Blo 2135435 207959507 := bstep (se 1 (by rfl) ⟨155969630, by rfl⟩ : syracuseStep 207959507 = 311939261) B311939261
theorem B138639671 : Blo 2135435 138639671 := bstep (se 1 (by rfl) ⟨103979753, by rfl⟩ : syracuseStep 138639671 = 207959507) B207959507
theorem B92426447 : Blo 2135435 92426447 := bstep (se 1 (by rfl) ⟨69319835, by rfl⟩ : syracuseStep 92426447 = 138639671) B138639671
theorem B61617631 : Blo 2135435 61617631 := bstep (se 1 (by rfl) ⟨46213223, by rfl⟩ : syracuseStep 61617631 = 92426447) B92426447
theorem B82156841 : Blo 2135435 82156841 := bstep (se 2 (by rfl) ⟨30808815, by rfl⟩ : syracuseStep 82156841 = 61617631) B61617631
theorem B54771227 : Blo 2135435 54771227 := bstep (se 1 (by rfl) ⟨41078420, by rfl⟩ : syracuseStep 54771227 = 82156841) B82156841
theorem B36514151 : Blo 2135435 36514151 := bstep (se 1 (by rfl) ⟨27385613, by rfl⟩ : syracuseStep 36514151 = 54771227) B54771227
theorem B24342767 : Blo 2135435 24342767 := bstep (se 1 (by rfl) ⟨18257075, by rfl⟩ : syracuseStep 24342767 = 36514151) B36514151
theorem B16228511 : Blo 2135435 16228511 := bstep (se 1 (by rfl) ⟨12171383, by rfl⟩ : syracuseStep 16228511 = 24342767) B24342767
theorem B10819007 : Blo 2135435 10819007 := bstep (se 1 (by rfl) ⟨8114255, by rfl⟩ : syracuseStep 10819007 = 16228511) B16228511
theorem B7212671 : Blo 2135435 7212671 := bstep (se 1 (by rfl) ⟨5409503, by rfl⟩ : syracuseStep 7212671 = 10819007) B10819007
theorem B4808447 : Blo 2135435 4808447 := bstep (se 1 (by rfl) ⟨3606335, by rfl⟩ : syracuseStep 4808447 = 7212671) B7212671
theorem B3205631 : Blo 2135435 3205631 := bstep (se 1 (by rfl) ⟨2404223, by rfl⟩ : syracuseStep 3205631 = 4808447) B4808447
theorem B2137087 : Blo 2135435 2137087 := bstep (se 1 (by rfl) ⟨1602815, by rfl⟩ : syracuseStep 2137087 = 3205631) B3205631
theorem B3205637 : Blo 2135435 3205637 := bbase (se 4 (by rfl) ⟨300528, by rfl⟩ : syracuseStep 3205637 = 601057) (by norm_num)
theorem B2137091 : Blo 2135435 2137091 := bstep (se 1 (by rfl) ⟨1602818, by rfl⟩ : syracuseStep 2137091 = 3205637) B3205637
theorem B3606349 : Blo 2135435 3606349 := bbase (se 3 (by rfl) ⟨676190, by rfl⟩ : syracuseStep 3606349 = 1352381) (by norm_num)
theorem B4808465 : Blo 2135435 4808465 := bstep (se 2 (by rfl) ⟨1803174, by rfl⟩ : syracuseStep 4808465 = 3606349) B3606349
theorem B3205643 : Blo 2135435 3205643 := bstep (se 1 (by rfl) ⟨2404232, by rfl⟩ : syracuseStep 3205643 = 4808465) B4808465
theorem B2137095 : Blo 2135435 2137095 := bstep (se 1 (by rfl) ⟨1602821, by rfl⟩ : syracuseStep 2137095 = 3205643) B3205643
theorem B2404237 : Blo 2135435 2404237 := bbase (se 3 (by rfl) ⟨450794, by rfl⟩ : syracuseStep 2404237 = 901589) (by norm_num)
theorem B3205649 : Blo 2135435 3205649 := bstep (se 2 (by rfl) ⟨1202118, by rfl⟩ : syracuseStep 3205649 = 2404237) B2404237
theorem B2137099 : Blo 2135435 2137099 := bstep (se 1 (by rfl) ⟨1602824, by rfl⟩ : syracuseStep 2137099 = 3205649) B3205649
theorem B7212725 : Blo 2135435 7212725 := bbase (se 5 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 7212725 = 676193) (by norm_num)
theorem B4808483 : Blo 2135435 4808483 := bstep (se 1 (by rfl) ⟨3606362, by rfl⟩ : syracuseStep 4808483 = 7212725) B7212725
theorem B3205655 : Blo 2135435 3205655 := bstep (se 1 (by rfl) ⟨2404241, by rfl⟩ : syracuseStep 3205655 = 4808483) B4808483
theorem B2137103 : Blo 2135435 2137103 := bstep (se 1 (by rfl) ⟨1602827, by rfl⟩ : syracuseStep 2137103 = 3205655) B3205655
theorem B3205661 : Blo 2135435 3205661 := bbase (se 3 (by rfl) ⟨601061, by rfl⟩ : syracuseStep 3205661 = 1202123) (by norm_num)
theorem B2137107 : Blo 2135435 2137107 := bstep (se 1 (by rfl) ⟨1602830, by rfl⟩ : syracuseStep 2137107 = 3205661) B3205661
theorem B4808501 : Blo 2135435 4808501 := bbase (se 5 (by rfl) ⟨225398, by rfl⟩ : syracuseStep 4808501 = 450797) (by norm_num)
theorem B3205667 : Blo 2135435 3205667 := bstep (se 1 (by rfl) ⟨2404250, by rfl⟩ : syracuseStep 3205667 = 4808501) B4808501
theorem B2137111 : Blo 2135435 2137111 := bstep (se 1 (by rfl) ⟨1602833, by rfl⟩ : syracuseStep 2137111 = 3205667) B3205667
theorem B11553461 : Blo 2135435 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B7702307 : Blo 2135435 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B5134871 : Blo 2135435 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B13692989 : Blo 2135435 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B9128659 : Blo 2135435 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B12171545 : Blo 2135435 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B8114363 : Blo 2135435 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B5409575 : Blo 2135435 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B3606383 : Blo 2135435 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B2404255 : Blo 2135435 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B3205673 : Blo 2135435 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B2137115 : Blo 2135435 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B13693013 : Blo 2135435 13693013 := bbase (se 8 (by rfl) ⟨80232, by rfl⟩ : syracuseStep 13693013 = 160465) (by norm_num)
theorem B9128675 : Blo 2135435 9128675 := bstep (se 1 (by rfl) ⟨6846506, by rfl⟩ : syracuseStep 9128675 = 13693013) B13693013
theorem B6085783 : Blo 2135435 6085783 := bstep (se 1 (by rfl) ⟨4564337, by rfl⟩ : syracuseStep 6085783 = 9128675) B9128675
theorem B8114377 : Blo 2135435 8114377 := bstep (se 2 (by rfl) ⟨3042891, by rfl⟩ : syracuseStep 8114377 = 6085783) B6085783
theorem B10819169 : Blo 2135435 10819169 := bstep (se 2 (by rfl) ⟨4057188, by rfl⟩ : syracuseStep 10819169 = 8114377) B8114377
theorem B7212779 : Blo 2135435 7212779 := bstep (se 1 (by rfl) ⟨5409584, by rfl⟩ : syracuseStep 7212779 = 10819169) B10819169
theorem B4808519 : Blo 2135435 4808519 := bstep (se 1 (by rfl) ⟨3606389, by rfl⟩ : syracuseStep 4808519 = 7212779) B7212779
theorem B3205679 : Blo 2135435 3205679 := bstep (se 1 (by rfl) ⟨2404259, by rfl⟩ : syracuseStep 3205679 = 4808519) B4808519
theorem B2137119 : Blo 2135435 2137119 := bstep (se 1 (by rfl) ⟨1602839, by rfl⟩ : syracuseStep 2137119 = 3205679) B3205679
theorem B3205685 : Blo 2135435 3205685 := bbase (se 5 (by rfl) ⟨150266, by rfl⟩ : syracuseStep 3205685 = 300533) (by norm_num)
theorem B2137123 : Blo 2135435 2137123 := bstep (se 1 (by rfl) ⟨1602842, by rfl⟩ : syracuseStep 2137123 = 3205685) B3205685
theorem B5409605 : Blo 2135435 5409605 := bbase (se 4 (by rfl) ⟨507150, by rfl⟩ : syracuseStep 5409605 = 1014301) (by norm_num)
theorem B3606403 : Blo 2135435 3606403 := bstep (se 1 (by rfl) ⟨2704802, by rfl⟩ : syracuseStep 3606403 = 5409605) B5409605
theorem B4808537 : Blo 2135435 4808537 := bstep (se 2 (by rfl) ⟨1803201, by rfl⟩ : syracuseStep 4808537 = 3606403) B3606403
theorem B3205691 : Blo 2135435 3205691 := bstep (se 1 (by rfl) ⟨2404268, by rfl⟩ : syracuseStep 3205691 = 4808537) B4808537
theorem B2137127 : Blo 2135435 2137127 := bstep (se 1 (by rfl) ⟨1602845, by rfl⟩ : syracuseStep 2137127 = 3205691) B3205691
theorem B2404273 : Blo 2135435 2404273 := bbase (se 2 (by rfl) ⟨901602, by rfl⟩ : syracuseStep 2404273 = 1803205) (by norm_num)
theorem B3205697 : Blo 2135435 3205697 := bstep (se 2 (by rfl) ⟨1202136, by rfl⟩ : syracuseStep 3205697 = 2404273) B2404273
theorem B2137131 : Blo 2135435 2137131 := bstep (se 1 (by rfl) ⟨1602848, by rfl⟩ : syracuseStep 2137131 = 3205697) B3205697
theorem B6085829 : Blo 2135435 6085829 := bbase (se 4 (by rfl) ⟨570546, by rfl⟩ : syracuseStep 6085829 = 1141093) (by norm_num)
theorem B4057219 : Blo 2135435 4057219 := bstep (se 1 (by rfl) ⟨3042914, by rfl⟩ : syracuseStep 4057219 = 6085829) B6085829
theorem B5409625 : Blo 2135435 5409625 := bstep (se 2 (by rfl) ⟨2028609, by rfl⟩ : syracuseStep 5409625 = 4057219) B4057219
theorem B7212833 : Blo 2135435 7212833 := bstep (se 2 (by rfl) ⟨2704812, by rfl⟩ : syracuseStep 7212833 = 5409625) B5409625
theorem B4808555 : Blo 2135435 4808555 := bstep (se 1 (by rfl) ⟨3606416, by rfl⟩ : syracuseStep 4808555 = 7212833) B7212833
theorem B3205703 : Blo 2135435 3205703 := bstep (se 1 (by rfl) ⟨2404277, by rfl⟩ : syracuseStep 3205703 = 4808555) B4808555
theorem B2137135 : Blo 2135435 2137135 := bstep (se 1 (by rfl) ⟨1602851, by rfl⟩ : syracuseStep 2137135 = 3205703) B3205703
theorem B3205709 : Blo 2135435 3205709 := bbase (se 3 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 3205709 = 1202141) (by norm_num)
theorem B2137139 : Blo 2135435 2137139 := bstep (se 1 (by rfl) ⟨1602854, by rfl⟩ : syracuseStep 2137139 = 3205709) B3205709
theorem B4808573 : Blo 2135435 4808573 := bbase (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) (by norm_num)
theorem B3205715 : Blo 2135435 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B2137143 : Blo 2135435 2137143 := bstep (se 1 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 2137143 = 3205715) B3205715
theorem B3606437 : Blo 2135435 3606437 := bbase (se 4 (by rfl) ⟨338103, by rfl⟩ : syracuseStep 3606437 = 676207) (by norm_num)
theorem B2404291 : Blo 2135435 2404291 := bstep (se 1 (by rfl) ⟨1803218, by rfl⟩ : syracuseStep 2404291 = 3606437) B3606437
theorem B3205721 : Blo 2135435 3205721 := bstep (se 2 (by rfl) ⟨1202145, by rfl⟩ : syracuseStep 3205721 = 2404291) B2404291
theorem B2137147 : Blo 2135435 2137147 := bstep (se 1 (by rfl) ⟨1602860, by rfl⟩ : syracuseStep 2137147 = 3205721) B3205721
theorem B5483477 : Blo 2135435 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B3655651 : Blo 2135435 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B4874201 : Blo 2135435 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B3249467 : Blo 2135435 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B2166311 : Blo 2135435 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B5776829 : Blo 2135435 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B3851219 : Blo 2135435 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B2567479 : Blo 2135435 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B3423305 : Blo 2135435 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B2282203 : Blo 2135435 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B3042937 : Blo 2135435 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B16228997 : Blo 2135435 16228997 := bstep (se 4 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 16228997 = 3042937) B3042937
theorem B10819331 : Blo 2135435 10819331 := bstep (se 1 (by rfl) ⟨8114498, by rfl⟩ : syracuseStep 10819331 = 16228997) B16228997
theorem B7212887 : Blo 2135435 7212887 := bstep (se 1 (by rfl) ⟨5409665, by rfl⟩ : syracuseStep 7212887 = 10819331) B10819331
theorem B4808591 : Blo 2135435 4808591 := bstep (se 1 (by rfl) ⟨3606443, by rfl⟩ : syracuseStep 4808591 = 7212887) B7212887
theorem B3205727 : Blo 2135435 3205727 := bstep (se 1 (by rfl) ⟨2404295, by rfl⟩ : syracuseStep 3205727 = 4808591) B4808591
theorem B2137151 : Blo 2135435 2137151 := bstep (se 1 (by rfl) ⟨1602863, by rfl⟩ : syracuseStep 2137151 = 3205727) B3205727
theorem B3205733 : Blo 2135435 3205733 := bbase (se 4 (by rfl) ⟨300537, by rfl⟩ : syracuseStep 3205733 = 601075) (by norm_num)
theorem B2137155 : Blo 2135435 2137155 := bstep (se 1 (by rfl) ⟨1602866, by rfl⟩ : syracuseStep 2137155 = 3205733) B3205733
theorem B3042949 : Blo 2135435 3042949 := bbase (se 4 (by rfl) ⟨285276, by rfl⟩ : syracuseStep 3042949 = 570553) (by norm_num)
theorem B4057265 : Blo 2135435 4057265 := bstep (se 2 (by rfl) ⟨1521474, by rfl⟩ : syracuseStep 4057265 = 3042949) B3042949
theorem B2704843 : Blo 2135435 2704843 := bstep (se 1 (by rfl) ⟨2028632, by rfl⟩ : syracuseStep 2704843 = 4057265) B4057265
theorem B3606457 : Blo 2135435 3606457 := bstep (se 2 (by rfl) ⟨1352421, by rfl⟩ : syracuseStep 3606457 = 2704843) B2704843
theorem B4808609 : Blo 2135435 4808609 := bstep (se 2 (by rfl) ⟨1803228, by rfl⟩ : syracuseStep 4808609 = 3606457) B3606457
theorem B3205739 : Blo 2135435 3205739 := bstep (se 1 (by rfl) ⟨2404304, by rfl⟩ : syracuseStep 3205739 = 4808609) B4808609
theorem B2137159 : Blo 2135435 2137159 := bstep (se 1 (by rfl) ⟨1602869, by rfl⟩ : syracuseStep 2137159 = 3205739) B3205739
theorem B2404309 : Blo 2135435 2404309 := bbase (se 7 (by rfl) ⟨28175, by rfl⟩ : syracuseStep 2404309 = 56351) (by norm_num)
theorem B3205745 : Blo 2135435 3205745 := bstep (se 2 (by rfl) ⟨1202154, by rfl⟩ : syracuseStep 3205745 = 2404309) B2404309
theorem B2137163 : Blo 2135435 2137163 := bstep (se 1 (by rfl) ⟨1602872, by rfl⟩ : syracuseStep 2137163 = 3205745) B3205745
theorem B2704853 : Blo 2135435 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B7212941 : Blo 2135435 7212941 := bstep (se 3 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 7212941 = 2704853) B2704853
theorem B4808627 : Blo 2135435 4808627 := bstep (se 1 (by rfl) ⟨3606470, by rfl⟩ : syracuseStep 4808627 = 7212941) B7212941
theorem B3205751 : Blo 2135435 3205751 := bstep (se 1 (by rfl) ⟨2404313, by rfl⟩ : syracuseStep 3205751 = 4808627) B4808627
theorem B2137167 : Blo 2135435 2137167 := bstep (se 1 (by rfl) ⟨1602875, by rfl⟩ : syracuseStep 2137167 = 3205751) B3205751
theorem B3205757 : Blo 2135435 3205757 := bbase (se 3 (by rfl) ⟨601079, by rfl⟩ : syracuseStep 3205757 = 1202159) (by norm_num)
theorem B2137171 : Blo 2135435 2137171 := bstep (se 1 (by rfl) ⟨1602878, by rfl⟩ : syracuseStep 2137171 = 3205757) B3205757
theorem B4808645 : Blo 2135435 4808645 := bbase (se 4 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 4808645 = 901621) (by norm_num)
theorem B3205763 : Blo 2135435 3205763 := bstep (se 1 (by rfl) ⟨2404322, by rfl⟩ : syracuseStep 3205763 = 4808645) B4808645
theorem B2137175 : Blo 2135435 2137175 := bstep (se 1 (by rfl) ⟨1602881, by rfl⟩ : syracuseStep 2137175 = 3205763) B3205763
theorem B9128933 : Blo 2135435 9128933 := bbase (se 4 (by rfl) ⟨855837, by rfl⟩ : syracuseStep 9128933 = 1711675) (by norm_num)
theorem B6085955 : Blo 2135435 6085955 := bstep (se 1 (by rfl) ⟨4564466, by rfl⟩ : syracuseStep 6085955 = 9128933) B9128933
theorem B4057303 : Blo 2135435 4057303 := bstep (se 1 (by rfl) ⟨3042977, by rfl⟩ : syracuseStep 4057303 = 6085955) B6085955
theorem B5409737 : Blo 2135435 5409737 := bstep (se 2 (by rfl) ⟨2028651, by rfl⟩ : syracuseStep 5409737 = 4057303) B4057303
theorem B3606491 : Blo 2135435 3606491 := bstep (se 1 (by rfl) ⟨2704868, by rfl⟩ : syracuseStep 3606491 = 5409737) B5409737
theorem B2404327 : Blo 2135435 2404327 := bstep (se 1 (by rfl) ⟨1803245, by rfl⟩ : syracuseStep 2404327 = 3606491) B3606491
theorem B3205769 : Blo 2135435 3205769 := bstep (se 2 (by rfl) ⟨1202163, by rfl⟩ : syracuseStep 3205769 = 2404327) B2404327
theorem B2137179 : Blo 2135435 2137179 := bstep (se 1 (by rfl) ⟨1602884, by rfl⟩ : syracuseStep 2137179 = 3205769) B3205769
theorem B10819493 : Blo 2135435 10819493 := bbase (se 4 (by rfl) ⟨1014327, by rfl⟩ : syracuseStep 10819493 = 2028655) (by norm_num)
theorem B7212995 : Blo 2135435 7212995 := bstep (se 1 (by rfl) ⟨5409746, by rfl⟩ : syracuseStep 7212995 = 10819493) B10819493
theorem B4808663 : Blo 2135435 4808663 := bstep (se 1 (by rfl) ⟨3606497, by rfl⟩ : syracuseStep 4808663 = 7212995) B7212995
theorem B3205775 : Blo 2135435 3205775 := bstep (se 1 (by rfl) ⟨2404331, by rfl⟩ : syracuseStep 3205775 = 4808663) B4808663
theorem B2137183 : Blo 2135435 2137183 := bstep (se 1 (by rfl) ⟨1602887, by rfl⟩ : syracuseStep 2137183 = 3205775) B3205775
theorem B3205781 : Blo 2135435 3205781 := bbase (se 6 (by rfl) ⟨75135, by rfl⟩ : syracuseStep 3205781 = 150271) (by norm_num)
theorem B2137187 : Blo 2135435 2137187 := bstep (se 1 (by rfl) ⟨1602890, by rfl⟩ : syracuseStep 2137187 = 3205781) B3205781
theorem B20540213 : Blo 2135435 20540213 := bbase (se 5 (by rfl) ⟨962822, by rfl⟩ : syracuseStep 20540213 = 1925645) (by norm_num)
theorem B13693475 : Blo 2135435 13693475 := bstep (se 1 (by rfl) ⟨10270106, by rfl⟩ : syracuseStep 13693475 = 20540213) B20540213
theorem B9128983 : Blo 2135435 9128983 := bstep (se 1 (by rfl) ⟨6846737, by rfl⟩ : syracuseStep 9128983 = 13693475) B13693475
theorem B12171977 : Blo 2135435 12171977 := bstep (se 2 (by rfl) ⟨4564491, by rfl⟩ : syracuseStep 12171977 = 9128983) B9128983
theorem B8114651 : Blo 2135435 8114651 := bstep (se 1 (by rfl) ⟨6085988, by rfl⟩ : syracuseStep 8114651 = 12171977) B12171977
theorem B5409767 : Blo 2135435 5409767 := bstep (se 1 (by rfl) ⟨4057325, by rfl⟩ : syracuseStep 5409767 = 8114651) B8114651
theorem B3606511 : Blo 2135435 3606511 := bstep (se 1 (by rfl) ⟨2704883, by rfl⟩ : syracuseStep 3606511 = 5409767) B5409767
theorem B4808681 : Blo 2135435 4808681 := bstep (se 2 (by rfl) ⟨1803255, by rfl⟩ : syracuseStep 4808681 = 3606511) B3606511
theorem B3205787 : Blo 2135435 3205787 := bstep (se 1 (by rfl) ⟨2404340, by rfl⟩ : syracuseStep 3205787 = 4808681) B4808681
theorem B2137191 : Blo 2135435 2137191 := bstep (se 1 (by rfl) ⟨1602893, by rfl⟩ : syracuseStep 2137191 = 3205787) B3205787
theorem B2404345 : Blo 2135435 2404345 := bbase (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) (by norm_num)
theorem B3205793 : Blo 2135435 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B2137195 : Blo 2135435 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B4874309 : Blo 2135435 4874309 := bbase (se 4 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 4874309 = 913933) (by norm_num)
theorem B3249539 : Blo 2135435 3249539 := bstep (se 1 (by rfl) ⟨2437154, by rfl⟩ : syracuseStep 3249539 = 4874309) B4874309
theorem B2166359 : Blo 2135435 2166359 := bstep (se 1 (by rfl) ⟨1624769, by rfl⟩ : syracuseStep 2166359 = 3249539) B3249539
theorem B5776957 : Blo 2135435 5776957 := bstep (se 3 (by rfl) ⟨1083179, by rfl⟩ : syracuseStep 5776957 = 2166359) B2166359
theorem B7702609 : Blo 2135435 7702609 := bstep (se 2 (by rfl) ⟨2888478, by rfl⟩ : syracuseStep 7702609 = 5776957) B5776957
theorem B10270145 : Blo 2135435 10270145 := bstep (se 2 (by rfl) ⟨3851304, by rfl⟩ : syracuseStep 10270145 = 7702609) B7702609
theorem B6846763 : Blo 2135435 6846763 := bstep (se 1 (by rfl) ⟨5135072, by rfl⟩ : syracuseStep 6846763 = 10270145) B10270145
theorem B9129017 : Blo 2135435 9129017 := bstep (se 2 (by rfl) ⟨3423381, by rfl⟩ : syracuseStep 9129017 = 6846763) B6846763
theorem B6086011 : Blo 2135435 6086011 := bstep (se 1 (by rfl) ⟨4564508, by rfl⟩ : syracuseStep 6086011 = 9129017) B9129017
theorem B8114681 : Blo 2135435 8114681 := bstep (se 2 (by rfl) ⟨3043005, by rfl⟩ : syracuseStep 8114681 = 6086011) B6086011
theorem B5409787 : Blo 2135435 5409787 := bstep (se 1 (by rfl) ⟨4057340, by rfl⟩ : syracuseStep 5409787 = 8114681) B8114681
theorem B7213049 : Blo 2135435 7213049 := bstep (se 2 (by rfl) ⟨2704893, by rfl⟩ : syracuseStep 7213049 = 5409787) B5409787
theorem B4808699 : Blo 2135435 4808699 := bstep (se 1 (by rfl) ⟨3606524, by rfl⟩ : syracuseStep 4808699 = 7213049) B7213049
theorem B3205799 : Blo 2135435 3205799 := bstep (se 1 (by rfl) ⟨2404349, by rfl⟩ : syracuseStep 3205799 = 4808699) B4808699
theorem B2137199 : Blo 2135435 2137199 := bstep (se 1 (by rfl) ⟨1602899, by rfl⟩ : syracuseStep 2137199 = 3205799) B3205799
theorem B3205805 : Blo 2135435 3205805 := bbase (se 3 (by rfl) ⟨601088, by rfl⟩ : syracuseStep 3205805 = 1202177) (by norm_num)
theorem B2137203 : Blo 2135435 2137203 := bstep (se 1 (by rfl) ⟨1602902, by rfl⟩ : syracuseStep 2137203 = 3205805) B3205805
theorem B4808717 : Blo 2135435 4808717 := bbase (se 3 (by rfl) ⟨901634, by rfl⟩ : syracuseStep 4808717 = 1803269) (by norm_num)
theorem B3205811 : Blo 2135435 3205811 := bstep (se 1 (by rfl) ⟨2404358, by rfl⟩ : syracuseStep 3205811 = 4808717) B4808717
theorem B2137207 : Blo 2135435 2137207 := bstep (se 1 (by rfl) ⟨1602905, by rfl⟩ : syracuseStep 2137207 = 3205811) B3205811
theorem B2704909 : Blo 2135435 2704909 := bbase (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) (by norm_num)
theorem B3606545 : Blo 2135435 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B2404363 : Blo 2135435 2404363 := bstep (se 1 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 2404363 = 3606545) B3606545
theorem B3205817 : Blo 2135435 3205817 := bstep (se 2 (by rfl) ⟨1202181, by rfl⟩ : syracuseStep 3205817 = 2404363) B2404363
theorem B2137211 : Blo 2135435 2137211 := bstep (se 1 (by rfl) ⟨1602908, by rfl⟩ : syracuseStep 2137211 = 3205817) B3205817
theorem B2927909 : Blo 2135435 2927909 := bbase (se 4 (by rfl) ⟨274491, by rfl⟩ : syracuseStep 2927909 = 548983) (by norm_num)
theorem B7807757 : Blo 2135435 7807757 := bstep (se 3 (by rfl) ⟨1463954, by rfl⟩ : syracuseStep 7807757 = 2927909) B2927909
theorem B20820685 : Blo 2135435 20820685 := bstep (se 3 (by rfl) ⟨3903878, by rfl⟩ : syracuseStep 20820685 = 7807757) B7807757
theorem B27760913 : Blo 2135435 27760913 := bstep (se 2 (by rfl) ⟨10410342, by rfl⟩ : syracuseStep 27760913 = 20820685) B20820685
theorem B18507275 : Blo 2135435 18507275 := bstep (se 1 (by rfl) ⟨13880456, by rfl⟩ : syracuseStep 18507275 = 27760913) B27760913
theorem B12338183 : Blo 2135435 12338183 := bstep (se 1 (by rfl) ⟨9253637, by rfl⟩ : syracuseStep 12338183 = 18507275) B18507275
theorem B32901821 : Blo 2135435 32901821 := bstep (se 3 (by rfl) ⟨6169091, by rfl⟩ : syracuseStep 32901821 = 12338183) B12338183
theorem B21934547 : Blo 2135435 21934547 := bstep (se 1 (by rfl) ⟨16450910, by rfl⟩ : syracuseStep 21934547 = 32901821) B32901821
theorem B14623031 : Blo 2135435 14623031 := bstep (se 1 (by rfl) ⟨10967273, by rfl⟩ : syracuseStep 14623031 = 21934547) B21934547
theorem B9748687 : Blo 2135435 9748687 := bstep (se 1 (by rfl) ⟨7311515, by rfl⟩ : syracuseStep 9748687 = 14623031) B14623031
theorem B12998249 : Blo 2135435 12998249 := bstep (se 2 (by rfl) ⟨4874343, by rfl⟩ : syracuseStep 12998249 = 9748687) B9748687
theorem B8665499 : Blo 2135435 8665499 := bstep (se 1 (by rfl) ⟨6499124, by rfl⟩ : syracuseStep 8665499 = 12998249) B12998249
theorem B23107997 : Blo 2135435 23107997 := bstep (se 3 (by rfl) ⟨4332749, by rfl⟩ : syracuseStep 23107997 = 8665499) B8665499
theorem B15405331 : Blo 2135435 15405331 := bstep (se 1 (by rfl) ⟨11553998, by rfl⟩ : syracuseStep 15405331 = 23107997) B23107997
theorem B20540441 : Blo 2135435 20540441 := bstep (se 2 (by rfl) ⟨7702665, by rfl⟩ : syracuseStep 20540441 = 15405331) B15405331
theorem B13693627 : Blo 2135435 13693627 := bstep (se 1 (by rfl) ⟨10270220, by rfl⟩ : syracuseStep 13693627 = 20540441) B20540441
theorem B18258169 : Blo 2135435 18258169 := bstep (se 2 (by rfl) ⟨6846813, by rfl⟩ : syracuseStep 18258169 = 13693627) B13693627
theorem B24344225 : Blo 2135435 24344225 := bstep (se 2 (by rfl) ⟨9129084, by rfl⟩ : syracuseStep 24344225 = 18258169) B18258169
theorem B16229483 : Blo 2135435 16229483 := bstep (se 1 (by rfl) ⟨12172112, by rfl⟩ : syracuseStep 16229483 = 24344225) B24344225
theorem B10819655 : Blo 2135435 10819655 := bstep (se 1 (by rfl) ⟨8114741, by rfl⟩ : syracuseStep 10819655 = 16229483) B16229483
theorem B7213103 : Blo 2135435 7213103 := bstep (se 1 (by rfl) ⟨5409827, by rfl⟩ : syracuseStep 7213103 = 10819655) B10819655
theorem B4808735 : Blo 2135435 4808735 := bstep (se 1 (by rfl) ⟨3606551, by rfl⟩ : syracuseStep 4808735 = 7213103) B7213103
theorem B3205823 : Blo 2135435 3205823 := bstep (se 1 (by rfl) ⟨2404367, by rfl⟩ : syracuseStep 3205823 = 4808735) B4808735
theorem B2137215 : Blo 2135435 2137215 := bstep (se 1 (by rfl) ⟨1602911, by rfl⟩ : syracuseStep 2137215 = 3205823) B3205823
theorem B3205829 : Blo 2135435 3205829 := bbase (se 4 (by rfl) ⟨300546, by rfl⟩ : syracuseStep 3205829 = 601093) (by norm_num)
theorem B2137219 : Blo 2135435 2137219 := bstep (se 1 (by rfl) ⟨1602914, by rfl⟩ : syracuseStep 2137219 = 3205829) B3205829
theorem B3606565 : Blo 2135435 3606565 := bbase (se 4 (by rfl) ⟨338115, by rfl⟩ : syracuseStep 3606565 = 676231) (by norm_num)
theorem B4808753 : Blo 2135435 4808753 := bstep (se 2 (by rfl) ⟨1803282, by rfl⟩ : syracuseStep 4808753 = 3606565) B3606565
theorem B3205835 : Blo 2135435 3205835 := bstep (se 1 (by rfl) ⟨2404376, by rfl⟩ : syracuseStep 3205835 = 4808753) B4808753
theorem B2137223 : Blo 2135435 2137223 := bstep (se 1 (by rfl) ⟨1602917, by rfl⟩ : syracuseStep 2137223 = 3205835) B3205835
theorem B2404381 : Blo 2135435 2404381 := bbase (se 3 (by rfl) ⟨450821, by rfl⟩ : syracuseStep 2404381 = 901643) (by norm_num)
theorem B3205841 : Blo 2135435 3205841 := bstep (se 2 (by rfl) ⟨1202190, by rfl⟩ : syracuseStep 3205841 = 2404381) B2404381
theorem B2137227 : Blo 2135435 2137227 := bstep (se 1 (by rfl) ⟨1602920, by rfl⟩ : syracuseStep 2137227 = 3205841) B3205841
theorem B7213157 : Blo 2135435 7213157 := bbase (se 4 (by rfl) ⟨676233, by rfl⟩ : syracuseStep 7213157 = 1352467) (by norm_num)
theorem B4808771 : Blo 2135435 4808771 := bstep (se 1 (by rfl) ⟨3606578, by rfl⟩ : syracuseStep 4808771 = 7213157) B7213157
theorem B3205847 : Blo 2135435 3205847 := bstep (se 1 (by rfl) ⟨2404385, by rfl⟩ : syracuseStep 3205847 = 4808771) B4808771
theorem B2137231 : Blo 2135435 2137231 := bstep (se 1 (by rfl) ⟨1602923, by rfl⟩ : syracuseStep 2137231 = 3205847) B3205847
theorem B3205853 : Blo 2135435 3205853 := bbase (se 3 (by rfl) ⟨601097, by rfl⟩ : syracuseStep 3205853 = 1202195) (by norm_num)
theorem B2137235 : Blo 2135435 2137235 := bstep (se 1 (by rfl) ⟨1602926, by rfl⟩ : syracuseStep 2137235 = 3205853) B3205853
theorem B4808789 : Blo 2135435 4808789 := bbase (se 8 (by rfl) ⟨28176, by rfl⟩ : syracuseStep 4808789 = 56353) (by norm_num)
theorem B3205859 : Blo 2135435 3205859 := bstep (se 1 (by rfl) ⟨2404394, by rfl⟩ : syracuseStep 3205859 = 4808789) B4808789
theorem B2137239 : Blo 2135435 2137239 := bstep (se 1 (by rfl) ⟨1602929, by rfl⟩ : syracuseStep 2137239 = 3205859) B3205859
theorem B5777077 : Blo 2135435 5777077 := bbase (se 5 (by rfl) ⟨270800, by rfl⟩ : syracuseStep 5777077 = 541601) (by norm_num)
theorem B7702769 : Blo 2135435 7702769 := bstep (se 2 (by rfl) ⟨2888538, by rfl⟩ : syracuseStep 7702769 = 5777077) B5777077
theorem B5135179 : Blo 2135435 5135179 := bstep (se 1 (by rfl) ⟨3851384, by rfl⟩ : syracuseStep 5135179 = 7702769) B7702769
theorem B6846905 : Blo 2135435 6846905 := bstep (se 2 (by rfl) ⟨2567589, by rfl⟩ : syracuseStep 6846905 = 5135179) B5135179
theorem B4564603 : Blo 2135435 4564603 := bstep (se 1 (by rfl) ⟨3423452, by rfl⟩ : syracuseStep 4564603 = 6846905) B6846905
theorem B6086137 : Blo 2135435 6086137 := bstep (se 2 (by rfl) ⟨2282301, by rfl⟩ : syracuseStep 6086137 = 4564603) B4564603
theorem B8114849 : Blo 2135435 8114849 := bstep (se 2 (by rfl) ⟨3043068, by rfl⟩ : syracuseStep 8114849 = 6086137) B6086137
theorem B5409899 : Blo 2135435 5409899 := bstep (se 1 (by rfl) ⟨4057424, by rfl⟩ : syracuseStep 5409899 = 8114849) B8114849
theorem B3606599 : Blo 2135435 3606599 := bstep (se 1 (by rfl) ⟨2704949, by rfl⟩ : syracuseStep 3606599 = 5409899) B5409899
theorem B2404399 : Blo 2135435 2404399 := bstep (se 1 (by rfl) ⟨1803299, by rfl⟩ : syracuseStep 2404399 = 3606599) B3606599
theorem B3205865 : Blo 2135435 3205865 := bstep (se 2 (by rfl) ⟨1202199, by rfl⟩ : syracuseStep 3205865 = 2404399) B2404399
theorem B2137243 : Blo 2135435 2137243 := bstep (se 1 (by rfl) ⟨1602932, by rfl⟩ : syracuseStep 2137243 = 3205865) B3205865
theorem B14623253 : Blo 2135435 14623253 := bbase (se 6 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 14623253 = 685465) (by norm_num)
theorem B9748835 : Blo 2135435 9748835 := bstep (se 1 (by rfl) ⟨7311626, by rfl⟩ : syracuseStep 9748835 = 14623253) B14623253
theorem B6499223 : Blo 2135435 6499223 := bstep (se 1 (by rfl) ⟨4874417, by rfl⟩ : syracuseStep 6499223 = 9748835) B9748835
theorem B4332815 : Blo 2135435 4332815 := bstep (se 1 (by rfl) ⟨3249611, by rfl⟩ : syracuseStep 4332815 = 6499223) B6499223
theorem B2888543 : Blo 2135435 2888543 := bstep (se 1 (by rfl) ⟨2166407, by rfl⟩ : syracuseStep 2888543 = 4332815) B4332815
theorem B7702781 : Blo 2135435 7702781 := bstep (se 3 (by rfl) ⟨1444271, by rfl⟩ : syracuseStep 7702781 = 2888543) B2888543
theorem B20540749 : Blo 2135435 20540749 := bstep (se 3 (by rfl) ⟨3851390, by rfl⟩ : syracuseStep 20540749 = 7702781) B7702781
theorem B27387665 : Blo 2135435 27387665 := bstep (se 2 (by rfl) ⟨10270374, by rfl⟩ : syracuseStep 27387665 = 20540749) B20540749
theorem B18258443 : Blo 2135435 18258443 := bstep (se 1 (by rfl) ⟨13693832, by rfl⟩ : syracuseStep 18258443 = 27387665) B27387665
theorem B12172295 : Blo 2135435 12172295 := bstep (se 1 (by rfl) ⟨9129221, by rfl⟩ : syracuseStep 12172295 = 18258443) B18258443
theorem B8114863 : Blo 2135435 8114863 := bstep (se 1 (by rfl) ⟨6086147, by rfl⟩ : syracuseStep 8114863 = 12172295) B12172295
theorem B10819817 : Blo 2135435 10819817 := bstep (se 2 (by rfl) ⟨4057431, by rfl⟩ : syracuseStep 10819817 = 8114863) B8114863
theorem B7213211 : Blo 2135435 7213211 := bstep (se 1 (by rfl) ⟨5409908, by rfl⟩ : syracuseStep 7213211 = 10819817) B10819817
theorem B4808807 : Blo 2135435 4808807 := bstep (se 1 (by rfl) ⟨3606605, by rfl⟩ : syracuseStep 4808807 = 7213211) B7213211
theorem B3205871 : Blo 2135435 3205871 := bstep (se 1 (by rfl) ⟨2404403, by rfl⟩ : syracuseStep 3205871 = 4808807) B4808807
theorem B2137247 : Blo 2135435 2137247 := bstep (se 1 (by rfl) ⟨1602935, by rfl⟩ : syracuseStep 2137247 = 3205871) B3205871
theorem B3205877 : Blo 2135435 3205877 := bbase (se 5 (by rfl) ⟨150275, by rfl⟩ : syracuseStep 3205877 = 300551) (by norm_num)
theorem B2137251 : Blo 2135435 2137251 := bstep (se 1 (by rfl) ⟨1602938, by rfl⟩ : syracuseStep 2137251 = 3205877) B3205877
theorem B65804885 : Blo 2135435 65804885 := bbase (se 8 (by rfl) ⟨385575, by rfl⟩ : syracuseStep 65804885 = 771151) (by norm_num)
theorem B43869923 : Blo 2135435 43869923 := bstep (se 1 (by rfl) ⟨32902442, by rfl⟩ : syracuseStep 43869923 = 65804885) B65804885
theorem B29246615 : Blo 2135435 29246615 := bstep (se 1 (by rfl) ⟨21934961, by rfl⟩ : syracuseStep 29246615 = 43869923) B43869923
theorem B19497743 : Blo 2135435 19497743 := bstep (se 1 (by rfl) ⟨14623307, by rfl⟩ : syracuseStep 19497743 = 29246615) B29246615
theorem B12998495 : Blo 2135435 12998495 := bstep (se 1 (by rfl) ⟨9748871, by rfl⟩ : syracuseStep 12998495 = 19497743) B19497743
theorem B34662653 : Blo 2135435 34662653 := bstep (se 3 (by rfl) ⟨6499247, by rfl⟩ : syracuseStep 34662653 = 12998495) B12998495
theorem B23108435 : Blo 2135435 23108435 := bstep (se 1 (by rfl) ⟨17331326, by rfl⟩ : syracuseStep 23108435 = 34662653) B34662653
theorem B15405623 : Blo 2135435 15405623 := bstep (se 1 (by rfl) ⟨11554217, by rfl⟩ : syracuseStep 15405623 = 23108435) B23108435
theorem B10270415 : Blo 2135435 10270415 := bstep (se 1 (by rfl) ⟨7702811, by rfl⟩ : syracuseStep 10270415 = 15405623) B15405623
theorem B6846943 : Blo 2135435 6846943 := bstep (se 1 (by rfl) ⟨5135207, by rfl⟩ : syracuseStep 6846943 = 10270415) B10270415
theorem B9129257 : Blo 2135435 9129257 := bstep (se 2 (by rfl) ⟨3423471, by rfl⟩ : syracuseStep 9129257 = 6846943) B6846943
theorem B6086171 : Blo 2135435 6086171 := bstep (se 1 (by rfl) ⟨4564628, by rfl⟩ : syracuseStep 6086171 = 9129257) B9129257
theorem B4057447 : Blo 2135435 4057447 := bstep (se 1 (by rfl) ⟨3043085, by rfl⟩ : syracuseStep 4057447 = 6086171) B6086171
theorem B5409929 : Blo 2135435 5409929 := bstep (se 2 (by rfl) ⟨2028723, by rfl⟩ : syracuseStep 5409929 = 4057447) B4057447
theorem B3606619 : Blo 2135435 3606619 := bstep (se 1 (by rfl) ⟨2704964, by rfl⟩ : syracuseStep 3606619 = 5409929) B5409929
theorem B4808825 : Blo 2135435 4808825 := bstep (se 2 (by rfl) ⟨1803309, by rfl⟩ : syracuseStep 4808825 = 3606619) B3606619
theorem B3205883 : Blo 2135435 3205883 := bstep (se 1 (by rfl) ⟨2404412, by rfl⟩ : syracuseStep 3205883 = 4808825) B4808825
theorem B2137255 : Blo 2135435 2137255 := bstep (se 1 (by rfl) ⟨1602941, by rfl⟩ : syracuseStep 2137255 = 3205883) B3205883
theorem B2404417 : Blo 2135435 2404417 := bbase (se 2 (by rfl) ⟨901656, by rfl⟩ : syracuseStep 2404417 = 1803313) (by norm_num)
theorem B3205889 : Blo 2135435 3205889 := bstep (se 2 (by rfl) ⟨1202208, by rfl⟩ : syracuseStep 3205889 = 2404417) B2404417
theorem B2137259 : Blo 2135435 2137259 := bstep (se 1 (by rfl) ⟨1602944, by rfl⟩ : syracuseStep 2137259 = 3205889) B3205889
theorem B5409949 : Blo 2135435 5409949 := bbase (se 3 (by rfl) ⟨1014365, by rfl⟩ : syracuseStep 5409949 = 2028731) (by norm_num)
theorem B7213265 : Blo 2135435 7213265 := bstep (se 2 (by rfl) ⟨2704974, by rfl⟩ : syracuseStep 7213265 = 5409949) B5409949
theorem B4808843 : Blo 2135435 4808843 := bstep (se 1 (by rfl) ⟨3606632, by rfl⟩ : syracuseStep 4808843 = 7213265) B7213265
theorem B3205895 : Blo 2135435 3205895 := bstep (se 1 (by rfl) ⟨2404421, by rfl⟩ : syracuseStep 3205895 = 4808843) B4808843
theorem B2137263 : Blo 2135435 2137263 := bstep (se 1 (by rfl) ⟨1602947, by rfl⟩ : syracuseStep 2137263 = 3205895) B3205895
theorem B3205901 : Blo 2135435 3205901 := bbase (se 3 (by rfl) ⟨601106, by rfl⟩ : syracuseStep 3205901 = 1202213) (by norm_num)
theorem B2137267 : Blo 2135435 2137267 := bstep (se 1 (by rfl) ⟨1602950, by rfl⟩ : syracuseStep 2137267 = 3205901) B3205901
theorem B4808861 : Blo 2135435 4808861 := bbase (se 3 (by rfl) ⟨901661, by rfl⟩ : syracuseStep 4808861 = 1803323) (by norm_num)
theorem B3205907 : Blo 2135435 3205907 := bstep (se 1 (by rfl) ⟨2404430, by rfl⟩ : syracuseStep 3205907 = 4808861) B4808861
theorem B2137271 : Blo 2135435 2137271 := bstep (se 1 (by rfl) ⟨1602953, by rfl⟩ : syracuseStep 2137271 = 3205907) B3205907
theorem B3606653 : Blo 2135435 3606653 := bbase (se 3 (by rfl) ⟨676247, by rfl⟩ : syracuseStep 3606653 = 1352495) (by norm_num)
theorem B2404435 : Blo 2135435 2404435 := bstep (se 1 (by rfl) ⟨1803326, by rfl⟩ : syracuseStep 2404435 = 3606653) B3606653
theorem B3205913 : Blo 2135435 3205913 := bstep (se 2 (by rfl) ⟨1202217, by rfl⟩ : syracuseStep 3205913 = 2404435) B2404435
theorem B2137275 : Blo 2135435 2137275 := bstep (se 1 (by rfl) ⟨1602956, by rfl⟩ : syracuseStep 2137275 = 3205913) B3205913
theorem B5777173 : Blo 2135435 5777173 := bbase (se 6 (by rfl) ⟨135402, by rfl⟩ : syracuseStep 5777173 = 270805) (by norm_num)
theorem B7702897 : Blo 2135435 7702897 := bstep (se 2 (by rfl) ⟨2888586, by rfl⟩ : syracuseStep 7702897 = 5777173) B5777173
theorem B10270529 : Blo 2135435 10270529 := bstep (se 2 (by rfl) ⟨3851448, by rfl⟩ : syracuseStep 10270529 = 7702897) B7702897
theorem B6847019 : Blo 2135435 6847019 := bstep (se 1 (by rfl) ⟨5135264, by rfl⟩ : syracuseStep 6847019 = 10270529) B10270529
theorem B4564679 : Blo 2135435 4564679 := bstep (se 1 (by rfl) ⟨3423509, by rfl⟩ : syracuseStep 4564679 = 6847019) B6847019
theorem B12172477 : Blo 2135435 12172477 := bstep (se 3 (by rfl) ⟨2282339, by rfl⟩ : syracuseStep 12172477 = 4564679) B4564679
theorem B16229969 : Blo 2135435 16229969 := bstep (se 2 (by rfl) ⟨6086238, by rfl⟩ : syracuseStep 16229969 = 12172477) B12172477
theorem B10819979 : Blo 2135435 10819979 := bstep (se 1 (by rfl) ⟨8114984, by rfl⟩ : syracuseStep 10819979 = 16229969) B16229969
theorem B7213319 : Blo 2135435 7213319 := bstep (se 1 (by rfl) ⟨5409989, by rfl⟩ : syracuseStep 7213319 = 10819979) B10819979
theorem B4808879 : Blo 2135435 4808879 := bstep (se 1 (by rfl) ⟨3606659, by rfl⟩ : syracuseStep 4808879 = 7213319) B7213319
theorem B3205919 : Blo 2135435 3205919 := bstep (se 1 (by rfl) ⟨2404439, by rfl⟩ : syracuseStep 3205919 = 4808879) B4808879
theorem B2137279 : Blo 2135435 2137279 := bstep (se 1 (by rfl) ⟨1602959, by rfl⟩ : syracuseStep 2137279 = 3205919) B3205919
theorem B3205925 : Blo 2135435 3205925 := bbase (se 4 (by rfl) ⟨300555, by rfl⟩ : syracuseStep 3205925 = 601111) (by norm_num)
theorem B2137283 : Blo 2135435 2137283 := bstep (se 1 (by rfl) ⟨1602962, by rfl⟩ : syracuseStep 2137283 = 3205925) B3205925
theorem B2705005 : Blo 2135435 2705005 := bbase (se 3 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 2705005 = 1014377) (by norm_num)
theorem B3606673 : Blo 2135435 3606673 := bstep (se 2 (by rfl) ⟨1352502, by rfl⟩ : syracuseStep 3606673 = 2705005) B2705005
theorem B4808897 : Blo 2135435 4808897 := bstep (se 2 (by rfl) ⟨1803336, by rfl⟩ : syracuseStep 4808897 = 3606673) B3606673
theorem B3205931 : Blo 2135435 3205931 := bstep (se 1 (by rfl) ⟨2404448, by rfl⟩ : syracuseStep 3205931 = 4808897) B4808897
theorem B2137287 : Blo 2135435 2137287 := bstep (se 1 (by rfl) ⟨1602965, by rfl⟩ : syracuseStep 2137287 = 3205931) B3205931
theorem B2404453 : Blo 2135435 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B3205937 : Blo 2135435 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B2137291 : Blo 2135435 2137291 := bstep (se 1 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 2137291 = 3205937) B3205937
theorem B2282357 : Blo 2135435 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B6086285 : Blo 2135435 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B4057523 : Blo 2135435 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B2705015 : Blo 2135435 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B7213373 : Blo 2135435 7213373 := bstep (se 3 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 7213373 = 2705015) B2705015
theorem B4808915 : Blo 2135435 4808915 := bstep (se 1 (by rfl) ⟨3606686, by rfl⟩ : syracuseStep 4808915 = 7213373) B7213373
theorem B3205943 : Blo 2135435 3205943 := bstep (se 1 (by rfl) ⟨2404457, by rfl⟩ : syracuseStep 3205943 = 4808915) B4808915
theorem B2137295 : Blo 2135435 2137295 := bstep (se 1 (by rfl) ⟨1602971, by rfl⟩ : syracuseStep 2137295 = 3205943) B3205943
theorem B3205949 : Blo 2135435 3205949 := bbase (se 3 (by rfl) ⟨601115, by rfl⟩ : syracuseStep 3205949 = 1202231) (by norm_num)
theorem B2137299 : Blo 2135435 2137299 := bstep (se 1 (by rfl) ⟨1602974, by rfl⟩ : syracuseStep 2137299 = 3205949) B3205949
theorem B4808933 : Blo 2135435 4808933 := bbase (se 4 (by rfl) ⟨450837, by rfl⟩ : syracuseStep 4808933 = 901675) (by norm_num)
theorem B3205955 : Blo 2135435 3205955 := bstep (se 1 (by rfl) ⟨2404466, by rfl⟩ : syracuseStep 3205955 = 4808933) B4808933
theorem B2137303 : Blo 2135435 2137303 := bstep (se 1 (by rfl) ⟨1602977, by rfl⟩ : syracuseStep 2137303 = 3205955) B3205955
theorem B5410061 : Blo 2135435 5410061 := bbase (se 3 (by rfl) ⟨1014386, by rfl⟩ : syracuseStep 5410061 = 2028773) (by norm_num)
theorem B3606707 : Blo 2135435 3606707 := bstep (se 1 (by rfl) ⟨2705030, by rfl⟩ : syracuseStep 3606707 = 5410061) B5410061
theorem B2404471 : Blo 2135435 2404471 := bstep (se 1 (by rfl) ⟨1803353, by rfl⟩ : syracuseStep 2404471 = 3606707) B3606707
theorem B3205961 : Blo 2135435 3205961 := bstep (se 2 (by rfl) ⟨1202235, by rfl⟩ : syracuseStep 3205961 = 2404471) B2404471
theorem B2137307 : Blo 2135435 2137307 := bstep (se 1 (by rfl) ⟨1602980, by rfl⟩ : syracuseStep 2137307 = 3205961) B3205961
theorem B3043165 : Blo 2135435 3043165 := bbase (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) (by norm_num)
theorem B4057553 : Blo 2135435 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B10820141 : Blo 2135435 10820141 := bstep (se 3 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 10820141 = 4057553) B4057553
theorem B7213427 : Blo 2135435 7213427 := bstep (se 1 (by rfl) ⟨5410070, by rfl⟩ : syracuseStep 7213427 = 10820141) B10820141
theorem B4808951 : Blo 2135435 4808951 := bstep (se 1 (by rfl) ⟨3606713, by rfl⟩ : syracuseStep 4808951 = 7213427) B7213427
theorem B3205967 : Blo 2135435 3205967 := bstep (se 1 (by rfl) ⟨2404475, by rfl⟩ : syracuseStep 3205967 = 4808951) B4808951
theorem B2137311 : Blo 2135435 2137311 := bstep (se 1 (by rfl) ⟨1602983, by rfl⟩ : syracuseStep 2137311 = 3205967) B3205967
theorem B3205973 : Blo 2135435 3205973 := bbase (se 9 (by rfl) ⟨9392, by rfl⟩ : syracuseStep 3205973 = 18785) (by norm_num)
theorem B2137315 : Blo 2135435 2137315 := bstep (se 1 (by rfl) ⟨1602986, by rfl⟩ : syracuseStep 2137315 = 3205973) B3205973
theorem B4564765 : Blo 2135435 4564765 := bbase (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) (by norm_num)
theorem B6086353 : Blo 2135435 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B8115137 : Blo 2135435 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B5410091 : Blo 2135435 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B3606727 : Blo 2135435 3606727 := bstep (se 1 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 3606727 = 5410091) B5410091
theorem B4808969 : Blo 2135435 4808969 := bstep (se 2 (by rfl) ⟨1803363, by rfl⟩ : syracuseStep 4808969 = 3606727) B3606727
theorem B3205979 : Blo 2135435 3205979 := bstep (se 1 (by rfl) ⟨2404484, by rfl⟩ : syracuseStep 3205979 = 4808969) B4808969
theorem B2137319 : Blo 2135435 2137319 := bstep (se 1 (by rfl) ⟨1602989, by rfl⟩ : syracuseStep 2137319 = 3205979) B3205979
theorem B2404489 : Blo 2135435 2404489 := bbase (se 2 (by rfl) ⟨901683, by rfl⟩ : syracuseStep 2404489 = 1803367) (by norm_num)
theorem B3205985 : Blo 2135435 3205985 := bstep (se 2 (by rfl) ⟨1202244, by rfl⟩ : syracuseStep 3205985 = 2404489) B2404489
theorem B2137323 : Blo 2135435 2137323 := bstep (se 1 (by rfl) ⟨1602992, by rfl⟩ : syracuseStep 2137323 = 3205985) B3205985
theorem B33352469 : Blo 2135435 33352469 := bbase (se 6 (by rfl) ⟨781698, by rfl⟩ : syracuseStep 33352469 = 1563397) (by norm_num)
theorem B22234979 : Blo 2135435 22234979 := bstep (se 1 (by rfl) ⟨16676234, by rfl⟩ : syracuseStep 22234979 = 33352469) B33352469
theorem B14823319 : Blo 2135435 14823319 := bstep (se 1 (by rfl) ⟨11117489, by rfl⟩ : syracuseStep 14823319 = 22234979) B22234979
theorem B19764425 : Blo 2135435 19764425 := bstep (se 2 (by rfl) ⟨7411659, by rfl⟩ : syracuseStep 19764425 = 14823319) B14823319
theorem B13176283 : Blo 2135435 13176283 := bstep (se 1 (by rfl) ⟨9882212, by rfl⟩ : syracuseStep 13176283 = 19764425) B19764425
theorem B17568377 : Blo 2135435 17568377 := bstep (se 2 (by rfl) ⟨6588141, by rfl⟩ : syracuseStep 17568377 = 13176283) B13176283
theorem B11712251 : Blo 2135435 11712251 := bstep (se 1 (by rfl) ⟨8784188, by rfl⟩ : syracuseStep 11712251 = 17568377) B17568377
theorem B7808167 : Blo 2135435 7808167 := bstep (se 1 (by rfl) ⟨5856125, by rfl⟩ : syracuseStep 7808167 = 11712251) B11712251
theorem B41643557 : Blo 2135435 41643557 := bstep (se 4 (by rfl) ⟨3904083, by rfl⟩ : syracuseStep 41643557 = 7808167) B7808167
theorem B27762371 : Blo 2135435 27762371 := bstep (se 1 (by rfl) ⟨20821778, by rfl⟩ : syracuseStep 27762371 = 41643557) B41643557
theorem B18508247 : Blo 2135435 18508247 := bstep (se 1 (by rfl) ⟨13881185, by rfl⟩ : syracuseStep 18508247 = 27762371) B27762371
theorem B12338831 : Blo 2135435 12338831 := bstep (se 1 (by rfl) ⟨9254123, by rfl⟩ : syracuseStep 12338831 = 18508247) B18508247
theorem B8225887 : Blo 2135435 8225887 := bstep (se 1 (by rfl) ⟨6169415, by rfl⟩ : syracuseStep 8225887 = 12338831) B12338831
theorem B10967849 : Blo 2135435 10967849 := bstep (se 2 (by rfl) ⟨4112943, by rfl⟩ : syracuseStep 10967849 = 8225887) B8225887
theorem B7311899 : Blo 2135435 7311899 := bstep (se 1 (by rfl) ⟨5483924, by rfl⟩ : syracuseStep 7311899 = 10967849) B10967849
theorem B4874599 : Blo 2135435 4874599 := bstep (se 1 (by rfl) ⟨3655949, by rfl⟩ : syracuseStep 4874599 = 7311899) B7311899
theorem B25997861 : Blo 2135435 25997861 := bstep (se 4 (by rfl) ⟨2437299, by rfl⟩ : syracuseStep 25997861 = 4874599) B4874599
theorem B17331907 : Blo 2135435 17331907 := bstep (se 1 (by rfl) ⟨12998930, by rfl⟩ : syracuseStep 17331907 = 25997861) B25997861
theorem B23109209 : Blo 2135435 23109209 := bstep (se 2 (by rfl) ⟨8665953, by rfl⟩ : syracuseStep 23109209 = 17331907) B17331907
theorem B15406139 : Blo 2135435 15406139 := bstep (se 1 (by rfl) ⟨11554604, by rfl⟩ : syracuseStep 15406139 = 23109209) B23109209
theorem B41083037 : Blo 2135435 41083037 := bstep (se 3 (by rfl) ⟨7703069, by rfl⟩ : syracuseStep 41083037 = 15406139) B15406139
theorem B27388691 : Blo 2135435 27388691 := bstep (se 1 (by rfl) ⟨20541518, by rfl⟩ : syracuseStep 27388691 = 41083037) B41083037
theorem B18259127 : Blo 2135435 18259127 := bstep (se 1 (by rfl) ⟨13694345, by rfl⟩ : syracuseStep 18259127 = 27388691) B27388691
theorem B12172751 : Blo 2135435 12172751 := bstep (se 1 (by rfl) ⟨9129563, by rfl⟩ : syracuseStep 12172751 = 18259127) B18259127
theorem B8115167 : Blo 2135435 8115167 := bstep (se 1 (by rfl) ⟨6086375, by rfl⟩ : syracuseStep 8115167 = 12172751) B12172751
theorem B5410111 : Blo 2135435 5410111 := bstep (se 1 (by rfl) ⟨4057583, by rfl⟩ : syracuseStep 5410111 = 8115167) B8115167
theorem B7213481 : Blo 2135435 7213481 := bstep (se 2 (by rfl) ⟨2705055, by rfl⟩ : syracuseStep 7213481 = 5410111) B5410111
theorem B4808987 : Blo 2135435 4808987 := bstep (se 1 (by rfl) ⟨3606740, by rfl⟩ : syracuseStep 4808987 = 7213481) B7213481
theorem B3205991 : Blo 2135435 3205991 := bstep (se 1 (by rfl) ⟨2404493, by rfl⟩ : syracuseStep 3205991 = 4808987) B4808987
theorem B2137327 : Blo 2135435 2137327 := bstep (se 1 (by rfl) ⟨1602995, by rfl⟩ : syracuseStep 2137327 = 3205991) B3205991
theorem B3205997 : Blo 2135435 3205997 := bbase (se 3 (by rfl) ⟨601124, by rfl⟩ : syracuseStep 3205997 = 1202249) (by norm_num)
theorem B2137331 : Blo 2135435 2137331 := bstep (se 1 (by rfl) ⟨1602998, by rfl⟩ : syracuseStep 2137331 = 3205997) B3205997
theorem B4809005 : Blo 2135435 4809005 := bbase (se 3 (by rfl) ⟨901688, by rfl⟩ : syracuseStep 4809005 = 1803377) (by norm_num)
theorem B3206003 : Blo 2135435 3206003 := bstep (se 1 (by rfl) ⟨2404502, by rfl⟩ : syracuseStep 3206003 = 4809005) B4809005
theorem B2137335 : Blo 2135435 2137335 := bstep (se 1 (by rfl) ⟨1603001, by rfl⟩ : syracuseStep 2137335 = 3206003) B3206003
theorem B2567705 : Blo 2135435 2567705 := bbase (se 2 (by rfl) ⟨962889, by rfl⟩ : syracuseStep 2567705 = 1925779) (by norm_num)
theorem B6847213 : Blo 2135435 6847213 := bstep (se 3 (by rfl) ⟨1283852, by rfl⟩ : syracuseStep 6847213 = 2567705) B2567705
theorem B9129617 : Blo 2135435 9129617 := bstep (se 2 (by rfl) ⟨3423606, by rfl⟩ : syracuseStep 9129617 = 6847213) B6847213
theorem B6086411 : Blo 2135435 6086411 := bstep (se 1 (by rfl) ⟨4564808, by rfl⟩ : syracuseStep 6086411 = 9129617) B9129617
theorem B4057607 : Blo 2135435 4057607 := bstep (se 1 (by rfl) ⟨3043205, by rfl⟩ : syracuseStep 4057607 = 6086411) B6086411
theorem B2705071 : Blo 2135435 2705071 := bstep (se 1 (by rfl) ⟨2028803, by rfl⟩ : syracuseStep 2705071 = 4057607) B4057607
theorem B3606761 : Blo 2135435 3606761 := bstep (se 2 (by rfl) ⟨1352535, by rfl⟩ : syracuseStep 3606761 = 2705071) B2705071
theorem B2404507 : Blo 2135435 2404507 := bstep (se 1 (by rfl) ⟨1803380, by rfl⟩ : syracuseStep 2404507 = 3606761) B3606761
theorem B3206009 : Blo 2135435 3206009 := bstep (se 2 (by rfl) ⟨1202253, by rfl⟩ : syracuseStep 3206009 = 2404507) B2404507
theorem B2137339 : Blo 2135435 2137339 := bstep (se 1 (by rfl) ⟨1603004, by rfl⟩ : syracuseStep 2137339 = 3206009) B3206009
theorem B2345113 : Blo 2135435 2345113 := bbase (se 2 (by rfl) ⟨879417, by rfl⟩ : syracuseStep 2345113 = 1758835) (by norm_num)
theorem B3126817 : Blo 2135435 3126817 := bstep (se 2 (by rfl) ⟨1172556, by rfl⟩ : syracuseStep 3126817 = 2345113) B2345113
theorem B4169089 : Blo 2135435 4169089 := bstep (se 2 (by rfl) ⟨1563408, by rfl⟩ : syracuseStep 4169089 = 3126817) B3126817
theorem B22235141 : Blo 2135435 22235141 := bstep (se 4 (by rfl) ⟨2084544, by rfl⟩ : syracuseStep 22235141 = 4169089) B4169089
theorem B14823427 : Blo 2135435 14823427 := bstep (se 1 (by rfl) ⟨11117570, by rfl⟩ : syracuseStep 14823427 = 22235141) B22235141
theorem B19764569 : Blo 2135435 19764569 := bstep (se 2 (by rfl) ⟨7411713, by rfl⟩ : syracuseStep 19764569 = 14823427) B14823427
theorem B13176379 : Blo 2135435 13176379 := bstep (se 1 (by rfl) ⟨9882284, by rfl⟩ : syracuseStep 13176379 = 19764569) B19764569
theorem B17568505 : Blo 2135435 17568505 := bstep (se 2 (by rfl) ⟨6588189, by rfl⟩ : syracuseStep 17568505 = 13176379) B13176379
theorem B23424673 : Blo 2135435 23424673 := bstep (se 2 (by rfl) ⟨8784252, by rfl⟩ : syracuseStep 23424673 = 17568505) B17568505
theorem B31232897 : Blo 2135435 31232897 := bstep (se 2 (by rfl) ⟨11712336, by rfl⟩ : syracuseStep 31232897 = 23424673) B23424673
theorem B20821931 : Blo 2135435 20821931 := bstep (se 1 (by rfl) ⟨15616448, by rfl⟩ : syracuseStep 20821931 = 31232897) B31232897
theorem B13881287 : Blo 2135435 13881287 := bstep (se 1 (by rfl) ⟨10410965, by rfl⟩ : syracuseStep 13881287 = 20821931) B20821931
theorem B9254191 : Blo 2135435 9254191 := bstep (se 1 (by rfl) ⟨6940643, by rfl⟩ : syracuseStep 9254191 = 13881287) B13881287
theorem B12338921 : Blo 2135435 12338921 := bstep (se 2 (by rfl) ⟨4627095, by rfl⟩ : syracuseStep 12338921 = 9254191) B9254191
theorem B8225947 : Blo 2135435 8225947 := bstep (se 1 (by rfl) ⟨6169460, by rfl⟩ : syracuseStep 8225947 = 12338921) B12338921
theorem B10967929 : Blo 2135435 10967929 := bstep (se 2 (by rfl) ⟨4112973, by rfl⟩ : syracuseStep 10967929 = 8225947) B8225947
theorem B58495621 : Blo 2135435 58495621 := bstep (se 4 (by rfl) ⟨5483964, by rfl⟩ : syracuseStep 58495621 = 10967929) B10967929
theorem B77994161 : Blo 2135435 77994161 := bstep (se 2 (by rfl) ⟨29247810, by rfl⟩ : syracuseStep 77994161 = 58495621) B58495621
theorem B51996107 : Blo 2135435 51996107 := bstep (se 1 (by rfl) ⟨38997080, by rfl⟩ : syracuseStep 51996107 = 77994161) B77994161
theorem B34664071 : Blo 2135435 34664071 := bstep (se 1 (by rfl) ⟨25998053, by rfl⟩ : syracuseStep 34664071 = 51996107) B51996107
theorem B46218761 : Blo 2135435 46218761 := bstep (se 2 (by rfl) ⟨17332035, by rfl⟩ : syracuseStep 46218761 = 34664071) B34664071
theorem B30812507 : Blo 2135435 30812507 := bstep (se 1 (by rfl) ⟨23109380, by rfl⟩ : syracuseStep 30812507 = 46218761) B46218761
theorem B20541671 : Blo 2135435 20541671 := bstep (se 1 (by rfl) ⟨15406253, by rfl⟩ : syracuseStep 20541671 = 30812507) B30812507
theorem B13694447 : Blo 2135435 13694447 := bstep (se 1 (by rfl) ⟨10270835, by rfl⟩ : syracuseStep 13694447 = 20541671) B20541671
theorem B36518525 : Blo 2135435 36518525 := bstep (se 3 (by rfl) ⟨6847223, by rfl⟩ : syracuseStep 36518525 = 13694447) B13694447
theorem B24345683 : Blo 2135435 24345683 := bstep (se 1 (by rfl) ⟨18259262, by rfl⟩ : syracuseStep 24345683 = 36518525) B36518525
theorem B16230455 : Blo 2135435 16230455 := bstep (se 1 (by rfl) ⟨12172841, by rfl⟩ : syracuseStep 16230455 = 24345683) B24345683
theorem B10820303 : Blo 2135435 10820303 := bstep (se 1 (by rfl) ⟨8115227, by rfl⟩ : syracuseStep 10820303 = 16230455) B16230455
theorem B7213535 : Blo 2135435 7213535 := bstep (se 1 (by rfl) ⟨5410151, by rfl⟩ : syracuseStep 7213535 = 10820303) B10820303
theorem B4809023 : Blo 2135435 4809023 := bstep (se 1 (by rfl) ⟨3606767, by rfl⟩ : syracuseStep 4809023 = 7213535) B7213535
theorem B3206015 : Blo 2135435 3206015 := bstep (se 1 (by rfl) ⟨2404511, by rfl⟩ : syracuseStep 3206015 = 4809023) B4809023
theorem B2137343 : Blo 2135435 2137343 := bstep (se 1 (by rfl) ⟨1603007, by rfl⟩ : syracuseStep 2137343 = 3206015) B3206015
theorem B3206021 : Blo 2135435 3206021 := bbase (se 4 (by rfl) ⟨300564, by rfl⟩ : syracuseStep 3206021 = 601129) (by norm_num)
theorem B2137347 : Blo 2135435 2137347 := bstep (se 1 (by rfl) ⟨1603010, by rfl⟩ : syracuseStep 2137347 = 3206021) B3206021
theorem B3606781 : Blo 2135435 3606781 := bbase (se 3 (by rfl) ⟨676271, by rfl⟩ : syracuseStep 3606781 = 1352543) (by norm_num)
theorem B4809041 : Blo 2135435 4809041 := bstep (se 2 (by rfl) ⟨1803390, by rfl⟩ : syracuseStep 4809041 = 3606781) B3606781
theorem B3206027 : Blo 2135435 3206027 := bstep (se 1 (by rfl) ⟨2404520, by rfl⟩ : syracuseStep 3206027 = 4809041) B4809041
theorem B2137351 : Blo 2135435 2137351 := bstep (se 1 (by rfl) ⟨1603013, by rfl⟩ : syracuseStep 2137351 = 3206027) B3206027
theorem B2404525 : Blo 2135435 2404525 := bbase (se 3 (by rfl) ⟨450848, by rfl⟩ : syracuseStep 2404525 = 901697) (by norm_num)
theorem B3206033 : Blo 2135435 3206033 := bstep (se 2 (by rfl) ⟨1202262, by rfl⟩ : syracuseStep 3206033 = 2404525) B2404525
theorem B2137355 : Blo 2135435 2137355 := bstep (se 1 (by rfl) ⟨1603016, by rfl⟩ : syracuseStep 2137355 = 3206033) B3206033
theorem B7213589 : Blo 2135435 7213589 := bbase (se 6 (by rfl) ⟨169068, by rfl⟩ : syracuseStep 7213589 = 338137) (by norm_num)
theorem B4809059 : Blo 2135435 4809059 := bstep (se 1 (by rfl) ⟨3606794, by rfl⟩ : syracuseStep 4809059 = 7213589) B7213589
theorem B3206039 : Blo 2135435 3206039 := bstep (se 1 (by rfl) ⟨2404529, by rfl⟩ : syracuseStep 3206039 = 4809059) B4809059
theorem B2137359 : Blo 2135435 2137359 := bstep (se 1 (by rfl) ⟨1603019, by rfl⟩ : syracuseStep 2137359 = 3206039) B3206039
theorem B3206045 : Blo 2135435 3206045 := bbase (se 3 (by rfl) ⟨601133, by rfl⟩ : syracuseStep 3206045 = 1202267) (by norm_num)
theorem B2137363 : Blo 2135435 2137363 := bstep (se 1 (by rfl) ⟨1603022, by rfl⟩ : syracuseStep 2137363 = 3206045) B3206045
theorem B4809077 : Blo 2135435 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B3206051 : Blo 2135435 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B2137367 : Blo 2135435 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B19498805 : Blo 2135435 19498805 := bbase (se 5 (by rfl) ⟨914006, by rfl⟩ : syracuseStep 19498805 = 1828013) (by norm_num)
theorem B12999203 : Blo 2135435 12999203 := bstep (se 1 (by rfl) ⟨9749402, by rfl⟩ : syracuseStep 12999203 = 19498805) B19498805
theorem B8666135 : Blo 2135435 8666135 := bstep (se 1 (by rfl) ⟨6499601, by rfl⟩ : syracuseStep 8666135 = 12999203) B12999203
theorem B5777423 : Blo 2135435 5777423 := bstep (se 1 (by rfl) ⟨4333067, by rfl⟩ : syracuseStep 5777423 = 8666135) B8666135
theorem B3851615 : Blo 2135435 3851615 := bstep (se 1 (by rfl) ⟨2888711, by rfl⟩ : syracuseStep 3851615 = 5777423) B5777423
theorem B2567743 : Blo 2135435 2567743 := bstep (se 1 (by rfl) ⟨1925807, by rfl⟩ : syracuseStep 2567743 = 3851615) B3851615
theorem B13694629 : Blo 2135435 13694629 := bstep (se 4 (by rfl) ⟨1283871, by rfl⟩ : syracuseStep 13694629 = 2567743) B2567743
theorem B18259505 : Blo 2135435 18259505 := bstep (se 2 (by rfl) ⟨6847314, by rfl⟩ : syracuseStep 18259505 = 13694629) B13694629
theorem B12173003 : Blo 2135435 12173003 := bstep (se 1 (by rfl) ⟨9129752, by rfl⟩ : syracuseStep 12173003 = 18259505) B18259505
theorem B8115335 : Blo 2135435 8115335 := bstep (se 1 (by rfl) ⟨6086501, by rfl⟩ : syracuseStep 8115335 = 12173003) B12173003
theorem B5410223 : Blo 2135435 5410223 := bstep (se 1 (by rfl) ⟨4057667, by rfl⟩ : syracuseStep 5410223 = 8115335) B8115335
theorem B3606815 : Blo 2135435 3606815 := bstep (se 1 (by rfl) ⟨2705111, by rfl⟩ : syracuseStep 3606815 = 5410223) B5410223
theorem B2404543 : Blo 2135435 2404543 := bstep (se 1 (by rfl) ⟨1803407, by rfl⟩ : syracuseStep 2404543 = 3606815) B3606815
theorem B3206057 : Blo 2135435 3206057 := bstep (se 2 (by rfl) ⟨1202271, by rfl⟩ : syracuseStep 3206057 = 2404543) B2404543
theorem B2137371 : Blo 2135435 2137371 := bstep (se 1 (by rfl) ⟨1603028, by rfl⟩ : syracuseStep 2137371 = 3206057) B3206057
theorem B8115349 : Blo 2135435 8115349 := bbase (se 6 (by rfl) ⟨190203, by rfl⟩ : syracuseStep 8115349 = 380407) (by norm_num)
theorem B10820465 : Blo 2135435 10820465 := bstep (se 2 (by rfl) ⟨4057674, by rfl⟩ : syracuseStep 10820465 = 8115349) B8115349
theorem B7213643 : Blo 2135435 7213643 := bstep (se 1 (by rfl) ⟨5410232, by rfl⟩ : syracuseStep 7213643 = 10820465) B10820465
theorem B4809095 : Blo 2135435 4809095 := bstep (se 1 (by rfl) ⟨3606821, by rfl⟩ : syracuseStep 4809095 = 7213643) B7213643
theorem B3206063 : Blo 2135435 3206063 := bstep (se 1 (by rfl) ⟨2404547, by rfl⟩ : syracuseStep 3206063 = 4809095) B4809095
theorem B2137375 : Blo 2135435 2137375 := bstep (se 1 (by rfl) ⟨1603031, by rfl⟩ : syracuseStep 2137375 = 3206063) B3206063
theorem B3206069 : Blo 2135435 3206069 := bbase (se 5 (by rfl) ⟨150284, by rfl⟩ : syracuseStep 3206069 = 300569) (by norm_num)
theorem B2137379 : Blo 2135435 2137379 := bstep (se 1 (by rfl) ⟨1603034, by rfl⟩ : syracuseStep 2137379 = 3206069) B3206069
theorem B5410253 : Blo 2135435 5410253 := bbase (se 3 (by rfl) ⟨1014422, by rfl⟩ : syracuseStep 5410253 = 2028845) (by norm_num)
theorem B3606835 : Blo 2135435 3606835 := bstep (se 1 (by rfl) ⟨2705126, by rfl⟩ : syracuseStep 3606835 = 5410253) B5410253
theorem B4809113 : Blo 2135435 4809113 := bstep (se 2 (by rfl) ⟨1803417, by rfl⟩ : syracuseStep 4809113 = 3606835) B3606835
theorem B3206075 : Blo 2135435 3206075 := bstep (se 1 (by rfl) ⟨2404556, by rfl⟩ : syracuseStep 3206075 = 4809113) B4809113
theorem B2137383 : Blo 2135435 2137383 := bstep (se 1 (by rfl) ⟨1603037, by rfl⟩ : syracuseStep 2137383 = 3206075) B3206075
theorem B2404561 : Blo 2135435 2404561 := bbase (se 2 (by rfl) ⟨901710, by rfl⟩ : syracuseStep 2404561 = 1803421) (by norm_num)
theorem B3206081 : Blo 2135435 3206081 := bstep (se 2 (by rfl) ⟨1202280, by rfl⟩ : syracuseStep 3206081 = 2404561) B2404561
theorem B2137387 : Blo 2135435 2137387 := bstep (se 1 (by rfl) ⟨1603040, by rfl⟩ : syracuseStep 2137387 = 3206081) B3206081
theorem B5777477 : Blo 2135435 5777477 := bbase (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) (by norm_num)
theorem B3851651 : Blo 2135435 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B10271069 : Blo 2135435 10271069 := bstep (se 3 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 10271069 = 3851651) B3851651
theorem B6847379 : Blo 2135435 6847379 := bstep (se 1 (by rfl) ⟨5135534, by rfl⟩ : syracuseStep 6847379 = 10271069) B10271069
theorem B4564919 : Blo 2135435 4564919 := bstep (se 1 (by rfl) ⟨3423689, by rfl⟩ : syracuseStep 4564919 = 6847379) B6847379
theorem B3043279 : Blo 2135435 3043279 := bstep (se 1 (by rfl) ⟨2282459, by rfl⟩ : syracuseStep 3043279 = 4564919) B4564919
theorem B4057705 : Blo 2135435 4057705 := bstep (se 2 (by rfl) ⟨1521639, by rfl⟩ : syracuseStep 4057705 = 3043279) B3043279
theorem B5410273 : Blo 2135435 5410273 := bstep (se 2 (by rfl) ⟨2028852, by rfl⟩ : syracuseStep 5410273 = 4057705) B4057705
theorem B7213697 : Blo 2135435 7213697 := bstep (se 2 (by rfl) ⟨2705136, by rfl⟩ : syracuseStep 7213697 = 5410273) B5410273
theorem B4809131 : Blo 2135435 4809131 := bstep (se 1 (by rfl) ⟨3606848, by rfl⟩ : syracuseStep 4809131 = 7213697) B7213697
theorem B3206087 : Blo 2135435 3206087 := bstep (se 1 (by rfl) ⟨2404565, by rfl⟩ : syracuseStep 3206087 = 4809131) B4809131
theorem B2137391 : Blo 2135435 2137391 := bstep (se 1 (by rfl) ⟨1603043, by rfl⟩ : syracuseStep 2137391 = 3206087) B3206087
theorem B3206093 : Blo 2135435 3206093 := bbase (se 3 (by rfl) ⟨601142, by rfl⟩ : syracuseStep 3206093 = 1202285) (by norm_num)
theorem B2137395 : Blo 2135435 2137395 := bstep (se 1 (by rfl) ⟨1603046, by rfl⟩ : syracuseStep 2137395 = 3206093) B3206093
theorem B4809149 : Blo 2135435 4809149 := bbase (se 3 (by rfl) ⟨901715, by rfl⟩ : syracuseStep 4809149 = 1803431) (by norm_num)
theorem B3206099 : Blo 2135435 3206099 := bstep (se 1 (by rfl) ⟨2404574, by rfl⟩ : syracuseStep 3206099 = 4809149) B4809149
theorem B2137399 : Blo 2135435 2137399 := bstep (se 1 (by rfl) ⟨1603049, by rfl⟩ : syracuseStep 2137399 = 3206099) B3206099
theorem B3606869 : Blo 2135435 3606869 := bbase (se 10 (by rfl) ⟨5283, by rfl⟩ : syracuseStep 3606869 = 10567) (by norm_num)
theorem B2404579 : Blo 2135435 2404579 := bstep (se 1 (by rfl) ⟨1803434, by rfl⟩ : syracuseStep 2404579 = 3606869) B3606869
theorem B3206105 : Blo 2135435 3206105 := bstep (se 2 (by rfl) ⟨1202289, by rfl⟩ : syracuseStep 3206105 = 2404579) B2404579
theorem B2137403 : Blo 2135435 2137403 := bstep (se 1 (by rfl) ⟨1603052, by rfl⟩ : syracuseStep 2137403 = 3206105) B3206105
theorem B6847429 : Blo 2135435 6847429 := bbase (se 4 (by rfl) ⟨641946, by rfl⟩ : syracuseStep 6847429 = 1283893) (by norm_num)
theorem B9129905 : Blo 2135435 9129905 := bstep (se 2 (by rfl) ⟨3423714, by rfl⟩ : syracuseStep 9129905 = 6847429) B6847429
theorem B6086603 : Blo 2135435 6086603 := bstep (se 1 (by rfl) ⟨4564952, by rfl⟩ : syracuseStep 6086603 = 9129905) B9129905
theorem B16230941 : Blo 2135435 16230941 := bstep (se 3 (by rfl) ⟨3043301, by rfl⟩ : syracuseStep 16230941 = 6086603) B6086603
theorem B10820627 : Blo 2135435 10820627 := bstep (se 1 (by rfl) ⟨8115470, by rfl⟩ : syracuseStep 10820627 = 16230941) B16230941
theorem B7213751 : Blo 2135435 7213751 := bstep (se 1 (by rfl) ⟨5410313, by rfl⟩ : syracuseStep 7213751 = 10820627) B10820627
theorem B4809167 : Blo 2135435 4809167 := bstep (se 1 (by rfl) ⟨3606875, by rfl⟩ : syracuseStep 4809167 = 7213751) B7213751
theorem B3206111 : Blo 2135435 3206111 := bstep (se 1 (by rfl) ⟨2404583, by rfl⟩ : syracuseStep 3206111 = 4809167) B4809167
theorem B2137407 : Blo 2135435 2137407 := bstep (se 1 (by rfl) ⟨1603055, by rfl⟩ : syracuseStep 2137407 = 3206111) B3206111
theorem B3206117 : Blo 2135435 3206117 := bbase (se 4 (by rfl) ⟨300573, by rfl⟩ : syracuseStep 3206117 = 601147) (by norm_num)
theorem B2137411 : Blo 2135435 2137411 := bstep (se 1 (by rfl) ⟨1603058, by rfl⟩ : syracuseStep 2137411 = 3206117) B3206117
theorem B9129941 : Blo 2135435 9129941 := bbase (se 7 (by rfl) ⟨106991, by rfl⟩ : syracuseStep 9129941 = 213983) (by norm_num)
theorem B6086627 : Blo 2135435 6086627 := bstep (se 1 (by rfl) ⟨4564970, by rfl⟩ : syracuseStep 6086627 = 9129941) B9129941
theorem B4057751 : Blo 2135435 4057751 := bstep (se 1 (by rfl) ⟨3043313, by rfl⟩ : syracuseStep 4057751 = 6086627) B6086627
theorem B2705167 : Blo 2135435 2705167 := bstep (se 1 (by rfl) ⟨2028875, by rfl⟩ : syracuseStep 2705167 = 4057751) B4057751
theorem B3606889 : Blo 2135435 3606889 := bstep (se 2 (by rfl) ⟨1352583, by rfl⟩ : syracuseStep 3606889 = 2705167) B2705167
theorem B4809185 : Blo 2135435 4809185 := bstep (se 2 (by rfl) ⟨1803444, by rfl⟩ : syracuseStep 4809185 = 3606889) B3606889
theorem B3206123 : Blo 2135435 3206123 := bstep (se 1 (by rfl) ⟨2404592, by rfl⟩ : syracuseStep 3206123 = 4809185) B4809185
theorem B2137415 : Blo 2135435 2137415 := bstep (se 1 (by rfl) ⟨1603061, by rfl⟩ : syracuseStep 2137415 = 3206123) B3206123
theorem B2404597 : Blo 2135435 2404597 := bbase (se 5 (by rfl) ⟨112715, by rfl⟩ : syracuseStep 2404597 = 225431) (by norm_num)
theorem B3206129 : Blo 2135435 3206129 := bstep (se 2 (by rfl) ⟨1202298, by rfl⟩ : syracuseStep 3206129 = 2404597) B2404597
theorem B2137419 : Blo 2135435 2137419 := bstep (se 1 (by rfl) ⟨1603064, by rfl⟩ : syracuseStep 2137419 = 3206129) B3206129
theorem B2705177 : Blo 2135435 2705177 := bbase (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) (by norm_num)
theorem B7213805 : Blo 2135435 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B4809203 : Blo 2135435 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B3206135 : Blo 2135435 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B2137423 : Blo 2135435 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B3206141 : Blo 2135435 3206141 := bbase (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) (by norm_num)
theorem B2137427 : Blo 2135435 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B4809221 : Blo 2135435 4809221 := bbase (se 4 (by rfl) ⟨450864, by rfl⟩ : syracuseStep 4809221 = 901729) (by norm_num)
theorem B3206147 : Blo 2135435 3206147 := bstep (se 1 (by rfl) ⟨2404610, by rfl⟩ : syracuseStep 3206147 = 4809221) B4809221
theorem B2137431 : Blo 2135435 2137431 := bstep (se 1 (by rfl) ⟨1603073, by rfl⟩ : syracuseStep 2137431 = 3206147) B3206147
theorem B4057789 : Blo 2135435 4057789 := bbase (se 3 (by rfl) ⟨760835, by rfl⟩ : syracuseStep 4057789 = 1521671) (by norm_num)
theorem B5410385 : Blo 2135435 5410385 := bstep (se 2 (by rfl) ⟨2028894, by rfl⟩ : syracuseStep 5410385 = 4057789) B4057789
theorem B3606923 : Blo 2135435 3606923 := bstep (se 1 (by rfl) ⟨2705192, by rfl⟩ : syracuseStep 3606923 = 5410385) B5410385
theorem B2404615 : Blo 2135435 2404615 := bstep (se 1 (by rfl) ⟨1803461, by rfl⟩ : syracuseStep 2404615 = 3606923) B3606923
theorem B3206153 : Blo 2135435 3206153 := bstep (se 2 (by rfl) ⟨1202307, by rfl⟩ : syracuseStep 3206153 = 2404615) B2404615
theorem B2137435 : Blo 2135435 2137435 := bstep (se 1 (by rfl) ⟨1603076, by rfl⟩ : syracuseStep 2137435 = 3206153) B3206153
theorem C0 (j : ℕ) (h1 : 533858 ≤ j) (h2 : j ≤ 534358) : Blo 2135435 (4 * j + 3) := by
  interval_cases j
  · exact B2135435
  · exact B2135439
  · exact B2135443
  · exact B2135447
  · exact B2135451
  · exact B2135455
  · exact B2135459
  · exact B2135463
  · exact B2135467
  · exact B2135471
  · exact B2135475
  · exact B2135479
  · exact B2135483
  · exact B2135487
  · exact B2135491
  · exact B2135495
  · exact B2135499
  · exact B2135503
  · exact B2135507
  · exact B2135511
  · exact B2135515
  · exact B2135519
  · exact B2135523
  · exact B2135527
  · exact B2135531
  · exact B2135535
  · exact B2135539
  · exact B2135543
  · exact B2135547
  · exact B2135551
  · exact B2135555
  · exact B2135559
  · exact B2135563
  · exact B2135567
  · exact B2135571
  · exact B2135575
  · exact B2135579
  · exact B2135583
  · exact B2135587
  · exact B2135591
  · exact B2135595
  · exact B2135599
  · exact B2135603
  · exact B2135607
  · exact B2135611
  · exact B2135615
  · exact B2135619
  · exact B2135623
  · exact B2135627
  · exact B2135631
  · exact B2135635
  · exact B2135639
  · exact B2135643
  · exact B2135647
  · exact B2135651
  · exact B2135655
  · exact B2135659
  · exact B2135663
  · exact B2135667
  · exact B2135671
  · exact B2135675
  · exact B2135679
  · exact B2135683
  · exact B2135687
  · exact B2135691
  · exact B2135695
  · exact B2135699
  · exact B2135703
  · exact B2135707
  · exact B2135711
  · exact B2135715
  · exact B2135719
  · exact B2135723
  · exact B2135727
  · exact B2135731
  · exact B2135735
  · exact B2135739
  · exact B2135743
  · exact B2135747
  · exact B2135751
  · exact B2135755
  · exact B2135759
  · exact B2135763
  · exact B2135767
  · exact B2135771
  · exact B2135775
  · exact B2135779
  · exact B2135783
  · exact B2135787
  · exact B2135791
  · exact B2135795
  · exact B2135799
  · exact B2135803
  · exact B2135807
  · exact B2135811
  · exact B2135815
  · exact B2135819
  · exact B2135823
  · exact B2135827
  · exact B2135831
  · exact B2135835
  · exact B2135839
  · exact B2135843
  · exact B2135847
  · exact B2135851
  · exact B2135855
  · exact B2135859
  · exact B2135863
  · exact B2135867
  · exact B2135871
  · exact B2135875
  · exact B2135879
  · exact B2135883
  · exact B2135887
  · exact B2135891
  · exact B2135895
  · exact B2135899
  · exact B2135903
  · exact B2135907
  · exact B2135911
  · exact B2135915
  · exact B2135919
  · exact B2135923
  · exact B2135927
  · exact B2135931
  · exact B2135935
  · exact B2135939
  · exact B2135943
  · exact B2135947
  · exact B2135951
  · exact B2135955
  · exact B2135959
  · exact B2135963
  · exact B2135967
  · exact B2135971
  · exact B2135975
  · exact B2135979
  · exact B2135983
  · exact B2135987
  · exact B2135991
  · exact B2135995
  · exact B2135999
  · exact B2136003
  · exact B2136007
  · exact B2136011
  · exact B2136015
  · exact B2136019
  · exact B2136023
  · exact B2136027
  · exact B2136031
  · exact B2136035
  · exact B2136039
  · exact B2136043
  · exact B2136047
  · exact B2136051
  · exact B2136055
  · exact B2136059
  · exact B2136063
  · exact B2136067
  · exact B2136071
  · exact B2136075
  · exact B2136079
  · exact B2136083
  · exact B2136087
  · exact B2136091
  · exact B2136095
  · exact B2136099
  · exact B2136103
  · exact B2136107
  · exact B2136111
  · exact B2136115
  · exact B2136119
  · exact B2136123
  · exact B2136127
  · exact B2136131
  · exact B2136135
  · exact B2136139
  · exact B2136143
  · exact B2136147
  · exact B2136151
  · exact B2136155
  · exact B2136159
  · exact B2136163
  · exact B2136167
  · exact B2136171
  · exact B2136175
  · exact B2136179
  · exact B2136183
  · exact B2136187
  · exact B2136191
  · exact B2136195
  · exact B2136199
  · exact B2136203
  · exact B2136207
  · exact B2136211
  · exact B2136215
  · exact B2136219
  · exact B2136223
  · exact B2136227
  · exact B2136231
  · exact B2136235
  · exact B2136239
  · exact B2136243
  · exact B2136247
  · exact B2136251
  · exact B2136255
  · exact B2136259
  · exact B2136263
  · exact B2136267
  · exact B2136271
  · exact B2136275
  · exact B2136279
  · exact B2136283
  · exact B2136287
  · exact B2136291
  · exact B2136295
  · exact B2136299
  · exact B2136303
  · exact B2136307
  · exact B2136311
  · exact B2136315
  · exact B2136319
  · exact B2136323
  · exact B2136327
  · exact B2136331
  · exact B2136335
  · exact B2136339
  · exact B2136343
  · exact B2136347
  · exact B2136351
  · exact B2136355
  · exact B2136359
  · exact B2136363
  · exact B2136367
  · exact B2136371
  · exact B2136375
  · exact B2136379
  · exact B2136383
  · exact B2136387
  · exact B2136391
  · exact B2136395
  · exact B2136399
  · exact B2136403
  · exact B2136407
  · exact B2136411
  · exact B2136415
  · exact B2136419
  · exact B2136423
  · exact B2136427
  · exact B2136431
  · exact B2136435
  · exact B2136439
  · exact B2136443
  · exact B2136447
  · exact B2136451
  · exact B2136455
  · exact B2136459
  · exact B2136463
  · exact B2136467
  · exact B2136471
  · exact B2136475
  · exact B2136479
  · exact B2136483
  · exact B2136487
  · exact B2136491
  · exact B2136495
  · exact B2136499
  · exact B2136503
  · exact B2136507
  · exact B2136511
  · exact B2136515
  · exact B2136519
  · exact B2136523
  · exact B2136527
  · exact B2136531
  · exact B2136535
  · exact B2136539
  · exact B2136543
  · exact B2136547
  · exact B2136551
  · exact B2136555
  · exact B2136559
  · exact B2136563
  · exact B2136567
  · exact B2136571
  · exact B2136575
  · exact B2136579
  · exact B2136583
  · exact B2136587
  · exact B2136591
  · exact B2136595
  · exact B2136599
  · exact B2136603
  · exact B2136607
  · exact B2136611
  · exact B2136615
  · exact B2136619
  · exact B2136623
  · exact B2136627
  · exact B2136631
  · exact B2136635
  · exact B2136639
  · exact B2136643
  · exact B2136647
  · exact B2136651
  · exact B2136655
  · exact B2136659
  · exact B2136663
  · exact B2136667
  · exact B2136671
  · exact B2136675
  · exact B2136679
  · exact B2136683
  · exact B2136687
  · exact B2136691
  · exact B2136695
  · exact B2136699
  · exact B2136703
  · exact B2136707
  · exact B2136711
  · exact B2136715
  · exact B2136719
  · exact B2136723
  · exact B2136727
  · exact B2136731
  · exact B2136735
  · exact B2136739
  · exact B2136743
  · exact B2136747
  · exact B2136751
  · exact B2136755
  · exact B2136759
  · exact B2136763
  · exact B2136767
  · exact B2136771
  · exact B2136775
  · exact B2136779
  · exact B2136783
  · exact B2136787
  · exact B2136791
  · exact B2136795
  · exact B2136799
  · exact B2136803
  · exact B2136807
  · exact B2136811
  · exact B2136815
  · exact B2136819
  · exact B2136823
  · exact B2136827
  · exact B2136831
  · exact B2136835
  · exact B2136839
  · exact B2136843
  · exact B2136847
  · exact B2136851
  · exact B2136855
  · exact B2136859
  · exact B2136863
  · exact B2136867
  · exact B2136871
  · exact B2136875
  · exact B2136879
  · exact B2136883
  · exact B2136887
  · exact B2136891
  · exact B2136895
  · exact B2136899
  · exact B2136903
  · exact B2136907
  · exact B2136911
  · exact B2136915
  · exact B2136919
  · exact B2136923
  · exact B2136927
  · exact B2136931
  · exact B2136935
  · exact B2136939
  · exact B2136943
  · exact B2136947
  · exact B2136951
  · exact B2136955
  · exact B2136959
  · exact B2136963
  · exact B2136967
  · exact B2136971
  · exact B2136975
  · exact B2136979
  · exact B2136983
  · exact B2136987
  · exact B2136991
  · exact B2136995
  · exact B2136999
  · exact B2137003
  · exact B2137007
  · exact B2137011
  · exact B2137015
  · exact B2137019
  · exact B2137023
  · exact B2137027
  · exact B2137031
  · exact B2137035
  · exact B2137039
  · exact B2137043
  · exact B2137047
  · exact B2137051
  · exact B2137055
  · exact B2137059
  · exact B2137063
  · exact B2137067
  · exact B2137071
  · exact B2137075
  · exact B2137079
  · exact B2137083
  · exact B2137087
  · exact B2137091
  · exact B2137095
  · exact B2137099
  · exact B2137103
  · exact B2137107
  · exact B2137111
  · exact B2137115
  · exact B2137119
  · exact B2137123
  · exact B2137127
  · exact B2137131
  · exact B2137135
  · exact B2137139
  · exact B2137143
  · exact B2137147
  · exact B2137151
  · exact B2137155
  · exact B2137159
  · exact B2137163
  · exact B2137167
  · exact B2137171
  · exact B2137175
  · exact B2137179
  · exact B2137183
  · exact B2137187
  · exact B2137191
  · exact B2137195
  · exact B2137199
  · exact B2137203
  · exact B2137207
  · exact B2137211
  · exact B2137215
  · exact B2137219
  · exact B2137223
  · exact B2137227
  · exact B2137231
  · exact B2137235
  · exact B2137239
  · exact B2137243
  · exact B2137247
  · exact B2137251
  · exact B2137255
  · exact B2137259
  · exact B2137263
  · exact B2137267
  · exact B2137271
  · exact B2137275
  · exact B2137279
  · exact B2137283
  · exact B2137287
  · exact B2137291
  · exact B2137295
  · exact B2137299
  · exact B2137303
  · exact B2137307
  · exact B2137311
  · exact B2137315
  · exact B2137319
  · exact B2137323
  · exact B2137327
  · exact B2137331
  · exact B2137335
  · exact B2137339
  · exact B2137343
  · exact B2137347
  · exact B2137351
  · exact B2137355
  · exact B2137359
  · exact B2137363
  · exact B2137367
  · exact B2137371
  · exact B2137375
  · exact B2137379
  · exact B2137383
  · exact B2137387
  · exact B2137391
  · exact B2137395
  · exact B2137399
  · exact B2137403
  · exact B2137407
  · exact B2137411
  · exact B2137415
  · exact B2137419
  · exact B2137423
  · exact B2137427
  · exact B2137431
  · exact B2137435
theorem solution (m : ℕ) (hlo : 2135435 ≤ m) (hhi : m ≤ 2137435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 533858 ≤ j := by omega
    have hj2 : j ≤ 534358 := by omega
    have hb : Blo 2135435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
