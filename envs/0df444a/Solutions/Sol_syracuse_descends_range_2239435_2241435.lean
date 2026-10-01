-- Prove2me | solution 1 for syracuse_descends_range_2239435_2241435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:57.263475+00:00
-- url     : https://prove2.me/submissions/4cb0028c-06f2-4a4b-b2c0-99edcf48291e

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

theorem B2519365 : Blo 2239435 2519365 := bbase (se 4 (by rfl) ⟨236190, by rfl⟩ : syracuseStep 2519365 = 472381) (by norm_num)
theorem B3359153 : Blo 2239435 3359153 := bstep (se 2 (by rfl) ⟨1259682, by rfl⟩ : syracuseStep 3359153 = 2519365) B2519365
theorem B2239435 : Blo 2239435 2239435 := bstep (se 1 (by rfl) ⟨1679576, by rfl⟩ : syracuseStep 2239435 = 3359153) B3359153
theorem B4251437 : Blo 2239435 4251437 := bbase (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) (by norm_num)
theorem B2834291 : Blo 2239435 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B7558109 : Blo 2239435 7558109 := bstep (se 3 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 7558109 = 2834291) B2834291
theorem B5038739 : Blo 2239435 5038739 := bstep (se 1 (by rfl) ⟨3779054, by rfl⟩ : syracuseStep 5038739 = 7558109) B7558109
theorem B3359159 : Blo 2239435 3359159 := bstep (se 1 (by rfl) ⟨2519369, by rfl⟩ : syracuseStep 3359159 = 5038739) B5038739
theorem B2239439 : Blo 2239435 2239439 := bstep (se 1 (by rfl) ⟨1679579, by rfl⟩ : syracuseStep 2239439 = 3359159) B3359159
theorem B3359165 : Blo 2239435 3359165 := bbase (se 3 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 3359165 = 1259687) (by norm_num)
theorem B2239443 : Blo 2239435 2239443 := bstep (se 1 (by rfl) ⟨1679582, by rfl⟩ : syracuseStep 2239443 = 3359165) B3359165
theorem B5038757 : Blo 2239435 5038757 := bbase (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) (by norm_num)
theorem B3359171 : Blo 2239435 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B2239447 : Blo 2239435 2239447 := bstep (se 1 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 2239447 = 3359171) B3359171
theorem B5668613 : Blo 2239435 5668613 := bbase (se 4 (by rfl) ⟨531432, by rfl⟩ : syracuseStep 5668613 = 1062865) (by norm_num)
theorem B3779075 : Blo 2239435 3779075 := bstep (se 1 (by rfl) ⟨2834306, by rfl⟩ : syracuseStep 3779075 = 5668613) B5668613
theorem B2519383 : Blo 2239435 2519383 := bstep (se 1 (by rfl) ⟨1889537, by rfl⟩ : syracuseStep 2519383 = 3779075) B3779075
theorem B3359177 : Blo 2239435 3359177 := bstep (se 2 (by rfl) ⟨1259691, by rfl⟩ : syracuseStep 3359177 = 2519383) B2519383
theorem B2239451 : Blo 2239435 2239451 := bstep (se 1 (by rfl) ⟨1679588, by rfl⟩ : syracuseStep 2239451 = 3359177) B3359177
theorem B4782901 : Blo 2239435 4782901 := bbase (se 5 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 4782901 = 448397) (by norm_num)
theorem B6377201 : Blo 2239435 6377201 := bstep (se 2 (by rfl) ⟨2391450, by rfl⟩ : syracuseStep 6377201 = 4782901) B4782901
theorem B4251467 : Blo 2239435 4251467 := bstep (se 1 (by rfl) ⟨3188600, by rfl⟩ : syracuseStep 4251467 = 6377201) B6377201
theorem B11337245 : Blo 2239435 11337245 := bstep (se 3 (by rfl) ⟨2125733, by rfl⟩ : syracuseStep 11337245 = 4251467) B4251467
theorem B7558163 : Blo 2239435 7558163 := bstep (se 1 (by rfl) ⟨5668622, by rfl⟩ : syracuseStep 7558163 = 11337245) B11337245
theorem B5038775 : Blo 2239435 5038775 := bstep (se 1 (by rfl) ⟨3779081, by rfl⟩ : syracuseStep 5038775 = 7558163) B7558163
theorem B3359183 : Blo 2239435 3359183 := bstep (se 1 (by rfl) ⟨2519387, by rfl⟩ : syracuseStep 3359183 = 5038775) B5038775
theorem B2239455 : Blo 2239435 2239455 := bstep (se 1 (by rfl) ⟨1679591, by rfl⟩ : syracuseStep 2239455 = 3359183) B3359183
theorem B3359189 : Blo 2239435 3359189 := bbase (se 7 (by rfl) ⟨39365, by rfl⟩ : syracuseStep 3359189 = 78731) (by norm_num)
theorem B2239459 : Blo 2239435 2239459 := bstep (se 1 (by rfl) ⟨1679594, by rfl⟩ : syracuseStep 2239459 = 3359189) B3359189
theorem B8502965 : Blo 2239435 8502965 := bbase (se 5 (by rfl) ⟨398576, by rfl⟩ : syracuseStep 8502965 = 797153) (by norm_num)
theorem B5668643 : Blo 2239435 5668643 := bstep (se 1 (by rfl) ⟨4251482, by rfl⟩ : syracuseStep 5668643 = 8502965) B8502965
theorem B3779095 : Blo 2239435 3779095 := bstep (se 1 (by rfl) ⟨2834321, by rfl⟩ : syracuseStep 3779095 = 5668643) B5668643
theorem B5038793 : Blo 2239435 5038793 := bstep (se 2 (by rfl) ⟨1889547, by rfl⟩ : syracuseStep 5038793 = 3779095) B3779095
theorem B3359195 : Blo 2239435 3359195 := bstep (se 1 (by rfl) ⟨2519396, by rfl⟩ : syracuseStep 3359195 = 5038793) B5038793
theorem B2239463 : Blo 2239435 2239463 := bstep (se 1 (by rfl) ⟨1679597, by rfl⟩ : syracuseStep 2239463 = 3359195) B3359195
theorem B2519401 : Blo 2239435 2519401 := bbase (se 2 (by rfl) ⟨944775, by rfl⟩ : syracuseStep 2519401 = 1889551) (by norm_num)
theorem B3359201 : Blo 2239435 3359201 := bstep (se 2 (by rfl) ⟨1259700, by rfl⟩ : syracuseStep 3359201 = 2519401) B2519401
theorem B2239467 : Blo 2239435 2239467 := bstep (se 1 (by rfl) ⟨1679600, by rfl⟩ : syracuseStep 2239467 = 3359201) B3359201
theorem B10761605 : Blo 2239435 10761605 := bbase (se 4 (by rfl) ⟨1008900, by rfl⟩ : syracuseStep 10761605 = 2017801) (by norm_num)
theorem B7174403 : Blo 2239435 7174403 := bstep (se 1 (by rfl) ⟨5380802, by rfl⟩ : syracuseStep 7174403 = 10761605) B10761605
theorem B4782935 : Blo 2239435 4782935 := bstep (se 1 (by rfl) ⟨3587201, by rfl⟩ : syracuseStep 4782935 = 7174403) B7174403
theorem B12754493 : Blo 2239435 12754493 := bstep (se 3 (by rfl) ⟨2391467, by rfl⟩ : syracuseStep 12754493 = 4782935) B4782935
theorem B8502995 : Blo 2239435 8502995 := bstep (se 1 (by rfl) ⟨6377246, by rfl⟩ : syracuseStep 8502995 = 12754493) B12754493
theorem B5668663 : Blo 2239435 5668663 := bstep (se 1 (by rfl) ⟨4251497, by rfl⟩ : syracuseStep 5668663 = 8502995) B8502995
theorem B7558217 : Blo 2239435 7558217 := bstep (se 2 (by rfl) ⟨2834331, by rfl⟩ : syracuseStep 7558217 = 5668663) B5668663
theorem B5038811 : Blo 2239435 5038811 := bstep (se 1 (by rfl) ⟨3779108, by rfl⟩ : syracuseStep 5038811 = 7558217) B7558217
theorem B3359207 : Blo 2239435 3359207 := bstep (se 1 (by rfl) ⟨2519405, by rfl⟩ : syracuseStep 3359207 = 5038811) B5038811
theorem B2239471 : Blo 2239435 2239471 := bstep (se 1 (by rfl) ⟨1679603, by rfl⟩ : syracuseStep 2239471 = 3359207) B3359207
theorem B3359213 : Blo 2239435 3359213 := bbase (se 3 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 3359213 = 1259705) (by norm_num)
theorem B2239475 : Blo 2239435 2239475 := bstep (se 1 (by rfl) ⟨1679606, by rfl⟩ : syracuseStep 2239475 = 3359213) B3359213
theorem B5038829 : Blo 2239435 5038829 := bbase (se 3 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 5038829 = 1889561) (by norm_num)
theorem B3359219 : Blo 2239435 3359219 := bstep (se 1 (by rfl) ⟨2519414, by rfl⟩ : syracuseStep 3359219 = 5038829) B5038829
theorem B2239479 : Blo 2239435 2239479 := bstep (se 1 (by rfl) ⟨1679609, by rfl⟩ : syracuseStep 2239479 = 3359219) B3359219
theorem B2391481 : Blo 2239435 2391481 := bbase (se 2 (by rfl) ⟨896805, by rfl⟩ : syracuseStep 2391481 = 1793611) (by norm_num)
theorem B3188641 : Blo 2239435 3188641 := bstep (se 2 (by rfl) ⟨1195740, by rfl⟩ : syracuseStep 3188641 = 2391481) B2391481
theorem B4251521 : Blo 2239435 4251521 := bstep (se 2 (by rfl) ⟨1594320, by rfl⟩ : syracuseStep 4251521 = 3188641) B3188641
theorem B2834347 : Blo 2239435 2834347 := bstep (se 1 (by rfl) ⟨2125760, by rfl⟩ : syracuseStep 2834347 = 4251521) B4251521
theorem B3779129 : Blo 2239435 3779129 := bstep (se 2 (by rfl) ⟨1417173, by rfl⟩ : syracuseStep 3779129 = 2834347) B2834347
theorem B2519419 : Blo 2239435 2519419 := bstep (se 1 (by rfl) ⟨1889564, by rfl⟩ : syracuseStep 2519419 = 3779129) B3779129
theorem B3359225 : Blo 2239435 3359225 := bstep (se 2 (by rfl) ⟨1259709, by rfl⟩ : syracuseStep 3359225 = 2519419) B2519419
theorem B2239483 : Blo 2239435 2239483 := bstep (se 1 (by rfl) ⟨1679612, by rfl⟩ : syracuseStep 2239483 = 3359225) B3359225
theorem B4981421 : Blo 2239435 4981421 := bbase (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) (by norm_num)
theorem B3320947 : Blo 2239435 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B4427929 : Blo 2239435 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B23615621 : Blo 2239435 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B15743747 : Blo 2239435 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B10495831 : Blo 2239435 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B13994441 : Blo 2239435 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B9329627 : Blo 2239435 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B24879005 : Blo 2239435 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B16586003 : Blo 2239435 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B44229341 : Blo 2239435 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B29486227 : Blo 2239435 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B39314969 : Blo 2239435 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B26209979 : Blo 2239435 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B17473319 : Blo 2239435 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B11648879 : Blo 2239435 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B7765919 : Blo 2239435 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B5177279 : Blo 2239435 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B13806077 : Blo 2239435 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B36816205 : Blo 2239435 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B49088273 : Blo 2239435 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B523608245 : Blo 2239435 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B349072163 : Blo 2239435 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B232714775 : Blo 2239435 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B155143183 : Blo 2239435 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B206857577 : Blo 2239435 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B137905051 : Blo 2239435 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B183873401 : Blo 2239435 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B122582267 : Blo 2239435 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B81721511 : Blo 2239435 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B54481007 : Blo 2239435 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B36320671 : Blo 2239435 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B48427561 : Blo 2239435 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B64570081 : Blo 2239435 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B86093441 : Blo 2239435 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B57395627 : Blo 2239435 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B38263751 : Blo 2239435 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B25509167 : Blo 2239435 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B17006111 : Blo 2239435 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B11337407 : Blo 2239435 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B7558271 : Blo 2239435 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B5038847 : Blo 2239435 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B3359231 : Blo 2239435 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B2239487 : Blo 2239435 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B3359237 : Blo 2239435 3359237 := bbase (se 4 (by rfl) ⟨314928, by rfl⟩ : syracuseStep 3359237 = 629857) (by norm_num)
theorem B2239491 : Blo 2239435 2239491 := bstep (se 1 (by rfl) ⟨1679618, by rfl⟩ : syracuseStep 2239491 = 3359237) B3359237
theorem B3779149 : Blo 2239435 3779149 := bbase (se 3 (by rfl) ⟨708590, by rfl⟩ : syracuseStep 3779149 = 1417181) (by norm_num)
theorem B5038865 : Blo 2239435 5038865 := bstep (se 2 (by rfl) ⟨1889574, by rfl⟩ : syracuseStep 5038865 = 3779149) B3779149
theorem B3359243 : Blo 2239435 3359243 := bstep (se 1 (by rfl) ⟨2519432, by rfl⟩ : syracuseStep 3359243 = 5038865) B5038865
theorem B2239495 : Blo 2239435 2239495 := bstep (se 1 (by rfl) ⟨1679621, by rfl⟩ : syracuseStep 2239495 = 3359243) B3359243
theorem B2519437 : Blo 2239435 2519437 := bbase (se 3 (by rfl) ⟨472394, by rfl⟩ : syracuseStep 2519437 = 944789) (by norm_num)
theorem B3359249 : Blo 2239435 3359249 := bstep (se 2 (by rfl) ⟨1259718, by rfl⟩ : syracuseStep 3359249 = 2519437) B2519437
theorem B2239499 : Blo 2239435 2239499 := bstep (se 1 (by rfl) ⟨1679624, by rfl⟩ : syracuseStep 2239499 = 3359249) B3359249
theorem B7558325 : Blo 2239435 7558325 := bbase (se 5 (by rfl) ⟨354296, by rfl⟩ : syracuseStep 7558325 = 708593) (by norm_num)
theorem B5038883 : Blo 2239435 5038883 := bstep (se 1 (by rfl) ⟨3779162, by rfl⟩ : syracuseStep 5038883 = 7558325) B7558325
theorem B3359255 : Blo 2239435 3359255 := bstep (se 1 (by rfl) ⟨2519441, by rfl⟩ : syracuseStep 3359255 = 5038883) B5038883
theorem B2239503 : Blo 2239435 2239503 := bstep (se 1 (by rfl) ⟨1679627, by rfl⟩ : syracuseStep 2239503 = 3359255) B3359255
theorem B3359261 : Blo 2239435 3359261 := bbase (se 3 (by rfl) ⟨629861, by rfl⟩ : syracuseStep 3359261 = 1259723) (by norm_num)
theorem B2239507 : Blo 2239435 2239507 := bstep (se 1 (by rfl) ⟨1679630, by rfl⟩ : syracuseStep 2239507 = 3359261) B3359261
theorem B5038901 : Blo 2239435 5038901 := bbase (se 5 (by rfl) ⟨236198, by rfl⟩ : syracuseStep 5038901 = 472397) (by norm_num)
theorem B3359267 : Blo 2239435 3359267 := bstep (se 1 (by rfl) ⟨2519450, by rfl⟩ : syracuseStep 3359267 = 5038901) B5038901
theorem B2239511 : Blo 2239435 2239511 := bstep (se 1 (by rfl) ⟨1679633, by rfl⟩ : syracuseStep 2239511 = 3359267) B3359267
theorem B5107661 : Blo 2239435 5107661 := bbase (se 3 (by rfl) ⟨957686, by rfl⟩ : syracuseStep 5107661 = 1915373) (by norm_num)
theorem B3405107 : Blo 2239435 3405107 := bstep (se 1 (by rfl) ⟨2553830, by rfl⟩ : syracuseStep 3405107 = 5107661) B5107661
theorem B2270071 : Blo 2239435 2270071 := bstep (se 1 (by rfl) ⟨1702553, by rfl⟩ : syracuseStep 2270071 = 3405107) B3405107
theorem B12107045 : Blo 2239435 12107045 := bstep (se 4 (by rfl) ⟨1135035, by rfl⟩ : syracuseStep 12107045 = 2270071) B2270071
theorem B8071363 : Blo 2239435 8071363 := bstep (se 1 (by rfl) ⟨6053522, by rfl⟩ : syracuseStep 8071363 = 12107045) B12107045
theorem B10761817 : Blo 2239435 10761817 := bstep (se 2 (by rfl) ⟨4035681, by rfl⟩ : syracuseStep 10761817 = 8071363) B8071363
theorem B14349089 : Blo 2239435 14349089 := bstep (se 2 (by rfl) ⟨5380908, by rfl⟩ : syracuseStep 14349089 = 10761817) B10761817
theorem B9566059 : Blo 2239435 9566059 := bstep (se 1 (by rfl) ⟨7174544, by rfl⟩ : syracuseStep 9566059 = 14349089) B14349089
theorem B12754745 : Blo 2239435 12754745 := bstep (se 2 (by rfl) ⟨4783029, by rfl⟩ : syracuseStep 12754745 = 9566059) B9566059
theorem B8503163 : Blo 2239435 8503163 := bstep (se 1 (by rfl) ⟨6377372, by rfl⟩ : syracuseStep 8503163 = 12754745) B12754745
theorem B5668775 : Blo 2239435 5668775 := bstep (se 1 (by rfl) ⟨4251581, by rfl⟩ : syracuseStep 5668775 = 8503163) B8503163
theorem B3779183 : Blo 2239435 3779183 := bstep (se 1 (by rfl) ⟨2834387, by rfl⟩ : syracuseStep 3779183 = 5668775) B5668775
theorem B2519455 : Blo 2239435 2519455 := bstep (se 1 (by rfl) ⟨1889591, by rfl⟩ : syracuseStep 2519455 = 3779183) B3779183
theorem B3359273 : Blo 2239435 3359273 := bstep (se 2 (by rfl) ⟨1259727, by rfl⟩ : syracuseStep 3359273 = 2519455) B2519455
theorem B2239515 : Blo 2239435 2239515 := bstep (se 1 (by rfl) ⟨1679636, by rfl⟩ : syracuseStep 2239515 = 3359273) B3359273
theorem B65451989 : Blo 2239435 65451989 := bbase (se 7 (by rfl) ⟨767015, by rfl⟩ : syracuseStep 65451989 = 1534031) (by norm_num)
theorem B43634659 : Blo 2239435 43634659 := bstep (se 1 (by rfl) ⟨32725994, by rfl⟩ : syracuseStep 43634659 = 65451989) B65451989
theorem B58179545 : Blo 2239435 58179545 := bstep (se 2 (by rfl) ⟨21817329, by rfl⟩ : syracuseStep 58179545 = 43634659) B43634659
theorem B38786363 : Blo 2239435 38786363 := bstep (se 1 (by rfl) ⟨29089772, by rfl⟩ : syracuseStep 38786363 = 58179545) B58179545
theorem B25857575 : Blo 2239435 25857575 := bstep (se 1 (by rfl) ⟨19393181, by rfl⟩ : syracuseStep 25857575 = 38786363) B38786363
theorem B17238383 : Blo 2239435 17238383 := bstep (se 1 (by rfl) ⟨12928787, by rfl⟩ : syracuseStep 17238383 = 25857575) B25857575
theorem B11492255 : Blo 2239435 11492255 := bstep (se 1 (by rfl) ⟨8619191, by rfl⟩ : syracuseStep 11492255 = 17238383) B17238383
theorem B7661503 : Blo 2239435 7661503 := bstep (se 1 (by rfl) ⟨5746127, by rfl⟩ : syracuseStep 7661503 = 11492255) B11492255
theorem B10215337 : Blo 2239435 10215337 := bstep (se 2 (by rfl) ⟨3830751, by rfl⟩ : syracuseStep 10215337 = 7661503) B7661503
theorem B13620449 : Blo 2239435 13620449 := bstep (se 2 (by rfl) ⟨5107668, by rfl⟩ : syracuseStep 13620449 = 10215337) B10215337
theorem B9080299 : Blo 2239435 9080299 := bstep (se 1 (by rfl) ⟨6810224, by rfl⟩ : syracuseStep 9080299 = 13620449) B13620449
theorem B12107065 : Blo 2239435 12107065 := bstep (se 2 (by rfl) ⟨4540149, by rfl⟩ : syracuseStep 12107065 = 9080299) B9080299
theorem B16142753 : Blo 2239435 16142753 := bstep (se 2 (by rfl) ⟨6053532, by rfl⟩ : syracuseStep 16142753 = 12107065) B12107065
theorem B10761835 : Blo 2239435 10761835 := bstep (se 1 (by rfl) ⟨8071376, by rfl⟩ : syracuseStep 10761835 = 16142753) B16142753
theorem B14349113 : Blo 2239435 14349113 := bstep (se 2 (by rfl) ⟨5380917, by rfl⟩ : syracuseStep 14349113 = 10761835) B10761835
theorem B9566075 : Blo 2239435 9566075 := bstep (se 1 (by rfl) ⟨7174556, by rfl⟩ : syracuseStep 9566075 = 14349113) B14349113
theorem B6377383 : Blo 2239435 6377383 := bstep (se 1 (by rfl) ⟨4783037, by rfl⟩ : syracuseStep 6377383 = 9566075) B9566075
theorem B8503177 : Blo 2239435 8503177 := bstep (se 2 (by rfl) ⟨3188691, by rfl⟩ : syracuseStep 8503177 = 6377383) B6377383
theorem B11337569 : Blo 2239435 11337569 := bstep (se 2 (by rfl) ⟨4251588, by rfl⟩ : syracuseStep 11337569 = 8503177) B8503177
theorem B7558379 : Blo 2239435 7558379 := bstep (se 1 (by rfl) ⟨5668784, by rfl⟩ : syracuseStep 7558379 = 11337569) B11337569
theorem B5038919 : Blo 2239435 5038919 := bstep (se 1 (by rfl) ⟨3779189, by rfl⟩ : syracuseStep 5038919 = 7558379) B7558379
theorem B3359279 : Blo 2239435 3359279 := bstep (se 1 (by rfl) ⟨2519459, by rfl⟩ : syracuseStep 3359279 = 5038919) B5038919
theorem B2239519 : Blo 2239435 2239519 := bstep (se 1 (by rfl) ⟨1679639, by rfl⟩ : syracuseStep 2239519 = 3359279) B3359279
theorem B3359285 : Blo 2239435 3359285 := bbase (se 5 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 3359285 = 314933) (by norm_num)
theorem B2239523 : Blo 2239435 2239523 := bstep (se 1 (by rfl) ⟨1679642, by rfl⟩ : syracuseStep 2239523 = 3359285) B3359285
theorem B5668805 : Blo 2239435 5668805 := bbase (se 4 (by rfl) ⟨531450, by rfl⟩ : syracuseStep 5668805 = 1062901) (by norm_num)
theorem B3779203 : Blo 2239435 3779203 := bstep (se 1 (by rfl) ⟨2834402, by rfl⟩ : syracuseStep 3779203 = 5668805) B5668805
theorem B5038937 : Blo 2239435 5038937 := bstep (se 2 (by rfl) ⟨1889601, by rfl⟩ : syracuseStep 5038937 = 3779203) B3779203
theorem B3359291 : Blo 2239435 3359291 := bstep (se 1 (by rfl) ⟨2519468, by rfl⟩ : syracuseStep 3359291 = 5038937) B5038937
theorem B2239527 : Blo 2239435 2239527 := bstep (se 1 (by rfl) ⟨1679645, by rfl⟩ : syracuseStep 2239527 = 3359291) B3359291
theorem B2519473 : Blo 2239435 2519473 := bbase (se 2 (by rfl) ⟨944802, by rfl⟩ : syracuseStep 2519473 = 1889605) (by norm_num)
theorem B3359297 : Blo 2239435 3359297 := bstep (se 2 (by rfl) ⟨1259736, by rfl⟩ : syracuseStep 3359297 = 2519473) B2519473
theorem B2239531 : Blo 2239435 2239531 := bstep (se 1 (by rfl) ⟨1679648, by rfl⟩ : syracuseStep 2239531 = 3359297) B3359297
theorem B6377429 : Blo 2239435 6377429 := bbase (se 7 (by rfl) ⟨74735, by rfl⟩ : syracuseStep 6377429 = 149471) (by norm_num)
theorem B4251619 : Blo 2239435 4251619 := bstep (se 1 (by rfl) ⟨3188714, by rfl⟩ : syracuseStep 4251619 = 6377429) B6377429
theorem B5668825 : Blo 2239435 5668825 := bstep (se 2 (by rfl) ⟨2125809, by rfl⟩ : syracuseStep 5668825 = 4251619) B4251619
theorem B7558433 : Blo 2239435 7558433 := bstep (se 2 (by rfl) ⟨2834412, by rfl⟩ : syracuseStep 7558433 = 5668825) B5668825
theorem B5038955 : Blo 2239435 5038955 := bstep (se 1 (by rfl) ⟨3779216, by rfl⟩ : syracuseStep 5038955 = 7558433) B7558433
theorem B3359303 : Blo 2239435 3359303 := bstep (se 1 (by rfl) ⟨2519477, by rfl⟩ : syracuseStep 3359303 = 5038955) B5038955
theorem B2239535 : Blo 2239435 2239535 := bstep (se 1 (by rfl) ⟨1679651, by rfl⟩ : syracuseStep 2239535 = 3359303) B3359303
theorem B3359309 : Blo 2239435 3359309 := bbase (se 3 (by rfl) ⟨629870, by rfl⟩ : syracuseStep 3359309 = 1259741) (by norm_num)
theorem B2239539 : Blo 2239435 2239539 := bstep (se 1 (by rfl) ⟨1679654, by rfl⟩ : syracuseStep 2239539 = 3359309) B3359309
theorem B5038973 : Blo 2239435 5038973 := bbase (se 3 (by rfl) ⟨944807, by rfl⟩ : syracuseStep 5038973 = 1889615) (by norm_num)
theorem B3359315 : Blo 2239435 3359315 := bstep (se 1 (by rfl) ⟨2519486, by rfl⟩ : syracuseStep 3359315 = 5038973) B5038973
theorem B2239543 : Blo 2239435 2239543 := bstep (se 1 (by rfl) ⟨1679657, by rfl⟩ : syracuseStep 2239543 = 3359315) B3359315
theorem B3779237 : Blo 2239435 3779237 := bbase (se 4 (by rfl) ⟨354303, by rfl⟩ : syracuseStep 3779237 = 708607) (by norm_num)
theorem B2519491 : Blo 2239435 2519491 := bstep (se 1 (by rfl) ⟨1889618, by rfl⟩ : syracuseStep 2519491 = 3779237) B3779237
theorem B3359321 : Blo 2239435 3359321 := bstep (se 2 (by rfl) ⟨1259745, by rfl⟩ : syracuseStep 3359321 = 2519491) B2519491
theorem B2239547 : Blo 2239435 2239547 := bstep (se 1 (by rfl) ⟨1679660, by rfl⟩ : syracuseStep 2239547 = 3359321) B3359321
theorem B2391553 : Blo 2239435 2391553 := bbase (se 2 (by rfl) ⟨896832, by rfl⟩ : syracuseStep 2391553 = 1793665) (by norm_num)
theorem B3188737 : Blo 2239435 3188737 := bstep (se 2 (by rfl) ⟨1195776, by rfl⟩ : syracuseStep 3188737 = 2391553) B2391553
theorem B17006597 : Blo 2239435 17006597 := bstep (se 4 (by rfl) ⟨1594368, by rfl⟩ : syracuseStep 17006597 = 3188737) B3188737
theorem B11337731 : Blo 2239435 11337731 := bstep (se 1 (by rfl) ⟨8503298, by rfl⟩ : syracuseStep 11337731 = 17006597) B17006597
theorem B7558487 : Blo 2239435 7558487 := bstep (se 1 (by rfl) ⟨5668865, by rfl⟩ : syracuseStep 7558487 = 11337731) B11337731
theorem B5038991 : Blo 2239435 5038991 := bstep (se 1 (by rfl) ⟨3779243, by rfl⟩ : syracuseStep 5038991 = 7558487) B7558487
theorem B3359327 : Blo 2239435 3359327 := bstep (se 1 (by rfl) ⟨2519495, by rfl⟩ : syracuseStep 3359327 = 5038991) B5038991
theorem B2239551 : Blo 2239435 2239551 := bstep (se 1 (by rfl) ⟨1679663, by rfl⟩ : syracuseStep 2239551 = 3359327) B3359327
theorem B3359333 : Blo 2239435 3359333 := bbase (se 4 (by rfl) ⟨314937, by rfl⟩ : syracuseStep 3359333 = 629875) (by norm_num)
theorem B2239555 : Blo 2239435 2239555 := bstep (se 1 (by rfl) ⟨1679666, by rfl⟩ : syracuseStep 2239555 = 3359333) B3359333
theorem B3188749 : Blo 2239435 3188749 := bbase (se 3 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 3188749 = 1195781) (by norm_num)
theorem B4251665 : Blo 2239435 4251665 := bstep (se 2 (by rfl) ⟨1594374, by rfl⟩ : syracuseStep 4251665 = 3188749) B3188749
theorem B2834443 : Blo 2239435 2834443 := bstep (se 1 (by rfl) ⟨2125832, by rfl⟩ : syracuseStep 2834443 = 4251665) B4251665
theorem B3779257 : Blo 2239435 3779257 := bstep (se 2 (by rfl) ⟨1417221, by rfl⟩ : syracuseStep 3779257 = 2834443) B2834443
theorem B5039009 : Blo 2239435 5039009 := bstep (se 2 (by rfl) ⟨1889628, by rfl⟩ : syracuseStep 5039009 = 3779257) B3779257
theorem B3359339 : Blo 2239435 3359339 := bstep (se 1 (by rfl) ⟨2519504, by rfl⟩ : syracuseStep 3359339 = 5039009) B5039009
theorem B2239559 : Blo 2239435 2239559 := bstep (se 1 (by rfl) ⟨1679669, by rfl⟩ : syracuseStep 2239559 = 3359339) B3359339
theorem B2519509 : Blo 2239435 2519509 := bbase (se 7 (by rfl) ⟨29525, by rfl⟩ : syracuseStep 2519509 = 59051) (by norm_num)
theorem B3359345 : Blo 2239435 3359345 := bstep (se 2 (by rfl) ⟨1259754, by rfl⟩ : syracuseStep 3359345 = 2519509) B2519509
theorem B2239563 : Blo 2239435 2239563 := bstep (se 1 (by rfl) ⟨1679672, by rfl⟩ : syracuseStep 2239563 = 3359345) B3359345
theorem B2834453 : Blo 2239435 2834453 := bbase (se 6 (by rfl) ⟨66432, by rfl⟩ : syracuseStep 2834453 = 132865) (by norm_num)
theorem B7558541 : Blo 2239435 7558541 := bstep (se 3 (by rfl) ⟨1417226, by rfl⟩ : syracuseStep 7558541 = 2834453) B2834453
theorem B5039027 : Blo 2239435 5039027 := bstep (se 1 (by rfl) ⟨3779270, by rfl⟩ : syracuseStep 5039027 = 7558541) B7558541
theorem B3359351 : Blo 2239435 3359351 := bstep (se 1 (by rfl) ⟨2519513, by rfl⟩ : syracuseStep 3359351 = 5039027) B5039027
theorem B2239567 : Blo 2239435 2239567 := bstep (se 1 (by rfl) ⟨1679675, by rfl⟩ : syracuseStep 2239567 = 3359351) B3359351
theorem B3359357 : Blo 2239435 3359357 := bbase (se 3 (by rfl) ⟨629879, by rfl⟩ : syracuseStep 3359357 = 1259759) (by norm_num)
theorem B2239571 : Blo 2239435 2239571 := bstep (se 1 (by rfl) ⟨1679678, by rfl⟩ : syracuseStep 2239571 = 3359357) B3359357
theorem B5039045 : Blo 2239435 5039045 := bbase (se 4 (by rfl) ⟨472410, by rfl⟩ : syracuseStep 5039045 = 944821) (by norm_num)
theorem B3359363 : Blo 2239435 3359363 := bstep (se 1 (by rfl) ⟨2519522, by rfl⟩ : syracuseStep 3359363 = 5039045) B5039045
theorem B2239575 : Blo 2239435 2239575 := bstep (se 1 (by rfl) ⟨1679681, by rfl⟩ : syracuseStep 2239575 = 3359363) B3359363
theorem B4090861 : Blo 2239435 4090861 := bbase (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) (by norm_num)
theorem B5454481 : Blo 2239435 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B7272641 : Blo 2239435 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B4848427 : Blo 2239435 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B25858277 : Blo 2239435 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B17238851 : Blo 2239435 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B11492567 : Blo 2239435 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B7661711 : Blo 2239435 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B5107807 : Blo 2239435 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B6810409 : Blo 2239435 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B9080545 : Blo 2239435 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B12107393 : Blo 2239435 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B8071595 : Blo 2239435 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B5381063 : Blo 2239435 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B3587375 : Blo 2239435 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B9566333 : Blo 2239435 9566333 := bstep (se 3 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 9566333 = 3587375) B3587375
theorem B6377555 : Blo 2239435 6377555 := bstep (se 1 (by rfl) ⟨4783166, by rfl⟩ : syracuseStep 6377555 = 9566333) B9566333
theorem B4251703 : Blo 2239435 4251703 := bstep (se 1 (by rfl) ⟨3188777, by rfl⟩ : syracuseStep 4251703 = 6377555) B6377555
theorem B5668937 : Blo 2239435 5668937 := bstep (se 2 (by rfl) ⟨2125851, by rfl⟩ : syracuseStep 5668937 = 4251703) B4251703
theorem B3779291 : Blo 2239435 3779291 := bstep (se 1 (by rfl) ⟨2834468, by rfl⟩ : syracuseStep 3779291 = 5668937) B5668937
theorem B2519527 : Blo 2239435 2519527 := bstep (se 1 (by rfl) ⟨1889645, by rfl⟩ : syracuseStep 2519527 = 3779291) B3779291
theorem B3359369 : Blo 2239435 3359369 := bstep (se 2 (by rfl) ⟨1259763, by rfl⟩ : syracuseStep 3359369 = 2519527) B2519527
theorem B2239579 : Blo 2239435 2239579 := bstep (se 1 (by rfl) ⟨1679684, by rfl⟩ : syracuseStep 2239579 = 3359369) B3359369
theorem B11337893 : Blo 2239435 11337893 := bbase (se 4 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 11337893 = 2125855) (by norm_num)
theorem B7558595 : Blo 2239435 7558595 := bstep (se 1 (by rfl) ⟨5668946, by rfl⟩ : syracuseStep 7558595 = 11337893) B11337893
theorem B5039063 : Blo 2239435 5039063 := bstep (se 1 (by rfl) ⟨3779297, by rfl⟩ : syracuseStep 5039063 = 7558595) B7558595
theorem B3359375 : Blo 2239435 3359375 := bstep (se 1 (by rfl) ⟨2519531, by rfl⟩ : syracuseStep 3359375 = 5039063) B5039063
theorem B2239583 : Blo 2239435 2239583 := bstep (se 1 (by rfl) ⟨1679687, by rfl⟩ : syracuseStep 2239583 = 3359375) B3359375
theorem B3359381 : Blo 2239435 3359381 := bbase (se 6 (by rfl) ⟨78735, by rfl⟩ : syracuseStep 3359381 = 157471) (by norm_num)
theorem B2239587 : Blo 2239435 2239587 := bstep (se 1 (by rfl) ⟨1679690, by rfl⟩ : syracuseStep 2239587 = 3359381) B3359381
theorem B30646997 : Blo 2239435 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B20431331 : Blo 2239435 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B13620887 : Blo 2239435 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B9080591 : Blo 2239435 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B24214909 : Blo 2239435 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B32286545 : Blo 2239435 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B21524363 : Blo 2239435 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B14349575 : Blo 2239435 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B9566383 : Blo 2239435 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B12755177 : Blo 2239435 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B8503451 : Blo 2239435 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B5668967 : Blo 2239435 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B3779311 : Blo 2239435 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B5039081 : Blo 2239435 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B3359387 : Blo 2239435 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B2239591 : Blo 2239435 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B2519545 : Blo 2239435 2519545 := bbase (se 2 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 2519545 = 1889659) (by norm_num)
theorem B3359393 : Blo 2239435 3359393 := bstep (se 2 (by rfl) ⟨1259772, by rfl⟩ : syracuseStep 3359393 = 2519545) B2519545
theorem B2239595 : Blo 2239435 2239595 := bstep (se 1 (by rfl) ⟨1679696, by rfl⟩ : syracuseStep 2239595 = 3359393) B3359393
theorem B5107853 : Blo 2239435 5107853 := bbase (se 3 (by rfl) ⟨957722, by rfl⟩ : syracuseStep 5107853 = 1915445) (by norm_num)
theorem B3405235 : Blo 2239435 3405235 := bstep (se 1 (by rfl) ⟨2553926, by rfl⟩ : syracuseStep 3405235 = 5107853) B5107853
theorem B4540313 : Blo 2239435 4540313 := bstep (se 2 (by rfl) ⟨1702617, by rfl⟩ : syracuseStep 4540313 = 3405235) B3405235
theorem B3026875 : Blo 2239435 3026875 := bstep (se 1 (by rfl) ⟨2270156, by rfl⟩ : syracuseStep 3026875 = 4540313) B4540313
theorem B4035833 : Blo 2239435 4035833 := bstep (se 2 (by rfl) ⟨1513437, by rfl⟩ : syracuseStep 4035833 = 3026875) B3026875
theorem B2690555 : Blo 2239435 2690555 := bstep (se 1 (by rfl) ⟨2017916, by rfl⟩ : syracuseStep 2690555 = 4035833) B4035833
theorem B7174813 : Blo 2239435 7174813 := bstep (se 3 (by rfl) ⟨1345277, by rfl⟩ : syracuseStep 7174813 = 2690555) B2690555
theorem B9566417 : Blo 2239435 9566417 := bstep (se 2 (by rfl) ⟨3587406, by rfl⟩ : syracuseStep 9566417 = 7174813) B7174813
theorem B6377611 : Blo 2239435 6377611 := bstep (se 1 (by rfl) ⟨4783208, by rfl⟩ : syracuseStep 6377611 = 9566417) B9566417
theorem B8503481 : Blo 2239435 8503481 := bstep (se 2 (by rfl) ⟨3188805, by rfl⟩ : syracuseStep 8503481 = 6377611) B6377611
theorem B5668987 : Blo 2239435 5668987 := bstep (se 1 (by rfl) ⟨4251740, by rfl⟩ : syracuseStep 5668987 = 8503481) B8503481
theorem B7558649 : Blo 2239435 7558649 := bstep (se 2 (by rfl) ⟨2834493, by rfl⟩ : syracuseStep 7558649 = 5668987) B5668987
theorem B5039099 : Blo 2239435 5039099 := bstep (se 1 (by rfl) ⟨3779324, by rfl⟩ : syracuseStep 5039099 = 7558649) B7558649
theorem B3359399 : Blo 2239435 3359399 := bstep (se 1 (by rfl) ⟨2519549, by rfl⟩ : syracuseStep 3359399 = 5039099) B5039099
theorem B2239599 : Blo 2239435 2239599 := bstep (se 1 (by rfl) ⟨1679699, by rfl⟩ : syracuseStep 2239599 = 3359399) B3359399
theorem B3359405 : Blo 2239435 3359405 := bbase (se 3 (by rfl) ⟨629888, by rfl⟩ : syracuseStep 3359405 = 1259777) (by norm_num)
theorem B2239603 : Blo 2239435 2239603 := bstep (se 1 (by rfl) ⟨1679702, by rfl⟩ : syracuseStep 2239603 = 3359405) B3359405
theorem B5039117 : Blo 2239435 5039117 := bbase (se 3 (by rfl) ⟨944834, by rfl⟩ : syracuseStep 5039117 = 1889669) (by norm_num)
theorem B3359411 : Blo 2239435 3359411 := bstep (se 1 (by rfl) ⟨2519558, by rfl⟩ : syracuseStep 3359411 = 5039117) B5039117
theorem B2239607 : Blo 2239435 2239607 := bstep (se 1 (by rfl) ⟨1679705, by rfl⟩ : syracuseStep 2239607 = 3359411) B3359411
theorem B2834509 : Blo 2239435 2834509 := bbase (se 3 (by rfl) ⟨531470, by rfl⟩ : syracuseStep 2834509 = 1062941) (by norm_num)
theorem B3779345 : Blo 2239435 3779345 := bstep (se 2 (by rfl) ⟨1417254, by rfl⟩ : syracuseStep 3779345 = 2834509) B2834509
theorem B2519563 : Blo 2239435 2519563 := bstep (se 1 (by rfl) ⟨1889672, by rfl⟩ : syracuseStep 2519563 = 3779345) B3779345
theorem B3359417 : Blo 2239435 3359417 := bstep (se 2 (by rfl) ⟨1259781, by rfl⟩ : syracuseStep 3359417 = 2519563) B2519563
theorem B2239611 : Blo 2239435 2239611 := bstep (se 1 (by rfl) ⟨1679708, by rfl⟩ : syracuseStep 2239611 = 3359417) B3359417
theorem B62130901 : Blo 2239435 62130901 := bbase (se 7 (by rfl) ⟨728096, by rfl⟩ : syracuseStep 62130901 = 1456193) (by norm_num)
theorem B82841201 : Blo 2239435 82841201 := bstep (se 2 (by rfl) ⟨31065450, by rfl⟩ : syracuseStep 82841201 = 62130901) B62130901
theorem B55227467 : Blo 2239435 55227467 := bstep (se 1 (by rfl) ⟨41420600, by rfl⟩ : syracuseStep 55227467 = 82841201) B82841201
theorem B36818311 : Blo 2239435 36818311 := bstep (se 1 (by rfl) ⟨27613733, by rfl⟩ : syracuseStep 36818311 = 55227467) B55227467
theorem B49091081 : Blo 2239435 49091081 := bstep (se 2 (by rfl) ⟨18409155, by rfl⟩ : syracuseStep 49091081 = 36818311) B36818311
theorem B130909549 : Blo 2239435 130909549 := bstep (se 3 (by rfl) ⟨24545540, by rfl⟩ : syracuseStep 130909549 = 49091081) B49091081
theorem B174546065 : Blo 2239435 174546065 := bstep (se 2 (by rfl) ⟨65454774, by rfl⟩ : syracuseStep 174546065 = 130909549) B130909549
theorem B116364043 : Blo 2239435 116364043 := bstep (se 1 (by rfl) ⟨87273032, by rfl⟩ : syracuseStep 116364043 = 174546065) B174546065
theorem B155152057 : Blo 2239435 155152057 := bstep (se 2 (by rfl) ⟨58182021, by rfl⟩ : syracuseStep 155152057 = 116364043) B116364043
theorem B206869409 : Blo 2239435 206869409 := bstep (se 2 (by rfl) ⟨77576028, by rfl⟩ : syracuseStep 206869409 = 155152057) B155152057
theorem B137912939 : Blo 2239435 137912939 := bstep (se 1 (by rfl) ⟨103434704, by rfl⟩ : syracuseStep 137912939 = 206869409) B206869409
theorem B91941959 : Blo 2239435 91941959 := bstep (se 1 (by rfl) ⟨68956469, by rfl⟩ : syracuseStep 91941959 = 137912939) B137912939
theorem B61294639 : Blo 2239435 61294639 := bstep (se 1 (by rfl) ⟨45970979, by rfl⟩ : syracuseStep 61294639 = 91941959) B91941959
theorem B81726185 : Blo 2239435 81726185 := bstep (se 2 (by rfl) ⟨30647319, by rfl⟩ : syracuseStep 81726185 = 61294639) B61294639
theorem B54484123 : Blo 2239435 54484123 := bstep (se 1 (by rfl) ⟨40863092, by rfl⟩ : syracuseStep 54484123 = 81726185) B81726185
theorem B72645497 : Blo 2239435 72645497 := bstep (se 2 (by rfl) ⟨27242061, by rfl⟩ : syracuseStep 72645497 = 54484123) B54484123
theorem B48430331 : Blo 2239435 48430331 := bstep (se 1 (by rfl) ⟨36322748, by rfl⟩ : syracuseStep 48430331 = 72645497) B72645497
theorem B32286887 : Blo 2239435 32286887 := bstep (se 1 (by rfl) ⟨24215165, by rfl⟩ : syracuseStep 32286887 = 48430331) B48430331
theorem B21524591 : Blo 2239435 21524591 := bstep (se 1 (by rfl) ⟨16143443, by rfl⟩ : syracuseStep 21524591 = 32286887) B32286887
theorem B14349727 : Blo 2239435 14349727 := bstep (se 1 (by rfl) ⟨10762295, by rfl⟩ : syracuseStep 14349727 = 21524591) B21524591
theorem B19132969 : Blo 2239435 19132969 := bstep (se 2 (by rfl) ⟨7174863, by rfl⟩ : syracuseStep 19132969 = 14349727) B14349727
theorem B25510625 : Blo 2239435 25510625 := bstep (se 2 (by rfl) ⟨9566484, by rfl⟩ : syracuseStep 25510625 = 19132969) B19132969
theorem B17007083 : Blo 2239435 17007083 := bstep (se 1 (by rfl) ⟨12755312, by rfl⟩ : syracuseStep 17007083 = 25510625) B25510625
theorem B11338055 : Blo 2239435 11338055 := bstep (se 1 (by rfl) ⟨8503541, by rfl⟩ : syracuseStep 11338055 = 17007083) B17007083
theorem B7558703 : Blo 2239435 7558703 := bstep (se 1 (by rfl) ⟨5669027, by rfl⟩ : syracuseStep 7558703 = 11338055) B11338055
theorem B5039135 : Blo 2239435 5039135 := bstep (se 1 (by rfl) ⟨3779351, by rfl⟩ : syracuseStep 5039135 = 7558703) B7558703
theorem B3359423 : Blo 2239435 3359423 := bstep (se 1 (by rfl) ⟨2519567, by rfl⟩ : syracuseStep 3359423 = 5039135) B5039135
theorem B2239615 : Blo 2239435 2239615 := bstep (se 1 (by rfl) ⟨1679711, by rfl⟩ : syracuseStep 2239615 = 3359423) B3359423
theorem B3359429 : Blo 2239435 3359429 := bbase (se 4 (by rfl) ⟨314946, by rfl⟩ : syracuseStep 3359429 = 629893) (by norm_num)
theorem B2239619 : Blo 2239435 2239619 := bstep (se 1 (by rfl) ⟨1679714, by rfl⟩ : syracuseStep 2239619 = 3359429) B3359429
theorem B3779365 : Blo 2239435 3779365 := bbase (se 4 (by rfl) ⟨354315, by rfl⟩ : syracuseStep 3779365 = 708631) (by norm_num)
theorem B5039153 : Blo 2239435 5039153 := bstep (se 2 (by rfl) ⟨1889682, by rfl⟩ : syracuseStep 5039153 = 3779365) B3779365
theorem B3359435 : Blo 2239435 3359435 := bstep (se 1 (by rfl) ⟨2519576, by rfl⟩ : syracuseStep 3359435 = 5039153) B5039153
theorem B2239623 : Blo 2239435 2239623 := bstep (se 1 (by rfl) ⟨1679717, by rfl⟩ : syracuseStep 2239623 = 3359435) B3359435
theorem B2519581 : Blo 2239435 2519581 := bbase (se 3 (by rfl) ⟨472421, by rfl⟩ : syracuseStep 2519581 = 944843) (by norm_num)
theorem B3359441 : Blo 2239435 3359441 := bstep (se 2 (by rfl) ⟨1259790, by rfl⟩ : syracuseStep 3359441 = 2519581) B2519581
theorem B2239627 : Blo 2239435 2239627 := bstep (se 1 (by rfl) ⟨1679720, by rfl⟩ : syracuseStep 2239627 = 3359441) B3359441
theorem B7558757 : Blo 2239435 7558757 := bbase (se 4 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 7558757 = 1417267) (by norm_num)
theorem B5039171 : Blo 2239435 5039171 := bstep (se 1 (by rfl) ⟨3779378, by rfl⟩ : syracuseStep 5039171 = 7558757) B7558757
theorem B3359447 : Blo 2239435 3359447 := bstep (se 1 (by rfl) ⟨2519585, by rfl⟩ : syracuseStep 3359447 = 5039171) B5039171
theorem B2239631 : Blo 2239435 2239631 := bstep (se 1 (by rfl) ⟨1679723, by rfl⟩ : syracuseStep 2239631 = 3359447) B3359447
theorem B3359453 : Blo 2239435 3359453 := bbase (se 3 (by rfl) ⟨629897, by rfl⟩ : syracuseStep 3359453 = 1259795) (by norm_num)
theorem B2239635 : Blo 2239435 2239635 := bstep (se 1 (by rfl) ⟨1679726, by rfl⟩ : syracuseStep 2239635 = 3359453) B3359453
theorem B5039189 : Blo 2239435 5039189 := bbase (se 8 (by rfl) ⟨29526, by rfl⟩ : syracuseStep 5039189 = 59053) (by norm_num)
theorem B3359459 : Blo 2239435 3359459 := bstep (se 1 (by rfl) ⟨2519594, by rfl⟩ : syracuseStep 3359459 = 5039189) B5039189
theorem B2239639 : Blo 2239435 2239639 := bstep (se 1 (by rfl) ⟨1679729, by rfl⟩ : syracuseStep 2239639 = 3359459) B3359459
theorem B2270201 : Blo 2239435 2270201 := bbase (se 2 (by rfl) ⟨851325, by rfl⟩ : syracuseStep 2270201 = 1702651) (by norm_num)
theorem B6053869 : Blo 2239435 6053869 := bstep (se 3 (by rfl) ⟨1135100, by rfl⟩ : syracuseStep 6053869 = 2270201) B2270201
theorem B8071825 : Blo 2239435 8071825 := bstep (se 2 (by rfl) ⟨3026934, by rfl⟩ : syracuseStep 8071825 = 6053869) B6053869
theorem B10762433 : Blo 2239435 10762433 := bstep (se 2 (by rfl) ⟨4035912, by rfl⟩ : syracuseStep 10762433 = 8071825) B8071825
theorem B7174955 : Blo 2239435 7174955 := bstep (se 1 (by rfl) ⟨5381216, by rfl⟩ : syracuseStep 7174955 = 10762433) B10762433
theorem B4783303 : Blo 2239435 4783303 := bstep (se 1 (by rfl) ⟨3587477, by rfl⟩ : syracuseStep 4783303 = 7174955) B7174955
theorem B6377737 : Blo 2239435 6377737 := bstep (se 2 (by rfl) ⟨2391651, by rfl⟩ : syracuseStep 6377737 = 4783303) B4783303
theorem B8503649 : Blo 2239435 8503649 := bstep (se 2 (by rfl) ⟨3188868, by rfl⟩ : syracuseStep 8503649 = 6377737) B6377737
theorem B5669099 : Blo 2239435 5669099 := bstep (se 1 (by rfl) ⟨4251824, by rfl⟩ : syracuseStep 5669099 = 8503649) B8503649
theorem B3779399 : Blo 2239435 3779399 := bstep (se 1 (by rfl) ⟨2834549, by rfl⟩ : syracuseStep 3779399 = 5669099) B5669099
theorem B2519599 : Blo 2239435 2519599 := bstep (se 1 (by rfl) ⟨1889699, by rfl⟩ : syracuseStep 2519599 = 3779399) B3779399
theorem B3359465 : Blo 2239435 3359465 := bstep (se 2 (by rfl) ⟨1259799, by rfl⟩ : syracuseStep 3359465 = 2519599) B2519599
theorem B2239643 : Blo 2239435 2239643 := bstep (se 1 (by rfl) ⟨1679732, by rfl⟩ : syracuseStep 2239643 = 3359465) B3359465
theorem B2332577 : Blo 2239435 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B6220205 : Blo 2239435 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B4146803 : Blo 2239435 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B2764535 : Blo 2239435 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B7372093 : Blo 2239435 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B9829457 : Blo 2239435 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B6552971 : Blo 2239435 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B4368647 : Blo 2239435 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B2912431 : Blo 2239435 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B3883241 : Blo 2239435 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B10355309 : Blo 2239435 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B6903539 : Blo 2239435 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B4602359 : Blo 2239435 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B12272957 : Blo 2239435 12272957 := bstep (se 3 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 12272957 = 4602359) B4602359
theorem B8181971 : Blo 2239435 8181971 := bstep (se 1 (by rfl) ⟨6136478, by rfl⟩ : syracuseStep 8181971 = 12272957) B12272957
theorem B5454647 : Blo 2239435 5454647 := bstep (se 1 (by rfl) ⟨4090985, by rfl⟩ : syracuseStep 5454647 = 8181971) B8181971
theorem B3636431 : Blo 2239435 3636431 := bstep (se 1 (by rfl) ⟨2727323, by rfl⟩ : syracuseStep 3636431 = 5454647) B5454647
theorem B2424287 : Blo 2239435 2424287 := bstep (se 1 (by rfl) ⟨1818215, by rfl⟩ : syracuseStep 2424287 = 3636431) B3636431
theorem B6464765 : Blo 2239435 6464765 := bstep (se 3 (by rfl) ⟨1212143, by rfl⟩ : syracuseStep 6464765 = 2424287) B2424287
theorem B4309843 : Blo 2239435 4309843 := bstep (se 1 (by rfl) ⟨3232382, by rfl⟩ : syracuseStep 4309843 = 6464765) B6464765
theorem B5746457 : Blo 2239435 5746457 := bstep (se 2 (by rfl) ⟨2154921, by rfl⟩ : syracuseStep 5746457 = 4309843) B4309843
theorem B3830971 : Blo 2239435 3830971 := bstep (se 1 (by rfl) ⟨2873228, by rfl⟩ : syracuseStep 3830971 = 5746457) B5746457
theorem B5107961 : Blo 2239435 5107961 := bstep (se 2 (by rfl) ⟨1915485, by rfl⟩ : syracuseStep 5107961 = 3830971) B3830971
theorem B3405307 : Blo 2239435 3405307 := bstep (se 1 (by rfl) ⟨2553980, by rfl⟩ : syracuseStep 3405307 = 5107961) B5107961
theorem B4540409 : Blo 2239435 4540409 := bstep (se 2 (by rfl) ⟨1702653, by rfl⟩ : syracuseStep 4540409 = 3405307) B3405307
theorem B3026939 : Blo 2239435 3026939 := bstep (se 1 (by rfl) ⟨2270204, by rfl⟩ : syracuseStep 3026939 = 4540409) B4540409
theorem B32287349 : Blo 2239435 32287349 := bstep (se 5 (by rfl) ⟨1513469, by rfl⟩ : syracuseStep 32287349 = 3026939) B3026939
theorem B21524899 : Blo 2239435 21524899 := bstep (se 1 (by rfl) ⟨16143674, by rfl⟩ : syracuseStep 21524899 = 32287349) B32287349
theorem B28699865 : Blo 2239435 28699865 := bstep (se 2 (by rfl) ⟨10762449, by rfl⟩ : syracuseStep 28699865 = 21524899) B21524899
theorem B19133243 : Blo 2239435 19133243 := bstep (se 1 (by rfl) ⟨14349932, by rfl⟩ : syracuseStep 19133243 = 28699865) B28699865
theorem B12755495 : Blo 2239435 12755495 := bstep (se 1 (by rfl) ⟨9566621, by rfl⟩ : syracuseStep 12755495 = 19133243) B19133243
theorem B8503663 : Blo 2239435 8503663 := bstep (se 1 (by rfl) ⟨6377747, by rfl⟩ : syracuseStep 8503663 = 12755495) B12755495
theorem B11338217 : Blo 2239435 11338217 := bstep (se 2 (by rfl) ⟨4251831, by rfl⟩ : syracuseStep 11338217 = 8503663) B8503663
theorem B7558811 : Blo 2239435 7558811 := bstep (se 1 (by rfl) ⟨5669108, by rfl⟩ : syracuseStep 7558811 = 11338217) B11338217
theorem B5039207 : Blo 2239435 5039207 := bstep (se 1 (by rfl) ⟨3779405, by rfl⟩ : syracuseStep 5039207 = 7558811) B7558811
theorem B3359471 : Blo 2239435 3359471 := bstep (se 1 (by rfl) ⟨2519603, by rfl⟩ : syracuseStep 3359471 = 5039207) B5039207
theorem B2239647 : Blo 2239435 2239647 := bstep (se 1 (by rfl) ⟨1679735, by rfl⟩ : syracuseStep 2239647 = 3359471) B3359471
theorem B3359477 : Blo 2239435 3359477 := bbase (se 5 (by rfl) ⟨157475, by rfl⟩ : syracuseStep 3359477 = 314951) (by norm_num)
theorem B2239651 : Blo 2239435 2239651 := bstep (se 1 (by rfl) ⟨1679738, by rfl⟩ : syracuseStep 2239651 = 3359477) B3359477
theorem B5381245 : Blo 2239435 5381245 := bbase (se 3 (by rfl) ⟨1008983, by rfl⟩ : syracuseStep 5381245 = 2017967) (by norm_num)
theorem B7174993 : Blo 2239435 7174993 := bstep (se 2 (by rfl) ⟨2690622, by rfl⟩ : syracuseStep 7174993 = 5381245) B5381245
theorem B9566657 : Blo 2239435 9566657 := bstep (se 2 (by rfl) ⟨3587496, by rfl⟩ : syracuseStep 9566657 = 7174993) B7174993
theorem B6377771 : Blo 2239435 6377771 := bstep (se 1 (by rfl) ⟨4783328, by rfl⟩ : syracuseStep 6377771 = 9566657) B9566657
theorem B4251847 : Blo 2239435 4251847 := bstep (se 1 (by rfl) ⟨3188885, by rfl⟩ : syracuseStep 4251847 = 6377771) B6377771
theorem B5669129 : Blo 2239435 5669129 := bstep (se 2 (by rfl) ⟨2125923, by rfl⟩ : syracuseStep 5669129 = 4251847) B4251847
theorem B3779419 : Blo 2239435 3779419 := bstep (se 1 (by rfl) ⟨2834564, by rfl⟩ : syracuseStep 3779419 = 5669129) B5669129
theorem B5039225 : Blo 2239435 5039225 := bstep (se 2 (by rfl) ⟨1889709, by rfl⟩ : syracuseStep 5039225 = 3779419) B3779419
theorem B3359483 : Blo 2239435 3359483 := bstep (se 1 (by rfl) ⟨2519612, by rfl⟩ : syracuseStep 3359483 = 5039225) B5039225
theorem B2239655 : Blo 2239435 2239655 := bstep (se 1 (by rfl) ⟨1679741, by rfl⟩ : syracuseStep 2239655 = 3359483) B3359483
theorem B2519617 : Blo 2239435 2519617 := bbase (se 2 (by rfl) ⟨944856, by rfl⟩ : syracuseStep 2519617 = 1889713) (by norm_num)
theorem B3359489 : Blo 2239435 3359489 := bstep (se 2 (by rfl) ⟨1259808, by rfl⟩ : syracuseStep 3359489 = 2519617) B2519617
theorem B2239659 : Blo 2239435 2239659 := bstep (se 1 (by rfl) ⟨1679744, by rfl⟩ : syracuseStep 2239659 = 3359489) B3359489
theorem B5669149 : Blo 2239435 5669149 := bbase (se 3 (by rfl) ⟨1062965, by rfl⟩ : syracuseStep 5669149 = 2125931) (by norm_num)
theorem B7558865 : Blo 2239435 7558865 := bstep (se 2 (by rfl) ⟨2834574, by rfl⟩ : syracuseStep 7558865 = 5669149) B5669149
theorem B5039243 : Blo 2239435 5039243 := bstep (se 1 (by rfl) ⟨3779432, by rfl⟩ : syracuseStep 5039243 = 7558865) B7558865
theorem B3359495 : Blo 2239435 3359495 := bstep (se 1 (by rfl) ⟨2519621, by rfl⟩ : syracuseStep 3359495 = 5039243) B5039243
theorem B2239663 : Blo 2239435 2239663 := bstep (se 1 (by rfl) ⟨1679747, by rfl⟩ : syracuseStep 2239663 = 3359495) B3359495
theorem B3359501 : Blo 2239435 3359501 := bbase (se 3 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 3359501 = 1259813) (by norm_num)
theorem B2239667 : Blo 2239435 2239667 := bstep (se 1 (by rfl) ⟨1679750, by rfl⟩ : syracuseStep 2239667 = 3359501) B3359501
theorem B5039261 : Blo 2239435 5039261 := bbase (se 3 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 5039261 = 1889723) (by norm_num)
theorem B3359507 : Blo 2239435 3359507 := bstep (se 1 (by rfl) ⟨2519630, by rfl⟩ : syracuseStep 3359507 = 5039261) B5039261
theorem B2239671 : Blo 2239435 2239671 := bstep (se 1 (by rfl) ⟨1679753, by rfl⟩ : syracuseStep 2239671 = 3359507) B3359507
theorem B3779453 : Blo 2239435 3779453 := bbase (se 3 (by rfl) ⟨708647, by rfl⟩ : syracuseStep 3779453 = 1417295) (by norm_num)
theorem B2519635 : Blo 2239435 2519635 := bstep (se 1 (by rfl) ⟨1889726, by rfl⟩ : syracuseStep 2519635 = 3779453) B3779453
theorem B3359513 : Blo 2239435 3359513 := bstep (se 2 (by rfl) ⟨1259817, by rfl⟩ : syracuseStep 3359513 = 2519635) B2519635
theorem B2239675 : Blo 2239435 2239675 := bstep (se 1 (by rfl) ⟨1679756, by rfl⟩ : syracuseStep 2239675 = 3359513) B3359513
theorem B7662053 : Blo 2239435 7662053 := bbase (se 4 (by rfl) ⟨718317, by rfl⟩ : syracuseStep 7662053 = 1436635) (by norm_num)
theorem B5108035 : Blo 2239435 5108035 := bstep (se 1 (by rfl) ⟨3831026, by rfl⟩ : syracuseStep 5108035 = 7662053) B7662053
theorem B6810713 : Blo 2239435 6810713 := bstep (se 2 (by rfl) ⟨2554017, by rfl⟩ : syracuseStep 6810713 = 5108035) B5108035
theorem B4540475 : Blo 2239435 4540475 := bstep (se 1 (by rfl) ⟨3405356, by rfl⟩ : syracuseStep 4540475 = 6810713) B6810713
theorem B3026983 : Blo 2239435 3026983 := bstep (se 1 (by rfl) ⟨2270237, by rfl⟩ : syracuseStep 3026983 = 4540475) B4540475
theorem B4035977 : Blo 2239435 4035977 := bstep (se 2 (by rfl) ⟨1513491, by rfl⟩ : syracuseStep 4035977 = 3026983) B3026983
theorem B2690651 : Blo 2239435 2690651 := bstep (se 1 (by rfl) ⟨2017988, by rfl⟩ : syracuseStep 2690651 = 4035977) B4035977
theorem B7175069 : Blo 2239435 7175069 := bstep (se 3 (by rfl) ⟨1345325, by rfl⟩ : syracuseStep 7175069 = 2690651) B2690651
theorem B4783379 : Blo 2239435 4783379 := bstep (se 1 (by rfl) ⟨3587534, by rfl⟩ : syracuseStep 4783379 = 7175069) B7175069
theorem B12755677 : Blo 2239435 12755677 := bstep (se 3 (by rfl) ⟨2391689, by rfl⟩ : syracuseStep 12755677 = 4783379) B4783379
theorem B17007569 : Blo 2239435 17007569 := bstep (se 2 (by rfl) ⟨6377838, by rfl⟩ : syracuseStep 17007569 = 12755677) B12755677
theorem B11338379 : Blo 2239435 11338379 := bstep (se 1 (by rfl) ⟨8503784, by rfl⟩ : syracuseStep 11338379 = 17007569) B17007569
theorem B7558919 : Blo 2239435 7558919 := bstep (se 1 (by rfl) ⟨5669189, by rfl⟩ : syracuseStep 7558919 = 11338379) B11338379
theorem B5039279 : Blo 2239435 5039279 := bstep (se 1 (by rfl) ⟨3779459, by rfl⟩ : syracuseStep 5039279 = 7558919) B7558919
theorem B3359519 : Blo 2239435 3359519 := bstep (se 1 (by rfl) ⟨2519639, by rfl⟩ : syracuseStep 3359519 = 5039279) B5039279
theorem B2239679 : Blo 2239435 2239679 := bstep (se 1 (by rfl) ⟨1679759, by rfl⟩ : syracuseStep 2239679 = 3359519) B3359519
theorem B3359525 : Blo 2239435 3359525 := bbase (se 4 (by rfl) ⟨314955, by rfl⟩ : syracuseStep 3359525 = 629911) (by norm_num)
theorem B2239683 : Blo 2239435 2239683 := bstep (se 1 (by rfl) ⟨1679762, by rfl⟩ : syracuseStep 2239683 = 3359525) B3359525
theorem B2834605 : Blo 2239435 2834605 := bbase (se 3 (by rfl) ⟨531488, by rfl⟩ : syracuseStep 2834605 = 1062977) (by norm_num)
theorem B3779473 : Blo 2239435 3779473 := bstep (se 2 (by rfl) ⟨1417302, by rfl⟩ : syracuseStep 3779473 = 2834605) B2834605
theorem B5039297 : Blo 2239435 5039297 := bstep (se 2 (by rfl) ⟨1889736, by rfl⟩ : syracuseStep 5039297 = 3779473) B3779473
theorem B3359531 : Blo 2239435 3359531 := bstep (se 1 (by rfl) ⟨2519648, by rfl⟩ : syracuseStep 3359531 = 5039297) B5039297
theorem B2239687 : Blo 2239435 2239687 := bstep (se 1 (by rfl) ⟨1679765, by rfl⟩ : syracuseStep 2239687 = 3359531) B3359531
theorem B2519653 : Blo 2239435 2519653 := bbase (se 4 (by rfl) ⟨236217, by rfl⟩ : syracuseStep 2519653 = 472435) (by norm_num)
theorem B3359537 : Blo 2239435 3359537 := bstep (se 2 (by rfl) ⟨1259826, by rfl⟩ : syracuseStep 3359537 = 2519653) B2519653
theorem B2239691 : Blo 2239435 2239691 := bstep (se 1 (by rfl) ⟨1679768, by rfl⟩ : syracuseStep 2239691 = 3359537) B3359537
theorem B3232453 : Blo 2239435 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B4309937 : Blo 2239435 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B2873291 : Blo 2239435 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B7662109 : Blo 2239435 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B10216145 : Blo 2239435 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B6810763 : Blo 2239435 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B9081017 : Blo 2239435 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B6054011 : Blo 2239435 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B4036007 : Blo 2239435 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B2690671 : Blo 2239435 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B3587561 : Blo 2239435 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B2391707 : Blo 2239435 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B6377885 : Blo 2239435 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B4251923 : Blo 2239435 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B2834615 : Blo 2239435 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B7558973 : Blo 2239435 7558973 := bstep (se 3 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 7558973 = 2834615) B2834615
theorem B5039315 : Blo 2239435 5039315 := bstep (se 1 (by rfl) ⟨3779486, by rfl⟩ : syracuseStep 5039315 = 7558973) B7558973
theorem B3359543 : Blo 2239435 3359543 := bstep (se 1 (by rfl) ⟨2519657, by rfl⟩ : syracuseStep 3359543 = 5039315) B5039315
theorem B2239695 : Blo 2239435 2239695 := bstep (se 1 (by rfl) ⟨1679771, by rfl⟩ : syracuseStep 2239695 = 3359543) B3359543
theorem B3359549 : Blo 2239435 3359549 := bbase (se 3 (by rfl) ⟨629915, by rfl⟩ : syracuseStep 3359549 = 1259831) (by norm_num)
theorem B2239699 : Blo 2239435 2239699 := bstep (se 1 (by rfl) ⟨1679774, by rfl⟩ : syracuseStep 2239699 = 3359549) B3359549
theorem B5039333 : Blo 2239435 5039333 := bbase (se 4 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 5039333 = 944875) (by norm_num)
theorem B3359555 : Blo 2239435 3359555 := bstep (se 1 (by rfl) ⟨2519666, by rfl⟩ : syracuseStep 3359555 = 5039333) B5039333
theorem B2239703 : Blo 2239435 2239703 := bstep (se 1 (by rfl) ⟨1679777, by rfl⟩ : syracuseStep 2239703 = 3359555) B3359555
theorem B5669261 : Blo 2239435 5669261 := bbase (se 3 (by rfl) ⟨1062986, by rfl⟩ : syracuseStep 5669261 = 2125973) (by norm_num)
theorem B3779507 : Blo 2239435 3779507 := bstep (se 1 (by rfl) ⟨2834630, by rfl⟩ : syracuseStep 3779507 = 5669261) B5669261
theorem B2519671 : Blo 2239435 2519671 := bstep (se 1 (by rfl) ⟨1889753, by rfl⟩ : syracuseStep 2519671 = 3779507) B3779507
theorem B3359561 : Blo 2239435 3359561 := bstep (se 2 (by rfl) ⟨1259835, by rfl⟩ : syracuseStep 3359561 = 2519671) B2519671
theorem B2239707 : Blo 2239435 2239707 := bstep (se 1 (by rfl) ⟨1679780, by rfl⟩ : syracuseStep 2239707 = 3359561) B3359561
theorem B3188965 : Blo 2239435 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B4251953 : Blo 2239435 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B11338541 : Blo 2239435 11338541 := bstep (se 3 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 11338541 = 4251953) B4251953
theorem B7559027 : Blo 2239435 7559027 := bstep (se 1 (by rfl) ⟨5669270, by rfl⟩ : syracuseStep 7559027 = 11338541) B11338541
theorem B5039351 : Blo 2239435 5039351 := bstep (se 1 (by rfl) ⟨3779513, by rfl⟩ : syracuseStep 5039351 = 7559027) B7559027
theorem B3359567 : Blo 2239435 3359567 := bstep (se 1 (by rfl) ⟨2519675, by rfl⟩ : syracuseStep 3359567 = 5039351) B5039351
theorem B2239711 : Blo 2239435 2239711 := bstep (se 1 (by rfl) ⟨1679783, by rfl⟩ : syracuseStep 2239711 = 3359567) B3359567
theorem B3359573 : Blo 2239435 3359573 := bbase (se 9 (by rfl) ⟨9842, by rfl⟩ : syracuseStep 3359573 = 19685) (by norm_num)
theorem B2239715 : Blo 2239435 2239715 := bstep (se 1 (by rfl) ⟨1679786, by rfl⟩ : syracuseStep 2239715 = 3359573) B3359573
theorem B12108149 : Blo 2239435 12108149 := bbase (se 5 (by rfl) ⟨567569, by rfl⟩ : syracuseStep 12108149 = 1135139) (by norm_num)
theorem B8072099 : Blo 2239435 8072099 := bstep (se 1 (by rfl) ⟨6054074, by rfl⟩ : syracuseStep 8072099 = 12108149) B12108149
theorem B5381399 : Blo 2239435 5381399 := bstep (se 1 (by rfl) ⟨4036049, by rfl⟩ : syracuseStep 5381399 = 8072099) B8072099
theorem B3587599 : Blo 2239435 3587599 := bstep (se 1 (by rfl) ⟨2690699, by rfl⟩ : syracuseStep 3587599 = 5381399) B5381399
theorem B4783465 : Blo 2239435 4783465 := bstep (se 2 (by rfl) ⟨1793799, by rfl⟩ : syracuseStep 4783465 = 3587599) B3587599
theorem B6377953 : Blo 2239435 6377953 := bstep (se 2 (by rfl) ⟨2391732, by rfl⟩ : syracuseStep 6377953 = 4783465) B4783465
theorem B8503937 : Blo 2239435 8503937 := bstep (se 2 (by rfl) ⟨3188976, by rfl⟩ : syracuseStep 8503937 = 6377953) B6377953
theorem B5669291 : Blo 2239435 5669291 := bstep (se 1 (by rfl) ⟨4251968, by rfl⟩ : syracuseStep 5669291 = 8503937) B8503937
theorem B3779527 : Blo 2239435 3779527 := bstep (se 1 (by rfl) ⟨2834645, by rfl⟩ : syracuseStep 3779527 = 5669291) B5669291
theorem B5039369 : Blo 2239435 5039369 := bstep (se 2 (by rfl) ⟨1889763, by rfl⟩ : syracuseStep 5039369 = 3779527) B3779527
theorem B3359579 : Blo 2239435 3359579 := bstep (se 1 (by rfl) ⟨2519684, by rfl⟩ : syracuseStep 3359579 = 5039369) B5039369
theorem B2239719 : Blo 2239435 2239719 := bstep (se 1 (by rfl) ⟨1679789, by rfl⟩ : syracuseStep 2239719 = 3359579) B3359579
theorem B2519689 : Blo 2239435 2519689 := bbase (se 2 (by rfl) ⟨944883, by rfl⟩ : syracuseStep 2519689 = 1889767) (by norm_num)
theorem B3359585 : Blo 2239435 3359585 := bstep (se 2 (by rfl) ⟨1259844, by rfl⟩ : syracuseStep 3359585 = 2519689) B2519689
theorem B2239723 : Blo 2239435 2239723 := bstep (se 1 (by rfl) ⟨1679792, by rfl⟩ : syracuseStep 2239723 = 3359585) B3359585
theorem B5177837 : Blo 2239435 5177837 := bbase (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) (by norm_num)
theorem B3451891 : Blo 2239435 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B4602521 : Blo 2239435 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B12273389 : Blo 2239435 12273389 := bstep (se 3 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 12273389 = 4602521) B4602521
theorem B8182259 : Blo 2239435 8182259 := bstep (se 1 (by rfl) ⟨6136694, by rfl⟩ : syracuseStep 8182259 = 12273389) B12273389
theorem B5454839 : Blo 2239435 5454839 := bstep (se 1 (by rfl) ⟨4091129, by rfl⟩ : syracuseStep 5454839 = 8182259) B8182259
theorem B3636559 : Blo 2239435 3636559 := bstep (se 1 (by rfl) ⟨2727419, by rfl⟩ : syracuseStep 3636559 = 5454839) B5454839
theorem B4848745 : Blo 2239435 4848745 := bstep (se 2 (by rfl) ⟨1818279, by rfl⟩ : syracuseStep 4848745 = 3636559) B3636559
theorem B6464993 : Blo 2239435 6464993 := bstep (se 2 (by rfl) ⟨2424372, by rfl⟩ : syracuseStep 6464993 = 4848745) B4848745
theorem B17239981 : Blo 2239435 17239981 := bstep (se 3 (by rfl) ⟨3232496, by rfl⟩ : syracuseStep 17239981 = 6464993) B6464993
theorem B22986641 : Blo 2239435 22986641 := bstep (se 2 (by rfl) ⟨8619990, by rfl⟩ : syracuseStep 22986641 = 17239981) B17239981
theorem B15324427 : Blo 2239435 15324427 := bstep (se 1 (by rfl) ⟨11493320, by rfl⟩ : syracuseStep 15324427 = 22986641) B22986641
theorem B20432569 : Blo 2239435 20432569 := bstep (se 2 (by rfl) ⟨7662213, by rfl⟩ : syracuseStep 20432569 = 15324427) B15324427
theorem B27243425 : Blo 2239435 27243425 := bstep (se 2 (by rfl) ⟨10216284, by rfl⟩ : syracuseStep 27243425 = 20432569) B20432569
theorem B72649133 : Blo 2239435 72649133 := bstep (se 3 (by rfl) ⟨13621712, by rfl⟩ : syracuseStep 72649133 = 27243425) B27243425
theorem B48432755 : Blo 2239435 48432755 := bstep (se 1 (by rfl) ⟨36324566, by rfl⟩ : syracuseStep 48432755 = 72649133) B72649133
theorem B32288503 : Blo 2239435 32288503 := bstep (se 1 (by rfl) ⟨24216377, by rfl⟩ : syracuseStep 32288503 = 48432755) B48432755
theorem B43051337 : Blo 2239435 43051337 := bstep (se 2 (by rfl) ⟨16144251, by rfl⟩ : syracuseStep 43051337 = 32288503) B32288503
theorem B28700891 : Blo 2239435 28700891 := bstep (se 1 (by rfl) ⟨21525668, by rfl⟩ : syracuseStep 28700891 = 43051337) B43051337
theorem B19133927 : Blo 2239435 19133927 := bstep (se 1 (by rfl) ⟨14350445, by rfl⟩ : syracuseStep 19133927 = 28700891) B28700891
theorem B12755951 : Blo 2239435 12755951 := bstep (se 1 (by rfl) ⟨9566963, by rfl⟩ : syracuseStep 12755951 = 19133927) B19133927
theorem B8503967 : Blo 2239435 8503967 := bstep (se 1 (by rfl) ⟨6377975, by rfl⟩ : syracuseStep 8503967 = 12755951) B12755951
theorem B5669311 : Blo 2239435 5669311 := bstep (se 1 (by rfl) ⟨4251983, by rfl⟩ : syracuseStep 5669311 = 8503967) B8503967
theorem B7559081 : Blo 2239435 7559081 := bstep (se 2 (by rfl) ⟨2834655, by rfl⟩ : syracuseStep 7559081 = 5669311) B5669311
theorem B5039387 : Blo 2239435 5039387 := bstep (se 1 (by rfl) ⟨3779540, by rfl⟩ : syracuseStep 5039387 = 7559081) B7559081
theorem B3359591 : Blo 2239435 3359591 := bstep (se 1 (by rfl) ⟨2519693, by rfl⟩ : syracuseStep 3359591 = 5039387) B5039387
theorem B2239727 : Blo 2239435 2239727 := bstep (se 1 (by rfl) ⟨1679795, by rfl⟩ : syracuseStep 2239727 = 3359591) B3359591
theorem B3359597 : Blo 2239435 3359597 := bbase (se 3 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 3359597 = 1259849) (by norm_num)
theorem B2239731 : Blo 2239435 2239731 := bstep (se 1 (by rfl) ⟨1679798, by rfl⟩ : syracuseStep 2239731 = 3359597) B3359597
theorem B5039405 : Blo 2239435 5039405 := bbase (se 3 (by rfl) ⟨944888, by rfl⟩ : syracuseStep 5039405 = 1889777) (by norm_num)
theorem B3359603 : Blo 2239435 3359603 := bstep (se 1 (by rfl) ⟨2519702, by rfl⟩ : syracuseStep 3359603 = 5039405) B5039405
theorem B2239735 : Blo 2239435 2239735 := bstep (se 1 (by rfl) ⟨1679801, by rfl⟩ : syracuseStep 2239735 = 3359603) B3359603
theorem B22986773 : Blo 2239435 22986773 := bbase (se 6 (by rfl) ⟨538752, by rfl⟩ : syracuseStep 22986773 = 1077505) (by norm_num)
theorem B15324515 : Blo 2239435 15324515 := bstep (se 1 (by rfl) ⟨11493386, by rfl⟩ : syracuseStep 15324515 = 22986773) B22986773
theorem B10216343 : Blo 2239435 10216343 := bstep (se 1 (by rfl) ⟨7662257, by rfl⟩ : syracuseStep 10216343 = 15324515) B15324515
theorem B6810895 : Blo 2239435 6810895 := bstep (se 1 (by rfl) ⟨5108171, by rfl⟩ : syracuseStep 6810895 = 10216343) B10216343
theorem B36324773 : Blo 2239435 36324773 := bstep (se 4 (by rfl) ⟨3405447, by rfl⟩ : syracuseStep 36324773 = 6810895) B6810895
theorem B24216515 : Blo 2239435 24216515 := bstep (se 1 (by rfl) ⟨18162386, by rfl⟩ : syracuseStep 24216515 = 36324773) B36324773
theorem B16144343 : Blo 2239435 16144343 := bstep (se 1 (by rfl) ⟨12108257, by rfl⟩ : syracuseStep 16144343 = 24216515) B24216515
theorem B10762895 : Blo 2239435 10762895 := bstep (se 1 (by rfl) ⟨8072171, by rfl⟩ : syracuseStep 10762895 = 16144343) B16144343
theorem B7175263 : Blo 2239435 7175263 := bstep (se 1 (by rfl) ⟨5381447, by rfl⟩ : syracuseStep 7175263 = 10762895) B10762895
theorem B9567017 : Blo 2239435 9567017 := bstep (se 2 (by rfl) ⟨3587631, by rfl⟩ : syracuseStep 9567017 = 7175263) B7175263
theorem B6378011 : Blo 2239435 6378011 := bstep (se 1 (by rfl) ⟨4783508, by rfl⟩ : syracuseStep 6378011 = 9567017) B9567017
theorem B4252007 : Blo 2239435 4252007 := bstep (se 1 (by rfl) ⟨3189005, by rfl⟩ : syracuseStep 4252007 = 6378011) B6378011
theorem B2834671 : Blo 2239435 2834671 := bstep (se 1 (by rfl) ⟨2126003, by rfl⟩ : syracuseStep 2834671 = 4252007) B4252007
theorem B3779561 : Blo 2239435 3779561 := bstep (se 2 (by rfl) ⟨1417335, by rfl⟩ : syracuseStep 3779561 = 2834671) B2834671
theorem B2519707 : Blo 2239435 2519707 := bstep (se 1 (by rfl) ⟨1889780, by rfl⟩ : syracuseStep 2519707 = 3779561) B3779561
theorem B3359609 : Blo 2239435 3359609 := bstep (se 2 (by rfl) ⟨1259853, by rfl⟩ : syracuseStep 3359609 = 2519707) B2519707
theorem B2239739 : Blo 2239435 2239739 := bstep (se 1 (by rfl) ⟨1679804, by rfl⟩ : syracuseStep 2239739 = 3359609) B3359609
theorem B4848781 : Blo 2239435 4848781 := bbase (se 3 (by rfl) ⟨909146, by rfl⟩ : syracuseStep 4848781 = 1818293) (by norm_num)
theorem B6465041 : Blo 2239435 6465041 := bstep (se 2 (by rfl) ⟨2424390, by rfl⟩ : syracuseStep 6465041 = 4848781) B4848781
theorem B4310027 : Blo 2239435 4310027 := bstep (se 1 (by rfl) ⟨3232520, by rfl⟩ : syracuseStep 4310027 = 6465041) B6465041
theorem B2873351 : Blo 2239435 2873351 := bstep (se 1 (by rfl) ⟨2155013, by rfl⟩ : syracuseStep 2873351 = 4310027) B4310027
theorem B7662269 : Blo 2239435 7662269 := bstep (se 3 (by rfl) ⟨1436675, by rfl⟩ : syracuseStep 7662269 = 2873351) B2873351
theorem B5108179 : Blo 2239435 5108179 := bstep (se 1 (by rfl) ⟨3831134, by rfl⟩ : syracuseStep 5108179 = 7662269) B7662269
theorem B6810905 : Blo 2239435 6810905 := bstep (se 2 (by rfl) ⟨2554089, by rfl⟩ : syracuseStep 6810905 = 5108179) B5108179
theorem B18162413 : Blo 2239435 18162413 := bstep (se 3 (by rfl) ⟨3405452, by rfl⟩ : syracuseStep 18162413 = 6810905) B6810905
theorem B12108275 : Blo 2239435 12108275 := bstep (se 1 (by rfl) ⟨9081206, by rfl⟩ : syracuseStep 12108275 = 18162413) B18162413
theorem B8072183 : Blo 2239435 8072183 := bstep (se 1 (by rfl) ⟨6054137, by rfl⟩ : syracuseStep 8072183 = 12108275) B12108275
theorem B21525821 : Blo 2239435 21525821 := bstep (se 3 (by rfl) ⟨4036091, by rfl⟩ : syracuseStep 21525821 = 8072183) B8072183
theorem B14350547 : Blo 2239435 14350547 := bstep (se 1 (by rfl) ⟨10762910, by rfl⟩ : syracuseStep 14350547 = 21525821) B21525821
theorem B38268125 : Blo 2239435 38268125 := bstep (se 3 (by rfl) ⟨7175273, by rfl⟩ : syracuseStep 38268125 = 14350547) B14350547
theorem B25512083 : Blo 2239435 25512083 := bstep (se 1 (by rfl) ⟨19134062, by rfl⟩ : syracuseStep 25512083 = 38268125) B38268125
theorem B17008055 : Blo 2239435 17008055 := bstep (se 1 (by rfl) ⟨12756041, by rfl⟩ : syracuseStep 17008055 = 25512083) B25512083
theorem B11338703 : Blo 2239435 11338703 := bstep (se 1 (by rfl) ⟨8504027, by rfl⟩ : syracuseStep 11338703 = 17008055) B17008055
theorem B7559135 : Blo 2239435 7559135 := bstep (se 1 (by rfl) ⟨5669351, by rfl⟩ : syracuseStep 7559135 = 11338703) B11338703
theorem B5039423 : Blo 2239435 5039423 := bstep (se 1 (by rfl) ⟨3779567, by rfl⟩ : syracuseStep 5039423 = 7559135) B7559135
theorem B3359615 : Blo 2239435 3359615 := bstep (se 1 (by rfl) ⟨2519711, by rfl⟩ : syracuseStep 3359615 = 5039423) B5039423
theorem B2239743 : Blo 2239435 2239743 := bstep (se 1 (by rfl) ⟨1679807, by rfl⟩ : syracuseStep 2239743 = 3359615) B3359615
theorem B3359621 : Blo 2239435 3359621 := bbase (se 4 (by rfl) ⟨314964, by rfl⟩ : syracuseStep 3359621 = 629929) (by norm_num)
theorem B2239747 : Blo 2239435 2239747 := bstep (se 1 (by rfl) ⟨1679810, by rfl⟩ : syracuseStep 2239747 = 3359621) B3359621
theorem B3779581 : Blo 2239435 3779581 := bbase (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) (by norm_num)
theorem B5039441 : Blo 2239435 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B3359627 : Blo 2239435 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B2239751 : Blo 2239435 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B2519725 : Blo 2239435 2519725 := bbase (se 3 (by rfl) ⟨472448, by rfl⟩ : syracuseStep 2519725 = 944897) (by norm_num)
theorem B3359633 : Blo 2239435 3359633 := bstep (se 2 (by rfl) ⟨1259862, by rfl⟩ : syracuseStep 3359633 = 2519725) B2519725
theorem B2239755 : Blo 2239435 2239755 := bstep (se 1 (by rfl) ⟨1679816, by rfl⟩ : syracuseStep 2239755 = 3359633) B3359633
theorem B7559189 : Blo 2239435 7559189 := bbase (se 6 (by rfl) ⟨177168, by rfl⟩ : syracuseStep 7559189 = 354337) (by norm_num)
theorem B5039459 : Blo 2239435 5039459 := bstep (se 1 (by rfl) ⟨3779594, by rfl⟩ : syracuseStep 5039459 = 7559189) B7559189
theorem B3359639 : Blo 2239435 3359639 := bstep (se 1 (by rfl) ⟨2519729, by rfl⟩ : syracuseStep 3359639 = 5039459) B5039459
theorem B2239759 : Blo 2239435 2239759 := bstep (se 1 (by rfl) ⟨1679819, by rfl⟩ : syracuseStep 2239759 = 3359639) B3359639
theorem B3359645 : Blo 2239435 3359645 := bbase (se 3 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 3359645 = 1259867) (by norm_num)
theorem B2239763 : Blo 2239435 2239763 := bstep (se 1 (by rfl) ⟨1679822, by rfl⟩ : syracuseStep 2239763 = 3359645) B3359645
theorem B5039477 : Blo 2239435 5039477 := bbase (se 5 (by rfl) ⟨236225, by rfl⟩ : syracuseStep 5039477 = 472451) (by norm_num)
theorem B3359651 : Blo 2239435 3359651 := bstep (se 1 (by rfl) ⟨2519738, by rfl⟩ : syracuseStep 3359651 = 5039477) B5039477
theorem B2239767 : Blo 2239435 2239767 := bstep (se 1 (by rfl) ⟨1679825, by rfl⟩ : syracuseStep 2239767 = 3359651) B3359651
theorem B8182421 : Blo 2239435 8182421 := bbase (se 6 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 8182421 = 383551) (by norm_num)
theorem B5454947 : Blo 2239435 5454947 := bstep (se 1 (by rfl) ⟨4091210, by rfl⟩ : syracuseStep 5454947 = 8182421) B8182421
theorem B3636631 : Blo 2239435 3636631 := bstep (se 1 (by rfl) ⟨2727473, by rfl⟩ : syracuseStep 3636631 = 5454947) B5454947
theorem B4848841 : Blo 2239435 4848841 := bstep (se 2 (by rfl) ⟨1818315, by rfl⟩ : syracuseStep 4848841 = 3636631) B3636631
theorem B25860485 : Blo 2239435 25860485 := bstep (se 4 (by rfl) ⟨2424420, by rfl⟩ : syracuseStep 25860485 = 4848841) B4848841
theorem B17240323 : Blo 2239435 17240323 := bstep (se 1 (by rfl) ⟨12930242, by rfl⟩ : syracuseStep 17240323 = 25860485) B25860485
theorem B22987097 : Blo 2239435 22987097 := bstep (se 2 (by rfl) ⟨8620161, by rfl⟩ : syracuseStep 22987097 = 17240323) B17240323
theorem B15324731 : Blo 2239435 15324731 := bstep (se 1 (by rfl) ⟨11493548, by rfl⟩ : syracuseStep 15324731 = 22987097) B22987097
theorem B10216487 : Blo 2239435 10216487 := bstep (se 1 (by rfl) ⟨7662365, by rfl⟩ : syracuseStep 10216487 = 15324731) B15324731
theorem B27243965 : Blo 2239435 27243965 := bstep (se 3 (by rfl) ⟨5108243, by rfl⟩ : syracuseStep 27243965 = 10216487) B10216487
theorem B18162643 : Blo 2239435 18162643 := bstep (se 1 (by rfl) ⟨13621982, by rfl⟩ : syracuseStep 18162643 = 27243965) B27243965
theorem B24216857 : Blo 2239435 24216857 := bstep (se 2 (by rfl) ⟨9081321, by rfl⟩ : syracuseStep 24216857 = 18162643) B18162643
theorem B16144571 : Blo 2239435 16144571 := bstep (se 1 (by rfl) ⟨12108428, by rfl⟩ : syracuseStep 16144571 = 24216857) B24216857
theorem B10763047 : Blo 2239435 10763047 := bstep (se 1 (by rfl) ⟨8072285, by rfl⟩ : syracuseStep 10763047 = 16144571) B16144571
theorem B14350729 : Blo 2239435 14350729 := bstep (se 2 (by rfl) ⟨5381523, by rfl⟩ : syracuseStep 14350729 = 10763047) B10763047
theorem B19134305 : Blo 2239435 19134305 := bstep (se 2 (by rfl) ⟨7175364, by rfl⟩ : syracuseStep 19134305 = 14350729) B14350729
theorem B12756203 : Blo 2239435 12756203 := bstep (se 1 (by rfl) ⟨9567152, by rfl⟩ : syracuseStep 12756203 = 19134305) B19134305
theorem B8504135 : Blo 2239435 8504135 := bstep (se 1 (by rfl) ⟨6378101, by rfl⟩ : syracuseStep 8504135 = 12756203) B12756203
theorem B5669423 : Blo 2239435 5669423 := bstep (se 1 (by rfl) ⟨4252067, by rfl⟩ : syracuseStep 5669423 = 8504135) B8504135
theorem B3779615 : Blo 2239435 3779615 := bstep (se 1 (by rfl) ⟨2834711, by rfl⟩ : syracuseStep 3779615 = 5669423) B5669423
theorem B2519743 : Blo 2239435 2519743 := bstep (se 1 (by rfl) ⟨1889807, by rfl⟩ : syracuseStep 2519743 = 3779615) B3779615
theorem B3359657 : Blo 2239435 3359657 := bstep (se 2 (by rfl) ⟨1259871, by rfl⟩ : syracuseStep 3359657 = 2519743) B2519743
theorem B2239771 : Blo 2239435 2239771 := bstep (se 1 (by rfl) ⟨1679828, by rfl⟩ : syracuseStep 2239771 = 3359657) B3359657
theorem B8504149 : Blo 2239435 8504149 := bbase (se 9 (by rfl) ⟨24914, by rfl⟩ : syracuseStep 8504149 = 49829) (by norm_num)
theorem B11338865 : Blo 2239435 11338865 := bstep (se 2 (by rfl) ⟨4252074, by rfl⟩ : syracuseStep 11338865 = 8504149) B8504149
theorem B7559243 : Blo 2239435 7559243 := bstep (se 1 (by rfl) ⟨5669432, by rfl⟩ : syracuseStep 7559243 = 11338865) B11338865
theorem B5039495 : Blo 2239435 5039495 := bstep (se 1 (by rfl) ⟨3779621, by rfl⟩ : syracuseStep 5039495 = 7559243) B7559243
theorem B3359663 : Blo 2239435 3359663 := bstep (se 1 (by rfl) ⟨2519747, by rfl⟩ : syracuseStep 3359663 = 5039495) B5039495
theorem B2239775 : Blo 2239435 2239775 := bstep (se 1 (by rfl) ⟨1679831, by rfl⟩ : syracuseStep 2239775 = 3359663) B3359663
theorem B3359669 : Blo 2239435 3359669 := bbase (se 5 (by rfl) ⟨157484, by rfl⟩ : syracuseStep 3359669 = 314969) (by norm_num)
theorem B2239779 : Blo 2239435 2239779 := bstep (se 1 (by rfl) ⟨1679834, by rfl⟩ : syracuseStep 2239779 = 3359669) B3359669
theorem B5669453 : Blo 2239435 5669453 := bbase (se 3 (by rfl) ⟨1063022, by rfl⟩ : syracuseStep 5669453 = 2126045) (by norm_num)
theorem B3779635 : Blo 2239435 3779635 := bstep (se 1 (by rfl) ⟨2834726, by rfl⟩ : syracuseStep 3779635 = 5669453) B5669453
theorem B5039513 : Blo 2239435 5039513 := bstep (se 2 (by rfl) ⟨1889817, by rfl⟩ : syracuseStep 5039513 = 3779635) B3779635
theorem B3359675 : Blo 2239435 3359675 := bstep (se 1 (by rfl) ⟨2519756, by rfl⟩ : syracuseStep 3359675 = 5039513) B5039513
theorem B2239783 : Blo 2239435 2239783 := bstep (se 1 (by rfl) ⟨1679837, by rfl⟩ : syracuseStep 2239783 = 3359675) B3359675
theorem B2519761 : Blo 2239435 2519761 := bbase (se 2 (by rfl) ⟨944910, by rfl⟩ : syracuseStep 2519761 = 1889821) (by norm_num)
theorem B3359681 : Blo 2239435 3359681 := bstep (se 2 (by rfl) ⟨1259880, by rfl⟩ : syracuseStep 3359681 = 2519761) B2519761
theorem B2239787 : Blo 2239435 2239787 := bstep (se 1 (by rfl) ⟨1679840, by rfl⟩ : syracuseStep 2239787 = 3359681) B3359681
theorem B7175429 : Blo 2239435 7175429 := bbase (se 4 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 7175429 = 1345393) (by norm_num)
theorem B4783619 : Blo 2239435 4783619 := bstep (se 1 (by rfl) ⟨3587714, by rfl⟩ : syracuseStep 4783619 = 7175429) B7175429
theorem B3189079 : Blo 2239435 3189079 := bstep (se 1 (by rfl) ⟨2391809, by rfl⟩ : syracuseStep 3189079 = 4783619) B4783619
theorem B4252105 : Blo 2239435 4252105 := bstep (se 2 (by rfl) ⟨1594539, by rfl⟩ : syracuseStep 4252105 = 3189079) B3189079
theorem B5669473 : Blo 2239435 5669473 := bstep (se 2 (by rfl) ⟨2126052, by rfl⟩ : syracuseStep 5669473 = 4252105) B4252105
theorem B7559297 : Blo 2239435 7559297 := bstep (se 2 (by rfl) ⟨2834736, by rfl⟩ : syracuseStep 7559297 = 5669473) B5669473
theorem B5039531 : Blo 2239435 5039531 := bstep (se 1 (by rfl) ⟨3779648, by rfl⟩ : syracuseStep 5039531 = 7559297) B7559297
theorem B3359687 : Blo 2239435 3359687 := bstep (se 1 (by rfl) ⟨2519765, by rfl⟩ : syracuseStep 3359687 = 5039531) B5039531
theorem B2239791 : Blo 2239435 2239791 := bstep (se 1 (by rfl) ⟨1679843, by rfl⟩ : syracuseStep 2239791 = 3359687) B3359687
theorem B3359693 : Blo 2239435 3359693 := bbase (se 3 (by rfl) ⟨629942, by rfl⟩ : syracuseStep 3359693 = 1259885) (by norm_num)
theorem B2239795 : Blo 2239435 2239795 := bstep (se 1 (by rfl) ⟨1679846, by rfl⟩ : syracuseStep 2239795 = 3359693) B3359693
theorem B5039549 : Blo 2239435 5039549 := bbase (se 3 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 5039549 = 1889831) (by norm_num)
theorem B3359699 : Blo 2239435 3359699 := bstep (se 1 (by rfl) ⟨2519774, by rfl⟩ : syracuseStep 3359699 = 5039549) B5039549
theorem B2239799 : Blo 2239435 2239799 := bstep (se 1 (by rfl) ⟨1679849, by rfl⟩ : syracuseStep 2239799 = 3359699) B3359699
theorem B3779669 : Blo 2239435 3779669 := bbase (se 8 (by rfl) ⟨22146, by rfl⟩ : syracuseStep 3779669 = 44293) (by norm_num)
theorem B2519779 : Blo 2239435 2519779 := bstep (se 1 (by rfl) ⟨1889834, by rfl⟩ : syracuseStep 2519779 = 3779669) B3779669
theorem B3359705 : Blo 2239435 3359705 := bstep (se 2 (by rfl) ⟨1259889, by rfl⟩ : syracuseStep 3359705 = 2519779) B2519779
theorem B2239803 : Blo 2239435 2239803 := bstep (se 1 (by rfl) ⟨1679852, by rfl⟩ : syracuseStep 2239803 = 3359705) B3359705
theorem B11493733 : Blo 2239435 11493733 := bbase (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) (by norm_num)
theorem B15324977 : Blo 2239435 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B10216651 : Blo 2239435 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B13622201 : Blo 2239435 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B9081467 : Blo 2239435 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B6054311 : Blo 2239435 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B16144829 : Blo 2239435 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B10763219 : Blo 2239435 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B7175479 : Blo 2239435 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B9567305 : Blo 2239435 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B6378203 : Blo 2239435 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B17008541 : Blo 2239435 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B11339027 : Blo 2239435 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B7559351 : Blo 2239435 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B5039567 : Blo 2239435 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B3359711 : Blo 2239435 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B2239807 : Blo 2239435 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B3359717 : Blo 2239435 3359717 := bbase (se 4 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 3359717 = 629947) (by norm_num)
theorem B2239811 : Blo 2239435 2239811 := bstep (se 1 (by rfl) ⟨1679858, by rfl⟩ : syracuseStep 2239811 = 3359717) B3359717
theorem B31068245 : Blo 2239435 31068245 := bbase (se 8 (by rfl) ⟨182040, by rfl⟩ : syracuseStep 31068245 = 364081) (by norm_num)
theorem B82848653 : Blo 2239435 82848653 := bstep (se 3 (by rfl) ⟨15534122, by rfl⟩ : syracuseStep 82848653 = 31068245) B31068245
theorem B55232435 : Blo 2239435 55232435 := bstep (se 1 (by rfl) ⟨41424326, by rfl⟩ : syracuseStep 55232435 = 82848653) B82848653
theorem B36821623 : Blo 2239435 36821623 := bstep (se 1 (by rfl) ⟨27616217, by rfl⟩ : syracuseStep 36821623 = 55232435) B55232435
theorem B49095497 : Blo 2239435 49095497 := bstep (se 2 (by rfl) ⟨18410811, by rfl⟩ : syracuseStep 49095497 = 36821623) B36821623
theorem B32730331 : Blo 2239435 32730331 := bstep (se 1 (by rfl) ⟨24547748, by rfl⟩ : syracuseStep 32730331 = 49095497) B49095497
theorem B43640441 : Blo 2239435 43640441 := bstep (se 2 (by rfl) ⟨16365165, by rfl⟩ : syracuseStep 43640441 = 32730331) B32730331
theorem B29093627 : Blo 2239435 29093627 := bstep (se 1 (by rfl) ⟨21820220, by rfl⟩ : syracuseStep 29093627 = 43640441) B43640441
theorem B77583005 : Blo 2239435 77583005 := bstep (se 3 (by rfl) ⟨14546813, by rfl⟩ : syracuseStep 77583005 = 29093627) B29093627
theorem B51722003 : Blo 2239435 51722003 := bstep (se 1 (by rfl) ⟨38791502, by rfl⟩ : syracuseStep 51722003 = 77583005) B77583005
theorem B34481335 : Blo 2239435 34481335 := bstep (se 1 (by rfl) ⟨25861001, by rfl⟩ : syracuseStep 34481335 = 51722003) B51722003
theorem B45975113 : Blo 2239435 45975113 := bstep (se 2 (by rfl) ⟨17240667, by rfl⟩ : syracuseStep 45975113 = 34481335) B34481335
theorem B30650075 : Blo 2239435 30650075 := bstep (se 1 (by rfl) ⟨22987556, by rfl⟩ : syracuseStep 30650075 = 45975113) B45975113
theorem B20433383 : Blo 2239435 20433383 := bstep (se 1 (by rfl) ⟨15325037, by rfl⟩ : syracuseStep 20433383 = 30650075) B30650075
theorem B13622255 : Blo 2239435 13622255 := bstep (se 1 (by rfl) ⟨10216691, by rfl⟩ : syracuseStep 13622255 = 20433383) B20433383
theorem B9081503 : Blo 2239435 9081503 := bstep (se 1 (by rfl) ⟨6811127, by rfl⟩ : syracuseStep 9081503 = 13622255) B13622255
theorem B6054335 : Blo 2239435 6054335 := bstep (se 1 (by rfl) ⟨4540751, by rfl⟩ : syracuseStep 6054335 = 9081503) B9081503
theorem B4036223 : Blo 2239435 4036223 := bstep (se 1 (by rfl) ⟨3027167, by rfl⟩ : syracuseStep 4036223 = 6054335) B6054335
theorem B2690815 : Blo 2239435 2690815 := bstep (se 1 (by rfl) ⟨2018111, by rfl⟩ : syracuseStep 2690815 = 4036223) B4036223
theorem B3587753 : Blo 2239435 3587753 := bstep (se 2 (by rfl) ⟨1345407, by rfl⟩ : syracuseStep 3587753 = 2690815) B2690815
theorem B9567341 : Blo 2239435 9567341 := bstep (se 3 (by rfl) ⟨1793876, by rfl⟩ : syracuseStep 9567341 = 3587753) B3587753
theorem B6378227 : Blo 2239435 6378227 := bstep (se 1 (by rfl) ⟨4783670, by rfl⟩ : syracuseStep 6378227 = 9567341) B9567341
theorem B4252151 : Blo 2239435 4252151 := bstep (se 1 (by rfl) ⟨3189113, by rfl⟩ : syracuseStep 4252151 = 6378227) B6378227
theorem B2834767 : Blo 2239435 2834767 := bstep (se 1 (by rfl) ⟨2126075, by rfl⟩ : syracuseStep 2834767 = 4252151) B4252151
theorem B3779689 : Blo 2239435 3779689 := bstep (se 2 (by rfl) ⟨1417383, by rfl⟩ : syracuseStep 3779689 = 2834767) B2834767
theorem B5039585 : Blo 2239435 5039585 := bstep (se 2 (by rfl) ⟨1889844, by rfl⟩ : syracuseStep 5039585 = 3779689) B3779689
theorem B3359723 : Blo 2239435 3359723 := bstep (se 1 (by rfl) ⟨2519792, by rfl⟩ : syracuseStep 3359723 = 5039585) B5039585
theorem B2239815 : Blo 2239435 2239815 := bstep (se 1 (by rfl) ⟨1679861, by rfl⟩ : syracuseStep 2239815 = 3359723) B3359723
theorem B2519797 : Blo 2239435 2519797 := bbase (se 5 (by rfl) ⟨118115, by rfl⟩ : syracuseStep 2519797 = 236231) (by norm_num)
theorem B3359729 : Blo 2239435 3359729 := bstep (se 2 (by rfl) ⟨1259898, by rfl⟩ : syracuseStep 3359729 = 2519797) B2519797
theorem B2239819 : Blo 2239435 2239819 := bstep (se 1 (by rfl) ⟨1679864, by rfl⟩ : syracuseStep 2239819 = 3359729) B3359729
theorem B2834777 : Blo 2239435 2834777 := bbase (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) (by norm_num)
theorem B7559405 : Blo 2239435 7559405 := bstep (se 3 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 7559405 = 2834777) B2834777
theorem B5039603 : Blo 2239435 5039603 := bstep (se 1 (by rfl) ⟨3779702, by rfl⟩ : syracuseStep 5039603 = 7559405) B7559405
theorem B3359735 : Blo 2239435 3359735 := bstep (se 1 (by rfl) ⟨2519801, by rfl⟩ : syracuseStep 3359735 = 5039603) B5039603
theorem B2239823 : Blo 2239435 2239823 := bstep (se 1 (by rfl) ⟨1679867, by rfl⟩ : syracuseStep 2239823 = 3359735) B3359735
theorem B3359741 : Blo 2239435 3359741 := bbase (se 3 (by rfl) ⟨629951, by rfl⟩ : syracuseStep 3359741 = 1259903) (by norm_num)
theorem B2239827 : Blo 2239435 2239827 := bstep (se 1 (by rfl) ⟨1679870, by rfl⟩ : syracuseStep 2239827 = 3359741) B3359741
theorem B5039621 : Blo 2239435 5039621 := bbase (se 4 (by rfl) ⟨472464, by rfl⟩ : syracuseStep 5039621 = 944929) (by norm_num)
theorem B3359747 : Blo 2239435 3359747 := bstep (se 1 (by rfl) ⟨2519810, by rfl⟩ : syracuseStep 3359747 = 5039621) B5039621
theorem B2239831 : Blo 2239435 2239831 := bstep (se 1 (by rfl) ⟨1679873, by rfl⟩ : syracuseStep 2239831 = 3359747) B3359747
theorem B4252189 : Blo 2239435 4252189 := bbase (se 3 (by rfl) ⟨797285, by rfl⟩ : syracuseStep 4252189 = 1594571) (by norm_num)
theorem B5669585 : Blo 2239435 5669585 := bstep (se 2 (by rfl) ⟨2126094, by rfl⟩ : syracuseStep 5669585 = 4252189) B4252189
theorem B3779723 : Blo 2239435 3779723 := bstep (se 1 (by rfl) ⟨2834792, by rfl⟩ : syracuseStep 3779723 = 5669585) B5669585
theorem B2519815 : Blo 2239435 2519815 := bstep (se 1 (by rfl) ⟨1889861, by rfl⟩ : syracuseStep 2519815 = 3779723) B3779723
theorem B3359753 : Blo 2239435 3359753 := bstep (se 2 (by rfl) ⟨1259907, by rfl⟩ : syracuseStep 3359753 = 2519815) B2519815
theorem B2239835 : Blo 2239435 2239835 := bstep (se 1 (by rfl) ⟨1679876, by rfl⟩ : syracuseStep 2239835 = 3359753) B3359753
theorem B11339189 : Blo 2239435 11339189 := bbase (se 5 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 11339189 = 1063049) (by norm_num)
theorem B7559459 : Blo 2239435 7559459 := bstep (se 1 (by rfl) ⟨5669594, by rfl⟩ : syracuseStep 7559459 = 11339189) B11339189
theorem B5039639 : Blo 2239435 5039639 := bstep (se 1 (by rfl) ⟨3779729, by rfl⟩ : syracuseStep 5039639 = 7559459) B7559459
theorem B3359759 : Blo 2239435 3359759 := bstep (se 1 (by rfl) ⟨2519819, by rfl⟩ : syracuseStep 3359759 = 5039639) B5039639
theorem B2239839 : Blo 2239435 2239839 := bstep (se 1 (by rfl) ⟨1679879, by rfl⟩ : syracuseStep 2239839 = 3359759) B3359759
theorem B3359765 : Blo 2239435 3359765 := bbase (se 6 (by rfl) ⟨78744, by rfl⟩ : syracuseStep 3359765 = 157489) (by norm_num)
theorem B2239843 : Blo 2239435 2239843 := bstep (se 1 (by rfl) ⟨1679882, by rfl⟩ : syracuseStep 2239843 = 3359765) B3359765
theorem B8620453 : Blo 2239435 8620453 := bbase (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) (by norm_num)
theorem B11493937 : Blo 2239435 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B15325249 : Blo 2239435 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B20433665 : Blo 2239435 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B54489773 : Blo 2239435 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B36326515 : Blo 2239435 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B48435353 : Blo 2239435 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B32290235 : Blo 2239435 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B21526823 : Blo 2239435 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B14351215 : Blo 2239435 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B19134953 : Blo 2239435 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B12756635 : Blo 2239435 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B8504423 : Blo 2239435 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B5669615 : Blo 2239435 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B3779743 : Blo 2239435 3779743 := bstep (se 1 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 3779743 = 5669615) B5669615
theorem B5039657 : Blo 2239435 5039657 := bstep (se 2 (by rfl) ⟨1889871, by rfl⟩ : syracuseStep 5039657 = 3779743) B3779743
theorem B3359771 : Blo 2239435 3359771 := bstep (se 1 (by rfl) ⟨2519828, by rfl⟩ : syracuseStep 3359771 = 5039657) B5039657
theorem B2239847 : Blo 2239435 2239847 := bstep (se 1 (by rfl) ⟨1679885, by rfl⟩ : syracuseStep 2239847 = 3359771) B3359771
theorem B2519833 : Blo 2239435 2519833 := bbase (se 2 (by rfl) ⟨944937, by rfl⟩ : syracuseStep 2519833 = 1889875) (by norm_num)
theorem B3359777 : Blo 2239435 3359777 := bstep (se 2 (by rfl) ⟨1259916, by rfl⟩ : syracuseStep 3359777 = 2519833) B2519833
theorem B2239851 : Blo 2239435 2239851 := bstep (se 1 (by rfl) ⟨1679888, by rfl⟩ : syracuseStep 2239851 = 3359777) B3359777
theorem B8504453 : Blo 2239435 8504453 := bbase (se 4 (by rfl) ⟨797292, by rfl⟩ : syracuseStep 8504453 = 1594585) (by norm_num)
theorem B5669635 : Blo 2239435 5669635 := bstep (se 1 (by rfl) ⟨4252226, by rfl⟩ : syracuseStep 5669635 = 8504453) B8504453
theorem B7559513 : Blo 2239435 7559513 := bstep (se 2 (by rfl) ⟨2834817, by rfl⟩ : syracuseStep 7559513 = 5669635) B5669635
theorem B5039675 : Blo 2239435 5039675 := bstep (se 1 (by rfl) ⟨3779756, by rfl⟩ : syracuseStep 5039675 = 7559513) B7559513
theorem B3359783 : Blo 2239435 3359783 := bstep (se 1 (by rfl) ⟨2519837, by rfl⟩ : syracuseStep 3359783 = 5039675) B5039675
theorem B2239855 : Blo 2239435 2239855 := bstep (se 1 (by rfl) ⟨1679891, by rfl⟩ : syracuseStep 2239855 = 3359783) B3359783
theorem B3359789 : Blo 2239435 3359789 := bbase (se 3 (by rfl) ⟨629960, by rfl⟩ : syracuseStep 3359789 = 1259921) (by norm_num)
theorem B2239859 : Blo 2239435 2239859 := bstep (se 1 (by rfl) ⟨1679894, by rfl⟩ : syracuseStep 2239859 = 3359789) B3359789
theorem B5039693 : Blo 2239435 5039693 := bbase (se 3 (by rfl) ⟨944942, by rfl⟩ : syracuseStep 5039693 = 1889885) (by norm_num)
theorem B3359795 : Blo 2239435 3359795 := bstep (se 1 (by rfl) ⟨2519846, by rfl⟩ : syracuseStep 3359795 = 5039693) B5039693
theorem B2239863 : Blo 2239435 2239863 := bstep (se 1 (by rfl) ⟨1679897, by rfl⟩ : syracuseStep 2239863 = 3359795) B3359795
theorem B2834833 : Blo 2239435 2834833 := bbase (se 2 (by rfl) ⟨1063062, by rfl⟩ : syracuseStep 2834833 = 2126125) (by norm_num)
theorem B3779777 : Blo 2239435 3779777 := bstep (se 2 (by rfl) ⟨1417416, by rfl⟩ : syracuseStep 3779777 = 2834833) B2834833
theorem B2519851 : Blo 2239435 2519851 := bstep (se 1 (by rfl) ⟨1889888, by rfl⟩ : syracuseStep 2519851 = 3779777) B3779777
theorem B3359801 : Blo 2239435 3359801 := bstep (se 2 (by rfl) ⟨1259925, by rfl⟩ : syracuseStep 3359801 = 2519851) B2519851
theorem B2239867 : Blo 2239435 2239867 := bstep (se 1 (by rfl) ⟨1679900, by rfl⟩ : syracuseStep 2239867 = 3359801) B3359801
theorem B4783789 : Blo 2239435 4783789 := bbase (se 3 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 4783789 = 1793921) (by norm_num)
theorem B25513541 : Blo 2239435 25513541 := bstep (se 4 (by rfl) ⟨2391894, by rfl⟩ : syracuseStep 25513541 = 4783789) B4783789
theorem B17009027 : Blo 2239435 17009027 := bstep (se 1 (by rfl) ⟨12756770, by rfl⟩ : syracuseStep 17009027 = 25513541) B25513541
theorem B11339351 : Blo 2239435 11339351 := bstep (se 1 (by rfl) ⟨8504513, by rfl⟩ : syracuseStep 11339351 = 17009027) B17009027
theorem B7559567 : Blo 2239435 7559567 := bstep (se 1 (by rfl) ⟨5669675, by rfl⟩ : syracuseStep 7559567 = 11339351) B11339351
theorem B5039711 : Blo 2239435 5039711 := bstep (se 1 (by rfl) ⟨3779783, by rfl⟩ : syracuseStep 5039711 = 7559567) B7559567
theorem B3359807 : Blo 2239435 3359807 := bstep (se 1 (by rfl) ⟨2519855, by rfl⟩ : syracuseStep 3359807 = 5039711) B5039711
theorem B2239871 : Blo 2239435 2239871 := bstep (se 1 (by rfl) ⟨1679903, by rfl⟩ : syracuseStep 2239871 = 3359807) B3359807
theorem B3359813 : Blo 2239435 3359813 := bbase (se 4 (by rfl) ⟨314982, by rfl⟩ : syracuseStep 3359813 = 629965) (by norm_num)
theorem B2239875 : Blo 2239435 2239875 := bstep (se 1 (by rfl) ⟨1679906, by rfl⟩ : syracuseStep 2239875 = 3359813) B3359813
theorem B3779797 : Blo 2239435 3779797 := bbase (se 7 (by rfl) ⟨44294, by rfl⟩ : syracuseStep 3779797 = 88589) (by norm_num)
theorem B5039729 : Blo 2239435 5039729 := bstep (se 2 (by rfl) ⟨1889898, by rfl⟩ : syracuseStep 5039729 = 3779797) B3779797
theorem B3359819 : Blo 2239435 3359819 := bstep (se 1 (by rfl) ⟨2519864, by rfl⟩ : syracuseStep 3359819 = 5039729) B5039729
theorem B2239879 : Blo 2239435 2239879 := bstep (se 1 (by rfl) ⟨1679909, by rfl⟩ : syracuseStep 2239879 = 3359819) B3359819
theorem B2519869 : Blo 2239435 2519869 := bbase (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) (by norm_num)
theorem B3359825 : Blo 2239435 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B2239883 : Blo 2239435 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B7559621 : Blo 2239435 7559621 := bbase (se 4 (by rfl) ⟨708714, by rfl⟩ : syracuseStep 7559621 = 1417429) (by norm_num)
theorem B5039747 : Blo 2239435 5039747 := bstep (se 1 (by rfl) ⟨3779810, by rfl⟩ : syracuseStep 5039747 = 7559621) B7559621
theorem B3359831 : Blo 2239435 3359831 := bstep (se 1 (by rfl) ⟨2519873, by rfl⟩ : syracuseStep 3359831 = 5039747) B5039747
theorem B2239887 : Blo 2239435 2239887 := bstep (se 1 (by rfl) ⟨1679915, by rfl⟩ : syracuseStep 2239887 = 3359831) B3359831
theorem B3359837 : Blo 2239435 3359837 := bbase (se 3 (by rfl) ⟨629969, by rfl⟩ : syracuseStep 3359837 = 1259939) (by norm_num)
theorem B2239891 : Blo 2239435 2239891 := bstep (se 1 (by rfl) ⟨1679918, by rfl⟩ : syracuseStep 2239891 = 3359837) B3359837
theorem B5039765 : Blo 2239435 5039765 := bbase (se 6 (by rfl) ⟨118119, by rfl⟩ : syracuseStep 5039765 = 236239) (by norm_num)
theorem B3359843 : Blo 2239435 3359843 := bstep (se 1 (by rfl) ⟨2519882, by rfl⟩ : syracuseStep 3359843 = 5039765) B5039765
theorem B2239895 : Blo 2239435 2239895 := bstep (se 1 (by rfl) ⟨1679921, by rfl⟩ : syracuseStep 2239895 = 3359843) B3359843
theorem B2391925 : Blo 2239435 2391925 := bbase (se 5 (by rfl) ⟨112121, by rfl⟩ : syracuseStep 2391925 = 224243) (by norm_num)
theorem B3189233 : Blo 2239435 3189233 := bstep (se 2 (by rfl) ⟨1195962, by rfl⟩ : syracuseStep 3189233 = 2391925) B2391925
theorem B8504621 : Blo 2239435 8504621 := bstep (se 3 (by rfl) ⟨1594616, by rfl⟩ : syracuseStep 8504621 = 3189233) B3189233
theorem B5669747 : Blo 2239435 5669747 := bstep (se 1 (by rfl) ⟨4252310, by rfl⟩ : syracuseStep 5669747 = 8504621) B8504621
theorem B3779831 : Blo 2239435 3779831 := bstep (se 1 (by rfl) ⟨2834873, by rfl⟩ : syracuseStep 3779831 = 5669747) B5669747
theorem B2519887 : Blo 2239435 2519887 := bstep (se 1 (by rfl) ⟨1889915, by rfl⟩ : syracuseStep 2519887 = 3779831) B3779831
theorem B3359849 : Blo 2239435 3359849 := bstep (se 2 (by rfl) ⟨1259943, by rfl⟩ : syracuseStep 3359849 = 2519887) B2519887
theorem B2239899 : Blo 2239435 2239899 := bstep (se 1 (by rfl) ⟨1679924, by rfl⟩ : syracuseStep 2239899 = 3359849) B3359849
theorem B14351573 : Blo 2239435 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B9567715 : Blo 2239435 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B12756953 : Blo 2239435 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B8504635 : Blo 2239435 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B11339513 : Blo 2239435 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B7559675 : Blo 2239435 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B5039783 : Blo 2239435 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B3359855 : Blo 2239435 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B2239903 : Blo 2239435 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B3359861 : Blo 2239435 3359861 := bbase (se 5 (by rfl) ⟨157493, by rfl⟩ : syracuseStep 3359861 = 314987) (by norm_num)
theorem B2239907 : Blo 2239435 2239907 := bstep (se 1 (by rfl) ⟨1679930, by rfl⟩ : syracuseStep 2239907 = 3359861) B3359861
theorem B4252333 : Blo 2239435 4252333 := bbase (se 3 (by rfl) ⟨797312, by rfl⟩ : syracuseStep 4252333 = 1594625) (by norm_num)
theorem B5669777 : Blo 2239435 5669777 := bstep (se 2 (by rfl) ⟨2126166, by rfl⟩ : syracuseStep 5669777 = 4252333) B4252333
theorem B3779851 : Blo 2239435 3779851 := bstep (se 1 (by rfl) ⟨2834888, by rfl⟩ : syracuseStep 3779851 = 5669777) B5669777
theorem B5039801 : Blo 2239435 5039801 := bstep (se 2 (by rfl) ⟨1889925, by rfl⟩ : syracuseStep 5039801 = 3779851) B3779851
theorem B3359867 : Blo 2239435 3359867 := bstep (se 1 (by rfl) ⟨2519900, by rfl⟩ : syracuseStep 3359867 = 5039801) B5039801
theorem B2239911 : Blo 2239435 2239911 := bstep (se 1 (by rfl) ⟨1679933, by rfl⟩ : syracuseStep 2239911 = 3359867) B3359867
theorem B2519905 : Blo 2239435 2519905 := bbase (se 2 (by rfl) ⟨944964, by rfl⟩ : syracuseStep 2519905 = 1889929) (by norm_num)
theorem B3359873 : Blo 2239435 3359873 := bstep (se 2 (by rfl) ⟨1259952, by rfl⟩ : syracuseStep 3359873 = 2519905) B2519905
theorem B2239915 : Blo 2239435 2239915 := bstep (se 1 (by rfl) ⟨1679936, by rfl⟩ : syracuseStep 2239915 = 3359873) B3359873
theorem B5669797 : Blo 2239435 5669797 := bbase (se 4 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 5669797 = 1063087) (by norm_num)
theorem B7559729 : Blo 2239435 7559729 := bstep (se 2 (by rfl) ⟨2834898, by rfl⟩ : syracuseStep 7559729 = 5669797) B5669797
theorem B5039819 : Blo 2239435 5039819 := bstep (se 1 (by rfl) ⟨3779864, by rfl⟩ : syracuseStep 5039819 = 7559729) B7559729
theorem B3359879 : Blo 2239435 3359879 := bstep (se 1 (by rfl) ⟨2519909, by rfl⟩ : syracuseStep 3359879 = 5039819) B5039819
theorem B2239919 : Blo 2239435 2239919 := bstep (se 1 (by rfl) ⟨1679939, by rfl⟩ : syracuseStep 2239919 = 3359879) B3359879
theorem B3359885 : Blo 2239435 3359885 := bbase (se 3 (by rfl) ⟨629978, by rfl⟩ : syracuseStep 3359885 = 1259957) (by norm_num)
theorem B2239923 : Blo 2239435 2239923 := bstep (se 1 (by rfl) ⟨1679942, by rfl⟩ : syracuseStep 2239923 = 3359885) B3359885
theorem B5039837 : Blo 2239435 5039837 := bbase (se 3 (by rfl) ⟨944969, by rfl⟩ : syracuseStep 5039837 = 1889939) (by norm_num)
theorem B3359891 : Blo 2239435 3359891 := bstep (se 1 (by rfl) ⟨2519918, by rfl⟩ : syracuseStep 3359891 = 5039837) B5039837
theorem B2239927 : Blo 2239435 2239927 := bstep (se 1 (by rfl) ⟨1679945, by rfl⟩ : syracuseStep 2239927 = 3359891) B3359891
theorem B3779885 : Blo 2239435 3779885 := bbase (se 3 (by rfl) ⟨708728, by rfl⟩ : syracuseStep 3779885 = 1417457) (by norm_num)
theorem B2519923 : Blo 2239435 2519923 := bstep (se 1 (by rfl) ⟨1889942, by rfl⟩ : syracuseStep 2519923 = 3779885) B3779885
theorem B3359897 : Blo 2239435 3359897 := bstep (se 2 (by rfl) ⟨1259961, by rfl⟩ : syracuseStep 3359897 = 2519923) B2519923
theorem B2239931 : Blo 2239435 2239931 := bstep (se 1 (by rfl) ⟨1679948, by rfl⟩ : syracuseStep 2239931 = 3359897) B3359897
theorem B10910693 : Blo 2239435 10910693 := bbase (se 4 (by rfl) ⟨1022877, by rfl⟩ : syracuseStep 10910693 = 2045755) (by norm_num)
theorem B7273795 : Blo 2239435 7273795 := bstep (se 1 (by rfl) ⟨5455346, by rfl⟩ : syracuseStep 7273795 = 10910693) B10910693
theorem B9698393 : Blo 2239435 9698393 := bstep (se 2 (by rfl) ⟨3636897, by rfl⟩ : syracuseStep 9698393 = 7273795) B7273795
theorem B6465595 : Blo 2239435 6465595 := bstep (se 1 (by rfl) ⟨4849196, by rfl⟩ : syracuseStep 6465595 = 9698393) B9698393
theorem B8620793 : Blo 2239435 8620793 := bstep (se 2 (by rfl) ⟨3232797, by rfl⟩ : syracuseStep 8620793 = 6465595) B6465595
theorem B5747195 : Blo 2239435 5747195 := bstep (se 1 (by rfl) ⟨4310396, by rfl⟩ : syracuseStep 5747195 = 8620793) B8620793
theorem B3831463 : Blo 2239435 3831463 := bstep (se 1 (by rfl) ⟨2873597, by rfl⟩ : syracuseStep 3831463 = 5747195) B5747195
theorem B5108617 : Blo 2239435 5108617 := bstep (se 2 (by rfl) ⟨1915731, by rfl⟩ : syracuseStep 5108617 = 3831463) B3831463
theorem B6811489 : Blo 2239435 6811489 := bstep (se 2 (by rfl) ⟨2554308, by rfl⟩ : syracuseStep 6811489 = 5108617) B5108617
theorem B9081985 : Blo 2239435 9081985 := bstep (se 2 (by rfl) ⟨3405744, by rfl⟩ : syracuseStep 9081985 = 6811489) B6811489
theorem B12109313 : Blo 2239435 12109313 := bstep (se 2 (by rfl) ⟨4540992, by rfl⟩ : syracuseStep 12109313 = 9081985) B9081985
theorem B8072875 : Blo 2239435 8072875 := bstep (se 1 (by rfl) ⟨6054656, by rfl⟩ : syracuseStep 8072875 = 12109313) B12109313
theorem B43055333 : Blo 2239435 43055333 := bstep (se 4 (by rfl) ⟨4036437, by rfl⟩ : syracuseStep 43055333 = 8072875) B8072875
theorem B28703555 : Blo 2239435 28703555 := bstep (se 1 (by rfl) ⟨21527666, by rfl⟩ : syracuseStep 28703555 = 43055333) B43055333
theorem B19135703 : Blo 2239435 19135703 := bstep (se 1 (by rfl) ⟨14351777, by rfl⟩ : syracuseStep 19135703 = 28703555) B28703555
theorem B12757135 : Blo 2239435 12757135 := bstep (se 1 (by rfl) ⟨9567851, by rfl⟩ : syracuseStep 12757135 = 19135703) B19135703
theorem B17009513 : Blo 2239435 17009513 := bstep (se 2 (by rfl) ⟨6378567, by rfl⟩ : syracuseStep 17009513 = 12757135) B12757135
theorem B11339675 : Blo 2239435 11339675 := bstep (se 1 (by rfl) ⟨8504756, by rfl⟩ : syracuseStep 11339675 = 17009513) B17009513
theorem B7559783 : Blo 2239435 7559783 := bstep (se 1 (by rfl) ⟨5669837, by rfl⟩ : syracuseStep 7559783 = 11339675) B11339675
theorem B5039855 : Blo 2239435 5039855 := bstep (se 1 (by rfl) ⟨3779891, by rfl⟩ : syracuseStep 5039855 = 7559783) B7559783
theorem B3359903 : Blo 2239435 3359903 := bstep (se 1 (by rfl) ⟨2519927, by rfl⟩ : syracuseStep 3359903 = 5039855) B5039855
theorem B2239935 : Blo 2239435 2239935 := bstep (se 1 (by rfl) ⟨1679951, by rfl⟩ : syracuseStep 2239935 = 3359903) B3359903
theorem B3359909 : Blo 2239435 3359909 := bbase (se 4 (by rfl) ⟨314991, by rfl⟩ : syracuseStep 3359909 = 629983) (by norm_num)
theorem B2239939 : Blo 2239435 2239939 := bstep (se 1 (by rfl) ⟨1679954, by rfl⟩ : syracuseStep 2239939 = 3359909) B3359909
theorem B2834929 : Blo 2239435 2834929 := bbase (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) (by norm_num)
theorem B3779905 : Blo 2239435 3779905 := bstep (se 2 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 3779905 = 2834929) B2834929
theorem B5039873 : Blo 2239435 5039873 := bstep (se 2 (by rfl) ⟨1889952, by rfl⟩ : syracuseStep 5039873 = 3779905) B3779905
theorem B3359915 : Blo 2239435 3359915 := bstep (se 1 (by rfl) ⟨2519936, by rfl⟩ : syracuseStep 3359915 = 5039873) B5039873
theorem B2239943 : Blo 2239435 2239943 := bstep (se 1 (by rfl) ⟨1679957, by rfl⟩ : syracuseStep 2239943 = 3359915) B3359915
theorem B2519941 : Blo 2239435 2519941 := bbase (se 4 (by rfl) ⟨236244, by rfl⟩ : syracuseStep 2519941 = 472489) (by norm_num)
theorem B3359921 : Blo 2239435 3359921 := bstep (se 2 (by rfl) ⟨1259970, by rfl⟩ : syracuseStep 3359921 = 2519941) B2519941
theorem B2239947 : Blo 2239435 2239947 := bstep (se 1 (by rfl) ⟨1679960, by rfl⟩ : syracuseStep 2239947 = 3359921) B3359921
theorem B5381957 : Blo 2239435 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B3587971 : Blo 2239435 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B4783961 : Blo 2239435 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B3189307 : Blo 2239435 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B4252409 : Blo 2239435 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B2834939 : Blo 2239435 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B7559837 : Blo 2239435 7559837 := bstep (se 3 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 7559837 = 2834939) B2834939
theorem B5039891 : Blo 2239435 5039891 := bstep (se 1 (by rfl) ⟨3779918, by rfl⟩ : syracuseStep 5039891 = 7559837) B7559837
theorem B3359927 : Blo 2239435 3359927 := bstep (se 1 (by rfl) ⟨2519945, by rfl⟩ : syracuseStep 3359927 = 5039891) B5039891
theorem B2239951 : Blo 2239435 2239951 := bstep (se 1 (by rfl) ⟨1679963, by rfl⟩ : syracuseStep 2239951 = 3359927) B3359927
theorem B3359933 : Blo 2239435 3359933 := bbase (se 3 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 3359933 = 1259975) (by norm_num)
theorem B2239955 : Blo 2239435 2239955 := bstep (se 1 (by rfl) ⟨1679966, by rfl⟩ : syracuseStep 2239955 = 3359933) B3359933
theorem B5039909 : Blo 2239435 5039909 := bbase (se 4 (by rfl) ⟨472491, by rfl⟩ : syracuseStep 5039909 = 944983) (by norm_num)
theorem B3359939 : Blo 2239435 3359939 := bstep (se 1 (by rfl) ⟨2519954, by rfl⟩ : syracuseStep 3359939 = 5039909) B5039909
theorem B2239959 : Blo 2239435 2239959 := bstep (se 1 (by rfl) ⟨1679969, by rfl⟩ : syracuseStep 2239959 = 3359939) B3359939
theorem B5669909 : Blo 2239435 5669909 := bbase (se 6 (by rfl) ⟨132888, by rfl⟩ : syracuseStep 5669909 = 265777) (by norm_num)
theorem B3779939 : Blo 2239435 3779939 := bstep (se 1 (by rfl) ⟨2834954, by rfl⟩ : syracuseStep 3779939 = 5669909) B5669909
theorem B2519959 : Blo 2239435 2519959 := bstep (se 1 (by rfl) ⟨1889969, by rfl⟩ : syracuseStep 2519959 = 3779939) B3779939
theorem B3359945 : Blo 2239435 3359945 := bstep (se 2 (by rfl) ⟨1259979, by rfl⟩ : syracuseStep 3359945 = 2519959) B2519959
theorem B2239963 : Blo 2239435 2239963 := bstep (se 1 (by rfl) ⟨1679972, by rfl⟩ : syracuseStep 2239963 = 3359945) B3359945
theorem B9567989 : Blo 2239435 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B6378659 : Blo 2239435 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B4252439 : Blo 2239435 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B11339837 : Blo 2239435 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B7559891 : Blo 2239435 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B5039927 : Blo 2239435 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B3359951 : Blo 2239435 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B2239967 : Blo 2239435 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B3359957 : Blo 2239435 3359957 := bbase (se 7 (by rfl) ⟨39374, by rfl⟩ : syracuseStep 3359957 = 78749) (by norm_num)
theorem B2239971 : Blo 2239435 2239971 := bstep (se 1 (by rfl) ⟨1679978, by rfl⟩ : syracuseStep 2239971 = 3359957) B3359957
theorem B3189341 : Blo 2239435 3189341 := bbase (se 3 (by rfl) ⟨598001, by rfl⟩ : syracuseStep 3189341 = 1196003) (by norm_num)
theorem B8504909 : Blo 2239435 8504909 := bstep (se 3 (by rfl) ⟨1594670, by rfl⟩ : syracuseStep 8504909 = 3189341) B3189341
theorem B5669939 : Blo 2239435 5669939 := bstep (se 1 (by rfl) ⟨4252454, by rfl⟩ : syracuseStep 5669939 = 8504909) B8504909
theorem B3779959 : Blo 2239435 3779959 := bstep (se 1 (by rfl) ⟨2834969, by rfl⟩ : syracuseStep 3779959 = 5669939) B5669939
theorem B5039945 : Blo 2239435 5039945 := bstep (se 2 (by rfl) ⟨1889979, by rfl⟩ : syracuseStep 5039945 = 3779959) B3779959
theorem B3359963 : Blo 2239435 3359963 := bstep (se 1 (by rfl) ⟨2519972, by rfl⟩ : syracuseStep 3359963 = 5039945) B5039945
theorem B2239975 : Blo 2239435 2239975 := bstep (se 1 (by rfl) ⟨1679981, by rfl⟩ : syracuseStep 2239975 = 3359963) B3359963
theorem B2519977 : Blo 2239435 2519977 := bbase (se 2 (by rfl) ⟨944991, by rfl⟩ : syracuseStep 2519977 = 1889983) (by norm_num)
theorem B3359969 : Blo 2239435 3359969 := bstep (se 2 (by rfl) ⟨1259988, by rfl⟩ : syracuseStep 3359969 = 2519977) B2519977
theorem B2239979 : Blo 2239435 2239979 := bstep (se 1 (by rfl) ⟨1679984, by rfl⟩ : syracuseStep 2239979 = 3359969) B3359969
theorem B9082181 : Blo 2239435 9082181 := bbase (se 4 (by rfl) ⟨851454, by rfl⟩ : syracuseStep 9082181 = 1702909) (by norm_num)
theorem B6054787 : Blo 2239435 6054787 := bstep (se 1 (by rfl) ⟨4541090, by rfl⟩ : syracuseStep 6054787 = 9082181) B9082181
theorem B8073049 : Blo 2239435 8073049 := bstep (se 2 (by rfl) ⟨3027393, by rfl⟩ : syracuseStep 8073049 = 6054787) B6054787
theorem B10764065 : Blo 2239435 10764065 := bstep (se 2 (by rfl) ⟨4036524, by rfl⟩ : syracuseStep 10764065 = 8073049) B8073049
theorem B7176043 : Blo 2239435 7176043 := bstep (se 1 (by rfl) ⟨5382032, by rfl⟩ : syracuseStep 7176043 = 10764065) B10764065
theorem B9568057 : Blo 2239435 9568057 := bstep (se 2 (by rfl) ⟨3588021, by rfl⟩ : syracuseStep 9568057 = 7176043) B7176043
theorem B12757409 : Blo 2239435 12757409 := bstep (se 2 (by rfl) ⟨4784028, by rfl⟩ : syracuseStep 12757409 = 9568057) B9568057
theorem B8504939 : Blo 2239435 8504939 := bstep (se 1 (by rfl) ⟨6378704, by rfl⟩ : syracuseStep 8504939 = 12757409) B12757409
theorem B5669959 : Blo 2239435 5669959 := bstep (se 1 (by rfl) ⟨4252469, by rfl⟩ : syracuseStep 5669959 = 8504939) B8504939
theorem B7559945 : Blo 2239435 7559945 := bstep (se 2 (by rfl) ⟨2834979, by rfl⟩ : syracuseStep 7559945 = 5669959) B5669959
theorem B5039963 : Blo 2239435 5039963 := bstep (se 1 (by rfl) ⟨3779972, by rfl⟩ : syracuseStep 5039963 = 7559945) B7559945
theorem B3359975 : Blo 2239435 3359975 := bstep (se 1 (by rfl) ⟨2519981, by rfl⟩ : syracuseStep 3359975 = 5039963) B5039963
theorem B2239983 : Blo 2239435 2239983 := bstep (se 1 (by rfl) ⟨1679987, by rfl⟩ : syracuseStep 2239983 = 3359975) B3359975
theorem B3359981 : Blo 2239435 3359981 := bbase (se 3 (by rfl) ⟨629996, by rfl⟩ : syracuseStep 3359981 = 1259993) (by norm_num)
theorem B2239987 : Blo 2239435 2239987 := bstep (se 1 (by rfl) ⟨1679990, by rfl⟩ : syracuseStep 2239987 = 3359981) B3359981
theorem B5039981 : Blo 2239435 5039981 := bbase (se 3 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 5039981 = 1889993) (by norm_num)
theorem B3359987 : Blo 2239435 3359987 := bstep (se 1 (by rfl) ⟨2519990, by rfl⟩ : syracuseStep 3359987 = 5039981) B5039981
theorem B2239991 : Blo 2239435 2239991 := bstep (se 1 (by rfl) ⟨1679993, by rfl⟩ : syracuseStep 2239991 = 3359987) B3359987
theorem B4252493 : Blo 2239435 4252493 := bbase (se 3 (by rfl) ⟨797342, by rfl⟩ : syracuseStep 4252493 = 1594685) (by norm_num)
theorem B2834995 : Blo 2239435 2834995 := bstep (se 1 (by rfl) ⟨2126246, by rfl⟩ : syracuseStep 2834995 = 4252493) B4252493
theorem B3779993 : Blo 2239435 3779993 := bstep (se 2 (by rfl) ⟨1417497, by rfl⟩ : syracuseStep 3779993 = 2834995) B2834995
theorem B2519995 : Blo 2239435 2519995 := bstep (se 1 (by rfl) ⟨1889996, by rfl⟩ : syracuseStep 2519995 = 3779993) B3779993
theorem B3359993 : Blo 2239435 3359993 := bstep (se 2 (by rfl) ⟨1259997, by rfl⟩ : syracuseStep 3359993 = 2519995) B2519995
theorem B2239995 : Blo 2239435 2239995 := bstep (se 1 (by rfl) ⟨1679996, by rfl⟩ : syracuseStep 2239995 = 3359993) B3359993
theorem B2270561 : Blo 2239435 2270561 := bbase (se 2 (by rfl) ⟨851460, by rfl⟩ : syracuseStep 2270561 = 1702921) (by norm_num)
theorem B24219317 : Blo 2239435 24219317 := bstep (se 5 (by rfl) ⟨1135280, by rfl⟩ : syracuseStep 24219317 = 2270561) B2270561
theorem B16146211 : Blo 2239435 16146211 := bstep (se 1 (by rfl) ⟨12109658, by rfl⟩ : syracuseStep 16146211 = 24219317) B24219317
theorem B21528281 : Blo 2239435 21528281 := bstep (se 2 (by rfl) ⟨8073105, by rfl⟩ : syracuseStep 21528281 = 16146211) B16146211
theorem B57408749 : Blo 2239435 57408749 := bstep (se 3 (by rfl) ⟨10764140, by rfl⟩ : syracuseStep 57408749 = 21528281) B21528281
theorem B38272499 : Blo 2239435 38272499 := bstep (se 1 (by rfl) ⟨28704374, by rfl⟩ : syracuseStep 38272499 = 57408749) B57408749
theorem B25514999 : Blo 2239435 25514999 := bstep (se 1 (by rfl) ⟨19136249, by rfl⟩ : syracuseStep 25514999 = 38272499) B38272499
theorem B17009999 : Blo 2239435 17009999 := bstep (se 1 (by rfl) ⟨12757499, by rfl⟩ : syracuseStep 17009999 = 25514999) B25514999
theorem B11339999 : Blo 2239435 11339999 := bstep (se 1 (by rfl) ⟨8504999, by rfl⟩ : syracuseStep 11339999 = 17009999) B17009999
theorem B7559999 : Blo 2239435 7559999 := bstep (se 1 (by rfl) ⟨5669999, by rfl⟩ : syracuseStep 7559999 = 11339999) B11339999
theorem B5039999 : Blo 2239435 5039999 := bstep (se 1 (by rfl) ⟨3779999, by rfl⟩ : syracuseStep 5039999 = 7559999) B7559999
theorem B3359999 : Blo 2239435 3359999 := bstep (se 1 (by rfl) ⟨2519999, by rfl⟩ : syracuseStep 3359999 = 5039999) B5039999
theorem B2239999 : Blo 2239435 2239999 := bstep (se 1 (by rfl) ⟨1679999, by rfl⟩ : syracuseStep 2239999 = 3359999) B3359999
theorem B3360005 : Blo 2239435 3360005 := bbase (se 4 (by rfl) ⟨315000, by rfl⟩ : syracuseStep 3360005 = 630001) (by norm_num)
theorem B2240003 : Blo 2239435 2240003 := bstep (se 1 (by rfl) ⟨1680002, by rfl⟩ : syracuseStep 2240003 = 3360005) B3360005
theorem B3780013 : Blo 2239435 3780013 := bbase (se 3 (by rfl) ⟨708752, by rfl⟩ : syracuseStep 3780013 = 1417505) (by norm_num)
theorem B5040017 : Blo 2239435 5040017 := bstep (se 2 (by rfl) ⟨1890006, by rfl⟩ : syracuseStep 5040017 = 3780013) B3780013
theorem B3360011 : Blo 2239435 3360011 := bstep (se 1 (by rfl) ⟨2520008, by rfl⟩ : syracuseStep 3360011 = 5040017) B5040017
theorem B2240007 : Blo 2239435 2240007 := bstep (se 1 (by rfl) ⟨1680005, by rfl⟩ : syracuseStep 2240007 = 3360011) B3360011
theorem B2520013 : Blo 2239435 2520013 := bbase (se 3 (by rfl) ⟨472502, by rfl⟩ : syracuseStep 2520013 = 945005) (by norm_num)
theorem B3360017 : Blo 2239435 3360017 := bstep (se 2 (by rfl) ⟨1260006, by rfl⟩ : syracuseStep 3360017 = 2520013) B2520013
theorem B2240011 : Blo 2239435 2240011 := bstep (se 1 (by rfl) ⟨1680008, by rfl⟩ : syracuseStep 2240011 = 3360017) B3360017
theorem B7560053 : Blo 2239435 7560053 := bbase (se 5 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 7560053 = 708755) (by norm_num)
theorem B5040035 : Blo 2239435 5040035 := bstep (se 1 (by rfl) ⟨3780026, by rfl⟩ : syracuseStep 5040035 = 7560053) B7560053
theorem B3360023 : Blo 2239435 3360023 := bstep (se 1 (by rfl) ⟨2520017, by rfl⟩ : syracuseStep 3360023 = 5040035) B5040035
theorem B2240015 : Blo 2239435 2240015 := bstep (se 1 (by rfl) ⟨1680011, by rfl⟩ : syracuseStep 2240015 = 3360023) B3360023
theorem B3360029 : Blo 2239435 3360029 := bbase (se 3 (by rfl) ⟨630005, by rfl⟩ : syracuseStep 3360029 = 1260011) (by norm_num)
theorem B2240019 : Blo 2239435 2240019 := bstep (se 1 (by rfl) ⟨1680014, by rfl⟩ : syracuseStep 2240019 = 3360029) B3360029
theorem B5040053 : Blo 2239435 5040053 := bbase (se 5 (by rfl) ⟨236252, by rfl⟩ : syracuseStep 5040053 = 472505) (by norm_num)
theorem B3360035 : Blo 2239435 3360035 := bstep (se 1 (by rfl) ⟨2520026, by rfl⟩ : syracuseStep 3360035 = 5040053) B5040053
theorem B2240023 : Blo 2239435 2240023 := bstep (se 1 (by rfl) ⟨1680017, by rfl⟩ : syracuseStep 2240023 = 3360035) B3360035
theorem B4849397 : Blo 2239435 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B3232931 : Blo 2239435 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B8621149 : Blo 2239435 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B11494865 : Blo 2239435 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B7663243 : Blo 2239435 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B10217657 : Blo 2239435 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B6811771 : Blo 2239435 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B9082361 : Blo 2239435 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B6054907 : Blo 2239435 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B8073209 : Blo 2239435 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5382139 : Blo 2239435 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B7176185 : Blo 2239435 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B4784123 : Blo 2239435 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B12757661 : Blo 2239435 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B8505107 : Blo 2239435 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B5670071 : Blo 2239435 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B3780047 : Blo 2239435 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B2520031 : Blo 2239435 2520031 := bstep (se 1 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 2520031 = 3780047) B3780047
theorem B3360041 : Blo 2239435 3360041 := bstep (se 2 (by rfl) ⟨1260015, by rfl⟩ : syracuseStep 3360041 = 2520031) B2520031
theorem B2240027 : Blo 2239435 2240027 := bstep (se 1 (by rfl) ⟨1680020, by rfl⟩ : syracuseStep 2240027 = 3360041) B3360041
theorem B7176197 : Blo 2239435 7176197 := bbase (se 4 (by rfl) ⟨672768, by rfl⟩ : syracuseStep 7176197 = 1345537) (by norm_num)
theorem B4784131 : Blo 2239435 4784131 := bstep (se 1 (by rfl) ⟨3588098, by rfl⟩ : syracuseStep 4784131 = 7176197) B7176197
theorem B6378841 : Blo 2239435 6378841 := bstep (se 2 (by rfl) ⟨2392065, by rfl⟩ : syracuseStep 6378841 = 4784131) B4784131
theorem B8505121 : Blo 2239435 8505121 := bstep (se 2 (by rfl) ⟨3189420, by rfl⟩ : syracuseStep 8505121 = 6378841) B6378841
theorem B11340161 : Blo 2239435 11340161 := bstep (se 2 (by rfl) ⟨4252560, by rfl⟩ : syracuseStep 11340161 = 8505121) B8505121
theorem B7560107 : Blo 2239435 7560107 := bstep (se 1 (by rfl) ⟨5670080, by rfl⟩ : syracuseStep 7560107 = 11340161) B11340161
theorem B5040071 : Blo 2239435 5040071 := bstep (se 1 (by rfl) ⟨3780053, by rfl⟩ : syracuseStep 5040071 = 7560107) B7560107
theorem B3360047 : Blo 2239435 3360047 := bstep (se 1 (by rfl) ⟨2520035, by rfl⟩ : syracuseStep 3360047 = 5040071) B5040071
theorem B2240031 : Blo 2239435 2240031 := bstep (se 1 (by rfl) ⟨1680023, by rfl⟩ : syracuseStep 2240031 = 3360047) B3360047
theorem B3360053 : Blo 2239435 3360053 := bbase (se 5 (by rfl) ⟨157502, by rfl⟩ : syracuseStep 3360053 = 315005) (by norm_num)
theorem B2240035 : Blo 2239435 2240035 := bstep (se 1 (by rfl) ⟨1680026, by rfl⟩ : syracuseStep 2240035 = 3360053) B3360053
theorem B5670101 : Blo 2239435 5670101 := bbase (se 7 (by rfl) ⟨66446, by rfl⟩ : syracuseStep 5670101 = 132893) (by norm_num)
theorem B3780067 : Blo 2239435 3780067 := bstep (se 1 (by rfl) ⟨2835050, by rfl⟩ : syracuseStep 3780067 = 5670101) B5670101
theorem B5040089 : Blo 2239435 5040089 := bstep (se 2 (by rfl) ⟨1890033, by rfl⟩ : syracuseStep 5040089 = 3780067) B3780067
theorem B3360059 : Blo 2239435 3360059 := bstep (se 1 (by rfl) ⟨2520044, by rfl⟩ : syracuseStep 3360059 = 5040089) B5040089
theorem B2240039 : Blo 2239435 2240039 := bstep (se 1 (by rfl) ⟨1680029, by rfl⟩ : syracuseStep 2240039 = 3360059) B3360059
theorem B2520049 : Blo 2239435 2520049 := bbase (se 2 (by rfl) ⟨945018, by rfl⟩ : syracuseStep 2520049 = 1890037) (by norm_num)
theorem B3360065 : Blo 2239435 3360065 := bstep (se 2 (by rfl) ⟨1260024, by rfl⟩ : syracuseStep 3360065 = 2520049) B2520049
theorem B2240043 : Blo 2239435 2240043 := bstep (se 1 (by rfl) ⟨1680032, by rfl⟩ : syracuseStep 2240043 = 3360065) B3360065
theorem B10764373 : Blo 2239435 10764373 := bbase (se 8 (by rfl) ⟨63072, by rfl⟩ : syracuseStep 10764373 = 126145) (by norm_num)
theorem B14352497 : Blo 2239435 14352497 := bstep (se 2 (by rfl) ⟨5382186, by rfl⟩ : syracuseStep 14352497 = 10764373) B10764373
theorem B9568331 : Blo 2239435 9568331 := bstep (se 1 (by rfl) ⟨7176248, by rfl⟩ : syracuseStep 9568331 = 14352497) B14352497
theorem B6378887 : Blo 2239435 6378887 := bstep (se 1 (by rfl) ⟨4784165, by rfl⟩ : syracuseStep 6378887 = 9568331) B9568331
theorem B4252591 : Blo 2239435 4252591 := bstep (se 1 (by rfl) ⟨3189443, by rfl⟩ : syracuseStep 4252591 = 6378887) B6378887
theorem B5670121 : Blo 2239435 5670121 := bstep (se 2 (by rfl) ⟨2126295, by rfl⟩ : syracuseStep 5670121 = 4252591) B4252591
theorem B7560161 : Blo 2239435 7560161 := bstep (se 2 (by rfl) ⟨2835060, by rfl⟩ : syracuseStep 7560161 = 5670121) B5670121
theorem B5040107 : Blo 2239435 5040107 := bstep (se 1 (by rfl) ⟨3780080, by rfl⟩ : syracuseStep 5040107 = 7560161) B7560161
theorem B3360071 : Blo 2239435 3360071 := bstep (se 1 (by rfl) ⟨2520053, by rfl⟩ : syracuseStep 3360071 = 5040107) B5040107
theorem B2240047 : Blo 2239435 2240047 := bstep (se 1 (by rfl) ⟨1680035, by rfl⟩ : syracuseStep 2240047 = 3360071) B3360071
theorem B3360077 : Blo 2239435 3360077 := bbase (se 3 (by rfl) ⟨630014, by rfl⟩ : syracuseStep 3360077 = 1260029) (by norm_num)
theorem B2240051 : Blo 2239435 2240051 := bstep (se 1 (by rfl) ⟨1680038, by rfl⟩ : syracuseStep 2240051 = 3360077) B3360077
theorem B5040125 : Blo 2239435 5040125 := bbase (se 3 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 5040125 = 1890047) (by norm_num)
theorem B3360083 : Blo 2239435 3360083 := bstep (se 1 (by rfl) ⟨2520062, by rfl⟩ : syracuseStep 3360083 = 5040125) B5040125
theorem B2240055 : Blo 2239435 2240055 := bstep (se 1 (by rfl) ⟨1680041, by rfl⟩ : syracuseStep 2240055 = 3360083) B3360083
theorem B3780101 : Blo 2239435 3780101 := bbase (se 4 (by rfl) ⟨354384, by rfl⟩ : syracuseStep 3780101 = 708769) (by norm_num)
theorem B2520067 : Blo 2239435 2520067 := bstep (se 1 (by rfl) ⟨1890050, by rfl⟩ : syracuseStep 2520067 = 3780101) B3780101
theorem B3360089 : Blo 2239435 3360089 := bstep (se 2 (by rfl) ⟨1260033, by rfl⟩ : syracuseStep 3360089 = 2520067) B2520067
theorem B2240059 : Blo 2239435 2240059 := bstep (se 1 (by rfl) ⟨1680044, by rfl⟩ : syracuseStep 2240059 = 3360089) B3360089
theorem B17010485 : Blo 2239435 17010485 := bbase (se 5 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 17010485 = 1594733) (by norm_num)
theorem B11340323 : Blo 2239435 11340323 := bstep (se 1 (by rfl) ⟨8505242, by rfl⟩ : syracuseStep 11340323 = 17010485) B17010485
theorem B7560215 : Blo 2239435 7560215 := bstep (se 1 (by rfl) ⟨5670161, by rfl⟩ : syracuseStep 7560215 = 11340323) B11340323
theorem B5040143 : Blo 2239435 5040143 := bstep (se 1 (by rfl) ⟨3780107, by rfl⟩ : syracuseStep 5040143 = 7560215) B7560215
theorem B3360095 : Blo 2239435 3360095 := bstep (se 1 (by rfl) ⟨2520071, by rfl⟩ : syracuseStep 3360095 = 5040143) B5040143
theorem B2240063 : Blo 2239435 2240063 := bstep (se 1 (by rfl) ⟨1680047, by rfl⟩ : syracuseStep 2240063 = 3360095) B3360095
theorem B3360101 : Blo 2239435 3360101 := bbase (se 4 (by rfl) ⟨315009, by rfl⟩ : syracuseStep 3360101 = 630019) (by norm_num)
theorem B2240067 : Blo 2239435 2240067 := bstep (se 1 (by rfl) ⟨1680050, by rfl⟩ : syracuseStep 2240067 = 3360101) B3360101
theorem B4252637 : Blo 2239435 4252637 := bbase (se 3 (by rfl) ⟨797369, by rfl⟩ : syracuseStep 4252637 = 1594739) (by norm_num)
theorem B2835091 : Blo 2239435 2835091 := bstep (se 1 (by rfl) ⟨2126318, by rfl⟩ : syracuseStep 2835091 = 4252637) B4252637
theorem B3780121 : Blo 2239435 3780121 := bstep (se 2 (by rfl) ⟨1417545, by rfl⟩ : syracuseStep 3780121 = 2835091) B2835091
theorem B5040161 : Blo 2239435 5040161 := bstep (se 2 (by rfl) ⟨1890060, by rfl⟩ : syracuseStep 5040161 = 3780121) B3780121
theorem B3360107 : Blo 2239435 3360107 := bstep (se 1 (by rfl) ⟨2520080, by rfl⟩ : syracuseStep 3360107 = 5040161) B5040161
theorem B2240071 : Blo 2239435 2240071 := bstep (se 1 (by rfl) ⟨1680053, by rfl⟩ : syracuseStep 2240071 = 3360107) B3360107
theorem B2520085 : Blo 2239435 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B3360113 : Blo 2239435 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B2240075 : Blo 2239435 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B2835101 : Blo 2239435 2835101 := bbase (se 3 (by rfl) ⟨531581, by rfl⟩ : syracuseStep 2835101 = 1063163) (by norm_num)
theorem B7560269 : Blo 2239435 7560269 := bstep (se 3 (by rfl) ⟨1417550, by rfl⟩ : syracuseStep 7560269 = 2835101) B2835101
theorem B5040179 : Blo 2239435 5040179 := bstep (se 1 (by rfl) ⟨3780134, by rfl⟩ : syracuseStep 5040179 = 7560269) B7560269
theorem B3360119 : Blo 2239435 3360119 := bstep (se 1 (by rfl) ⟨2520089, by rfl⟩ : syracuseStep 3360119 = 5040179) B5040179
theorem B2240079 : Blo 2239435 2240079 := bstep (se 1 (by rfl) ⟨1680059, by rfl⟩ : syracuseStep 2240079 = 3360119) B3360119
theorem B3360125 : Blo 2239435 3360125 := bbase (se 3 (by rfl) ⟨630023, by rfl⟩ : syracuseStep 3360125 = 1260047) (by norm_num)
theorem B2240083 : Blo 2239435 2240083 := bstep (se 1 (by rfl) ⟨1680062, by rfl⟩ : syracuseStep 2240083 = 3360125) B3360125
theorem B5040197 : Blo 2239435 5040197 := bbase (se 4 (by rfl) ⟨472518, by rfl⟩ : syracuseStep 5040197 = 945037) (by norm_num)
theorem B3360131 : Blo 2239435 3360131 := bstep (se 1 (by rfl) ⟨2520098, by rfl⟩ : syracuseStep 3360131 = 5040197) B5040197
theorem B2240087 : Blo 2239435 2240087 := bstep (se 1 (by rfl) ⟨1680065, by rfl⟩ : syracuseStep 2240087 = 3360131) B3360131
theorem B6379013 : Blo 2239435 6379013 := bbase (se 4 (by rfl) ⟨598032, by rfl⟩ : syracuseStep 6379013 = 1196065) (by norm_num)
theorem B4252675 : Blo 2239435 4252675 := bstep (se 1 (by rfl) ⟨3189506, by rfl⟩ : syracuseStep 4252675 = 6379013) B6379013
theorem B5670233 : Blo 2239435 5670233 := bstep (se 2 (by rfl) ⟨2126337, by rfl⟩ : syracuseStep 5670233 = 4252675) B4252675
theorem B3780155 : Blo 2239435 3780155 := bstep (se 1 (by rfl) ⟨2835116, by rfl⟩ : syracuseStep 3780155 = 5670233) B5670233
theorem B2520103 : Blo 2239435 2520103 := bstep (se 1 (by rfl) ⟨1890077, by rfl⟩ : syracuseStep 2520103 = 3780155) B3780155
theorem B3360137 : Blo 2239435 3360137 := bstep (se 2 (by rfl) ⟨1260051, by rfl⟩ : syracuseStep 3360137 = 2520103) B2520103
theorem B2240091 : Blo 2239435 2240091 := bstep (se 1 (by rfl) ⟨1680068, by rfl⟩ : syracuseStep 2240091 = 3360137) B3360137
theorem B11340485 : Blo 2239435 11340485 := bbase (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) (by norm_num)
theorem B7560323 : Blo 2239435 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B5040215 : Blo 2239435 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B3360143 : Blo 2239435 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B2240095 : Blo 2239435 2240095 := bstep (se 1 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 2240095 = 3360143) B3360143
theorem B3360149 : Blo 2239435 3360149 := bbase (se 6 (by rfl) ⟨78753, by rfl⟩ : syracuseStep 3360149 = 157507) (by norm_num)
theorem B2240099 : Blo 2239435 2240099 := bstep (se 1 (by rfl) ⟨1680074, by rfl⟩ : syracuseStep 2240099 = 3360149) B3360149
theorem B4784285 : Blo 2239435 4784285 := bbase (se 3 (by rfl) ⟨897053, by rfl⟩ : syracuseStep 4784285 = 1794107) (by norm_num)
theorem B12758093 : Blo 2239435 12758093 := bstep (se 3 (by rfl) ⟨2392142, by rfl⟩ : syracuseStep 12758093 = 4784285) B4784285
theorem B8505395 : Blo 2239435 8505395 := bstep (se 1 (by rfl) ⟨6379046, by rfl⟩ : syracuseStep 8505395 = 12758093) B12758093
theorem B5670263 : Blo 2239435 5670263 := bstep (se 1 (by rfl) ⟨4252697, by rfl⟩ : syracuseStep 5670263 = 8505395) B8505395
theorem B3780175 : Blo 2239435 3780175 := bstep (se 1 (by rfl) ⟨2835131, by rfl⟩ : syracuseStep 3780175 = 5670263) B5670263
theorem B5040233 : Blo 2239435 5040233 := bstep (se 2 (by rfl) ⟨1890087, by rfl⟩ : syracuseStep 5040233 = 3780175) B3780175
theorem B3360155 : Blo 2239435 3360155 := bstep (se 1 (by rfl) ⟨2520116, by rfl⟩ : syracuseStep 3360155 = 5040233) B5040233
theorem B2240103 : Blo 2239435 2240103 := bstep (se 1 (by rfl) ⟨1680077, by rfl⟩ : syracuseStep 2240103 = 3360155) B3360155
theorem B2520121 : Blo 2239435 2520121 := bbase (se 2 (by rfl) ⟨945045, by rfl⟩ : syracuseStep 2520121 = 1890091) (by norm_num)
theorem B3360161 : Blo 2239435 3360161 := bstep (se 2 (by rfl) ⟨1260060, by rfl⟩ : syracuseStep 3360161 = 2520121) B2520121
theorem B2240107 : Blo 2239435 2240107 := bstep (se 1 (by rfl) ⟨1680080, by rfl⟩ : syracuseStep 2240107 = 3360161) B3360161
theorem B5382341 : Blo 2239435 5382341 := bbase (se 4 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 5382341 = 1009189) (by norm_num)
theorem B3588227 : Blo 2239435 3588227 := bstep (se 1 (by rfl) ⟨2691170, by rfl⟩ : syracuseStep 3588227 = 5382341) B5382341
theorem B2392151 : Blo 2239435 2392151 := bstep (se 1 (by rfl) ⟨1794113, by rfl⟩ : syracuseStep 2392151 = 3588227) B3588227
theorem B6379069 : Blo 2239435 6379069 := bstep (se 3 (by rfl) ⟨1196075, by rfl⟩ : syracuseStep 6379069 = 2392151) B2392151
theorem B8505425 : Blo 2239435 8505425 := bstep (se 2 (by rfl) ⟨3189534, by rfl⟩ : syracuseStep 8505425 = 6379069) B6379069
theorem B5670283 : Blo 2239435 5670283 := bstep (se 1 (by rfl) ⟨4252712, by rfl⟩ : syracuseStep 5670283 = 8505425) B8505425
theorem B7560377 : Blo 2239435 7560377 := bstep (se 2 (by rfl) ⟨2835141, by rfl⟩ : syracuseStep 7560377 = 5670283) B5670283
theorem B5040251 : Blo 2239435 5040251 := bstep (se 1 (by rfl) ⟨3780188, by rfl⟩ : syracuseStep 5040251 = 7560377) B7560377
theorem B3360167 : Blo 2239435 3360167 := bstep (se 1 (by rfl) ⟨2520125, by rfl⟩ : syracuseStep 3360167 = 5040251) B5040251
theorem B2240111 : Blo 2239435 2240111 := bstep (se 1 (by rfl) ⟨1680083, by rfl⟩ : syracuseStep 2240111 = 3360167) B3360167
theorem B3360173 : Blo 2239435 3360173 := bbase (se 3 (by rfl) ⟨630032, by rfl⟩ : syracuseStep 3360173 = 1260065) (by norm_num)
theorem B2240115 : Blo 2239435 2240115 := bstep (se 1 (by rfl) ⟨1680086, by rfl⟩ : syracuseStep 2240115 = 3360173) B3360173
theorem B5040269 : Blo 2239435 5040269 := bbase (se 3 (by rfl) ⟨945050, by rfl⟩ : syracuseStep 5040269 = 1890101) (by norm_num)
theorem B3360179 : Blo 2239435 3360179 := bstep (se 1 (by rfl) ⟨2520134, by rfl⟩ : syracuseStep 3360179 = 5040269) B5040269
theorem B2240119 : Blo 2239435 2240119 := bstep (se 1 (by rfl) ⟨1680089, by rfl⟩ : syracuseStep 2240119 = 3360179) B3360179
theorem B2835157 : Blo 2239435 2835157 := bbase (se 7 (by rfl) ⟨33224, by rfl⟩ : syracuseStep 2835157 = 66449) (by norm_num)
theorem B3780209 : Blo 2239435 3780209 := bstep (se 2 (by rfl) ⟨1417578, by rfl⟩ : syracuseStep 3780209 = 2835157) B2835157
theorem B2520139 : Blo 2239435 2520139 := bstep (se 1 (by rfl) ⟨1890104, by rfl⟩ : syracuseStep 2520139 = 3780209) B3780209
theorem B3360185 : Blo 2239435 3360185 := bstep (se 2 (by rfl) ⟨1260069, by rfl⟩ : syracuseStep 3360185 = 2520139) B2520139
theorem B2240123 : Blo 2239435 2240123 := bstep (se 1 (by rfl) ⟨1680092, by rfl⟩ : syracuseStep 2240123 = 3360185) B3360185
theorem B4310765 : Blo 2239435 4310765 := bbase (se 3 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 4310765 = 1616537) (by norm_num)
theorem B2873843 : Blo 2239435 2873843 := bstep (se 1 (by rfl) ⟨2155382, by rfl⟩ : syracuseStep 2873843 = 4310765) B4310765
theorem B30654325 : Blo 2239435 30654325 := bstep (se 5 (by rfl) ⟨1436921, by rfl⟩ : syracuseStep 30654325 = 2873843) B2873843
theorem B40872433 : Blo 2239435 40872433 := bstep (se 2 (by rfl) ⟨15327162, by rfl⟩ : syracuseStep 40872433 = 30654325) B30654325
theorem B54496577 : Blo 2239435 54496577 := bstep (se 2 (by rfl) ⟨20436216, by rfl⟩ : syracuseStep 54496577 = 40872433) B40872433
theorem B145324205 : Blo 2239435 145324205 := bstep (se 3 (by rfl) ⟨27248288, by rfl⟩ : syracuseStep 145324205 = 54496577) B54496577
theorem B96882803 : Blo 2239435 96882803 := bstep (se 1 (by rfl) ⟨72662102, by rfl⟩ : syracuseStep 96882803 = 145324205) B145324205
theorem B64588535 : Blo 2239435 64588535 := bstep (se 1 (by rfl) ⟨48441401, by rfl⟩ : syracuseStep 64588535 = 96882803) B96882803
theorem B43059023 : Blo 2239435 43059023 := bstep (se 1 (by rfl) ⟨32294267, by rfl⟩ : syracuseStep 43059023 = 64588535) B64588535
theorem B28706015 : Blo 2239435 28706015 := bstep (se 1 (by rfl) ⟨21529511, by rfl⟩ : syracuseStep 28706015 = 43059023) B43059023
theorem B19137343 : Blo 2239435 19137343 := bstep (se 1 (by rfl) ⟨14353007, by rfl⟩ : syracuseStep 19137343 = 28706015) B28706015
theorem B25516457 : Blo 2239435 25516457 := bstep (se 2 (by rfl) ⟨9568671, by rfl⟩ : syracuseStep 25516457 = 19137343) B19137343
theorem B17010971 : Blo 2239435 17010971 := bstep (se 1 (by rfl) ⟨12758228, by rfl⟩ : syracuseStep 17010971 = 25516457) B25516457
theorem B11340647 : Blo 2239435 11340647 := bstep (se 1 (by rfl) ⟨8505485, by rfl⟩ : syracuseStep 11340647 = 17010971) B17010971
theorem B7560431 : Blo 2239435 7560431 := bstep (se 1 (by rfl) ⟨5670323, by rfl⟩ : syracuseStep 7560431 = 11340647) B11340647
theorem B5040287 : Blo 2239435 5040287 := bstep (se 1 (by rfl) ⟨3780215, by rfl⟩ : syracuseStep 5040287 = 7560431) B7560431
theorem B3360191 : Blo 2239435 3360191 := bstep (se 1 (by rfl) ⟨2520143, by rfl⟩ : syracuseStep 3360191 = 5040287) B5040287
theorem B2240127 : Blo 2239435 2240127 := bstep (se 1 (by rfl) ⟨1680095, by rfl⟩ : syracuseStep 2240127 = 3360191) B3360191
theorem B3360197 : Blo 2239435 3360197 := bbase (se 4 (by rfl) ⟨315018, by rfl⟩ : syracuseStep 3360197 = 630037) (by norm_num)
theorem B2240131 : Blo 2239435 2240131 := bstep (se 1 (by rfl) ⟨1680098, by rfl⟩ : syracuseStep 2240131 = 3360197) B3360197
theorem B3780229 : Blo 2239435 3780229 := bbase (se 4 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 3780229 = 708793) (by norm_num)
theorem B5040305 : Blo 2239435 5040305 := bstep (se 2 (by rfl) ⟨1890114, by rfl⟩ : syracuseStep 5040305 = 3780229) B3780229
theorem B3360203 : Blo 2239435 3360203 := bstep (se 1 (by rfl) ⟨2520152, by rfl⟩ : syracuseStep 3360203 = 5040305) B5040305
theorem B2240135 : Blo 2239435 2240135 := bstep (se 1 (by rfl) ⟨1680101, by rfl⟩ : syracuseStep 2240135 = 3360203) B3360203
theorem B2520157 : Blo 2239435 2520157 := bbase (se 3 (by rfl) ⟨472529, by rfl⟩ : syracuseStep 2520157 = 945059) (by norm_num)
theorem B3360209 : Blo 2239435 3360209 := bstep (se 2 (by rfl) ⟨1260078, by rfl⟩ : syracuseStep 3360209 = 2520157) B2520157
theorem B2240139 : Blo 2239435 2240139 := bstep (se 1 (by rfl) ⟨1680104, by rfl⟩ : syracuseStep 2240139 = 3360209) B3360209
theorem B7560485 : Blo 2239435 7560485 := bbase (se 4 (by rfl) ⟨708795, by rfl⟩ : syracuseStep 7560485 = 1417591) (by norm_num)
theorem B5040323 : Blo 2239435 5040323 := bstep (se 1 (by rfl) ⟨3780242, by rfl⟩ : syracuseStep 5040323 = 7560485) B7560485
theorem B3360215 : Blo 2239435 3360215 := bstep (se 1 (by rfl) ⟨2520161, by rfl⟩ : syracuseStep 3360215 = 5040323) B5040323
theorem B2240143 : Blo 2239435 2240143 := bstep (se 1 (by rfl) ⟨1680107, by rfl⟩ : syracuseStep 2240143 = 3360215) B3360215
theorem B3360221 : Blo 2239435 3360221 := bbase (se 3 (by rfl) ⟨630041, by rfl⟩ : syracuseStep 3360221 = 1260083) (by norm_num)
theorem B2240147 : Blo 2239435 2240147 := bstep (se 1 (by rfl) ⟨1680110, by rfl⟩ : syracuseStep 2240147 = 3360221) B3360221
theorem B5040341 : Blo 2239435 5040341 := bbase (se 7 (by rfl) ⟨59066, by rfl⟩ : syracuseStep 5040341 = 118133) (by norm_num)
theorem B3360227 : Blo 2239435 3360227 := bstep (se 1 (by rfl) ⟨2520170, by rfl⟩ : syracuseStep 3360227 = 5040341) B5040341
theorem B2240151 : Blo 2239435 2240151 := bstep (se 1 (by rfl) ⟨1680113, by rfl⟩ : syracuseStep 2240151 = 3360227) B3360227
theorem B6055253 : Blo 2239435 6055253 := bbase (se 12 (by rfl) ⟨2217, by rfl⟩ : syracuseStep 6055253 = 4435) (by norm_num)
theorem B4036835 : Blo 2239435 4036835 := bstep (se 1 (by rfl) ⟨3027626, by rfl⟩ : syracuseStep 4036835 = 6055253) B6055253
theorem B10764893 : Blo 2239435 10764893 := bstep (se 3 (by rfl) ⟨2018417, by rfl⟩ : syracuseStep 10764893 = 4036835) B4036835
theorem B7176595 : Blo 2239435 7176595 := bstep (se 1 (by rfl) ⟨5382446, by rfl⟩ : syracuseStep 7176595 = 10764893) B10764893
theorem B9568793 : Blo 2239435 9568793 := bstep (se 2 (by rfl) ⟨3588297, by rfl⟩ : syracuseStep 9568793 = 7176595) B7176595
theorem B6379195 : Blo 2239435 6379195 := bstep (se 1 (by rfl) ⟨4784396, by rfl⟩ : syracuseStep 6379195 = 9568793) B9568793
theorem B8505593 : Blo 2239435 8505593 := bstep (se 2 (by rfl) ⟨3189597, by rfl⟩ : syracuseStep 8505593 = 6379195) B6379195
theorem B5670395 : Blo 2239435 5670395 := bstep (se 1 (by rfl) ⟨4252796, by rfl⟩ : syracuseStep 5670395 = 8505593) B8505593
theorem B3780263 : Blo 2239435 3780263 := bstep (se 1 (by rfl) ⟨2835197, by rfl⟩ : syracuseStep 3780263 = 5670395) B5670395
theorem B2520175 : Blo 2239435 2520175 := bstep (se 1 (by rfl) ⟨1890131, by rfl⟩ : syracuseStep 2520175 = 3780263) B3780263
theorem B3360233 : Blo 2239435 3360233 := bstep (se 2 (by rfl) ⟨1260087, by rfl⟩ : syracuseStep 3360233 = 2520175) B2520175
theorem B2240155 : Blo 2239435 2240155 := bstep (se 1 (by rfl) ⟨1680116, by rfl⟩ : syracuseStep 2240155 = 3360233) B3360233
theorem B2873885 : Blo 2239435 2873885 := bbase (se 3 (by rfl) ⟨538853, by rfl⟩ : syracuseStep 2873885 = 1077707) (by norm_num)
theorem B7663693 : Blo 2239435 7663693 := bstep (se 3 (by rfl) ⟨1436942, by rfl⟩ : syracuseStep 7663693 = 2873885) B2873885
theorem B10218257 : Blo 2239435 10218257 := bstep (se 2 (by rfl) ⟨3831846, by rfl⟩ : syracuseStep 10218257 = 7663693) B7663693
theorem B6812171 : Blo 2239435 6812171 := bstep (se 1 (by rfl) ⟨5109128, by rfl⟩ : syracuseStep 6812171 = 10218257) B10218257
theorem B4541447 : Blo 2239435 4541447 := bstep (se 1 (by rfl) ⟨3406085, by rfl⟩ : syracuseStep 4541447 = 6812171) B6812171
theorem B12110525 : Blo 2239435 12110525 := bstep (se 3 (by rfl) ⟨2270723, by rfl⟩ : syracuseStep 12110525 = 4541447) B4541447
theorem B8073683 : Blo 2239435 8073683 := bstep (se 1 (by rfl) ⟨6055262, by rfl⟩ : syracuseStep 8073683 = 12110525) B12110525
theorem B5382455 : Blo 2239435 5382455 := bstep (se 1 (by rfl) ⟨4036841, by rfl⟩ : syracuseStep 5382455 = 8073683) B8073683
theorem B14353213 : Blo 2239435 14353213 := bstep (se 3 (by rfl) ⟨2691227, by rfl⟩ : syracuseStep 14353213 = 5382455) B5382455
theorem B19137617 : Blo 2239435 19137617 := bstep (se 2 (by rfl) ⟨7176606, by rfl⟩ : syracuseStep 19137617 = 14353213) B14353213
theorem B12758411 : Blo 2239435 12758411 := bstep (se 1 (by rfl) ⟨9568808, by rfl⟩ : syracuseStep 12758411 = 19137617) B19137617
theorem B8505607 : Blo 2239435 8505607 := bstep (se 1 (by rfl) ⟨6379205, by rfl⟩ : syracuseStep 8505607 = 12758411) B12758411
theorem B11340809 : Blo 2239435 11340809 := bstep (se 2 (by rfl) ⟨4252803, by rfl⟩ : syracuseStep 11340809 = 8505607) B8505607
theorem B7560539 : Blo 2239435 7560539 := bstep (se 1 (by rfl) ⟨5670404, by rfl⟩ : syracuseStep 7560539 = 11340809) B11340809
theorem B5040359 : Blo 2239435 5040359 := bstep (se 1 (by rfl) ⟨3780269, by rfl⟩ : syracuseStep 5040359 = 7560539) B7560539
theorem B3360239 : Blo 2239435 3360239 := bstep (se 1 (by rfl) ⟨2520179, by rfl⟩ : syracuseStep 3360239 = 5040359) B5040359
theorem B2240159 : Blo 2239435 2240159 := bstep (se 1 (by rfl) ⟨1680119, by rfl⟩ : syracuseStep 2240159 = 3360239) B3360239
theorem B3360245 : Blo 2239435 3360245 := bbase (se 5 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 3360245 = 315023) (by norm_num)
theorem B2240163 : Blo 2239435 2240163 := bstep (se 1 (by rfl) ⟨1680122, by rfl⟩ : syracuseStep 2240163 = 3360245) B3360245
theorem B3588317 : Blo 2239435 3588317 := bbase (se 3 (by rfl) ⟨672809, by rfl⟩ : syracuseStep 3588317 = 1345619) (by norm_num)
theorem B2392211 : Blo 2239435 2392211 := bstep (se 1 (by rfl) ⟨1794158, by rfl⟩ : syracuseStep 2392211 = 3588317) B3588317
theorem B6379229 : Blo 2239435 6379229 := bstep (se 3 (by rfl) ⟨1196105, by rfl⟩ : syracuseStep 6379229 = 2392211) B2392211
theorem B4252819 : Blo 2239435 4252819 := bstep (se 1 (by rfl) ⟨3189614, by rfl⟩ : syracuseStep 4252819 = 6379229) B6379229
theorem B5670425 : Blo 2239435 5670425 := bstep (se 2 (by rfl) ⟨2126409, by rfl⟩ : syracuseStep 5670425 = 4252819) B4252819
theorem B3780283 : Blo 2239435 3780283 := bstep (se 1 (by rfl) ⟨2835212, by rfl⟩ : syracuseStep 3780283 = 5670425) B5670425
theorem B5040377 : Blo 2239435 5040377 := bstep (se 2 (by rfl) ⟨1890141, by rfl⟩ : syracuseStep 5040377 = 3780283) B3780283
theorem B3360251 : Blo 2239435 3360251 := bstep (se 1 (by rfl) ⟨2520188, by rfl⟩ : syracuseStep 3360251 = 5040377) B5040377
theorem B2240167 : Blo 2239435 2240167 := bstep (se 1 (by rfl) ⟨1680125, by rfl⟩ : syracuseStep 2240167 = 3360251) B3360251
theorem B2520193 : Blo 2239435 2520193 := bbase (se 2 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 2520193 = 1890145) (by norm_num)
theorem B3360257 : Blo 2239435 3360257 := bstep (se 2 (by rfl) ⟨1260096, by rfl⟩ : syracuseStep 3360257 = 2520193) B2520193
theorem B2240171 : Blo 2239435 2240171 := bstep (se 1 (by rfl) ⟨1680128, by rfl⟩ : syracuseStep 2240171 = 3360257) B3360257
theorem B5670445 : Blo 2239435 5670445 := bbase (se 3 (by rfl) ⟨1063208, by rfl⟩ : syracuseStep 5670445 = 2126417) (by norm_num)
theorem B7560593 : Blo 2239435 7560593 := bstep (se 2 (by rfl) ⟨2835222, by rfl⟩ : syracuseStep 7560593 = 5670445) B5670445
theorem B5040395 : Blo 2239435 5040395 := bstep (se 1 (by rfl) ⟨3780296, by rfl⟩ : syracuseStep 5040395 = 7560593) B7560593
theorem B3360263 : Blo 2239435 3360263 := bstep (se 1 (by rfl) ⟨2520197, by rfl⟩ : syracuseStep 3360263 = 5040395) B5040395
theorem B2240175 : Blo 2239435 2240175 := bstep (se 1 (by rfl) ⟨1680131, by rfl⟩ : syracuseStep 2240175 = 3360263) B3360263
theorem B3360269 : Blo 2239435 3360269 := bbase (se 3 (by rfl) ⟨630050, by rfl⟩ : syracuseStep 3360269 = 1260101) (by norm_num)
theorem B2240179 : Blo 2239435 2240179 := bstep (se 1 (by rfl) ⟨1680134, by rfl⟩ : syracuseStep 2240179 = 3360269) B3360269
theorem B5040413 : Blo 2239435 5040413 := bbase (se 3 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 5040413 = 1890155) (by norm_num)
theorem B3360275 : Blo 2239435 3360275 := bstep (se 1 (by rfl) ⟨2520206, by rfl⟩ : syracuseStep 3360275 = 5040413) B5040413
theorem B2240183 : Blo 2239435 2240183 := bstep (se 1 (by rfl) ⟨1680137, by rfl⟩ : syracuseStep 2240183 = 3360275) B3360275
theorem B3780317 : Blo 2239435 3780317 := bbase (se 3 (by rfl) ⟨708809, by rfl⟩ : syracuseStep 3780317 = 1417619) (by norm_num)
theorem B2520211 : Blo 2239435 2520211 := bstep (se 1 (by rfl) ⟨1890158, by rfl⟩ : syracuseStep 2520211 = 3780317) B3780317
theorem B3360281 : Blo 2239435 3360281 := bstep (se 2 (by rfl) ⟨1260105, by rfl⟩ : syracuseStep 3360281 = 2520211) B2520211
theorem B2240187 : Blo 2239435 2240187 := bstep (se 1 (by rfl) ⟨1680140, by rfl⟩ : syracuseStep 2240187 = 3360281) B3360281
theorem B7176709 : Blo 2239435 7176709 := bbase (se 4 (by rfl) ⟨672816, by rfl⟩ : syracuseStep 7176709 = 1345633) (by norm_num)
theorem B9568945 : Blo 2239435 9568945 := bstep (se 2 (by rfl) ⟨3588354, by rfl⟩ : syracuseStep 9568945 = 7176709) B7176709
theorem B12758593 : Blo 2239435 12758593 := bstep (se 2 (by rfl) ⟨4784472, by rfl⟩ : syracuseStep 12758593 = 9568945) B9568945
theorem B17011457 : Blo 2239435 17011457 := bstep (se 2 (by rfl) ⟨6379296, by rfl⟩ : syracuseStep 17011457 = 12758593) B12758593
theorem B11340971 : Blo 2239435 11340971 := bstep (se 1 (by rfl) ⟨8505728, by rfl⟩ : syracuseStep 11340971 = 17011457) B17011457
theorem B7560647 : Blo 2239435 7560647 := bstep (se 1 (by rfl) ⟨5670485, by rfl⟩ : syracuseStep 7560647 = 11340971) B11340971
theorem B5040431 : Blo 2239435 5040431 := bstep (se 1 (by rfl) ⟨3780323, by rfl⟩ : syracuseStep 5040431 = 7560647) B7560647
theorem B3360287 : Blo 2239435 3360287 := bstep (se 1 (by rfl) ⟨2520215, by rfl⟩ : syracuseStep 3360287 = 5040431) B5040431
theorem B2240191 : Blo 2239435 2240191 := bstep (se 1 (by rfl) ⟨1680143, by rfl⟩ : syracuseStep 2240191 = 3360287) B3360287
theorem B3360293 : Blo 2239435 3360293 := bbase (se 4 (by rfl) ⟨315027, by rfl⟩ : syracuseStep 3360293 = 630055) (by norm_num)
theorem B2240195 : Blo 2239435 2240195 := bstep (se 1 (by rfl) ⟨1680146, by rfl⟩ : syracuseStep 2240195 = 3360293) B3360293
theorem B2835253 : Blo 2239435 2835253 := bbase (se 5 (by rfl) ⟨132902, by rfl⟩ : syracuseStep 2835253 = 265805) (by norm_num)
theorem B3780337 : Blo 2239435 3780337 := bstep (se 2 (by rfl) ⟨1417626, by rfl⟩ : syracuseStep 3780337 = 2835253) B2835253
theorem B5040449 : Blo 2239435 5040449 := bstep (se 2 (by rfl) ⟨1890168, by rfl⟩ : syracuseStep 5040449 = 3780337) B3780337
theorem B3360299 : Blo 2239435 3360299 := bstep (se 1 (by rfl) ⟨2520224, by rfl⟩ : syracuseStep 3360299 = 5040449) B5040449
theorem B2240199 : Blo 2239435 2240199 := bstep (se 1 (by rfl) ⟨1680149, by rfl⟩ : syracuseStep 2240199 = 3360299) B3360299
theorem B2520229 : Blo 2239435 2520229 := bbase (se 4 (by rfl) ⟨236271, by rfl⟩ : syracuseStep 2520229 = 472543) (by norm_num)
theorem B3360305 : Blo 2239435 3360305 := bstep (se 2 (by rfl) ⟨1260114, by rfl⟩ : syracuseStep 3360305 = 2520229) B2520229
theorem B2240203 : Blo 2239435 2240203 := bstep (se 1 (by rfl) ⟨1680152, by rfl⟩ : syracuseStep 2240203 = 3360305) B3360305
theorem B3884213 : Blo 2239435 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2589475 : Blo 2239435 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B3452633 : Blo 2239435 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2301755 : Blo 2239435 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B6138013 : Blo 2239435 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B8184017 : Blo 2239435 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B5456011 : Blo 2239435 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B7274681 : Blo 2239435 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B4849787 : Blo 2239435 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B3233191 : Blo 2239435 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B4310921 : Blo 2239435 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B11495789 : Blo 2239435 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B7663859 : Blo 2239435 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B5109239 : Blo 2239435 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B3406159 : Blo 2239435 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B4541545 : Blo 2239435 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B6055393 : Blo 2239435 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B8073857 : Blo 2239435 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B21530285 : Blo 2239435 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B14353523 : Blo 2239435 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B9569015 : Blo 2239435 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B6379343 : Blo 2239435 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B4252895 : Blo 2239435 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B2835263 : Blo 2239435 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B7560701 : Blo 2239435 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B5040467 : Blo 2239435 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B3360311 : Blo 2239435 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B2240207 : Blo 2239435 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B3360317 : Blo 2239435 3360317 := bbase (se 3 (by rfl) ⟨630059, by rfl⟩ : syracuseStep 3360317 = 1260119) (by norm_num)
theorem B2240211 : Blo 2239435 2240211 := bstep (se 1 (by rfl) ⟨1680158, by rfl⟩ : syracuseStep 2240211 = 3360317) B3360317
theorem B5040485 : Blo 2239435 5040485 := bbase (se 4 (by rfl) ⟨472545, by rfl⟩ : syracuseStep 5040485 = 945091) (by norm_num)
theorem B3360323 : Blo 2239435 3360323 := bstep (se 1 (by rfl) ⟨2520242, by rfl⟩ : syracuseStep 3360323 = 5040485) B5040485
theorem B2240215 : Blo 2239435 2240215 := bstep (se 1 (by rfl) ⟨1680161, by rfl⟩ : syracuseStep 2240215 = 3360323) B3360323
theorem B5670557 : Blo 2239435 5670557 := bbase (se 3 (by rfl) ⟨1063229, by rfl⟩ : syracuseStep 5670557 = 2126459) (by norm_num)
theorem B3780371 : Blo 2239435 3780371 := bstep (se 1 (by rfl) ⟨2835278, by rfl⟩ : syracuseStep 3780371 = 5670557) B5670557
theorem B2520247 : Blo 2239435 2520247 := bstep (se 1 (by rfl) ⟨1890185, by rfl⟩ : syracuseStep 2520247 = 3780371) B3780371
theorem B3360329 : Blo 2239435 3360329 := bstep (se 2 (by rfl) ⟨1260123, by rfl⟩ : syracuseStep 3360329 = 2520247) B2520247
theorem B2240219 : Blo 2239435 2240219 := bstep (se 1 (by rfl) ⟨1680164, by rfl⟩ : syracuseStep 2240219 = 3360329) B3360329
theorem B4252925 : Blo 2239435 4252925 := bbase (se 3 (by rfl) ⟨797423, by rfl⟩ : syracuseStep 4252925 = 1594847) (by norm_num)
theorem B11341133 : Blo 2239435 11341133 := bstep (se 3 (by rfl) ⟨2126462, by rfl⟩ : syracuseStep 11341133 = 4252925) B4252925
theorem B7560755 : Blo 2239435 7560755 := bstep (se 1 (by rfl) ⟨5670566, by rfl⟩ : syracuseStep 7560755 = 11341133) B11341133
theorem B5040503 : Blo 2239435 5040503 := bstep (se 1 (by rfl) ⟨3780377, by rfl⟩ : syracuseStep 5040503 = 7560755) B7560755
theorem B3360335 : Blo 2239435 3360335 := bstep (se 1 (by rfl) ⟨2520251, by rfl⟩ : syracuseStep 3360335 = 5040503) B5040503
theorem B2240223 : Blo 2239435 2240223 := bstep (se 1 (by rfl) ⟨1680167, by rfl⟩ : syracuseStep 2240223 = 3360335) B3360335
theorem B3360341 : Blo 2239435 3360341 := bbase (se 8 (by rfl) ⟨19689, by rfl⟩ : syracuseStep 3360341 = 39379) (by norm_num)
theorem B2240227 : Blo 2239435 2240227 := bstep (se 1 (by rfl) ⟨1680170, by rfl⟩ : syracuseStep 2240227 = 3360341) B3360341
theorem B5382629 : Blo 2239435 5382629 := bbase (se 4 (by rfl) ⟨504621, by rfl⟩ : syracuseStep 5382629 = 1009243) (by norm_num)
theorem B3588419 : Blo 2239435 3588419 := bstep (se 1 (by rfl) ⟨2691314, by rfl⟩ : syracuseStep 3588419 = 5382629) B5382629
theorem B9569117 : Blo 2239435 9569117 := bstep (se 3 (by rfl) ⟨1794209, by rfl⟩ : syracuseStep 9569117 = 3588419) B3588419
theorem B6379411 : Blo 2239435 6379411 := bstep (se 1 (by rfl) ⟨4784558, by rfl⟩ : syracuseStep 6379411 = 9569117) B9569117
theorem B8505881 : Blo 2239435 8505881 := bstep (se 2 (by rfl) ⟨3189705, by rfl⟩ : syracuseStep 8505881 = 6379411) B6379411
theorem B5670587 : Blo 2239435 5670587 := bstep (se 1 (by rfl) ⟨4252940, by rfl⟩ : syracuseStep 5670587 = 8505881) B8505881
theorem B3780391 : Blo 2239435 3780391 := bstep (se 1 (by rfl) ⟨2835293, by rfl⟩ : syracuseStep 3780391 = 5670587) B5670587
theorem B5040521 : Blo 2239435 5040521 := bstep (se 2 (by rfl) ⟨1890195, by rfl⟩ : syracuseStep 5040521 = 3780391) B3780391
theorem B3360347 : Blo 2239435 3360347 := bstep (se 1 (by rfl) ⟨2520260, by rfl⟩ : syracuseStep 3360347 = 5040521) B5040521
theorem B2240231 : Blo 2239435 2240231 := bstep (se 1 (by rfl) ⟨1680173, by rfl⟩ : syracuseStep 2240231 = 3360347) B3360347
theorem B2520265 : Blo 2239435 2520265 := bbase (se 2 (by rfl) ⟨945099, by rfl⟩ : syracuseStep 2520265 = 1890199) (by norm_num)
theorem B3360353 : Blo 2239435 3360353 := bstep (se 2 (by rfl) ⟨1260132, by rfl⟩ : syracuseStep 3360353 = 2520265) B2520265
theorem B2240235 : Blo 2239435 2240235 := bstep (se 1 (by rfl) ⟨1680176, by rfl⟩ : syracuseStep 2240235 = 3360353) B3360353
theorem B23305589 : Blo 2239435 23305589 := bbase (se 5 (by rfl) ⟨1092449, by rfl⟩ : syracuseStep 23305589 = 2184899) (by norm_num)
theorem B15537059 : Blo 2239435 15537059 := bstep (se 1 (by rfl) ⟨11652794, by rfl⟩ : syracuseStep 15537059 = 23305589) B23305589
theorem B10358039 : Blo 2239435 10358039 := bstep (se 1 (by rfl) ⟨7768529, by rfl⟩ : syracuseStep 10358039 = 15537059) B15537059
theorem B6905359 : Blo 2239435 6905359 := bstep (se 1 (by rfl) ⟨5179019, by rfl⟩ : syracuseStep 6905359 = 10358039) B10358039
theorem B9207145 : Blo 2239435 9207145 := bstep (se 2 (by rfl) ⟨3452679, by rfl⟩ : syracuseStep 9207145 = 6905359) B6905359
theorem B12276193 : Blo 2239435 12276193 := bstep (se 2 (by rfl) ⟨4603572, by rfl⟩ : syracuseStep 12276193 = 9207145) B9207145
theorem B16368257 : Blo 2239435 16368257 := bstep (se 2 (by rfl) ⟨6138096, by rfl⟩ : syracuseStep 16368257 = 12276193) B12276193
theorem B10912171 : Blo 2239435 10912171 := bstep (se 1 (by rfl) ⟨8184128, by rfl⟩ : syracuseStep 10912171 = 16368257) B16368257
theorem B14549561 : Blo 2239435 14549561 := bstep (se 2 (by rfl) ⟨5456085, by rfl⟩ : syracuseStep 14549561 = 10912171) B10912171
theorem B9699707 : Blo 2239435 9699707 := bstep (se 1 (by rfl) ⟨7274780, by rfl⟩ : syracuseStep 9699707 = 14549561) B14549561
theorem B25865885 : Blo 2239435 25865885 := bstep (se 3 (by rfl) ⟨4849853, by rfl⟩ : syracuseStep 25865885 = 9699707) B9699707
theorem B17243923 : Blo 2239435 17243923 := bstep (se 1 (by rfl) ⟨12932942, by rfl⟩ : syracuseStep 17243923 = 25865885) B25865885
theorem B22991897 : Blo 2239435 22991897 := bstep (se 2 (by rfl) ⟨8621961, by rfl⟩ : syracuseStep 22991897 = 17243923) B17243923
theorem B61311725 : Blo 2239435 61311725 := bstep (se 3 (by rfl) ⟨11495948, by rfl⟩ : syracuseStep 61311725 = 22991897) B22991897
theorem B40874483 : Blo 2239435 40874483 := bstep (se 1 (by rfl) ⟨30655862, by rfl⟩ : syracuseStep 40874483 = 61311725) B61311725
theorem B27249655 : Blo 2239435 27249655 := bstep (se 1 (by rfl) ⟨20437241, by rfl⟩ : syracuseStep 27249655 = 40874483) B40874483
theorem B36332873 : Blo 2239435 36332873 := bstep (se 2 (by rfl) ⟨13624827, by rfl⟩ : syracuseStep 36332873 = 27249655) B27249655
theorem B24221915 : Blo 2239435 24221915 := bstep (se 1 (by rfl) ⟨18166436, by rfl⟩ : syracuseStep 24221915 = 36332873) B36332873
theorem B16147943 : Blo 2239435 16147943 := bstep (se 1 (by rfl) ⟨12110957, by rfl⟩ : syracuseStep 16147943 = 24221915) B24221915
theorem B10765295 : Blo 2239435 10765295 := bstep (se 1 (by rfl) ⟨8073971, by rfl⟩ : syracuseStep 10765295 = 16147943) B16147943
theorem B7176863 : Blo 2239435 7176863 := bstep (se 1 (by rfl) ⟨5382647, by rfl⟩ : syracuseStep 7176863 = 10765295) B10765295
theorem B19138301 : Blo 2239435 19138301 := bstep (se 3 (by rfl) ⟨3588431, by rfl⟩ : syracuseStep 19138301 = 7176863) B7176863
theorem B12758867 : Blo 2239435 12758867 := bstep (se 1 (by rfl) ⟨9569150, by rfl⟩ : syracuseStep 12758867 = 19138301) B19138301
theorem B8505911 : Blo 2239435 8505911 := bstep (se 1 (by rfl) ⟨6379433, by rfl⟩ : syracuseStep 8505911 = 12758867) B12758867
theorem B5670607 : Blo 2239435 5670607 := bstep (se 1 (by rfl) ⟨4252955, by rfl⟩ : syracuseStep 5670607 = 8505911) B8505911
theorem B7560809 : Blo 2239435 7560809 := bstep (se 2 (by rfl) ⟨2835303, by rfl⟩ : syracuseStep 7560809 = 5670607) B5670607
theorem B5040539 : Blo 2239435 5040539 := bstep (se 1 (by rfl) ⟨3780404, by rfl⟩ : syracuseStep 5040539 = 7560809) B7560809
theorem B3360359 : Blo 2239435 3360359 := bstep (se 1 (by rfl) ⟨2520269, by rfl⟩ : syracuseStep 3360359 = 5040539) B5040539
theorem B2240239 : Blo 2239435 2240239 := bstep (se 1 (by rfl) ⟨1680179, by rfl⟩ : syracuseStep 2240239 = 3360359) B3360359
theorem B3360365 : Blo 2239435 3360365 := bbase (se 3 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 3360365 = 1260137) (by norm_num)
theorem B2240243 : Blo 2239435 2240243 := bstep (se 1 (by rfl) ⟨1680182, by rfl⟩ : syracuseStep 2240243 = 3360365) B3360365
theorem B5040557 : Blo 2239435 5040557 := bbase (se 3 (by rfl) ⟨945104, by rfl⟩ : syracuseStep 5040557 = 1890209) (by norm_num)
theorem B3360371 : Blo 2239435 3360371 := bstep (se 1 (by rfl) ⟨2520278, by rfl⟩ : syracuseStep 3360371 = 5040557) B5040557
theorem B2240247 : Blo 2239435 2240247 := bstep (se 1 (by rfl) ⟨1680185, by rfl⟩ : syracuseStep 2240247 = 3360371) B3360371
theorem B2392301 : Blo 2239435 2392301 := bbase (se 3 (by rfl) ⟨448556, by rfl⟩ : syracuseStep 2392301 = 897113) (by norm_num)
theorem B6379469 : Blo 2239435 6379469 := bstep (se 3 (by rfl) ⟨1196150, by rfl⟩ : syracuseStep 6379469 = 2392301) B2392301
theorem B4252979 : Blo 2239435 4252979 := bstep (se 1 (by rfl) ⟨3189734, by rfl⟩ : syracuseStep 4252979 = 6379469) B6379469
theorem B2835319 : Blo 2239435 2835319 := bstep (se 1 (by rfl) ⟨2126489, by rfl⟩ : syracuseStep 2835319 = 4252979) B4252979
theorem B3780425 : Blo 2239435 3780425 := bstep (se 2 (by rfl) ⟨1417659, by rfl⟩ : syracuseStep 3780425 = 2835319) B2835319
theorem B2520283 : Blo 2239435 2520283 := bstep (se 1 (by rfl) ⟨1890212, by rfl⟩ : syracuseStep 2520283 = 3780425) B3780425
theorem B3360377 : Blo 2239435 3360377 := bstep (se 2 (by rfl) ⟨1260141, by rfl⟩ : syracuseStep 3360377 = 2520283) B2520283
theorem B2240251 : Blo 2239435 2240251 := bstep (se 1 (by rfl) ⟨1680188, by rfl⟩ : syracuseStep 2240251 = 3360377) B3360377
theorem B5530565 : Blo 2239435 5530565 := bbase (se 4 (by rfl) ⟨518490, by rfl⟩ : syracuseStep 5530565 = 1036981) (by norm_num)
theorem B3687043 : Blo 2239435 3687043 := bstep (se 1 (by rfl) ⟨2765282, by rfl⟩ : syracuseStep 3687043 = 5530565) B5530565
theorem B4916057 : Blo 2239435 4916057 := bstep (se 2 (by rfl) ⟨1843521, by rfl⟩ : syracuseStep 4916057 = 3687043) B3687043
theorem B52437941 : Blo 2239435 52437941 := bstep (se 5 (by rfl) ⟨2458028, by rfl⟩ : syracuseStep 52437941 = 4916057) B4916057
theorem B34958627 : Blo 2239435 34958627 := bstep (se 1 (by rfl) ⟨26218970, by rfl⟩ : syracuseStep 34958627 = 52437941) B52437941
theorem B23305751 : Blo 2239435 23305751 := bstep (se 1 (by rfl) ⟨17479313, by rfl⟩ : syracuseStep 23305751 = 34958627) B34958627
theorem B15537167 : Blo 2239435 15537167 := bstep (se 1 (by rfl) ⟨11652875, by rfl⟩ : syracuseStep 15537167 = 23305751) B23305751
theorem B10358111 : Blo 2239435 10358111 := bstep (se 1 (by rfl) ⟨7768583, by rfl⟩ : syracuseStep 10358111 = 15537167) B15537167
theorem B6905407 : Blo 2239435 6905407 := bstep (se 1 (by rfl) ⟨5179055, by rfl⟩ : syracuseStep 6905407 = 10358111) B10358111
theorem B9207209 : Blo 2239435 9207209 := bstep (se 2 (by rfl) ⟨3452703, by rfl⟩ : syracuseStep 9207209 = 6905407) B6905407
theorem B24552557 : Blo 2239435 24552557 := bstep (se 3 (by rfl) ⟨4603604, by rfl⟩ : syracuseStep 24552557 = 9207209) B9207209
theorem B16368371 : Blo 2239435 16368371 := bstep (se 1 (by rfl) ⟨12276278, by rfl⟩ : syracuseStep 16368371 = 24552557) B24552557
theorem B10912247 : Blo 2239435 10912247 := bstep (se 1 (by rfl) ⟨8184185, by rfl⟩ : syracuseStep 10912247 = 16368371) B16368371
theorem B7274831 : Blo 2239435 7274831 := bstep (se 1 (by rfl) ⟨5456123, by rfl⟩ : syracuseStep 7274831 = 10912247) B10912247
theorem B19399549 : Blo 2239435 19399549 := bstep (se 3 (by rfl) ⟨3637415, by rfl⟩ : syracuseStep 19399549 = 7274831) B7274831
theorem B25866065 : Blo 2239435 25866065 := bstep (se 2 (by rfl) ⟨9699774, by rfl⟩ : syracuseStep 25866065 = 19399549) B19399549
theorem B68976173 : Blo 2239435 68976173 := bstep (se 3 (by rfl) ⟨12933032, by rfl⟩ : syracuseStep 68976173 = 25866065) B25866065
theorem B45984115 : Blo 2239435 45984115 := bstep (se 1 (by rfl) ⟨34488086, by rfl⟩ : syracuseStep 45984115 = 68976173) B68976173
theorem B61312153 : Blo 2239435 61312153 := bstep (se 2 (by rfl) ⟨22992057, by rfl⟩ : syracuseStep 61312153 = 45984115) B45984115
theorem B81749537 : Blo 2239435 81749537 := bstep (se 2 (by rfl) ⟨30656076, by rfl⟩ : syracuseStep 81749537 = 61312153) B61312153
theorem B54499691 : Blo 2239435 54499691 := bstep (se 1 (by rfl) ⟨40874768, by rfl⟩ : syracuseStep 54499691 = 81749537) B81749537
theorem B36333127 : Blo 2239435 36333127 := bstep (se 1 (by rfl) ⟨27249845, by rfl⟩ : syracuseStep 36333127 = 54499691) B54499691
theorem B48444169 : Blo 2239435 48444169 := bstep (se 2 (by rfl) ⟨18166563, by rfl⟩ : syracuseStep 48444169 = 36333127) B36333127
theorem B64592225 : Blo 2239435 64592225 := bstep (se 2 (by rfl) ⟨24222084, by rfl⟩ : syracuseStep 64592225 = 48444169) B48444169
theorem B43061483 : Blo 2239435 43061483 := bstep (se 1 (by rfl) ⟨32296112, by rfl⟩ : syracuseStep 43061483 = 64592225) B64592225
theorem B28707655 : Blo 2239435 28707655 := bstep (se 1 (by rfl) ⟨21530741, by rfl⟩ : syracuseStep 28707655 = 43061483) B43061483
theorem B38276873 : Blo 2239435 38276873 := bstep (se 2 (by rfl) ⟨14353827, by rfl⟩ : syracuseStep 38276873 = 28707655) B28707655
theorem B25517915 : Blo 2239435 25517915 := bstep (se 1 (by rfl) ⟨19138436, by rfl⟩ : syracuseStep 25517915 = 38276873) B38276873
theorem B17011943 : Blo 2239435 17011943 := bstep (se 1 (by rfl) ⟨12758957, by rfl⟩ : syracuseStep 17011943 = 25517915) B25517915
theorem B11341295 : Blo 2239435 11341295 := bstep (se 1 (by rfl) ⟨8505971, by rfl⟩ : syracuseStep 11341295 = 17011943) B17011943
theorem B7560863 : Blo 2239435 7560863 := bstep (se 1 (by rfl) ⟨5670647, by rfl⟩ : syracuseStep 7560863 = 11341295) B11341295
theorem B5040575 : Blo 2239435 5040575 := bstep (se 1 (by rfl) ⟨3780431, by rfl⟩ : syracuseStep 5040575 = 7560863) B7560863
theorem B3360383 : Blo 2239435 3360383 := bstep (se 1 (by rfl) ⟨2520287, by rfl⟩ : syracuseStep 3360383 = 5040575) B5040575
theorem B2240255 : Blo 2239435 2240255 := bstep (se 1 (by rfl) ⟨1680191, by rfl⟩ : syracuseStep 2240255 = 3360383) B3360383
theorem B3360389 : Blo 2239435 3360389 := bbase (se 4 (by rfl) ⟨315036, by rfl⟩ : syracuseStep 3360389 = 630073) (by norm_num)
theorem B2240259 : Blo 2239435 2240259 := bstep (se 1 (by rfl) ⟨1680194, by rfl⟩ : syracuseStep 2240259 = 3360389) B3360389
theorem B3780445 : Blo 2239435 3780445 := bbase (se 3 (by rfl) ⟨708833, by rfl⟩ : syracuseStep 3780445 = 1417667) (by norm_num)
theorem B5040593 : Blo 2239435 5040593 := bstep (se 2 (by rfl) ⟨1890222, by rfl⟩ : syracuseStep 5040593 = 3780445) B3780445
theorem B3360395 : Blo 2239435 3360395 := bstep (se 1 (by rfl) ⟨2520296, by rfl⟩ : syracuseStep 3360395 = 5040593) B5040593
theorem B2240263 : Blo 2239435 2240263 := bstep (se 1 (by rfl) ⟨1680197, by rfl⟩ : syracuseStep 2240263 = 3360395) B3360395
theorem B2520301 : Blo 2239435 2520301 := bbase (se 3 (by rfl) ⟨472556, by rfl⟩ : syracuseStep 2520301 = 945113) (by norm_num)
theorem B3360401 : Blo 2239435 3360401 := bstep (se 2 (by rfl) ⟨1260150, by rfl⟩ : syracuseStep 3360401 = 2520301) B2520301
theorem B2240267 : Blo 2239435 2240267 := bstep (se 1 (by rfl) ⟨1680200, by rfl⟩ : syracuseStep 2240267 = 3360401) B3360401
theorem B7560917 : Blo 2239435 7560917 := bbase (se 7 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 7560917 = 177209) (by norm_num)
theorem B5040611 : Blo 2239435 5040611 := bstep (se 1 (by rfl) ⟨3780458, by rfl⟩ : syracuseStep 5040611 = 7560917) B7560917
theorem B3360407 : Blo 2239435 3360407 := bstep (se 1 (by rfl) ⟨2520305, by rfl⟩ : syracuseStep 3360407 = 5040611) B5040611
theorem B2240271 : Blo 2239435 2240271 := bstep (se 1 (by rfl) ⟨1680203, by rfl⟩ : syracuseStep 2240271 = 3360407) B3360407
theorem B3360413 : Blo 2239435 3360413 := bbase (se 3 (by rfl) ⟨630077, by rfl⟩ : syracuseStep 3360413 = 1260155) (by norm_num)
theorem B2240275 : Blo 2239435 2240275 := bstep (se 1 (by rfl) ⟨1680206, by rfl⟩ : syracuseStep 2240275 = 3360413) B3360413
theorem B5040629 : Blo 2239435 5040629 := bbase (se 5 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 5040629 = 472559) (by norm_num)
theorem B3360419 : Blo 2239435 3360419 := bstep (se 1 (by rfl) ⟨2520314, by rfl⟩ : syracuseStep 3360419 = 5040629) B5040629
theorem B2240279 : Blo 2239435 2240279 := bstep (se 1 (by rfl) ⟨1680209, by rfl⟩ : syracuseStep 2240279 = 3360419) B3360419
theorem B6812549 : Blo 2239435 6812549 := bbase (se 4 (by rfl) ⟨638676, by rfl⟩ : syracuseStep 6812549 = 1277353) (by norm_num)
theorem B4541699 : Blo 2239435 4541699 := bstep (se 1 (by rfl) ⟨3406274, by rfl⟩ : syracuseStep 4541699 = 6812549) B6812549
theorem B3027799 : Blo 2239435 3027799 := bstep (se 1 (by rfl) ⟨2270849, by rfl⟩ : syracuseStep 3027799 = 4541699) B4541699
theorem B16148261 : Blo 2239435 16148261 := bstep (se 4 (by rfl) ⟨1513899, by rfl⟩ : syracuseStep 16148261 = 3027799) B3027799
theorem B43062029 : Blo 2239435 43062029 := bstep (se 3 (by rfl) ⟨8074130, by rfl⟩ : syracuseStep 43062029 = 16148261) B16148261
theorem B28708019 : Blo 2239435 28708019 := bstep (se 1 (by rfl) ⟨21531014, by rfl⟩ : syracuseStep 28708019 = 43062029) B43062029
theorem B19138679 : Blo 2239435 19138679 := bstep (se 1 (by rfl) ⟨14354009, by rfl⟩ : syracuseStep 19138679 = 28708019) B28708019
theorem B12759119 : Blo 2239435 12759119 := bstep (se 1 (by rfl) ⟨9569339, by rfl⟩ : syracuseStep 12759119 = 19138679) B19138679
theorem B8506079 : Blo 2239435 8506079 := bstep (se 1 (by rfl) ⟨6379559, by rfl⟩ : syracuseStep 8506079 = 12759119) B12759119
theorem B5670719 : Blo 2239435 5670719 := bstep (se 1 (by rfl) ⟨4253039, by rfl⟩ : syracuseStep 5670719 = 8506079) B8506079
theorem B3780479 : Blo 2239435 3780479 := bstep (se 1 (by rfl) ⟨2835359, by rfl⟩ : syracuseStep 3780479 = 5670719) B5670719
theorem B2520319 : Blo 2239435 2520319 := bstep (se 1 (by rfl) ⟨1890239, by rfl⟩ : syracuseStep 2520319 = 3780479) B3780479
theorem B3360425 : Blo 2239435 3360425 := bstep (se 2 (by rfl) ⟨1260159, by rfl⟩ : syracuseStep 3360425 = 2520319) B2520319
theorem B2240283 : Blo 2239435 2240283 := bstep (se 1 (by rfl) ⟨1680212, by rfl⟩ : syracuseStep 2240283 = 3360425) B3360425
theorem B3588509 : Blo 2239435 3588509 := bbase (se 3 (by rfl) ⟨672845, by rfl⟩ : syracuseStep 3588509 = 1345691) (by norm_num)
theorem B2392339 : Blo 2239435 2392339 := bstep (se 1 (by rfl) ⟨1794254, by rfl⟩ : syracuseStep 2392339 = 3588509) B3588509
theorem B3189785 : Blo 2239435 3189785 := bstep (se 2 (by rfl) ⟨1196169, by rfl⟩ : syracuseStep 3189785 = 2392339) B2392339
theorem B8506093 : Blo 2239435 8506093 := bstep (se 3 (by rfl) ⟨1594892, by rfl⟩ : syracuseStep 8506093 = 3189785) B3189785
theorem B11341457 : Blo 2239435 11341457 := bstep (se 2 (by rfl) ⟨4253046, by rfl⟩ : syracuseStep 11341457 = 8506093) B8506093
theorem B7560971 : Blo 2239435 7560971 := bstep (se 1 (by rfl) ⟨5670728, by rfl⟩ : syracuseStep 7560971 = 11341457) B11341457
theorem B5040647 : Blo 2239435 5040647 := bstep (se 1 (by rfl) ⟨3780485, by rfl⟩ : syracuseStep 5040647 = 7560971) B7560971
theorem B3360431 : Blo 2239435 3360431 := bstep (se 1 (by rfl) ⟨2520323, by rfl⟩ : syracuseStep 3360431 = 5040647) B5040647
theorem B2240287 : Blo 2239435 2240287 := bstep (se 1 (by rfl) ⟨1680215, by rfl⟩ : syracuseStep 2240287 = 3360431) B3360431
theorem B3360437 : Blo 2239435 3360437 := bbase (se 5 (by rfl) ⟨157520, by rfl⟩ : syracuseStep 3360437 = 315041) (by norm_num)
theorem B2240291 : Blo 2239435 2240291 := bstep (se 1 (by rfl) ⟨1680218, by rfl⟩ : syracuseStep 2240291 = 3360437) B3360437
theorem B5670749 : Blo 2239435 5670749 := bbase (se 3 (by rfl) ⟨1063265, by rfl⟩ : syracuseStep 5670749 = 2126531) (by norm_num)
theorem B3780499 : Blo 2239435 3780499 := bstep (se 1 (by rfl) ⟨2835374, by rfl⟩ : syracuseStep 3780499 = 5670749) B5670749
theorem B5040665 : Blo 2239435 5040665 := bstep (se 2 (by rfl) ⟨1890249, by rfl⟩ : syracuseStep 5040665 = 3780499) B3780499
theorem B3360443 : Blo 2239435 3360443 := bstep (se 1 (by rfl) ⟨2520332, by rfl⟩ : syracuseStep 3360443 = 5040665) B5040665
theorem B2240295 : Blo 2239435 2240295 := bstep (se 1 (by rfl) ⟨1680221, by rfl⟩ : syracuseStep 2240295 = 3360443) B3360443
theorem B2520337 : Blo 2239435 2520337 := bbase (se 2 (by rfl) ⟨945126, by rfl⟩ : syracuseStep 2520337 = 1890253) (by norm_num)
theorem B3360449 : Blo 2239435 3360449 := bstep (se 2 (by rfl) ⟨1260168, by rfl⟩ : syracuseStep 3360449 = 2520337) B2520337
theorem B2240299 : Blo 2239435 2240299 := bstep (se 1 (by rfl) ⟨1680224, by rfl⟩ : syracuseStep 2240299 = 3360449) B3360449
theorem B4253077 : Blo 2239435 4253077 := bbase (se 6 (by rfl) ⟨99681, by rfl⟩ : syracuseStep 4253077 = 199363) (by norm_num)
theorem B5670769 : Blo 2239435 5670769 := bstep (se 2 (by rfl) ⟨2126538, by rfl⟩ : syracuseStep 5670769 = 4253077) B4253077
theorem B7561025 : Blo 2239435 7561025 := bstep (se 2 (by rfl) ⟨2835384, by rfl⟩ : syracuseStep 7561025 = 5670769) B5670769
theorem B5040683 : Blo 2239435 5040683 := bstep (se 1 (by rfl) ⟨3780512, by rfl⟩ : syracuseStep 5040683 = 7561025) B7561025
theorem B3360455 : Blo 2239435 3360455 := bstep (se 1 (by rfl) ⟨2520341, by rfl⟩ : syracuseStep 3360455 = 5040683) B5040683
theorem B2240303 : Blo 2239435 2240303 := bstep (se 1 (by rfl) ⟨1680227, by rfl⟩ : syracuseStep 2240303 = 3360455) B3360455
theorem B3360461 : Blo 2239435 3360461 := bbase (se 3 (by rfl) ⟨630086, by rfl⟩ : syracuseStep 3360461 = 1260173) (by norm_num)
theorem B2240307 : Blo 2239435 2240307 := bstep (se 1 (by rfl) ⟨1680230, by rfl⟩ : syracuseStep 2240307 = 3360461) B3360461
theorem B5040701 : Blo 2239435 5040701 := bbase (se 3 (by rfl) ⟨945131, by rfl⟩ : syracuseStep 5040701 = 1890263) (by norm_num)
theorem B3360467 : Blo 2239435 3360467 := bstep (se 1 (by rfl) ⟨2520350, by rfl⟩ : syracuseStep 3360467 = 5040701) B5040701
theorem B2240311 : Blo 2239435 2240311 := bstep (se 1 (by rfl) ⟨1680233, by rfl⟩ : syracuseStep 2240311 = 3360467) B3360467
theorem B3780533 : Blo 2239435 3780533 := bbase (se 5 (by rfl) ⟨177212, by rfl⟩ : syracuseStep 3780533 = 354425) (by norm_num)
theorem B2520355 : Blo 2239435 2520355 := bstep (se 1 (by rfl) ⟨1890266, by rfl⟩ : syracuseStep 2520355 = 3780533) B3780533
theorem B3360473 : Blo 2239435 3360473 := bstep (se 2 (by rfl) ⟨1260177, by rfl⟩ : syracuseStep 3360473 = 2520355) B2520355
theorem B2240315 : Blo 2239435 2240315 := bstep (se 1 (by rfl) ⟨1680236, by rfl⟩ : syracuseStep 2240315 = 3360473) B3360473
theorem B2392373 : Blo 2239435 2392373 := bbase (se 5 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 2392373 = 224285) (by norm_num)
theorem B6379661 : Blo 2239435 6379661 := bstep (se 3 (by rfl) ⟨1196186, by rfl⟩ : syracuseStep 6379661 = 2392373) B2392373
theorem B17012429 : Blo 2239435 17012429 := bstep (se 3 (by rfl) ⟨3189830, by rfl⟩ : syracuseStep 17012429 = 6379661) B6379661
theorem B11341619 : Blo 2239435 11341619 := bstep (se 1 (by rfl) ⟨8506214, by rfl⟩ : syracuseStep 11341619 = 17012429) B17012429
theorem B7561079 : Blo 2239435 7561079 := bstep (se 1 (by rfl) ⟨5670809, by rfl⟩ : syracuseStep 7561079 = 11341619) B11341619
theorem B5040719 : Blo 2239435 5040719 := bstep (se 1 (by rfl) ⟨3780539, by rfl⟩ : syracuseStep 5040719 = 7561079) B7561079
theorem B3360479 : Blo 2239435 3360479 := bstep (se 1 (by rfl) ⟨2520359, by rfl⟩ : syracuseStep 3360479 = 5040719) B5040719
theorem B2240319 : Blo 2239435 2240319 := bstep (se 1 (by rfl) ⟨1680239, by rfl⟩ : syracuseStep 2240319 = 3360479) B3360479
theorem B3360485 : Blo 2239435 3360485 := bbase (se 4 (by rfl) ⟨315045, by rfl⟩ : syracuseStep 3360485 = 630091) (by norm_num)
theorem B2240323 : Blo 2239435 2240323 := bstep (se 1 (by rfl) ⟨1680242, by rfl⟩ : syracuseStep 2240323 = 3360485) B3360485
theorem B6379685 : Blo 2239435 6379685 := bbase (se 4 (by rfl) ⟨598095, by rfl⟩ : syracuseStep 6379685 = 1196191) (by norm_num)
theorem B4253123 : Blo 2239435 4253123 := bstep (se 1 (by rfl) ⟨3189842, by rfl⟩ : syracuseStep 4253123 = 6379685) B6379685
theorem B2835415 : Blo 2239435 2835415 := bstep (se 1 (by rfl) ⟨2126561, by rfl⟩ : syracuseStep 2835415 = 4253123) B4253123
theorem B3780553 : Blo 2239435 3780553 := bstep (se 2 (by rfl) ⟨1417707, by rfl⟩ : syracuseStep 3780553 = 2835415) B2835415
theorem B5040737 : Blo 2239435 5040737 := bstep (se 2 (by rfl) ⟨1890276, by rfl⟩ : syracuseStep 5040737 = 3780553) B3780553
theorem B3360491 : Blo 2239435 3360491 := bstep (se 1 (by rfl) ⟨2520368, by rfl⟩ : syracuseStep 3360491 = 5040737) B5040737
theorem B2240327 : Blo 2239435 2240327 := bstep (se 1 (by rfl) ⟨1680245, by rfl⟩ : syracuseStep 2240327 = 3360491) B3360491
theorem B2520373 : Blo 2239435 2520373 := bbase (se 5 (by rfl) ⟨118142, by rfl⟩ : syracuseStep 2520373 = 236285) (by norm_num)
theorem B3360497 : Blo 2239435 3360497 := bstep (se 2 (by rfl) ⟨1260186, by rfl⟩ : syracuseStep 3360497 = 2520373) B2520373
theorem B2240331 : Blo 2239435 2240331 := bstep (se 1 (by rfl) ⟨1680248, by rfl⟩ : syracuseStep 2240331 = 3360497) B3360497
theorem B2835425 : Blo 2239435 2835425 := bbase (se 2 (by rfl) ⟨1063284, by rfl⟩ : syracuseStep 2835425 = 2126569) (by norm_num)
theorem B7561133 : Blo 2239435 7561133 := bstep (se 3 (by rfl) ⟨1417712, by rfl⟩ : syracuseStep 7561133 = 2835425) B2835425
theorem B5040755 : Blo 2239435 5040755 := bstep (se 1 (by rfl) ⟨3780566, by rfl⟩ : syracuseStep 5040755 = 7561133) B7561133
theorem B3360503 : Blo 2239435 3360503 := bstep (se 1 (by rfl) ⟨2520377, by rfl⟩ : syracuseStep 3360503 = 5040755) B5040755
theorem B2240335 : Blo 2239435 2240335 := bstep (se 1 (by rfl) ⟨1680251, by rfl⟩ : syracuseStep 2240335 = 3360503) B3360503
theorem B3360509 : Blo 2239435 3360509 := bbase (se 3 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 3360509 = 1260191) (by norm_num)
theorem B2240339 : Blo 2239435 2240339 := bstep (se 1 (by rfl) ⟨1680254, by rfl⟩ : syracuseStep 2240339 = 3360509) B3360509
theorem B5040773 : Blo 2239435 5040773 := bbase (se 4 (by rfl) ⟨472572, by rfl⟩ : syracuseStep 5040773 = 945145) (by norm_num)
theorem B3360515 : Blo 2239435 3360515 := bstep (se 1 (by rfl) ⟨2520386, by rfl⟩ : syracuseStep 3360515 = 5040773) B5040773
theorem B2240343 : Blo 2239435 2240343 := bstep (se 1 (by rfl) ⟨1680257, by rfl⟩ : syracuseStep 2240343 = 3360515) B3360515
theorem B9700181 : Blo 2239435 9700181 := bbase (se 9 (by rfl) ⟨28418, by rfl⟩ : syracuseStep 9700181 = 56837) (by norm_num)
theorem B6466787 : Blo 2239435 6466787 := bstep (se 1 (by rfl) ⟨4850090, by rfl⟩ : syracuseStep 6466787 = 9700181) B9700181
theorem B4311191 : Blo 2239435 4311191 := bstep (se 1 (by rfl) ⟨3233393, by rfl⟩ : syracuseStep 4311191 = 6466787) B6466787
theorem B2874127 : Blo 2239435 2874127 := bstep (se 1 (by rfl) ⟨2155595, by rfl⟩ : syracuseStep 2874127 = 4311191) B4311191
theorem B3832169 : Blo 2239435 3832169 := bstep (se 2 (by rfl) ⟨1437063, by rfl⟩ : syracuseStep 3832169 = 2874127) B2874127
theorem B10219117 : Blo 2239435 10219117 := bstep (se 3 (by rfl) ⟨1916084, by rfl⟩ : syracuseStep 10219117 = 3832169) B3832169
theorem B13625489 : Blo 2239435 13625489 := bstep (se 2 (by rfl) ⟨5109558, by rfl⟩ : syracuseStep 13625489 = 10219117) B10219117
theorem B9083659 : Blo 2239435 9083659 := bstep (se 1 (by rfl) ⟨6812744, by rfl⟩ : syracuseStep 9083659 = 13625489) B13625489
theorem B12111545 : Blo 2239435 12111545 := bstep (se 2 (by rfl) ⟨4541829, by rfl⟩ : syracuseStep 12111545 = 9083659) B9083659
theorem B8074363 : Blo 2239435 8074363 := bstep (se 1 (by rfl) ⟨6055772, by rfl⟩ : syracuseStep 8074363 = 12111545) B12111545
theorem B10765817 : Blo 2239435 10765817 := bstep (se 2 (by rfl) ⟨4037181, by rfl⟩ : syracuseStep 10765817 = 8074363) B8074363
theorem B7177211 : Blo 2239435 7177211 := bstep (se 1 (by rfl) ⟨5382908, by rfl⟩ : syracuseStep 7177211 = 10765817) B10765817
theorem B4784807 : Blo 2239435 4784807 := bstep (se 1 (by rfl) ⟨3588605, by rfl⟩ : syracuseStep 4784807 = 7177211) B7177211
theorem B3189871 : Blo 2239435 3189871 := bstep (se 1 (by rfl) ⟨2392403, by rfl⟩ : syracuseStep 3189871 = 4784807) B4784807
theorem B4253161 : Blo 2239435 4253161 := bstep (se 2 (by rfl) ⟨1594935, by rfl⟩ : syracuseStep 4253161 = 3189871) B3189871
theorem B5670881 : Blo 2239435 5670881 := bstep (se 2 (by rfl) ⟨2126580, by rfl⟩ : syracuseStep 5670881 = 4253161) B4253161
theorem B3780587 : Blo 2239435 3780587 := bstep (se 1 (by rfl) ⟨2835440, by rfl⟩ : syracuseStep 3780587 = 5670881) B5670881
theorem B2520391 : Blo 2239435 2520391 := bstep (se 1 (by rfl) ⟨1890293, by rfl⟩ : syracuseStep 2520391 = 3780587) B3780587
theorem B3360521 : Blo 2239435 3360521 := bstep (se 2 (by rfl) ⟨1260195, by rfl⟩ : syracuseStep 3360521 = 2520391) B2520391
theorem B2240347 : Blo 2239435 2240347 := bstep (se 1 (by rfl) ⟨1680260, by rfl⟩ : syracuseStep 2240347 = 3360521) B3360521
theorem B11341781 : Blo 2239435 11341781 := bbase (se 7 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 11341781 = 265823) (by norm_num)
theorem B7561187 : Blo 2239435 7561187 := bstep (se 1 (by rfl) ⟨5670890, by rfl⟩ : syracuseStep 7561187 = 11341781) B11341781
theorem B5040791 : Blo 2239435 5040791 := bstep (se 1 (by rfl) ⟨3780593, by rfl⟩ : syracuseStep 5040791 = 7561187) B7561187
theorem B3360527 : Blo 2239435 3360527 := bstep (se 1 (by rfl) ⟨2520395, by rfl⟩ : syracuseStep 3360527 = 5040791) B5040791
theorem B2240351 : Blo 2239435 2240351 := bstep (se 1 (by rfl) ⟨1680263, by rfl⟩ : syracuseStep 2240351 = 3360527) B3360527
theorem B3360533 : Blo 2239435 3360533 := bbase (se 6 (by rfl) ⟨78762, by rfl⟩ : syracuseStep 3360533 = 157525) (by norm_num)
theorem B2240355 : Blo 2239435 2240355 := bstep (se 1 (by rfl) ⟨1680266, by rfl⟩ : syracuseStep 2240355 = 3360533) B3360533
theorem B15964757 : Blo 2239435 15964757 := bbase (se 8 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 15964757 = 187087) (by norm_num)
theorem B10643171 : Blo 2239435 10643171 := bstep (se 1 (by rfl) ⟨7982378, by rfl⟩ : syracuseStep 10643171 = 15964757) B15964757
theorem B28381789 : Blo 2239435 28381789 := bstep (se 3 (by rfl) ⟨5321585, by rfl⟩ : syracuseStep 28381789 = 10643171) B10643171
theorem B37842385 : Blo 2239435 37842385 := bstep (se 2 (by rfl) ⟨14190894, by rfl⟩ : syracuseStep 37842385 = 28381789) B28381789
theorem B50456513 : Blo 2239435 50456513 := bstep (se 2 (by rfl) ⟨18921192, by rfl⟩ : syracuseStep 50456513 = 37842385) B37842385
theorem B33637675 : Blo 2239435 33637675 := bstep (se 1 (by rfl) ⟨25228256, by rfl⟩ : syracuseStep 33637675 = 50456513) B50456513
theorem B44850233 : Blo 2239435 44850233 := bstep (se 2 (by rfl) ⟨16818837, by rfl⟩ : syracuseStep 44850233 = 33637675) B33637675
theorem B119600621 : Blo 2239435 119600621 := bstep (se 3 (by rfl) ⟨22425116, by rfl⟩ : syracuseStep 119600621 = 44850233) B44850233
theorem B79733747 : Blo 2239435 79733747 := bstep (se 1 (by rfl) ⟨59800310, by rfl⟩ : syracuseStep 79733747 = 119600621) B119600621
theorem B53155831 : Blo 2239435 53155831 := bstep (se 1 (by rfl) ⟨39866873, by rfl⟩ : syracuseStep 53155831 = 79733747) B79733747
theorem B70874441 : Blo 2239435 70874441 := bstep (se 2 (by rfl) ⟨26577915, by rfl⟩ : syracuseStep 70874441 = 53155831) B53155831
theorem B47249627 : Blo 2239435 47249627 := bstep (se 1 (by rfl) ⟨35437220, by rfl⟩ : syracuseStep 47249627 = 70874441) B70874441
theorem B125999005 : Blo 2239435 125999005 := bstep (se 3 (by rfl) ⟨23624813, by rfl⟩ : syracuseStep 125999005 = 47249627) B47249627
theorem B167998673 : Blo 2239435 167998673 := bstep (se 2 (by rfl) ⟨62999502, by rfl⟩ : syracuseStep 167998673 = 125999005) B125999005
theorem B111999115 : Blo 2239435 111999115 := bstep (se 1 (by rfl) ⟨83999336, by rfl⟩ : syracuseStep 111999115 = 167998673) B167998673
theorem B597328613 : Blo 2239435 597328613 := bstep (se 4 (by rfl) ⟨55999557, by rfl⟩ : syracuseStep 597328613 = 111999115) B111999115
theorem B398219075 : Blo 2239435 398219075 := bstep (se 1 (by rfl) ⟨298664306, by rfl⟩ : syracuseStep 398219075 = 597328613) B597328613
theorem B265479383 : Blo 2239435 265479383 := bstep (se 1 (by rfl) ⟨199109537, by rfl⟩ : syracuseStep 265479383 = 398219075) B398219075
theorem B176986255 : Blo 2239435 176986255 := bstep (se 1 (by rfl) ⟨132739691, by rfl⟩ : syracuseStep 176986255 = 265479383) B265479383
theorem B235981673 : Blo 2239435 235981673 := bstep (se 2 (by rfl) ⟨88493127, by rfl⟩ : syracuseStep 235981673 = 176986255) B176986255
theorem B157321115 : Blo 2239435 157321115 := bstep (se 1 (by rfl) ⟨117990836, by rfl⟩ : syracuseStep 157321115 = 235981673) B235981673
theorem B104880743 : Blo 2239435 104880743 := bstep (se 1 (by rfl) ⟨78660557, by rfl⟩ : syracuseStep 104880743 = 157321115) B157321115
theorem B69920495 : Blo 2239435 69920495 := bstep (se 1 (by rfl) ⟨52440371, by rfl⟩ : syracuseStep 69920495 = 104880743) B104880743
theorem B46613663 : Blo 2239435 46613663 := bstep (se 1 (by rfl) ⟨34960247, by rfl⟩ : syracuseStep 46613663 = 69920495) B69920495
theorem B31075775 : Blo 2239435 31075775 := bstep (se 1 (by rfl) ⟨23306831, by rfl⟩ : syracuseStep 31075775 = 46613663) B46613663
theorem B20717183 : Blo 2239435 20717183 := bstep (se 1 (by rfl) ⟨15537887, by rfl⟩ : syracuseStep 20717183 = 31075775) B31075775
theorem B13811455 : Blo 2239435 13811455 := bstep (se 1 (by rfl) ⟨10358591, by rfl⟩ : syracuseStep 13811455 = 20717183) B20717183
theorem B18415273 : Blo 2239435 18415273 := bstep (se 2 (by rfl) ⟨6905727, by rfl⟩ : syracuseStep 18415273 = 13811455) B13811455
theorem B24553697 : Blo 2239435 24553697 := bstep (se 2 (by rfl) ⟨9207636, by rfl⟩ : syracuseStep 24553697 = 18415273) B18415273
theorem B65476525 : Blo 2239435 65476525 := bstep (se 3 (by rfl) ⟨12276848, by rfl⟩ : syracuseStep 65476525 = 24553697) B24553697
theorem B87302033 : Blo 2239435 87302033 := bstep (se 2 (by rfl) ⟨32738262, by rfl⟩ : syracuseStep 87302033 = 65476525) B65476525
theorem B58201355 : Blo 2239435 58201355 := bstep (se 1 (by rfl) ⟨43651016, by rfl⟩ : syracuseStep 58201355 = 87302033) B87302033
theorem B38800903 : Blo 2239435 38800903 := bstep (se 1 (by rfl) ⟨29100677, by rfl⟩ : syracuseStep 38800903 = 58201355) B58201355
theorem B51734537 : Blo 2239435 51734537 := bstep (se 2 (by rfl) ⟨19400451, by rfl⟩ : syracuseStep 51734537 = 38800903) B38800903
theorem B34489691 : Blo 2239435 34489691 := bstep (se 1 (by rfl) ⟨25867268, by rfl⟩ : syracuseStep 34489691 = 51734537) B51734537
theorem B22993127 : Blo 2239435 22993127 := bstep (se 1 (by rfl) ⟨17244845, by rfl⟩ : syracuseStep 22993127 = 34489691) B34489691
theorem B245260021 : Blo 2239435 245260021 := bstep (se 5 (by rfl) ⟨11496563, by rfl⟩ : syracuseStep 245260021 = 22993127) B22993127
theorem B327013361 : Blo 2239435 327013361 := bstep (se 2 (by rfl) ⟨122630010, by rfl⟩ : syracuseStep 327013361 = 245260021) B245260021
theorem B218008907 : Blo 2239435 218008907 := bstep (se 1 (by rfl) ⟨163506680, by rfl⟩ : syracuseStep 218008907 = 327013361) B327013361
theorem B145339271 : Blo 2239435 145339271 := bstep (se 1 (by rfl) ⟨109004453, by rfl⟩ : syracuseStep 145339271 = 218008907) B218008907
theorem B96892847 : Blo 2239435 96892847 := bstep (se 1 (by rfl) ⟨72669635, by rfl⟩ : syracuseStep 96892847 = 145339271) B145339271
theorem B64595231 : Blo 2239435 64595231 := bstep (se 1 (by rfl) ⟨48446423, by rfl⟩ : syracuseStep 64595231 = 96892847) B96892847
theorem B43063487 : Blo 2239435 43063487 := bstep (se 1 (by rfl) ⟨32297615, by rfl⟩ : syracuseStep 43063487 = 64595231) B64595231
theorem B28708991 : Blo 2239435 28708991 := bstep (se 1 (by rfl) ⟨21531743, by rfl⟩ : syracuseStep 28708991 = 43063487) B43063487
theorem B19139327 : Blo 2239435 19139327 := bstep (se 1 (by rfl) ⟨14354495, by rfl⟩ : syracuseStep 19139327 = 28708991) B28708991
theorem B12759551 : Blo 2239435 12759551 := bstep (se 1 (by rfl) ⟨9569663, by rfl⟩ : syracuseStep 12759551 = 19139327) B19139327
theorem B8506367 : Blo 2239435 8506367 := bstep (se 1 (by rfl) ⟨6379775, by rfl⟩ : syracuseStep 8506367 = 12759551) B12759551
theorem B5670911 : Blo 2239435 5670911 := bstep (se 1 (by rfl) ⟨4253183, by rfl⟩ : syracuseStep 5670911 = 8506367) B8506367
theorem B3780607 : Blo 2239435 3780607 := bstep (se 1 (by rfl) ⟨2835455, by rfl⟩ : syracuseStep 3780607 = 5670911) B5670911
theorem B5040809 : Blo 2239435 5040809 := bstep (se 2 (by rfl) ⟨1890303, by rfl⟩ : syracuseStep 5040809 = 3780607) B3780607
theorem B3360539 : Blo 2239435 3360539 := bstep (se 1 (by rfl) ⟨2520404, by rfl⟩ : syracuseStep 3360539 = 5040809) B5040809
theorem B2240359 : Blo 2239435 2240359 := bstep (se 1 (by rfl) ⟨1680269, by rfl⟩ : syracuseStep 2240359 = 3360539) B3360539
theorem B2520409 : Blo 2239435 2520409 := bbase (se 2 (by rfl) ⟨945153, by rfl⟩ : syracuseStep 2520409 = 1890307) (by norm_num)
theorem B3360545 : Blo 2239435 3360545 := bstep (se 2 (by rfl) ⟨1260204, by rfl⟩ : syracuseStep 3360545 = 2520409) B2520409
theorem B2240363 : Blo 2239435 2240363 := bstep (se 1 (by rfl) ⟨1680272, by rfl⟩ : syracuseStep 2240363 = 3360545) B3360545
theorem B3588637 : Blo 2239435 3588637 := bbase (se 3 (by rfl) ⟨672869, by rfl⟩ : syracuseStep 3588637 = 1345739) (by norm_num)
theorem B4784849 : Blo 2239435 4784849 := bstep (se 2 (by rfl) ⟨1794318, by rfl⟩ : syracuseStep 4784849 = 3588637) B3588637
theorem B3189899 : Blo 2239435 3189899 := bstep (se 1 (by rfl) ⟨2392424, by rfl⟩ : syracuseStep 3189899 = 4784849) B4784849
theorem B8506397 : Blo 2239435 8506397 := bstep (se 3 (by rfl) ⟨1594949, by rfl⟩ : syracuseStep 8506397 = 3189899) B3189899
theorem B5670931 : Blo 2239435 5670931 := bstep (se 1 (by rfl) ⟨4253198, by rfl⟩ : syracuseStep 5670931 = 8506397) B8506397
theorem B7561241 : Blo 2239435 7561241 := bstep (se 2 (by rfl) ⟨2835465, by rfl⟩ : syracuseStep 7561241 = 5670931) B5670931
theorem B5040827 : Blo 2239435 5040827 := bstep (se 1 (by rfl) ⟨3780620, by rfl⟩ : syracuseStep 5040827 = 7561241) B7561241
theorem B3360551 : Blo 2239435 3360551 := bstep (se 1 (by rfl) ⟨2520413, by rfl⟩ : syracuseStep 3360551 = 5040827) B5040827
theorem B2240367 : Blo 2239435 2240367 := bstep (se 1 (by rfl) ⟨1680275, by rfl⟩ : syracuseStep 2240367 = 3360551) B3360551
theorem B3360557 : Blo 2239435 3360557 := bbase (se 3 (by rfl) ⟨630104, by rfl⟩ : syracuseStep 3360557 = 1260209) (by norm_num)
theorem B2240371 : Blo 2239435 2240371 := bstep (se 1 (by rfl) ⟨1680278, by rfl⟩ : syracuseStep 2240371 = 3360557) B3360557
theorem B5040845 : Blo 2239435 5040845 := bbase (se 3 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 5040845 = 1890317) (by norm_num)
theorem B3360563 : Blo 2239435 3360563 := bstep (se 1 (by rfl) ⟨2520422, by rfl⟩ : syracuseStep 3360563 = 5040845) B5040845
theorem B2240375 : Blo 2239435 2240375 := bstep (se 1 (by rfl) ⟨1680281, by rfl⟩ : syracuseStep 2240375 = 3360563) B3360563
theorem B2835481 : Blo 2239435 2835481 := bbase (se 2 (by rfl) ⟨1063305, by rfl⟩ : syracuseStep 2835481 = 2126611) (by norm_num)
theorem B3780641 : Blo 2239435 3780641 := bstep (se 2 (by rfl) ⟨1417740, by rfl⟩ : syracuseStep 3780641 = 2835481) B2835481
theorem B2520427 : Blo 2239435 2520427 := bstep (se 1 (by rfl) ⟨1890320, by rfl⟩ : syracuseStep 2520427 = 3780641) B3780641
theorem B3360569 : Blo 2239435 3360569 := bstep (se 2 (by rfl) ⟨1260213, by rfl⟩ : syracuseStep 3360569 = 2520427) B2520427
theorem B2240379 : Blo 2239435 2240379 := bstep (se 1 (by rfl) ⟨1680284, by rfl⟩ : syracuseStep 2240379 = 3360569) B3360569
theorem B9569765 : Blo 2239435 9569765 := bbase (se 4 (by rfl) ⟨897165, by rfl⟩ : syracuseStep 9569765 = 1794331) (by norm_num)
theorem B25519373 : Blo 2239435 25519373 := bstep (se 3 (by rfl) ⟨4784882, by rfl⟩ : syracuseStep 25519373 = 9569765) B9569765
theorem B17012915 : Blo 2239435 17012915 := bstep (se 1 (by rfl) ⟨12759686, by rfl⟩ : syracuseStep 17012915 = 25519373) B25519373
theorem B11341943 : Blo 2239435 11341943 := bstep (se 1 (by rfl) ⟨8506457, by rfl⟩ : syracuseStep 11341943 = 17012915) B17012915
theorem B7561295 : Blo 2239435 7561295 := bstep (se 1 (by rfl) ⟨5670971, by rfl⟩ : syracuseStep 7561295 = 11341943) B11341943
theorem B5040863 : Blo 2239435 5040863 := bstep (se 1 (by rfl) ⟨3780647, by rfl⟩ : syracuseStep 5040863 = 7561295) B7561295
theorem B3360575 : Blo 2239435 3360575 := bstep (se 1 (by rfl) ⟨2520431, by rfl⟩ : syracuseStep 3360575 = 5040863) B5040863
theorem B2240383 : Blo 2239435 2240383 := bstep (se 1 (by rfl) ⟨1680287, by rfl⟩ : syracuseStep 2240383 = 3360575) B3360575
theorem B3360581 : Blo 2239435 3360581 := bbase (se 4 (by rfl) ⟨315054, by rfl⟩ : syracuseStep 3360581 = 630109) (by norm_num)
theorem B2240387 : Blo 2239435 2240387 := bstep (se 1 (by rfl) ⟨1680290, by rfl⟩ : syracuseStep 2240387 = 3360581) B3360581
theorem B3780661 : Blo 2239435 3780661 := bbase (se 5 (by rfl) ⟨177218, by rfl⟩ : syracuseStep 3780661 = 354437) (by norm_num)
theorem B5040881 : Blo 2239435 5040881 := bstep (se 2 (by rfl) ⟨1890330, by rfl⟩ : syracuseStep 5040881 = 3780661) B3780661
theorem B3360587 : Blo 2239435 3360587 := bstep (se 1 (by rfl) ⟨2520440, by rfl⟩ : syracuseStep 3360587 = 5040881) B5040881
theorem B2240391 : Blo 2239435 2240391 := bstep (se 1 (by rfl) ⟨1680293, by rfl⟩ : syracuseStep 2240391 = 3360587) B3360587
theorem B2520445 : Blo 2239435 2520445 := bbase (se 3 (by rfl) ⟨472583, by rfl⟩ : syracuseStep 2520445 = 945167) (by norm_num)
theorem B3360593 : Blo 2239435 3360593 := bstep (se 2 (by rfl) ⟨1260222, by rfl⟩ : syracuseStep 3360593 = 2520445) B2520445
theorem B2240395 : Blo 2239435 2240395 := bstep (se 1 (by rfl) ⟨1680296, by rfl⟩ : syracuseStep 2240395 = 3360593) B3360593
theorem B7561349 : Blo 2239435 7561349 := bbase (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) (by norm_num)
theorem B5040899 : Blo 2239435 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B3360599 : Blo 2239435 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B2240399 : Blo 2239435 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B3360605 : Blo 2239435 3360605 := bbase (se 3 (by rfl) ⟨630113, by rfl⟩ : syracuseStep 3360605 = 1260227) (by norm_num)
theorem B2240403 : Blo 2239435 2240403 := bstep (se 1 (by rfl) ⟨1680302, by rfl⟩ : syracuseStep 2240403 = 3360605) B3360605
theorem B5040917 : Blo 2239435 5040917 := bbase (se 6 (by rfl) ⟨118146, by rfl⟩ : syracuseStep 5040917 = 236293) (by norm_num)
theorem B3360611 : Blo 2239435 3360611 := bstep (se 1 (by rfl) ⟨2520458, by rfl⟩ : syracuseStep 3360611 = 5040917) B5040917
theorem B2240407 : Blo 2239435 2240407 := bstep (se 1 (by rfl) ⟨1680305, by rfl⟩ : syracuseStep 2240407 = 3360611) B3360611
theorem B8506565 : Blo 2239435 8506565 := bbase (se 4 (by rfl) ⟨797490, by rfl⟩ : syracuseStep 8506565 = 1594981) (by norm_num)
theorem B5671043 : Blo 2239435 5671043 := bstep (se 1 (by rfl) ⟨4253282, by rfl⟩ : syracuseStep 5671043 = 8506565) B8506565
theorem B3780695 : Blo 2239435 3780695 := bstep (se 1 (by rfl) ⟨2835521, by rfl⟩ : syracuseStep 3780695 = 5671043) B5671043
theorem B2520463 : Blo 2239435 2520463 := bstep (se 1 (by rfl) ⟨1890347, by rfl⟩ : syracuseStep 2520463 = 3780695) B3780695
theorem B3360617 : Blo 2239435 3360617 := bstep (se 2 (by rfl) ⟨1260231, by rfl⟩ : syracuseStep 3360617 = 2520463) B2520463
theorem B2240411 : Blo 2239435 2240411 := bstep (se 1 (by rfl) ⟨1680308, by rfl⟩ : syracuseStep 2240411 = 3360617) B3360617
theorem B3832285 : Blo 2239435 3832285 := bbase (se 3 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 3832285 = 1437107) (by norm_num)
theorem B5109713 : Blo 2239435 5109713 := bstep (se 2 (by rfl) ⟨1916142, by rfl⟩ : syracuseStep 5109713 = 3832285) B3832285
theorem B3406475 : Blo 2239435 3406475 := bstep (se 1 (by rfl) ⟨2554856, by rfl⟩ : syracuseStep 3406475 = 5109713) B5109713
theorem B9083933 : Blo 2239435 9083933 := bstep (se 3 (by rfl) ⟨1703237, by rfl⟩ : syracuseStep 9083933 = 3406475) B3406475
theorem B6055955 : Blo 2239435 6055955 := bstep (se 1 (by rfl) ⟨4541966, by rfl⟩ : syracuseStep 6055955 = 9083933) B9083933
theorem B4037303 : Blo 2239435 4037303 := bstep (se 1 (by rfl) ⟨3027977, by rfl⟩ : syracuseStep 4037303 = 6055955) B6055955
theorem B10766141 : Blo 2239435 10766141 := bstep (se 3 (by rfl) ⟨2018651, by rfl⟩ : syracuseStep 10766141 = 4037303) B4037303
theorem B7177427 : Blo 2239435 7177427 := bstep (se 1 (by rfl) ⟨5383070, by rfl⟩ : syracuseStep 7177427 = 10766141) B10766141
theorem B4784951 : Blo 2239435 4784951 := bstep (se 1 (by rfl) ⟨3588713, by rfl⟩ : syracuseStep 4784951 = 7177427) B7177427
theorem B12759869 : Blo 2239435 12759869 := bstep (se 3 (by rfl) ⟨2392475, by rfl⟩ : syracuseStep 12759869 = 4784951) B4784951
theorem B8506579 : Blo 2239435 8506579 := bstep (se 1 (by rfl) ⟨6379934, by rfl⟩ : syracuseStep 8506579 = 12759869) B12759869
theorem B11342105 : Blo 2239435 11342105 := bstep (se 2 (by rfl) ⟨4253289, by rfl⟩ : syracuseStep 11342105 = 8506579) B8506579
theorem B7561403 : Blo 2239435 7561403 := bstep (se 1 (by rfl) ⟨5671052, by rfl⟩ : syracuseStep 7561403 = 11342105) B11342105
theorem B5040935 : Blo 2239435 5040935 := bstep (se 1 (by rfl) ⟨3780701, by rfl⟩ : syracuseStep 5040935 = 7561403) B7561403
theorem B3360623 : Blo 2239435 3360623 := bstep (se 1 (by rfl) ⟨2520467, by rfl⟩ : syracuseStep 3360623 = 5040935) B5040935
theorem B2240415 : Blo 2239435 2240415 := bstep (se 1 (by rfl) ⟨1680311, by rfl⟩ : syracuseStep 2240415 = 3360623) B3360623
theorem B3360629 : Blo 2239435 3360629 := bbase (se 5 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 3360629 = 315059) (by norm_num)
theorem B2240419 : Blo 2239435 2240419 := bstep (se 1 (by rfl) ⟨1680314, by rfl⟩ : syracuseStep 2240419 = 3360629) B3360629
theorem B3027989 : Blo 2239435 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B8074637 : Blo 2239435 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B5383091 : Blo 2239435 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B3588727 : Blo 2239435 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B4784969 : Blo 2239435 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B3189979 : Blo 2239435 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B4253305 : Blo 2239435 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B5671073 : Blo 2239435 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B3780715 : Blo 2239435 3780715 := bstep (se 1 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 3780715 = 5671073) B5671073
theorem B5040953 : Blo 2239435 5040953 := bstep (se 2 (by rfl) ⟨1890357, by rfl⟩ : syracuseStep 5040953 = 3780715) B3780715
theorem B3360635 : Blo 2239435 3360635 := bstep (se 1 (by rfl) ⟨2520476, by rfl⟩ : syracuseStep 3360635 = 5040953) B5040953
theorem B2240423 : Blo 2239435 2240423 := bstep (se 1 (by rfl) ⟨1680317, by rfl⟩ : syracuseStep 2240423 = 3360635) B3360635
theorem B2520481 : Blo 2239435 2520481 := bbase (se 2 (by rfl) ⟨945180, by rfl⟩ : syracuseStep 2520481 = 1890361) (by norm_num)
theorem B3360641 : Blo 2239435 3360641 := bstep (se 2 (by rfl) ⟨1260240, by rfl⟩ : syracuseStep 3360641 = 2520481) B2520481
theorem B2240427 : Blo 2239435 2240427 := bstep (se 1 (by rfl) ⟨1680320, by rfl⟩ : syracuseStep 2240427 = 3360641) B3360641
theorem B5671093 : Blo 2239435 5671093 := bbase (se 5 (by rfl) ⟨265832, by rfl⟩ : syracuseStep 5671093 = 531665) (by norm_num)
theorem B7561457 : Blo 2239435 7561457 := bstep (se 2 (by rfl) ⟨2835546, by rfl⟩ : syracuseStep 7561457 = 5671093) B5671093
theorem B5040971 : Blo 2239435 5040971 := bstep (se 1 (by rfl) ⟨3780728, by rfl⟩ : syracuseStep 5040971 = 7561457) B7561457
theorem B3360647 : Blo 2239435 3360647 := bstep (se 1 (by rfl) ⟨2520485, by rfl⟩ : syracuseStep 3360647 = 5040971) B5040971
theorem B2240431 : Blo 2239435 2240431 := bstep (se 1 (by rfl) ⟨1680323, by rfl⟩ : syracuseStep 2240431 = 3360647) B3360647
theorem B3360653 : Blo 2239435 3360653 := bbase (se 3 (by rfl) ⟨630122, by rfl⟩ : syracuseStep 3360653 = 1260245) (by norm_num)
theorem B2240435 : Blo 2239435 2240435 := bstep (se 1 (by rfl) ⟨1680326, by rfl⟩ : syracuseStep 2240435 = 3360653) B3360653
theorem B5040989 : Blo 2239435 5040989 := bbase (se 3 (by rfl) ⟨945185, by rfl⟩ : syracuseStep 5040989 = 1890371) (by norm_num)
theorem B3360659 : Blo 2239435 3360659 := bstep (se 1 (by rfl) ⟨2520494, by rfl⟩ : syracuseStep 3360659 = 5040989) B5040989
theorem B2240439 : Blo 2239435 2240439 := bstep (se 1 (by rfl) ⟨1680329, by rfl⟩ : syracuseStep 2240439 = 3360659) B3360659
theorem B3780749 : Blo 2239435 3780749 := bbase (se 3 (by rfl) ⟨708890, by rfl⟩ : syracuseStep 3780749 = 1417781) (by norm_num)
theorem B2520499 : Blo 2239435 2520499 := bstep (se 1 (by rfl) ⟨1890374, by rfl⟩ : syracuseStep 2520499 = 3780749) B3780749
theorem B3360665 : Blo 2239435 3360665 := bstep (se 2 (by rfl) ⟨1260249, by rfl⟩ : syracuseStep 3360665 = 2520499) B2520499
theorem B2240443 : Blo 2239435 2240443 := bstep (se 1 (by rfl) ⟨1680332, by rfl⟩ : syracuseStep 2240443 = 3360665) B3360665
theorem B5748509 : Blo 2239435 5748509 := bbase (se 3 (by rfl) ⟨1077845, by rfl⟩ : syracuseStep 5748509 = 2155691) (by norm_num)
theorem B15329357 : Blo 2239435 15329357 := bstep (se 3 (by rfl) ⟨2874254, by rfl⟩ : syracuseStep 15329357 = 5748509) B5748509
theorem B10219571 : Blo 2239435 10219571 := bstep (se 1 (by rfl) ⟨7664678, by rfl⟩ : syracuseStep 10219571 = 15329357) B15329357
theorem B6813047 : Blo 2239435 6813047 := bstep (se 1 (by rfl) ⟨5109785, by rfl⟩ : syracuseStep 6813047 = 10219571) B10219571
theorem B4542031 : Blo 2239435 4542031 := bstep (se 1 (by rfl) ⟨3406523, by rfl⟩ : syracuseStep 4542031 = 6813047) B6813047
theorem B6056041 : Blo 2239435 6056041 := bstep (se 2 (by rfl) ⟨2271015, by rfl⟩ : syracuseStep 6056041 = 4542031) B4542031
theorem B8074721 : Blo 2239435 8074721 := bstep (se 2 (by rfl) ⟨3028020, by rfl⟩ : syracuseStep 8074721 = 6056041) B6056041
theorem B5383147 : Blo 2239435 5383147 := bstep (se 1 (by rfl) ⟨4037360, by rfl⟩ : syracuseStep 5383147 = 8074721) B8074721
theorem B7177529 : Blo 2239435 7177529 := bstep (se 2 (by rfl) ⟨2691573, by rfl⟩ : syracuseStep 7177529 = 5383147) B5383147
theorem B19140077 : Blo 2239435 19140077 := bstep (se 3 (by rfl) ⟨3588764, by rfl⟩ : syracuseStep 19140077 = 7177529) B7177529
theorem B12760051 : Blo 2239435 12760051 := bstep (se 1 (by rfl) ⟨9570038, by rfl⟩ : syracuseStep 12760051 = 19140077) B19140077
theorem B17013401 : Blo 2239435 17013401 := bstep (se 2 (by rfl) ⟨6380025, by rfl⟩ : syracuseStep 17013401 = 12760051) B12760051
theorem B11342267 : Blo 2239435 11342267 := bstep (se 1 (by rfl) ⟨8506700, by rfl⟩ : syracuseStep 11342267 = 17013401) B17013401
theorem B7561511 : Blo 2239435 7561511 := bstep (se 1 (by rfl) ⟨5671133, by rfl⟩ : syracuseStep 7561511 = 11342267) B11342267
theorem B5041007 : Blo 2239435 5041007 := bstep (se 1 (by rfl) ⟨3780755, by rfl⟩ : syracuseStep 5041007 = 7561511) B7561511
theorem B3360671 : Blo 2239435 3360671 := bstep (se 1 (by rfl) ⟨2520503, by rfl⟩ : syracuseStep 3360671 = 5041007) B5041007
theorem B2240447 : Blo 2239435 2240447 := bstep (se 1 (by rfl) ⟨1680335, by rfl⟩ : syracuseStep 2240447 = 3360671) B3360671
theorem B3360677 : Blo 2239435 3360677 := bbase (se 4 (by rfl) ⟨315063, by rfl⟩ : syracuseStep 3360677 = 630127) (by norm_num)
theorem B2240451 : Blo 2239435 2240451 := bstep (se 1 (by rfl) ⟨1680338, by rfl⟩ : syracuseStep 2240451 = 3360677) B3360677
theorem B2835577 : Blo 2239435 2835577 := bbase (se 2 (by rfl) ⟨1063341, by rfl⟩ : syracuseStep 2835577 = 2126683) (by norm_num)
theorem B3780769 : Blo 2239435 3780769 := bstep (se 2 (by rfl) ⟨1417788, by rfl⟩ : syracuseStep 3780769 = 2835577) B2835577
theorem B5041025 : Blo 2239435 5041025 := bstep (se 2 (by rfl) ⟨1890384, by rfl⟩ : syracuseStep 5041025 = 3780769) B3780769
theorem B3360683 : Blo 2239435 3360683 := bstep (se 1 (by rfl) ⟨2520512, by rfl⟩ : syracuseStep 3360683 = 5041025) B5041025
theorem B2240455 : Blo 2239435 2240455 := bstep (se 1 (by rfl) ⟨1680341, by rfl⟩ : syracuseStep 2240455 = 3360683) B3360683
theorem B2520517 : Blo 2239435 2520517 := bbase (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) (by norm_num)
theorem B3360689 : Blo 2239435 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B2240459 : Blo 2239435 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B4253381 : Blo 2239435 4253381 := bbase (se 4 (by rfl) ⟨398754, by rfl⟩ : syracuseStep 4253381 = 797509) (by norm_num)
theorem B2835587 : Blo 2239435 2835587 := bstep (se 1 (by rfl) ⟨2126690, by rfl⟩ : syracuseStep 2835587 = 4253381) B4253381
theorem B7561565 : Blo 2239435 7561565 := bstep (se 3 (by rfl) ⟨1417793, by rfl⟩ : syracuseStep 7561565 = 2835587) B2835587
theorem B5041043 : Blo 2239435 5041043 := bstep (se 1 (by rfl) ⟨3780782, by rfl⟩ : syracuseStep 5041043 = 7561565) B7561565
theorem B3360695 : Blo 2239435 3360695 := bstep (se 1 (by rfl) ⟨2520521, by rfl⟩ : syracuseStep 3360695 = 5041043) B5041043
theorem B2240463 : Blo 2239435 2240463 := bstep (se 1 (by rfl) ⟨1680347, by rfl⟩ : syracuseStep 2240463 = 3360695) B3360695
theorem B3360701 : Blo 2239435 3360701 := bbase (se 3 (by rfl) ⟨630131, by rfl⟩ : syracuseStep 3360701 = 1260263) (by norm_num)
theorem B2240467 : Blo 2239435 2240467 := bstep (se 1 (by rfl) ⟨1680350, by rfl⟩ : syracuseStep 2240467 = 3360701) B3360701
theorem B5041061 : Blo 2239435 5041061 := bbase (se 4 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 5041061 = 945199) (by norm_num)
theorem B3360707 : Blo 2239435 3360707 := bstep (se 1 (by rfl) ⟨2520530, by rfl⟩ : syracuseStep 3360707 = 5041061) B5041061
theorem B2240471 : Blo 2239435 2240471 := bstep (se 1 (by rfl) ⟨1680353, by rfl⟩ : syracuseStep 2240471 = 3360707) B3360707
theorem B5671205 : Blo 2239435 5671205 := bbase (se 4 (by rfl) ⟨531675, by rfl⟩ : syracuseStep 5671205 = 1063351) (by norm_num)
theorem B3780803 : Blo 2239435 3780803 := bstep (se 1 (by rfl) ⟨2835602, by rfl⟩ : syracuseStep 3780803 = 5671205) B5671205
theorem B2520535 : Blo 2239435 2520535 := bstep (se 1 (by rfl) ⟨1890401, by rfl⟩ : syracuseStep 2520535 = 3780803) B3780803
theorem B3360713 : Blo 2239435 3360713 := bstep (se 2 (by rfl) ⟨1260267, by rfl⟩ : syracuseStep 3360713 = 2520535) B2520535
theorem B2240475 : Blo 2239435 2240475 := bstep (se 1 (by rfl) ⟨1680356, by rfl⟩ : syracuseStep 2240475 = 3360713) B3360713
theorem B6380117 : Blo 2239435 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B4253411 : Blo 2239435 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B11342429 : Blo 2239435 11342429 := bstep (se 3 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 11342429 = 4253411) B4253411
theorem B7561619 : Blo 2239435 7561619 := bstep (se 1 (by rfl) ⟨5671214, by rfl⟩ : syracuseStep 7561619 = 11342429) B11342429
theorem B5041079 : Blo 2239435 5041079 := bstep (se 1 (by rfl) ⟨3780809, by rfl⟩ : syracuseStep 5041079 = 7561619) B7561619
theorem B3360719 : Blo 2239435 3360719 := bstep (se 1 (by rfl) ⟨2520539, by rfl⟩ : syracuseStep 3360719 = 5041079) B5041079
theorem B2240479 : Blo 2239435 2240479 := bstep (se 1 (by rfl) ⟨1680359, by rfl⟩ : syracuseStep 2240479 = 3360719) B3360719
theorem B3360725 : Blo 2239435 3360725 := bbase (se 7 (by rfl) ⟨39383, by rfl⟩ : syracuseStep 3360725 = 78767) (by norm_num)
theorem B2240483 : Blo 2239435 2240483 := bstep (se 1 (by rfl) ⟨1680362, by rfl⟩ : syracuseStep 2240483 = 3360725) B3360725
theorem B8506853 : Blo 2239435 8506853 := bbase (se 4 (by rfl) ⟨797517, by rfl⟩ : syracuseStep 8506853 = 1595035) (by norm_num)
theorem B5671235 : Blo 2239435 5671235 := bstep (se 1 (by rfl) ⟨4253426, by rfl⟩ : syracuseStep 5671235 = 8506853) B8506853
theorem B3780823 : Blo 2239435 3780823 := bstep (se 1 (by rfl) ⟨2835617, by rfl⟩ : syracuseStep 3780823 = 5671235) B5671235
theorem B5041097 : Blo 2239435 5041097 := bstep (se 2 (by rfl) ⟨1890411, by rfl⟩ : syracuseStep 5041097 = 3780823) B3780823
theorem B3360731 : Blo 2239435 3360731 := bstep (se 1 (by rfl) ⟨2520548, by rfl⟩ : syracuseStep 3360731 = 5041097) B5041097
theorem B2240487 : Blo 2239435 2240487 := bstep (se 1 (by rfl) ⟨1680365, by rfl⟩ : syracuseStep 2240487 = 3360731) B3360731
theorem B2520553 : Blo 2239435 2520553 := bbase (se 2 (by rfl) ⟨945207, by rfl⟩ : syracuseStep 2520553 = 1890415) (by norm_num)
theorem B3360737 : Blo 2239435 3360737 := bstep (se 2 (by rfl) ⟨1260276, by rfl⟩ : syracuseStep 3360737 = 2520553) B2520553
theorem B2240491 : Blo 2239435 2240491 := bstep (se 1 (by rfl) ⟨1680368, by rfl⟩ : syracuseStep 2240491 = 3360737) B3360737
theorem B2392561 : Blo 2239435 2392561 := bbase (se 2 (by rfl) ⟨897210, by rfl⟩ : syracuseStep 2392561 = 1794421) (by norm_num)
theorem B12760325 : Blo 2239435 12760325 := bstep (se 4 (by rfl) ⟨1196280, by rfl⟩ : syracuseStep 12760325 = 2392561) B2392561
theorem B8506883 : Blo 2239435 8506883 := bstep (se 1 (by rfl) ⟨6380162, by rfl⟩ : syracuseStep 8506883 = 12760325) B12760325
theorem B5671255 : Blo 2239435 5671255 := bstep (se 1 (by rfl) ⟨4253441, by rfl⟩ : syracuseStep 5671255 = 8506883) B8506883
theorem B7561673 : Blo 2239435 7561673 := bstep (se 2 (by rfl) ⟨2835627, by rfl⟩ : syracuseStep 7561673 = 5671255) B5671255
theorem B5041115 : Blo 2239435 5041115 := bstep (se 1 (by rfl) ⟨3780836, by rfl⟩ : syracuseStep 5041115 = 7561673) B7561673
theorem B3360743 : Blo 2239435 3360743 := bstep (se 1 (by rfl) ⟨2520557, by rfl⟩ : syracuseStep 3360743 = 5041115) B5041115
theorem B2240495 : Blo 2239435 2240495 := bstep (se 1 (by rfl) ⟨1680371, by rfl⟩ : syracuseStep 2240495 = 3360743) B3360743
theorem B3360749 : Blo 2239435 3360749 := bbase (se 3 (by rfl) ⟨630140, by rfl⟩ : syracuseStep 3360749 = 1260281) (by norm_num)
theorem B2240499 : Blo 2239435 2240499 := bstep (se 1 (by rfl) ⟨1680374, by rfl⟩ : syracuseStep 2240499 = 3360749) B3360749
theorem B5041133 : Blo 2239435 5041133 := bbase (se 3 (by rfl) ⟨945212, by rfl⟩ : syracuseStep 5041133 = 1890425) (by norm_num)
theorem B3360755 : Blo 2239435 3360755 := bstep (se 1 (by rfl) ⟨2520566, by rfl⟩ : syracuseStep 3360755 = 5041133) B5041133
theorem B2240503 : Blo 2239435 2240503 := bstep (se 1 (by rfl) ⟨1680377, by rfl⟩ : syracuseStep 2240503 = 3360755) B3360755
theorem B4785149 : Blo 2239435 4785149 := bbase (se 3 (by rfl) ⟨897215, by rfl⟩ : syracuseStep 4785149 = 1794431) (by norm_num)
theorem B3190099 : Blo 2239435 3190099 := bstep (se 1 (by rfl) ⟨2392574, by rfl⟩ : syracuseStep 3190099 = 4785149) B4785149
theorem B4253465 : Blo 2239435 4253465 := bstep (se 2 (by rfl) ⟨1595049, by rfl⟩ : syracuseStep 4253465 = 3190099) B3190099
theorem B2835643 : Blo 2239435 2835643 := bstep (se 1 (by rfl) ⟨2126732, by rfl⟩ : syracuseStep 2835643 = 4253465) B4253465
theorem B3780857 : Blo 2239435 3780857 := bstep (se 2 (by rfl) ⟨1417821, by rfl⟩ : syracuseStep 3780857 = 2835643) B2835643
theorem B2520571 : Blo 2239435 2520571 := bstep (se 1 (by rfl) ⟨1890428, by rfl⟩ : syracuseStep 2520571 = 3780857) B3780857
theorem B3360761 : Blo 2239435 3360761 := bstep (se 2 (by rfl) ⟨1260285, by rfl⟩ : syracuseStep 3360761 = 2520571) B2520571
theorem B2240507 : Blo 2239435 2240507 := bstep (se 1 (by rfl) ⟨1680380, by rfl⟩ : syracuseStep 2240507 = 3360761) B3360761
theorem B9333893 : Blo 2239435 9333893 := bbase (se 4 (by rfl) ⟨875052, by rfl⟩ : syracuseStep 9333893 = 1750105) (by norm_num)
theorem B6222595 : Blo 2239435 6222595 := bstep (se 1 (by rfl) ⟨4666946, by rfl⟩ : syracuseStep 6222595 = 9333893) B9333893
theorem B8296793 : Blo 2239435 8296793 := bstep (se 2 (by rfl) ⟨3111297, by rfl⟩ : syracuseStep 8296793 = 6222595) B6222595
theorem B5531195 : Blo 2239435 5531195 := bstep (se 1 (by rfl) ⟨4148396, by rfl⟩ : syracuseStep 5531195 = 8296793) B8296793
theorem B3687463 : Blo 2239435 3687463 := bstep (se 1 (by rfl) ⟨2765597, by rfl⟩ : syracuseStep 3687463 = 5531195) B5531195
theorem B19666469 : Blo 2239435 19666469 := bstep (se 4 (by rfl) ⟨1843731, by rfl⟩ : syracuseStep 19666469 = 3687463) B3687463
theorem B52443917 : Blo 2239435 52443917 := bstep (se 3 (by rfl) ⟨9833234, by rfl⟩ : syracuseStep 52443917 = 19666469) B19666469
theorem B34962611 : Blo 2239435 34962611 := bstep (se 1 (by rfl) ⟨26221958, by rfl⟩ : syracuseStep 34962611 = 52443917) B52443917
theorem B93233629 : Blo 2239435 93233629 := bstep (se 3 (by rfl) ⟨17481305, by rfl⟩ : syracuseStep 93233629 = 34962611) B34962611
theorem B124311505 : Blo 2239435 124311505 := bstep (se 2 (by rfl) ⟨46616814, by rfl⟩ : syracuseStep 124311505 = 93233629) B93233629
theorem B165748673 : Blo 2239435 165748673 := bstep (se 2 (by rfl) ⟨62155752, by rfl⟩ : syracuseStep 165748673 = 124311505) B124311505
theorem B110499115 : Blo 2239435 110499115 := bstep (se 1 (by rfl) ⟨82874336, by rfl⟩ : syracuseStep 110499115 = 165748673) B165748673
theorem B147332153 : Blo 2239435 147332153 := bstep (se 2 (by rfl) ⟨55249557, by rfl⟩ : syracuseStep 147332153 = 110499115) B110499115
theorem B392885741 : Blo 2239435 392885741 := bstep (se 3 (by rfl) ⟨73666076, by rfl⟩ : syracuseStep 392885741 = 147332153) B147332153
theorem B261923827 : Blo 2239435 261923827 := bstep (se 1 (by rfl) ⟨196442870, by rfl⟩ : syracuseStep 261923827 = 392885741) B392885741
theorem B349231769 : Blo 2239435 349231769 := bstep (se 2 (by rfl) ⟨130961913, by rfl⟩ : syracuseStep 349231769 = 261923827) B261923827
theorem B232821179 : Blo 2239435 232821179 := bstep (se 1 (by rfl) ⟨174615884, by rfl⟩ : syracuseStep 232821179 = 349231769) B349231769
theorem B155214119 : Blo 2239435 155214119 := bstep (se 1 (by rfl) ⟨116410589, by rfl⟩ : syracuseStep 155214119 = 232821179) B232821179
theorem B103476079 : Blo 2239435 103476079 := bstep (se 1 (by rfl) ⟨77607059, by rfl⟩ : syracuseStep 103476079 = 155214119) B155214119
theorem B137968105 : Blo 2239435 137968105 := bstep (se 2 (by rfl) ⟨51738039, by rfl⟩ : syracuseStep 137968105 = 103476079) B103476079
theorem B183957473 : Blo 2239435 183957473 := bstep (se 2 (by rfl) ⟨68984052, by rfl⟩ : syracuseStep 183957473 = 137968105) B137968105
theorem B122638315 : Blo 2239435 122638315 := bstep (se 1 (by rfl) ⟨91978736, by rfl⟩ : syracuseStep 122638315 = 183957473) B183957473
theorem B163517753 : Blo 2239435 163517753 := bstep (se 2 (by rfl) ⟨61319157, by rfl⟩ : syracuseStep 163517753 = 122638315) B122638315
theorem B109011835 : Blo 2239435 109011835 := bstep (se 1 (by rfl) ⟨81758876, by rfl⟩ : syracuseStep 109011835 = 163517753) B163517753
theorem B145349113 : Blo 2239435 145349113 := bstep (se 2 (by rfl) ⟨54505917, by rfl⟩ : syracuseStep 145349113 = 109011835) B109011835
theorem B193798817 : Blo 2239435 193798817 := bstep (se 2 (by rfl) ⟨72674556, by rfl⟩ : syracuseStep 193798817 = 145349113) B145349113
theorem B129199211 : Blo 2239435 129199211 := bstep (se 1 (by rfl) ⟨96899408, by rfl⟩ : syracuseStep 129199211 = 193798817) B193798817
theorem B86132807 : Blo 2239435 86132807 := bstep (se 1 (by rfl) ⟨64599605, by rfl⟩ : syracuseStep 86132807 = 129199211) B129199211
theorem B57421871 : Blo 2239435 57421871 := bstep (se 1 (by rfl) ⟨43066403, by rfl⟩ : syracuseStep 57421871 = 86132807) B86132807
theorem B38281247 : Blo 2239435 38281247 := bstep (se 1 (by rfl) ⟨28710935, by rfl⟩ : syracuseStep 38281247 = 57421871) B57421871
theorem B25520831 : Blo 2239435 25520831 := bstep (se 1 (by rfl) ⟨19140623, by rfl⟩ : syracuseStep 25520831 = 38281247) B38281247
theorem B17013887 : Blo 2239435 17013887 := bstep (se 1 (by rfl) ⟨12760415, by rfl⟩ : syracuseStep 17013887 = 25520831) B25520831
theorem B11342591 : Blo 2239435 11342591 := bstep (se 1 (by rfl) ⟨8506943, by rfl⟩ : syracuseStep 11342591 = 17013887) B17013887
theorem B7561727 : Blo 2239435 7561727 := bstep (se 1 (by rfl) ⟨5671295, by rfl⟩ : syracuseStep 7561727 = 11342591) B11342591
theorem B5041151 : Blo 2239435 5041151 := bstep (se 1 (by rfl) ⟨3780863, by rfl⟩ : syracuseStep 5041151 = 7561727) B7561727
theorem B3360767 : Blo 2239435 3360767 := bstep (se 1 (by rfl) ⟨2520575, by rfl⟩ : syracuseStep 3360767 = 5041151) B5041151
theorem B2240511 : Blo 2239435 2240511 := bstep (se 1 (by rfl) ⟨1680383, by rfl⟩ : syracuseStep 2240511 = 3360767) B3360767
theorem B3360773 : Blo 2239435 3360773 := bbase (se 4 (by rfl) ⟨315072, by rfl⟩ : syracuseStep 3360773 = 630145) (by norm_num)
theorem B2240515 : Blo 2239435 2240515 := bstep (se 1 (by rfl) ⟨1680386, by rfl⟩ : syracuseStep 2240515 = 3360773) B3360773
theorem B3780877 : Blo 2239435 3780877 := bbase (se 3 (by rfl) ⟨708914, by rfl⟩ : syracuseStep 3780877 = 1417829) (by norm_num)
theorem B5041169 : Blo 2239435 5041169 := bstep (se 2 (by rfl) ⟨1890438, by rfl⟩ : syracuseStep 5041169 = 3780877) B3780877
theorem B3360779 : Blo 2239435 3360779 := bstep (se 1 (by rfl) ⟨2520584, by rfl⟩ : syracuseStep 3360779 = 5041169) B5041169
theorem B2240519 : Blo 2239435 2240519 := bstep (se 1 (by rfl) ⟨1680389, by rfl⟩ : syracuseStep 2240519 = 3360779) B3360779
theorem B2520589 : Blo 2239435 2520589 := bbase (se 3 (by rfl) ⟨472610, by rfl⟩ : syracuseStep 2520589 = 945221) (by norm_num)
theorem B3360785 : Blo 2239435 3360785 := bstep (se 2 (by rfl) ⟨1260294, by rfl⟩ : syracuseStep 3360785 = 2520589) B2520589
theorem B2240523 : Blo 2239435 2240523 := bstep (se 1 (by rfl) ⟨1680392, by rfl⟩ : syracuseStep 2240523 = 3360785) B3360785
theorem B7561781 : Blo 2239435 7561781 := bbase (se 5 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 7561781 = 708917) (by norm_num)
theorem B5041187 : Blo 2239435 5041187 := bstep (se 1 (by rfl) ⟨3780890, by rfl⟩ : syracuseStep 5041187 = 7561781) B7561781
theorem B3360791 : Blo 2239435 3360791 := bstep (se 1 (by rfl) ⟨2520593, by rfl⟩ : syracuseStep 3360791 = 5041187) B5041187
theorem B2240527 : Blo 2239435 2240527 := bstep (se 1 (by rfl) ⟨1680395, by rfl⟩ : syracuseStep 2240527 = 3360791) B3360791
theorem B3360797 : Blo 2239435 3360797 := bbase (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) (by norm_num)
theorem B2240531 : Blo 2239435 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B5041205 : Blo 2239435 5041205 := bbase (se 5 (by rfl) ⟨236306, by rfl⟩ : syracuseStep 5041205 = 472613) (by norm_num)
theorem B3360803 : Blo 2239435 3360803 := bstep (se 1 (by rfl) ⟨2520602, by rfl⟩ : syracuseStep 3360803 = 5041205) B5041205
theorem B2240535 : Blo 2239435 2240535 := bstep (se 1 (by rfl) ⟨1680401, by rfl⟩ : syracuseStep 2240535 = 3360803) B3360803
theorem B9084437 : Blo 2239435 9084437 := bbase (se 6 (by rfl) ⟨212916, by rfl⟩ : syracuseStep 9084437 = 425833) (by norm_num)
theorem B6056291 : Blo 2239435 6056291 := bstep (se 1 (by rfl) ⟨4542218, by rfl⟩ : syracuseStep 6056291 = 9084437) B9084437
theorem B4037527 : Blo 2239435 4037527 := bstep (se 1 (by rfl) ⟨3028145, by rfl⟩ : syracuseStep 4037527 = 6056291) B6056291
theorem B5383369 : Blo 2239435 5383369 := bstep (se 2 (by rfl) ⟨2018763, by rfl⟩ : syracuseStep 5383369 = 4037527) B4037527
theorem B7177825 : Blo 2239435 7177825 := bstep (se 2 (by rfl) ⟨2691684, by rfl⟩ : syracuseStep 7177825 = 5383369) B5383369
theorem B9570433 : Blo 2239435 9570433 := bstep (se 2 (by rfl) ⟨3588912, by rfl⟩ : syracuseStep 9570433 = 7177825) B7177825
theorem B12760577 : Blo 2239435 12760577 := bstep (se 2 (by rfl) ⟨4785216, by rfl⟩ : syracuseStep 12760577 = 9570433) B9570433
theorem B8507051 : Blo 2239435 8507051 := bstep (se 1 (by rfl) ⟨6380288, by rfl⟩ : syracuseStep 8507051 = 12760577) B12760577
theorem B5671367 : Blo 2239435 5671367 := bstep (se 1 (by rfl) ⟨4253525, by rfl⟩ : syracuseStep 5671367 = 8507051) B8507051
theorem B3780911 : Blo 2239435 3780911 := bstep (se 1 (by rfl) ⟨2835683, by rfl⟩ : syracuseStep 3780911 = 5671367) B5671367
theorem B2520607 : Blo 2239435 2520607 := bstep (se 1 (by rfl) ⟨1890455, by rfl⟩ : syracuseStep 2520607 = 3780911) B3780911
theorem B3360809 : Blo 2239435 3360809 := bstep (se 2 (by rfl) ⟨1260303, by rfl⟩ : syracuseStep 3360809 = 2520607) B2520607
theorem B2240539 : Blo 2239435 2240539 := bstep (se 1 (by rfl) ⟨1680404, by rfl⟩ : syracuseStep 2240539 = 3360809) B3360809
theorem B2691689 : Blo 2239435 2691689 := bbase (se 2 (by rfl) ⟨1009383, by rfl⟩ : syracuseStep 2691689 = 2018767) (by norm_num)
theorem B7177837 : Blo 2239435 7177837 := bstep (se 3 (by rfl) ⟨1345844, by rfl⟩ : syracuseStep 7177837 = 2691689) B2691689
theorem B9570449 : Blo 2239435 9570449 := bstep (se 2 (by rfl) ⟨3588918, by rfl⟩ : syracuseStep 9570449 = 7177837) B7177837
theorem B6380299 : Blo 2239435 6380299 := bstep (se 1 (by rfl) ⟨4785224, by rfl⟩ : syracuseStep 6380299 = 9570449) B9570449
theorem B8507065 : Blo 2239435 8507065 := bstep (se 2 (by rfl) ⟨3190149, by rfl⟩ : syracuseStep 8507065 = 6380299) B6380299
theorem B11342753 : Blo 2239435 11342753 := bstep (se 2 (by rfl) ⟨4253532, by rfl⟩ : syracuseStep 11342753 = 8507065) B8507065
theorem B7561835 : Blo 2239435 7561835 := bstep (se 1 (by rfl) ⟨5671376, by rfl⟩ : syracuseStep 7561835 = 11342753) B11342753
theorem B5041223 : Blo 2239435 5041223 := bstep (se 1 (by rfl) ⟨3780917, by rfl⟩ : syracuseStep 5041223 = 7561835) B7561835
theorem B3360815 : Blo 2239435 3360815 := bstep (se 1 (by rfl) ⟨2520611, by rfl⟩ : syracuseStep 3360815 = 5041223) B5041223
theorem B2240543 : Blo 2239435 2240543 := bstep (se 1 (by rfl) ⟨1680407, by rfl⟩ : syracuseStep 2240543 = 3360815) B3360815
theorem B3360821 : Blo 2239435 3360821 := bbase (se 5 (by rfl) ⟨157538, by rfl⟩ : syracuseStep 3360821 = 315077) (by norm_num)
theorem B2240547 : Blo 2239435 2240547 := bstep (se 1 (by rfl) ⟨1680410, by rfl⟩ : syracuseStep 2240547 = 3360821) B3360821
theorem B5671397 : Blo 2239435 5671397 := bbase (se 4 (by rfl) ⟨531693, by rfl⟩ : syracuseStep 5671397 = 1063387) (by norm_num)
theorem B3780931 : Blo 2239435 3780931 := bstep (se 1 (by rfl) ⟨2835698, by rfl⟩ : syracuseStep 3780931 = 5671397) B5671397
theorem B5041241 : Blo 2239435 5041241 := bstep (se 2 (by rfl) ⟨1890465, by rfl⟩ : syracuseStep 5041241 = 3780931) B3780931
theorem B3360827 : Blo 2239435 3360827 := bstep (se 1 (by rfl) ⟨2520620, by rfl⟩ : syracuseStep 3360827 = 5041241) B5041241
theorem B2240551 : Blo 2239435 2240551 := bstep (se 1 (by rfl) ⟨1680413, by rfl⟩ : syracuseStep 2240551 = 3360827) B3360827
theorem B2520625 : Blo 2239435 2520625 := bbase (se 2 (by rfl) ⟨945234, by rfl⟩ : syracuseStep 2520625 = 1890469) (by norm_num)
theorem B3360833 : Blo 2239435 3360833 := bstep (se 2 (by rfl) ⟨1260312, by rfl⟩ : syracuseStep 3360833 = 2520625) B2520625
theorem B2240555 : Blo 2239435 2240555 := bstep (se 1 (by rfl) ⟨1680416, by rfl⟩ : syracuseStep 2240555 = 3360833) B3360833
theorem B2555021 : Blo 2239435 2555021 := bbase (se 3 (by rfl) ⟨479066, by rfl⟩ : syracuseStep 2555021 = 958133) (by norm_num)
theorem B6813389 : Blo 2239435 6813389 := bstep (se 3 (by rfl) ⟨1277510, by rfl⟩ : syracuseStep 6813389 = 2555021) B2555021
theorem B4542259 : Blo 2239435 4542259 := bstep (se 1 (by rfl) ⟨3406694, by rfl⟩ : syracuseStep 4542259 = 6813389) B6813389
theorem B6056345 : Blo 2239435 6056345 := bstep (se 2 (by rfl) ⟨2271129, by rfl⟩ : syracuseStep 6056345 = 4542259) B4542259
theorem B4037563 : Blo 2239435 4037563 := bstep (se 1 (by rfl) ⟨3028172, by rfl⟩ : syracuseStep 4037563 = 6056345) B6056345
theorem B5383417 : Blo 2239435 5383417 := bstep (se 2 (by rfl) ⟨2018781, by rfl⟩ : syracuseStep 5383417 = 4037563) B4037563
theorem B7177889 : Blo 2239435 7177889 := bstep (se 2 (by rfl) ⟨2691708, by rfl⟩ : syracuseStep 7177889 = 5383417) B5383417
theorem B4785259 : Blo 2239435 4785259 := bstep (se 1 (by rfl) ⟨3588944, by rfl⟩ : syracuseStep 4785259 = 7177889) B7177889
theorem B6380345 : Blo 2239435 6380345 := bstep (se 2 (by rfl) ⟨2392629, by rfl⟩ : syracuseStep 6380345 = 4785259) B4785259
theorem B4253563 : Blo 2239435 4253563 := bstep (se 1 (by rfl) ⟨3190172, by rfl⟩ : syracuseStep 4253563 = 6380345) B6380345
theorem B5671417 : Blo 2239435 5671417 := bstep (se 2 (by rfl) ⟨2126781, by rfl⟩ : syracuseStep 5671417 = 4253563) B4253563
theorem B7561889 : Blo 2239435 7561889 := bstep (se 2 (by rfl) ⟨2835708, by rfl⟩ : syracuseStep 7561889 = 5671417) B5671417
theorem B5041259 : Blo 2239435 5041259 := bstep (se 1 (by rfl) ⟨3780944, by rfl⟩ : syracuseStep 5041259 = 7561889) B7561889
theorem B3360839 : Blo 2239435 3360839 := bstep (se 1 (by rfl) ⟨2520629, by rfl⟩ : syracuseStep 3360839 = 5041259) B5041259
theorem B2240559 : Blo 2239435 2240559 := bstep (se 1 (by rfl) ⟨1680419, by rfl⟩ : syracuseStep 2240559 = 3360839) B3360839
theorem B3360845 : Blo 2239435 3360845 := bbase (se 3 (by rfl) ⟨630158, by rfl⟩ : syracuseStep 3360845 = 1260317) (by norm_num)
theorem B2240563 : Blo 2239435 2240563 := bstep (se 1 (by rfl) ⟨1680422, by rfl⟩ : syracuseStep 2240563 = 3360845) B3360845
theorem B5041277 : Blo 2239435 5041277 := bbase (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) (by norm_num)
theorem B3360851 : Blo 2239435 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B2240567 : Blo 2239435 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B3780965 : Blo 2239435 3780965 := bbase (se 4 (by rfl) ⟨354465, by rfl⟩ : syracuseStep 3780965 = 708931) (by norm_num)
theorem B2520643 : Blo 2239435 2520643 := bstep (se 1 (by rfl) ⟨1890482, by rfl⟩ : syracuseStep 2520643 = 3780965) B3780965
theorem B3360857 : Blo 2239435 3360857 := bstep (se 2 (by rfl) ⟨1260321, by rfl⟩ : syracuseStep 3360857 = 2520643) B2520643
theorem B2240571 : Blo 2239435 2240571 := bstep (se 1 (by rfl) ⟨1680428, by rfl⟩ : syracuseStep 2240571 = 3360857) B3360857
theorem B4785293 : Blo 2239435 4785293 := bbase (se 3 (by rfl) ⟨897242, by rfl⟩ : syracuseStep 4785293 = 1794485) (by norm_num)
theorem B3190195 : Blo 2239435 3190195 := bstep (se 1 (by rfl) ⟨2392646, by rfl⟩ : syracuseStep 3190195 = 4785293) B4785293
theorem B17014373 : Blo 2239435 17014373 := bstep (se 4 (by rfl) ⟨1595097, by rfl⟩ : syracuseStep 17014373 = 3190195) B3190195
theorem B11342915 : Blo 2239435 11342915 := bstep (se 1 (by rfl) ⟨8507186, by rfl⟩ : syracuseStep 11342915 = 17014373) B17014373
theorem B7561943 : Blo 2239435 7561943 := bstep (se 1 (by rfl) ⟨5671457, by rfl⟩ : syracuseStep 7561943 = 11342915) B11342915
theorem B5041295 : Blo 2239435 5041295 := bstep (se 1 (by rfl) ⟨3780971, by rfl⟩ : syracuseStep 5041295 = 7561943) B7561943
theorem B3360863 : Blo 2239435 3360863 := bstep (se 1 (by rfl) ⟨2520647, by rfl⟩ : syracuseStep 3360863 = 5041295) B5041295
theorem B2240575 : Blo 2239435 2240575 := bstep (se 1 (by rfl) ⟨1680431, by rfl⟩ : syracuseStep 2240575 = 3360863) B3360863
theorem B3360869 : Blo 2239435 3360869 := bbase (se 4 (by rfl) ⟨315081, by rfl⟩ : syracuseStep 3360869 = 630163) (by norm_num)
theorem B2240579 : Blo 2239435 2240579 := bstep (se 1 (by rfl) ⟨1680434, by rfl⟩ : syracuseStep 2240579 = 3360869) B3360869
theorem B11497717 : Blo 2239435 11497717 := bbase (se 5 (by rfl) ⟨538955, by rfl⟩ : syracuseStep 11497717 = 1077911) (by norm_num)
theorem B61321157 : Blo 2239435 61321157 := bstep (se 4 (by rfl) ⟨5748858, by rfl⟩ : syracuseStep 61321157 = 11497717) B11497717
theorem B40880771 : Blo 2239435 40880771 := bstep (se 1 (by rfl) ⟨30660578, by rfl⟩ : syracuseStep 40880771 = 61321157) B61321157
theorem B27253847 : Blo 2239435 27253847 := bstep (se 1 (by rfl) ⟨20440385, by rfl⟩ : syracuseStep 27253847 = 40880771) B40880771
theorem B18169231 : Blo 2239435 18169231 := bstep (se 1 (by rfl) ⟨13626923, by rfl⟩ : syracuseStep 18169231 = 27253847) B27253847
theorem B24225641 : Blo 2239435 24225641 := bstep (se 2 (by rfl) ⟨9084615, by rfl⟩ : syracuseStep 24225641 = 18169231) B18169231
theorem B16150427 : Blo 2239435 16150427 := bstep (se 1 (by rfl) ⟨12112820, by rfl⟩ : syracuseStep 16150427 = 24225641) B24225641
theorem B10766951 : Blo 2239435 10766951 := bstep (se 1 (by rfl) ⟨8075213, by rfl⟩ : syracuseStep 10766951 = 16150427) B16150427
theorem B7177967 : Blo 2239435 7177967 := bstep (se 1 (by rfl) ⟨5383475, by rfl⟩ : syracuseStep 7177967 = 10766951) B10766951
theorem B4785311 : Blo 2239435 4785311 := bstep (se 1 (by rfl) ⟨3588983, by rfl⟩ : syracuseStep 4785311 = 7177967) B7177967
theorem B3190207 : Blo 2239435 3190207 := bstep (se 1 (by rfl) ⟨2392655, by rfl⟩ : syracuseStep 3190207 = 4785311) B4785311
theorem B4253609 : Blo 2239435 4253609 := bstep (se 2 (by rfl) ⟨1595103, by rfl⟩ : syracuseStep 4253609 = 3190207) B3190207
theorem B2835739 : Blo 2239435 2835739 := bstep (se 1 (by rfl) ⟨2126804, by rfl⟩ : syracuseStep 2835739 = 4253609) B4253609
theorem B3780985 : Blo 2239435 3780985 := bstep (se 2 (by rfl) ⟨1417869, by rfl⟩ : syracuseStep 3780985 = 2835739) B2835739
theorem B5041313 : Blo 2239435 5041313 := bstep (se 2 (by rfl) ⟨1890492, by rfl⟩ : syracuseStep 5041313 = 3780985) B3780985
theorem B3360875 : Blo 2239435 3360875 := bstep (se 1 (by rfl) ⟨2520656, by rfl⟩ : syracuseStep 3360875 = 5041313) B5041313
theorem B2240583 : Blo 2239435 2240583 := bstep (se 1 (by rfl) ⟨1680437, by rfl⟩ : syracuseStep 2240583 = 3360875) B3360875
theorem B2520661 : Blo 2239435 2520661 := bbase (se 8 (by rfl) ⟨14769, by rfl⟩ : syracuseStep 2520661 = 29539) (by norm_num)
theorem B3360881 : Blo 2239435 3360881 := bstep (se 2 (by rfl) ⟨1260330, by rfl⟩ : syracuseStep 3360881 = 2520661) B2520661
theorem B2240587 : Blo 2239435 2240587 := bstep (se 1 (by rfl) ⟨1680440, by rfl⟩ : syracuseStep 2240587 = 3360881) B3360881
theorem B2835749 : Blo 2239435 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B7561997 : Blo 2239435 7561997 := bstep (se 3 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 7561997 = 2835749) B2835749
theorem B5041331 : Blo 2239435 5041331 := bstep (se 1 (by rfl) ⟨3780998, by rfl⟩ : syracuseStep 5041331 = 7561997) B7561997
theorem B3360887 : Blo 2239435 3360887 := bstep (se 1 (by rfl) ⟨2520665, by rfl⟩ : syracuseStep 3360887 = 5041331) B5041331
theorem B2240591 : Blo 2239435 2240591 := bstep (se 1 (by rfl) ⟨1680443, by rfl⟩ : syracuseStep 2240591 = 3360887) B3360887
theorem B3360893 : Blo 2239435 3360893 := bbase (se 3 (by rfl) ⟨630167, by rfl⟩ : syracuseStep 3360893 = 1260335) (by norm_num)
theorem B2240595 : Blo 2239435 2240595 := bstep (se 1 (by rfl) ⟨1680446, by rfl⟩ : syracuseStep 2240595 = 3360893) B3360893
theorem B5041349 : Blo 2239435 5041349 := bbase (se 4 (by rfl) ⟨472626, by rfl⟩ : syracuseStep 5041349 = 945253) (by norm_num)
theorem B3360899 : Blo 2239435 3360899 := bstep (se 1 (by rfl) ⟨2520674, by rfl⟩ : syracuseStep 3360899 = 5041349) B5041349
theorem B2240599 : Blo 2239435 2240599 := bstep (se 1 (by rfl) ⟨1680449, by rfl⟩ : syracuseStep 2240599 = 3360899) B3360899
theorem B8075285 : Blo 2239435 8075285 := bbase (se 6 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 8075285 = 378529) (by norm_num)
theorem B5383523 : Blo 2239435 5383523 := bstep (se 1 (by rfl) ⟨4037642, by rfl⟩ : syracuseStep 5383523 = 8075285) B8075285
theorem B14356061 : Blo 2239435 14356061 := bstep (se 3 (by rfl) ⟨2691761, by rfl⟩ : syracuseStep 14356061 = 5383523) B5383523
theorem B9570707 : Blo 2239435 9570707 := bstep (se 1 (by rfl) ⟨7178030, by rfl⟩ : syracuseStep 9570707 = 14356061) B14356061
theorem B6380471 : Blo 2239435 6380471 := bstep (se 1 (by rfl) ⟨4785353, by rfl⟩ : syracuseStep 6380471 = 9570707) B9570707
theorem B4253647 : Blo 2239435 4253647 := bstep (se 1 (by rfl) ⟨3190235, by rfl⟩ : syracuseStep 4253647 = 6380471) B6380471
theorem B5671529 : Blo 2239435 5671529 := bstep (se 2 (by rfl) ⟨2126823, by rfl⟩ : syracuseStep 5671529 = 4253647) B4253647
theorem B3781019 : Blo 2239435 3781019 := bstep (se 1 (by rfl) ⟨2835764, by rfl⟩ : syracuseStep 3781019 = 5671529) B5671529
theorem B2520679 : Blo 2239435 2520679 := bstep (se 1 (by rfl) ⟨1890509, by rfl⟩ : syracuseStep 2520679 = 3781019) B3781019
theorem B3360905 : Blo 2239435 3360905 := bstep (se 2 (by rfl) ⟨1260339, by rfl⟩ : syracuseStep 3360905 = 2520679) B2520679
theorem B2240603 : Blo 2239435 2240603 := bstep (se 1 (by rfl) ⟨1680452, by rfl⟩ : syracuseStep 2240603 = 3360905) B3360905
theorem B11343077 : Blo 2239435 11343077 := bbase (se 4 (by rfl) ⟨1063413, by rfl⟩ : syracuseStep 11343077 = 2126827) (by norm_num)
theorem B7562051 : Blo 2239435 7562051 := bstep (se 1 (by rfl) ⟨5671538, by rfl⟩ : syracuseStep 7562051 = 11343077) B11343077
theorem B5041367 : Blo 2239435 5041367 := bstep (se 1 (by rfl) ⟨3781025, by rfl⟩ : syracuseStep 5041367 = 7562051) B7562051
theorem B3360911 : Blo 2239435 3360911 := bstep (se 1 (by rfl) ⟨2520683, by rfl⟩ : syracuseStep 3360911 = 5041367) B5041367
theorem B2240607 : Blo 2239435 2240607 := bstep (se 1 (by rfl) ⟨1680455, by rfl⟩ : syracuseStep 2240607 = 3360911) B3360911
theorem B3360917 : Blo 2239435 3360917 := bbase (se 6 (by rfl) ⟨78771, by rfl⟩ : syracuseStep 3360917 = 157543) (by norm_num)
theorem B2240611 : Blo 2239435 2240611 := bstep (se 1 (by rfl) ⟨1680458, by rfl⟩ : syracuseStep 2240611 = 3360917) B3360917
theorem B9570757 : Blo 2239435 9570757 := bbase (se 4 (by rfl) ⟨897258, by rfl⟩ : syracuseStep 9570757 = 1794517) (by norm_num)
theorem B12761009 : Blo 2239435 12761009 := bstep (se 2 (by rfl) ⟨4785378, by rfl⟩ : syracuseStep 12761009 = 9570757) B9570757
theorem B8507339 : Blo 2239435 8507339 := bstep (se 1 (by rfl) ⟨6380504, by rfl⟩ : syracuseStep 8507339 = 12761009) B12761009
theorem B5671559 : Blo 2239435 5671559 := bstep (se 1 (by rfl) ⟨4253669, by rfl⟩ : syracuseStep 5671559 = 8507339) B8507339
theorem B3781039 : Blo 2239435 3781039 := bstep (se 1 (by rfl) ⟨2835779, by rfl⟩ : syracuseStep 3781039 = 5671559) B5671559
theorem B5041385 : Blo 2239435 5041385 := bstep (se 2 (by rfl) ⟨1890519, by rfl⟩ : syracuseStep 5041385 = 3781039) B3781039
theorem B3360923 : Blo 2239435 3360923 := bstep (se 1 (by rfl) ⟨2520692, by rfl⟩ : syracuseStep 3360923 = 5041385) B5041385
theorem B2240615 : Blo 2239435 2240615 := bstep (se 1 (by rfl) ⟨1680461, by rfl⟩ : syracuseStep 2240615 = 3360923) B3360923
theorem B2520697 : Blo 2239435 2520697 := bbase (se 2 (by rfl) ⟨945261, by rfl⟩ : syracuseStep 2520697 = 1890523) (by norm_num)
theorem B3360929 : Blo 2239435 3360929 := bstep (se 2 (by rfl) ⟨1260348, by rfl⟩ : syracuseStep 3360929 = 2520697) B2520697
theorem B2240619 : Blo 2239435 2240619 := bstep (se 1 (by rfl) ⟨1680464, by rfl⟩ : syracuseStep 2240619 = 3360929) B3360929
theorem B4148605 : Blo 2239435 4148605 := bbase (se 3 (by rfl) ⟨777863, by rfl⟩ : syracuseStep 4148605 = 1555727) (by norm_num)
theorem B5531473 : Blo 2239435 5531473 := bstep (se 2 (by rfl) ⟨2074302, by rfl⟩ : syracuseStep 5531473 = 4148605) B4148605
theorem B7375297 : Blo 2239435 7375297 := bstep (se 2 (by rfl) ⟨2765736, by rfl⟩ : syracuseStep 7375297 = 5531473) B5531473
theorem B9833729 : Blo 2239435 9833729 := bstep (se 2 (by rfl) ⟨3687648, by rfl⟩ : syracuseStep 9833729 = 7375297) B7375297
theorem B26223277 : Blo 2239435 26223277 := bstep (se 3 (by rfl) ⟨4916864, by rfl⟩ : syracuseStep 26223277 = 9833729) B9833729
theorem B34964369 : Blo 2239435 34964369 := bstep (se 2 (by rfl) ⟨13111638, by rfl⟩ : syracuseStep 34964369 = 26223277) B26223277
theorem B23309579 : Blo 2239435 23309579 := bstep (se 1 (by rfl) ⟨17482184, by rfl⟩ : syracuseStep 23309579 = 34964369) B34964369
theorem B62158877 : Blo 2239435 62158877 := bstep (se 3 (by rfl) ⟨11654789, by rfl⟩ : syracuseStep 62158877 = 23309579) B23309579
theorem B41439251 : Blo 2239435 41439251 := bstep (se 1 (by rfl) ⟨31079438, by rfl⟩ : syracuseStep 41439251 = 62158877) B62158877
theorem B27626167 : Blo 2239435 27626167 := bstep (se 1 (by rfl) ⟨20719625, by rfl⟩ : syracuseStep 27626167 = 41439251) B41439251
theorem B147339557 : Blo 2239435 147339557 := bstep (se 4 (by rfl) ⟨13813083, by rfl⟩ : syracuseStep 147339557 = 27626167) B27626167
theorem B98226371 : Blo 2239435 98226371 := bstep (se 1 (by rfl) ⟨73669778, by rfl⟩ : syracuseStep 98226371 = 147339557) B147339557
theorem B261936989 : Blo 2239435 261936989 := bstep (se 3 (by rfl) ⟨49113185, by rfl⟩ : syracuseStep 261936989 = 98226371) B98226371
theorem B174624659 : Blo 2239435 174624659 := bstep (se 1 (by rfl) ⟨130968494, by rfl⟩ : syracuseStep 174624659 = 261936989) B261936989
theorem B116416439 : Blo 2239435 116416439 := bstep (se 1 (by rfl) ⟨87312329, by rfl⟩ : syracuseStep 116416439 = 174624659) B174624659
theorem B77610959 : Blo 2239435 77610959 := bstep (se 1 (by rfl) ⟨58208219, by rfl⟩ : syracuseStep 77610959 = 116416439) B116416439
theorem B51740639 : Blo 2239435 51740639 := bstep (se 1 (by rfl) ⟨38805479, by rfl⟩ : syracuseStep 51740639 = 77610959) B77610959
theorem B34493759 : Blo 2239435 34493759 := bstep (se 1 (by rfl) ⟨25870319, by rfl⟩ : syracuseStep 34493759 = 51740639) B51740639
theorem B22995839 : Blo 2239435 22995839 := bstep (se 1 (by rfl) ⟨17246879, by rfl⟩ : syracuseStep 22995839 = 34493759) B34493759
theorem B15330559 : Blo 2239435 15330559 := bstep (se 1 (by rfl) ⟨11497919, by rfl⟩ : syracuseStep 15330559 = 22995839) B22995839
theorem B20440745 : Blo 2239435 20440745 := bstep (se 2 (by rfl) ⟨7665279, by rfl⟩ : syracuseStep 20440745 = 15330559) B15330559
theorem B13627163 : Blo 2239435 13627163 := bstep (se 1 (by rfl) ⟨10220372, by rfl⟩ : syracuseStep 13627163 = 20440745) B20440745
theorem B36339101 : Blo 2239435 36339101 := bstep (se 3 (by rfl) ⟨6813581, by rfl⟩ : syracuseStep 36339101 = 13627163) B13627163
theorem B24226067 : Blo 2239435 24226067 := bstep (se 1 (by rfl) ⟨18169550, by rfl⟩ : syracuseStep 24226067 = 36339101) B36339101
theorem B16150711 : Blo 2239435 16150711 := bstep (se 1 (by rfl) ⟨12113033, by rfl⟩ : syracuseStep 16150711 = 24226067) B24226067
theorem B21534281 : Blo 2239435 21534281 := bstep (se 2 (by rfl) ⟨8075355, by rfl⟩ : syracuseStep 21534281 = 16150711) B16150711
theorem B14356187 : Blo 2239435 14356187 := bstep (se 1 (by rfl) ⟨10767140, by rfl⟩ : syracuseStep 14356187 = 21534281) B21534281
theorem B9570791 : Blo 2239435 9570791 := bstep (se 1 (by rfl) ⟨7178093, by rfl⟩ : syracuseStep 9570791 = 14356187) B14356187
theorem B6380527 : Blo 2239435 6380527 := bstep (se 1 (by rfl) ⟨4785395, by rfl⟩ : syracuseStep 6380527 = 9570791) B9570791
theorem B8507369 : Blo 2239435 8507369 := bstep (se 2 (by rfl) ⟨3190263, by rfl⟩ : syracuseStep 8507369 = 6380527) B6380527
theorem B5671579 : Blo 2239435 5671579 := bstep (se 1 (by rfl) ⟨4253684, by rfl⟩ : syracuseStep 5671579 = 8507369) B8507369
theorem B7562105 : Blo 2239435 7562105 := bstep (se 2 (by rfl) ⟨2835789, by rfl⟩ : syracuseStep 7562105 = 5671579) B5671579
theorem B5041403 : Blo 2239435 5041403 := bstep (se 1 (by rfl) ⟨3781052, by rfl⟩ : syracuseStep 5041403 = 7562105) B7562105
theorem B3360935 : Blo 2239435 3360935 := bstep (se 1 (by rfl) ⟨2520701, by rfl⟩ : syracuseStep 3360935 = 5041403) B5041403
theorem B2240623 : Blo 2239435 2240623 := bstep (se 1 (by rfl) ⟨1680467, by rfl⟩ : syracuseStep 2240623 = 3360935) B3360935
theorem B3360941 : Blo 2239435 3360941 := bbase (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) (by norm_num)
theorem B2240627 : Blo 2239435 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B5041421 : Blo 2239435 5041421 := bbase (se 3 (by rfl) ⟨945266, by rfl⟩ : syracuseStep 5041421 = 1890533) (by norm_num)
theorem B3360947 : Blo 2239435 3360947 := bstep (se 1 (by rfl) ⟨2520710, by rfl⟩ : syracuseStep 3360947 = 5041421) B5041421
theorem B2240631 : Blo 2239435 2240631 := bstep (se 1 (by rfl) ⟨1680473, by rfl⟩ : syracuseStep 2240631 = 3360947) B3360947
theorem B2835805 : Blo 2239435 2835805 := bbase (se 3 (by rfl) ⟨531713, by rfl⟩ : syracuseStep 2835805 = 1063427) (by norm_num)
theorem B3781073 : Blo 2239435 3781073 := bstep (se 2 (by rfl) ⟨1417902, by rfl⟩ : syracuseStep 3781073 = 2835805) B2835805
theorem B2520715 : Blo 2239435 2520715 := bstep (se 1 (by rfl) ⟨1890536, by rfl⟩ : syracuseStep 2520715 = 3781073) B3781073
theorem B3360953 : Blo 2239435 3360953 := bstep (se 2 (by rfl) ⟨1260357, by rfl⟩ : syracuseStep 3360953 = 2520715) B2520715
theorem B2240635 : Blo 2239435 2240635 := bstep (se 1 (by rfl) ⟨1680476, by rfl⟩ : syracuseStep 2240635 = 3360953) B3360953
theorem B19141717 : Blo 2239435 19141717 := bbase (se 8 (by rfl) ⟨112158, by rfl⟩ : syracuseStep 19141717 = 224317) (by norm_num)
theorem B25522289 : Blo 2239435 25522289 := bstep (se 2 (by rfl) ⟨9570858, by rfl⟩ : syracuseStep 25522289 = 19141717) B19141717
theorem B17014859 : Blo 2239435 17014859 := bstep (se 1 (by rfl) ⟨12761144, by rfl⟩ : syracuseStep 17014859 = 25522289) B25522289
theorem B11343239 : Blo 2239435 11343239 := bstep (se 1 (by rfl) ⟨8507429, by rfl⟩ : syracuseStep 11343239 = 17014859) B17014859
theorem B7562159 : Blo 2239435 7562159 := bstep (se 1 (by rfl) ⟨5671619, by rfl⟩ : syracuseStep 7562159 = 11343239) B11343239
theorem B5041439 : Blo 2239435 5041439 := bstep (se 1 (by rfl) ⟨3781079, by rfl⟩ : syracuseStep 5041439 = 7562159) B7562159
theorem B3360959 : Blo 2239435 3360959 := bstep (se 1 (by rfl) ⟨2520719, by rfl⟩ : syracuseStep 3360959 = 5041439) B5041439
theorem B2240639 : Blo 2239435 2240639 := bstep (se 1 (by rfl) ⟨1680479, by rfl⟩ : syracuseStep 2240639 = 3360959) B3360959
theorem B3360965 : Blo 2239435 3360965 := bbase (se 4 (by rfl) ⟨315090, by rfl⟩ : syracuseStep 3360965 = 630181) (by norm_num)
theorem B2240643 : Blo 2239435 2240643 := bstep (se 1 (by rfl) ⟨1680482, by rfl⟩ : syracuseStep 2240643 = 3360965) B3360965
theorem B3781093 : Blo 2239435 3781093 := bbase (se 4 (by rfl) ⟨354477, by rfl⟩ : syracuseStep 3781093 = 708955) (by norm_num)
theorem B5041457 : Blo 2239435 5041457 := bstep (se 2 (by rfl) ⟨1890546, by rfl⟩ : syracuseStep 5041457 = 3781093) B3781093
theorem B3360971 : Blo 2239435 3360971 := bstep (se 1 (by rfl) ⟨2520728, by rfl⟩ : syracuseStep 3360971 = 5041457) B5041457
theorem B2240647 : Blo 2239435 2240647 := bstep (se 1 (by rfl) ⟨1680485, by rfl⟩ : syracuseStep 2240647 = 3360971) B3360971
theorem B2520733 : Blo 2239435 2520733 := bbase (se 3 (by rfl) ⟨472637, by rfl⟩ : syracuseStep 2520733 = 945275) (by norm_num)
theorem B3360977 : Blo 2239435 3360977 := bstep (se 2 (by rfl) ⟨1260366, by rfl⟩ : syracuseStep 3360977 = 2520733) B2520733
theorem B2240651 : Blo 2239435 2240651 := bstep (se 1 (by rfl) ⟨1680488, by rfl⟩ : syracuseStep 2240651 = 3360977) B3360977
theorem B7562213 : Blo 2239435 7562213 := bbase (se 4 (by rfl) ⟨708957, by rfl⟩ : syracuseStep 7562213 = 1417915) (by norm_num)
theorem B5041475 : Blo 2239435 5041475 := bstep (se 1 (by rfl) ⟨3781106, by rfl⟩ : syracuseStep 5041475 = 7562213) B7562213
theorem B3360983 : Blo 2239435 3360983 := bstep (se 1 (by rfl) ⟨2520737, by rfl⟩ : syracuseStep 3360983 = 5041475) B5041475
theorem B2240655 : Blo 2239435 2240655 := bstep (se 1 (by rfl) ⟨1680491, by rfl⟩ : syracuseStep 2240655 = 3360983) B3360983
theorem B3360989 : Blo 2239435 3360989 := bbase (se 3 (by rfl) ⟨630185, by rfl⟩ : syracuseStep 3360989 = 1260371) (by norm_num)
theorem B2240659 : Blo 2239435 2240659 := bstep (se 1 (by rfl) ⟨1680494, by rfl⟩ : syracuseStep 2240659 = 3360989) B3360989
theorem B5041493 : Blo 2239435 5041493 := bbase (se 11 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 5041493 = 7385) (by norm_num)
theorem B3360995 : Blo 2239435 3360995 := bstep (se 1 (by rfl) ⟨2520746, by rfl⟩ : syracuseStep 3360995 = 5041493) B5041493
theorem B2240663 : Blo 2239435 2240663 := bstep (se 1 (by rfl) ⟨1680497, by rfl⟩ : syracuseStep 2240663 = 3360995) B3360995
theorem B2392745 : Blo 2239435 2392745 := bbase (se 2 (by rfl) ⟨897279, by rfl⟩ : syracuseStep 2392745 = 1794559) (by norm_num)
theorem B6380653 : Blo 2239435 6380653 := bstep (se 3 (by rfl) ⟨1196372, by rfl⟩ : syracuseStep 6380653 = 2392745) B2392745
theorem B8507537 : Blo 2239435 8507537 := bstep (se 2 (by rfl) ⟨3190326, by rfl⟩ : syracuseStep 8507537 = 6380653) B6380653
theorem B5671691 : Blo 2239435 5671691 := bstep (se 1 (by rfl) ⟨4253768, by rfl⟩ : syracuseStep 5671691 = 8507537) B8507537
theorem B3781127 : Blo 2239435 3781127 := bstep (se 1 (by rfl) ⟨2835845, by rfl⟩ : syracuseStep 3781127 = 5671691) B5671691
theorem B2520751 : Blo 2239435 2520751 := bstep (se 1 (by rfl) ⟨1890563, by rfl⟩ : syracuseStep 2520751 = 3781127) B3781127
theorem B3361001 : Blo 2239435 3361001 := bstep (se 2 (by rfl) ⟨1260375, by rfl⟩ : syracuseStep 3361001 = 2520751) B2520751
theorem B2240667 : Blo 2239435 2240667 := bstep (se 1 (by rfl) ⟨1680500, by rfl⟩ : syracuseStep 2240667 = 3361001) B3361001
theorem B2953513 : Blo 2239435 2953513 := bbase (se 2 (by rfl) ⟨1107567, by rfl⟩ : syracuseStep 2953513 = 2215135) (by norm_num)
theorem B15752069 : Blo 2239435 15752069 := bstep (se 4 (by rfl) ⟨1476756, by rfl⟩ : syracuseStep 15752069 = 2953513) B2953513
theorem B10501379 : Blo 2239435 10501379 := bstep (se 1 (by rfl) ⟨7876034, by rfl⟩ : syracuseStep 10501379 = 15752069) B15752069
theorem B7000919 : Blo 2239435 7000919 := bstep (se 1 (by rfl) ⟨5250689, by rfl⟩ : syracuseStep 7000919 = 10501379) B10501379
theorem B4667279 : Blo 2239435 4667279 := bstep (se 1 (by rfl) ⟨3500459, by rfl⟩ : syracuseStep 4667279 = 7000919) B7000919
theorem B12446077 : Blo 2239435 12446077 := bstep (se 3 (by rfl) ⟨2333639, by rfl⟩ : syracuseStep 12446077 = 4667279) B4667279
theorem B16594769 : Blo 2239435 16594769 := bstep (se 2 (by rfl) ⟨6223038, by rfl⟩ : syracuseStep 16594769 = 12446077) B12446077
theorem B44252717 : Blo 2239435 44252717 := bstep (se 3 (by rfl) ⟨8297384, by rfl⟩ : syracuseStep 44252717 = 16594769) B16594769
theorem B118007245 : Blo 2239435 118007245 := bstep (se 3 (by rfl) ⟨22126358, by rfl⟩ : syracuseStep 118007245 = 44252717) B44252717
theorem B629371973 : Blo 2239435 629371973 := bstep (se 4 (by rfl) ⟨59003622, by rfl⟩ : syracuseStep 629371973 = 118007245) B118007245
theorem B419581315 : Blo 2239435 419581315 := bstep (se 1 (by rfl) ⟨314685986, by rfl⟩ : syracuseStep 419581315 = 629371973) B629371973
theorem B2237767013 : Blo 2239435 2237767013 := bstep (se 4 (by rfl) ⟨209790657, by rfl⟩ : syracuseStep 2237767013 = 419581315) B419581315
theorem B1491844675 : Blo 2239435 1491844675 := bstep (se 1 (by rfl) ⟨1118883506, by rfl⟩ : syracuseStep 1491844675 = 2237767013) B2237767013
theorem B1989126233 : Blo 2239435 1989126233 := bstep (se 2 (by rfl) ⟨745922337, by rfl⟩ : syracuseStep 1989126233 = 1491844675) B1491844675
theorem B1326084155 : Blo 2239435 1326084155 := bstep (se 1 (by rfl) ⟨994563116, by rfl⟩ : syracuseStep 1326084155 = 1989126233) B1989126233
theorem B884056103 : Blo 2239435 884056103 := bstep (se 1 (by rfl) ⟨663042077, by rfl⟩ : syracuseStep 884056103 = 1326084155) B1326084155
theorem B589370735 : Blo 2239435 589370735 := bstep (se 1 (by rfl) ⟨442028051, by rfl⟩ : syracuseStep 589370735 = 884056103) B884056103
theorem B392913823 : Blo 2239435 392913823 := bstep (se 1 (by rfl) ⟨294685367, by rfl⟩ : syracuseStep 392913823 = 589370735) B589370735
theorem B523885097 : Blo 2239435 523885097 := bstep (se 2 (by rfl) ⟨196456911, by rfl⟩ : syracuseStep 523885097 = 392913823) B392913823
theorem B349256731 : Blo 2239435 349256731 := bstep (se 1 (by rfl) ⟨261942548, by rfl⟩ : syracuseStep 349256731 = 523885097) B523885097
theorem B465675641 : Blo 2239435 465675641 := bstep (se 2 (by rfl) ⟨174628365, by rfl⟩ : syracuseStep 465675641 = 349256731) B349256731
theorem B310450427 : Blo 2239435 310450427 := bstep (se 1 (by rfl) ⟨232837820, by rfl⟩ : syracuseStep 310450427 = 465675641) B465675641
theorem B206966951 : Blo 2239435 206966951 := bstep (se 1 (by rfl) ⟨155225213, by rfl⟩ : syracuseStep 206966951 = 310450427) B310450427
theorem B137977967 : Blo 2239435 137977967 := bstep (se 1 (by rfl) ⟨103483475, by rfl⟩ : syracuseStep 137977967 = 206966951) B206966951
theorem B91985311 : Blo 2239435 91985311 := bstep (se 1 (by rfl) ⟨68988983, by rfl⟩ : syracuseStep 91985311 = 137977967) B137977967
theorem B122647081 : Blo 2239435 122647081 := bstep (se 2 (by rfl) ⟨45992655, by rfl⟩ : syracuseStep 122647081 = 91985311) B91985311
theorem B163529441 : Blo 2239435 163529441 := bstep (se 2 (by rfl) ⟨61323540, by rfl⟩ : syracuseStep 163529441 = 122647081) B122647081
theorem B109019627 : Blo 2239435 109019627 := bstep (se 1 (by rfl) ⟨81764720, by rfl⟩ : syracuseStep 109019627 = 163529441) B163529441
theorem B72679751 : Blo 2239435 72679751 := bstep (se 1 (by rfl) ⟨54509813, by rfl⟩ : syracuseStep 72679751 = 109019627) B109019627
theorem B48453167 : Blo 2239435 48453167 := bstep (se 1 (by rfl) ⟨36339875, by rfl⟩ : syracuseStep 48453167 = 72679751) B72679751
theorem B32302111 : Blo 2239435 32302111 := bstep (se 1 (by rfl) ⟨24226583, by rfl⟩ : syracuseStep 32302111 = 48453167) B48453167
theorem B43069481 : Blo 2239435 43069481 := bstep (se 2 (by rfl) ⟨16151055, by rfl⟩ : syracuseStep 43069481 = 32302111) B32302111
theorem B28712987 : Blo 2239435 28712987 := bstep (se 1 (by rfl) ⟨21534740, by rfl⟩ : syracuseStep 28712987 = 43069481) B43069481
theorem B19141991 : Blo 2239435 19141991 := bstep (se 1 (by rfl) ⟨14356493, by rfl⟩ : syracuseStep 19141991 = 28712987) B28712987
theorem B12761327 : Blo 2239435 12761327 := bstep (se 1 (by rfl) ⟨9570995, by rfl⟩ : syracuseStep 12761327 = 19141991) B19141991
theorem B8507551 : Blo 2239435 8507551 := bstep (se 1 (by rfl) ⟨6380663, by rfl⟩ : syracuseStep 8507551 = 12761327) B12761327
theorem B11343401 : Blo 2239435 11343401 := bstep (se 2 (by rfl) ⟨4253775, by rfl⟩ : syracuseStep 11343401 = 8507551) B8507551
theorem B7562267 : Blo 2239435 7562267 := bstep (se 1 (by rfl) ⟨5671700, by rfl⟩ : syracuseStep 7562267 = 11343401) B11343401
theorem B5041511 : Blo 2239435 5041511 := bstep (se 1 (by rfl) ⟨3781133, by rfl⟩ : syracuseStep 5041511 = 7562267) B7562267
theorem B3361007 : Blo 2239435 3361007 := bstep (se 1 (by rfl) ⟨2520755, by rfl⟩ : syracuseStep 3361007 = 5041511) B5041511
theorem B2240671 : Blo 2239435 2240671 := bstep (se 1 (by rfl) ⟨1680503, by rfl⟩ : syracuseStep 2240671 = 3361007) B3361007
theorem B3361013 : Blo 2239435 3361013 := bbase (se 5 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 3361013 = 315095) (by norm_num)
theorem B2240675 : Blo 2239435 2240675 := bstep (se 1 (by rfl) ⟨1680506, by rfl⟩ : syracuseStep 2240675 = 3361013) B3361013
theorem B3406877 : Blo 2239435 3406877 := bbase (se 3 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 3406877 = 1277579) (by norm_num)
theorem B2271251 : Blo 2239435 2271251 := bstep (se 1 (by rfl) ⟨1703438, by rfl⟩ : syracuseStep 2271251 = 3406877) B3406877
theorem B6056669 : Blo 2239435 6056669 := bstep (se 3 (by rfl) ⟨1135625, by rfl⟩ : syracuseStep 6056669 = 2271251) B2271251
theorem B4037779 : Blo 2239435 4037779 := bstep (se 1 (by rfl) ⟨3028334, by rfl⟩ : syracuseStep 4037779 = 6056669) B6056669
theorem B21534821 : Blo 2239435 21534821 := bstep (se 4 (by rfl) ⟨2018889, by rfl⟩ : syracuseStep 21534821 = 4037779) B4037779
theorem B14356547 : Blo 2239435 14356547 := bstep (se 1 (by rfl) ⟨10767410, by rfl⟩ : syracuseStep 14356547 = 21534821) B21534821
theorem B9571031 : Blo 2239435 9571031 := bstep (se 1 (by rfl) ⟨7178273, by rfl⟩ : syracuseStep 9571031 = 14356547) B14356547
theorem B6380687 : Blo 2239435 6380687 := bstep (se 1 (by rfl) ⟨4785515, by rfl⟩ : syracuseStep 6380687 = 9571031) B9571031
theorem B4253791 : Blo 2239435 4253791 := bstep (se 1 (by rfl) ⟨3190343, by rfl⟩ : syracuseStep 4253791 = 6380687) B6380687
theorem B5671721 : Blo 2239435 5671721 := bstep (se 2 (by rfl) ⟨2126895, by rfl⟩ : syracuseStep 5671721 = 4253791) B4253791
theorem B3781147 : Blo 2239435 3781147 := bstep (se 1 (by rfl) ⟨2835860, by rfl⟩ : syracuseStep 3781147 = 5671721) B5671721
theorem B5041529 : Blo 2239435 5041529 := bstep (se 2 (by rfl) ⟨1890573, by rfl⟩ : syracuseStep 5041529 = 3781147) B3781147
theorem B3361019 : Blo 2239435 3361019 := bstep (se 1 (by rfl) ⟨2520764, by rfl⟩ : syracuseStep 3361019 = 5041529) B5041529
theorem B2240679 : Blo 2239435 2240679 := bstep (se 1 (by rfl) ⟨1680509, by rfl⟩ : syracuseStep 2240679 = 3361019) B3361019
theorem B2520769 : Blo 2239435 2520769 := bbase (se 2 (by rfl) ⟨945288, by rfl⟩ : syracuseStep 2520769 = 1890577) (by norm_num)
theorem B3361025 : Blo 2239435 3361025 := bstep (se 2 (by rfl) ⟨1260384, by rfl⟩ : syracuseStep 3361025 = 2520769) B2520769
theorem B2240683 : Blo 2239435 2240683 := bstep (se 1 (by rfl) ⟨1680512, by rfl⟩ : syracuseStep 2240683 = 3361025) B3361025
theorem B5671741 : Blo 2239435 5671741 := bbase (se 3 (by rfl) ⟨1063451, by rfl⟩ : syracuseStep 5671741 = 2126903) (by norm_num)
theorem B7562321 : Blo 2239435 7562321 := bstep (se 2 (by rfl) ⟨2835870, by rfl⟩ : syracuseStep 7562321 = 5671741) B5671741
theorem B5041547 : Blo 2239435 5041547 := bstep (se 1 (by rfl) ⟨3781160, by rfl⟩ : syracuseStep 5041547 = 7562321) B7562321
theorem B3361031 : Blo 2239435 3361031 := bstep (se 1 (by rfl) ⟨2520773, by rfl⟩ : syracuseStep 3361031 = 5041547) B5041547
theorem B2240687 : Blo 2239435 2240687 := bstep (se 1 (by rfl) ⟨1680515, by rfl⟩ : syracuseStep 2240687 = 3361031) B3361031
theorem B3361037 : Blo 2239435 3361037 := bbase (se 3 (by rfl) ⟨630194, by rfl⟩ : syracuseStep 3361037 = 1260389) (by norm_num)
theorem B2240691 : Blo 2239435 2240691 := bstep (se 1 (by rfl) ⟨1680518, by rfl⟩ : syracuseStep 2240691 = 3361037) B3361037
theorem B5041565 : Blo 2239435 5041565 := bbase (se 3 (by rfl) ⟨945293, by rfl⟩ : syracuseStep 5041565 = 1890587) (by norm_num)
theorem B3361043 : Blo 2239435 3361043 := bstep (se 1 (by rfl) ⟨2520782, by rfl⟩ : syracuseStep 3361043 = 5041565) B5041565
theorem B2240695 : Blo 2239435 2240695 := bstep (se 1 (by rfl) ⟨1680521, by rfl⟩ : syracuseStep 2240695 = 3361043) B3361043
theorem B3781181 : Blo 2239435 3781181 := bbase (se 3 (by rfl) ⟨708971, by rfl⟩ : syracuseStep 3781181 = 1417943) (by norm_num)
theorem B2520787 : Blo 2239435 2520787 := bstep (se 1 (by rfl) ⟨1890590, by rfl⟩ : syracuseStep 2520787 = 3781181) B3781181
theorem B3361049 : Blo 2239435 3361049 := bstep (se 2 (by rfl) ⟨1260393, by rfl⟩ : syracuseStep 3361049 = 2520787) B2520787
theorem B2240699 : Blo 2239435 2240699 := bstep (se 1 (by rfl) ⟨1680524, by rfl⟩ : syracuseStep 2240699 = 3361049) B3361049
theorem B10220741 : Blo 2239435 10220741 := bbase (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) (by norm_num)
theorem B6813827 : Blo 2239435 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B4542551 : Blo 2239435 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3028367 : Blo 2239435 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B8075645 : Blo 2239435 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B5383763 : Blo 2239435 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3589175 : Blo 2239435 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B2392783 : Blo 2239435 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B12761509 : Blo 2239435 12761509 := bstep (se 4 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 12761509 = 2392783) B2392783
theorem B17015345 : Blo 2239435 17015345 := bstep (se 2 (by rfl) ⟨6380754, by rfl⟩ : syracuseStep 17015345 = 12761509) B12761509
theorem B11343563 : Blo 2239435 11343563 := bstep (se 1 (by rfl) ⟨8507672, by rfl⟩ : syracuseStep 11343563 = 17015345) B17015345
theorem B7562375 : Blo 2239435 7562375 := bstep (se 1 (by rfl) ⟨5671781, by rfl⟩ : syracuseStep 7562375 = 11343563) B11343563
theorem B5041583 : Blo 2239435 5041583 := bstep (se 1 (by rfl) ⟨3781187, by rfl⟩ : syracuseStep 5041583 = 7562375) B7562375
theorem B3361055 : Blo 2239435 3361055 := bstep (se 1 (by rfl) ⟨2520791, by rfl⟩ : syracuseStep 3361055 = 5041583) B5041583
theorem B2240703 : Blo 2239435 2240703 := bstep (se 1 (by rfl) ⟨1680527, by rfl⟩ : syracuseStep 2240703 = 3361055) B3361055
theorem B3361061 : Blo 2239435 3361061 := bbase (se 4 (by rfl) ⟨315099, by rfl⟩ : syracuseStep 3361061 = 630199) (by norm_num)
theorem B2240707 : Blo 2239435 2240707 := bstep (se 1 (by rfl) ⟨1680530, by rfl⟩ : syracuseStep 2240707 = 3361061) B3361061
theorem B2835901 : Blo 2239435 2835901 := bbase (se 3 (by rfl) ⟨531731, by rfl⟩ : syracuseStep 2835901 = 1063463) (by norm_num)
theorem B3781201 : Blo 2239435 3781201 := bstep (se 2 (by rfl) ⟨1417950, by rfl⟩ : syracuseStep 3781201 = 2835901) B2835901
theorem B5041601 : Blo 2239435 5041601 := bstep (se 2 (by rfl) ⟨1890600, by rfl⟩ : syracuseStep 5041601 = 3781201) B3781201
theorem B3361067 : Blo 2239435 3361067 := bstep (se 1 (by rfl) ⟨2520800, by rfl⟩ : syracuseStep 3361067 = 5041601) B5041601
theorem B2240711 : Blo 2239435 2240711 := bstep (se 1 (by rfl) ⟨1680533, by rfl⟩ : syracuseStep 2240711 = 3361067) B3361067
theorem B2520805 : Blo 2239435 2520805 := bbase (se 4 (by rfl) ⟨236325, by rfl⟩ : syracuseStep 2520805 = 472651) (by norm_num)
theorem B3361073 : Blo 2239435 3361073 := bstep (se 2 (by rfl) ⟨1260402, by rfl⟩ : syracuseStep 3361073 = 2520805) B2520805
theorem B2240715 : Blo 2239435 2240715 := bstep (se 1 (by rfl) ⟨1680536, by rfl⟩ : syracuseStep 2240715 = 3361073) B3361073
theorem B2691901 : Blo 2239435 2691901 := bbase (se 3 (by rfl) ⟨504731, by rfl⟩ : syracuseStep 2691901 = 1009463) (by norm_num)
theorem B3589201 : Blo 2239435 3589201 := bstep (se 2 (by rfl) ⟨1345950, by rfl⟩ : syracuseStep 3589201 = 2691901) B2691901
theorem B4785601 : Blo 2239435 4785601 := bstep (se 2 (by rfl) ⟨1794600, by rfl⟩ : syracuseStep 4785601 = 3589201) B3589201
theorem B6380801 : Blo 2239435 6380801 := bstep (se 2 (by rfl) ⟨2392800, by rfl⟩ : syracuseStep 6380801 = 4785601) B4785601
theorem B4253867 : Blo 2239435 4253867 := bstep (se 1 (by rfl) ⟨3190400, by rfl⟩ : syracuseStep 4253867 = 6380801) B6380801
theorem B2835911 : Blo 2239435 2835911 := bstep (se 1 (by rfl) ⟨2126933, by rfl⟩ : syracuseStep 2835911 = 4253867) B4253867
theorem B7562429 : Blo 2239435 7562429 := bstep (se 3 (by rfl) ⟨1417955, by rfl⟩ : syracuseStep 7562429 = 2835911) B2835911
theorem B5041619 : Blo 2239435 5041619 := bstep (se 1 (by rfl) ⟨3781214, by rfl⟩ : syracuseStep 5041619 = 7562429) B7562429
theorem B3361079 : Blo 2239435 3361079 := bstep (se 1 (by rfl) ⟨2520809, by rfl⟩ : syracuseStep 3361079 = 5041619) B5041619
theorem B2240719 : Blo 2239435 2240719 := bstep (se 1 (by rfl) ⟨1680539, by rfl⟩ : syracuseStep 2240719 = 3361079) B3361079
theorem B3361085 : Blo 2239435 3361085 := bbase (se 3 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 3361085 = 1260407) (by norm_num)
theorem B2240723 : Blo 2239435 2240723 := bstep (se 1 (by rfl) ⟨1680542, by rfl⟩ : syracuseStep 2240723 = 3361085) B3361085
theorem B5041637 : Blo 2239435 5041637 := bbase (se 4 (by rfl) ⟨472653, by rfl⟩ : syracuseStep 5041637 = 945307) (by norm_num)
theorem B3361091 : Blo 2239435 3361091 := bstep (se 1 (by rfl) ⟨2520818, by rfl⟩ : syracuseStep 3361091 = 5041637) B5041637
theorem B2240727 : Blo 2239435 2240727 := bstep (se 1 (by rfl) ⟨1680545, by rfl⟩ : syracuseStep 2240727 = 3361091) B3361091
theorem B5671853 : Blo 2239435 5671853 := bbase (se 3 (by rfl) ⟨1063472, by rfl⟩ : syracuseStep 5671853 = 2126945) (by norm_num)
theorem B3781235 : Blo 2239435 3781235 := bstep (se 1 (by rfl) ⟨2835926, by rfl⟩ : syracuseStep 3781235 = 5671853) B5671853
theorem B2520823 : Blo 2239435 2520823 := bstep (se 1 (by rfl) ⟨1890617, by rfl⟩ : syracuseStep 2520823 = 3781235) B3781235
theorem B3361097 : Blo 2239435 3361097 := bstep (se 2 (by rfl) ⟨1260411, by rfl⟩ : syracuseStep 3361097 = 2520823) B2520823
theorem B2240731 : Blo 2239435 2240731 := bstep (se 1 (by rfl) ⟨1680548, by rfl⟩ : syracuseStep 2240731 = 3361097) B3361097
theorem B7178453 : Blo 2239435 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B4785635 : Blo 2239435 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B3190423 : Blo 2239435 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B4253897 : Blo 2239435 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B11343725 : Blo 2239435 11343725 := bstep (se 3 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 11343725 = 4253897) B4253897
theorem B7562483 : Blo 2239435 7562483 := bstep (se 1 (by rfl) ⟨5671862, by rfl⟩ : syracuseStep 7562483 = 11343725) B11343725
theorem B5041655 : Blo 2239435 5041655 := bstep (se 1 (by rfl) ⟨3781241, by rfl⟩ : syracuseStep 5041655 = 7562483) B7562483
theorem B3361103 : Blo 2239435 3361103 := bstep (se 1 (by rfl) ⟨2520827, by rfl⟩ : syracuseStep 3361103 = 5041655) B5041655
theorem B2240735 : Blo 2239435 2240735 := bstep (se 1 (by rfl) ⟨1680551, by rfl⟩ : syracuseStep 2240735 = 3361103) B3361103
theorem B3361109 : Blo 2239435 3361109 := bbase (se 10 (by rfl) ⟨4923, by rfl⟩ : syracuseStep 3361109 = 9847) (by norm_num)
theorem B2240739 : Blo 2239435 2240739 := bstep (se 1 (by rfl) ⟨1680554, by rfl⟩ : syracuseStep 2240739 = 3361109) B3361109
theorem B6380869 : Blo 2239435 6380869 := bbase (se 4 (by rfl) ⟨598206, by rfl⟩ : syracuseStep 6380869 = 1196413) (by norm_num)
theorem B8507825 : Blo 2239435 8507825 := bstep (se 2 (by rfl) ⟨3190434, by rfl⟩ : syracuseStep 8507825 = 6380869) B6380869
theorem B5671883 : Blo 2239435 5671883 := bstep (se 1 (by rfl) ⟨4253912, by rfl⟩ : syracuseStep 5671883 = 8507825) B8507825
theorem B3781255 : Blo 2239435 3781255 := bstep (se 1 (by rfl) ⟨2835941, by rfl⟩ : syracuseStep 3781255 = 5671883) B5671883
theorem B5041673 : Blo 2239435 5041673 := bstep (se 2 (by rfl) ⟨1890627, by rfl⟩ : syracuseStep 5041673 = 3781255) B3781255
theorem B3361115 : Blo 2239435 3361115 := bstep (se 1 (by rfl) ⟨2520836, by rfl⟩ : syracuseStep 3361115 = 5041673) B5041673
theorem B2240743 : Blo 2239435 2240743 := bstep (se 1 (by rfl) ⟨1680557, by rfl⟩ : syracuseStep 2240743 = 3361115) B3361115
theorem B2520841 : Blo 2239435 2520841 := bbase (se 2 (by rfl) ⟨945315, by rfl⟩ : syracuseStep 2520841 = 1890631) (by norm_num)
theorem B3361121 : Blo 2239435 3361121 := bstep (se 2 (by rfl) ⟨1260420, by rfl⟩ : syracuseStep 3361121 = 2520841) B2520841
theorem B2240747 : Blo 2239435 2240747 := bstep (se 1 (by rfl) ⟨1680560, by rfl⟩ : syracuseStep 2240747 = 3361121) B3361121
theorem B2302313 : Blo 2239435 2302313 := bbase (se 2 (by rfl) ⟨863367, by rfl⟩ : syracuseStep 2302313 = 1726735) (by norm_num)
theorem B24558005 : Blo 2239435 24558005 := bstep (se 5 (by rfl) ⟨1151156, by rfl⟩ : syracuseStep 24558005 = 2302313) B2302313
theorem B16372003 : Blo 2239435 16372003 := bstep (se 1 (by rfl) ⟨12279002, by rfl⟩ : syracuseStep 16372003 = 24558005) B24558005
theorem B21829337 : Blo 2239435 21829337 := bstep (se 2 (by rfl) ⟨8186001, by rfl⟩ : syracuseStep 21829337 = 16372003) B16372003
theorem B14552891 : Blo 2239435 14552891 := bstep (se 1 (by rfl) ⟨10914668, by rfl⟩ : syracuseStep 14552891 = 21829337) B21829337
theorem B9701927 : Blo 2239435 9701927 := bstep (se 1 (by rfl) ⟨7276445, by rfl⟩ : syracuseStep 9701927 = 14552891) B14552891
theorem B6467951 : Blo 2239435 6467951 := bstep (se 1 (by rfl) ⟨4850963, by rfl⟩ : syracuseStep 6467951 = 9701927) B9701927
theorem B4311967 : Blo 2239435 4311967 := bstep (se 1 (by rfl) ⟨3233975, by rfl⟩ : syracuseStep 4311967 = 6467951) B6467951
theorem B5749289 : Blo 2239435 5749289 := bstep (se 2 (by rfl) ⟨2155983, by rfl⟩ : syracuseStep 5749289 = 4311967) B4311967
theorem B3832859 : Blo 2239435 3832859 := bstep (se 1 (by rfl) ⟨2874644, by rfl⟩ : syracuseStep 3832859 = 5749289) B5749289
theorem B10220957 : Blo 2239435 10220957 := bstep (se 3 (by rfl) ⟨1916429, by rfl⟩ : syracuseStep 10220957 = 3832859) B3832859
theorem B6813971 : Blo 2239435 6813971 := bstep (se 1 (by rfl) ⟨5110478, by rfl⟩ : syracuseStep 6813971 = 10220957) B10220957
theorem B4542647 : Blo 2239435 4542647 := bstep (se 1 (by rfl) ⟨3406985, by rfl⟩ : syracuseStep 4542647 = 6813971) B6813971
theorem B12113725 : Blo 2239435 12113725 := bstep (se 3 (by rfl) ⟨2271323, by rfl⟩ : syracuseStep 12113725 = 4542647) B4542647
theorem B16151633 : Blo 2239435 16151633 := bstep (se 2 (by rfl) ⟨6056862, by rfl⟩ : syracuseStep 16151633 = 12113725) B12113725
theorem B10767755 : Blo 2239435 10767755 := bstep (se 1 (by rfl) ⟨8075816, by rfl⟩ : syracuseStep 10767755 = 16151633) B16151633
theorem B28714013 : Blo 2239435 28714013 := bstep (se 3 (by rfl) ⟨5383877, by rfl⟩ : syracuseStep 28714013 = 10767755) B10767755
theorem B19142675 : Blo 2239435 19142675 := bstep (se 1 (by rfl) ⟨14357006, by rfl⟩ : syracuseStep 19142675 = 28714013) B28714013
theorem B12761783 : Blo 2239435 12761783 := bstep (se 1 (by rfl) ⟨9571337, by rfl⟩ : syracuseStep 12761783 = 19142675) B19142675
theorem B8507855 : Blo 2239435 8507855 := bstep (se 1 (by rfl) ⟨6380891, by rfl⟩ : syracuseStep 8507855 = 12761783) B12761783
theorem B5671903 : Blo 2239435 5671903 := bstep (se 1 (by rfl) ⟨4253927, by rfl⟩ : syracuseStep 5671903 = 8507855) B8507855
theorem B7562537 : Blo 2239435 7562537 := bstep (se 2 (by rfl) ⟨2835951, by rfl⟩ : syracuseStep 7562537 = 5671903) B5671903
theorem B5041691 : Blo 2239435 5041691 := bstep (se 1 (by rfl) ⟨3781268, by rfl⟩ : syracuseStep 5041691 = 7562537) B7562537
theorem B3361127 : Blo 2239435 3361127 := bstep (se 1 (by rfl) ⟨2520845, by rfl⟩ : syracuseStep 3361127 = 5041691) B5041691
theorem B2240751 : Blo 2239435 2240751 := bstep (se 1 (by rfl) ⟨1680563, by rfl⟩ : syracuseStep 2240751 = 3361127) B3361127
theorem B3361133 : Blo 2239435 3361133 := bbase (se 3 (by rfl) ⟨630212, by rfl⟩ : syracuseStep 3361133 = 1260425) (by norm_num)
theorem B2240755 : Blo 2239435 2240755 := bstep (se 1 (by rfl) ⟨1680566, by rfl⟩ : syracuseStep 2240755 = 3361133) B3361133
theorem B5041709 : Blo 2239435 5041709 := bbase (se 3 (by rfl) ⟨945320, by rfl⟩ : syracuseStep 5041709 = 1890641) (by norm_num)
theorem B3361139 : Blo 2239435 3361139 := bstep (se 1 (by rfl) ⟨2520854, by rfl⟩ : syracuseStep 3361139 = 5041709) B5041709
theorem B2240759 : Blo 2239435 2240759 := bstep (se 1 (by rfl) ⟨1680569, by rfl⟩ : syracuseStep 2240759 = 3361139) B3361139
theorem B10221013 : Blo 2239435 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B13628017 : Blo 2239435 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B72682757 : Blo 2239435 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B48455171 : Blo 2239435 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B32303447 : Blo 2239435 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B21535631 : Blo 2239435 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B14357087 : Blo 2239435 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B9571391 : Blo 2239435 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B6380927 : Blo 2239435 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B4253951 : Blo 2239435 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B2835967 : Blo 2239435 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B3781289 : Blo 2239435 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B2520859 : Blo 2239435 2520859 := bstep (se 1 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 2520859 = 3781289) B3781289
theorem B3361145 : Blo 2239435 3361145 := bstep (se 2 (by rfl) ⟨1260429, by rfl⟩ : syracuseStep 3361145 = 2520859) B2520859
theorem B2240763 : Blo 2239435 2240763 := bstep (se 1 (by rfl) ⟨1680572, by rfl⟩ : syracuseStep 2240763 = 3361145) B3361145
theorem B3589277 : Blo 2239435 3589277 := bbase (se 3 (by rfl) ⟨672989, by rfl⟩ : syracuseStep 3589277 = 1345979) (by norm_num)
theorem B38285621 : Blo 2239435 38285621 := bstep (se 5 (by rfl) ⟨1794638, by rfl⟩ : syracuseStep 38285621 = 3589277) B3589277
theorem B25523747 : Blo 2239435 25523747 := bstep (se 1 (by rfl) ⟨19142810, by rfl⟩ : syracuseStep 25523747 = 38285621) B38285621
theorem B17015831 : Blo 2239435 17015831 := bstep (se 1 (by rfl) ⟨12761873, by rfl⟩ : syracuseStep 17015831 = 25523747) B25523747
theorem B11343887 : Blo 2239435 11343887 := bstep (se 1 (by rfl) ⟨8507915, by rfl⟩ : syracuseStep 11343887 = 17015831) B17015831
theorem B7562591 : Blo 2239435 7562591 := bstep (se 1 (by rfl) ⟨5671943, by rfl⟩ : syracuseStep 7562591 = 11343887) B11343887
theorem B5041727 : Blo 2239435 5041727 := bstep (se 1 (by rfl) ⟨3781295, by rfl⟩ : syracuseStep 5041727 = 7562591) B7562591
theorem B3361151 : Blo 2239435 3361151 := bstep (se 1 (by rfl) ⟨2520863, by rfl⟩ : syracuseStep 3361151 = 5041727) B5041727
theorem B2240767 : Blo 2239435 2240767 := bstep (se 1 (by rfl) ⟨1680575, by rfl⟩ : syracuseStep 2240767 = 3361151) B3361151
theorem B3361157 : Blo 2239435 3361157 := bbase (se 4 (by rfl) ⟨315108, by rfl⟩ : syracuseStep 3361157 = 630217) (by norm_num)
theorem B2240771 : Blo 2239435 2240771 := bstep (se 1 (by rfl) ⟨1680578, by rfl⟩ : syracuseStep 2240771 = 3361157) B3361157
theorem B3781309 : Blo 2239435 3781309 := bbase (se 3 (by rfl) ⟨708995, by rfl⟩ : syracuseStep 3781309 = 1417991) (by norm_num)
theorem B5041745 : Blo 2239435 5041745 := bstep (se 2 (by rfl) ⟨1890654, by rfl⟩ : syracuseStep 5041745 = 3781309) B3781309
theorem B3361163 : Blo 2239435 3361163 := bstep (se 1 (by rfl) ⟨2520872, by rfl⟩ : syracuseStep 3361163 = 5041745) B5041745
theorem B2240775 : Blo 2239435 2240775 := bstep (se 1 (by rfl) ⟨1680581, by rfl⟩ : syracuseStep 2240775 = 3361163) B3361163
theorem B2520877 : Blo 2239435 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B3361169 : Blo 2239435 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B2240779 : Blo 2239435 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B7562645 : Blo 2239435 7562645 := bbase (se 6 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 7562645 = 354499) (by norm_num)
theorem B5041763 : Blo 2239435 5041763 := bstep (se 1 (by rfl) ⟨3781322, by rfl⟩ : syracuseStep 5041763 = 7562645) B7562645
theorem B3361175 : Blo 2239435 3361175 := bstep (se 1 (by rfl) ⟨2520881, by rfl⟩ : syracuseStep 3361175 = 5041763) B5041763
theorem B2240783 : Blo 2239435 2240783 := bstep (se 1 (by rfl) ⟨1680587, by rfl⟩ : syracuseStep 2240783 = 3361175) B3361175
theorem B3361181 : Blo 2239435 3361181 := bbase (se 3 (by rfl) ⟨630221, by rfl⟩ : syracuseStep 3361181 = 1260443) (by norm_num)
theorem B2240787 : Blo 2239435 2240787 := bstep (se 1 (by rfl) ⟨1680590, by rfl⟩ : syracuseStep 2240787 = 3361181) B3361181
theorem B5041781 : Blo 2239435 5041781 := bbase (se 5 (by rfl) ⟨236333, by rfl⟩ : syracuseStep 5041781 = 472667) (by norm_num)
theorem B3361187 : Blo 2239435 3361187 := bstep (se 1 (by rfl) ⟨2520890, by rfl⟩ : syracuseStep 3361187 = 5041781) B5041781
theorem B2240791 : Blo 2239435 2240791 := bstep (se 1 (by rfl) ⟨1680593, by rfl⟩ : syracuseStep 2240791 = 3361187) B3361187
theorem B7178645 : Blo 2239435 7178645 := bbase (se 6 (by rfl) ⟨168249, by rfl⟩ : syracuseStep 7178645 = 336499) (by norm_num)
theorem B19143053 : Blo 2239435 19143053 := bstep (se 3 (by rfl) ⟨3589322, by rfl⟩ : syracuseStep 19143053 = 7178645) B7178645
theorem B12762035 : Blo 2239435 12762035 := bstep (se 1 (by rfl) ⟨9571526, by rfl⟩ : syracuseStep 12762035 = 19143053) B19143053
theorem B8508023 : Blo 2239435 8508023 := bstep (se 1 (by rfl) ⟨6381017, by rfl⟩ : syracuseStep 8508023 = 12762035) B12762035
theorem B5672015 : Blo 2239435 5672015 := bstep (se 1 (by rfl) ⟨4254011, by rfl⟩ : syracuseStep 5672015 = 8508023) B8508023
theorem B3781343 : Blo 2239435 3781343 := bstep (se 1 (by rfl) ⟨2836007, by rfl⟩ : syracuseStep 3781343 = 5672015) B5672015
theorem B2520895 : Blo 2239435 2520895 := bstep (se 1 (by rfl) ⟨1890671, by rfl⟩ : syracuseStep 2520895 = 3781343) B3781343
theorem B3361193 : Blo 2239435 3361193 := bstep (se 2 (by rfl) ⟨1260447, by rfl⟩ : syracuseStep 3361193 = 2520895) B2520895
theorem B2240795 : Blo 2239435 2240795 := bstep (se 1 (by rfl) ⟨1680596, by rfl⟩ : syracuseStep 2240795 = 3361193) B3361193
theorem B8508037 : Blo 2239435 8508037 := bbase (se 4 (by rfl) ⟨797628, by rfl⟩ : syracuseStep 8508037 = 1595257) (by norm_num)
theorem B11344049 : Blo 2239435 11344049 := bstep (se 2 (by rfl) ⟨4254018, by rfl⟩ : syracuseStep 11344049 = 8508037) B8508037
theorem B7562699 : Blo 2239435 7562699 := bstep (se 1 (by rfl) ⟨5672024, by rfl⟩ : syracuseStep 7562699 = 11344049) B11344049
theorem B5041799 : Blo 2239435 5041799 := bstep (se 1 (by rfl) ⟨3781349, by rfl⟩ : syracuseStep 5041799 = 7562699) B7562699
theorem B3361199 : Blo 2239435 3361199 := bstep (se 1 (by rfl) ⟨2520899, by rfl⟩ : syracuseStep 3361199 = 5041799) B5041799
theorem B2240799 : Blo 2239435 2240799 := bstep (se 1 (by rfl) ⟨1680599, by rfl⟩ : syracuseStep 2240799 = 3361199) B3361199
theorem B3361205 : Blo 2239435 3361205 := bbase (se 5 (by rfl) ⟨157556, by rfl⟩ : syracuseStep 3361205 = 315113) (by norm_num)
theorem B2240803 : Blo 2239435 2240803 := bstep (se 1 (by rfl) ⟨1680602, by rfl⟩ : syracuseStep 2240803 = 3361205) B3361205
theorem B5672045 : Blo 2239435 5672045 := bbase (se 3 (by rfl) ⟨1063508, by rfl⟩ : syracuseStep 5672045 = 2127017) (by norm_num)
theorem B3781363 : Blo 2239435 3781363 := bstep (se 1 (by rfl) ⟨2836022, by rfl⟩ : syracuseStep 3781363 = 5672045) B5672045
theorem B5041817 : Blo 2239435 5041817 := bstep (se 2 (by rfl) ⟨1890681, by rfl⟩ : syracuseStep 5041817 = 3781363) B3781363
theorem B3361211 : Blo 2239435 3361211 := bstep (se 1 (by rfl) ⟨2520908, by rfl⟩ : syracuseStep 3361211 = 5041817) B5041817
theorem B2240807 : Blo 2239435 2240807 := bstep (se 1 (by rfl) ⟨1680605, by rfl⟩ : syracuseStep 2240807 = 3361211) B3361211
theorem B2520913 : Blo 2239435 2520913 := bbase (se 2 (by rfl) ⟨945342, by rfl⟩ : syracuseStep 2520913 = 1890685) (by norm_num)
theorem B3361217 : Blo 2239435 3361217 := bstep (se 2 (by rfl) ⟨1260456, by rfl⟩ : syracuseStep 3361217 = 2520913) B2520913
theorem B2240811 : Blo 2239435 2240811 := bstep (se 1 (by rfl) ⟨1680608, by rfl⟩ : syracuseStep 2240811 = 3361217) B3361217
theorem B7665941 : Blo 2239435 7665941 := bbase (se 6 (by rfl) ⟨179670, by rfl⟩ : syracuseStep 7665941 = 359341) (by norm_num)
theorem B5110627 : Blo 2239435 5110627 := bstep (se 1 (by rfl) ⟨3832970, by rfl⟩ : syracuseStep 5110627 = 7665941) B7665941
theorem B6814169 : Blo 2239435 6814169 := bstep (se 2 (by rfl) ⟨2555313, by rfl⟩ : syracuseStep 6814169 = 5110627) B5110627
theorem B4542779 : Blo 2239435 4542779 := bstep (se 1 (by rfl) ⟨3407084, by rfl⟩ : syracuseStep 4542779 = 6814169) B6814169
theorem B3028519 : Blo 2239435 3028519 := bstep (se 1 (by rfl) ⟨2271389, by rfl⟩ : syracuseStep 3028519 = 4542779) B4542779
theorem B4038025 : Blo 2239435 4038025 := bstep (se 2 (by rfl) ⟨1514259, by rfl⟩ : syracuseStep 4038025 = 3028519) B3028519
theorem B5384033 : Blo 2239435 5384033 := bstep (se 2 (by rfl) ⟨2019012, by rfl⟩ : syracuseStep 5384033 = 4038025) B4038025
theorem B3589355 : Blo 2239435 3589355 := bstep (se 1 (by rfl) ⟨2692016, by rfl⟩ : syracuseStep 3589355 = 5384033) B5384033
theorem B2392903 : Blo 2239435 2392903 := bstep (se 1 (by rfl) ⟨1794677, by rfl⟩ : syracuseStep 2392903 = 3589355) B3589355
theorem B3190537 : Blo 2239435 3190537 := bstep (se 2 (by rfl) ⟨1196451, by rfl⟩ : syracuseStep 3190537 = 2392903) B2392903
theorem B4254049 : Blo 2239435 4254049 := bstep (se 2 (by rfl) ⟨1595268, by rfl⟩ : syracuseStep 4254049 = 3190537) B3190537
theorem B5672065 : Blo 2239435 5672065 := bstep (se 2 (by rfl) ⟨2127024, by rfl⟩ : syracuseStep 5672065 = 4254049) B4254049
theorem B7562753 : Blo 2239435 7562753 := bstep (se 2 (by rfl) ⟨2836032, by rfl⟩ : syracuseStep 7562753 = 5672065) B5672065
theorem B5041835 : Blo 2239435 5041835 := bstep (se 1 (by rfl) ⟨3781376, by rfl⟩ : syracuseStep 5041835 = 7562753) B7562753
theorem B3361223 : Blo 2239435 3361223 := bstep (se 1 (by rfl) ⟨2520917, by rfl⟩ : syracuseStep 3361223 = 5041835) B5041835
theorem B2240815 : Blo 2239435 2240815 := bstep (se 1 (by rfl) ⟨1680611, by rfl⟩ : syracuseStep 2240815 = 3361223) B3361223
theorem B3361229 : Blo 2239435 3361229 := bbase (se 3 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 3361229 = 1260461) (by norm_num)
theorem B2240819 : Blo 2239435 2240819 := bstep (se 1 (by rfl) ⟨1680614, by rfl⟩ : syracuseStep 2240819 = 3361229) B3361229
theorem B5041853 : Blo 2239435 5041853 := bbase (se 3 (by rfl) ⟨945347, by rfl⟩ : syracuseStep 5041853 = 1890695) (by norm_num)
theorem B3361235 : Blo 2239435 3361235 := bstep (se 1 (by rfl) ⟨2520926, by rfl⟩ : syracuseStep 3361235 = 5041853) B5041853
theorem B2240823 : Blo 2239435 2240823 := bstep (se 1 (by rfl) ⟨1680617, by rfl⟩ : syracuseStep 2240823 = 3361235) B3361235
theorem B3781397 : Blo 2239435 3781397 := bbase (se 6 (by rfl) ⟨88626, by rfl⟩ : syracuseStep 3781397 = 177253) (by norm_num)
theorem B2520931 : Blo 2239435 2520931 := bstep (se 1 (by rfl) ⟨1890698, by rfl⟩ : syracuseStep 2520931 = 3781397) B3781397
theorem B3361241 : Blo 2239435 3361241 := bstep (se 2 (by rfl) ⟨1260465, by rfl⟩ : syracuseStep 3361241 = 2520931) B2520931
theorem B2240827 : Blo 2239435 2240827 := bstep (se 1 (by rfl) ⟨1680620, by rfl⟩ : syracuseStep 2240827 = 3361241) B3361241
theorem B5110661 : Blo 2239435 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B3407107 : Blo 2239435 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B4542809 : Blo 2239435 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B48456629 : Blo 2239435 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B32304419 : Blo 2239435 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B21536279 : Blo 2239435 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B14357519 : Blo 2239435 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B9571679 : Blo 2239435 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B6381119 : Blo 2239435 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B17016317 : Blo 2239435 17016317 := bstep (se 3 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 17016317 = 6381119) B6381119
theorem B11344211 : Blo 2239435 11344211 := bstep (se 1 (by rfl) ⟨8508158, by rfl⟩ : syracuseStep 11344211 = 17016317) B17016317
theorem B7562807 : Blo 2239435 7562807 := bstep (se 1 (by rfl) ⟨5672105, by rfl⟩ : syracuseStep 7562807 = 11344211) B11344211
theorem B5041871 : Blo 2239435 5041871 := bstep (se 1 (by rfl) ⟨3781403, by rfl⟩ : syracuseStep 5041871 = 7562807) B7562807
theorem B3361247 : Blo 2239435 3361247 := bstep (se 1 (by rfl) ⟨2520935, by rfl⟩ : syracuseStep 3361247 = 5041871) B5041871
theorem B2240831 : Blo 2239435 2240831 := bstep (se 1 (by rfl) ⟨1680623, by rfl⟩ : syracuseStep 2240831 = 3361247) B3361247
theorem B3361253 : Blo 2239435 3361253 := bbase (se 4 (by rfl) ⟨315117, by rfl⟩ : syracuseStep 3361253 = 630235) (by norm_num)
theorem B2240835 : Blo 2239435 2240835 := bstep (se 1 (by rfl) ⟨1680626, by rfl⟩ : syracuseStep 2240835 = 3361253) B3361253
theorem B2692045 : Blo 2239435 2692045 := bbase (se 3 (by rfl) ⟨504758, by rfl⟩ : syracuseStep 2692045 = 1009517) (by norm_num)
theorem B14357573 : Blo 2239435 14357573 := bstep (se 4 (by rfl) ⟨1346022, by rfl⟩ : syracuseStep 14357573 = 2692045) B2692045
theorem B9571715 : Blo 2239435 9571715 := bstep (se 1 (by rfl) ⟨7178786, by rfl⟩ : syracuseStep 9571715 = 14357573) B14357573
theorem B6381143 : Blo 2239435 6381143 := bstep (se 1 (by rfl) ⟨4785857, by rfl⟩ : syracuseStep 6381143 = 9571715) B9571715
theorem B4254095 : Blo 2239435 4254095 := bstep (se 1 (by rfl) ⟨3190571, by rfl⟩ : syracuseStep 4254095 = 6381143) B6381143
theorem B2836063 : Blo 2239435 2836063 := bstep (se 1 (by rfl) ⟨2127047, by rfl⟩ : syracuseStep 2836063 = 4254095) B4254095
theorem B3781417 : Blo 2239435 3781417 := bstep (se 2 (by rfl) ⟨1418031, by rfl⟩ : syracuseStep 3781417 = 2836063) B2836063
theorem B5041889 : Blo 2239435 5041889 := bstep (se 2 (by rfl) ⟨1890708, by rfl⟩ : syracuseStep 5041889 = 3781417) B3781417
theorem B3361259 : Blo 2239435 3361259 := bstep (se 1 (by rfl) ⟨2520944, by rfl⟩ : syracuseStep 3361259 = 5041889) B5041889
theorem B2240839 : Blo 2239435 2240839 := bstep (se 1 (by rfl) ⟨1680629, by rfl⟩ : syracuseStep 2240839 = 3361259) B3361259
theorem B2520949 : Blo 2239435 2520949 := bbase (se 5 (by rfl) ⟨118169, by rfl⟩ : syracuseStep 2520949 = 236339) (by norm_num)
theorem B3361265 : Blo 2239435 3361265 := bstep (se 2 (by rfl) ⟨1260474, by rfl⟩ : syracuseStep 3361265 = 2520949) B2520949
theorem B2240843 : Blo 2239435 2240843 := bstep (se 1 (by rfl) ⟨1680632, by rfl⟩ : syracuseStep 2240843 = 3361265) B3361265
theorem B2836073 : Blo 2239435 2836073 := bbase (se 2 (by rfl) ⟨1063527, by rfl⟩ : syracuseStep 2836073 = 2127055) (by norm_num)
theorem B7562861 : Blo 2239435 7562861 := bstep (se 3 (by rfl) ⟨1418036, by rfl⟩ : syracuseStep 7562861 = 2836073) B2836073
theorem B5041907 : Blo 2239435 5041907 := bstep (se 1 (by rfl) ⟨3781430, by rfl⟩ : syracuseStep 5041907 = 7562861) B7562861
theorem B3361271 : Blo 2239435 3361271 := bstep (se 1 (by rfl) ⟨2520953, by rfl⟩ : syracuseStep 3361271 = 5041907) B5041907
theorem B2240847 : Blo 2239435 2240847 := bstep (se 1 (by rfl) ⟨1680635, by rfl⟩ : syracuseStep 2240847 = 3361271) B3361271
theorem B3361277 : Blo 2239435 3361277 := bbase (se 3 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 3361277 = 1260479) (by norm_num)
theorem B2240851 : Blo 2239435 2240851 := bstep (se 1 (by rfl) ⟨1680638, by rfl⟩ : syracuseStep 2240851 = 3361277) B3361277
theorem B5041925 : Blo 2239435 5041925 := bbase (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) (by norm_num)
theorem B3361283 : Blo 2239435 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B2240855 : Blo 2239435 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B4254133 : Blo 2239435 4254133 := bbase (se 5 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 4254133 = 398825) (by norm_num)
theorem B5672177 : Blo 2239435 5672177 := bstep (se 2 (by rfl) ⟨2127066, by rfl⟩ : syracuseStep 5672177 = 4254133) B4254133
theorem B3781451 : Blo 2239435 3781451 := bstep (se 1 (by rfl) ⟨2836088, by rfl⟩ : syracuseStep 3781451 = 5672177) B5672177
theorem B2520967 : Blo 2239435 2520967 := bstep (se 1 (by rfl) ⟨1890725, by rfl⟩ : syracuseStep 2520967 = 3781451) B3781451
theorem B3361289 : Blo 2239435 3361289 := bstep (se 2 (by rfl) ⟨1260483, by rfl⟩ : syracuseStep 3361289 = 2520967) B2520967
theorem B2240859 : Blo 2239435 2240859 := bstep (se 1 (by rfl) ⟨1680644, by rfl⟩ : syracuseStep 2240859 = 3361289) B3361289
theorem B11344373 : Blo 2239435 11344373 := bbase (se 5 (by rfl) ⟨531767, by rfl⟩ : syracuseStep 11344373 = 1063535) (by norm_num)
theorem B7562915 : Blo 2239435 7562915 := bstep (se 1 (by rfl) ⟨5672186, by rfl⟩ : syracuseStep 7562915 = 11344373) B11344373
theorem B5041943 : Blo 2239435 5041943 := bstep (se 1 (by rfl) ⟨3781457, by rfl⟩ : syracuseStep 5041943 = 7562915) B7562915
theorem B3361295 : Blo 2239435 3361295 := bstep (se 1 (by rfl) ⟨2520971, by rfl⟩ : syracuseStep 3361295 = 5041943) B5041943
theorem B2240863 : Blo 2239435 2240863 := bstep (se 1 (by rfl) ⟨1680647, by rfl⟩ : syracuseStep 2240863 = 3361295) B3361295
theorem B3361301 : Blo 2239435 3361301 := bbase (se 6 (by rfl) ⟨78780, by rfl⟩ : syracuseStep 3361301 = 157561) (by norm_num)
theorem B2240867 : Blo 2239435 2240867 := bstep (se 1 (by rfl) ⟨1680650, by rfl⟩ : syracuseStep 2240867 = 3361301) B3361301
theorem B19143701 : Blo 2239435 19143701 := bbase (se 6 (by rfl) ⟨448680, by rfl⟩ : syracuseStep 19143701 = 897361) (by norm_num)
theorem B12762467 : Blo 2239435 12762467 := bstep (se 1 (by rfl) ⟨9571850, by rfl⟩ : syracuseStep 12762467 = 19143701) B19143701
theorem B8508311 : Blo 2239435 8508311 := bstep (se 1 (by rfl) ⟨6381233, by rfl⟩ : syracuseStep 8508311 = 12762467) B12762467
theorem B5672207 : Blo 2239435 5672207 := bstep (se 1 (by rfl) ⟨4254155, by rfl⟩ : syracuseStep 5672207 = 8508311) B8508311
theorem B3781471 : Blo 2239435 3781471 := bstep (se 1 (by rfl) ⟨2836103, by rfl⟩ : syracuseStep 3781471 = 5672207) B5672207
theorem B5041961 : Blo 2239435 5041961 := bstep (se 2 (by rfl) ⟨1890735, by rfl⟩ : syracuseStep 5041961 = 3781471) B3781471
theorem B3361307 : Blo 2239435 3361307 := bstep (se 1 (by rfl) ⟨2520980, by rfl⟩ : syracuseStep 3361307 = 5041961) B5041961
theorem B2240871 : Blo 2239435 2240871 := bstep (se 1 (by rfl) ⟨1680653, by rfl⟩ : syracuseStep 2240871 = 3361307) B3361307
theorem B2520985 : Blo 2239435 2520985 := bbase (se 2 (by rfl) ⟨945369, by rfl⟩ : syracuseStep 2520985 = 1890739) (by norm_num)
theorem B3361313 : Blo 2239435 3361313 := bstep (se 2 (by rfl) ⟨1260492, by rfl⟩ : syracuseStep 3361313 = 2520985) B2520985
theorem B2240875 : Blo 2239435 2240875 := bstep (se 1 (by rfl) ⟨1680656, by rfl⟩ : syracuseStep 2240875 = 3361313) B3361313
theorem B8508341 : Blo 2239435 8508341 := bbase (se 5 (by rfl) ⟨398828, by rfl⟩ : syracuseStep 8508341 = 797657) (by norm_num)
theorem B5672227 : Blo 2239435 5672227 := bstep (se 1 (by rfl) ⟨4254170, by rfl⟩ : syracuseStep 5672227 = 8508341) B8508341
theorem B7562969 : Blo 2239435 7562969 := bstep (se 2 (by rfl) ⟨2836113, by rfl⟩ : syracuseStep 7562969 = 5672227) B5672227
theorem B5041979 : Blo 2239435 5041979 := bstep (se 1 (by rfl) ⟨3781484, by rfl⟩ : syracuseStep 5041979 = 7562969) B7562969
theorem B3361319 : Blo 2239435 3361319 := bstep (se 1 (by rfl) ⟨2520989, by rfl⟩ : syracuseStep 3361319 = 5041979) B5041979
theorem B2240879 : Blo 2239435 2240879 := bstep (se 1 (by rfl) ⟨1680659, by rfl⟩ : syracuseStep 2240879 = 3361319) B3361319
theorem B3361325 : Blo 2239435 3361325 := bbase (se 3 (by rfl) ⟨630248, by rfl⟩ : syracuseStep 3361325 = 1260497) (by norm_num)
theorem B2240883 : Blo 2239435 2240883 := bstep (se 1 (by rfl) ⟨1680662, by rfl⟩ : syracuseStep 2240883 = 3361325) B3361325
theorem B5041997 : Blo 2239435 5041997 := bbase (se 3 (by rfl) ⟨945374, by rfl⟩ : syracuseStep 5041997 = 1890749) (by norm_num)
theorem B3361331 : Blo 2239435 3361331 := bstep (se 1 (by rfl) ⟨2520998, by rfl⟩ : syracuseStep 3361331 = 5041997) B5041997
theorem B2240887 : Blo 2239435 2240887 := bstep (se 1 (by rfl) ⟨1680665, by rfl⟩ : syracuseStep 2240887 = 3361331) B3361331
theorem B2836129 : Blo 2239435 2836129 := bbase (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) (by norm_num)
theorem B3781505 : Blo 2239435 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B2521003 : Blo 2239435 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B3361337 : Blo 2239435 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B2240891 : Blo 2239435 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B25525205 : Blo 2239435 25525205 := bbase (se 7 (by rfl) ⟨299123, by rfl⟩ : syracuseStep 25525205 = 598247) (by norm_num)
theorem B17016803 : Blo 2239435 17016803 := bstep (se 1 (by rfl) ⟨12762602, by rfl⟩ : syracuseStep 17016803 = 25525205) B25525205
theorem B11344535 : Blo 2239435 11344535 := bstep (se 1 (by rfl) ⟨8508401, by rfl⟩ : syracuseStep 11344535 = 17016803) B17016803
theorem B7563023 : Blo 2239435 7563023 := bstep (se 1 (by rfl) ⟨5672267, by rfl⟩ : syracuseStep 7563023 = 11344535) B11344535
theorem B5042015 : Blo 2239435 5042015 := bstep (se 1 (by rfl) ⟨3781511, by rfl⟩ : syracuseStep 5042015 = 7563023) B7563023
theorem B3361343 : Blo 2239435 3361343 := bstep (se 1 (by rfl) ⟨2521007, by rfl⟩ : syracuseStep 3361343 = 5042015) B5042015
theorem B2240895 : Blo 2239435 2240895 := bstep (se 1 (by rfl) ⟨1680671, by rfl⟩ : syracuseStep 2240895 = 3361343) B3361343
theorem B3361349 : Blo 2239435 3361349 := bbase (se 4 (by rfl) ⟨315126, by rfl⟩ : syracuseStep 3361349 = 630253) (by norm_num)
theorem B2240899 : Blo 2239435 2240899 := bstep (se 1 (by rfl) ⟨1680674, by rfl⟩ : syracuseStep 2240899 = 3361349) B3361349
theorem B3781525 : Blo 2239435 3781525 := bbase (se 6 (by rfl) ⟨88629, by rfl⟩ : syracuseStep 3781525 = 177259) (by norm_num)
theorem B5042033 : Blo 2239435 5042033 := bstep (se 2 (by rfl) ⟨1890762, by rfl⟩ : syracuseStep 5042033 = 3781525) B3781525
theorem B3361355 : Blo 2239435 3361355 := bstep (se 1 (by rfl) ⟨2521016, by rfl⟩ : syracuseStep 3361355 = 5042033) B5042033
theorem B2240903 : Blo 2239435 2240903 := bstep (se 1 (by rfl) ⟨1680677, by rfl⟩ : syracuseStep 2240903 = 3361355) B3361355
theorem B2521021 : Blo 2239435 2521021 := bbase (se 3 (by rfl) ⟨472691, by rfl⟩ : syracuseStep 2521021 = 945383) (by norm_num)
theorem B3361361 : Blo 2239435 3361361 := bstep (se 2 (by rfl) ⟨1260510, by rfl⟩ : syracuseStep 3361361 = 2521021) B2521021
theorem B2240907 : Blo 2239435 2240907 := bstep (se 1 (by rfl) ⟨1680680, by rfl⟩ : syracuseStep 2240907 = 3361361) B3361361
theorem B7563077 : Blo 2239435 7563077 := bbase (se 4 (by rfl) ⟨709038, by rfl⟩ : syracuseStep 7563077 = 1418077) (by norm_num)
theorem B5042051 : Blo 2239435 5042051 := bstep (se 1 (by rfl) ⟨3781538, by rfl⟩ : syracuseStep 5042051 = 7563077) B7563077
theorem B3361367 : Blo 2239435 3361367 := bstep (se 1 (by rfl) ⟨2521025, by rfl⟩ : syracuseStep 3361367 = 5042051) B5042051
theorem B2240911 : Blo 2239435 2240911 := bstep (se 1 (by rfl) ⟨1680683, by rfl⟩ : syracuseStep 2240911 = 3361367) B3361367
theorem B3361373 : Blo 2239435 3361373 := bbase (se 3 (by rfl) ⟨630257, by rfl⟩ : syracuseStep 3361373 = 1260515) (by norm_num)
theorem B2240915 : Blo 2239435 2240915 := bstep (se 1 (by rfl) ⟨1680686, by rfl⟩ : syracuseStep 2240915 = 3361373) B3361373
theorem B5042069 : Blo 2239435 5042069 := bbase (se 6 (by rfl) ⟨118173, by rfl⟩ : syracuseStep 5042069 = 236347) (by norm_num)
theorem B3361379 : Blo 2239435 3361379 := bstep (se 1 (by rfl) ⟨2521034, by rfl⟩ : syracuseStep 3361379 = 5042069) B5042069
theorem B2240919 : Blo 2239435 2240919 := bstep (se 1 (by rfl) ⟨1680689, by rfl⟩ : syracuseStep 2240919 = 3361379) B3361379
theorem B4786037 : Blo 2239435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 2239435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B8508509 : Blo 2239435 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B5672339 : Blo 2239435 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B3781559 : Blo 2239435 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B2521039 : Blo 2239435 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B3361385 : Blo 2239435 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B2240923 : Blo 2239435 2240923 := bstep (se 1 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 2240923 = 3361385) B3361385
theorem B12114677 : Blo 2239435 12114677 := bbase (se 5 (by rfl) ⟨567875, by rfl⟩ : syracuseStep 12114677 = 1135751) (by norm_num)
theorem B8076451 : Blo 2239435 8076451 := bstep (se 1 (by rfl) ⟨6057338, by rfl⟩ : syracuseStep 8076451 = 12114677) B12114677
theorem B10768601 : Blo 2239435 10768601 := bstep (se 2 (by rfl) ⟨4038225, by rfl⟩ : syracuseStep 10768601 = 8076451) B8076451
theorem B7179067 : Blo 2239435 7179067 := bstep (se 1 (by rfl) ⟨5384300, by rfl⟩ : syracuseStep 7179067 = 10768601) B10768601
theorem B9572089 : Blo 2239435 9572089 := bstep (se 2 (by rfl) ⟨3589533, by rfl⟩ : syracuseStep 9572089 = 7179067) B7179067
theorem B12762785 : Blo 2239435 12762785 := bstep (se 2 (by rfl) ⟨4786044, by rfl⟩ : syracuseStep 12762785 = 9572089) B9572089
theorem B8508523 : Blo 2239435 8508523 := bstep (se 1 (by rfl) ⟨6381392, by rfl⟩ : syracuseStep 8508523 = 12762785) B12762785
theorem B11344697 : Blo 2239435 11344697 := bstep (se 2 (by rfl) ⟨4254261, by rfl⟩ : syracuseStep 11344697 = 8508523) B8508523
theorem B7563131 : Blo 2239435 7563131 := bstep (se 1 (by rfl) ⟨5672348, by rfl⟩ : syracuseStep 7563131 = 11344697) B11344697
theorem B5042087 : Blo 2239435 5042087 := bstep (se 1 (by rfl) ⟨3781565, by rfl⟩ : syracuseStep 5042087 = 7563131) B7563131
theorem B3361391 : Blo 2239435 3361391 := bstep (se 1 (by rfl) ⟨2521043, by rfl⟩ : syracuseStep 3361391 = 5042087) B5042087
theorem B2240927 : Blo 2239435 2240927 := bstep (se 1 (by rfl) ⟨1680695, by rfl⟩ : syracuseStep 2240927 = 3361391) B3361391
theorem B3361397 : Blo 2239435 3361397 := bbase (se 5 (by rfl) ⟨157565, by rfl⟩ : syracuseStep 3361397 = 315131) (by norm_num)
theorem B2240931 : Blo 2239435 2240931 := bstep (se 1 (by rfl) ⟨1680698, by rfl⟩ : syracuseStep 2240931 = 3361397) B3361397
theorem B4254277 : Blo 2239435 4254277 := bbase (se 4 (by rfl) ⟨398838, by rfl⟩ : syracuseStep 4254277 = 797677) (by norm_num)
theorem B5672369 : Blo 2239435 5672369 := bstep (se 2 (by rfl) ⟨2127138, by rfl⟩ : syracuseStep 5672369 = 4254277) B4254277
theorem B3781579 : Blo 2239435 3781579 := bstep (se 1 (by rfl) ⟨2836184, by rfl⟩ : syracuseStep 3781579 = 5672369) B5672369
theorem B5042105 : Blo 2239435 5042105 := bstep (se 2 (by rfl) ⟨1890789, by rfl⟩ : syracuseStep 5042105 = 3781579) B3781579
theorem B3361403 : Blo 2239435 3361403 := bstep (se 1 (by rfl) ⟨2521052, by rfl⟩ : syracuseStep 3361403 = 5042105) B5042105
theorem B2240935 : Blo 2239435 2240935 := bstep (se 1 (by rfl) ⟨1680701, by rfl⟩ : syracuseStep 2240935 = 3361403) B3361403
theorem B2521057 : Blo 2239435 2521057 := bbase (se 2 (by rfl) ⟨945396, by rfl⟩ : syracuseStep 2521057 = 1890793) (by norm_num)
theorem B3361409 : Blo 2239435 3361409 := bstep (se 2 (by rfl) ⟨1260528, by rfl⟩ : syracuseStep 3361409 = 2521057) B2521057
theorem B2240939 : Blo 2239435 2240939 := bstep (se 1 (by rfl) ⟨1680704, by rfl⟩ : syracuseStep 2240939 = 3361409) B3361409
theorem B5672389 : Blo 2239435 5672389 := bbase (se 4 (by rfl) ⟨531786, by rfl⟩ : syracuseStep 5672389 = 1063573) (by norm_num)
theorem B7563185 : Blo 2239435 7563185 := bstep (se 2 (by rfl) ⟨2836194, by rfl⟩ : syracuseStep 7563185 = 5672389) B5672389
theorem B5042123 : Blo 2239435 5042123 := bstep (se 1 (by rfl) ⟨3781592, by rfl⟩ : syracuseStep 5042123 = 7563185) B7563185
theorem B3361415 : Blo 2239435 3361415 := bstep (se 1 (by rfl) ⟨2521061, by rfl⟩ : syracuseStep 3361415 = 5042123) B5042123
theorem B2240943 : Blo 2239435 2240943 := bstep (se 1 (by rfl) ⟨1680707, by rfl⟩ : syracuseStep 2240943 = 3361415) B3361415
theorem B3361421 : Blo 2239435 3361421 := bbase (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) (by norm_num)
theorem B2240947 : Blo 2239435 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B5042141 : Blo 2239435 5042141 := bbase (se 3 (by rfl) ⟨945401, by rfl⟩ : syracuseStep 5042141 = 1890803) (by norm_num)
theorem B3361427 : Blo 2239435 3361427 := bstep (se 1 (by rfl) ⟨2521070, by rfl⟩ : syracuseStep 3361427 = 5042141) B5042141
theorem B2240951 : Blo 2239435 2240951 := bstep (se 1 (by rfl) ⟨1680713, by rfl⟩ : syracuseStep 2240951 = 3361427) B3361427
theorem B3781613 : Blo 2239435 3781613 := bbase (se 3 (by rfl) ⟨709052, by rfl⟩ : syracuseStep 3781613 = 1418105) (by norm_num)
theorem B2521075 : Blo 2239435 2521075 := bstep (se 1 (by rfl) ⟨1890806, by rfl⟩ : syracuseStep 2521075 = 3781613) B3781613
theorem B3361433 : Blo 2239435 3361433 := bstep (se 2 (by rfl) ⟨1260537, by rfl⟩ : syracuseStep 3361433 = 2521075) B2521075
theorem B2240955 : Blo 2239435 2240955 := bstep (se 1 (by rfl) ⟨1680716, by rfl⟩ : syracuseStep 2240955 = 3361433) B3361433
theorem B4543069 : Blo 2239435 4543069 := bbase (se 3 (by rfl) ⟨851825, by rfl⟩ : syracuseStep 4543069 = 1703651) (by norm_num)
theorem B6057425 : Blo 2239435 6057425 := bstep (se 2 (by rfl) ⟨2271534, by rfl⟩ : syracuseStep 6057425 = 4543069) B4543069
theorem B4038283 : Blo 2239435 4038283 := bstep (se 1 (by rfl) ⟨3028712, by rfl⟩ : syracuseStep 4038283 = 6057425) B6057425
theorem B5384377 : Blo 2239435 5384377 := bstep (se 2 (by rfl) ⟨2019141, by rfl⟩ : syracuseStep 5384377 = 4038283) B4038283
theorem B28716677 : Blo 2239435 28716677 := bstep (se 4 (by rfl) ⟨2692188, by rfl⟩ : syracuseStep 28716677 = 5384377) B5384377
theorem B19144451 : Blo 2239435 19144451 := bstep (se 1 (by rfl) ⟨14358338, by rfl⟩ : syracuseStep 19144451 = 28716677) B28716677
theorem B12762967 : Blo 2239435 12762967 := bstep (se 1 (by rfl) ⟨9572225, by rfl⟩ : syracuseStep 12762967 = 19144451) B19144451
theorem B17017289 : Blo 2239435 17017289 := bstep (se 2 (by rfl) ⟨6381483, by rfl⟩ : syracuseStep 17017289 = 12762967) B12762967
theorem B11344859 : Blo 2239435 11344859 := bstep (se 1 (by rfl) ⟨8508644, by rfl⟩ : syracuseStep 11344859 = 17017289) B17017289
theorem B7563239 : Blo 2239435 7563239 := bstep (se 1 (by rfl) ⟨5672429, by rfl⟩ : syracuseStep 7563239 = 11344859) B11344859
theorem B5042159 : Blo 2239435 5042159 := bstep (se 1 (by rfl) ⟨3781619, by rfl⟩ : syracuseStep 5042159 = 7563239) B7563239
theorem B3361439 : Blo 2239435 3361439 := bstep (se 1 (by rfl) ⟨2521079, by rfl⟩ : syracuseStep 3361439 = 5042159) B5042159
theorem B2240959 : Blo 2239435 2240959 := bstep (se 1 (by rfl) ⟨1680719, by rfl⟩ : syracuseStep 2240959 = 3361439) B3361439
theorem B3361445 : Blo 2239435 3361445 := bbase (se 4 (by rfl) ⟨315135, by rfl⟩ : syracuseStep 3361445 = 630271) (by norm_num)
theorem B2240963 : Blo 2239435 2240963 := bstep (se 1 (by rfl) ⟨1680722, by rfl⟩ : syracuseStep 2240963 = 3361445) B3361445
theorem B2836225 : Blo 2239435 2836225 := bbase (se 2 (by rfl) ⟨1063584, by rfl⟩ : syracuseStep 2836225 = 2127169) (by norm_num)
theorem B3781633 : Blo 2239435 3781633 := bstep (se 2 (by rfl) ⟨1418112, by rfl⟩ : syracuseStep 3781633 = 2836225) B2836225
theorem B5042177 : Blo 2239435 5042177 := bstep (se 2 (by rfl) ⟨1890816, by rfl⟩ : syracuseStep 5042177 = 3781633) B3781633
theorem B3361451 : Blo 2239435 3361451 := bstep (se 1 (by rfl) ⟨2521088, by rfl⟩ : syracuseStep 3361451 = 5042177) B5042177
theorem B2240967 : Blo 2239435 2240967 := bstep (se 1 (by rfl) ⟨1680725, by rfl⟩ : syracuseStep 2240967 = 3361451) B3361451
theorem B2521093 : Blo 2239435 2521093 := bbase (se 4 (by rfl) ⟨236352, by rfl⟩ : syracuseStep 2521093 = 472705) (by norm_num)
theorem B3361457 : Blo 2239435 3361457 := bstep (se 2 (by rfl) ⟨1260546, by rfl⟩ : syracuseStep 3361457 = 2521093) B2521093
theorem B2240971 : Blo 2239435 2240971 := bstep (se 1 (by rfl) ⟨1680728, by rfl⟩ : syracuseStep 2240971 = 3361457) B3361457
theorem B3190765 : Blo 2239435 3190765 := bbase (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) (by norm_num)
theorem B4254353 : Blo 2239435 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B2836235 : Blo 2239435 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B7563293 : Blo 2239435 7563293 := bstep (se 3 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 7563293 = 2836235) B2836235
theorem B5042195 : Blo 2239435 5042195 := bstep (se 1 (by rfl) ⟨3781646, by rfl⟩ : syracuseStep 5042195 = 7563293) B7563293
theorem B3361463 : Blo 2239435 3361463 := bstep (se 1 (by rfl) ⟨2521097, by rfl⟩ : syracuseStep 3361463 = 5042195) B5042195
theorem B2240975 : Blo 2239435 2240975 := bstep (se 1 (by rfl) ⟨1680731, by rfl⟩ : syracuseStep 2240975 = 3361463) B3361463
theorem B3361469 : Blo 2239435 3361469 := bbase (se 3 (by rfl) ⟨630275, by rfl⟩ : syracuseStep 3361469 = 1260551) (by norm_num)
theorem B2240979 : Blo 2239435 2240979 := bstep (se 1 (by rfl) ⟨1680734, by rfl⟩ : syracuseStep 2240979 = 3361469) B3361469
theorem B5042213 : Blo 2239435 5042213 := bbase (se 4 (by rfl) ⟨472707, by rfl⟩ : syracuseStep 5042213 = 945415) (by norm_num)
theorem B3361475 : Blo 2239435 3361475 := bstep (se 1 (by rfl) ⟨2521106, by rfl⟩ : syracuseStep 3361475 = 5042213) B5042213
theorem B2240983 : Blo 2239435 2240983 := bstep (se 1 (by rfl) ⟨1680737, by rfl⟩ : syracuseStep 2240983 = 3361475) B3361475
theorem B5672501 : Blo 2239435 5672501 := bbase (se 5 (by rfl) ⟨265898, by rfl⟩ : syracuseStep 5672501 = 531797) (by norm_num)
theorem B3781667 : Blo 2239435 3781667 := bstep (se 1 (by rfl) ⟨2836250, by rfl⟩ : syracuseStep 3781667 = 5672501) B5672501
theorem B2521111 : Blo 2239435 2521111 := bstep (se 1 (by rfl) ⟨1890833, by rfl⟩ : syracuseStep 2521111 = 3781667) B3781667
theorem B3361481 : Blo 2239435 3361481 := bstep (se 2 (by rfl) ⟨1260555, by rfl⟩ : syracuseStep 3361481 = 2521111) B2521111
theorem B2240987 : Blo 2239435 2240987 := bstep (se 1 (by rfl) ⟨1680740, by rfl⟩ : syracuseStep 2240987 = 3361481) B3361481
theorem B4038341 : Blo 2239435 4038341 := bbase (se 4 (by rfl) ⟨378594, by rfl⟩ : syracuseStep 4038341 = 757189) (by norm_num)
theorem B10768909 : Blo 2239435 10768909 := bstep (se 3 (by rfl) ⟨2019170, by rfl⟩ : syracuseStep 10768909 = 4038341) B4038341
theorem B14358545 : Blo 2239435 14358545 := bstep (se 2 (by rfl) ⟨5384454, by rfl⟩ : syracuseStep 14358545 = 10768909) B10768909
theorem B9572363 : Blo 2239435 9572363 := bstep (se 1 (by rfl) ⟨7179272, by rfl⟩ : syracuseStep 9572363 = 14358545) B14358545
theorem B6381575 : Blo 2239435 6381575 := bstep (se 1 (by rfl) ⟨4786181, by rfl⟩ : syracuseStep 6381575 = 9572363) B9572363
theorem B4254383 : Blo 2239435 4254383 := bstep (se 1 (by rfl) ⟨3190787, by rfl⟩ : syracuseStep 4254383 = 6381575) B6381575
theorem B11345021 : Blo 2239435 11345021 := bstep (se 3 (by rfl) ⟨2127191, by rfl⟩ : syracuseStep 11345021 = 4254383) B4254383
theorem B7563347 : Blo 2239435 7563347 := bstep (se 1 (by rfl) ⟨5672510, by rfl⟩ : syracuseStep 7563347 = 11345021) B11345021
theorem B5042231 : Blo 2239435 5042231 := bstep (se 1 (by rfl) ⟨3781673, by rfl⟩ : syracuseStep 5042231 = 7563347) B7563347
theorem B3361487 : Blo 2239435 3361487 := bstep (se 1 (by rfl) ⟨2521115, by rfl⟩ : syracuseStep 3361487 = 5042231) B5042231
theorem B2240991 : Blo 2239435 2240991 := bstep (se 1 (by rfl) ⟨1680743, by rfl⟩ : syracuseStep 2240991 = 3361487) B3361487
theorem B3361493 : Blo 2239435 3361493 := bbase (se 7 (by rfl) ⟨39392, by rfl⟩ : syracuseStep 3361493 = 78785) (by norm_num)
theorem B2240995 : Blo 2239435 2240995 := bstep (se 1 (by rfl) ⟨1680746, by rfl⟩ : syracuseStep 2240995 = 3361493) B3361493
theorem B10768949 : Blo 2239435 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B7179299 : Blo 2239435 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B4786199 : Blo 2239435 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B3190799 : Blo 2239435 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B8508797 : Blo 2239435 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B5672531 : Blo 2239435 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B3781687 : Blo 2239435 3781687 := bstep (se 1 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 3781687 = 5672531) B5672531
theorem B5042249 : Blo 2239435 5042249 := bstep (se 2 (by rfl) ⟨1890843, by rfl⟩ : syracuseStep 5042249 = 3781687) B3781687
theorem B3361499 : Blo 2239435 3361499 := bstep (se 1 (by rfl) ⟨2521124, by rfl⟩ : syracuseStep 3361499 = 5042249) B5042249
theorem B2240999 : Blo 2239435 2240999 := bstep (se 1 (by rfl) ⟨1680749, by rfl⟩ : syracuseStep 2240999 = 3361499) B3361499
theorem B2521129 : Blo 2239435 2521129 := bbase (se 2 (by rfl) ⟨945423, by rfl⟩ : syracuseStep 2521129 = 1890847) (by norm_num)
theorem B3361505 : Blo 2239435 3361505 := bstep (se 2 (by rfl) ⟨1260564, by rfl⟩ : syracuseStep 3361505 = 2521129) B2521129
theorem B2241003 : Blo 2239435 2241003 := bstep (se 1 (by rfl) ⟨1680752, by rfl⟩ : syracuseStep 2241003 = 3361505) B3361505
theorem B11499893 : Blo 2239435 11499893 := bbase (se 5 (by rfl) ⟨539057, by rfl⟩ : syracuseStep 11499893 = 1078115) (by norm_num)
theorem B7666595 : Blo 2239435 7666595 := bstep (se 1 (by rfl) ⟨5749946, by rfl⟩ : syracuseStep 7666595 = 11499893) B11499893
theorem B5111063 : Blo 2239435 5111063 := bstep (se 1 (by rfl) ⟨3833297, by rfl⟩ : syracuseStep 5111063 = 7666595) B7666595
theorem B3407375 : Blo 2239435 3407375 := bstep (se 1 (by rfl) ⟨2555531, by rfl⟩ : syracuseStep 3407375 = 5111063) B5111063
theorem B2271583 : Blo 2239435 2271583 := bstep (se 1 (by rfl) ⟨1703687, by rfl⟩ : syracuseStep 2271583 = 3407375) B3407375
theorem B12115109 : Blo 2239435 12115109 := bstep (se 4 (by rfl) ⟨1135791, by rfl⟩ : syracuseStep 12115109 = 2271583) B2271583
theorem B32306957 : Blo 2239435 32306957 := bstep (se 3 (by rfl) ⟨6057554, by rfl⟩ : syracuseStep 32306957 = 12115109) B12115109
theorem B21537971 : Blo 2239435 21537971 := bstep (se 1 (by rfl) ⟨16153478, by rfl⟩ : syracuseStep 21537971 = 32306957) B32306957
theorem B14358647 : Blo 2239435 14358647 := bstep (se 1 (by rfl) ⟨10768985, by rfl⟩ : syracuseStep 14358647 = 21537971) B21537971
theorem B9572431 : Blo 2239435 9572431 := bstep (se 1 (by rfl) ⟨7179323, by rfl⟩ : syracuseStep 9572431 = 14358647) B14358647
theorem B12763241 : Blo 2239435 12763241 := bstep (se 2 (by rfl) ⟨4786215, by rfl⟩ : syracuseStep 12763241 = 9572431) B9572431
theorem B8508827 : Blo 2239435 8508827 := bstep (se 1 (by rfl) ⟨6381620, by rfl⟩ : syracuseStep 8508827 = 12763241) B12763241
theorem B5672551 : Blo 2239435 5672551 := bstep (se 1 (by rfl) ⟨4254413, by rfl⟩ : syracuseStep 5672551 = 8508827) B8508827
theorem B7563401 : Blo 2239435 7563401 := bstep (se 2 (by rfl) ⟨2836275, by rfl⟩ : syracuseStep 7563401 = 5672551) B5672551
theorem B5042267 : Blo 2239435 5042267 := bstep (se 1 (by rfl) ⟨3781700, by rfl⟩ : syracuseStep 5042267 = 7563401) B7563401
theorem B3361511 : Blo 2239435 3361511 := bstep (se 1 (by rfl) ⟨2521133, by rfl⟩ : syracuseStep 3361511 = 5042267) B5042267
theorem B2241007 : Blo 2239435 2241007 := bstep (se 1 (by rfl) ⟨1680755, by rfl⟩ : syracuseStep 2241007 = 3361511) B3361511
theorem B3361517 : Blo 2239435 3361517 := bbase (se 3 (by rfl) ⟨630284, by rfl⟩ : syracuseStep 3361517 = 1260569) (by norm_num)
theorem B2241011 : Blo 2239435 2241011 := bstep (se 1 (by rfl) ⟨1680758, by rfl⟩ : syracuseStep 2241011 = 3361517) B3361517
theorem B5042285 : Blo 2239435 5042285 := bbase (se 3 (by rfl) ⟨945428, by rfl⟩ : syracuseStep 5042285 = 1890857) (by norm_num)
theorem B3361523 : Blo 2239435 3361523 := bstep (se 1 (by rfl) ⟨2521142, by rfl⟩ : syracuseStep 3361523 = 5042285) B5042285
theorem B2241015 : Blo 2239435 2241015 := bstep (se 1 (by rfl) ⟨1680761, by rfl⟩ : syracuseStep 2241015 = 3361523) B3361523
theorem B4254437 : Blo 2239435 4254437 := bbase (se 4 (by rfl) ⟨398853, by rfl⟩ : syracuseStep 4254437 = 797707) (by norm_num)
theorem B2836291 : Blo 2239435 2836291 := bstep (se 1 (by rfl) ⟨2127218, by rfl⟩ : syracuseStep 2836291 = 4254437) B4254437
theorem B3781721 : Blo 2239435 3781721 := bstep (se 2 (by rfl) ⟨1418145, by rfl⟩ : syracuseStep 3781721 = 2836291) B2836291
theorem B2521147 : Blo 2239435 2521147 := bstep (se 1 (by rfl) ⟨1890860, by rfl⟩ : syracuseStep 2521147 = 3781721) B3781721
theorem B3361529 : Blo 2239435 3361529 := bstep (se 2 (by rfl) ⟨1260573, by rfl⟩ : syracuseStep 3361529 = 2521147) B2521147
theorem B2241019 : Blo 2239435 2241019 := bstep (se 1 (by rfl) ⟨1680764, by rfl⟩ : syracuseStep 2241019 = 3361529) B3361529
theorem B43076245 : Blo 2239435 43076245 := bbase (se 6 (by rfl) ⟨1009599, by rfl⟩ : syracuseStep 43076245 = 2019199) (by norm_num)
theorem B57434993 : Blo 2239435 57434993 := bstep (se 2 (by rfl) ⟨21538122, by rfl⟩ : syracuseStep 57434993 = 43076245) B43076245
theorem B38289995 : Blo 2239435 38289995 := bstep (se 1 (by rfl) ⟨28717496, by rfl⟩ : syracuseStep 38289995 = 57434993) B57434993
theorem B25526663 : Blo 2239435 25526663 := bstep (se 1 (by rfl) ⟨19144997, by rfl⟩ : syracuseStep 25526663 = 38289995) B38289995
theorem B17017775 : Blo 2239435 17017775 := bstep (se 1 (by rfl) ⟨12763331, by rfl⟩ : syracuseStep 17017775 = 25526663) B25526663
theorem B11345183 : Blo 2239435 11345183 := bstep (se 1 (by rfl) ⟨8508887, by rfl⟩ : syracuseStep 11345183 = 17017775) B17017775
theorem B7563455 : Blo 2239435 7563455 := bstep (se 1 (by rfl) ⟨5672591, by rfl⟩ : syracuseStep 7563455 = 11345183) B11345183
theorem B5042303 : Blo 2239435 5042303 := bstep (se 1 (by rfl) ⟨3781727, by rfl⟩ : syracuseStep 5042303 = 7563455) B7563455
theorem B3361535 : Blo 2239435 3361535 := bstep (se 1 (by rfl) ⟨2521151, by rfl⟩ : syracuseStep 3361535 = 5042303) B5042303
theorem B2241023 : Blo 2239435 2241023 := bstep (se 1 (by rfl) ⟨1680767, by rfl⟩ : syracuseStep 2241023 = 3361535) B3361535
theorem B3361541 : Blo 2239435 3361541 := bbase (se 4 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 3361541 = 630289) (by norm_num)
theorem B2241027 : Blo 2239435 2241027 := bstep (se 1 (by rfl) ⟨1680770, by rfl⟩ : syracuseStep 2241027 = 3361541) B3361541
theorem B3781741 : Blo 2239435 3781741 := bbase (se 3 (by rfl) ⟨709076, by rfl⟩ : syracuseStep 3781741 = 1418153) (by norm_num)
theorem B5042321 : Blo 2239435 5042321 := bstep (se 2 (by rfl) ⟨1890870, by rfl⟩ : syracuseStep 5042321 = 3781741) B3781741
theorem B3361547 : Blo 2239435 3361547 := bstep (se 1 (by rfl) ⟨2521160, by rfl⟩ : syracuseStep 3361547 = 5042321) B5042321
theorem B2241031 : Blo 2239435 2241031 := bstep (se 1 (by rfl) ⟨1680773, by rfl⟩ : syracuseStep 2241031 = 3361547) B3361547
theorem B2521165 : Blo 2239435 2521165 := bbase (se 3 (by rfl) ⟨472718, by rfl⟩ : syracuseStep 2521165 = 945437) (by norm_num)
theorem B3361553 : Blo 2239435 3361553 := bstep (se 2 (by rfl) ⟨1260582, by rfl⟩ : syracuseStep 3361553 = 2521165) B2521165
theorem B2241035 : Blo 2239435 2241035 := bstep (se 1 (by rfl) ⟨1680776, by rfl⟩ : syracuseStep 2241035 = 3361553) B3361553
theorem B7563509 : Blo 2239435 7563509 := bbase (se 5 (by rfl) ⟨354539, by rfl⟩ : syracuseStep 7563509 = 709079) (by norm_num)
theorem B5042339 : Blo 2239435 5042339 := bstep (se 1 (by rfl) ⟨3781754, by rfl⟩ : syracuseStep 5042339 = 7563509) B7563509
theorem B3361559 : Blo 2239435 3361559 := bstep (se 1 (by rfl) ⟨2521169, by rfl⟩ : syracuseStep 3361559 = 5042339) B5042339
theorem B2241039 : Blo 2239435 2241039 := bstep (se 1 (by rfl) ⟨1680779, by rfl⟩ : syracuseStep 2241039 = 3361559) B3361559
theorem B3361565 : Blo 2239435 3361565 := bbase (se 3 (by rfl) ⟨630293, by rfl⟩ : syracuseStep 3361565 = 1260587) (by norm_num)
theorem B2241043 : Blo 2239435 2241043 := bstep (se 1 (by rfl) ⟨1680782, by rfl⟩ : syracuseStep 2241043 = 3361565) B3361565
theorem B5042357 : Blo 2239435 5042357 := bbase (se 5 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 5042357 = 472721) (by norm_num)
theorem B3361571 : Blo 2239435 3361571 := bstep (se 1 (by rfl) ⟨2521178, by rfl⟩ : syracuseStep 3361571 = 5042357) B5042357
theorem B2241047 : Blo 2239435 2241047 := bstep (se 1 (by rfl) ⟨1680785, by rfl⟩ : syracuseStep 2241047 = 3361571) B3361571
theorem B3589733 : Blo 2239435 3589733 := bbase (se 4 (by rfl) ⟨336537, by rfl⟩ : syracuseStep 3589733 = 673075) (by norm_num)
theorem B2393155 : Blo 2239435 2393155 := bstep (se 1 (by rfl) ⟨1794866, by rfl⟩ : syracuseStep 2393155 = 3589733) B3589733
theorem B12763493 : Blo 2239435 12763493 := bstep (se 4 (by rfl) ⟨1196577, by rfl⟩ : syracuseStep 12763493 = 2393155) B2393155
theorem B8508995 : Blo 2239435 8508995 := bstep (se 1 (by rfl) ⟨6381746, by rfl⟩ : syracuseStep 8508995 = 12763493) B12763493
theorem B5672663 : Blo 2239435 5672663 := bstep (se 1 (by rfl) ⟨4254497, by rfl⟩ : syracuseStep 5672663 = 8508995) B8508995
theorem B3781775 : Blo 2239435 3781775 := bstep (se 1 (by rfl) ⟨2836331, by rfl⟩ : syracuseStep 3781775 = 5672663) B5672663
theorem B2521183 : Blo 2239435 2521183 := bstep (se 1 (by rfl) ⟨1890887, by rfl⟩ : syracuseStep 2521183 = 3781775) B3781775
theorem B3361577 : Blo 2239435 3361577 := bstep (se 2 (by rfl) ⟨1260591, by rfl⟩ : syracuseStep 3361577 = 2521183) B2521183
theorem B2241051 : Blo 2239435 2241051 := bstep (se 1 (by rfl) ⟨1680788, by rfl⟩ : syracuseStep 2241051 = 3361577) B3361577
theorem B3833381 : Blo 2239435 3833381 := bbase (se 4 (by rfl) ⟨359379, by rfl⟩ : syracuseStep 3833381 = 718759) (by norm_num)
theorem B2555587 : Blo 2239435 2555587 := bstep (se 1 (by rfl) ⟨1916690, by rfl⟩ : syracuseStep 2555587 = 3833381) B3833381
theorem B3407449 : Blo 2239435 3407449 := bstep (se 2 (by rfl) ⟨1277793, by rfl⟩ : syracuseStep 3407449 = 2555587) B2555587
theorem B4543265 : Blo 2239435 4543265 := bstep (se 2 (by rfl) ⟨1703724, by rfl⟩ : syracuseStep 4543265 = 3407449) B3407449
theorem B3028843 : Blo 2239435 3028843 := bstep (se 1 (by rfl) ⟨2271632, by rfl⟩ : syracuseStep 3028843 = 4543265) B4543265
theorem B4038457 : Blo 2239435 4038457 := bstep (se 2 (by rfl) ⟨1514421, by rfl⟩ : syracuseStep 4038457 = 3028843) B3028843
theorem B5384609 : Blo 2239435 5384609 := bstep (se 2 (by rfl) ⟨2019228, by rfl⟩ : syracuseStep 5384609 = 4038457) B4038457
theorem B3589739 : Blo 2239435 3589739 := bstep (se 1 (by rfl) ⟨2692304, by rfl⟩ : syracuseStep 3589739 = 5384609) B5384609
theorem B2393159 : Blo 2239435 2393159 := bstep (se 1 (by rfl) ⟨1794869, by rfl⟩ : syracuseStep 2393159 = 3589739) B3589739
theorem B6381757 : Blo 2239435 6381757 := bstep (se 3 (by rfl) ⟨1196579, by rfl⟩ : syracuseStep 6381757 = 2393159) B2393159
theorem B8509009 : Blo 2239435 8509009 := bstep (se 2 (by rfl) ⟨3190878, by rfl⟩ : syracuseStep 8509009 = 6381757) B6381757
theorem B11345345 : Blo 2239435 11345345 := bstep (se 2 (by rfl) ⟨4254504, by rfl⟩ : syracuseStep 11345345 = 8509009) B8509009
theorem B7563563 : Blo 2239435 7563563 := bstep (se 1 (by rfl) ⟨5672672, by rfl⟩ : syracuseStep 7563563 = 11345345) B11345345
theorem B5042375 : Blo 2239435 5042375 := bstep (se 1 (by rfl) ⟨3781781, by rfl⟩ : syracuseStep 5042375 = 7563563) B7563563
theorem B3361583 : Blo 2239435 3361583 := bstep (se 1 (by rfl) ⟨2521187, by rfl⟩ : syracuseStep 3361583 = 5042375) B5042375
theorem B2241055 : Blo 2239435 2241055 := bstep (se 1 (by rfl) ⟨1680791, by rfl⟩ : syracuseStep 2241055 = 3361583) B3361583
theorem B3361589 : Blo 2239435 3361589 := bbase (se 5 (by rfl) ⟨157574, by rfl⟩ : syracuseStep 3361589 = 315149) (by norm_num)
theorem B2241059 : Blo 2239435 2241059 := bstep (se 1 (by rfl) ⟨1680794, by rfl⟩ : syracuseStep 2241059 = 3361589) B3361589
theorem B5672693 : Blo 2239435 5672693 := bbase (se 5 (by rfl) ⟨265907, by rfl⟩ : syracuseStep 5672693 = 531815) (by norm_num)
theorem B3781795 : Blo 2239435 3781795 := bstep (se 1 (by rfl) ⟨2836346, by rfl⟩ : syracuseStep 3781795 = 5672693) B5672693
theorem B5042393 : Blo 2239435 5042393 := bstep (se 2 (by rfl) ⟨1890897, by rfl⟩ : syracuseStep 5042393 = 3781795) B3781795
theorem B3361595 : Blo 2239435 3361595 := bstep (se 1 (by rfl) ⟨2521196, by rfl⟩ : syracuseStep 3361595 = 5042393) B5042393
theorem B2241063 : Blo 2239435 2241063 := bstep (se 1 (by rfl) ⟨1680797, by rfl⟩ : syracuseStep 2241063 = 3361595) B3361595
theorem B2521201 : Blo 2239435 2521201 := bbase (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) (by norm_num)
theorem B3361601 : Blo 2239435 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B2241067 : Blo 2239435 2241067 := bstep (se 1 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 2241067 = 3361601) B3361601
theorem B2729057 : Blo 2239435 2729057 := bbase (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) (by norm_num)
theorem B29109941 : Blo 2239435 29109941 := bstep (se 5 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 29109941 = 2729057) B2729057
theorem B19406627 : Blo 2239435 19406627 := bstep (se 1 (by rfl) ⟨14554970, by rfl⟩ : syracuseStep 19406627 = 29109941) B29109941
theorem B12937751 : Blo 2239435 12937751 := bstep (se 1 (by rfl) ⟨9703313, by rfl⟩ : syracuseStep 12937751 = 19406627) B19406627
theorem B8625167 : Blo 2239435 8625167 := bstep (se 1 (by rfl) ⟨6468875, by rfl⟩ : syracuseStep 8625167 = 12937751) B12937751
theorem B5750111 : Blo 2239435 5750111 := bstep (se 1 (by rfl) ⟨4312583, by rfl⟩ : syracuseStep 5750111 = 8625167) B8625167
theorem B3833407 : Blo 2239435 3833407 := bstep (se 1 (by rfl) ⟨2875055, by rfl⟩ : syracuseStep 3833407 = 5750111) B5750111
theorem B5111209 : Blo 2239435 5111209 := bstep (se 2 (by rfl) ⟨1916703, by rfl⟩ : syracuseStep 5111209 = 3833407) B3833407
theorem B6814945 : Blo 2239435 6814945 := bstep (se 2 (by rfl) ⟨2555604, by rfl⟩ : syracuseStep 6814945 = 5111209) B5111209
theorem B9086593 : Blo 2239435 9086593 := bstep (se 2 (by rfl) ⟨3407472, by rfl⟩ : syracuseStep 9086593 = 6814945) B6814945
theorem B12115457 : Blo 2239435 12115457 := bstep (se 2 (by rfl) ⟨4543296, by rfl⟩ : syracuseStep 12115457 = 9086593) B9086593
theorem B8076971 : Blo 2239435 8076971 := bstep (se 1 (by rfl) ⟨6057728, by rfl⟩ : syracuseStep 8076971 = 12115457) B12115457
theorem B5384647 : Blo 2239435 5384647 := bstep (se 1 (by rfl) ⟨4038485, by rfl⟩ : syracuseStep 5384647 = 8076971) B8076971
theorem B7179529 : Blo 2239435 7179529 := bstep (se 2 (by rfl) ⟨2692323, by rfl⟩ : syracuseStep 7179529 = 5384647) B5384647
theorem B9572705 : Blo 2239435 9572705 := bstep (se 2 (by rfl) ⟨3589764, by rfl⟩ : syracuseStep 9572705 = 7179529) B7179529
theorem B6381803 : Blo 2239435 6381803 := bstep (se 1 (by rfl) ⟨4786352, by rfl⟩ : syracuseStep 6381803 = 9572705) B9572705
theorem B4254535 : Blo 2239435 4254535 := bstep (se 1 (by rfl) ⟨3190901, by rfl⟩ : syracuseStep 4254535 = 6381803) B6381803
theorem B5672713 : Blo 2239435 5672713 := bstep (se 2 (by rfl) ⟨2127267, by rfl⟩ : syracuseStep 5672713 = 4254535) B4254535
theorem B7563617 : Blo 2239435 7563617 := bstep (se 2 (by rfl) ⟨2836356, by rfl⟩ : syracuseStep 7563617 = 5672713) B5672713
theorem B5042411 : Blo 2239435 5042411 := bstep (se 1 (by rfl) ⟨3781808, by rfl⟩ : syracuseStep 5042411 = 7563617) B7563617
theorem B3361607 : Blo 2239435 3361607 := bstep (se 1 (by rfl) ⟨2521205, by rfl⟩ : syracuseStep 3361607 = 5042411) B5042411
theorem B2241071 : Blo 2239435 2241071 := bstep (se 1 (by rfl) ⟨1680803, by rfl⟩ : syracuseStep 2241071 = 3361607) B3361607
theorem B3361613 : Blo 2239435 3361613 := bbase (se 3 (by rfl) ⟨630302, by rfl⟩ : syracuseStep 3361613 = 1260605) (by norm_num)
theorem B2241075 : Blo 2239435 2241075 := bstep (se 1 (by rfl) ⟨1680806, by rfl⟩ : syracuseStep 2241075 = 3361613) B3361613
theorem B5042429 : Blo 2239435 5042429 := bbase (se 3 (by rfl) ⟨945455, by rfl⟩ : syracuseStep 5042429 = 1890911) (by norm_num)
theorem B3361619 : Blo 2239435 3361619 := bstep (se 1 (by rfl) ⟨2521214, by rfl⟩ : syracuseStep 3361619 = 5042429) B5042429
theorem B2241079 : Blo 2239435 2241079 := bstep (se 1 (by rfl) ⟨1680809, by rfl⟩ : syracuseStep 2241079 = 3361619) B3361619
theorem B3781829 : Blo 2239435 3781829 := bbase (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) (by norm_num)
theorem B2521219 : Blo 2239435 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B3361625 : Blo 2239435 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B2241083 : Blo 2239435 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B17018261 : Blo 2239435 17018261 := bbase (se 6 (by rfl) ⟨398865, by rfl⟩ : syracuseStep 17018261 = 797731) (by norm_num)
theorem B11345507 : Blo 2239435 11345507 := bstep (se 1 (by rfl) ⟨8509130, by rfl⟩ : syracuseStep 11345507 = 17018261) B17018261
theorem B7563671 : Blo 2239435 7563671 := bstep (se 1 (by rfl) ⟨5672753, by rfl⟩ : syracuseStep 7563671 = 11345507) B11345507
theorem B5042447 : Blo 2239435 5042447 := bstep (se 1 (by rfl) ⟨3781835, by rfl⟩ : syracuseStep 5042447 = 7563671) B7563671
theorem B3361631 : Blo 2239435 3361631 := bstep (se 1 (by rfl) ⟨2521223, by rfl⟩ : syracuseStep 3361631 = 5042447) B5042447
theorem B2241087 : Blo 2239435 2241087 := bstep (se 1 (by rfl) ⟨1680815, by rfl⟩ : syracuseStep 2241087 = 3361631) B3361631
theorem B3361637 : Blo 2239435 3361637 := bbase (se 4 (by rfl) ⟨315153, by rfl⟩ : syracuseStep 3361637 = 630307) (by norm_num)
theorem B2241091 : Blo 2239435 2241091 := bstep (se 1 (by rfl) ⟨1680818, by rfl⟩ : syracuseStep 2241091 = 3361637) B3361637
theorem B4254581 : Blo 2239435 4254581 := bbase (se 5 (by rfl) ⟨199433, by rfl⟩ : syracuseStep 4254581 = 398867) (by norm_num)
theorem B2836387 : Blo 2239435 2836387 := bstep (se 1 (by rfl) ⟨2127290, by rfl⟩ : syracuseStep 2836387 = 4254581) B4254581
theorem B3781849 : Blo 2239435 3781849 := bstep (se 2 (by rfl) ⟨1418193, by rfl⟩ : syracuseStep 3781849 = 2836387) B2836387
theorem B5042465 : Blo 2239435 5042465 := bstep (se 2 (by rfl) ⟨1890924, by rfl⟩ : syracuseStep 5042465 = 3781849) B3781849
theorem B3361643 : Blo 2239435 3361643 := bstep (se 1 (by rfl) ⟨2521232, by rfl⟩ : syracuseStep 3361643 = 5042465) B5042465
theorem B2241095 : Blo 2239435 2241095 := bstep (se 1 (by rfl) ⟨1680821, by rfl⟩ : syracuseStep 2241095 = 3361643) B3361643
theorem B2521237 : Blo 2239435 2521237 := bbase (se 6 (by rfl) ⟨59091, by rfl⟩ : syracuseStep 2521237 = 118183) (by norm_num)
theorem B3361649 : Blo 2239435 3361649 := bstep (se 2 (by rfl) ⟨1260618, by rfl⟩ : syracuseStep 3361649 = 2521237) B2521237
theorem B2241099 : Blo 2239435 2241099 := bstep (se 1 (by rfl) ⟨1680824, by rfl⟩ : syracuseStep 2241099 = 3361649) B3361649
theorem B2836397 : Blo 2239435 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B7563725 : Blo 2239435 7563725 := bstep (se 3 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 7563725 = 2836397) B2836397
theorem B5042483 : Blo 2239435 5042483 := bstep (se 1 (by rfl) ⟨3781862, by rfl⟩ : syracuseStep 5042483 = 7563725) B7563725
theorem B3361655 : Blo 2239435 3361655 := bstep (se 1 (by rfl) ⟨2521241, by rfl⟩ : syracuseStep 3361655 = 5042483) B5042483
theorem B2241103 : Blo 2239435 2241103 := bstep (se 1 (by rfl) ⟨1680827, by rfl⟩ : syracuseStep 2241103 = 3361655) B3361655
theorem B3361661 : Blo 2239435 3361661 := bbase (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) (by norm_num)
theorem B2241107 : Blo 2239435 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B5042501 : Blo 2239435 5042501 := bbase (se 4 (by rfl) ⟨472734, by rfl⟩ : syracuseStep 5042501 = 945469) (by norm_num)
theorem B3361667 : Blo 2239435 3361667 := bstep (se 1 (by rfl) ⟨2521250, by rfl⟩ : syracuseStep 3361667 = 5042501) B5042501
theorem B2241111 : Blo 2239435 2241111 := bstep (se 1 (by rfl) ⟨1680833, by rfl⟩ : syracuseStep 2241111 = 3361667) B3361667
theorem B16154261 : Blo 2239435 16154261 := bbase (se 6 (by rfl) ⟨378615, by rfl⟩ : syracuseStep 16154261 = 757231) (by norm_num)
theorem B10769507 : Blo 2239435 10769507 := bstep (se 1 (by rfl) ⟨8077130, by rfl⟩ : syracuseStep 10769507 = 16154261) B16154261
theorem B7179671 : Blo 2239435 7179671 := bstep (se 1 (by rfl) ⟨5384753, by rfl⟩ : syracuseStep 7179671 = 10769507) B10769507
theorem B4786447 : Blo 2239435 4786447 := bstep (se 1 (by rfl) ⟨3589835, by rfl⟩ : syracuseStep 4786447 = 7179671) B7179671
theorem B6381929 : Blo 2239435 6381929 := bstep (se 2 (by rfl) ⟨2393223, by rfl⟩ : syracuseStep 6381929 = 4786447) B4786447
theorem B4254619 : Blo 2239435 4254619 := bstep (se 1 (by rfl) ⟨3190964, by rfl⟩ : syracuseStep 4254619 = 6381929) B6381929
theorem B5672825 : Blo 2239435 5672825 := bstep (se 2 (by rfl) ⟨2127309, by rfl⟩ : syracuseStep 5672825 = 4254619) B4254619
theorem B3781883 : Blo 2239435 3781883 := bstep (se 1 (by rfl) ⟨2836412, by rfl⟩ : syracuseStep 3781883 = 5672825) B5672825
theorem B2521255 : Blo 2239435 2521255 := bstep (se 1 (by rfl) ⟨1890941, by rfl⟩ : syracuseStep 2521255 = 3781883) B3781883
theorem B3361673 : Blo 2239435 3361673 := bstep (se 2 (by rfl) ⟨1260627, by rfl⟩ : syracuseStep 3361673 = 2521255) B2521255
theorem B2241115 : Blo 2239435 2241115 := bstep (se 1 (by rfl) ⟨1680836, by rfl⟩ : syracuseStep 2241115 = 3361673) B3361673
theorem B11345669 : Blo 2239435 11345669 := bbase (se 4 (by rfl) ⟨1063656, by rfl⟩ : syracuseStep 11345669 = 2127313) (by norm_num)
theorem B7563779 : Blo 2239435 7563779 := bstep (se 1 (by rfl) ⟨5672834, by rfl⟩ : syracuseStep 7563779 = 11345669) B11345669
theorem B5042519 : Blo 2239435 5042519 := bstep (se 1 (by rfl) ⟨3781889, by rfl⟩ : syracuseStep 5042519 = 7563779) B7563779
theorem B3361679 : Blo 2239435 3361679 := bstep (se 1 (by rfl) ⟨2521259, by rfl⟩ : syracuseStep 3361679 = 5042519) B5042519
theorem B2241119 : Blo 2239435 2241119 := bstep (se 1 (by rfl) ⟨1680839, by rfl⟩ : syracuseStep 2241119 = 3361679) B3361679
theorem B3361685 : Blo 2239435 3361685 := bbase (se 6 (by rfl) ⟨78789, by rfl⟩ : syracuseStep 3361685 = 157579) (by norm_num)
theorem B2241123 : Blo 2239435 2241123 := bstep (se 1 (by rfl) ⟨1680842, by rfl⟩ : syracuseStep 2241123 = 3361685) B3361685
theorem B12763925 : Blo 2239435 12763925 := bbase (se 6 (by rfl) ⟨299154, by rfl⟩ : syracuseStep 12763925 = 598309) (by norm_num)
theorem B8509283 : Blo 2239435 8509283 := bstep (se 1 (by rfl) ⟨6381962, by rfl⟩ : syracuseStep 8509283 = 12763925) B12763925
theorem B5672855 : Blo 2239435 5672855 := bstep (se 1 (by rfl) ⟨4254641, by rfl⟩ : syracuseStep 5672855 = 8509283) B8509283
theorem B3781903 : Blo 2239435 3781903 := bstep (se 1 (by rfl) ⟨2836427, by rfl⟩ : syracuseStep 3781903 = 5672855) B5672855
theorem B5042537 : Blo 2239435 5042537 := bstep (se 2 (by rfl) ⟨1890951, by rfl⟩ : syracuseStep 5042537 = 3781903) B3781903
theorem B3361691 : Blo 2239435 3361691 := bstep (se 1 (by rfl) ⟨2521268, by rfl⟩ : syracuseStep 3361691 = 5042537) B5042537
theorem B2241127 : Blo 2239435 2241127 := bstep (se 1 (by rfl) ⟨1680845, by rfl⟩ : syracuseStep 2241127 = 3361691) B3361691
theorem B2521273 : Blo 2239435 2521273 := bbase (se 2 (by rfl) ⟨945477, by rfl⟩ : syracuseStep 2521273 = 1890955) (by norm_num)
theorem B3361697 : Blo 2239435 3361697 := bstep (se 2 (by rfl) ⟨1260636, by rfl⟩ : syracuseStep 3361697 = 2521273) B2521273
theorem B2241131 : Blo 2239435 2241131 := bstep (se 1 (by rfl) ⟨1680848, by rfl⟩ : syracuseStep 2241131 = 3361697) B3361697
theorem B6815141 : Blo 2239435 6815141 := bbase (se 4 (by rfl) ⟨638919, by rfl⟩ : syracuseStep 6815141 = 1277839) (by norm_num)
theorem B4543427 : Blo 2239435 4543427 := bstep (se 1 (by rfl) ⟨3407570, by rfl⟩ : syracuseStep 4543427 = 6815141) B6815141
theorem B3028951 : Blo 2239435 3028951 := bstep (se 1 (by rfl) ⟨2271713, by rfl⟩ : syracuseStep 3028951 = 4543427) B4543427
theorem B4038601 : Blo 2239435 4038601 := bstep (se 2 (by rfl) ⟨1514475, by rfl⟩ : syracuseStep 4038601 = 3028951) B3028951
theorem B5384801 : Blo 2239435 5384801 := bstep (se 2 (by rfl) ⟨2019300, by rfl⟩ : syracuseStep 5384801 = 4038601) B4038601
theorem B3589867 : Blo 2239435 3589867 := bstep (se 1 (by rfl) ⟨2692400, by rfl⟩ : syracuseStep 3589867 = 5384801) B5384801
theorem B4786489 : Blo 2239435 4786489 := bstep (se 2 (by rfl) ⟨1794933, by rfl⟩ : syracuseStep 4786489 = 3589867) B3589867
theorem B6381985 : Blo 2239435 6381985 := bstep (se 2 (by rfl) ⟨2393244, by rfl⟩ : syracuseStep 6381985 = 4786489) B4786489
theorem B8509313 : Blo 2239435 8509313 := bstep (se 2 (by rfl) ⟨3190992, by rfl⟩ : syracuseStep 8509313 = 6381985) B6381985
theorem B5672875 : Blo 2239435 5672875 := bstep (se 1 (by rfl) ⟨4254656, by rfl⟩ : syracuseStep 5672875 = 8509313) B8509313
theorem B7563833 : Blo 2239435 7563833 := bstep (se 2 (by rfl) ⟨2836437, by rfl⟩ : syracuseStep 7563833 = 5672875) B5672875
theorem B5042555 : Blo 2239435 5042555 := bstep (se 1 (by rfl) ⟨3781916, by rfl⟩ : syracuseStep 5042555 = 7563833) B7563833
theorem B3361703 : Blo 2239435 3361703 := bstep (se 1 (by rfl) ⟨2521277, by rfl⟩ : syracuseStep 3361703 = 5042555) B5042555
theorem B2241135 : Blo 2239435 2241135 := bstep (se 1 (by rfl) ⟨1680851, by rfl⟩ : syracuseStep 2241135 = 3361703) B3361703
theorem B3361709 : Blo 2239435 3361709 := bbase (se 3 (by rfl) ⟨630320, by rfl⟩ : syracuseStep 3361709 = 1260641) (by norm_num)
theorem B2241139 : Blo 2239435 2241139 := bstep (se 1 (by rfl) ⟨1680854, by rfl⟩ : syracuseStep 2241139 = 3361709) B3361709
theorem B5042573 : Blo 2239435 5042573 := bbase (se 3 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 5042573 = 1890965) (by norm_num)
theorem B3361715 : Blo 2239435 3361715 := bstep (se 1 (by rfl) ⟨2521286, by rfl⟩ : syracuseStep 3361715 = 5042573) B5042573
theorem B2241143 : Blo 2239435 2241143 := bstep (se 1 (by rfl) ⟨1680857, by rfl⟩ : syracuseStep 2241143 = 3361715) B3361715
theorem B2836453 : Blo 2239435 2836453 := bbase (se 4 (by rfl) ⟨265917, by rfl⟩ : syracuseStep 2836453 = 531835) (by norm_num)
theorem B3781937 : Blo 2239435 3781937 := bstep (se 2 (by rfl) ⟨1418226, by rfl⟩ : syracuseStep 3781937 = 2836453) B2836453
theorem B2521291 : Blo 2239435 2521291 := bstep (se 1 (by rfl) ⟨1890968, by rfl⟩ : syracuseStep 2521291 = 3781937) B3781937
theorem B3361721 : Blo 2239435 3361721 := bstep (se 2 (by rfl) ⟨1260645, by rfl⟩ : syracuseStep 3361721 = 2521291) B2521291
theorem B2241147 : Blo 2239435 2241147 := bstep (se 1 (by rfl) ⟨1680860, by rfl⟩ : syracuseStep 2241147 = 3361721) B3361721
theorem B4851829 : Blo 2239435 4851829 := bbase (se 5 (by rfl) ⟨227429, by rfl⟩ : syracuseStep 4851829 = 454859) (by norm_num)
theorem B6469105 : Blo 2239435 6469105 := bstep (se 2 (by rfl) ⟨2425914, by rfl⟩ : syracuseStep 6469105 = 4851829) B4851829
theorem B8625473 : Blo 2239435 8625473 := bstep (se 2 (by rfl) ⟨3234552, by rfl⟩ : syracuseStep 8625473 = 6469105) B6469105
theorem B5750315 : Blo 2239435 5750315 := bstep (se 1 (by rfl) ⟨4312736, by rfl⟩ : syracuseStep 5750315 = 8625473) B8625473
theorem B3833543 : Blo 2239435 3833543 := bstep (se 1 (by rfl) ⟨2875157, by rfl⟩ : syracuseStep 3833543 = 5750315) B5750315
theorem B2555695 : Blo 2239435 2555695 := bstep (se 1 (by rfl) ⟨1916771, by rfl⟩ : syracuseStep 2555695 = 3833543) B3833543
theorem B13630373 : Blo 2239435 13630373 := bstep (se 4 (by rfl) ⟨1277847, by rfl⟩ : syracuseStep 13630373 = 2555695) B2555695
theorem B9086915 : Blo 2239435 9086915 := bstep (se 1 (by rfl) ⟨6815186, by rfl⟩ : syracuseStep 9086915 = 13630373) B13630373
theorem B24231773 : Blo 2239435 24231773 := bstep (se 3 (by rfl) ⟨4543457, by rfl⟩ : syracuseStep 24231773 = 9086915) B9086915
theorem B16154515 : Blo 2239435 16154515 := bstep (se 1 (by rfl) ⟨12115886, by rfl⟩ : syracuseStep 16154515 = 24231773) B24231773
theorem B21539353 : Blo 2239435 21539353 := bstep (se 2 (by rfl) ⟨8077257, by rfl⟩ : syracuseStep 21539353 = 16154515) B16154515
theorem B28719137 : Blo 2239435 28719137 := bstep (se 2 (by rfl) ⟨10769676, by rfl⟩ : syracuseStep 28719137 = 21539353) B21539353
theorem B19146091 : Blo 2239435 19146091 := bstep (se 1 (by rfl) ⟨14359568, by rfl⟩ : syracuseStep 19146091 = 28719137) B28719137
theorem B25528121 : Blo 2239435 25528121 := bstep (se 2 (by rfl) ⟨9573045, by rfl⟩ : syracuseStep 25528121 = 19146091) B19146091
theorem B17018747 : Blo 2239435 17018747 := bstep (se 1 (by rfl) ⟨12764060, by rfl⟩ : syracuseStep 17018747 = 25528121) B25528121
theorem B11345831 : Blo 2239435 11345831 := bstep (se 1 (by rfl) ⟨8509373, by rfl⟩ : syracuseStep 11345831 = 17018747) B17018747
theorem B7563887 : Blo 2239435 7563887 := bstep (se 1 (by rfl) ⟨5672915, by rfl⟩ : syracuseStep 7563887 = 11345831) B11345831
theorem B5042591 : Blo 2239435 5042591 := bstep (se 1 (by rfl) ⟨3781943, by rfl⟩ : syracuseStep 5042591 = 7563887) B7563887
theorem B3361727 : Blo 2239435 3361727 := bstep (se 1 (by rfl) ⟨2521295, by rfl⟩ : syracuseStep 3361727 = 5042591) B5042591
theorem B2241151 : Blo 2239435 2241151 := bstep (se 1 (by rfl) ⟨1680863, by rfl⟩ : syracuseStep 2241151 = 3361727) B3361727
theorem B3361733 : Blo 2239435 3361733 := bbase (se 4 (by rfl) ⟨315162, by rfl⟩ : syracuseStep 3361733 = 630325) (by norm_num)
theorem B2241155 : Blo 2239435 2241155 := bstep (se 1 (by rfl) ⟨1680866, by rfl⟩ : syracuseStep 2241155 = 3361733) B3361733
theorem B3781957 : Blo 2239435 3781957 := bbase (se 4 (by rfl) ⟨354558, by rfl⟩ : syracuseStep 3781957 = 709117) (by norm_num)
theorem B5042609 : Blo 2239435 5042609 := bstep (se 2 (by rfl) ⟨1890978, by rfl⟩ : syracuseStep 5042609 = 3781957) B3781957
theorem B3361739 : Blo 2239435 3361739 := bstep (se 1 (by rfl) ⟨2521304, by rfl⟩ : syracuseStep 3361739 = 5042609) B5042609
theorem B2241159 : Blo 2239435 2241159 := bstep (se 1 (by rfl) ⟨1680869, by rfl⟩ : syracuseStep 2241159 = 3361739) B3361739
theorem B2521309 : Blo 2239435 2521309 := bbase (se 3 (by rfl) ⟨472745, by rfl⟩ : syracuseStep 2521309 = 945491) (by norm_num)
theorem B3361745 : Blo 2239435 3361745 := bstep (se 2 (by rfl) ⟨1260654, by rfl⟩ : syracuseStep 3361745 = 2521309) B2521309
theorem B2241163 : Blo 2239435 2241163 := bstep (se 1 (by rfl) ⟨1680872, by rfl⟩ : syracuseStep 2241163 = 3361745) B3361745
theorem B7563941 : Blo 2239435 7563941 := bbase (se 4 (by rfl) ⟨709119, by rfl⟩ : syracuseStep 7563941 = 1418239) (by norm_num)
theorem B5042627 : Blo 2239435 5042627 := bstep (se 1 (by rfl) ⟨3781970, by rfl⟩ : syracuseStep 5042627 = 7563941) B7563941
theorem B3361751 : Blo 2239435 3361751 := bstep (se 1 (by rfl) ⟨2521313, by rfl⟩ : syracuseStep 3361751 = 5042627) B5042627
theorem B2241167 : Blo 2239435 2241167 := bstep (se 1 (by rfl) ⟨1680875, by rfl⟩ : syracuseStep 2241167 = 3361751) B3361751
theorem B3361757 : Blo 2239435 3361757 := bbase (se 3 (by rfl) ⟨630329, by rfl⟩ : syracuseStep 3361757 = 1260659) (by norm_num)
theorem B2241171 : Blo 2239435 2241171 := bstep (se 1 (by rfl) ⟨1680878, by rfl⟩ : syracuseStep 2241171 = 3361757) B3361757
theorem B5042645 : Blo 2239435 5042645 := bbase (se 7 (by rfl) ⟨59093, by rfl⟩ : syracuseStep 5042645 = 118187) (by norm_num)
theorem B3361763 : Blo 2239435 3361763 := bstep (se 1 (by rfl) ⟨2521322, by rfl⟩ : syracuseStep 3361763 = 5042645) B5042645
theorem B2241175 : Blo 2239435 2241175 := bstep (se 1 (by rfl) ⟨1680881, by rfl⟩ : syracuseStep 2241175 = 3361763) B3361763
theorem B2590597 : Blo 2239435 2590597 := bbase (se 4 (by rfl) ⟨242868, by rfl⟩ : syracuseStep 2590597 = 485737) (by norm_num)
theorem B3454129 : Blo 2239435 3454129 := bstep (se 2 (by rfl) ⟨1295298, by rfl⟩ : syracuseStep 3454129 = 2590597) B2590597
theorem B4605505 : Blo 2239435 4605505 := bstep (se 2 (by rfl) ⟨1727064, by rfl⟩ : syracuseStep 4605505 = 3454129) B3454129
theorem B24562693 : Blo 2239435 24562693 := bstep (se 4 (by rfl) ⟨2302752, by rfl⟩ : syracuseStep 24562693 = 4605505) B4605505
theorem B32750257 : Blo 2239435 32750257 := bstep (se 2 (by rfl) ⟨12281346, by rfl⟩ : syracuseStep 32750257 = 24562693) B24562693
theorem B43667009 : Blo 2239435 43667009 := bstep (se 2 (by rfl) ⟨16375128, by rfl⟩ : syracuseStep 43667009 = 32750257) B32750257
theorem B29111339 : Blo 2239435 29111339 := bstep (se 1 (by rfl) ⟨21833504, by rfl⟩ : syracuseStep 29111339 = 43667009) B43667009
theorem B19407559 : Blo 2239435 19407559 := bstep (se 1 (by rfl) ⟨14555669, by rfl⟩ : syracuseStep 19407559 = 29111339) B29111339
theorem B25876745 : Blo 2239435 25876745 := bstep (se 2 (by rfl) ⟨9703779, by rfl⟩ : syracuseStep 25876745 = 19407559) B19407559
theorem B17251163 : Blo 2239435 17251163 := bstep (se 1 (by rfl) ⟨12938372, by rfl⟩ : syracuseStep 17251163 = 25876745) B25876745
theorem B11500775 : Blo 2239435 11500775 := bstep (se 1 (by rfl) ⟨8625581, by rfl⟩ : syracuseStep 11500775 = 17251163) B17251163
theorem B7667183 : Blo 2239435 7667183 := bstep (se 1 (by rfl) ⟨5750387, by rfl⟩ : syracuseStep 7667183 = 11500775) B11500775
theorem B5111455 : Blo 2239435 5111455 := bstep (se 1 (by rfl) ⟨3833591, by rfl⟩ : syracuseStep 5111455 = 7667183) B7667183
theorem B6815273 : Blo 2239435 6815273 := bstep (se 2 (by rfl) ⟨2555727, by rfl⟩ : syracuseStep 6815273 = 5111455) B5111455
theorem B18174061 : Blo 2239435 18174061 := bstep (se 3 (by rfl) ⟨3407636, by rfl⟩ : syracuseStep 18174061 = 6815273) B6815273
theorem B24232081 : Blo 2239435 24232081 := bstep (se 2 (by rfl) ⟨9087030, by rfl⟩ : syracuseStep 24232081 = 18174061) B18174061
theorem B32309441 : Blo 2239435 32309441 := bstep (se 2 (by rfl) ⟨12116040, by rfl⟩ : syracuseStep 32309441 = 24232081) B24232081
theorem B21539627 : Blo 2239435 21539627 := bstep (se 1 (by rfl) ⟨16154720, by rfl⟩ : syracuseStep 21539627 = 32309441) B32309441
theorem B14359751 : Blo 2239435 14359751 := bstep (se 1 (by rfl) ⟨10769813, by rfl⟩ : syracuseStep 14359751 = 21539627) B21539627
theorem B9573167 : Blo 2239435 9573167 := bstep (se 1 (by rfl) ⟨7179875, by rfl⟩ : syracuseStep 9573167 = 14359751) B14359751
theorem B6382111 : Blo 2239435 6382111 := bstep (se 1 (by rfl) ⟨4786583, by rfl⟩ : syracuseStep 6382111 = 9573167) B9573167
theorem B8509481 : Blo 2239435 8509481 := bstep (se 2 (by rfl) ⟨3191055, by rfl⟩ : syracuseStep 8509481 = 6382111) B6382111
theorem B5672987 : Blo 2239435 5672987 := bstep (se 1 (by rfl) ⟨4254740, by rfl⟩ : syracuseStep 5672987 = 8509481) B8509481
theorem B3781991 : Blo 2239435 3781991 := bstep (se 1 (by rfl) ⟨2836493, by rfl⟩ : syracuseStep 3781991 = 5672987) B5672987
theorem B2521327 : Blo 2239435 2521327 := bstep (se 1 (by rfl) ⟨1890995, by rfl⟩ : syracuseStep 2521327 = 3781991) B3781991
theorem B3361769 : Blo 2239435 3361769 := bstep (se 2 (by rfl) ⟨1260663, by rfl⟩ : syracuseStep 3361769 = 2521327) B2521327
theorem B2241179 : Blo 2239435 2241179 := bstep (se 1 (by rfl) ⟨1680884, by rfl⟩ : syracuseStep 2241179 = 3361769) B3361769
theorem B4093789 : Blo 2239435 4093789 := bbase (se 3 (by rfl) ⟨767585, by rfl⟩ : syracuseStep 4093789 = 1535171) (by norm_num)
theorem B5458385 : Blo 2239435 5458385 := bstep (se 2 (by rfl) ⟨2046894, by rfl⟩ : syracuseStep 5458385 = 4093789) B4093789
theorem B14555693 : Blo 2239435 14555693 := bstep (se 3 (by rfl) ⟨2729192, by rfl⟩ : syracuseStep 14555693 = 5458385) B5458385
theorem B9703795 : Blo 2239435 9703795 := bstep (se 1 (by rfl) ⟨7277846, by rfl⟩ : syracuseStep 9703795 = 14555693) B14555693
theorem B12938393 : Blo 2239435 12938393 := bstep (se 2 (by rfl) ⟨4851897, by rfl⟩ : syracuseStep 12938393 = 9703795) B9703795
theorem B8625595 : Blo 2239435 8625595 := bstep (se 1 (by rfl) ⟨6469196, by rfl⟩ : syracuseStep 8625595 = 12938393) B12938393
theorem B11500793 : Blo 2239435 11500793 := bstep (se 2 (by rfl) ⟨4312797, by rfl⟩ : syracuseStep 11500793 = 8625595) B8625595
theorem B7667195 : Blo 2239435 7667195 := bstep (se 1 (by rfl) ⟨5750396, by rfl⟩ : syracuseStep 7667195 = 11500793) B11500793
theorem B20445853 : Blo 2239435 20445853 := bstep (se 3 (by rfl) ⟨3833597, by rfl⟩ : syracuseStep 20445853 = 7667195) B7667195
theorem B27261137 : Blo 2239435 27261137 := bstep (se 2 (by rfl) ⟨10222926, by rfl⟩ : syracuseStep 27261137 = 20445853) B20445853
theorem B18174091 : Blo 2239435 18174091 := bstep (se 1 (by rfl) ⟨13630568, by rfl⟩ : syracuseStep 18174091 = 27261137) B27261137
theorem B24232121 : Blo 2239435 24232121 := bstep (se 2 (by rfl) ⟨9087045, by rfl⟩ : syracuseStep 24232121 = 18174091) B18174091
theorem B16154747 : Blo 2239435 16154747 := bstep (se 1 (by rfl) ⟨12116060, by rfl⟩ : syracuseStep 16154747 = 24232121) B24232121
theorem B10769831 : Blo 2239435 10769831 := bstep (se 1 (by rfl) ⟨8077373, by rfl⟩ : syracuseStep 10769831 = 16154747) B16154747
theorem B7179887 : Blo 2239435 7179887 := bstep (se 1 (by rfl) ⟨5384915, by rfl⟩ : syracuseStep 7179887 = 10769831) B10769831
theorem B19146365 : Blo 2239435 19146365 := bstep (se 3 (by rfl) ⟨3589943, by rfl⟩ : syracuseStep 19146365 = 7179887) B7179887
theorem B12764243 : Blo 2239435 12764243 := bstep (se 1 (by rfl) ⟨9573182, by rfl⟩ : syracuseStep 12764243 = 19146365) B19146365
theorem B8509495 : Blo 2239435 8509495 := bstep (se 1 (by rfl) ⟨6382121, by rfl⟩ : syracuseStep 8509495 = 12764243) B12764243
theorem B11345993 : Blo 2239435 11345993 := bstep (se 2 (by rfl) ⟨4254747, by rfl⟩ : syracuseStep 11345993 = 8509495) B8509495
theorem B7563995 : Blo 2239435 7563995 := bstep (se 1 (by rfl) ⟨5672996, by rfl⟩ : syracuseStep 7563995 = 11345993) B11345993
theorem B5042663 : Blo 2239435 5042663 := bstep (se 1 (by rfl) ⟨3781997, by rfl⟩ : syracuseStep 5042663 = 7563995) B7563995
theorem B3361775 : Blo 2239435 3361775 := bstep (se 1 (by rfl) ⟨2521331, by rfl⟩ : syracuseStep 3361775 = 5042663) B5042663
theorem B2241183 : Blo 2239435 2241183 := bstep (se 1 (by rfl) ⟨1680887, by rfl⟩ : syracuseStep 2241183 = 3361775) B3361775
theorem B3361781 : Blo 2239435 3361781 := bbase (se 5 (by rfl) ⟨157583, by rfl⟩ : syracuseStep 3361781 = 315167) (by norm_num)
theorem B2241187 : Blo 2239435 2241187 := bstep (se 1 (by rfl) ⟨1680890, by rfl⟩ : syracuseStep 2241187 = 3361781) B3361781
theorem B3589957 : Blo 2239435 3589957 := bbase (se 4 (by rfl) ⟨336558, by rfl⟩ : syracuseStep 3589957 = 673117) (by norm_num)
theorem B4786609 : Blo 2239435 4786609 := bstep (se 2 (by rfl) ⟨1794978, by rfl⟩ : syracuseStep 4786609 = 3589957) B3589957
theorem B6382145 : Blo 2239435 6382145 := bstep (se 2 (by rfl) ⟨2393304, by rfl⟩ : syracuseStep 6382145 = 4786609) B4786609
theorem B4254763 : Blo 2239435 4254763 := bstep (se 1 (by rfl) ⟨3191072, by rfl⟩ : syracuseStep 4254763 = 6382145) B6382145
theorem B5673017 : Blo 2239435 5673017 := bstep (se 2 (by rfl) ⟨2127381, by rfl⟩ : syracuseStep 5673017 = 4254763) B4254763
theorem B3782011 : Blo 2239435 3782011 := bstep (se 1 (by rfl) ⟨2836508, by rfl⟩ : syracuseStep 3782011 = 5673017) B5673017
theorem B5042681 : Blo 2239435 5042681 := bstep (se 2 (by rfl) ⟨1891005, by rfl⟩ : syracuseStep 5042681 = 3782011) B3782011
theorem B3361787 : Blo 2239435 3361787 := bstep (se 1 (by rfl) ⟨2521340, by rfl⟩ : syracuseStep 3361787 = 5042681) B5042681
theorem B2241191 : Blo 2239435 2241191 := bstep (se 1 (by rfl) ⟨1680893, by rfl⟩ : syracuseStep 2241191 = 3361787) B3361787
theorem B2521345 : Blo 2239435 2521345 := bbase (se 2 (by rfl) ⟨945504, by rfl⟩ : syracuseStep 2521345 = 1891009) (by norm_num)
theorem B3361793 : Blo 2239435 3361793 := bstep (se 2 (by rfl) ⟨1260672, by rfl⟩ : syracuseStep 3361793 = 2521345) B2521345
theorem B2241195 : Blo 2239435 2241195 := bstep (se 1 (by rfl) ⟨1680896, by rfl⟩ : syracuseStep 2241195 = 3361793) B3361793
theorem B5673037 : Blo 2239435 5673037 := bbase (se 3 (by rfl) ⟨1063694, by rfl⟩ : syracuseStep 5673037 = 2127389) (by norm_num)
theorem B7564049 : Blo 2239435 7564049 := bstep (se 2 (by rfl) ⟨2836518, by rfl⟩ : syracuseStep 7564049 = 5673037) B5673037
theorem B5042699 : Blo 2239435 5042699 := bstep (se 1 (by rfl) ⟨3782024, by rfl⟩ : syracuseStep 5042699 = 7564049) B7564049
theorem B3361799 : Blo 2239435 3361799 := bstep (se 1 (by rfl) ⟨2521349, by rfl⟩ : syracuseStep 3361799 = 5042699) B5042699
theorem B2241199 : Blo 2239435 2241199 := bstep (se 1 (by rfl) ⟨1680899, by rfl⟩ : syracuseStep 2241199 = 3361799) B3361799
theorem B3361805 : Blo 2239435 3361805 := bbase (se 3 (by rfl) ⟨630338, by rfl⟩ : syracuseStep 3361805 = 1260677) (by norm_num)
theorem B2241203 : Blo 2239435 2241203 := bstep (se 1 (by rfl) ⟨1680902, by rfl⟩ : syracuseStep 2241203 = 3361805) B3361805
theorem B5042717 : Blo 2239435 5042717 := bbase (se 3 (by rfl) ⟨945509, by rfl⟩ : syracuseStep 5042717 = 1891019) (by norm_num)
theorem B3361811 : Blo 2239435 3361811 := bstep (se 1 (by rfl) ⟨2521358, by rfl⟩ : syracuseStep 3361811 = 5042717) B5042717
theorem B2241207 : Blo 2239435 2241207 := bstep (se 1 (by rfl) ⟨1680905, by rfl⟩ : syracuseStep 2241207 = 3361811) B3361811
theorem B3782045 : Blo 2239435 3782045 := bbase (se 3 (by rfl) ⟨709133, by rfl⟩ : syracuseStep 3782045 = 1418267) (by norm_num)
theorem B2521363 : Blo 2239435 2521363 := bstep (se 1 (by rfl) ⟨1891022, by rfl⟩ : syracuseStep 2521363 = 3782045) B3782045
theorem B3361817 : Blo 2239435 3361817 := bstep (se 2 (by rfl) ⟨1260681, by rfl⟩ : syracuseStep 3361817 = 2521363) B2521363
theorem B2241211 : Blo 2239435 2241211 := bstep (se 1 (by rfl) ⟨1680908, by rfl⟩ : syracuseStep 2241211 = 3361817) B3361817
theorem B15543829 : Blo 2239435 15543829 := bbase (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) (by norm_num)
theorem B82900421 : Blo 2239435 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B55266947 : Blo 2239435 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B36844631 : Blo 2239435 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B24563087 : Blo 2239435 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B16375391 : Blo 2239435 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B10916927 : Blo 2239435 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B7277951 : Blo 2239435 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B4851967 : Blo 2239435 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B6469289 : Blo 2239435 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B4312859 : Blo 2239435 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B11500957 : Blo 2239435 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B15334609 : Blo 2239435 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B20446145 : Blo 2239435 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B13630763 : Blo 2239435 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B9087175 : Blo 2239435 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B12116233 : Blo 2239435 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B16154977 : Blo 2239435 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B21539969 : Blo 2239435 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B14359979 : Blo 2239435 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B9573319 : Blo 2239435 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B12764425 : Blo 2239435 12764425 := bstep (se 2 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 12764425 = 9573319) B9573319
theorem B17019233 : Blo 2239435 17019233 := bstep (se 2 (by rfl) ⟨6382212, by rfl⟩ : syracuseStep 17019233 = 12764425) B12764425
theorem B11346155 : Blo 2239435 11346155 := bstep (se 1 (by rfl) ⟨8509616, by rfl⟩ : syracuseStep 11346155 = 17019233) B17019233
theorem B7564103 : Blo 2239435 7564103 := bstep (se 1 (by rfl) ⟨5673077, by rfl⟩ : syracuseStep 7564103 = 11346155) B11346155
theorem B5042735 : Blo 2239435 5042735 := bstep (se 1 (by rfl) ⟨3782051, by rfl⟩ : syracuseStep 5042735 = 7564103) B7564103
theorem B3361823 : Blo 2239435 3361823 := bstep (se 1 (by rfl) ⟨2521367, by rfl⟩ : syracuseStep 3361823 = 5042735) B5042735
theorem B2241215 : Blo 2239435 2241215 := bstep (se 1 (by rfl) ⟨1680911, by rfl⟩ : syracuseStep 2241215 = 3361823) B3361823
theorem B3361829 : Blo 2239435 3361829 := bbase (se 4 (by rfl) ⟨315171, by rfl⟩ : syracuseStep 3361829 = 630343) (by norm_num)
theorem B2241219 : Blo 2239435 2241219 := bstep (se 1 (by rfl) ⟨1680914, by rfl⟩ : syracuseStep 2241219 = 3361829) B3361829
theorem B2836549 : Blo 2239435 2836549 := bbase (se 4 (by rfl) ⟨265926, by rfl⟩ : syracuseStep 2836549 = 531853) (by norm_num)
theorem B3782065 : Blo 2239435 3782065 := bstep (se 2 (by rfl) ⟨1418274, by rfl⟩ : syracuseStep 3782065 = 2836549) B2836549
theorem B5042753 : Blo 2239435 5042753 := bstep (se 2 (by rfl) ⟨1891032, by rfl⟩ : syracuseStep 5042753 = 3782065) B3782065
theorem B3361835 : Blo 2239435 3361835 := bstep (se 1 (by rfl) ⟨2521376, by rfl⟩ : syracuseStep 3361835 = 5042753) B5042753
theorem B2241223 : Blo 2239435 2241223 := bstep (se 1 (by rfl) ⟨1680917, by rfl⟩ : syracuseStep 2241223 = 3361835) B3361835
theorem B2521381 : Blo 2239435 2521381 := bbase (se 4 (by rfl) ⟨236379, by rfl⟩ : syracuseStep 2521381 = 472759) (by norm_num)
theorem B3361841 : Blo 2239435 3361841 := bstep (se 2 (by rfl) ⟨1260690, by rfl⟩ : syracuseStep 3361841 = 2521381) B2521381
theorem B2241227 : Blo 2239435 2241227 := bstep (se 1 (by rfl) ⟨1680920, by rfl⟩ : syracuseStep 2241227 = 3361841) B3361841
theorem B3590021 : Blo 2239435 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B9573389 : Blo 2239435 9573389 := bstep (se 3 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 9573389 = 3590021) B3590021
theorem B6382259 : Blo 2239435 6382259 := bstep (se 1 (by rfl) ⟨4786694, by rfl⟩ : syracuseStep 6382259 = 9573389) B9573389
theorem B4254839 : Blo 2239435 4254839 := bstep (se 1 (by rfl) ⟨3191129, by rfl⟩ : syracuseStep 4254839 = 6382259) B6382259
theorem B2836559 : Blo 2239435 2836559 := bstep (se 1 (by rfl) ⟨2127419, by rfl⟩ : syracuseStep 2836559 = 4254839) B4254839
theorem B7564157 : Blo 2239435 7564157 := bstep (se 3 (by rfl) ⟨1418279, by rfl⟩ : syracuseStep 7564157 = 2836559) B2836559
theorem B5042771 : Blo 2239435 5042771 := bstep (se 1 (by rfl) ⟨3782078, by rfl⟩ : syracuseStep 5042771 = 7564157) B7564157
theorem B3361847 : Blo 2239435 3361847 := bstep (se 1 (by rfl) ⟨2521385, by rfl⟩ : syracuseStep 3361847 = 5042771) B5042771
theorem B2241231 : Blo 2239435 2241231 := bstep (se 1 (by rfl) ⟨1680923, by rfl⟩ : syracuseStep 2241231 = 3361847) B3361847
theorem B3361853 : Blo 2239435 3361853 := bbase (se 3 (by rfl) ⟨630347, by rfl⟩ : syracuseStep 3361853 = 1260695) (by norm_num)
theorem B2241235 : Blo 2239435 2241235 := bstep (se 1 (by rfl) ⟨1680926, by rfl⟩ : syracuseStep 2241235 = 3361853) B3361853
theorem B5042789 : Blo 2239435 5042789 := bbase (se 4 (by rfl) ⟨472761, by rfl⟩ : syracuseStep 5042789 = 945523) (by norm_num)
theorem B3361859 : Blo 2239435 3361859 := bstep (se 1 (by rfl) ⟨2521394, by rfl⟩ : syracuseStep 3361859 = 5042789) B5042789
theorem B2241239 : Blo 2239435 2241239 := bstep (se 1 (by rfl) ⟨1680929, by rfl⟩ : syracuseStep 2241239 = 3361859) B3361859
theorem B5673149 : Blo 2239435 5673149 := bbase (se 3 (by rfl) ⟨1063715, by rfl⟩ : syracuseStep 5673149 = 2127431) (by norm_num)
theorem B3782099 : Blo 2239435 3782099 := bstep (se 1 (by rfl) ⟨2836574, by rfl⟩ : syracuseStep 3782099 = 5673149) B5673149
theorem B2521399 : Blo 2239435 2521399 := bstep (se 1 (by rfl) ⟨1891049, by rfl⟩ : syracuseStep 2521399 = 3782099) B3782099
theorem B3361865 : Blo 2239435 3361865 := bstep (se 2 (by rfl) ⟨1260699, by rfl⟩ : syracuseStep 3361865 = 2521399) B2521399
theorem B2241243 : Blo 2239435 2241243 := bstep (se 1 (by rfl) ⟨1680932, by rfl⟩ : syracuseStep 2241243 = 3361865) B3361865
theorem B4254869 : Blo 2239435 4254869 := bbase (se 6 (by rfl) ⟨99723, by rfl⟩ : syracuseStep 4254869 = 199447) (by norm_num)
theorem B11346317 : Blo 2239435 11346317 := bstep (se 3 (by rfl) ⟨2127434, by rfl⟩ : syracuseStep 11346317 = 4254869) B4254869
theorem B7564211 : Blo 2239435 7564211 := bstep (se 1 (by rfl) ⟨5673158, by rfl⟩ : syracuseStep 7564211 = 11346317) B11346317
theorem B5042807 : Blo 2239435 5042807 := bstep (se 1 (by rfl) ⟨3782105, by rfl⟩ : syracuseStep 5042807 = 7564211) B7564211
theorem B3361871 : Blo 2239435 3361871 := bstep (se 1 (by rfl) ⟨2521403, by rfl⟩ : syracuseStep 3361871 = 5042807) B5042807
theorem B2241247 : Blo 2239435 2241247 := bstep (se 1 (by rfl) ⟨1680935, by rfl⟩ : syracuseStep 2241247 = 3361871) B3361871
theorem B3361877 : Blo 2239435 3361877 := bbase (se 8 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 3361877 = 39397) (by norm_num)
theorem B2241251 : Blo 2239435 2241251 := bstep (se 1 (by rfl) ⟨1680938, by rfl⟩ : syracuseStep 2241251 = 3361877) B3361877
theorem B5458565 : Blo 2239435 5458565 := bbase (se 4 (by rfl) ⟨511740, by rfl⟩ : syracuseStep 5458565 = 1023481) (by norm_num)
theorem B3639043 : Blo 2239435 3639043 := bstep (se 1 (by rfl) ⟨2729282, by rfl⟩ : syracuseStep 3639043 = 5458565) B5458565
theorem B4852057 : Blo 2239435 4852057 := bstep (se 2 (by rfl) ⟨1819521, by rfl⟩ : syracuseStep 4852057 = 3639043) B3639043
theorem B6469409 : Blo 2239435 6469409 := bstep (se 2 (by rfl) ⟨2426028, by rfl⟩ : syracuseStep 6469409 = 4852057) B4852057
theorem B4312939 : Blo 2239435 4312939 := bstep (se 1 (by rfl) ⟨3234704, by rfl⟩ : syracuseStep 4312939 = 6469409) B6469409
theorem B5750585 : Blo 2239435 5750585 := bstep (se 2 (by rfl) ⟨2156469, by rfl⟩ : syracuseStep 5750585 = 4312939) B4312939
theorem B3833723 : Blo 2239435 3833723 := bstep (se 1 (by rfl) ⟨2875292, by rfl⟩ : syracuseStep 3833723 = 5750585) B5750585
theorem B2555815 : Blo 2239435 2555815 := bstep (se 1 (by rfl) ⟨1916861, by rfl⟩ : syracuseStep 2555815 = 3833723) B3833723
theorem B3407753 : Blo 2239435 3407753 := bstep (se 2 (by rfl) ⟨1277907, by rfl⟩ : syracuseStep 3407753 = 2555815) B2555815
theorem B2271835 : Blo 2239435 2271835 := bstep (se 1 (by rfl) ⟨1703876, by rfl⟩ : syracuseStep 2271835 = 3407753) B3407753
theorem B3029113 : Blo 2239435 3029113 := bstep (se 2 (by rfl) ⟨1135917, by rfl⟩ : syracuseStep 3029113 = 2271835) B2271835
theorem B4038817 : Blo 2239435 4038817 := bstep (se 2 (by rfl) ⟨1514556, by rfl⟩ : syracuseStep 4038817 = 3029113) B3029113
theorem B5385089 : Blo 2239435 5385089 := bstep (se 2 (by rfl) ⟨2019408, by rfl⟩ : syracuseStep 5385089 = 4038817) B4038817
theorem B14360237 : Blo 2239435 14360237 := bstep (se 3 (by rfl) ⟨2692544, by rfl⟩ : syracuseStep 14360237 = 5385089) B5385089
theorem B9573491 : Blo 2239435 9573491 := bstep (se 1 (by rfl) ⟨7180118, by rfl⟩ : syracuseStep 9573491 = 14360237) B14360237
theorem B6382327 : Blo 2239435 6382327 := bstep (se 1 (by rfl) ⟨4786745, by rfl⟩ : syracuseStep 6382327 = 9573491) B9573491
theorem B8509769 : Blo 2239435 8509769 := bstep (se 2 (by rfl) ⟨3191163, by rfl⟩ : syracuseStep 8509769 = 6382327) B6382327
theorem B5673179 : Blo 2239435 5673179 := bstep (se 1 (by rfl) ⟨4254884, by rfl⟩ : syracuseStep 5673179 = 8509769) B8509769
theorem B3782119 : Blo 2239435 3782119 := bstep (se 1 (by rfl) ⟨2836589, by rfl⟩ : syracuseStep 3782119 = 5673179) B5673179
theorem B5042825 : Blo 2239435 5042825 := bstep (se 2 (by rfl) ⟨1891059, by rfl⟩ : syracuseStep 5042825 = 3782119) B3782119
theorem B3361883 : Blo 2239435 3361883 := bstep (se 1 (by rfl) ⟨2521412, by rfl⟩ : syracuseStep 3361883 = 5042825) B5042825
theorem B2241255 : Blo 2239435 2241255 := bstep (se 1 (by rfl) ⟨1680941, by rfl⟩ : syracuseStep 2241255 = 3361883) B3361883
theorem B2521417 : Blo 2239435 2521417 := bbase (se 2 (by rfl) ⟨945531, by rfl⟩ : syracuseStep 2521417 = 1891063) (by norm_num)
theorem B3361889 : Blo 2239435 3361889 := bstep (se 2 (by rfl) ⟨1260708, by rfl⟩ : syracuseStep 3361889 = 2521417) B2521417
theorem B2241259 : Blo 2239435 2241259 := bstep (se 1 (by rfl) ⟨1680944, by rfl⟩ : syracuseStep 2241259 = 3361889) B3361889
theorem B3639053 : Blo 2239435 3639053 := bbase (se 3 (by rfl) ⟨682322, by rfl⟩ : syracuseStep 3639053 = 1364645) (by norm_num)
theorem B9704141 : Blo 2239435 9704141 := bstep (se 3 (by rfl) ⟨1819526, by rfl⟩ : syracuseStep 9704141 = 3639053) B3639053
theorem B6469427 : Blo 2239435 6469427 := bstep (se 1 (by rfl) ⟨4852070, by rfl⟩ : syracuseStep 6469427 = 9704141) B9704141
theorem B17251805 : Blo 2239435 17251805 := bstep (se 3 (by rfl) ⟨3234713, by rfl⟩ : syracuseStep 17251805 = 6469427) B6469427
theorem B11501203 : Blo 2239435 11501203 := bstep (se 1 (by rfl) ⟨8625902, by rfl⟩ : syracuseStep 11501203 = 17251805) B17251805
theorem B15334937 : Blo 2239435 15334937 := bstep (se 2 (by rfl) ⟨5750601, by rfl⟩ : syracuseStep 15334937 = 11501203) B11501203
theorem B10223291 : Blo 2239435 10223291 := bstep (se 1 (by rfl) ⟨7667468, by rfl⟩ : syracuseStep 10223291 = 15334937) B15334937
theorem B27262109 : Blo 2239435 27262109 := bstep (se 3 (by rfl) ⟨5111645, by rfl⟩ : syracuseStep 27262109 = 10223291) B10223291
theorem B72698957 : Blo 2239435 72698957 := bstep (se 3 (by rfl) ⟨13631054, by rfl⟩ : syracuseStep 72698957 = 27262109) B27262109
theorem B48465971 : Blo 2239435 48465971 := bstep (se 1 (by rfl) ⟨36349478, by rfl⟩ : syracuseStep 48465971 = 72698957) B72698957
theorem B32310647 : Blo 2239435 32310647 := bstep (se 1 (by rfl) ⟨24232985, by rfl⟩ : syracuseStep 32310647 = 48465971) B48465971
theorem B21540431 : Blo 2239435 21540431 := bstep (se 1 (by rfl) ⟨16155323, by rfl⟩ : syracuseStep 21540431 = 32310647) B32310647
theorem B14360287 : Blo 2239435 14360287 := bstep (se 1 (by rfl) ⟨10770215, by rfl⟩ : syracuseStep 14360287 = 21540431) B21540431
theorem B19147049 : Blo 2239435 19147049 := bstep (se 2 (by rfl) ⟨7180143, by rfl⟩ : syracuseStep 19147049 = 14360287) B14360287
theorem B12764699 : Blo 2239435 12764699 := bstep (se 1 (by rfl) ⟨9573524, by rfl⟩ : syracuseStep 12764699 = 19147049) B19147049
theorem B8509799 : Blo 2239435 8509799 := bstep (se 1 (by rfl) ⟨6382349, by rfl⟩ : syracuseStep 8509799 = 12764699) B12764699
theorem B5673199 : Blo 2239435 5673199 := bstep (se 1 (by rfl) ⟨4254899, by rfl⟩ : syracuseStep 5673199 = 8509799) B8509799
theorem B7564265 : Blo 2239435 7564265 := bstep (se 2 (by rfl) ⟨2836599, by rfl⟩ : syracuseStep 7564265 = 5673199) B5673199
theorem B5042843 : Blo 2239435 5042843 := bstep (se 1 (by rfl) ⟨3782132, by rfl⟩ : syracuseStep 5042843 = 7564265) B7564265
theorem B3361895 : Blo 2239435 3361895 := bstep (se 1 (by rfl) ⟨2521421, by rfl⟩ : syracuseStep 3361895 = 5042843) B5042843
theorem B2241263 : Blo 2239435 2241263 := bstep (se 1 (by rfl) ⟨1680947, by rfl⟩ : syracuseStep 2241263 = 3361895) B3361895
theorem B3361901 : Blo 2239435 3361901 := bbase (se 3 (by rfl) ⟨630356, by rfl⟩ : syracuseStep 3361901 = 1260713) (by norm_num)
theorem B2241267 : Blo 2239435 2241267 := bstep (se 1 (by rfl) ⟨1680950, by rfl⟩ : syracuseStep 2241267 = 3361901) B3361901
theorem B5042861 : Blo 2239435 5042861 := bbase (se 3 (by rfl) ⟨945536, by rfl⟩ : syracuseStep 5042861 = 1891073) (by norm_num)
theorem B3361907 : Blo 2239435 3361907 := bstep (se 1 (by rfl) ⟨2521430, by rfl⟩ : syracuseStep 3361907 = 5042861) B5042861
theorem B2241271 : Blo 2239435 2241271 := bstep (se 1 (by rfl) ⟨1680953, by rfl⟩ : syracuseStep 2241271 = 3361907) B3361907
theorem B4786789 : Blo 2239435 4786789 := bbase (se 4 (by rfl) ⟨448761, by rfl⟩ : syracuseStep 4786789 = 897523) (by norm_num)
theorem B6382385 : Blo 2239435 6382385 := bstep (se 2 (by rfl) ⟨2393394, by rfl⟩ : syracuseStep 6382385 = 4786789) B4786789
theorem B4254923 : Blo 2239435 4254923 := bstep (se 1 (by rfl) ⟨3191192, by rfl⟩ : syracuseStep 4254923 = 6382385) B6382385
theorem B2836615 : Blo 2239435 2836615 := bstep (se 1 (by rfl) ⟨2127461, by rfl⟩ : syracuseStep 2836615 = 4254923) B4254923
theorem B3782153 : Blo 2239435 3782153 := bstep (se 2 (by rfl) ⟨1418307, by rfl⟩ : syracuseStep 3782153 = 2836615) B2836615
theorem B2521435 : Blo 2239435 2521435 := bstep (se 1 (by rfl) ⟨1891076, by rfl⟩ : syracuseStep 2521435 = 3782153) B3782153
theorem B3361913 : Blo 2239435 3361913 := bstep (se 2 (by rfl) ⟨1260717, by rfl⟩ : syracuseStep 3361913 = 2521435) B2521435
theorem B2241275 : Blo 2239435 2241275 := bstep (se 1 (by rfl) ⟨1680956, by rfl⟩ : syracuseStep 2241275 = 3361913) B3361913
theorem B4605709 : Blo 2239435 4605709 := bbase (se 3 (by rfl) ⟨863570, by rfl⟩ : syracuseStep 4605709 = 1727141) (by norm_num)
theorem B6140945 : Blo 2239435 6140945 := bstep (se 2 (by rfl) ⟨2302854, by rfl⟩ : syracuseStep 6140945 = 4605709) B4605709
theorem B4093963 : Blo 2239435 4093963 := bstep (se 1 (by rfl) ⟨3070472, by rfl⟩ : syracuseStep 4093963 = 6140945) B6140945
theorem B21834469 : Blo 2239435 21834469 := bstep (se 4 (by rfl) ⟨2046981, by rfl⟩ : syracuseStep 21834469 = 4093963) B4093963
theorem B29112625 : Blo 2239435 29112625 := bstep (se 2 (by rfl) ⟨10917234, by rfl⟩ : syracuseStep 29112625 = 21834469) B21834469
theorem B38816833 : Blo 2239435 38816833 := bstep (se 2 (by rfl) ⟨14556312, by rfl⟩ : syracuseStep 38816833 = 29112625) B29112625
theorem B51755777 : Blo 2239435 51755777 := bstep (se 2 (by rfl) ⟨19408416, by rfl⟩ : syracuseStep 51755777 = 38816833) B38816833
theorem B34503851 : Blo 2239435 34503851 := bstep (se 1 (by rfl) ⟨25877888, by rfl⟩ : syracuseStep 34503851 = 51755777) B51755777
theorem B92010269 : Blo 2239435 92010269 := bstep (se 3 (by rfl) ⟨17251925, by rfl⟩ : syracuseStep 92010269 = 34503851) B34503851
theorem B61340179 : Blo 2239435 61340179 := bstep (se 1 (by rfl) ⟨46005134, by rfl⟩ : syracuseStep 61340179 = 92010269) B92010269
theorem B81786905 : Blo 2239435 81786905 := bstep (se 2 (by rfl) ⟨30670089, by rfl⟩ : syracuseStep 81786905 = 61340179) B61340179
theorem B54524603 : Blo 2239435 54524603 := bstep (se 1 (by rfl) ⟨40893452, by rfl⟩ : syracuseStep 54524603 = 81786905) B81786905
theorem B36349735 : Blo 2239435 36349735 := bstep (se 1 (by rfl) ⟨27262301, by rfl⟩ : syracuseStep 36349735 = 54524603) B54524603
theorem B48466313 : Blo 2239435 48466313 := bstep (se 2 (by rfl) ⟨18174867, by rfl⟩ : syracuseStep 48466313 = 36349735) B36349735
theorem B32310875 : Blo 2239435 32310875 := bstep (se 1 (by rfl) ⟨24233156, by rfl⟩ : syracuseStep 32310875 = 48466313) B48466313
theorem B21540583 : Blo 2239435 21540583 := bstep (se 1 (by rfl) ⟨16155437, by rfl⟩ : syracuseStep 21540583 = 32310875) B32310875
theorem B28720777 : Blo 2239435 28720777 := bstep (se 2 (by rfl) ⟨10770291, by rfl⟩ : syracuseStep 28720777 = 21540583) B21540583
theorem B38294369 : Blo 2239435 38294369 := bstep (se 2 (by rfl) ⟨14360388, by rfl⟩ : syracuseStep 38294369 = 28720777) B28720777
theorem B25529579 : Blo 2239435 25529579 := bstep (se 1 (by rfl) ⟨19147184, by rfl⟩ : syracuseStep 25529579 = 38294369) B38294369
theorem B17019719 : Blo 2239435 17019719 := bstep (se 1 (by rfl) ⟨12764789, by rfl⟩ : syracuseStep 17019719 = 25529579) B25529579
theorem B11346479 : Blo 2239435 11346479 := bstep (se 1 (by rfl) ⟨8509859, by rfl⟩ : syracuseStep 11346479 = 17019719) B17019719
theorem B7564319 : Blo 2239435 7564319 := bstep (se 1 (by rfl) ⟨5673239, by rfl⟩ : syracuseStep 7564319 = 11346479) B11346479
theorem B5042879 : Blo 2239435 5042879 := bstep (se 1 (by rfl) ⟨3782159, by rfl⟩ : syracuseStep 5042879 = 7564319) B7564319
theorem B3361919 : Blo 2239435 3361919 := bstep (se 1 (by rfl) ⟨2521439, by rfl⟩ : syracuseStep 3361919 = 5042879) B5042879
theorem B2241279 : Blo 2239435 2241279 := bstep (se 1 (by rfl) ⟨1680959, by rfl⟩ : syracuseStep 2241279 = 3361919) B3361919
theorem B3361925 : Blo 2239435 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B2241283 : Blo 2239435 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B3782173 : Blo 2239435 3782173 := bbase (se 3 (by rfl) ⟨709157, by rfl⟩ : syracuseStep 3782173 = 1418315) (by norm_num)
theorem B5042897 : Blo 2239435 5042897 := bstep (se 2 (by rfl) ⟨1891086, by rfl⟩ : syracuseStep 5042897 = 3782173) B3782173
theorem B3361931 : Blo 2239435 3361931 := bstep (se 1 (by rfl) ⟨2521448, by rfl⟩ : syracuseStep 3361931 = 5042897) B5042897
theorem B2241287 : Blo 2239435 2241287 := bstep (se 1 (by rfl) ⟨1680965, by rfl⟩ : syracuseStep 2241287 = 3361931) B3361931
theorem B2521453 : Blo 2239435 2521453 := bbase (se 3 (by rfl) ⟨472772, by rfl⟩ : syracuseStep 2521453 = 945545) (by norm_num)
theorem B3361937 : Blo 2239435 3361937 := bstep (se 2 (by rfl) ⟨1260726, by rfl⟩ : syracuseStep 3361937 = 2521453) B2521453
theorem B2241291 : Blo 2239435 2241291 := bstep (se 1 (by rfl) ⟨1680968, by rfl⟩ : syracuseStep 2241291 = 3361937) B3361937
theorem B7564373 : Blo 2239435 7564373 := bbase (se 8 (by rfl) ⟨44322, by rfl⟩ : syracuseStep 7564373 = 88645) (by norm_num)
theorem B5042915 : Blo 2239435 5042915 := bstep (se 1 (by rfl) ⟨3782186, by rfl⟩ : syracuseStep 5042915 = 7564373) B7564373
theorem B3361943 : Blo 2239435 3361943 := bstep (se 1 (by rfl) ⟨2521457, by rfl⟩ : syracuseStep 3361943 = 5042915) B5042915
theorem B2241295 : Blo 2239435 2241295 := bstep (se 1 (by rfl) ⟨1680971, by rfl⟩ : syracuseStep 2241295 = 3361943) B3361943
theorem B3361949 : Blo 2239435 3361949 := bbase (se 3 (by rfl) ⟨630365, by rfl⟩ : syracuseStep 3361949 = 1260731) (by norm_num)
theorem B2241299 : Blo 2239435 2241299 := bstep (se 1 (by rfl) ⟨1680974, by rfl⟩ : syracuseStep 2241299 = 3361949) B3361949
theorem B5042933 : Blo 2239435 5042933 := bbase (se 5 (by rfl) ⟨236387, by rfl⟩ : syracuseStep 5042933 = 472775) (by norm_num)
theorem B3361955 : Blo 2239435 3361955 := bstep (se 1 (by rfl) ⟨2521466, by rfl⟩ : syracuseStep 3361955 = 5042933) B5042933
theorem B2241303 : Blo 2239435 2241303 := bstep (se 1 (by rfl) ⟨1680977, by rfl⟩ : syracuseStep 2241303 = 3361955) B3361955
theorem B69008597 : Blo 2239435 69008597 := bbase (se 7 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 69008597 = 1617389) (by norm_num)
theorem B46005731 : Blo 2239435 46005731 := bstep (se 1 (by rfl) ⟨34504298, by rfl⟩ : syracuseStep 46005731 = 69008597) B69008597
theorem B30670487 : Blo 2239435 30670487 := bstep (se 1 (by rfl) ⟨23002865, by rfl⟩ : syracuseStep 30670487 = 46005731) B46005731
theorem B20446991 : Blo 2239435 20446991 := bstep (se 1 (by rfl) ⟨15335243, by rfl⟩ : syracuseStep 20446991 = 30670487) B30670487
theorem B13631327 : Blo 2239435 13631327 := bstep (se 1 (by rfl) ⟨10223495, by rfl⟩ : syracuseStep 13631327 = 20446991) B20446991
theorem B9087551 : Blo 2239435 9087551 := bstep (se 1 (by rfl) ⟨6815663, by rfl⟩ : syracuseStep 9087551 = 13631327) B13631327
theorem B6058367 : Blo 2239435 6058367 := bstep (se 1 (by rfl) ⟨4543775, by rfl⟩ : syracuseStep 6058367 = 9087551) B9087551
theorem B4038911 : Blo 2239435 4038911 := bstep (se 1 (by rfl) ⟨3029183, by rfl⟩ : syracuseStep 4038911 = 6058367) B6058367
theorem B2692607 : Blo 2239435 2692607 := bstep (se 1 (by rfl) ⟨2019455, by rfl⟩ : syracuseStep 2692607 = 4038911) B4038911
theorem B28721141 : Blo 2239435 28721141 := bstep (se 5 (by rfl) ⟨1346303, by rfl⟩ : syracuseStep 28721141 = 2692607) B2692607
theorem B19147427 : Blo 2239435 19147427 := bstep (se 1 (by rfl) ⟨14360570, by rfl⟩ : syracuseStep 19147427 = 28721141) B28721141
theorem B12764951 : Blo 2239435 12764951 := bstep (se 1 (by rfl) ⟨9573713, by rfl⟩ : syracuseStep 12764951 = 19147427) B19147427
theorem B8509967 : Blo 2239435 8509967 := bstep (se 1 (by rfl) ⟨6382475, by rfl⟩ : syracuseStep 8509967 = 12764951) B12764951
theorem B5673311 : Blo 2239435 5673311 := bstep (se 1 (by rfl) ⟨4254983, by rfl⟩ : syracuseStep 5673311 = 8509967) B8509967
theorem B3782207 : Blo 2239435 3782207 := bstep (se 1 (by rfl) ⟨2836655, by rfl⟩ : syracuseStep 3782207 = 5673311) B5673311
theorem B2521471 : Blo 2239435 2521471 := bstep (se 1 (by rfl) ⟨1891103, by rfl⟩ : syracuseStep 2521471 = 3782207) B3782207
theorem B3361961 : Blo 2239435 3361961 := bstep (se 2 (by rfl) ⟨1260735, by rfl⟩ : syracuseStep 3361961 = 2521471) B2521471
theorem B2241307 : Blo 2239435 2241307 := bstep (se 1 (by rfl) ⟨1680980, by rfl⟩ : syracuseStep 2241307 = 3361961) B3361961
theorem B3590149 : Blo 2239435 3590149 := bbase (se 4 (by rfl) ⟨336576, by rfl⟩ : syracuseStep 3590149 = 673153) (by norm_num)
theorem B4786865 : Blo 2239435 4786865 := bstep (se 2 (by rfl) ⟨1795074, by rfl⟩ : syracuseStep 4786865 = 3590149) B3590149
theorem B3191243 : Blo 2239435 3191243 := bstep (se 1 (by rfl) ⟨2393432, by rfl⟩ : syracuseStep 3191243 = 4786865) B4786865
theorem B8509981 : Blo 2239435 8509981 := bstep (se 3 (by rfl) ⟨1595621, by rfl⟩ : syracuseStep 8509981 = 3191243) B3191243
theorem B11346641 : Blo 2239435 11346641 := bstep (se 2 (by rfl) ⟨4254990, by rfl⟩ : syracuseStep 11346641 = 8509981) B8509981
theorem B7564427 : Blo 2239435 7564427 := bstep (se 1 (by rfl) ⟨5673320, by rfl⟩ : syracuseStep 7564427 = 11346641) B11346641
theorem B5042951 : Blo 2239435 5042951 := bstep (se 1 (by rfl) ⟨3782213, by rfl⟩ : syracuseStep 5042951 = 7564427) B7564427
theorem B3361967 : Blo 2239435 3361967 := bstep (se 1 (by rfl) ⟨2521475, by rfl⟩ : syracuseStep 3361967 = 5042951) B5042951
theorem B2241311 : Blo 2239435 2241311 := bstep (se 1 (by rfl) ⟨1680983, by rfl⟩ : syracuseStep 2241311 = 3361967) B3361967
theorem B3361973 : Blo 2239435 3361973 := bbase (se 5 (by rfl) ⟨157592, by rfl⟩ : syracuseStep 3361973 = 315185) (by norm_num)
theorem B2241315 : Blo 2239435 2241315 := bstep (se 1 (by rfl) ⟨1680986, by rfl⟩ : syracuseStep 2241315 = 3361973) B3361973
theorem B5673341 : Blo 2239435 5673341 := bbase (se 3 (by rfl) ⟨1063751, by rfl⟩ : syracuseStep 5673341 = 2127503) (by norm_num)
theorem B3782227 : Blo 2239435 3782227 := bstep (se 1 (by rfl) ⟨2836670, by rfl⟩ : syracuseStep 3782227 = 5673341) B5673341
theorem B5042969 : Blo 2239435 5042969 := bstep (se 2 (by rfl) ⟨1891113, by rfl⟩ : syracuseStep 5042969 = 3782227) B3782227
theorem B3361979 : Blo 2239435 3361979 := bstep (se 1 (by rfl) ⟨2521484, by rfl⟩ : syracuseStep 3361979 = 5042969) B5042969
theorem B2241319 : Blo 2239435 2241319 := bstep (se 1 (by rfl) ⟨1680989, by rfl⟩ : syracuseStep 2241319 = 3361979) B3361979
theorem B2521489 : Blo 2239435 2521489 := bbase (se 2 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 2521489 = 1891117) (by norm_num)
theorem B3361985 : Blo 2239435 3361985 := bstep (se 2 (by rfl) ⟨1260744, by rfl⟩ : syracuseStep 3361985 = 2521489) B2521489
theorem B2241323 : Blo 2239435 2241323 := bstep (se 1 (by rfl) ⟨1680992, by rfl⟩ : syracuseStep 2241323 = 3361985) B3361985
theorem B4255021 : Blo 2239435 4255021 := bbase (se 3 (by rfl) ⟨797816, by rfl⟩ : syracuseStep 4255021 = 1595633) (by norm_num)
theorem B5673361 : Blo 2239435 5673361 := bstep (se 2 (by rfl) ⟨2127510, by rfl⟩ : syracuseStep 5673361 = 4255021) B4255021
theorem B7564481 : Blo 2239435 7564481 := bstep (se 2 (by rfl) ⟨2836680, by rfl⟩ : syracuseStep 7564481 = 5673361) B5673361
theorem B5042987 : Blo 2239435 5042987 := bstep (se 1 (by rfl) ⟨3782240, by rfl⟩ : syracuseStep 5042987 = 7564481) B7564481
theorem B3361991 : Blo 2239435 3361991 := bstep (se 1 (by rfl) ⟨2521493, by rfl⟩ : syracuseStep 3361991 = 5042987) B5042987
theorem B2241327 : Blo 2239435 2241327 := bstep (se 1 (by rfl) ⟨1680995, by rfl⟩ : syracuseStep 2241327 = 3361991) B3361991
theorem B3361997 : Blo 2239435 3361997 := bbase (se 3 (by rfl) ⟨630374, by rfl⟩ : syracuseStep 3361997 = 1260749) (by norm_num)
theorem B2241331 : Blo 2239435 2241331 := bstep (se 1 (by rfl) ⟨1680998, by rfl⟩ : syracuseStep 2241331 = 3361997) B3361997
theorem B5043005 : Blo 2239435 5043005 := bbase (se 3 (by rfl) ⟨945563, by rfl⟩ : syracuseStep 5043005 = 1891127) (by norm_num)
theorem B3362003 : Blo 2239435 3362003 := bstep (se 1 (by rfl) ⟨2521502, by rfl⟩ : syracuseStep 3362003 = 5043005) B5043005
theorem B2241335 : Blo 2239435 2241335 := bstep (se 1 (by rfl) ⟨1681001, by rfl⟩ : syracuseStep 2241335 = 3362003) B3362003
theorem B3782261 : Blo 2239435 3782261 := bbase (se 5 (by rfl) ⟨177293, by rfl⟩ : syracuseStep 3782261 = 354587) (by norm_num)
theorem B2521507 : Blo 2239435 2521507 := bstep (se 1 (by rfl) ⟨1891130, by rfl⟩ : syracuseStep 2521507 = 3782261) B3782261
theorem B3362009 : Blo 2239435 3362009 := bstep (se 2 (by rfl) ⟨1260753, by rfl⟩ : syracuseStep 3362009 = 2521507) B2521507
theorem B2241339 : Blo 2239435 2241339 := bstep (se 1 (by rfl) ⟨1681004, by rfl⟩ : syracuseStep 2241339 = 3362009) B3362009
theorem B4786933 : Blo 2239435 4786933 := bbase (se 5 (by rfl) ⟨224387, by rfl⟩ : syracuseStep 4786933 = 448775) (by norm_num)
theorem B6382577 : Blo 2239435 6382577 := bstep (se 2 (by rfl) ⟨2393466, by rfl⟩ : syracuseStep 6382577 = 4786933) B4786933
theorem B17020205 : Blo 2239435 17020205 := bstep (se 3 (by rfl) ⟨3191288, by rfl⟩ : syracuseStep 17020205 = 6382577) B6382577
theorem B11346803 : Blo 2239435 11346803 := bstep (se 1 (by rfl) ⟨8510102, by rfl⟩ : syracuseStep 11346803 = 17020205) B17020205
theorem B7564535 : Blo 2239435 7564535 := bstep (se 1 (by rfl) ⟨5673401, by rfl⟩ : syracuseStep 7564535 = 11346803) B11346803
theorem B5043023 : Blo 2239435 5043023 := bstep (se 1 (by rfl) ⟨3782267, by rfl⟩ : syracuseStep 5043023 = 7564535) B7564535
theorem B3362015 : Blo 2239435 3362015 := bstep (se 1 (by rfl) ⟨2521511, by rfl⟩ : syracuseStep 3362015 = 5043023) B5043023
theorem B2241343 : Blo 2239435 2241343 := bstep (se 1 (by rfl) ⟨1681007, by rfl⟩ : syracuseStep 2241343 = 3362015) B3362015
theorem B3362021 : Blo 2239435 3362021 := bbase (se 4 (by rfl) ⟨315189, by rfl⟩ : syracuseStep 3362021 = 630379) (by norm_num)
theorem B2241347 : Blo 2239435 2241347 := bstep (se 1 (by rfl) ⟨1681010, by rfl⟩ : syracuseStep 2241347 = 3362021) B3362021
theorem B5829293 : Blo 2239435 5829293 := bbase (se 3 (by rfl) ⟨1092992, by rfl⟩ : syracuseStep 5829293 = 2185985) (by norm_num)
theorem B15544781 : Blo 2239435 15544781 := bstep (se 3 (by rfl) ⟨2914646, by rfl⟩ : syracuseStep 15544781 = 5829293) B5829293
theorem B10363187 : Blo 2239435 10363187 := bstep (se 1 (by rfl) ⟨7772390, by rfl⟩ : syracuseStep 10363187 = 15544781) B15544781
theorem B27635165 : Blo 2239435 27635165 := bstep (se 3 (by rfl) ⟨5181593, by rfl⟩ : syracuseStep 27635165 = 10363187) B10363187
theorem B18423443 : Blo 2239435 18423443 := bstep (se 1 (by rfl) ⟨13817582, by rfl⟩ : syracuseStep 18423443 = 27635165) B27635165
theorem B12282295 : Blo 2239435 12282295 := bstep (se 1 (by rfl) ⟨9211721, by rfl⟩ : syracuseStep 12282295 = 18423443) B18423443
theorem B16376393 : Blo 2239435 16376393 := bstep (se 2 (by rfl) ⟨6141147, by rfl⟩ : syracuseStep 16376393 = 12282295) B12282295
theorem B10917595 : Blo 2239435 10917595 := bstep (se 1 (by rfl) ⟨8188196, by rfl⟩ : syracuseStep 10917595 = 16376393) B16376393
theorem B14556793 : Blo 2239435 14556793 := bstep (se 2 (by rfl) ⟨5458797, by rfl⟩ : syracuseStep 14556793 = 10917595) B10917595
theorem B19409057 : Blo 2239435 19409057 := bstep (se 2 (by rfl) ⟨7278396, by rfl⟩ : syracuseStep 19409057 = 14556793) B14556793
theorem B12939371 : Blo 2239435 12939371 := bstep (se 1 (by rfl) ⟨9704528, by rfl⟩ : syracuseStep 12939371 = 19409057) B19409057
theorem B8626247 : Blo 2239435 8626247 := bstep (se 1 (by rfl) ⟨6469685, by rfl⟩ : syracuseStep 8626247 = 12939371) B12939371
theorem B5750831 : Blo 2239435 5750831 := bstep (se 1 (by rfl) ⟨4313123, by rfl⟩ : syracuseStep 5750831 = 8626247) B8626247
theorem B3833887 : Blo 2239435 3833887 := bstep (se 1 (by rfl) ⟨2875415, by rfl⟩ : syracuseStep 3833887 = 5750831) B5750831
theorem B5111849 : Blo 2239435 5111849 := bstep (se 2 (by rfl) ⟨1916943, by rfl⟩ : syracuseStep 5111849 = 3833887) B3833887
theorem B3407899 : Blo 2239435 3407899 := bstep (se 1 (by rfl) ⟨2555924, by rfl⟩ : syracuseStep 3407899 = 5111849) B5111849
theorem B4543865 : Blo 2239435 4543865 := bstep (se 2 (by rfl) ⟨1703949, by rfl⟩ : syracuseStep 4543865 = 3407899) B3407899
theorem B3029243 : Blo 2239435 3029243 := bstep (se 1 (by rfl) ⟨2271932, by rfl⟩ : syracuseStep 3029243 = 4543865) B4543865
theorem B8077981 : Blo 2239435 8077981 := bstep (se 3 (by rfl) ⟨1514621, by rfl⟩ : syracuseStep 8077981 = 3029243) B3029243
theorem B10770641 : Blo 2239435 10770641 := bstep (se 2 (by rfl) ⟨4038990, by rfl⟩ : syracuseStep 10770641 = 8077981) B8077981
theorem B7180427 : Blo 2239435 7180427 := bstep (se 1 (by rfl) ⟨5385320, by rfl⟩ : syracuseStep 7180427 = 10770641) B10770641
theorem B4786951 : Blo 2239435 4786951 := bstep (se 1 (by rfl) ⟨3590213, by rfl⟩ : syracuseStep 4786951 = 7180427) B7180427
theorem B6382601 : Blo 2239435 6382601 := bstep (se 2 (by rfl) ⟨2393475, by rfl⟩ : syracuseStep 6382601 = 4786951) B4786951
theorem B4255067 : Blo 2239435 4255067 := bstep (se 1 (by rfl) ⟨3191300, by rfl⟩ : syracuseStep 4255067 = 6382601) B6382601
theorem B2836711 : Blo 2239435 2836711 := bstep (se 1 (by rfl) ⟨2127533, by rfl⟩ : syracuseStep 2836711 = 4255067) B4255067
theorem B3782281 : Blo 2239435 3782281 := bstep (se 2 (by rfl) ⟨1418355, by rfl⟩ : syracuseStep 3782281 = 2836711) B2836711
theorem B5043041 : Blo 2239435 5043041 := bstep (se 2 (by rfl) ⟨1891140, by rfl⟩ : syracuseStep 5043041 = 3782281) B3782281
theorem B3362027 : Blo 2239435 3362027 := bstep (se 1 (by rfl) ⟨2521520, by rfl⟩ : syracuseStep 3362027 = 5043041) B5043041
theorem B2241351 : Blo 2239435 2241351 := bstep (se 1 (by rfl) ⟨1681013, by rfl⟩ : syracuseStep 2241351 = 3362027) B3362027
theorem B2521525 : Blo 2239435 2521525 := bbase (se 5 (by rfl) ⟨118196, by rfl⟩ : syracuseStep 2521525 = 236393) (by norm_num)
theorem B3362033 : Blo 2239435 3362033 := bstep (se 2 (by rfl) ⟨1260762, by rfl⟩ : syracuseStep 3362033 = 2521525) B2521525
theorem B2241355 : Blo 2239435 2241355 := bstep (se 1 (by rfl) ⟨1681016, by rfl⟩ : syracuseStep 2241355 = 3362033) B3362033
theorem B2836721 : Blo 2239435 2836721 := bbase (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) (by norm_num)
theorem B7564589 : Blo 2239435 7564589 := bstep (se 3 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 7564589 = 2836721) B2836721
theorem B5043059 : Blo 2239435 5043059 := bstep (se 1 (by rfl) ⟨3782294, by rfl⟩ : syracuseStep 5043059 = 7564589) B7564589
theorem B3362039 : Blo 2239435 3362039 := bstep (se 1 (by rfl) ⟨2521529, by rfl⟩ : syracuseStep 3362039 = 5043059) B5043059
theorem B2241359 : Blo 2239435 2241359 := bstep (se 1 (by rfl) ⟨1681019, by rfl⟩ : syracuseStep 2241359 = 3362039) B3362039
theorem B3362045 : Blo 2239435 3362045 := bbase (se 3 (by rfl) ⟨630383, by rfl⟩ : syracuseStep 3362045 = 1260767) (by norm_num)
theorem B2241363 : Blo 2239435 2241363 := bstep (se 1 (by rfl) ⟨1681022, by rfl⟩ : syracuseStep 2241363 = 3362045) B3362045
theorem B5043077 : Blo 2239435 5043077 := bbase (se 4 (by rfl) ⟨472788, by rfl⟩ : syracuseStep 5043077 = 945577) (by norm_num)
theorem B3362051 : Blo 2239435 3362051 := bstep (se 1 (by rfl) ⟨2521538, by rfl⟩ : syracuseStep 3362051 = 5043077) B5043077
theorem B2241367 : Blo 2239435 2241367 := bstep (se 1 (by rfl) ⟨1681025, by rfl⟩ : syracuseStep 2241367 = 3362051) B3362051
theorem B2393497 : Blo 2239435 2393497 := bbase (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) (by norm_num)
theorem B3191329 : Blo 2239435 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B4255105 : Blo 2239435 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B5673473 : Blo 2239435 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B3782315 : Blo 2239435 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B2521543 : Blo 2239435 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B3362057 : Blo 2239435 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B2241371 : Blo 2239435 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B11346965 : Blo 2239435 11346965 := bbase (se 6 (by rfl) ⟨265944, by rfl⟩ : syracuseStep 11346965 = 531889) (by norm_num)
theorem B7564643 : Blo 2239435 7564643 := bstep (se 1 (by rfl) ⟨5673482, by rfl⟩ : syracuseStep 7564643 = 11346965) B11346965
theorem B5043095 : Blo 2239435 5043095 := bstep (se 1 (by rfl) ⟨3782321, by rfl⟩ : syracuseStep 5043095 = 7564643) B7564643
theorem B3362063 : Blo 2239435 3362063 := bstep (se 1 (by rfl) ⟨2521547, by rfl⟩ : syracuseStep 3362063 = 5043095) B5043095
theorem B2241375 : Blo 2239435 2241375 := bstep (se 1 (by rfl) ⟨1681031, by rfl⟩ : syracuseStep 2241375 = 3362063) B3362063
theorem B3362069 : Blo 2239435 3362069 := bbase (se 6 (by rfl) ⟨78798, by rfl⟩ : syracuseStep 3362069 = 157597) (by norm_num)
theorem B2241379 : Blo 2239435 2241379 := bstep (se 1 (by rfl) ⟨1681034, by rfl⟩ : syracuseStep 2241379 = 3362069) B3362069
theorem B6815893 : Blo 2239435 6815893 := bbase (se 6 (by rfl) ⟨159747, by rfl⟩ : syracuseStep 6815893 = 319495) (by norm_num)
theorem B9087857 : Blo 2239435 9087857 := bstep (se 2 (by rfl) ⟨3407946, by rfl⟩ : syracuseStep 9087857 = 6815893) B6815893
theorem B6058571 : Blo 2239435 6058571 := bstep (se 1 (by rfl) ⟨4543928, by rfl⟩ : syracuseStep 6058571 = 9087857) B9087857
theorem B16156189 : Blo 2239435 16156189 := bstep (se 3 (by rfl) ⟨3029285, by rfl⟩ : syracuseStep 16156189 = 6058571) B6058571
theorem B21541585 : Blo 2239435 21541585 := bstep (se 2 (by rfl) ⟨8078094, by rfl⟩ : syracuseStep 21541585 = 16156189) B16156189
theorem B28722113 : Blo 2239435 28722113 := bstep (se 2 (by rfl) ⟨10770792, by rfl⟩ : syracuseStep 28722113 = 21541585) B21541585
theorem B19148075 : Blo 2239435 19148075 := bstep (se 1 (by rfl) ⟨14361056, by rfl⟩ : syracuseStep 19148075 = 28722113) B28722113
theorem B12765383 : Blo 2239435 12765383 := bstep (se 1 (by rfl) ⟨9574037, by rfl⟩ : syracuseStep 12765383 = 19148075) B19148075
theorem B8510255 : Blo 2239435 8510255 := bstep (se 1 (by rfl) ⟨6382691, by rfl⟩ : syracuseStep 8510255 = 12765383) B12765383
theorem B5673503 : Blo 2239435 5673503 := bstep (se 1 (by rfl) ⟨4255127, by rfl⟩ : syracuseStep 5673503 = 8510255) B8510255
theorem B3782335 : Blo 2239435 3782335 := bstep (se 1 (by rfl) ⟨2836751, by rfl⟩ : syracuseStep 3782335 = 5673503) B5673503
theorem B5043113 : Blo 2239435 5043113 := bstep (se 2 (by rfl) ⟨1891167, by rfl⟩ : syracuseStep 5043113 = 3782335) B3782335
theorem B3362075 : Blo 2239435 3362075 := bstep (se 1 (by rfl) ⟨2521556, by rfl⟩ : syracuseStep 3362075 = 5043113) B5043113
theorem B2241383 : Blo 2239435 2241383 := bstep (se 1 (by rfl) ⟨1681037, by rfl⟩ : syracuseStep 2241383 = 3362075) B3362075
theorem B2521561 : Blo 2239435 2521561 := bbase (se 2 (by rfl) ⟨945585, by rfl⟩ : syracuseStep 2521561 = 1891171) (by norm_num)
theorem B3362081 : Blo 2239435 3362081 := bstep (se 2 (by rfl) ⟨1260780, by rfl⟩ : syracuseStep 3362081 = 2521561) B2521561
theorem B2241387 : Blo 2239435 2241387 := bstep (se 1 (by rfl) ⟨1681040, by rfl⟩ : syracuseStep 2241387 = 3362081) B3362081
theorem B3191357 : Blo 2239435 3191357 := bbase (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) (by norm_num)
theorem B8510285 : Blo 2239435 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B5673523 : Blo 2239435 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B7564697 : Blo 2239435 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B5043131 : Blo 2239435 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B3362087 : Blo 2239435 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B2241391 : Blo 2239435 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B3362093 : Blo 2239435 3362093 := bbase (se 3 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 3362093 = 1260785) (by norm_num)
theorem B2241395 : Blo 2239435 2241395 := bstep (se 1 (by rfl) ⟨1681046, by rfl⟩ : syracuseStep 2241395 = 3362093) B3362093
theorem B5043149 : Blo 2239435 5043149 := bbase (se 3 (by rfl) ⟨945590, by rfl⟩ : syracuseStep 5043149 = 1891181) (by norm_num)
theorem B3362099 : Blo 2239435 3362099 := bstep (se 1 (by rfl) ⟨2521574, by rfl⟩ : syracuseStep 3362099 = 5043149) B5043149
theorem B2241399 : Blo 2239435 2241399 := bstep (se 1 (by rfl) ⟨1681049, by rfl⟩ : syracuseStep 2241399 = 3362099) B3362099
theorem B2836777 : Blo 2239435 2836777 := bbase (se 2 (by rfl) ⟨1063791, by rfl⟩ : syracuseStep 2836777 = 2127583) (by norm_num)
theorem B3782369 : Blo 2239435 3782369 := bstep (se 2 (by rfl) ⟨1418388, by rfl⟩ : syracuseStep 3782369 = 2836777) B2836777
theorem B2521579 : Blo 2239435 2521579 := bstep (se 1 (by rfl) ⟨1891184, by rfl⟩ : syracuseStep 2521579 = 3782369) B3782369
theorem B3362105 : Blo 2239435 3362105 := bstep (se 2 (by rfl) ⟨1260789, by rfl⟩ : syracuseStep 3362105 = 2521579) B2521579
theorem B2241403 : Blo 2239435 2241403 := bstep (se 1 (by rfl) ⟨1681052, by rfl⟩ : syracuseStep 2241403 = 3362105) B3362105
theorem B3833981 : Blo 2239435 3833981 := bbase (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) (by norm_num)
theorem B2555987 : Blo 2239435 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B27263861 : Blo 2239435 27263861 := bstep (se 5 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 27263861 = 2555987) B2555987
theorem B18175907 : Blo 2239435 18175907 := bstep (se 1 (by rfl) ⟨13631930, by rfl⟩ : syracuseStep 18175907 = 27263861) B27263861
theorem B12117271 : Blo 2239435 12117271 := bstep (se 1 (by rfl) ⟨9087953, by rfl⟩ : syracuseStep 12117271 = 18175907) B18175907
theorem B16156361 : Blo 2239435 16156361 := bstep (se 2 (by rfl) ⟨6058635, by rfl⟩ : syracuseStep 16156361 = 12117271) B12117271
theorem B10770907 : Blo 2239435 10770907 := bstep (se 1 (by rfl) ⟨8078180, by rfl⟩ : syracuseStep 10770907 = 16156361) B16156361
theorem B14361209 : Blo 2239435 14361209 := bstep (se 2 (by rfl) ⟨5385453, by rfl⟩ : syracuseStep 14361209 = 10770907) B10770907
theorem B9574139 : Blo 2239435 9574139 := bstep (se 1 (by rfl) ⟨7180604, by rfl⟩ : syracuseStep 9574139 = 14361209) B14361209
theorem B25531037 : Blo 2239435 25531037 := bstep (se 3 (by rfl) ⟨4787069, by rfl⟩ : syracuseStep 25531037 = 9574139) B9574139
theorem B17020691 : Blo 2239435 17020691 := bstep (se 1 (by rfl) ⟨12765518, by rfl⟩ : syracuseStep 17020691 = 25531037) B25531037
theorem B11347127 : Blo 2239435 11347127 := bstep (se 1 (by rfl) ⟨8510345, by rfl⟩ : syracuseStep 11347127 = 17020691) B17020691
theorem B7564751 : Blo 2239435 7564751 := bstep (se 1 (by rfl) ⟨5673563, by rfl⟩ : syracuseStep 7564751 = 11347127) B11347127
theorem B5043167 : Blo 2239435 5043167 := bstep (se 1 (by rfl) ⟨3782375, by rfl⟩ : syracuseStep 5043167 = 7564751) B7564751
theorem B3362111 : Blo 2239435 3362111 := bstep (se 1 (by rfl) ⟨2521583, by rfl⟩ : syracuseStep 3362111 = 5043167) B5043167
theorem B2241407 : Blo 2239435 2241407 := bstep (se 1 (by rfl) ⟨1681055, by rfl⟩ : syracuseStep 2241407 = 3362111) B3362111
theorem B3362117 : Blo 2239435 3362117 := bbase (se 4 (by rfl) ⟨315198, by rfl⟩ : syracuseStep 3362117 = 630397) (by norm_num)
theorem B2241411 : Blo 2239435 2241411 := bstep (se 1 (by rfl) ⟨1681058, by rfl⟩ : syracuseStep 2241411 = 3362117) B3362117
theorem B3782389 : Blo 2239435 3782389 := bbase (se 5 (by rfl) ⟨177299, by rfl⟩ : syracuseStep 3782389 = 354599) (by norm_num)
theorem B5043185 : Blo 2239435 5043185 := bstep (se 2 (by rfl) ⟨1891194, by rfl⟩ : syracuseStep 5043185 = 3782389) B3782389
theorem B3362123 : Blo 2239435 3362123 := bstep (se 1 (by rfl) ⟨2521592, by rfl⟩ : syracuseStep 3362123 = 5043185) B5043185
theorem B2241415 : Blo 2239435 2241415 := bstep (se 1 (by rfl) ⟨1681061, by rfl⟩ : syracuseStep 2241415 = 3362123) B3362123
theorem B2521597 : Blo 2239435 2521597 := bbase (se 3 (by rfl) ⟨472799, by rfl⟩ : syracuseStep 2521597 = 945599) (by norm_num)
theorem B3362129 : Blo 2239435 3362129 := bstep (se 2 (by rfl) ⟨1260798, by rfl⟩ : syracuseStep 3362129 = 2521597) B2521597
theorem B2241419 : Blo 2239435 2241419 := bstep (se 1 (by rfl) ⟨1681064, by rfl⟩ : syracuseStep 2241419 = 3362129) B3362129
theorem B7564805 : Blo 2239435 7564805 := bbase (se 4 (by rfl) ⟨709200, by rfl⟩ : syracuseStep 7564805 = 1418401) (by norm_num)
theorem B5043203 : Blo 2239435 5043203 := bstep (se 1 (by rfl) ⟨3782402, by rfl⟩ : syracuseStep 5043203 = 7564805) B7564805
theorem B3362135 : Blo 2239435 3362135 := bstep (se 1 (by rfl) ⟨2521601, by rfl⟩ : syracuseStep 3362135 = 5043203) B5043203
theorem B2241423 : Blo 2239435 2241423 := bstep (se 1 (by rfl) ⟨1681067, by rfl⟩ : syracuseStep 2241423 = 3362135) B3362135
theorem B3362141 : Blo 2239435 3362141 := bbase (se 3 (by rfl) ⟨630401, by rfl⟩ : syracuseStep 3362141 = 1260803) (by norm_num)
theorem B2241427 : Blo 2239435 2241427 := bstep (se 1 (by rfl) ⟨1681070, by rfl⟩ : syracuseStep 2241427 = 3362141) B3362141
theorem B5043221 : Blo 2239435 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B3362147 : Blo 2239435 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B2241431 : Blo 2239435 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B8510453 : Blo 2239435 8510453 := bbase (se 5 (by rfl) ⟨398927, by rfl⟩ : syracuseStep 8510453 = 797855) (by norm_num)
theorem B5673635 : Blo 2239435 5673635 := bstep (se 1 (by rfl) ⟨4255226, by rfl⟩ : syracuseStep 5673635 = 8510453) B8510453
theorem B3782423 : Blo 2239435 3782423 := bstep (se 1 (by rfl) ⟨2836817, by rfl⟩ : syracuseStep 3782423 = 5673635) B5673635
theorem B2521615 : Blo 2239435 2521615 := bstep (se 1 (by rfl) ⟨1891211, by rfl⟩ : syracuseStep 2521615 = 3782423) B3782423
theorem B3362153 : Blo 2239435 3362153 := bstep (se 2 (by rfl) ⟨1260807, by rfl⟩ : syracuseStep 3362153 = 2521615) B2521615
theorem B2241435 : Blo 2239435 2241435 := bstep (se 1 (by rfl) ⟨1681076, by rfl⟩ : syracuseStep 2241435 = 3362153) B3362153
theorem C0 (j : ℕ) (h1 : 559858 ≤ j) (h2 : j ≤ 560358) : Blo 2239435 (4 * j + 3) := by
  interval_cases j
  · exact B2239435
  · exact B2239439
  · exact B2239443
  · exact B2239447
  · exact B2239451
  · exact B2239455
  · exact B2239459
  · exact B2239463
  · exact B2239467
  · exact B2239471
  · exact B2239475
  · exact B2239479
  · exact B2239483
  · exact B2239487
  · exact B2239491
  · exact B2239495
  · exact B2239499
  · exact B2239503
  · exact B2239507
  · exact B2239511
  · exact B2239515
  · exact B2239519
  · exact B2239523
  · exact B2239527
  · exact B2239531
  · exact B2239535
  · exact B2239539
  · exact B2239543
  · exact B2239547
  · exact B2239551
  · exact B2239555
  · exact B2239559
  · exact B2239563
  · exact B2239567
  · exact B2239571
  · exact B2239575
  · exact B2239579
  · exact B2239583
  · exact B2239587
  · exact B2239591
  · exact B2239595
  · exact B2239599
  · exact B2239603
  · exact B2239607
  · exact B2239611
  · exact B2239615
  · exact B2239619
  · exact B2239623
  · exact B2239627
  · exact B2239631
  · exact B2239635
  · exact B2239639
  · exact B2239643
  · exact B2239647
  · exact B2239651
  · exact B2239655
  · exact B2239659
  · exact B2239663
  · exact B2239667
  · exact B2239671
  · exact B2239675
  · exact B2239679
  · exact B2239683
  · exact B2239687
  · exact B2239691
  · exact B2239695
  · exact B2239699
  · exact B2239703
  · exact B2239707
  · exact B2239711
  · exact B2239715
  · exact B2239719
  · exact B2239723
  · exact B2239727
  · exact B2239731
  · exact B2239735
  · exact B2239739
  · exact B2239743
  · exact B2239747
  · exact B2239751
  · exact B2239755
  · exact B2239759
  · exact B2239763
  · exact B2239767
  · exact B2239771
  · exact B2239775
  · exact B2239779
  · exact B2239783
  · exact B2239787
  · exact B2239791
  · exact B2239795
  · exact B2239799
  · exact B2239803
  · exact B2239807
  · exact B2239811
  · exact B2239815
  · exact B2239819
  · exact B2239823
  · exact B2239827
  · exact B2239831
  · exact B2239835
  · exact B2239839
  · exact B2239843
  · exact B2239847
  · exact B2239851
  · exact B2239855
  · exact B2239859
  · exact B2239863
  · exact B2239867
  · exact B2239871
  · exact B2239875
  · exact B2239879
  · exact B2239883
  · exact B2239887
  · exact B2239891
  · exact B2239895
  · exact B2239899
  · exact B2239903
  · exact B2239907
  · exact B2239911
  · exact B2239915
  · exact B2239919
  · exact B2239923
  · exact B2239927
  · exact B2239931
  · exact B2239935
  · exact B2239939
  · exact B2239943
  · exact B2239947
  · exact B2239951
  · exact B2239955
  · exact B2239959
  · exact B2239963
  · exact B2239967
  · exact B2239971
  · exact B2239975
  · exact B2239979
  · exact B2239983
  · exact B2239987
  · exact B2239991
  · exact B2239995
  · exact B2239999
  · exact B2240003
  · exact B2240007
  · exact B2240011
  · exact B2240015
  · exact B2240019
  · exact B2240023
  · exact B2240027
  · exact B2240031
  · exact B2240035
  · exact B2240039
  · exact B2240043
  · exact B2240047
  · exact B2240051
  · exact B2240055
  · exact B2240059
  · exact B2240063
  · exact B2240067
  · exact B2240071
  · exact B2240075
  · exact B2240079
  · exact B2240083
  · exact B2240087
  · exact B2240091
  · exact B2240095
  · exact B2240099
  · exact B2240103
  · exact B2240107
  · exact B2240111
  · exact B2240115
  · exact B2240119
  · exact B2240123
  · exact B2240127
  · exact B2240131
  · exact B2240135
  · exact B2240139
  · exact B2240143
  · exact B2240147
  · exact B2240151
  · exact B2240155
  · exact B2240159
  · exact B2240163
  · exact B2240167
  · exact B2240171
  · exact B2240175
  · exact B2240179
  · exact B2240183
  · exact B2240187
  · exact B2240191
  · exact B2240195
  · exact B2240199
  · exact B2240203
  · exact B2240207
  · exact B2240211
  · exact B2240215
  · exact B2240219
  · exact B2240223
  · exact B2240227
  · exact B2240231
  · exact B2240235
  · exact B2240239
  · exact B2240243
  · exact B2240247
  · exact B2240251
  · exact B2240255
  · exact B2240259
  · exact B2240263
  · exact B2240267
  · exact B2240271
  · exact B2240275
  · exact B2240279
  · exact B2240283
  · exact B2240287
  · exact B2240291
  · exact B2240295
  · exact B2240299
  · exact B2240303
  · exact B2240307
  · exact B2240311
  · exact B2240315
  · exact B2240319
  · exact B2240323
  · exact B2240327
  · exact B2240331
  · exact B2240335
  · exact B2240339
  · exact B2240343
  · exact B2240347
  · exact B2240351
  · exact B2240355
  · exact B2240359
  · exact B2240363
  · exact B2240367
  · exact B2240371
  · exact B2240375
  · exact B2240379
  · exact B2240383
  · exact B2240387
  · exact B2240391
  · exact B2240395
  · exact B2240399
  · exact B2240403
  · exact B2240407
  · exact B2240411
  · exact B2240415
  · exact B2240419
  · exact B2240423
  · exact B2240427
  · exact B2240431
  · exact B2240435
  · exact B2240439
  · exact B2240443
  · exact B2240447
  · exact B2240451
  · exact B2240455
  · exact B2240459
  · exact B2240463
  · exact B2240467
  · exact B2240471
  · exact B2240475
  · exact B2240479
  · exact B2240483
  · exact B2240487
  · exact B2240491
  · exact B2240495
  · exact B2240499
  · exact B2240503
  · exact B2240507
  · exact B2240511
  · exact B2240515
  · exact B2240519
  · exact B2240523
  · exact B2240527
  · exact B2240531
  · exact B2240535
  · exact B2240539
  · exact B2240543
  · exact B2240547
  · exact B2240551
  · exact B2240555
  · exact B2240559
  · exact B2240563
  · exact B2240567
  · exact B2240571
  · exact B2240575
  · exact B2240579
  · exact B2240583
  · exact B2240587
  · exact B2240591
  · exact B2240595
  · exact B2240599
  · exact B2240603
  · exact B2240607
  · exact B2240611
  · exact B2240615
  · exact B2240619
  · exact B2240623
  · exact B2240627
  · exact B2240631
  · exact B2240635
  · exact B2240639
  · exact B2240643
  · exact B2240647
  · exact B2240651
  · exact B2240655
  · exact B2240659
  · exact B2240663
  · exact B2240667
  · exact B2240671
  · exact B2240675
  · exact B2240679
  · exact B2240683
  · exact B2240687
  · exact B2240691
  · exact B2240695
  · exact B2240699
  · exact B2240703
  · exact B2240707
  · exact B2240711
  · exact B2240715
  · exact B2240719
  · exact B2240723
  · exact B2240727
  · exact B2240731
  · exact B2240735
  · exact B2240739
  · exact B2240743
  · exact B2240747
  · exact B2240751
  · exact B2240755
  · exact B2240759
  · exact B2240763
  · exact B2240767
  · exact B2240771
  · exact B2240775
  · exact B2240779
  · exact B2240783
  · exact B2240787
  · exact B2240791
  · exact B2240795
  · exact B2240799
  · exact B2240803
  · exact B2240807
  · exact B2240811
  · exact B2240815
  · exact B2240819
  · exact B2240823
  · exact B2240827
  · exact B2240831
  · exact B2240835
  · exact B2240839
  · exact B2240843
  · exact B2240847
  · exact B2240851
  · exact B2240855
  · exact B2240859
  · exact B2240863
  · exact B2240867
  · exact B2240871
  · exact B2240875
  · exact B2240879
  · exact B2240883
  · exact B2240887
  · exact B2240891
  · exact B2240895
  · exact B2240899
  · exact B2240903
  · exact B2240907
  · exact B2240911
  · exact B2240915
  · exact B2240919
  · exact B2240923
  · exact B2240927
  · exact B2240931
  · exact B2240935
  · exact B2240939
  · exact B2240943
  · exact B2240947
  · exact B2240951
  · exact B2240955
  · exact B2240959
  · exact B2240963
  · exact B2240967
  · exact B2240971
  · exact B2240975
  · exact B2240979
  · exact B2240983
  · exact B2240987
  · exact B2240991
  · exact B2240995
  · exact B2240999
  · exact B2241003
  · exact B2241007
  · exact B2241011
  · exact B2241015
  · exact B2241019
  · exact B2241023
  · exact B2241027
  · exact B2241031
  · exact B2241035
  · exact B2241039
  · exact B2241043
  · exact B2241047
  · exact B2241051
  · exact B2241055
  · exact B2241059
  · exact B2241063
  · exact B2241067
  · exact B2241071
  · exact B2241075
  · exact B2241079
  · exact B2241083
  · exact B2241087
  · exact B2241091
  · exact B2241095
  · exact B2241099
  · exact B2241103
  · exact B2241107
  · exact B2241111
  · exact B2241115
  · exact B2241119
  · exact B2241123
  · exact B2241127
  · exact B2241131
  · exact B2241135
  · exact B2241139
  · exact B2241143
  · exact B2241147
  · exact B2241151
  · exact B2241155
  · exact B2241159
  · exact B2241163
  · exact B2241167
  · exact B2241171
  · exact B2241175
  · exact B2241179
  · exact B2241183
  · exact B2241187
  · exact B2241191
  · exact B2241195
  · exact B2241199
  · exact B2241203
  · exact B2241207
  · exact B2241211
  · exact B2241215
  · exact B2241219
  · exact B2241223
  · exact B2241227
  · exact B2241231
  · exact B2241235
  · exact B2241239
  · exact B2241243
  · exact B2241247
  · exact B2241251
  · exact B2241255
  · exact B2241259
  · exact B2241263
  · exact B2241267
  · exact B2241271
  · exact B2241275
  · exact B2241279
  · exact B2241283
  · exact B2241287
  · exact B2241291
  · exact B2241295
  · exact B2241299
  · exact B2241303
  · exact B2241307
  · exact B2241311
  · exact B2241315
  · exact B2241319
  · exact B2241323
  · exact B2241327
  · exact B2241331
  · exact B2241335
  · exact B2241339
  · exact B2241343
  · exact B2241347
  · exact B2241351
  · exact B2241355
  · exact B2241359
  · exact B2241363
  · exact B2241367
  · exact B2241371
  · exact B2241375
  · exact B2241379
  · exact B2241383
  · exact B2241387
  · exact B2241391
  · exact B2241395
  · exact B2241399
  · exact B2241403
  · exact B2241407
  · exact B2241411
  · exact B2241415
  · exact B2241419
  · exact B2241423
  · exact B2241427
  · exact B2241431
  · exact B2241435
theorem solution (m : ℕ) (hlo : 2239435 ≤ m) (hhi : m ≤ 2241435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 559858 ≤ j := by omega
    have hj2 : j ≤ 560358 := by omega
    have hb : Blo 2239435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
