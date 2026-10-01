-- Prove2me | solution 1 for syracuse_descends_range_2225435_2227435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:43.929062+00:00
-- url     : https://prove2.me/submissions/aea20f29-dad8-423d-8812-b7ed852d9dc5

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

theorem B10572277 : Blo 2225435 10572277 := bbase (se 5 (by rfl) ⟨495575, by rfl⟩ : syracuseStep 10572277 = 991151) (by norm_num)
theorem B14096369 : Blo 2225435 14096369 := bstep (se 2 (by rfl) ⟨5286138, by rfl⟩ : syracuseStep 14096369 = 10572277) B10572277
theorem B9397579 : Blo 2225435 9397579 := bstep (se 1 (by rfl) ⟨7048184, by rfl⟩ : syracuseStep 9397579 = 14096369) B14096369
theorem B12530105 : Blo 2225435 12530105 := bstep (se 2 (by rfl) ⟨4698789, by rfl⟩ : syracuseStep 12530105 = 9397579) B9397579
theorem B8353403 : Blo 2225435 8353403 := bstep (se 1 (by rfl) ⟨6265052, by rfl⟩ : syracuseStep 8353403 = 12530105) B12530105
theorem B5568935 : Blo 2225435 5568935 := bstep (se 1 (by rfl) ⟨4176701, by rfl⟩ : syracuseStep 5568935 = 8353403) B8353403
theorem B59401973 : Blo 2225435 59401973 := bstep (se 5 (by rfl) ⟨2784467, by rfl⟩ : syracuseStep 59401973 = 5568935) B5568935
theorem B39601315 : Blo 2225435 39601315 := bstep (se 1 (by rfl) ⟨29700986, by rfl⟩ : syracuseStep 39601315 = 59401973) B59401973
theorem B52801753 : Blo 2225435 52801753 := bstep (se 2 (by rfl) ⟨19800657, by rfl⟩ : syracuseStep 52801753 = 39601315) B39601315
theorem B70402337 : Blo 2225435 70402337 := bstep (se 2 (by rfl) ⟨26400876, by rfl⟩ : syracuseStep 70402337 = 52801753) B52801753
theorem B46934891 : Blo 2225435 46934891 := bstep (se 1 (by rfl) ⟨35201168, by rfl⟩ : syracuseStep 46934891 = 70402337) B70402337
theorem B31289927 : Blo 2225435 31289927 := bstep (se 1 (by rfl) ⟨23467445, by rfl⟩ : syracuseStep 31289927 = 46934891) B46934891
theorem B333759221 : Blo 2225435 333759221 := bstep (se 5 (by rfl) ⟨15644963, by rfl⟩ : syracuseStep 333759221 = 31289927) B31289927
theorem B222506147 : Blo 2225435 222506147 := bstep (se 1 (by rfl) ⟨166879610, by rfl⟩ : syracuseStep 222506147 = 333759221) B333759221
theorem B593349725 : Blo 2225435 593349725 := bstep (se 3 (by rfl) ⟨111253073, by rfl⟩ : syracuseStep 593349725 = 222506147) B222506147
theorem B1582265933 : Blo 2225435 1582265933 := bstep (se 3 (by rfl) ⟨296674862, by rfl⟩ : syracuseStep 1582265933 = 593349725) B593349725
theorem B1054843955 : Blo 2225435 1054843955 := bstep (se 1 (by rfl) ⟨791132966, by rfl⟩ : syracuseStep 1054843955 = 1582265933) B1582265933
theorem B703229303 : Blo 2225435 703229303 := bstep (se 1 (by rfl) ⟨527421977, by rfl⟩ : syracuseStep 703229303 = 1054843955) B1054843955
theorem B468819535 : Blo 2225435 468819535 := bstep (se 1 (by rfl) ⟨351614651, by rfl⟩ : syracuseStep 468819535 = 703229303) B703229303
theorem B625092713 : Blo 2225435 625092713 := bstep (se 2 (by rfl) ⟨234409767, by rfl⟩ : syracuseStep 625092713 = 468819535) B468819535
theorem B416728475 : Blo 2225435 416728475 := bstep (se 1 (by rfl) ⟨312546356, by rfl⟩ : syracuseStep 416728475 = 625092713) B625092713
theorem B277818983 : Blo 2225435 277818983 := bstep (se 1 (by rfl) ⟨208364237, by rfl⟩ : syracuseStep 277818983 = 416728475) B416728475
theorem B185212655 : Blo 2225435 185212655 := bstep (se 1 (by rfl) ⟨138909491, by rfl⟩ : syracuseStep 185212655 = 277818983) B277818983
theorem B123475103 : Blo 2225435 123475103 := bstep (se 1 (by rfl) ⟨92606327, by rfl⟩ : syracuseStep 123475103 = 185212655) B185212655
theorem B82316735 : Blo 2225435 82316735 := bstep (se 1 (by rfl) ⟨61737551, by rfl⟩ : syracuseStep 82316735 = 123475103) B123475103
theorem B54877823 : Blo 2225435 54877823 := bstep (se 1 (by rfl) ⟨41158367, by rfl⟩ : syracuseStep 54877823 = 82316735) B82316735
theorem B36585215 : Blo 2225435 36585215 := bstep (se 1 (by rfl) ⟨27438911, by rfl⟩ : syracuseStep 36585215 = 54877823) B54877823
theorem B24390143 : Blo 2225435 24390143 := bstep (se 1 (by rfl) ⟨18292607, by rfl⟩ : syracuseStep 24390143 = 36585215) B36585215
theorem B16260095 : Blo 2225435 16260095 := bstep (se 1 (by rfl) ⟨12195071, by rfl⟩ : syracuseStep 16260095 = 24390143) B24390143
theorem B10840063 : Blo 2225435 10840063 := bstep (se 1 (by rfl) ⟨8130047, by rfl⟩ : syracuseStep 10840063 = 16260095) B16260095
theorem B14453417 : Blo 2225435 14453417 := bstep (se 2 (by rfl) ⟨5420031, by rfl⟩ : syracuseStep 14453417 = 10840063) B10840063
theorem B9635611 : Blo 2225435 9635611 := bstep (se 1 (by rfl) ⟨7226708, by rfl⟩ : syracuseStep 9635611 = 14453417) B14453417
theorem B12847481 : Blo 2225435 12847481 := bstep (se 2 (by rfl) ⟨4817805, by rfl⟩ : syracuseStep 12847481 = 9635611) B9635611
theorem B8564987 : Blo 2225435 8564987 := bstep (se 1 (by rfl) ⟨6423740, by rfl⟩ : syracuseStep 8564987 = 12847481) B12847481
theorem B22839965 : Blo 2225435 22839965 := bstep (se 3 (by rfl) ⟨4282493, by rfl⟩ : syracuseStep 22839965 = 8564987) B8564987
theorem B15226643 : Blo 2225435 15226643 := bstep (se 1 (by rfl) ⟨11419982, by rfl⟩ : syracuseStep 15226643 = 22839965) B22839965
theorem B10151095 : Blo 2225435 10151095 := bstep (se 1 (by rfl) ⟨7613321, by rfl⟩ : syracuseStep 10151095 = 15226643) B15226643
theorem B13534793 : Blo 2225435 13534793 := bstep (se 2 (by rfl) ⟨5075547, by rfl⟩ : syracuseStep 13534793 = 10151095) B10151095
theorem B9023195 : Blo 2225435 9023195 := bstep (se 1 (by rfl) ⟨6767396, by rfl⟩ : syracuseStep 9023195 = 13534793) B13534793
theorem B24061853 : Blo 2225435 24061853 := bstep (se 3 (by rfl) ⟨4511597, by rfl⟩ : syracuseStep 24061853 = 9023195) B9023195
theorem B16041235 : Blo 2225435 16041235 := bstep (se 1 (by rfl) ⟨12030926, by rfl⟩ : syracuseStep 16041235 = 24061853) B24061853
theorem B21388313 : Blo 2225435 21388313 := bstep (se 2 (by rfl) ⟨8020617, by rfl⟩ : syracuseStep 21388313 = 16041235) B16041235
theorem B14258875 : Blo 2225435 14258875 := bstep (se 1 (by rfl) ⟨10694156, by rfl⟩ : syracuseStep 14258875 = 21388313) B21388313
theorem B19011833 : Blo 2225435 19011833 := bstep (se 2 (by rfl) ⟨7129437, by rfl⟩ : syracuseStep 19011833 = 14258875) B14258875
theorem B12674555 : Blo 2225435 12674555 := bstep (se 1 (by rfl) ⟨9505916, by rfl⟩ : syracuseStep 12674555 = 19011833) B19011833
theorem B8449703 : Blo 2225435 8449703 := bstep (se 1 (by rfl) ⟨6337277, by rfl⟩ : syracuseStep 8449703 = 12674555) B12674555
theorem B5633135 : Blo 2225435 5633135 := bstep (se 1 (by rfl) ⟨4224851, by rfl⟩ : syracuseStep 5633135 = 8449703) B8449703
theorem B3755423 : Blo 2225435 3755423 := bstep (se 1 (by rfl) ⟨2816567, by rfl⟩ : syracuseStep 3755423 = 5633135) B5633135
theorem B2503615 : Blo 2225435 2503615 := bstep (se 1 (by rfl) ⟨1877711, by rfl⟩ : syracuseStep 2503615 = 3755423) B3755423
theorem B3338153 : Blo 2225435 3338153 := bstep (se 2 (by rfl) ⟨1251807, by rfl⟩ : syracuseStep 3338153 = 2503615) B2503615
theorem B2225435 : Blo 2225435 2225435 := bstep (se 1 (by rfl) ⟨1669076, by rfl⟩ : syracuseStep 2225435 = 3338153) B3338153
theorem B8449717 : Blo 2225435 8449717 := bbase (se 5 (by rfl) ⟨396080, by rfl⟩ : syracuseStep 8449717 = 792161) (by norm_num)
theorem B11266289 : Blo 2225435 11266289 := bstep (se 2 (by rfl) ⟨4224858, by rfl⟩ : syracuseStep 11266289 = 8449717) B8449717
theorem B7510859 : Blo 2225435 7510859 := bstep (se 1 (by rfl) ⟨5633144, by rfl⟩ : syracuseStep 7510859 = 11266289) B11266289
theorem B5007239 : Blo 2225435 5007239 := bstep (se 1 (by rfl) ⟨3755429, by rfl⟩ : syracuseStep 5007239 = 7510859) B7510859
theorem B3338159 : Blo 2225435 3338159 := bstep (se 1 (by rfl) ⟨2503619, by rfl⟩ : syracuseStep 3338159 = 5007239) B5007239
theorem B2225439 : Blo 2225435 2225439 := bstep (se 1 (by rfl) ⟨1669079, by rfl⟩ : syracuseStep 2225439 = 3338159) B3338159
theorem B3338165 : Blo 2225435 3338165 := bbase (se 5 (by rfl) ⟨156476, by rfl⟩ : syracuseStep 3338165 = 312953) (by norm_num)
theorem B2225443 : Blo 2225435 2225443 := bstep (se 1 (by rfl) ⟨1669082, by rfl⟩ : syracuseStep 2225443 = 3338165) B3338165
theorem B5633165 : Blo 2225435 5633165 := bbase (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) (by norm_num)
theorem B3755443 : Blo 2225435 3755443 := bstep (se 1 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 3755443 = 5633165) B5633165
theorem B5007257 : Blo 2225435 5007257 := bstep (se 2 (by rfl) ⟨1877721, by rfl⟩ : syracuseStep 5007257 = 3755443) B3755443
theorem B3338171 : Blo 2225435 3338171 := bstep (se 1 (by rfl) ⟨2503628, by rfl⟩ : syracuseStep 3338171 = 5007257) B5007257
theorem B2225447 : Blo 2225435 2225447 := bstep (se 1 (by rfl) ⟨1669085, by rfl⟩ : syracuseStep 2225447 = 3338171) B3338171
theorem B2503633 : Blo 2225435 2503633 := bbase (se 2 (by rfl) ⟨938862, by rfl⟩ : syracuseStep 2503633 = 1877725) (by norm_num)
theorem B3338177 : Blo 2225435 3338177 := bstep (se 2 (by rfl) ⟨1251816, by rfl⟩ : syracuseStep 3338177 = 2503633) B2503633
theorem B2225451 : Blo 2225435 2225451 := bstep (se 1 (by rfl) ⟨1669088, by rfl⟩ : syracuseStep 2225451 = 3338177) B3338177
theorem B10151189 : Blo 2225435 10151189 := bbase (se 6 (by rfl) ⟨237918, by rfl⟩ : syracuseStep 10151189 = 475837) (by norm_num)
theorem B6767459 : Blo 2225435 6767459 := bstep (se 1 (by rfl) ⟨5075594, by rfl⟩ : syracuseStep 6767459 = 10151189) B10151189
theorem B4511639 : Blo 2225435 4511639 := bstep (se 1 (by rfl) ⟨3383729, by rfl⟩ : syracuseStep 4511639 = 6767459) B6767459
theorem B12031037 : Blo 2225435 12031037 := bstep (se 3 (by rfl) ⟨2255819, by rfl⟩ : syracuseStep 12031037 = 4511639) B4511639
theorem B8020691 : Blo 2225435 8020691 := bstep (se 1 (by rfl) ⟨6015518, by rfl⟩ : syracuseStep 8020691 = 12031037) B12031037
theorem B5347127 : Blo 2225435 5347127 := bstep (se 1 (by rfl) ⟨4010345, by rfl⟩ : syracuseStep 5347127 = 8020691) B8020691
theorem B3564751 : Blo 2225435 3564751 := bstep (se 1 (by rfl) ⟨2673563, by rfl⟩ : syracuseStep 3564751 = 5347127) B5347127
theorem B4753001 : Blo 2225435 4753001 := bstep (se 2 (by rfl) ⟨1782375, by rfl⟩ : syracuseStep 4753001 = 3564751) B3564751
theorem B3168667 : Blo 2225435 3168667 := bstep (se 1 (by rfl) ⟨2376500, by rfl⟩ : syracuseStep 3168667 = 4753001) B4753001
theorem B4224889 : Blo 2225435 4224889 := bstep (se 2 (by rfl) ⟨1584333, by rfl⟩ : syracuseStep 4224889 = 3168667) B3168667
theorem B5633185 : Blo 2225435 5633185 := bstep (se 2 (by rfl) ⟨2112444, by rfl⟩ : syracuseStep 5633185 = 4224889) B4224889
theorem B7510913 : Blo 2225435 7510913 := bstep (se 2 (by rfl) ⟨2816592, by rfl⟩ : syracuseStep 7510913 = 5633185) B5633185
theorem B5007275 : Blo 2225435 5007275 := bstep (se 1 (by rfl) ⟨3755456, by rfl⟩ : syracuseStep 5007275 = 7510913) B7510913
theorem B3338183 : Blo 2225435 3338183 := bstep (se 1 (by rfl) ⟨2503637, by rfl⟩ : syracuseStep 3338183 = 5007275) B5007275
theorem B2225455 : Blo 2225435 2225455 := bstep (se 1 (by rfl) ⟨1669091, by rfl⟩ : syracuseStep 2225455 = 3338183) B3338183
theorem B3338189 : Blo 2225435 3338189 := bbase (se 3 (by rfl) ⟨625910, by rfl⟩ : syracuseStep 3338189 = 1251821) (by norm_num)
theorem B2225459 : Blo 2225435 2225459 := bstep (se 1 (by rfl) ⟨1669094, by rfl⟩ : syracuseStep 2225459 = 3338189) B3338189
theorem B5007293 : Blo 2225435 5007293 := bbase (se 3 (by rfl) ⟨938867, by rfl⟩ : syracuseStep 5007293 = 1877735) (by norm_num)
theorem B3338195 : Blo 2225435 3338195 := bstep (se 1 (by rfl) ⟨2503646, by rfl⟩ : syracuseStep 3338195 = 5007293) B5007293
theorem B2225463 : Blo 2225435 2225463 := bstep (se 1 (by rfl) ⟨1669097, by rfl⟩ : syracuseStep 2225463 = 3338195) B3338195
theorem B3755477 : Blo 2225435 3755477 := bbase (se 7 (by rfl) ⟨44009, by rfl⟩ : syracuseStep 3755477 = 88019) (by norm_num)
theorem B2503651 : Blo 2225435 2503651 := bstep (se 1 (by rfl) ⟨1877738, by rfl⟩ : syracuseStep 2503651 = 3755477) B3755477
theorem B3338201 : Blo 2225435 3338201 := bstep (se 2 (by rfl) ⟨1251825, by rfl⟩ : syracuseStep 3338201 = 2503651) B2503651
theorem B2225467 : Blo 2225435 2225467 := bstep (se 1 (by rfl) ⟨1669100, by rfl⟩ : syracuseStep 2225467 = 3338201) B3338201
theorem B9506069 : Blo 2225435 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B6337379 : Blo 2225435 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B16899677 : Blo 2225435 16899677 := bstep (se 3 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 16899677 = 6337379) B6337379
theorem B11266451 : Blo 2225435 11266451 := bstep (se 1 (by rfl) ⟨8449838, by rfl⟩ : syracuseStep 11266451 = 16899677) B16899677
theorem B7510967 : Blo 2225435 7510967 := bstep (se 1 (by rfl) ⟨5633225, by rfl⟩ : syracuseStep 7510967 = 11266451) B11266451
theorem B5007311 : Blo 2225435 5007311 := bstep (se 1 (by rfl) ⟨3755483, by rfl⟩ : syracuseStep 5007311 = 7510967) B7510967
theorem B3338207 : Blo 2225435 3338207 := bstep (se 1 (by rfl) ⟨2503655, by rfl⟩ : syracuseStep 3338207 = 5007311) B5007311
theorem B2225471 : Blo 2225435 2225471 := bstep (se 1 (by rfl) ⟨1669103, by rfl⟩ : syracuseStep 2225471 = 3338207) B3338207
theorem B3338213 : Blo 2225435 3338213 := bbase (se 4 (by rfl) ⟨312957, by rfl⟩ : syracuseStep 3338213 = 625915) (by norm_num)
theorem B2225475 : Blo 2225435 2225475 := bstep (se 1 (by rfl) ⟨1669106, by rfl⟩ : syracuseStep 2225475 = 3338213) B3338213
theorem B5420141 : Blo 2225435 5420141 := bbase (se 3 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 5420141 = 2032553) (by norm_num)
theorem B3613427 : Blo 2225435 3613427 := bstep (se 1 (by rfl) ⟨2710070, by rfl⟩ : syracuseStep 3613427 = 5420141) B5420141
theorem B2408951 : Blo 2225435 2408951 := bstep (se 1 (by rfl) ⟨1806713, by rfl⟩ : syracuseStep 2408951 = 3613427) B3613427
theorem B6423869 : Blo 2225435 6423869 := bstep (se 3 (by rfl) ⟨1204475, by rfl⟩ : syracuseStep 6423869 = 2408951) B2408951
theorem B4282579 : Blo 2225435 4282579 := bstep (se 1 (by rfl) ⟨3211934, by rfl⟩ : syracuseStep 4282579 = 6423869) B6423869
theorem B5710105 : Blo 2225435 5710105 := bstep (se 2 (by rfl) ⟨2141289, by rfl⟩ : syracuseStep 5710105 = 4282579) B4282579
theorem B30453893 : Blo 2225435 30453893 := bstep (se 4 (by rfl) ⟨2855052, by rfl⟩ : syracuseStep 30453893 = 5710105) B5710105
theorem B20302595 : Blo 2225435 20302595 := bstep (se 1 (by rfl) ⟨15226946, by rfl⟩ : syracuseStep 20302595 = 30453893) B30453893
theorem B13535063 : Blo 2225435 13535063 := bstep (se 1 (by rfl) ⟨10151297, by rfl⟩ : syracuseStep 13535063 = 20302595) B20302595
theorem B9023375 : Blo 2225435 9023375 := bstep (se 1 (by rfl) ⟨6767531, by rfl⟩ : syracuseStep 9023375 = 13535063) B13535063
theorem B6015583 : Blo 2225435 6015583 := bstep (se 1 (by rfl) ⟨4511687, by rfl⟩ : syracuseStep 6015583 = 9023375) B9023375
theorem B8020777 : Blo 2225435 8020777 := bstep (se 2 (by rfl) ⟨3007791, by rfl⟩ : syracuseStep 8020777 = 6015583) B6015583
theorem B10694369 : Blo 2225435 10694369 := bstep (se 2 (by rfl) ⟨4010388, by rfl⟩ : syracuseStep 10694369 = 8020777) B8020777
theorem B7129579 : Blo 2225435 7129579 := bstep (se 1 (by rfl) ⟨5347184, by rfl⟩ : syracuseStep 7129579 = 10694369) B10694369
theorem B9506105 : Blo 2225435 9506105 := bstep (se 2 (by rfl) ⟨3564789, by rfl⟩ : syracuseStep 9506105 = 7129579) B7129579
theorem B6337403 : Blo 2225435 6337403 := bstep (se 1 (by rfl) ⟨4753052, by rfl⟩ : syracuseStep 6337403 = 9506105) B9506105
theorem B4224935 : Blo 2225435 4224935 := bstep (se 1 (by rfl) ⟨3168701, by rfl⟩ : syracuseStep 4224935 = 6337403) B6337403
theorem B2816623 : Blo 2225435 2816623 := bstep (se 1 (by rfl) ⟨2112467, by rfl⟩ : syracuseStep 2816623 = 4224935) B4224935
theorem B3755497 : Blo 2225435 3755497 := bstep (se 2 (by rfl) ⟨1408311, by rfl⟩ : syracuseStep 3755497 = 2816623) B2816623
theorem B5007329 : Blo 2225435 5007329 := bstep (se 2 (by rfl) ⟨1877748, by rfl⟩ : syracuseStep 5007329 = 3755497) B3755497
theorem B3338219 : Blo 2225435 3338219 := bstep (se 1 (by rfl) ⟨2503664, by rfl⟩ : syracuseStep 3338219 = 5007329) B5007329
theorem B2225479 : Blo 2225435 2225479 := bstep (se 1 (by rfl) ⟨1669109, by rfl⟩ : syracuseStep 2225479 = 3338219) B3338219
theorem B2503669 : Blo 2225435 2503669 := bbase (se 5 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 2503669 = 234719) (by norm_num)
theorem B3338225 : Blo 2225435 3338225 := bstep (se 2 (by rfl) ⟨1251834, by rfl⟩ : syracuseStep 3338225 = 2503669) B2503669
theorem B2225483 : Blo 2225435 2225483 := bstep (se 1 (by rfl) ⟨1669112, by rfl⟩ : syracuseStep 2225483 = 3338225) B3338225
theorem B2816633 : Blo 2225435 2816633 := bbase (se 2 (by rfl) ⟨1056237, by rfl⟩ : syracuseStep 2816633 = 2112475) (by norm_num)
theorem B7511021 : Blo 2225435 7511021 := bstep (se 3 (by rfl) ⟨1408316, by rfl⟩ : syracuseStep 7511021 = 2816633) B2816633
theorem B5007347 : Blo 2225435 5007347 := bstep (se 1 (by rfl) ⟨3755510, by rfl⟩ : syracuseStep 5007347 = 7511021) B7511021
theorem B3338231 : Blo 2225435 3338231 := bstep (se 1 (by rfl) ⟨2503673, by rfl⟩ : syracuseStep 3338231 = 5007347) B5007347
theorem B2225487 : Blo 2225435 2225487 := bstep (se 1 (by rfl) ⟨1669115, by rfl⟩ : syracuseStep 2225487 = 3338231) B3338231
theorem B3338237 : Blo 2225435 3338237 := bbase (se 3 (by rfl) ⟨625919, by rfl⟩ : syracuseStep 3338237 = 1251839) (by norm_num)
theorem B2225491 : Blo 2225435 2225491 := bstep (se 1 (by rfl) ⟨1669118, by rfl⟩ : syracuseStep 2225491 = 3338237) B3338237
theorem B5007365 : Blo 2225435 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B3338243 : Blo 2225435 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2225495 : Blo 2225435 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B4224973 : Blo 2225435 4224973 := bbase (se 3 (by rfl) ⟨792182, by rfl⟩ : syracuseStep 4224973 = 1584365) (by norm_num)
theorem B5633297 : Blo 2225435 5633297 := bstep (se 2 (by rfl) ⟨2112486, by rfl⟩ : syracuseStep 5633297 = 4224973) B4224973
theorem B3755531 : Blo 2225435 3755531 := bstep (se 1 (by rfl) ⟨2816648, by rfl⟩ : syracuseStep 3755531 = 5633297) B5633297
theorem B2503687 : Blo 2225435 2503687 := bstep (se 1 (by rfl) ⟨1877765, by rfl⟩ : syracuseStep 2503687 = 3755531) B3755531
theorem B3338249 : Blo 2225435 3338249 := bstep (se 2 (by rfl) ⟨1251843, by rfl⟩ : syracuseStep 3338249 = 2503687) B2503687
theorem B2225499 : Blo 2225435 2225499 := bstep (se 1 (by rfl) ⟨1669124, by rfl⟩ : syracuseStep 2225499 = 3338249) B3338249
theorem B11266613 : Blo 2225435 11266613 := bbase (se 5 (by rfl) ⟨528122, by rfl⟩ : syracuseStep 11266613 = 1056245) (by norm_num)
theorem B7511075 : Blo 2225435 7511075 := bstep (se 1 (by rfl) ⟨5633306, by rfl⟩ : syracuseStep 7511075 = 11266613) B11266613
theorem B5007383 : Blo 2225435 5007383 := bstep (se 1 (by rfl) ⟨3755537, by rfl⟩ : syracuseStep 5007383 = 7511075) B7511075
theorem B3338255 : Blo 2225435 3338255 := bstep (se 1 (by rfl) ⟨2503691, by rfl⟩ : syracuseStep 3338255 = 5007383) B5007383
theorem B2225503 : Blo 2225435 2225503 := bstep (se 1 (by rfl) ⟨1669127, by rfl⟩ : syracuseStep 2225503 = 3338255) B3338255
theorem B3338261 : Blo 2225435 3338261 := bbase (se 6 (by rfl) ⟨78240, by rfl⟩ : syracuseStep 3338261 = 156481) (by norm_num)
theorem B2225507 : Blo 2225435 2225507 := bstep (se 1 (by rfl) ⟨1669130, by rfl⟩ : syracuseStep 2225507 = 3338261) B3338261
theorem B2855093 : Blo 2225435 2855093 := bbase (se 5 (by rfl) ⟨133832, by rfl⟩ : syracuseStep 2855093 = 267665) (by norm_num)
theorem B30454325 : Blo 2225435 30454325 := bstep (se 5 (by rfl) ⟨1427546, by rfl⟩ : syracuseStep 30454325 = 2855093) B2855093
theorem B20302883 : Blo 2225435 20302883 := bstep (se 1 (by rfl) ⟨15227162, by rfl⟩ : syracuseStep 20302883 = 30454325) B30454325
theorem B13535255 : Blo 2225435 13535255 := bstep (se 1 (by rfl) ⟨10151441, by rfl⟩ : syracuseStep 13535255 = 20302883) B20302883
theorem B9023503 : Blo 2225435 9023503 := bstep (se 1 (by rfl) ⟨6767627, by rfl⟩ : syracuseStep 9023503 = 13535255) B13535255
theorem B12031337 : Blo 2225435 12031337 := bstep (se 2 (by rfl) ⟨4511751, by rfl⟩ : syracuseStep 12031337 = 9023503) B9023503
theorem B8020891 : Blo 2225435 8020891 := bstep (se 1 (by rfl) ⟨6015668, by rfl⟩ : syracuseStep 8020891 = 12031337) B12031337
theorem B10694521 : Blo 2225435 10694521 := bstep (se 2 (by rfl) ⟨4010445, by rfl⟩ : syracuseStep 10694521 = 8020891) B8020891
theorem B14259361 : Blo 2225435 14259361 := bstep (se 2 (by rfl) ⟨5347260, by rfl⟩ : syracuseStep 14259361 = 10694521) B10694521
theorem B19012481 : Blo 2225435 19012481 := bstep (se 2 (by rfl) ⟨7129680, by rfl⟩ : syracuseStep 19012481 = 14259361) B14259361
theorem B12674987 : Blo 2225435 12674987 := bstep (se 1 (by rfl) ⟨9506240, by rfl⟩ : syracuseStep 12674987 = 19012481) B19012481
theorem B8449991 : Blo 2225435 8449991 := bstep (se 1 (by rfl) ⟨6337493, by rfl⟩ : syracuseStep 8449991 = 12674987) B12674987
theorem B5633327 : Blo 2225435 5633327 := bstep (se 1 (by rfl) ⟨4224995, by rfl⟩ : syracuseStep 5633327 = 8449991) B8449991
theorem B3755551 : Blo 2225435 3755551 := bstep (se 1 (by rfl) ⟨2816663, by rfl⟩ : syracuseStep 3755551 = 5633327) B5633327
theorem B5007401 : Blo 2225435 5007401 := bstep (se 2 (by rfl) ⟨1877775, by rfl⟩ : syracuseStep 5007401 = 3755551) B3755551
theorem B3338267 : Blo 2225435 3338267 := bstep (se 1 (by rfl) ⟨2503700, by rfl⟩ : syracuseStep 3338267 = 5007401) B5007401
theorem B2225511 : Blo 2225435 2225511 := bstep (se 1 (by rfl) ⟨1669133, by rfl⟩ : syracuseStep 2225511 = 3338267) B3338267
theorem B2503705 : Blo 2225435 2503705 := bbase (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) (by norm_num)
theorem B3338273 : Blo 2225435 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B2225515 : Blo 2225435 2225515 := bstep (se 1 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 2225515 = 3338273) B3338273
theorem B8450021 : Blo 2225435 8450021 := bbase (se 4 (by rfl) ⟨792189, by rfl⟩ : syracuseStep 8450021 = 1584379) (by norm_num)
theorem B5633347 : Blo 2225435 5633347 := bstep (se 1 (by rfl) ⟨4225010, by rfl⟩ : syracuseStep 5633347 = 8450021) B8450021
theorem B7511129 : Blo 2225435 7511129 := bstep (se 2 (by rfl) ⟨2816673, by rfl⟩ : syracuseStep 7511129 = 5633347) B5633347
theorem B5007419 : Blo 2225435 5007419 := bstep (se 1 (by rfl) ⟨3755564, by rfl⟩ : syracuseStep 5007419 = 7511129) B7511129
theorem B3338279 : Blo 2225435 3338279 := bstep (se 1 (by rfl) ⟨2503709, by rfl⟩ : syracuseStep 3338279 = 5007419) B5007419
theorem B2225519 : Blo 2225435 2225519 := bstep (se 1 (by rfl) ⟨1669139, by rfl⟩ : syracuseStep 2225519 = 3338279) B3338279
theorem B3338285 : Blo 2225435 3338285 := bbase (se 3 (by rfl) ⟨625928, by rfl⟩ : syracuseStep 3338285 = 1251857) (by norm_num)
theorem B2225523 : Blo 2225435 2225523 := bstep (se 1 (by rfl) ⟨1669142, by rfl⟩ : syracuseStep 2225523 = 3338285) B3338285
theorem B5007437 : Blo 2225435 5007437 := bbase (se 3 (by rfl) ⟨938894, by rfl⟩ : syracuseStep 5007437 = 1877789) (by norm_num)
theorem B3338291 : Blo 2225435 3338291 := bstep (se 1 (by rfl) ⟨2503718, by rfl⟩ : syracuseStep 3338291 = 5007437) B5007437
theorem B2225527 : Blo 2225435 2225527 := bstep (se 1 (by rfl) ⟨1669145, by rfl⟩ : syracuseStep 2225527 = 3338291) B3338291
theorem B2816689 : Blo 2225435 2816689 := bbase (se 2 (by rfl) ⟨1056258, by rfl⟩ : syracuseStep 2816689 = 2112517) (by norm_num)
theorem B3755585 : Blo 2225435 3755585 := bstep (se 2 (by rfl) ⟨1408344, by rfl⟩ : syracuseStep 3755585 = 2816689) B2816689
theorem B2503723 : Blo 2225435 2503723 := bstep (se 1 (by rfl) ⟨1877792, by rfl⟩ : syracuseStep 2503723 = 3755585) B3755585
theorem B3338297 : Blo 2225435 3338297 := bstep (se 2 (by rfl) ⟨1251861, by rfl⟩ : syracuseStep 3338297 = 2503723) B2503723
theorem B2225531 : Blo 2225435 2225531 := bstep (se 1 (by rfl) ⟨1669148, by rfl⟩ : syracuseStep 2225531 = 3338297) B3338297
theorem B2855125 : Blo 2225435 2855125 := bbase (se 7 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 2855125 = 66917) (by norm_num)
theorem B3806833 : Blo 2225435 3806833 := bstep (se 2 (by rfl) ⟨1427562, by rfl⟩ : syracuseStep 3806833 = 2855125) B2855125
theorem B5075777 : Blo 2225435 5075777 := bstep (se 2 (by rfl) ⟨1903416, by rfl⟩ : syracuseStep 5075777 = 3806833) B3806833
theorem B3383851 : Blo 2225435 3383851 := bstep (se 1 (by rfl) ⟨2537888, by rfl⟩ : syracuseStep 3383851 = 5075777) B5075777
theorem B4511801 : Blo 2225435 4511801 := bstep (se 2 (by rfl) ⟨1691925, by rfl⟩ : syracuseStep 4511801 = 3383851) B3383851
theorem B3007867 : Blo 2225435 3007867 := bstep (se 1 (by rfl) ⟨2255900, by rfl⟩ : syracuseStep 3007867 = 4511801) B4511801
theorem B4010489 : Blo 2225435 4010489 := bstep (se 2 (by rfl) ⟨1503933, by rfl⟩ : syracuseStep 4010489 = 3007867) B3007867
theorem B2673659 : Blo 2225435 2673659 := bstep (se 1 (by rfl) ⟨2005244, by rfl⟩ : syracuseStep 2673659 = 4010489) B4010489
theorem B7129757 : Blo 2225435 7129757 := bstep (se 3 (by rfl) ⟨1336829, by rfl⟩ : syracuseStep 7129757 = 2673659) B2673659
theorem B4753171 : Blo 2225435 4753171 := bstep (se 1 (by rfl) ⟨3564878, by rfl⟩ : syracuseStep 4753171 = 7129757) B7129757
theorem B25350245 : Blo 2225435 25350245 := bstep (se 4 (by rfl) ⟨2376585, by rfl⟩ : syracuseStep 25350245 = 4753171) B4753171
theorem B16900163 : Blo 2225435 16900163 := bstep (se 1 (by rfl) ⟨12675122, by rfl⟩ : syracuseStep 16900163 = 25350245) B25350245
theorem B11266775 : Blo 2225435 11266775 := bstep (se 1 (by rfl) ⟨8450081, by rfl⟩ : syracuseStep 11266775 = 16900163) B16900163
theorem B7511183 : Blo 2225435 7511183 := bstep (se 1 (by rfl) ⟨5633387, by rfl⟩ : syracuseStep 7511183 = 11266775) B11266775
theorem B5007455 : Blo 2225435 5007455 := bstep (se 1 (by rfl) ⟨3755591, by rfl⟩ : syracuseStep 5007455 = 7511183) B7511183
theorem B3338303 : Blo 2225435 3338303 := bstep (se 1 (by rfl) ⟨2503727, by rfl⟩ : syracuseStep 3338303 = 5007455) B5007455
theorem B2225535 : Blo 2225435 2225535 := bstep (se 1 (by rfl) ⟨1669151, by rfl⟩ : syracuseStep 2225535 = 3338303) B3338303
theorem B3338309 : Blo 2225435 3338309 := bbase (se 4 (by rfl) ⟨312966, by rfl⟩ : syracuseStep 3338309 = 625933) (by norm_num)
theorem B2225539 : Blo 2225435 2225539 := bstep (se 1 (by rfl) ⟨1669154, by rfl⟩ : syracuseStep 2225539 = 3338309) B3338309
theorem B3755605 : Blo 2225435 3755605 := bbase (se 8 (by rfl) ⟨22005, by rfl⟩ : syracuseStep 3755605 = 44011) (by norm_num)
theorem B5007473 : Blo 2225435 5007473 := bstep (se 2 (by rfl) ⟨1877802, by rfl⟩ : syracuseStep 5007473 = 3755605) B3755605
theorem B3338315 : Blo 2225435 3338315 := bstep (se 1 (by rfl) ⟨2503736, by rfl⟩ : syracuseStep 3338315 = 5007473) B5007473
theorem B2225543 : Blo 2225435 2225543 := bstep (se 1 (by rfl) ⟨1669157, by rfl⟩ : syracuseStep 2225543 = 3338315) B3338315
theorem B2503741 : Blo 2225435 2503741 := bbase (se 3 (by rfl) ⟨469451, by rfl⟩ : syracuseStep 2503741 = 938903) (by norm_num)
theorem B3338321 : Blo 2225435 3338321 := bstep (se 2 (by rfl) ⟨1251870, by rfl⟩ : syracuseStep 3338321 = 2503741) B2503741
theorem B2225547 : Blo 2225435 2225547 := bstep (se 1 (by rfl) ⟨1669160, by rfl⟩ : syracuseStep 2225547 = 3338321) B3338321
theorem B7511237 : Blo 2225435 7511237 := bbase (se 4 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 7511237 = 1408357) (by norm_num)
theorem B5007491 : Blo 2225435 5007491 := bstep (se 1 (by rfl) ⟨3755618, by rfl⟩ : syracuseStep 5007491 = 7511237) B7511237
theorem B3338327 : Blo 2225435 3338327 := bstep (se 1 (by rfl) ⟨2503745, by rfl⟩ : syracuseStep 3338327 = 5007491) B5007491
theorem B2225551 : Blo 2225435 2225551 := bstep (se 1 (by rfl) ⟨1669163, by rfl⟩ : syracuseStep 2225551 = 3338327) B3338327
theorem B3338333 : Blo 2225435 3338333 := bbase (se 3 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 3338333 = 1251875) (by norm_num)
theorem B2225555 : Blo 2225435 2225555 := bstep (se 1 (by rfl) ⟨1669166, by rfl⟩ : syracuseStep 2225555 = 3338333) B3338333
theorem B5007509 : Blo 2225435 5007509 := bbase (se 6 (by rfl) ⟨117363, by rfl⟩ : syracuseStep 5007509 = 234727) (by norm_num)
theorem B3338339 : Blo 2225435 3338339 := bstep (se 1 (by rfl) ⟨2503754, by rfl⟩ : syracuseStep 3338339 = 5007509) B5007509
theorem B2225559 : Blo 2225435 2225559 := bstep (se 1 (by rfl) ⟨1669169, by rfl⟩ : syracuseStep 2225559 = 3338339) B3338339
theorem B3168821 : Blo 2225435 3168821 := bbase (se 5 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 3168821 = 297077) (by norm_num)
theorem B8450189 : Blo 2225435 8450189 := bstep (se 3 (by rfl) ⟨1584410, by rfl⟩ : syracuseStep 8450189 = 3168821) B3168821
theorem B5633459 : Blo 2225435 5633459 := bstep (se 1 (by rfl) ⟨4225094, by rfl⟩ : syracuseStep 5633459 = 8450189) B8450189
theorem B3755639 : Blo 2225435 3755639 := bstep (se 1 (by rfl) ⟨2816729, by rfl⟩ : syracuseStep 3755639 = 5633459) B5633459
theorem B2503759 : Blo 2225435 2503759 := bstep (se 1 (by rfl) ⟨1877819, by rfl⟩ : syracuseStep 2503759 = 3755639) B3755639
theorem B3338345 : Blo 2225435 3338345 := bstep (se 2 (by rfl) ⟨1251879, by rfl⟩ : syracuseStep 3338345 = 2503759) B2503759
theorem B2225563 : Blo 2225435 2225563 := bstep (se 1 (by rfl) ⟨1669172, by rfl⟩ : syracuseStep 2225563 = 3338345) B3338345
theorem B6767797 : Blo 2225435 6767797 := bbase (se 5 (by rfl) ⟨317240, by rfl⟩ : syracuseStep 6767797 = 634481) (by norm_num)
theorem B9023729 : Blo 2225435 9023729 := bstep (se 2 (by rfl) ⟨3383898, by rfl⟩ : syracuseStep 9023729 = 6767797) B6767797
theorem B24063277 : Blo 2225435 24063277 := bstep (se 3 (by rfl) ⟨4511864, by rfl⟩ : syracuseStep 24063277 = 9023729) B9023729
theorem B32084369 : Blo 2225435 32084369 := bstep (se 2 (by rfl) ⟨12031638, by rfl⟩ : syracuseStep 32084369 = 24063277) B24063277
theorem B21389579 : Blo 2225435 21389579 := bstep (se 1 (by rfl) ⟨16042184, by rfl⟩ : syracuseStep 21389579 = 32084369) B32084369
theorem B14259719 : Blo 2225435 14259719 := bstep (se 1 (by rfl) ⟨10694789, by rfl⟩ : syracuseStep 14259719 = 21389579) B21389579
theorem B9506479 : Blo 2225435 9506479 := bstep (se 1 (by rfl) ⟨7129859, by rfl⟩ : syracuseStep 9506479 = 14259719) B14259719
theorem B12675305 : Blo 2225435 12675305 := bstep (se 2 (by rfl) ⟨4753239, by rfl⟩ : syracuseStep 12675305 = 9506479) B9506479
theorem B8450203 : Blo 2225435 8450203 := bstep (se 1 (by rfl) ⟨6337652, by rfl⟩ : syracuseStep 8450203 = 12675305) B12675305
theorem B11266937 : Blo 2225435 11266937 := bstep (se 2 (by rfl) ⟨4225101, by rfl⟩ : syracuseStep 11266937 = 8450203) B8450203
theorem B7511291 : Blo 2225435 7511291 := bstep (se 1 (by rfl) ⟨5633468, by rfl⟩ : syracuseStep 7511291 = 11266937) B11266937
theorem B5007527 : Blo 2225435 5007527 := bstep (se 1 (by rfl) ⟨3755645, by rfl⟩ : syracuseStep 5007527 = 7511291) B7511291
theorem B3338351 : Blo 2225435 3338351 := bstep (se 1 (by rfl) ⟨2503763, by rfl⟩ : syracuseStep 3338351 = 5007527) B5007527
theorem B2225567 : Blo 2225435 2225567 := bstep (se 1 (by rfl) ⟨1669175, by rfl⟩ : syracuseStep 2225567 = 3338351) B3338351
theorem B3338357 : Blo 2225435 3338357 := bbase (se 5 (by rfl) ⟨156485, by rfl⟩ : syracuseStep 3338357 = 312971) (by norm_num)
theorem B2225571 : Blo 2225435 2225571 := bstep (se 1 (by rfl) ⟨1669178, by rfl⟩ : syracuseStep 2225571 = 3338357) B3338357
theorem B4225117 : Blo 2225435 4225117 := bbase (se 3 (by rfl) ⟨792209, by rfl⟩ : syracuseStep 4225117 = 1584419) (by norm_num)
theorem B5633489 : Blo 2225435 5633489 := bstep (se 2 (by rfl) ⟨2112558, by rfl⟩ : syracuseStep 5633489 = 4225117) B4225117
theorem B3755659 : Blo 2225435 3755659 := bstep (se 1 (by rfl) ⟨2816744, by rfl⟩ : syracuseStep 3755659 = 5633489) B5633489
theorem B5007545 : Blo 2225435 5007545 := bstep (se 2 (by rfl) ⟨1877829, by rfl⟩ : syracuseStep 5007545 = 3755659) B3755659
theorem B3338363 : Blo 2225435 3338363 := bstep (se 1 (by rfl) ⟨2503772, by rfl⟩ : syracuseStep 3338363 = 5007545) B5007545
theorem B2225575 : Blo 2225435 2225575 := bstep (se 1 (by rfl) ⟨1669181, by rfl⟩ : syracuseStep 2225575 = 3338363) B3338363
theorem B2503777 : Blo 2225435 2503777 := bbase (se 2 (by rfl) ⟨938916, by rfl⟩ : syracuseStep 2503777 = 1877833) (by norm_num)
theorem B3338369 : Blo 2225435 3338369 := bstep (se 2 (by rfl) ⟨1251888, by rfl⟩ : syracuseStep 3338369 = 2503777) B2503777
theorem B2225579 : Blo 2225435 2225579 := bstep (se 1 (by rfl) ⟨1669184, by rfl⟩ : syracuseStep 2225579 = 3338369) B3338369
theorem B5633509 : Blo 2225435 5633509 := bbase (se 4 (by rfl) ⟨528141, by rfl⟩ : syracuseStep 5633509 = 1056283) (by norm_num)
theorem B7511345 : Blo 2225435 7511345 := bstep (se 2 (by rfl) ⟨2816754, by rfl⟩ : syracuseStep 7511345 = 5633509) B5633509
theorem B5007563 : Blo 2225435 5007563 := bstep (se 1 (by rfl) ⟨3755672, by rfl⟩ : syracuseStep 5007563 = 7511345) B7511345
theorem B3338375 : Blo 2225435 3338375 := bstep (se 1 (by rfl) ⟨2503781, by rfl⟩ : syracuseStep 3338375 = 5007563) B5007563
theorem B2225583 : Blo 2225435 2225583 := bstep (se 1 (by rfl) ⟨1669187, by rfl⟩ : syracuseStep 2225583 = 3338375) B3338375
theorem B3338381 : Blo 2225435 3338381 := bbase (se 3 (by rfl) ⟨625946, by rfl⟩ : syracuseStep 3338381 = 1251893) (by norm_num)
theorem B2225587 : Blo 2225435 2225587 := bstep (se 1 (by rfl) ⟨1669190, by rfl⟩ : syracuseStep 2225587 = 3338381) B3338381
theorem B5007581 : Blo 2225435 5007581 := bbase (se 3 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 5007581 = 1877843) (by norm_num)
theorem B3338387 : Blo 2225435 3338387 := bstep (se 1 (by rfl) ⟨2503790, by rfl⟩ : syracuseStep 3338387 = 5007581) B5007581
theorem B2225591 : Blo 2225435 2225591 := bstep (se 1 (by rfl) ⟨1669193, by rfl⟩ : syracuseStep 2225591 = 3338387) B3338387
theorem B3755693 : Blo 2225435 3755693 := bbase (se 3 (by rfl) ⟨704192, by rfl⟩ : syracuseStep 3755693 = 1408385) (by norm_num)
theorem B2503795 : Blo 2225435 2503795 := bstep (se 1 (by rfl) ⟨1877846, by rfl⟩ : syracuseStep 2503795 = 3755693) B3755693
theorem B3338393 : Blo 2225435 3338393 := bstep (se 2 (by rfl) ⟨1251897, by rfl⟩ : syracuseStep 3338393 = 2503795) B2503795
theorem B2225595 : Blo 2225435 2225595 := bstep (se 1 (by rfl) ⟨1669196, by rfl⟩ : syracuseStep 2225595 = 3338393) B3338393
theorem B11420821 : Blo 2225435 11420821 := bbase (se 6 (by rfl) ⟨267675, by rfl⟩ : syracuseStep 11420821 = 535351) (by norm_num)
theorem B15227761 : Blo 2225435 15227761 := bstep (se 2 (by rfl) ⟨5710410, by rfl⟩ : syracuseStep 15227761 = 11420821) B11420821
theorem B20303681 : Blo 2225435 20303681 := bstep (se 2 (by rfl) ⟨7613880, by rfl⟩ : syracuseStep 20303681 = 15227761) B15227761
theorem B54143149 : Blo 2225435 54143149 := bstep (se 3 (by rfl) ⟨10151840, by rfl⟩ : syracuseStep 54143149 = 20303681) B20303681
theorem B72190865 : Blo 2225435 72190865 := bstep (se 2 (by rfl) ⟨27071574, by rfl⟩ : syracuseStep 72190865 = 54143149) B54143149
theorem B48127243 : Blo 2225435 48127243 := bstep (se 1 (by rfl) ⟨36095432, by rfl⟩ : syracuseStep 48127243 = 72190865) B72190865
theorem B64169657 : Blo 2225435 64169657 := bstep (se 2 (by rfl) ⟨24063621, by rfl⟩ : syracuseStep 64169657 = 48127243) B48127243
theorem B42779771 : Blo 2225435 42779771 := bstep (se 1 (by rfl) ⟨32084828, by rfl⟩ : syracuseStep 42779771 = 64169657) B64169657
theorem B28519847 : Blo 2225435 28519847 := bstep (se 1 (by rfl) ⟨21389885, by rfl⟩ : syracuseStep 28519847 = 42779771) B42779771
theorem B19013231 : Blo 2225435 19013231 := bstep (se 1 (by rfl) ⟨14259923, by rfl⟩ : syracuseStep 19013231 = 28519847) B28519847
theorem B12675487 : Blo 2225435 12675487 := bstep (se 1 (by rfl) ⟨9506615, by rfl⟩ : syracuseStep 12675487 = 19013231) B19013231
theorem B16900649 : Blo 2225435 16900649 := bstep (se 2 (by rfl) ⟨6337743, by rfl⟩ : syracuseStep 16900649 = 12675487) B12675487
theorem B11267099 : Blo 2225435 11267099 := bstep (se 1 (by rfl) ⟨8450324, by rfl⟩ : syracuseStep 11267099 = 16900649) B16900649
theorem B7511399 : Blo 2225435 7511399 := bstep (se 1 (by rfl) ⟨5633549, by rfl⟩ : syracuseStep 7511399 = 11267099) B11267099
theorem B5007599 : Blo 2225435 5007599 := bstep (se 1 (by rfl) ⟨3755699, by rfl⟩ : syracuseStep 5007599 = 7511399) B7511399
theorem B3338399 : Blo 2225435 3338399 := bstep (se 1 (by rfl) ⟨2503799, by rfl⟩ : syracuseStep 3338399 = 5007599) B5007599
theorem B2225599 : Blo 2225435 2225599 := bstep (se 1 (by rfl) ⟨1669199, by rfl⟩ : syracuseStep 2225599 = 3338399) B3338399
theorem B3338405 : Blo 2225435 3338405 := bbase (se 4 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 3338405 = 625951) (by norm_num)
theorem B2225603 : Blo 2225435 2225603 := bstep (se 1 (by rfl) ⟨1669202, by rfl⟩ : syracuseStep 2225603 = 3338405) B3338405
theorem B2816785 : Blo 2225435 2816785 := bbase (se 2 (by rfl) ⟨1056294, by rfl⟩ : syracuseStep 2816785 = 2112589) (by norm_num)
theorem B3755713 : Blo 2225435 3755713 := bstep (se 2 (by rfl) ⟨1408392, by rfl⟩ : syracuseStep 3755713 = 2816785) B2816785
theorem B5007617 : Blo 2225435 5007617 := bstep (se 2 (by rfl) ⟨1877856, by rfl⟩ : syracuseStep 5007617 = 3755713) B3755713
theorem B3338411 : Blo 2225435 3338411 := bstep (se 1 (by rfl) ⟨2503808, by rfl⟩ : syracuseStep 3338411 = 5007617) B5007617
theorem B2225607 : Blo 2225435 2225607 := bstep (se 1 (by rfl) ⟨1669205, by rfl⟩ : syracuseStep 2225607 = 3338411) B3338411
theorem B2503813 : Blo 2225435 2503813 := bbase (se 4 (by rfl) ⟨234732, by rfl⟩ : syracuseStep 2503813 = 469465) (by norm_num)
theorem B3338417 : Blo 2225435 3338417 := bstep (se 2 (by rfl) ⟨1251906, by rfl⟩ : syracuseStep 3338417 = 2503813) B2503813
theorem B2225611 : Blo 2225435 2225611 := bstep (se 1 (by rfl) ⟨1669208, by rfl⟩ : syracuseStep 2225611 = 3338417) B3338417
theorem B4818197 : Blo 2225435 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B3212131 : Blo 2225435 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B4282841 : Blo 2225435 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B2855227 : Blo 2225435 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B3806969 : Blo 2225435 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B40607669 : Blo 2225435 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B27071779 : Blo 2225435 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B36095705 : Blo 2225435 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B24063803 : Blo 2225435 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B16042535 : Blo 2225435 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B10695023 : Blo 2225435 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B7130015 : Blo 2225435 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B4753343 : Blo 2225435 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B3168895 : Blo 2225435 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B4225193 : Blo 2225435 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B2816795 : Blo 2225435 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B7511453 : Blo 2225435 7511453 := bstep (se 3 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 7511453 = 2816795) B2816795
theorem B5007635 : Blo 2225435 5007635 := bstep (se 1 (by rfl) ⟨3755726, by rfl⟩ : syracuseStep 5007635 = 7511453) B7511453
theorem B3338423 : Blo 2225435 3338423 := bstep (se 1 (by rfl) ⟨2503817, by rfl⟩ : syracuseStep 3338423 = 5007635) B5007635
theorem B2225615 : Blo 2225435 2225615 := bstep (se 1 (by rfl) ⟨1669211, by rfl⟩ : syracuseStep 2225615 = 3338423) B3338423
theorem B3338429 : Blo 2225435 3338429 := bbase (se 3 (by rfl) ⟨625955, by rfl⟩ : syracuseStep 3338429 = 1251911) (by norm_num)
theorem B2225619 : Blo 2225435 2225619 := bstep (se 1 (by rfl) ⟨1669214, by rfl⟩ : syracuseStep 2225619 = 3338429) B3338429
theorem B5007653 : Blo 2225435 5007653 := bbase (se 4 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 5007653 = 938935) (by norm_num)
theorem B3338435 : Blo 2225435 3338435 := bstep (se 1 (by rfl) ⟨2503826, by rfl⟩ : syracuseStep 3338435 = 5007653) B5007653
theorem B2225623 : Blo 2225435 2225623 := bstep (se 1 (by rfl) ⟨1669217, by rfl⟩ : syracuseStep 2225623 = 3338435) B3338435
theorem B5633621 : Blo 2225435 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B3755747 : Blo 2225435 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B2503831 : Blo 2225435 2503831 := bstep (se 1 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 2503831 = 3755747) B3755747
theorem B3338441 : Blo 2225435 3338441 := bstep (se 2 (by rfl) ⟨1251915, by rfl⟩ : syracuseStep 3338441 = 2503831) B2503831
theorem B2225627 : Blo 2225435 2225627 := bstep (se 1 (by rfl) ⟨1669220, by rfl⟩ : syracuseStep 2225627 = 3338441) B3338441
theorem B5347549 : Blo 2225435 5347549 := bbase (se 3 (by rfl) ⟨1002665, by rfl⟩ : syracuseStep 5347549 = 2005331) (by norm_num)
theorem B7130065 : Blo 2225435 7130065 := bstep (se 2 (by rfl) ⟨2673774, by rfl⟩ : syracuseStep 7130065 = 5347549) B5347549
theorem B9506753 : Blo 2225435 9506753 := bstep (se 2 (by rfl) ⟨3565032, by rfl⟩ : syracuseStep 9506753 = 7130065) B7130065
theorem B6337835 : Blo 2225435 6337835 := bstep (se 1 (by rfl) ⟨4753376, by rfl⟩ : syracuseStep 6337835 = 9506753) B9506753
theorem B4225223 : Blo 2225435 4225223 := bstep (se 1 (by rfl) ⟨3168917, by rfl⟩ : syracuseStep 4225223 = 6337835) B6337835
theorem B11267261 : Blo 2225435 11267261 := bstep (se 3 (by rfl) ⟨2112611, by rfl⟩ : syracuseStep 11267261 = 4225223) B4225223
theorem B7511507 : Blo 2225435 7511507 := bstep (se 1 (by rfl) ⟨5633630, by rfl⟩ : syracuseStep 7511507 = 11267261) B11267261
theorem B5007671 : Blo 2225435 5007671 := bstep (se 1 (by rfl) ⟨3755753, by rfl⟩ : syracuseStep 5007671 = 7511507) B7511507
theorem B3338447 : Blo 2225435 3338447 := bstep (se 1 (by rfl) ⟨2503835, by rfl⟩ : syracuseStep 3338447 = 5007671) B5007671
theorem B2225631 : Blo 2225435 2225631 := bstep (se 1 (by rfl) ⟨1669223, by rfl⟩ : syracuseStep 2225631 = 3338447) B3338447
theorem B3338453 : Blo 2225435 3338453 := bbase (se 7 (by rfl) ⟨39122, by rfl⟩ : syracuseStep 3338453 = 78245) (by norm_num)
theorem B2225635 : Blo 2225435 2225635 := bstep (se 1 (by rfl) ⟨1669226, by rfl⟩ : syracuseStep 2225635 = 3338453) B3338453
theorem B2376697 : Blo 2225435 2376697 := bbase (se 2 (by rfl) ⟨891261, by rfl⟩ : syracuseStep 2376697 = 1782523) (by norm_num)
theorem B3168929 : Blo 2225435 3168929 := bstep (se 2 (by rfl) ⟨1188348, by rfl⟩ : syracuseStep 3168929 = 2376697) B2376697
theorem B8450477 : Blo 2225435 8450477 := bstep (se 3 (by rfl) ⟨1584464, by rfl⟩ : syracuseStep 8450477 = 3168929) B3168929
theorem B5633651 : Blo 2225435 5633651 := bstep (se 1 (by rfl) ⟨4225238, by rfl⟩ : syracuseStep 5633651 = 8450477) B8450477
theorem B3755767 : Blo 2225435 3755767 := bstep (se 1 (by rfl) ⟨2816825, by rfl⟩ : syracuseStep 3755767 = 5633651) B5633651
theorem B5007689 : Blo 2225435 5007689 := bstep (se 2 (by rfl) ⟨1877883, by rfl⟩ : syracuseStep 5007689 = 3755767) B3755767
theorem B3338459 : Blo 2225435 3338459 := bstep (se 1 (by rfl) ⟨2503844, by rfl⟩ : syracuseStep 3338459 = 5007689) B5007689
theorem B2225639 : Blo 2225435 2225639 := bstep (se 1 (by rfl) ⟨1669229, by rfl⟩ : syracuseStep 2225639 = 3338459) B3338459
theorem B2503849 : Blo 2225435 2503849 := bbase (se 2 (by rfl) ⟨938943, by rfl⟩ : syracuseStep 2503849 = 1877887) (by norm_num)
theorem B3338465 : Blo 2225435 3338465 := bstep (se 2 (by rfl) ⟨1251924, by rfl⟩ : syracuseStep 3338465 = 2503849) B2503849
theorem B2225643 : Blo 2225435 2225643 := bstep (se 1 (by rfl) ⟨1669232, by rfl⟩ : syracuseStep 2225643 = 3338465) B3338465
theorem B9506821 : Blo 2225435 9506821 := bbase (se 4 (by rfl) ⟨891264, by rfl⟩ : syracuseStep 9506821 = 1782529) (by norm_num)
theorem B12675761 : Blo 2225435 12675761 := bstep (se 2 (by rfl) ⟨4753410, by rfl⟩ : syracuseStep 12675761 = 9506821) B9506821
theorem B8450507 : Blo 2225435 8450507 := bstep (se 1 (by rfl) ⟨6337880, by rfl⟩ : syracuseStep 8450507 = 12675761) B12675761
theorem B5633671 : Blo 2225435 5633671 := bstep (se 1 (by rfl) ⟨4225253, by rfl⟩ : syracuseStep 5633671 = 8450507) B8450507
theorem B7511561 : Blo 2225435 7511561 := bstep (se 2 (by rfl) ⟨2816835, by rfl⟩ : syracuseStep 7511561 = 5633671) B5633671
theorem B5007707 : Blo 2225435 5007707 := bstep (se 1 (by rfl) ⟨3755780, by rfl⟩ : syracuseStep 5007707 = 7511561) B7511561
theorem B3338471 : Blo 2225435 3338471 := bstep (se 1 (by rfl) ⟨2503853, by rfl⟩ : syracuseStep 3338471 = 5007707) B5007707
theorem B2225647 : Blo 2225435 2225647 := bstep (se 1 (by rfl) ⟨1669235, by rfl⟩ : syracuseStep 2225647 = 3338471) B3338471
theorem B3338477 : Blo 2225435 3338477 := bbase (se 3 (by rfl) ⟨625964, by rfl⟩ : syracuseStep 3338477 = 1251929) (by norm_num)
theorem B2225651 : Blo 2225435 2225651 := bstep (se 1 (by rfl) ⟨1669238, by rfl⟩ : syracuseStep 2225651 = 3338477) B3338477
theorem B5007725 : Blo 2225435 5007725 := bbase (se 3 (by rfl) ⟨938948, by rfl⟩ : syracuseStep 5007725 = 1877897) (by norm_num)
theorem B3338483 : Blo 2225435 3338483 := bstep (se 1 (by rfl) ⟨2503862, by rfl⟩ : syracuseStep 3338483 = 5007725) B5007725
theorem B2225655 : Blo 2225435 2225655 := bstep (se 1 (by rfl) ⟨1669241, by rfl⟩ : syracuseStep 2225655 = 3338483) B3338483
theorem B4225277 : Blo 2225435 4225277 := bbase (se 3 (by rfl) ⟨792239, by rfl⟩ : syracuseStep 4225277 = 1584479) (by norm_num)
theorem B2816851 : Blo 2225435 2816851 := bstep (se 1 (by rfl) ⟨2112638, by rfl⟩ : syracuseStep 2816851 = 4225277) B4225277
theorem B3755801 : Blo 2225435 3755801 := bstep (se 2 (by rfl) ⟨1408425, by rfl⟩ : syracuseStep 3755801 = 2816851) B2816851
theorem B2503867 : Blo 2225435 2503867 := bstep (se 1 (by rfl) ⟨1877900, by rfl⟩ : syracuseStep 2503867 = 3755801) B3755801
theorem B3338489 : Blo 2225435 3338489 := bstep (se 2 (by rfl) ⟨1251933, by rfl⟩ : syracuseStep 3338489 = 2503867) B2503867
theorem B2225659 : Blo 2225435 2225659 := bstep (se 1 (by rfl) ⟨1669244, by rfl⟩ : syracuseStep 2225659 = 3338489) B3338489
theorem B7614101 : Blo 2225435 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B20304269 : Blo 2225435 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B13536179 : Blo 2225435 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B9024119 : Blo 2225435 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B6016079 : Blo 2225435 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B4010719 : Blo 2225435 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B5347625 : Blo 2225435 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B57041333 : Blo 2225435 57041333 := bstep (se 5 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 57041333 = 5347625) B5347625
theorem B38027555 : Blo 2225435 38027555 := bstep (se 1 (by rfl) ⟨28520666, by rfl⟩ : syracuseStep 38027555 = 57041333) B57041333
theorem B25351703 : Blo 2225435 25351703 := bstep (se 1 (by rfl) ⟨19013777, by rfl⟩ : syracuseStep 25351703 = 38027555) B38027555
theorem B16901135 : Blo 2225435 16901135 := bstep (se 1 (by rfl) ⟨12675851, by rfl⟩ : syracuseStep 16901135 = 25351703) B25351703
theorem B11267423 : Blo 2225435 11267423 := bstep (se 1 (by rfl) ⟨8450567, by rfl⟩ : syracuseStep 11267423 = 16901135) B16901135
theorem B7511615 : Blo 2225435 7511615 := bstep (se 1 (by rfl) ⟨5633711, by rfl⟩ : syracuseStep 7511615 = 11267423) B11267423
theorem B5007743 : Blo 2225435 5007743 := bstep (se 1 (by rfl) ⟨3755807, by rfl⟩ : syracuseStep 5007743 = 7511615) B7511615
theorem B3338495 : Blo 2225435 3338495 := bstep (se 1 (by rfl) ⟨2503871, by rfl⟩ : syracuseStep 3338495 = 5007743) B5007743
theorem B2225663 : Blo 2225435 2225663 := bstep (se 1 (by rfl) ⟨1669247, by rfl⟩ : syracuseStep 2225663 = 3338495) B3338495
theorem B3338501 : Blo 2225435 3338501 := bbase (se 4 (by rfl) ⟨312984, by rfl⟩ : syracuseStep 3338501 = 625969) (by norm_num)
theorem B2225667 : Blo 2225435 2225667 := bstep (se 1 (by rfl) ⟨1669250, by rfl⟩ : syracuseStep 2225667 = 3338501) B3338501
theorem B3755821 : Blo 2225435 3755821 := bbase (se 3 (by rfl) ⟨704216, by rfl⟩ : syracuseStep 3755821 = 1408433) (by norm_num)
theorem B5007761 : Blo 2225435 5007761 := bstep (se 2 (by rfl) ⟨1877910, by rfl⟩ : syracuseStep 5007761 = 3755821) B3755821
theorem B3338507 : Blo 2225435 3338507 := bstep (se 1 (by rfl) ⟨2503880, by rfl⟩ : syracuseStep 3338507 = 5007761) B5007761
theorem B2225671 : Blo 2225435 2225671 := bstep (se 1 (by rfl) ⟨1669253, by rfl⟩ : syracuseStep 2225671 = 3338507) B3338507
theorem B2503885 : Blo 2225435 2503885 := bbase (se 3 (by rfl) ⟨469478, by rfl⟩ : syracuseStep 2503885 = 938957) (by norm_num)
theorem B3338513 : Blo 2225435 3338513 := bstep (se 2 (by rfl) ⟨1251942, by rfl⟩ : syracuseStep 3338513 = 2503885) B2503885
theorem B2225675 : Blo 2225435 2225675 := bstep (se 1 (by rfl) ⟨1669256, by rfl⟩ : syracuseStep 2225675 = 3338513) B3338513
theorem B7511669 : Blo 2225435 7511669 := bbase (se 5 (by rfl) ⟨352109, by rfl⟩ : syracuseStep 7511669 = 704219) (by norm_num)
theorem B5007779 : Blo 2225435 5007779 := bstep (se 1 (by rfl) ⟨3755834, by rfl⟩ : syracuseStep 5007779 = 7511669) B7511669
theorem B3338519 : Blo 2225435 3338519 := bstep (se 1 (by rfl) ⟨2503889, by rfl⟩ : syracuseStep 3338519 = 5007779) B5007779
theorem B2225679 : Blo 2225435 2225679 := bstep (se 1 (by rfl) ⟨1669259, by rfl⟩ : syracuseStep 2225679 = 3338519) B3338519
theorem B3338525 : Blo 2225435 3338525 := bbase (se 3 (by rfl) ⟨625973, by rfl⟩ : syracuseStep 3338525 = 1251947) (by norm_num)
theorem B2225683 : Blo 2225435 2225683 := bstep (se 1 (by rfl) ⟨1669262, by rfl⟩ : syracuseStep 2225683 = 3338525) B3338525
theorem B5007797 : Blo 2225435 5007797 := bbase (se 5 (by rfl) ⟨234740, by rfl⟩ : syracuseStep 5007797 = 469481) (by norm_num)
theorem B3338531 : Blo 2225435 3338531 := bstep (se 1 (by rfl) ⟨2503898, by rfl⟩ : syracuseStep 3338531 = 5007797) B5007797
theorem B2225687 : Blo 2225435 2225687 := bstep (se 1 (by rfl) ⟨1669265, by rfl⟩ : syracuseStep 2225687 = 3338531) B3338531
theorem B3807101 : Blo 2225435 3807101 := bbase (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) (by norm_num)
theorem B2538067 : Blo 2225435 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B3384089 : Blo 2225435 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B2256059 : Blo 2225435 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B6016157 : Blo 2225435 6016157 := bstep (se 3 (by rfl) ⟨1128029, by rfl⟩ : syracuseStep 6016157 = 2256059) B2256059
theorem B4010771 : Blo 2225435 4010771 := bstep (se 1 (by rfl) ⟨3008078, by rfl⟩ : syracuseStep 4010771 = 6016157) B6016157
theorem B2673847 : Blo 2225435 2673847 := bstep (se 1 (by rfl) ⟨2005385, by rfl⟩ : syracuseStep 2673847 = 4010771) B4010771
theorem B3565129 : Blo 2225435 3565129 := bstep (se 2 (by rfl) ⟨1336923, by rfl⟩ : syracuseStep 3565129 = 2673847) B2673847
theorem B4753505 : Blo 2225435 4753505 := bstep (se 2 (by rfl) ⟨1782564, by rfl⟩ : syracuseStep 4753505 = 3565129) B3565129
theorem B12676013 : Blo 2225435 12676013 := bstep (se 3 (by rfl) ⟨2376752, by rfl⟩ : syracuseStep 12676013 = 4753505) B4753505
theorem B8450675 : Blo 2225435 8450675 := bstep (se 1 (by rfl) ⟨6338006, by rfl⟩ : syracuseStep 8450675 = 12676013) B12676013
theorem B5633783 : Blo 2225435 5633783 := bstep (se 1 (by rfl) ⟨4225337, by rfl⟩ : syracuseStep 5633783 = 8450675) B8450675
theorem B3755855 : Blo 2225435 3755855 := bstep (se 1 (by rfl) ⟨2816891, by rfl⟩ : syracuseStep 3755855 = 5633783) B5633783
theorem B2503903 : Blo 2225435 2503903 := bstep (se 1 (by rfl) ⟨1877927, by rfl⟩ : syracuseStep 2503903 = 3755855) B3755855
theorem B3338537 : Blo 2225435 3338537 := bstep (se 2 (by rfl) ⟨1251951, by rfl⟩ : syracuseStep 3338537 = 2503903) B2503903
theorem B2225691 : Blo 2225435 2225691 := bstep (se 1 (by rfl) ⟨1669268, by rfl⟩ : syracuseStep 2225691 = 3338537) B3338537
theorem B4512125 : Blo 2225435 4512125 := bbase (se 3 (by rfl) ⟨846023, by rfl⟩ : syracuseStep 4512125 = 1692047) (by norm_num)
theorem B12032333 : Blo 2225435 12032333 := bstep (se 3 (by rfl) ⟨2256062, by rfl⟩ : syracuseStep 12032333 = 4512125) B4512125
theorem B8021555 : Blo 2225435 8021555 := bstep (se 1 (by rfl) ⟨6016166, by rfl⟩ : syracuseStep 8021555 = 12032333) B12032333
theorem B5347703 : Blo 2225435 5347703 := bstep (se 1 (by rfl) ⟨4010777, by rfl⟩ : syracuseStep 5347703 = 8021555) B8021555
theorem B3565135 : Blo 2225435 3565135 := bstep (se 1 (by rfl) ⟨2673851, by rfl⟩ : syracuseStep 3565135 = 5347703) B5347703
theorem B4753513 : Blo 2225435 4753513 := bstep (se 2 (by rfl) ⟨1782567, by rfl⟩ : syracuseStep 4753513 = 3565135) B3565135
theorem B6338017 : Blo 2225435 6338017 := bstep (se 2 (by rfl) ⟨2376756, by rfl⟩ : syracuseStep 6338017 = 4753513) B4753513
theorem B8450689 : Blo 2225435 8450689 := bstep (se 2 (by rfl) ⟨3169008, by rfl⟩ : syracuseStep 8450689 = 6338017) B6338017
theorem B11267585 : Blo 2225435 11267585 := bstep (se 2 (by rfl) ⟨4225344, by rfl⟩ : syracuseStep 11267585 = 8450689) B8450689
theorem B7511723 : Blo 2225435 7511723 := bstep (se 1 (by rfl) ⟨5633792, by rfl⟩ : syracuseStep 7511723 = 11267585) B11267585
theorem B5007815 : Blo 2225435 5007815 := bstep (se 1 (by rfl) ⟨3755861, by rfl⟩ : syracuseStep 5007815 = 7511723) B7511723
theorem B3338543 : Blo 2225435 3338543 := bstep (se 1 (by rfl) ⟨2503907, by rfl⟩ : syracuseStep 3338543 = 5007815) B5007815
theorem B2225695 : Blo 2225435 2225695 := bstep (se 1 (by rfl) ⟨1669271, by rfl⟩ : syracuseStep 2225695 = 3338543) B3338543
theorem B3338549 : Blo 2225435 3338549 := bbase (se 5 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 3338549 = 312989) (by norm_num)
theorem B2225699 : Blo 2225435 2225699 := bstep (se 1 (by rfl) ⟨1669274, by rfl⟩ : syracuseStep 2225699 = 3338549) B3338549
theorem B5633813 : Blo 2225435 5633813 := bbase (se 6 (by rfl) ⟨132042, by rfl⟩ : syracuseStep 5633813 = 264085) (by norm_num)
theorem B3755875 : Blo 2225435 3755875 := bstep (se 1 (by rfl) ⟨2816906, by rfl⟩ : syracuseStep 3755875 = 5633813) B5633813
theorem B5007833 : Blo 2225435 5007833 := bstep (se 2 (by rfl) ⟨1877937, by rfl⟩ : syracuseStep 5007833 = 3755875) B3755875
theorem B3338555 : Blo 2225435 3338555 := bstep (se 1 (by rfl) ⟨2503916, by rfl⟩ : syracuseStep 3338555 = 5007833) B5007833
theorem B2225703 : Blo 2225435 2225703 := bstep (se 1 (by rfl) ⟨1669277, by rfl⟩ : syracuseStep 2225703 = 3338555) B3338555
theorem B2503921 : Blo 2225435 2503921 := bbase (se 2 (by rfl) ⟨938970, by rfl⟩ : syracuseStep 2503921 = 1877941) (by norm_num)
theorem B3338561 : Blo 2225435 3338561 := bstep (se 2 (by rfl) ⟨1251960, by rfl⟩ : syracuseStep 3338561 = 2503921) B2503921
theorem B2225707 : Blo 2225435 2225707 := bstep (se 1 (by rfl) ⟨1669280, by rfl⟩ : syracuseStep 2225707 = 3338561) B3338561
theorem B21390965 : Blo 2225435 21390965 := bbase (se 5 (by rfl) ⟨1002701, by rfl⟩ : syracuseStep 21390965 = 2005403) (by norm_num)
theorem B14260643 : Blo 2225435 14260643 := bstep (se 1 (by rfl) ⟨10695482, by rfl⟩ : syracuseStep 14260643 = 21390965) B21390965
theorem B9507095 : Blo 2225435 9507095 := bstep (se 1 (by rfl) ⟨7130321, by rfl⟩ : syracuseStep 9507095 = 14260643) B14260643
theorem B6338063 : Blo 2225435 6338063 := bstep (se 1 (by rfl) ⟨4753547, by rfl⟩ : syracuseStep 6338063 = 9507095) B9507095
theorem B4225375 : Blo 2225435 4225375 := bstep (se 1 (by rfl) ⟨3169031, by rfl⟩ : syracuseStep 4225375 = 6338063) B6338063
theorem B5633833 : Blo 2225435 5633833 := bstep (se 2 (by rfl) ⟨2112687, by rfl⟩ : syracuseStep 5633833 = 4225375) B4225375
theorem B7511777 : Blo 2225435 7511777 := bstep (se 2 (by rfl) ⟨2816916, by rfl⟩ : syracuseStep 7511777 = 5633833) B5633833
theorem B5007851 : Blo 2225435 5007851 := bstep (se 1 (by rfl) ⟨3755888, by rfl⟩ : syracuseStep 5007851 = 7511777) B7511777
theorem B3338567 : Blo 2225435 3338567 := bstep (se 1 (by rfl) ⟨2503925, by rfl⟩ : syracuseStep 3338567 = 5007851) B5007851
theorem B2225711 : Blo 2225435 2225711 := bstep (se 1 (by rfl) ⟨1669283, by rfl⟩ : syracuseStep 2225711 = 3338567) B3338567
theorem B3338573 : Blo 2225435 3338573 := bbase (se 3 (by rfl) ⟨625982, by rfl⟩ : syracuseStep 3338573 = 1251965) (by norm_num)
theorem B2225715 : Blo 2225435 2225715 := bstep (se 1 (by rfl) ⟨1669286, by rfl⟩ : syracuseStep 2225715 = 3338573) B3338573
theorem B5007869 : Blo 2225435 5007869 := bbase (se 3 (by rfl) ⟨938975, by rfl⟩ : syracuseStep 5007869 = 1877951) (by norm_num)
theorem B3338579 : Blo 2225435 3338579 := bstep (se 1 (by rfl) ⟨2503934, by rfl⟩ : syracuseStep 3338579 = 5007869) B5007869
theorem B2225719 : Blo 2225435 2225719 := bstep (se 1 (by rfl) ⟨1669289, by rfl⟩ : syracuseStep 2225719 = 3338579) B3338579
theorem B3755909 : Blo 2225435 3755909 := bbase (se 4 (by rfl) ⟨352116, by rfl⟩ : syracuseStep 3755909 = 704233) (by norm_num)
theorem B2503939 : Blo 2225435 2503939 := bstep (se 1 (by rfl) ⟨1877954, by rfl⟩ : syracuseStep 2503939 = 3755909) B3755909
theorem B3338585 : Blo 2225435 3338585 := bstep (se 2 (by rfl) ⟨1251969, by rfl⟩ : syracuseStep 3338585 = 2503939) B2503939
theorem B2225723 : Blo 2225435 2225723 := bstep (se 1 (by rfl) ⟨1669292, by rfl⟩ : syracuseStep 2225723 = 3338585) B3338585
theorem B16901621 : Blo 2225435 16901621 := bbase (se 5 (by rfl) ⟨792263, by rfl⟩ : syracuseStep 16901621 = 1584527) (by norm_num)
theorem B11267747 : Blo 2225435 11267747 := bstep (se 1 (by rfl) ⟨8450810, by rfl⟩ : syracuseStep 11267747 = 16901621) B16901621
theorem B7511831 : Blo 2225435 7511831 := bstep (se 1 (by rfl) ⟨5633873, by rfl⟩ : syracuseStep 7511831 = 11267747) B11267747
theorem B5007887 : Blo 2225435 5007887 := bstep (se 1 (by rfl) ⟨3755915, by rfl⟩ : syracuseStep 5007887 = 7511831) B7511831
theorem B3338591 : Blo 2225435 3338591 := bstep (se 1 (by rfl) ⟨2503943, by rfl⟩ : syracuseStep 3338591 = 5007887) B5007887
theorem B2225727 : Blo 2225435 2225727 := bstep (se 1 (by rfl) ⟨1669295, by rfl⟩ : syracuseStep 2225727 = 3338591) B3338591
theorem B3338597 : Blo 2225435 3338597 := bbase (se 4 (by rfl) ⟨312993, by rfl⟩ : syracuseStep 3338597 = 625987) (by norm_num)
theorem B2225731 : Blo 2225435 2225731 := bstep (se 1 (by rfl) ⟨1669298, by rfl⟩ : syracuseStep 2225731 = 3338597) B3338597
theorem B4225421 : Blo 2225435 4225421 := bbase (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) (by norm_num)
theorem B2816947 : Blo 2225435 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B3755929 : Blo 2225435 3755929 := bstep (se 2 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 3755929 = 2816947) B2816947
theorem B5007905 : Blo 2225435 5007905 := bstep (se 2 (by rfl) ⟨1877964, by rfl⟩ : syracuseStep 5007905 = 3755929) B3755929
theorem B3338603 : Blo 2225435 3338603 := bstep (se 1 (by rfl) ⟨2503952, by rfl⟩ : syracuseStep 3338603 = 5007905) B5007905
theorem B2225735 : Blo 2225435 2225735 := bstep (se 1 (by rfl) ⟨1669301, by rfl⟩ : syracuseStep 2225735 = 3338603) B3338603
theorem B2503957 : Blo 2225435 2503957 := bbase (se 6 (by rfl) ⟨58686, by rfl⟩ : syracuseStep 2503957 = 117373) (by norm_num)
theorem B3338609 : Blo 2225435 3338609 := bstep (se 2 (by rfl) ⟨1251978, by rfl⟩ : syracuseStep 3338609 = 2503957) B2503957
theorem B2225739 : Blo 2225435 2225739 := bstep (se 1 (by rfl) ⟨1669304, by rfl⟩ : syracuseStep 2225739 = 3338609) B3338609
theorem B2816957 : Blo 2225435 2816957 := bbase (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) (by norm_num)
theorem B7511885 : Blo 2225435 7511885 := bstep (se 3 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 7511885 = 2816957) B2816957
theorem B5007923 : Blo 2225435 5007923 := bstep (se 1 (by rfl) ⟨3755942, by rfl⟩ : syracuseStep 5007923 = 7511885) B7511885
theorem B3338615 : Blo 2225435 3338615 := bstep (se 1 (by rfl) ⟨2503961, by rfl⟩ : syracuseStep 3338615 = 5007923) B5007923
theorem B2225743 : Blo 2225435 2225743 := bstep (se 1 (by rfl) ⟨1669307, by rfl⟩ : syracuseStep 2225743 = 3338615) B3338615
theorem B3338621 : Blo 2225435 3338621 := bbase (se 3 (by rfl) ⟨625991, by rfl⟩ : syracuseStep 3338621 = 1251983) (by norm_num)
theorem B2225747 : Blo 2225435 2225747 := bstep (se 1 (by rfl) ⟨1669310, by rfl⟩ : syracuseStep 2225747 = 3338621) B3338621
theorem B5007941 : Blo 2225435 5007941 := bbase (se 4 (by rfl) ⟨469494, by rfl⟩ : syracuseStep 5007941 = 938989) (by norm_num)
theorem B3338627 : Blo 2225435 3338627 := bstep (se 1 (by rfl) ⟨2503970, by rfl⟩ : syracuseStep 3338627 = 5007941) B5007941
theorem B2225751 : Blo 2225435 2225751 := bstep (se 1 (by rfl) ⟨1669313, by rfl⟩ : syracuseStep 2225751 = 3338627) B3338627
theorem B2376821 : Blo 2225435 2376821 := bbase (se 5 (by rfl) ⟨111413, by rfl⟩ : syracuseStep 2376821 = 222827) (by norm_num)
theorem B6338189 : Blo 2225435 6338189 := bstep (se 3 (by rfl) ⟨1188410, by rfl⟩ : syracuseStep 6338189 = 2376821) B2376821
theorem B4225459 : Blo 2225435 4225459 := bstep (se 1 (by rfl) ⟨3169094, by rfl⟩ : syracuseStep 4225459 = 6338189) B6338189
theorem B5633945 : Blo 2225435 5633945 := bstep (se 2 (by rfl) ⟨2112729, by rfl⟩ : syracuseStep 5633945 = 4225459) B4225459
theorem B3755963 : Blo 2225435 3755963 := bstep (se 1 (by rfl) ⟨2816972, by rfl⟩ : syracuseStep 3755963 = 5633945) B5633945
theorem B2503975 : Blo 2225435 2503975 := bstep (se 1 (by rfl) ⟨1877981, by rfl⟩ : syracuseStep 2503975 = 3755963) B3755963
theorem B3338633 : Blo 2225435 3338633 := bstep (se 2 (by rfl) ⟨1251987, by rfl⟩ : syracuseStep 3338633 = 2503975) B2503975
theorem B2225755 : Blo 2225435 2225755 := bstep (se 1 (by rfl) ⟨1669316, by rfl⟩ : syracuseStep 2225755 = 3338633) B3338633
theorem B11267909 : Blo 2225435 11267909 := bbase (se 4 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 11267909 = 2112733) (by norm_num)
theorem B7511939 : Blo 2225435 7511939 := bstep (se 1 (by rfl) ⟨5633954, by rfl⟩ : syracuseStep 7511939 = 11267909) B11267909
theorem B5007959 : Blo 2225435 5007959 := bstep (se 1 (by rfl) ⟨3755969, by rfl⟩ : syracuseStep 5007959 = 7511939) B7511939
theorem B3338639 : Blo 2225435 3338639 := bstep (se 1 (by rfl) ⟨2503979, by rfl⟩ : syracuseStep 3338639 = 5007959) B5007959
theorem B2225759 : Blo 2225435 2225759 := bstep (se 1 (by rfl) ⟨1669319, by rfl⟩ : syracuseStep 2225759 = 3338639) B3338639
theorem B3338645 : Blo 2225435 3338645 := bbase (se 6 (by rfl) ⟨78249, by rfl⟩ : syracuseStep 3338645 = 156499) (by norm_num)
theorem B2225763 : Blo 2225435 2225763 := bstep (se 1 (by rfl) ⟨1669322, by rfl⟩ : syracuseStep 2225763 = 3338645) B3338645
theorem B7130501 : Blo 2225435 7130501 := bbase (se 4 (by rfl) ⟨668484, by rfl⟩ : syracuseStep 7130501 = 1336969) (by norm_num)
theorem B4753667 : Blo 2225435 4753667 := bstep (se 1 (by rfl) ⟨3565250, by rfl⟩ : syracuseStep 4753667 = 7130501) B7130501
theorem B12676445 : Blo 2225435 12676445 := bstep (se 3 (by rfl) ⟨2376833, by rfl⟩ : syracuseStep 12676445 = 4753667) B4753667
theorem B8450963 : Blo 2225435 8450963 := bstep (se 1 (by rfl) ⟨6338222, by rfl⟩ : syracuseStep 8450963 = 12676445) B12676445
theorem B5633975 : Blo 2225435 5633975 := bstep (se 1 (by rfl) ⟨4225481, by rfl⟩ : syracuseStep 5633975 = 8450963) B8450963
theorem B3755983 : Blo 2225435 3755983 := bstep (se 1 (by rfl) ⟨2816987, by rfl⟩ : syracuseStep 3755983 = 5633975) B5633975
theorem B5007977 : Blo 2225435 5007977 := bstep (se 2 (by rfl) ⟨1877991, by rfl⟩ : syracuseStep 5007977 = 3755983) B3755983
theorem B3338651 : Blo 2225435 3338651 := bstep (se 1 (by rfl) ⟨2503988, by rfl⟩ : syracuseStep 3338651 = 5007977) B5007977
theorem B2225767 : Blo 2225435 2225767 := bstep (se 1 (by rfl) ⟨1669325, by rfl⟩ : syracuseStep 2225767 = 3338651) B3338651
theorem B2503993 : Blo 2225435 2503993 := bbase (se 2 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 2503993 = 1877995) (by norm_num)
theorem B3338657 : Blo 2225435 3338657 := bstep (se 2 (by rfl) ⟨1251996, by rfl⟩ : syracuseStep 3338657 = 2503993) B2503993
theorem B2225771 : Blo 2225435 2225771 := bstep (se 1 (by rfl) ⟨1669328, by rfl⟩ : syracuseStep 2225771 = 3338657) B3338657
theorem B6338245 : Blo 2225435 6338245 := bbase (se 4 (by rfl) ⟨594210, by rfl⟩ : syracuseStep 6338245 = 1188421) (by norm_num)
theorem B8450993 : Blo 2225435 8450993 := bstep (se 2 (by rfl) ⟨3169122, by rfl⟩ : syracuseStep 8450993 = 6338245) B6338245
theorem B5633995 : Blo 2225435 5633995 := bstep (se 1 (by rfl) ⟨4225496, by rfl⟩ : syracuseStep 5633995 = 8450993) B8450993
theorem B7511993 : Blo 2225435 7511993 := bstep (se 2 (by rfl) ⟨2816997, by rfl⟩ : syracuseStep 7511993 = 5633995) B5633995
theorem B5007995 : Blo 2225435 5007995 := bstep (se 1 (by rfl) ⟨3755996, by rfl⟩ : syracuseStep 5007995 = 7511993) B7511993
theorem B3338663 : Blo 2225435 3338663 := bstep (se 1 (by rfl) ⟨2503997, by rfl⟩ : syracuseStep 3338663 = 5007995) B5007995
theorem B2225775 : Blo 2225435 2225775 := bstep (se 1 (by rfl) ⟨1669331, by rfl⟩ : syracuseStep 2225775 = 3338663) B3338663
theorem B3338669 : Blo 2225435 3338669 := bbase (se 3 (by rfl) ⟨626000, by rfl⟩ : syracuseStep 3338669 = 1252001) (by norm_num)
theorem B2225779 : Blo 2225435 2225779 := bstep (se 1 (by rfl) ⟨1669334, by rfl⟩ : syracuseStep 2225779 = 3338669) B3338669
theorem B5008013 : Blo 2225435 5008013 := bbase (se 3 (by rfl) ⟨939002, by rfl⟩ : syracuseStep 5008013 = 1878005) (by norm_num)
theorem B3338675 : Blo 2225435 3338675 := bstep (se 1 (by rfl) ⟨2504006, by rfl⟩ : syracuseStep 3338675 = 5008013) B5008013
theorem B2225783 : Blo 2225435 2225783 := bstep (se 1 (by rfl) ⟨1669337, by rfl⟩ : syracuseStep 2225783 = 3338675) B3338675
theorem B2817013 : Blo 2225435 2817013 := bbase (se 5 (by rfl) ⟨132047, by rfl⟩ : syracuseStep 2817013 = 264095) (by norm_num)
theorem B3756017 : Blo 2225435 3756017 := bstep (se 2 (by rfl) ⟨1408506, by rfl⟩ : syracuseStep 3756017 = 2817013) B2817013
theorem B2504011 : Blo 2225435 2504011 := bstep (se 1 (by rfl) ⟨1878008, by rfl⟩ : syracuseStep 2504011 = 3756017) B3756017
theorem B3338681 : Blo 2225435 3338681 := bstep (se 2 (by rfl) ⟨1252005, by rfl⟩ : syracuseStep 3338681 = 2504011) B2504011
theorem B2225787 : Blo 2225435 2225787 := bstep (se 1 (by rfl) ⟨1669340, by rfl⟩ : syracuseStep 2225787 = 3338681) B3338681
theorem B8566357 : Blo 2225435 8566357 := bbase (se 8 (by rfl) ⟨50193, by rfl⟩ : syracuseStep 8566357 = 100387) (by norm_num)
theorem B11421809 : Blo 2225435 11421809 := bstep (se 2 (by rfl) ⟨4283178, by rfl⟩ : syracuseStep 11421809 = 8566357) B8566357
theorem B7614539 : Blo 2225435 7614539 := bstep (se 1 (by rfl) ⟨5710904, by rfl⟩ : syracuseStep 7614539 = 11421809) B11421809
theorem B5076359 : Blo 2225435 5076359 := bstep (se 1 (by rfl) ⟨3807269, by rfl⟩ : syracuseStep 5076359 = 7614539) B7614539
theorem B3384239 : Blo 2225435 3384239 := bstep (se 1 (by rfl) ⟨2538179, by rfl⟩ : syracuseStep 3384239 = 5076359) B5076359
theorem B9024637 : Blo 2225435 9024637 := bstep (se 3 (by rfl) ⟨1692119, by rfl⟩ : syracuseStep 9024637 = 3384239) B3384239
theorem B12032849 : Blo 2225435 12032849 := bstep (se 2 (by rfl) ⟨4512318, by rfl⟩ : syracuseStep 12032849 = 9024637) B9024637
theorem B8021899 : Blo 2225435 8021899 := bstep (se 1 (by rfl) ⟨6016424, by rfl⟩ : syracuseStep 8021899 = 12032849) B12032849
theorem B42783461 : Blo 2225435 42783461 := bstep (se 4 (by rfl) ⟨4010949, by rfl⟩ : syracuseStep 42783461 = 8021899) B8021899
theorem B28522307 : Blo 2225435 28522307 := bstep (se 1 (by rfl) ⟨21391730, by rfl⟩ : syracuseStep 28522307 = 42783461) B42783461
theorem B19014871 : Blo 2225435 19014871 := bstep (se 1 (by rfl) ⟨14261153, by rfl⟩ : syracuseStep 19014871 = 28522307) B28522307
theorem B25353161 : Blo 2225435 25353161 := bstep (se 2 (by rfl) ⟨9507435, by rfl⟩ : syracuseStep 25353161 = 19014871) B19014871
theorem B16902107 : Blo 2225435 16902107 := bstep (se 1 (by rfl) ⟨12676580, by rfl⟩ : syracuseStep 16902107 = 25353161) B25353161
theorem B11268071 : Blo 2225435 11268071 := bstep (se 1 (by rfl) ⟨8451053, by rfl⟩ : syracuseStep 11268071 = 16902107) B16902107
theorem B7512047 : Blo 2225435 7512047 := bstep (se 1 (by rfl) ⟨5634035, by rfl⟩ : syracuseStep 7512047 = 11268071) B11268071
theorem B5008031 : Blo 2225435 5008031 := bstep (se 1 (by rfl) ⟨3756023, by rfl⟩ : syracuseStep 5008031 = 7512047) B7512047
theorem B3338687 : Blo 2225435 3338687 := bstep (se 1 (by rfl) ⟨2504015, by rfl⟩ : syracuseStep 3338687 = 5008031) B5008031
theorem B2225791 : Blo 2225435 2225791 := bstep (se 1 (by rfl) ⟨1669343, by rfl⟩ : syracuseStep 2225791 = 3338687) B3338687
theorem B3338693 : Blo 2225435 3338693 := bbase (se 4 (by rfl) ⟨313002, by rfl⟩ : syracuseStep 3338693 = 626005) (by norm_num)
theorem B2225795 : Blo 2225435 2225795 := bstep (se 1 (by rfl) ⟨1669346, by rfl⟩ : syracuseStep 2225795 = 3338693) B3338693
theorem B3756037 : Blo 2225435 3756037 := bbase (se 4 (by rfl) ⟨352128, by rfl⟩ : syracuseStep 3756037 = 704257) (by norm_num)
theorem B5008049 : Blo 2225435 5008049 := bstep (se 2 (by rfl) ⟨1878018, by rfl⟩ : syracuseStep 5008049 = 3756037) B3756037
theorem B3338699 : Blo 2225435 3338699 := bstep (se 1 (by rfl) ⟨2504024, by rfl⟩ : syracuseStep 3338699 = 5008049) B5008049
theorem B2225799 : Blo 2225435 2225799 := bstep (se 1 (by rfl) ⟨1669349, by rfl⟩ : syracuseStep 2225799 = 3338699) B3338699
theorem B2504029 : Blo 2225435 2504029 := bbase (se 3 (by rfl) ⟨469505, by rfl⟩ : syracuseStep 2504029 = 939011) (by norm_num)
theorem B3338705 : Blo 2225435 3338705 := bstep (se 2 (by rfl) ⟨1252014, by rfl⟩ : syracuseStep 3338705 = 2504029) B2504029
theorem B2225803 : Blo 2225435 2225803 := bstep (se 1 (by rfl) ⟨1669352, by rfl⟩ : syracuseStep 2225803 = 3338705) B3338705
theorem B7512101 : Blo 2225435 7512101 := bbase (se 4 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 7512101 = 1408519) (by norm_num)
theorem B5008067 : Blo 2225435 5008067 := bstep (se 1 (by rfl) ⟨3756050, by rfl⟩ : syracuseStep 5008067 = 7512101) B7512101
theorem B3338711 : Blo 2225435 3338711 := bstep (se 1 (by rfl) ⟨2504033, by rfl⟩ : syracuseStep 3338711 = 5008067) B5008067
theorem B2225807 : Blo 2225435 2225807 := bstep (se 1 (by rfl) ⟨1669355, by rfl⟩ : syracuseStep 2225807 = 3338711) B3338711
theorem B3338717 : Blo 2225435 3338717 := bbase (se 3 (by rfl) ⟨626009, by rfl⟩ : syracuseStep 3338717 = 1252019) (by norm_num)
theorem B2225811 : Blo 2225435 2225811 := bstep (se 1 (by rfl) ⟨1669358, by rfl⟩ : syracuseStep 2225811 = 3338717) B3338717
theorem B5008085 : Blo 2225435 5008085 := bbase (se 7 (by rfl) ⟨58688, by rfl⟩ : syracuseStep 5008085 = 117377) (by norm_num)
theorem B3338723 : Blo 2225435 3338723 := bstep (se 1 (by rfl) ⟨2504042, by rfl⟩ : syracuseStep 3338723 = 5008085) B5008085
theorem B2225815 : Blo 2225435 2225815 := bstep (se 1 (by rfl) ⟨1669361, by rfl⟩ : syracuseStep 2225815 = 3338723) B3338723
theorem B9507557 : Blo 2225435 9507557 := bbase (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) (by norm_num)
theorem B6338371 : Blo 2225435 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B8451161 : Blo 2225435 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B5634107 : Blo 2225435 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B3756071 : Blo 2225435 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B2504047 : Blo 2225435 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B3338729 : Blo 2225435 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B2225819 : Blo 2225435 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B51398869 : Blo 2225435 51398869 := bbase (se 7 (by rfl) ⟨602330, by rfl⟩ : syracuseStep 51398869 = 1204661) (by norm_num)
theorem B68531825 : Blo 2225435 68531825 := bstep (se 2 (by rfl) ⟨25699434, by rfl⟩ : syracuseStep 68531825 = 51398869) B51398869
theorem B45687883 : Blo 2225435 45687883 := bstep (se 1 (by rfl) ⟨34265912, by rfl⟩ : syracuseStep 45687883 = 68531825) B68531825
theorem B60917177 : Blo 2225435 60917177 := bstep (se 2 (by rfl) ⟨22843941, by rfl⟩ : syracuseStep 60917177 = 45687883) B45687883
theorem B40611451 : Blo 2225435 40611451 := bstep (se 1 (by rfl) ⟨30458588, by rfl⟩ : syracuseStep 40611451 = 60917177) B60917177
theorem B54148601 : Blo 2225435 54148601 := bstep (se 2 (by rfl) ⟨20305725, by rfl⟩ : syracuseStep 54148601 = 40611451) B40611451
theorem B36099067 : Blo 2225435 36099067 := bstep (se 1 (by rfl) ⟨27074300, by rfl⟩ : syracuseStep 36099067 = 54148601) B54148601
theorem B48132089 : Blo 2225435 48132089 := bstep (se 2 (by rfl) ⟨18049533, by rfl⟩ : syracuseStep 48132089 = 36099067) B36099067
theorem B32088059 : Blo 2225435 32088059 := bstep (se 1 (by rfl) ⟨24066044, by rfl⟩ : syracuseStep 32088059 = 48132089) B48132089
theorem B21392039 : Blo 2225435 21392039 := bstep (se 1 (by rfl) ⟨16044029, by rfl⟩ : syracuseStep 21392039 = 32088059) B32088059
theorem B14261359 : Blo 2225435 14261359 := bstep (se 1 (by rfl) ⟨10696019, by rfl⟩ : syracuseStep 14261359 = 21392039) B21392039
theorem B19015145 : Blo 2225435 19015145 := bstep (se 2 (by rfl) ⟨7130679, by rfl⟩ : syracuseStep 19015145 = 14261359) B14261359
theorem B12676763 : Blo 2225435 12676763 := bstep (se 1 (by rfl) ⟨9507572, by rfl⟩ : syracuseStep 12676763 = 19015145) B19015145
theorem B8451175 : Blo 2225435 8451175 := bstep (se 1 (by rfl) ⟨6338381, by rfl⟩ : syracuseStep 8451175 = 12676763) B12676763
theorem B11268233 : Blo 2225435 11268233 := bstep (se 2 (by rfl) ⟨4225587, by rfl⟩ : syracuseStep 11268233 = 8451175) B8451175
theorem B7512155 : Blo 2225435 7512155 := bstep (se 1 (by rfl) ⟨5634116, by rfl⟩ : syracuseStep 7512155 = 11268233) B11268233
theorem B5008103 : Blo 2225435 5008103 := bstep (se 1 (by rfl) ⟨3756077, by rfl⟩ : syracuseStep 5008103 = 7512155) B7512155
theorem B3338735 : Blo 2225435 3338735 := bstep (se 1 (by rfl) ⟨2504051, by rfl⟩ : syracuseStep 3338735 = 5008103) B5008103
theorem B2225823 : Blo 2225435 2225823 := bstep (se 1 (by rfl) ⟨1669367, by rfl⟩ : syracuseStep 2225823 = 3338735) B3338735
theorem B3338741 : Blo 2225435 3338741 := bbase (se 5 (by rfl) ⟨156503, by rfl⟩ : syracuseStep 3338741 = 313007) (by norm_num)
theorem B2225827 : Blo 2225435 2225827 := bstep (se 1 (by rfl) ⟨1669370, by rfl⟩ : syracuseStep 2225827 = 3338741) B3338741
theorem B6338405 : Blo 2225435 6338405 := bbase (se 4 (by rfl) ⟨594225, by rfl⟩ : syracuseStep 6338405 = 1188451) (by norm_num)
theorem B4225603 : Blo 2225435 4225603 := bstep (se 1 (by rfl) ⟨3169202, by rfl⟩ : syracuseStep 4225603 = 6338405) B6338405
theorem B5634137 : Blo 2225435 5634137 := bstep (se 2 (by rfl) ⟨2112801, by rfl⟩ : syracuseStep 5634137 = 4225603) B4225603
theorem B3756091 : Blo 2225435 3756091 := bstep (se 1 (by rfl) ⟨2817068, by rfl⟩ : syracuseStep 3756091 = 5634137) B5634137
theorem B5008121 : Blo 2225435 5008121 := bstep (se 2 (by rfl) ⟨1878045, by rfl⟩ : syracuseStep 5008121 = 3756091) B3756091
theorem B3338747 : Blo 2225435 3338747 := bstep (se 1 (by rfl) ⟨2504060, by rfl⟩ : syracuseStep 3338747 = 5008121) B5008121
theorem B2225831 : Blo 2225435 2225831 := bstep (se 1 (by rfl) ⟨1669373, by rfl⟩ : syracuseStep 2225831 = 3338747) B3338747
theorem B2504065 : Blo 2225435 2504065 := bbase (se 2 (by rfl) ⟨939024, by rfl⟩ : syracuseStep 2504065 = 1878049) (by norm_num)
theorem B3338753 : Blo 2225435 3338753 := bstep (se 2 (by rfl) ⟨1252032, by rfl⟩ : syracuseStep 3338753 = 2504065) B2504065
theorem B2225835 : Blo 2225435 2225835 := bstep (se 1 (by rfl) ⟨1669376, by rfl⟩ : syracuseStep 2225835 = 3338753) B3338753
theorem B5634157 : Blo 2225435 5634157 := bbase (se 3 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 5634157 = 2112809) (by norm_num)
theorem B7512209 : Blo 2225435 7512209 := bstep (se 2 (by rfl) ⟨2817078, by rfl⟩ : syracuseStep 7512209 = 5634157) B5634157
theorem B5008139 : Blo 2225435 5008139 := bstep (se 1 (by rfl) ⟨3756104, by rfl⟩ : syracuseStep 5008139 = 7512209) B7512209
theorem B3338759 : Blo 2225435 3338759 := bstep (se 1 (by rfl) ⟨2504069, by rfl⟩ : syracuseStep 3338759 = 5008139) B5008139
theorem B2225839 : Blo 2225435 2225839 := bstep (se 1 (by rfl) ⟨1669379, by rfl⟩ : syracuseStep 2225839 = 3338759) B3338759
theorem B3338765 : Blo 2225435 3338765 := bbase (se 3 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 3338765 = 1252037) (by norm_num)
theorem B2225843 : Blo 2225435 2225843 := bstep (se 1 (by rfl) ⟨1669382, by rfl⟩ : syracuseStep 2225843 = 3338765) B3338765
theorem B5008157 : Blo 2225435 5008157 := bbase (se 3 (by rfl) ⟨939029, by rfl⟩ : syracuseStep 5008157 = 1878059) (by norm_num)
theorem B3338771 : Blo 2225435 3338771 := bstep (se 1 (by rfl) ⟨2504078, by rfl⟩ : syracuseStep 3338771 = 5008157) B5008157
theorem B2225847 : Blo 2225435 2225847 := bstep (se 1 (by rfl) ⟨1669385, by rfl⟩ : syracuseStep 2225847 = 3338771) B3338771
theorem B3756125 : Blo 2225435 3756125 := bbase (se 3 (by rfl) ⟨704273, by rfl⟩ : syracuseStep 3756125 = 1408547) (by norm_num)
theorem B2504083 : Blo 2225435 2504083 := bstep (se 1 (by rfl) ⟨1878062, by rfl⟩ : syracuseStep 2504083 = 3756125) B3756125
theorem B3338777 : Blo 2225435 3338777 := bstep (se 2 (by rfl) ⟨1252041, by rfl⟩ : syracuseStep 3338777 = 2504083) B2504083
theorem B2225851 : Blo 2225435 2225851 := bstep (se 1 (by rfl) ⟨1669388, by rfl⟩ : syracuseStep 2225851 = 3338777) B3338777
theorem B2538253 : Blo 2225435 2538253 := bbase (se 3 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 2538253 = 951845) (by norm_num)
theorem B3384337 : Blo 2225435 3384337 := bstep (se 2 (by rfl) ⟨1269126, by rfl⟩ : syracuseStep 3384337 = 2538253) B2538253
theorem B4512449 : Blo 2225435 4512449 := bstep (se 2 (by rfl) ⟨1692168, by rfl⟩ : syracuseStep 4512449 = 3384337) B3384337
theorem B12033197 : Blo 2225435 12033197 := bstep (se 3 (by rfl) ⟨2256224, by rfl⟩ : syracuseStep 12033197 = 4512449) B4512449
theorem B8022131 : Blo 2225435 8022131 := bstep (se 1 (by rfl) ⟨6016598, by rfl⟩ : syracuseStep 8022131 = 12033197) B12033197
theorem B5348087 : Blo 2225435 5348087 := bstep (se 1 (by rfl) ⟨4011065, by rfl⟩ : syracuseStep 5348087 = 8022131) B8022131
theorem B3565391 : Blo 2225435 3565391 := bstep (se 1 (by rfl) ⟨2674043, by rfl⟩ : syracuseStep 3565391 = 5348087) B5348087
theorem B9507709 : Blo 2225435 9507709 := bstep (se 3 (by rfl) ⟨1782695, by rfl⟩ : syracuseStep 9507709 = 3565391) B3565391
theorem B12676945 : Blo 2225435 12676945 := bstep (se 2 (by rfl) ⟨4753854, by rfl⟩ : syracuseStep 12676945 = 9507709) B9507709
theorem B16902593 : Blo 2225435 16902593 := bstep (se 2 (by rfl) ⟨6338472, by rfl⟩ : syracuseStep 16902593 = 12676945) B12676945
theorem B11268395 : Blo 2225435 11268395 := bstep (se 1 (by rfl) ⟨8451296, by rfl⟩ : syracuseStep 11268395 = 16902593) B16902593
theorem B7512263 : Blo 2225435 7512263 := bstep (se 1 (by rfl) ⟨5634197, by rfl⟩ : syracuseStep 7512263 = 11268395) B11268395
theorem B5008175 : Blo 2225435 5008175 := bstep (se 1 (by rfl) ⟨3756131, by rfl⟩ : syracuseStep 5008175 = 7512263) B7512263
theorem B3338783 : Blo 2225435 3338783 := bstep (se 1 (by rfl) ⟨2504087, by rfl⟩ : syracuseStep 3338783 = 5008175) B5008175
theorem B2225855 : Blo 2225435 2225855 := bstep (se 1 (by rfl) ⟨1669391, by rfl⟩ : syracuseStep 2225855 = 3338783) B3338783
theorem B3338789 : Blo 2225435 3338789 := bbase (se 4 (by rfl) ⟨313011, by rfl⟩ : syracuseStep 3338789 = 626023) (by norm_num)
theorem B2225859 : Blo 2225435 2225859 := bstep (se 1 (by rfl) ⟨1669394, by rfl⟩ : syracuseStep 2225859 = 3338789) B3338789
theorem B2817109 : Blo 2225435 2817109 := bbase (se 8 (by rfl) ⟨16506, by rfl⟩ : syracuseStep 2817109 = 33013) (by norm_num)
theorem B3756145 : Blo 2225435 3756145 := bstep (se 2 (by rfl) ⟨1408554, by rfl⟩ : syracuseStep 3756145 = 2817109) B2817109
theorem B5008193 : Blo 2225435 5008193 := bstep (se 2 (by rfl) ⟨1878072, by rfl⟩ : syracuseStep 5008193 = 3756145) B3756145
theorem B3338795 : Blo 2225435 3338795 := bstep (se 1 (by rfl) ⟨2504096, by rfl⟩ : syracuseStep 3338795 = 5008193) B5008193
theorem B2225863 : Blo 2225435 2225863 := bstep (se 1 (by rfl) ⟨1669397, by rfl⟩ : syracuseStep 2225863 = 3338795) B3338795
theorem B2504101 : Blo 2225435 2504101 := bbase (se 4 (by rfl) ⟨234759, by rfl⟩ : syracuseStep 2504101 = 469519) (by norm_num)
theorem B3338801 : Blo 2225435 3338801 := bstep (se 2 (by rfl) ⟨1252050, by rfl⟩ : syracuseStep 3338801 = 2504101) B2504101
theorem B2225867 : Blo 2225435 2225867 := bstep (se 1 (by rfl) ⟨1669400, by rfl⟩ : syracuseStep 2225867 = 3338801) B3338801
theorem B9024965 : Blo 2225435 9024965 := bbase (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) (by norm_num)
theorem B6016643 : Blo 2225435 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B4011095 : Blo 2225435 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2674063 : Blo 2225435 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B14261669 : Blo 2225435 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B9507779 : Blo 2225435 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B6338519 : Blo 2225435 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B4225679 : Blo 2225435 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B2817119 : Blo 2225435 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B7512317 : Blo 2225435 7512317 := bstep (se 3 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 7512317 = 2817119) B2817119
theorem B5008211 : Blo 2225435 5008211 := bstep (se 1 (by rfl) ⟨3756158, by rfl⟩ : syracuseStep 5008211 = 7512317) B7512317
theorem B3338807 : Blo 2225435 3338807 := bstep (se 1 (by rfl) ⟨2504105, by rfl⟩ : syracuseStep 3338807 = 5008211) B5008211
theorem B2225871 : Blo 2225435 2225871 := bstep (se 1 (by rfl) ⟨1669403, by rfl⟩ : syracuseStep 2225871 = 3338807) B3338807
theorem B3338813 : Blo 2225435 3338813 := bbase (se 3 (by rfl) ⟨626027, by rfl⟩ : syracuseStep 3338813 = 1252055) (by norm_num)
theorem B2225875 : Blo 2225435 2225875 := bstep (se 1 (by rfl) ⟨1669406, by rfl⟩ : syracuseStep 2225875 = 3338813) B3338813
theorem B5008229 : Blo 2225435 5008229 := bbase (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) (by norm_num)
theorem B3338819 : Blo 2225435 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B2225879 : Blo 2225435 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B5634269 : Blo 2225435 5634269 := bbase (se 3 (by rfl) ⟨1056425, by rfl⟩ : syracuseStep 5634269 = 2112851) (by norm_num)
theorem B3756179 : Blo 2225435 3756179 := bstep (se 1 (by rfl) ⟨2817134, by rfl⟩ : syracuseStep 3756179 = 5634269) B5634269
theorem B2504119 : Blo 2225435 2504119 := bstep (se 1 (by rfl) ⟨1878089, by rfl⟩ : syracuseStep 2504119 = 3756179) B3756179
theorem B3338825 : Blo 2225435 3338825 := bstep (se 2 (by rfl) ⟨1252059, by rfl⟩ : syracuseStep 3338825 = 2504119) B2504119
theorem B2225883 : Blo 2225435 2225883 := bstep (se 1 (by rfl) ⟨1669412, by rfl⟩ : syracuseStep 2225883 = 3338825) B3338825
theorem B4225709 : Blo 2225435 4225709 := bbase (se 3 (by rfl) ⟨792320, by rfl⟩ : syracuseStep 4225709 = 1584641) (by norm_num)
theorem B11268557 : Blo 2225435 11268557 := bstep (se 3 (by rfl) ⟨2112854, by rfl⟩ : syracuseStep 11268557 = 4225709) B4225709
theorem B7512371 : Blo 2225435 7512371 := bstep (se 1 (by rfl) ⟨5634278, by rfl⟩ : syracuseStep 7512371 = 11268557) B11268557
theorem B5008247 : Blo 2225435 5008247 := bstep (se 1 (by rfl) ⟨3756185, by rfl⟩ : syracuseStep 5008247 = 7512371) B7512371
theorem B3338831 : Blo 2225435 3338831 := bstep (se 1 (by rfl) ⟨2504123, by rfl⟩ : syracuseStep 3338831 = 5008247) B5008247
theorem B2225887 : Blo 2225435 2225887 := bstep (se 1 (by rfl) ⟨1669415, by rfl⟩ : syracuseStep 2225887 = 3338831) B3338831
theorem B3338837 : Blo 2225435 3338837 := bbase (se 8 (by rfl) ⟨19563, by rfl⟩ : syracuseStep 3338837 = 39127) (by norm_num)
theorem B2225891 : Blo 2225435 2225891 := bstep (se 1 (by rfl) ⟨1669418, by rfl⟩ : syracuseStep 2225891 = 3338837) B3338837
theorem B3614101 : Blo 2225435 3614101 := bbase (se 6 (by rfl) ⟨84705, by rfl⟩ : syracuseStep 3614101 = 169411) (by norm_num)
theorem B19275205 : Blo 2225435 19275205 := bstep (se 4 (by rfl) ⟨1807050, by rfl⟩ : syracuseStep 19275205 = 3614101) B3614101
theorem B25700273 : Blo 2225435 25700273 := bstep (se 2 (by rfl) ⟨9637602, by rfl⟩ : syracuseStep 25700273 = 19275205) B19275205
theorem B17133515 : Blo 2225435 17133515 := bstep (se 1 (by rfl) ⟨12850136, by rfl⟩ : syracuseStep 17133515 = 25700273) B25700273
theorem B11422343 : Blo 2225435 11422343 := bstep (se 1 (by rfl) ⟨8566757, by rfl⟩ : syracuseStep 11422343 = 17133515) B17133515
theorem B7614895 : Blo 2225435 7614895 := bstep (se 1 (by rfl) ⟨5711171, by rfl⟩ : syracuseStep 7614895 = 11422343) B11422343
theorem B10153193 : Blo 2225435 10153193 := bstep (se 2 (by rfl) ⟨3807447, by rfl⟩ : syracuseStep 10153193 = 7614895) B7614895
theorem B27075181 : Blo 2225435 27075181 := bstep (se 3 (by rfl) ⟨5076596, by rfl⟩ : syracuseStep 27075181 = 10153193) B10153193
theorem B36100241 : Blo 2225435 36100241 := bstep (se 2 (by rfl) ⟨13537590, by rfl⟩ : syracuseStep 36100241 = 27075181) B27075181
theorem B24066827 : Blo 2225435 24066827 := bstep (se 1 (by rfl) ⟨18050120, by rfl⟩ : syracuseStep 24066827 = 36100241) B36100241
theorem B16044551 : Blo 2225435 16044551 := bstep (se 1 (by rfl) ⟨12033413, by rfl⟩ : syracuseStep 16044551 = 24066827) B24066827
theorem B10696367 : Blo 2225435 10696367 := bstep (se 1 (by rfl) ⟨8022275, by rfl⟩ : syracuseStep 10696367 = 16044551) B16044551
theorem B7130911 : Blo 2225435 7130911 := bstep (se 1 (by rfl) ⟨5348183, by rfl⟩ : syracuseStep 7130911 = 10696367) B10696367
theorem B9507881 : Blo 2225435 9507881 := bstep (se 2 (by rfl) ⟨3565455, by rfl⟩ : syracuseStep 9507881 = 7130911) B7130911
theorem B6338587 : Blo 2225435 6338587 := bstep (se 1 (by rfl) ⟨4753940, by rfl⟩ : syracuseStep 6338587 = 9507881) B9507881
theorem B8451449 : Blo 2225435 8451449 := bstep (se 2 (by rfl) ⟨3169293, by rfl⟩ : syracuseStep 8451449 = 6338587) B6338587
theorem B5634299 : Blo 2225435 5634299 := bstep (se 1 (by rfl) ⟨4225724, by rfl⟩ : syracuseStep 5634299 = 8451449) B8451449
theorem B3756199 : Blo 2225435 3756199 := bstep (se 1 (by rfl) ⟨2817149, by rfl⟩ : syracuseStep 3756199 = 5634299) B5634299
theorem B5008265 : Blo 2225435 5008265 := bstep (se 2 (by rfl) ⟨1878099, by rfl⟩ : syracuseStep 5008265 = 3756199) B3756199
theorem B3338843 : Blo 2225435 3338843 := bstep (se 1 (by rfl) ⟨2504132, by rfl⟩ : syracuseStep 3338843 = 5008265) B5008265
theorem B2225895 : Blo 2225435 2225895 := bstep (se 1 (by rfl) ⟨1669421, by rfl⟩ : syracuseStep 2225895 = 3338843) B3338843
theorem B2504137 : Blo 2225435 2504137 := bbase (se 2 (by rfl) ⟨939051, by rfl⟩ : syracuseStep 2504137 = 1878103) (by norm_num)
theorem B3338849 : Blo 2225435 3338849 := bstep (se 2 (by rfl) ⟨1252068, by rfl⟩ : syracuseStep 3338849 = 2504137) B2504137
theorem B2225899 : Blo 2225435 2225899 := bstep (se 1 (by rfl) ⟨1669424, by rfl⟩ : syracuseStep 2225899 = 3338849) B3338849
theorem B19015829 : Blo 2225435 19015829 := bbase (se 6 (by rfl) ⟨445683, by rfl⟩ : syracuseStep 19015829 = 891367) (by norm_num)
theorem B12677219 : Blo 2225435 12677219 := bstep (se 1 (by rfl) ⟨9507914, by rfl⟩ : syracuseStep 12677219 = 19015829) B19015829
theorem B8451479 : Blo 2225435 8451479 := bstep (se 1 (by rfl) ⟨6338609, by rfl⟩ : syracuseStep 8451479 = 12677219) B12677219
theorem B5634319 : Blo 2225435 5634319 := bstep (se 1 (by rfl) ⟨4225739, by rfl⟩ : syracuseStep 5634319 = 8451479) B8451479
theorem B7512425 : Blo 2225435 7512425 := bstep (se 2 (by rfl) ⟨2817159, by rfl⟩ : syracuseStep 7512425 = 5634319) B5634319
theorem B5008283 : Blo 2225435 5008283 := bstep (se 1 (by rfl) ⟨3756212, by rfl⟩ : syracuseStep 5008283 = 7512425) B7512425
theorem B3338855 : Blo 2225435 3338855 := bstep (se 1 (by rfl) ⟨2504141, by rfl⟩ : syracuseStep 3338855 = 5008283) B5008283
theorem B2225903 : Blo 2225435 2225903 := bstep (se 1 (by rfl) ⟨1669427, by rfl⟩ : syracuseStep 2225903 = 3338855) B3338855
theorem B3338861 : Blo 2225435 3338861 := bbase (se 3 (by rfl) ⟨626036, by rfl⟩ : syracuseStep 3338861 = 1252073) (by norm_num)
theorem B2225907 : Blo 2225435 2225907 := bstep (se 1 (by rfl) ⟨1669430, by rfl⟩ : syracuseStep 2225907 = 3338861) B3338861
theorem B5008301 : Blo 2225435 5008301 := bbase (se 3 (by rfl) ⟨939056, by rfl⟩ : syracuseStep 5008301 = 1878113) (by norm_num)
theorem B3338867 : Blo 2225435 3338867 := bstep (se 1 (by rfl) ⟨2504150, by rfl⟩ : syracuseStep 3338867 = 5008301) B5008301
theorem B2225911 : Blo 2225435 2225911 := bstep (se 1 (by rfl) ⟨1669433, by rfl⟩ : syracuseStep 2225911 = 3338867) B3338867
theorem B6338645 : Blo 2225435 6338645 := bbase (se 8 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 6338645 = 74281) (by norm_num)
theorem B4225763 : Blo 2225435 4225763 := bstep (se 1 (by rfl) ⟨3169322, by rfl⟩ : syracuseStep 4225763 = 6338645) B6338645
theorem B2817175 : Blo 2225435 2817175 := bstep (se 1 (by rfl) ⟨2112881, by rfl⟩ : syracuseStep 2817175 = 4225763) B4225763
theorem B3756233 : Blo 2225435 3756233 := bstep (se 2 (by rfl) ⟨1408587, by rfl⟩ : syracuseStep 3756233 = 2817175) B2817175
theorem B2504155 : Blo 2225435 2504155 := bstep (se 1 (by rfl) ⟨1878116, by rfl⟩ : syracuseStep 2504155 = 3756233) B3756233
theorem B3338873 : Blo 2225435 3338873 := bstep (se 2 (by rfl) ⟨1252077, by rfl⟩ : syracuseStep 3338873 = 2504155) B2504155
theorem B2225915 : Blo 2225435 2225915 := bstep (se 1 (by rfl) ⟨1669436, by rfl⟩ : syracuseStep 2225915 = 3338873) B3338873
theorem B4121381 : Blo 2225435 4121381 := bbase (se 4 (by rfl) ⟨386379, by rfl⟩ : syracuseStep 4121381 = 772759) (by norm_num)
theorem B10990349 : Blo 2225435 10990349 := bstep (se 3 (by rfl) ⟨2060690, by rfl⟩ : syracuseStep 10990349 = 4121381) B4121381
theorem B7326899 : Blo 2225435 7326899 := bstep (se 1 (by rfl) ⟨5495174, by rfl⟩ : syracuseStep 7326899 = 10990349) B10990349
theorem B4884599 : Blo 2225435 4884599 := bstep (se 1 (by rfl) ⟨3663449, by rfl⟩ : syracuseStep 4884599 = 7326899) B7326899
theorem B3256399 : Blo 2225435 3256399 := bstep (se 1 (by rfl) ⟨2442299, by rfl⟩ : syracuseStep 3256399 = 4884599) B4884599
theorem B4341865 : Blo 2225435 4341865 := bstep (se 2 (by rfl) ⟨1628199, by rfl⟩ : syracuseStep 4341865 = 3256399) B3256399
theorem B5789153 : Blo 2225435 5789153 := bstep (se 2 (by rfl) ⟨2170932, by rfl⟩ : syracuseStep 5789153 = 4341865) B4341865
theorem B3859435 : Blo 2225435 3859435 := bstep (se 1 (by rfl) ⟨2894576, by rfl⟩ : syracuseStep 3859435 = 5789153) B5789153
theorem B5145913 : Blo 2225435 5145913 := bstep (se 2 (by rfl) ⟨1929717, by rfl⟩ : syracuseStep 5145913 = 3859435) B3859435
theorem B6861217 : Blo 2225435 6861217 := bstep (se 2 (by rfl) ⟨2572956, by rfl⟩ : syracuseStep 6861217 = 5145913) B5145913
theorem B146372629 : Blo 2225435 146372629 := bstep (se 6 (by rfl) ⟨3430608, by rfl⟩ : syracuseStep 146372629 = 6861217) B6861217
theorem B195163505 : Blo 2225435 195163505 := bstep (se 2 (by rfl) ⟨73186314, by rfl⟩ : syracuseStep 195163505 = 146372629) B146372629
theorem B130109003 : Blo 2225435 130109003 := bstep (se 1 (by rfl) ⟨97581752, by rfl⟩ : syracuseStep 130109003 = 195163505) B195163505
theorem B86739335 : Blo 2225435 86739335 := bstep (se 1 (by rfl) ⟨65054501, by rfl⟩ : syracuseStep 86739335 = 130109003) B130109003
theorem B57826223 : Blo 2225435 57826223 := bstep (se 1 (by rfl) ⟨43369667, by rfl⟩ : syracuseStep 57826223 = 86739335) B86739335
theorem B38550815 : Blo 2225435 38550815 := bstep (se 1 (by rfl) ⟨28913111, by rfl⟩ : syracuseStep 38550815 = 57826223) B57826223
theorem B25700543 : Blo 2225435 25700543 := bstep (se 1 (by rfl) ⟨19275407, by rfl⟩ : syracuseStep 25700543 = 38550815) B38550815
theorem B17133695 : Blo 2225435 17133695 := bstep (se 1 (by rfl) ⟨12850271, by rfl⟩ : syracuseStep 17133695 = 25700543) B25700543
theorem B11422463 : Blo 2225435 11422463 := bstep (se 1 (by rfl) ⟨8566847, by rfl⟩ : syracuseStep 11422463 = 17133695) B17133695
theorem B30459901 : Blo 2225435 30459901 := bstep (se 3 (by rfl) ⟨5711231, by rfl⟩ : syracuseStep 30459901 = 11422463) B11422463
theorem B40613201 : Blo 2225435 40613201 := bstep (se 2 (by rfl) ⟨15229950, by rfl⟩ : syracuseStep 40613201 = 30459901) B30459901
theorem B27075467 : Blo 2225435 27075467 := bstep (se 1 (by rfl) ⟨20306600, by rfl⟩ : syracuseStep 27075467 = 40613201) B40613201
theorem B18050311 : Blo 2225435 18050311 := bstep (se 1 (by rfl) ⟨13537733, by rfl⟩ : syracuseStep 18050311 = 27075467) B27075467
theorem B24067081 : Blo 2225435 24067081 := bstep (se 2 (by rfl) ⟨9025155, by rfl⟩ : syracuseStep 24067081 = 18050311) B18050311
theorem B32089441 : Blo 2225435 32089441 := bstep (se 2 (by rfl) ⟨12033540, by rfl⟩ : syracuseStep 32089441 = 24067081) B24067081
theorem B42785921 : Blo 2225435 42785921 := bstep (se 2 (by rfl) ⟨16044720, by rfl⟩ : syracuseStep 42785921 = 32089441) B32089441
theorem B28523947 : Blo 2225435 28523947 := bstep (se 1 (by rfl) ⟨21392960, by rfl⟩ : syracuseStep 28523947 = 42785921) B42785921
theorem B38031929 : Blo 2225435 38031929 := bstep (se 2 (by rfl) ⟨14261973, by rfl⟩ : syracuseStep 38031929 = 28523947) B28523947
theorem B25354619 : Blo 2225435 25354619 := bstep (se 1 (by rfl) ⟨19015964, by rfl⟩ : syracuseStep 25354619 = 38031929) B38031929
theorem B16903079 : Blo 2225435 16903079 := bstep (se 1 (by rfl) ⟨12677309, by rfl⟩ : syracuseStep 16903079 = 25354619) B25354619
theorem B11268719 : Blo 2225435 11268719 := bstep (se 1 (by rfl) ⟨8451539, by rfl⟩ : syracuseStep 11268719 = 16903079) B16903079
theorem B7512479 : Blo 2225435 7512479 := bstep (se 1 (by rfl) ⟨5634359, by rfl⟩ : syracuseStep 7512479 = 11268719) B11268719
theorem B5008319 : Blo 2225435 5008319 := bstep (se 1 (by rfl) ⟨3756239, by rfl⟩ : syracuseStep 5008319 = 7512479) B7512479
theorem B3338879 : Blo 2225435 3338879 := bstep (se 1 (by rfl) ⟨2504159, by rfl⟩ : syracuseStep 3338879 = 5008319) B5008319
theorem B2225919 : Blo 2225435 2225919 := bstep (se 1 (by rfl) ⟨1669439, by rfl⟩ : syracuseStep 2225919 = 3338879) B3338879
theorem B3338885 : Blo 2225435 3338885 := bbase (se 4 (by rfl) ⟨313020, by rfl⟩ : syracuseStep 3338885 = 626041) (by norm_num)
theorem B2225923 : Blo 2225435 2225923 := bstep (se 1 (by rfl) ⟨1669442, by rfl⟩ : syracuseStep 2225923 = 3338885) B3338885
theorem B3756253 : Blo 2225435 3756253 := bbase (se 3 (by rfl) ⟨704297, by rfl⟩ : syracuseStep 3756253 = 1408595) (by norm_num)
theorem B5008337 : Blo 2225435 5008337 := bstep (se 2 (by rfl) ⟨1878126, by rfl⟩ : syracuseStep 5008337 = 3756253) B3756253
theorem B3338891 : Blo 2225435 3338891 := bstep (se 1 (by rfl) ⟨2504168, by rfl⟩ : syracuseStep 3338891 = 5008337) B5008337
theorem B2225927 : Blo 2225435 2225927 := bstep (se 1 (by rfl) ⟨1669445, by rfl⟩ : syracuseStep 2225927 = 3338891) B3338891
theorem B2504173 : Blo 2225435 2504173 := bbase (se 3 (by rfl) ⟨469532, by rfl⟩ : syracuseStep 2504173 = 939065) (by norm_num)
theorem B3338897 : Blo 2225435 3338897 := bstep (se 2 (by rfl) ⟨1252086, by rfl⟩ : syracuseStep 3338897 = 2504173) B2504173
theorem B2225931 : Blo 2225435 2225931 := bstep (se 1 (by rfl) ⟨1669448, by rfl⟩ : syracuseStep 2225931 = 3338897) B3338897
theorem B7512533 : Blo 2225435 7512533 := bbase (se 7 (by rfl) ⟨88037, by rfl⟩ : syracuseStep 7512533 = 176075) (by norm_num)
theorem B5008355 : Blo 2225435 5008355 := bstep (se 1 (by rfl) ⟨3756266, by rfl⟩ : syracuseStep 5008355 = 7512533) B7512533
theorem B3338903 : Blo 2225435 3338903 := bstep (se 1 (by rfl) ⟨2504177, by rfl⟩ : syracuseStep 3338903 = 5008355) B5008355
theorem B2225935 : Blo 2225435 2225935 := bstep (se 1 (by rfl) ⟨1669451, by rfl⟩ : syracuseStep 2225935 = 3338903) B3338903
theorem B3338909 : Blo 2225435 3338909 := bbase (se 3 (by rfl) ⟨626045, by rfl⟩ : syracuseStep 3338909 = 1252091) (by norm_num)
theorem B2225939 : Blo 2225435 2225939 := bstep (se 1 (by rfl) ⟨1669454, by rfl⟩ : syracuseStep 2225939 = 3338909) B3338909
theorem B5008373 : Blo 2225435 5008373 := bbase (se 5 (by rfl) ⟨234767, by rfl⟩ : syracuseStep 5008373 = 469535) (by norm_num)
theorem B3338915 : Blo 2225435 3338915 := bstep (se 1 (by rfl) ⟨2504186, by rfl⟩ : syracuseStep 3338915 = 5008373) B5008373
theorem B2225943 : Blo 2225435 2225943 := bstep (se 1 (by rfl) ⟨1669457, by rfl⟩ : syracuseStep 2225943 = 3338915) B3338915
theorem B9637829 : Blo 2225435 9637829 := bbase (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) (by norm_num)
theorem B6425219 : Blo 2225435 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B4283479 : Blo 2225435 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B5711305 : Blo 2225435 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B7615073 : Blo 2225435 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B20306861 : Blo 2225435 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B13537907 : Blo 2225435 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B9025271 : Blo 2225435 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B6016847 : Blo 2225435 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B64179701 : Blo 2225435 64179701 := bstep (se 5 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 64179701 = 6016847) B6016847
theorem B42786467 : Blo 2225435 42786467 := bstep (se 1 (by rfl) ⟨32089850, by rfl⟩ : syracuseStep 42786467 = 64179701) B64179701
theorem B28524311 : Blo 2225435 28524311 := bstep (se 1 (by rfl) ⟨21393233, by rfl⟩ : syracuseStep 28524311 = 42786467) B42786467
theorem B19016207 : Blo 2225435 19016207 := bstep (se 1 (by rfl) ⟨14262155, by rfl⟩ : syracuseStep 19016207 = 28524311) B28524311
theorem B12677471 : Blo 2225435 12677471 := bstep (se 1 (by rfl) ⟨9508103, by rfl⟩ : syracuseStep 12677471 = 19016207) B19016207
theorem B8451647 : Blo 2225435 8451647 := bstep (se 1 (by rfl) ⟨6338735, by rfl⟩ : syracuseStep 8451647 = 12677471) B12677471
theorem B5634431 : Blo 2225435 5634431 := bstep (se 1 (by rfl) ⟨4225823, by rfl⟩ : syracuseStep 5634431 = 8451647) B8451647
theorem B3756287 : Blo 2225435 3756287 := bstep (se 1 (by rfl) ⟨2817215, by rfl⟩ : syracuseStep 3756287 = 5634431) B5634431
theorem B2504191 : Blo 2225435 2504191 := bstep (se 1 (by rfl) ⟨1878143, by rfl⟩ : syracuseStep 2504191 = 3756287) B3756287
theorem B3338921 : Blo 2225435 3338921 := bstep (se 2 (by rfl) ⟨1252095, by rfl⟩ : syracuseStep 3338921 = 2504191) B2504191
theorem B2225947 : Blo 2225435 2225947 := bstep (se 1 (by rfl) ⟨1669460, by rfl⟩ : syracuseStep 2225947 = 3338921) B3338921
theorem B3169373 : Blo 2225435 3169373 := bbase (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) (by norm_num)
theorem B8451661 : Blo 2225435 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B11268881 : Blo 2225435 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B7512587 : Blo 2225435 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B5008391 : Blo 2225435 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B3338927 : Blo 2225435 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B2225951 : Blo 2225435 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B3338933 : Blo 2225435 3338933 := bbase (se 5 (by rfl) ⟨156512, by rfl⟩ : syracuseStep 3338933 = 313025) (by norm_num)
theorem B2225955 : Blo 2225435 2225955 := bstep (se 1 (by rfl) ⟨1669466, by rfl⟩ : syracuseStep 2225955 = 3338933) B3338933
theorem B5634461 : Blo 2225435 5634461 := bbase (se 3 (by rfl) ⟨1056461, by rfl⟩ : syracuseStep 5634461 = 2112923) (by norm_num)
theorem B3756307 : Blo 2225435 3756307 := bstep (se 1 (by rfl) ⟨2817230, by rfl⟩ : syracuseStep 3756307 = 5634461) B5634461
theorem B5008409 : Blo 2225435 5008409 := bstep (se 2 (by rfl) ⟨1878153, by rfl⟩ : syracuseStep 5008409 = 3756307) B3756307
theorem B3338939 : Blo 2225435 3338939 := bstep (se 1 (by rfl) ⟨2504204, by rfl⟩ : syracuseStep 3338939 = 5008409) B5008409
theorem B2225959 : Blo 2225435 2225959 := bstep (se 1 (by rfl) ⟨1669469, by rfl⟩ : syracuseStep 2225959 = 3338939) B3338939
theorem B2504209 : Blo 2225435 2504209 := bbase (se 2 (by rfl) ⟨939078, by rfl⟩ : syracuseStep 2504209 = 1878157) (by norm_num)
theorem B3338945 : Blo 2225435 3338945 := bstep (se 2 (by rfl) ⟨1252104, by rfl⟩ : syracuseStep 3338945 = 2504209) B2504209
theorem B2225963 : Blo 2225435 2225963 := bstep (se 1 (by rfl) ⟨1669472, by rfl⟩ : syracuseStep 2225963 = 3338945) B3338945
theorem B4225861 : Blo 2225435 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B5634481 : Blo 2225435 5634481 := bstep (se 2 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 5634481 = 4225861) B4225861
theorem B7512641 : Blo 2225435 7512641 := bstep (se 2 (by rfl) ⟨2817240, by rfl⟩ : syracuseStep 7512641 = 5634481) B5634481
theorem B5008427 : Blo 2225435 5008427 := bstep (se 1 (by rfl) ⟨3756320, by rfl⟩ : syracuseStep 5008427 = 7512641) B7512641
theorem B3338951 : Blo 2225435 3338951 := bstep (se 1 (by rfl) ⟨2504213, by rfl⟩ : syracuseStep 3338951 = 5008427) B5008427
theorem B2225967 : Blo 2225435 2225967 := bstep (se 1 (by rfl) ⟨1669475, by rfl⟩ : syracuseStep 2225967 = 3338951) B3338951
theorem B3338957 : Blo 2225435 3338957 := bbase (se 3 (by rfl) ⟨626054, by rfl⟩ : syracuseStep 3338957 = 1252109) (by norm_num)
theorem B2225971 : Blo 2225435 2225971 := bstep (se 1 (by rfl) ⟨1669478, by rfl⟩ : syracuseStep 2225971 = 3338957) B3338957
theorem B5008445 : Blo 2225435 5008445 := bbase (se 3 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 5008445 = 1878167) (by norm_num)
theorem B3338963 : Blo 2225435 3338963 := bstep (se 1 (by rfl) ⟨2504222, by rfl⟩ : syracuseStep 3338963 = 5008445) B5008445
theorem B2225975 : Blo 2225435 2225975 := bstep (se 1 (by rfl) ⟨1669481, by rfl⟩ : syracuseStep 2225975 = 3338963) B3338963
theorem B3756341 : Blo 2225435 3756341 := bbase (se 5 (by rfl) ⟨176078, by rfl⟩ : syracuseStep 3756341 = 352157) (by norm_num)
theorem B2504227 : Blo 2225435 2504227 := bstep (se 1 (by rfl) ⟨1878170, by rfl⟩ : syracuseStep 2504227 = 3756341) B3756341
theorem B3338969 : Blo 2225435 3338969 := bstep (se 2 (by rfl) ⟨1252113, by rfl⟩ : syracuseStep 3338969 = 2504227) B2504227
theorem B2225979 : Blo 2225435 2225979 := bstep (se 1 (by rfl) ⟨1669484, by rfl⟩ : syracuseStep 2225979 = 3338969) B3338969
theorem B6338837 : Blo 2225435 6338837 := bbase (se 6 (by rfl) ⟨148566, by rfl⟩ : syracuseStep 6338837 = 297133) (by norm_num)
theorem B16903565 : Blo 2225435 16903565 := bstep (se 3 (by rfl) ⟨3169418, by rfl⟩ : syracuseStep 16903565 = 6338837) B6338837
theorem B11269043 : Blo 2225435 11269043 := bstep (se 1 (by rfl) ⟨8451782, by rfl⟩ : syracuseStep 11269043 = 16903565) B16903565
theorem B7512695 : Blo 2225435 7512695 := bstep (se 1 (by rfl) ⟨5634521, by rfl⟩ : syracuseStep 7512695 = 11269043) B11269043
theorem B5008463 : Blo 2225435 5008463 := bstep (se 1 (by rfl) ⟨3756347, by rfl⟩ : syracuseStep 5008463 = 7512695) B7512695
theorem B3338975 : Blo 2225435 3338975 := bstep (se 1 (by rfl) ⟨2504231, by rfl⟩ : syracuseStep 3338975 = 5008463) B5008463
theorem B2225983 : Blo 2225435 2225983 := bstep (se 1 (by rfl) ⟨1669487, by rfl⟩ : syracuseStep 2225983 = 3338975) B3338975
theorem B3338981 : Blo 2225435 3338981 := bbase (se 4 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 3338981 = 626059) (by norm_num)
theorem B2225987 : Blo 2225435 2225987 := bstep (se 1 (by rfl) ⟨1669490, by rfl⟩ : syracuseStep 2225987 = 3338981) B3338981
theorem B2377073 : Blo 2225435 2377073 := bbase (se 2 (by rfl) ⟨891402, by rfl⟩ : syracuseStep 2377073 = 1782805) (by norm_num)
theorem B6338861 : Blo 2225435 6338861 := bstep (se 3 (by rfl) ⟨1188536, by rfl⟩ : syracuseStep 6338861 = 2377073) B2377073
theorem B4225907 : Blo 2225435 4225907 := bstep (se 1 (by rfl) ⟨3169430, by rfl⟩ : syracuseStep 4225907 = 6338861) B6338861
theorem B2817271 : Blo 2225435 2817271 := bstep (se 1 (by rfl) ⟨2112953, by rfl⟩ : syracuseStep 2817271 = 4225907) B4225907
theorem B3756361 : Blo 2225435 3756361 := bstep (se 2 (by rfl) ⟨1408635, by rfl⟩ : syracuseStep 3756361 = 2817271) B2817271
theorem B5008481 : Blo 2225435 5008481 := bstep (se 2 (by rfl) ⟨1878180, by rfl⟩ : syracuseStep 5008481 = 3756361) B3756361
theorem B3338987 : Blo 2225435 3338987 := bstep (se 1 (by rfl) ⟨2504240, by rfl⟩ : syracuseStep 3338987 = 5008481) B5008481
theorem B2225991 : Blo 2225435 2225991 := bstep (se 1 (by rfl) ⟨1669493, by rfl⟩ : syracuseStep 2225991 = 3338987) B3338987
theorem B2504245 : Blo 2225435 2504245 := bbase (se 5 (by rfl) ⟨117386, by rfl⟩ : syracuseStep 2504245 = 234773) (by norm_num)
theorem B3338993 : Blo 2225435 3338993 := bstep (se 2 (by rfl) ⟨1252122, by rfl⟩ : syracuseStep 3338993 = 2504245) B2504245
theorem B2225995 : Blo 2225435 2225995 := bstep (se 1 (by rfl) ⟨1669496, by rfl⟩ : syracuseStep 2225995 = 3338993) B3338993
theorem B2817281 : Blo 2225435 2817281 := bbase (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) (by norm_num)
theorem B7512749 : Blo 2225435 7512749 := bstep (se 3 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 7512749 = 2817281) B2817281
theorem B5008499 : Blo 2225435 5008499 := bstep (se 1 (by rfl) ⟨3756374, by rfl⟩ : syracuseStep 5008499 = 7512749) B7512749
theorem B3338999 : Blo 2225435 3338999 := bstep (se 1 (by rfl) ⟨2504249, by rfl⟩ : syracuseStep 3338999 = 5008499) B5008499
theorem B2225999 : Blo 2225435 2225999 := bstep (se 1 (by rfl) ⟨1669499, by rfl⟩ : syracuseStep 2225999 = 3338999) B3338999
theorem B3339005 : Blo 2225435 3339005 := bbase (se 3 (by rfl) ⟨626063, by rfl⟩ : syracuseStep 3339005 = 1252127) (by norm_num)
theorem B2226003 : Blo 2225435 2226003 := bstep (se 1 (by rfl) ⟨1669502, by rfl⟩ : syracuseStep 2226003 = 3339005) B3339005
theorem B5008517 : Blo 2225435 5008517 := bbase (se 4 (by rfl) ⟨469548, by rfl⟩ : syracuseStep 5008517 = 939097) (by norm_num)
theorem B3339011 : Blo 2225435 3339011 := bstep (se 1 (by rfl) ⟨2504258, by rfl⟩ : syracuseStep 3339011 = 5008517) B5008517
theorem B2226007 : Blo 2225435 2226007 := bstep (se 1 (by rfl) ⟨1669505, by rfl⟩ : syracuseStep 2226007 = 3339011) B3339011
theorem B4754189 : Blo 2225435 4754189 := bbase (se 3 (by rfl) ⟨891410, by rfl⟩ : syracuseStep 4754189 = 1782821) (by norm_num)
theorem B3169459 : Blo 2225435 3169459 := bstep (se 1 (by rfl) ⟨2377094, by rfl⟩ : syracuseStep 3169459 = 4754189) B4754189
theorem B4225945 : Blo 2225435 4225945 := bstep (se 2 (by rfl) ⟨1584729, by rfl⟩ : syracuseStep 4225945 = 3169459) B3169459
theorem B5634593 : Blo 2225435 5634593 := bstep (se 2 (by rfl) ⟨2112972, by rfl⟩ : syracuseStep 5634593 = 4225945) B4225945
theorem B3756395 : Blo 2225435 3756395 := bstep (se 1 (by rfl) ⟨2817296, by rfl⟩ : syracuseStep 3756395 = 5634593) B5634593
theorem B2504263 : Blo 2225435 2504263 := bstep (se 1 (by rfl) ⟨1878197, by rfl⟩ : syracuseStep 2504263 = 3756395) B3756395
theorem B3339017 : Blo 2225435 3339017 := bstep (se 2 (by rfl) ⟨1252131, by rfl⟩ : syracuseStep 3339017 = 2504263) B2504263
theorem B2226011 : Blo 2225435 2226011 := bstep (se 1 (by rfl) ⟨1669508, by rfl⟩ : syracuseStep 2226011 = 3339017) B3339017
theorem B11269205 : Blo 2225435 11269205 := bbase (se 8 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 11269205 = 132061) (by norm_num)
theorem B7512803 : Blo 2225435 7512803 := bstep (se 1 (by rfl) ⟨5634602, by rfl⟩ : syracuseStep 7512803 = 11269205) B11269205
theorem B5008535 : Blo 2225435 5008535 := bstep (se 1 (by rfl) ⟨3756401, by rfl⟩ : syracuseStep 5008535 = 7512803) B7512803
theorem B3339023 : Blo 2225435 3339023 := bstep (se 1 (by rfl) ⟨2504267, by rfl⟩ : syracuseStep 3339023 = 5008535) B5008535
theorem B2226015 : Blo 2225435 2226015 := bstep (se 1 (by rfl) ⟨1669511, by rfl⟩ : syracuseStep 2226015 = 3339023) B3339023
theorem B3339029 : Blo 2225435 3339029 := bbase (se 6 (by rfl) ⟨78258, by rfl⟩ : syracuseStep 3339029 = 156517) (by norm_num)
theorem B2226019 : Blo 2225435 2226019 := bstep (se 1 (by rfl) ⟨1669514, by rfl⟩ : syracuseStep 2226019 = 3339029) B3339029
theorem B42787925 : Blo 2225435 42787925 := bbase (se 8 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 42787925 = 501421) (by norm_num)
theorem B28525283 : Blo 2225435 28525283 := bstep (se 1 (by rfl) ⟨21393962, by rfl⟩ : syracuseStep 28525283 = 42787925) B42787925
theorem B19016855 : Blo 2225435 19016855 := bstep (se 1 (by rfl) ⟨14262641, by rfl⟩ : syracuseStep 19016855 = 28525283) B28525283
theorem B12677903 : Blo 2225435 12677903 := bstep (se 1 (by rfl) ⟨9508427, by rfl⟩ : syracuseStep 12677903 = 19016855) B19016855
theorem B8451935 : Blo 2225435 8451935 := bstep (se 1 (by rfl) ⟨6338951, by rfl⟩ : syracuseStep 8451935 = 12677903) B12677903
theorem B5634623 : Blo 2225435 5634623 := bstep (se 1 (by rfl) ⟨4225967, by rfl⟩ : syracuseStep 5634623 = 8451935) B8451935
theorem B3756415 : Blo 2225435 3756415 := bstep (se 1 (by rfl) ⟨2817311, by rfl⟩ : syracuseStep 3756415 = 5634623) B5634623
theorem B5008553 : Blo 2225435 5008553 := bstep (se 2 (by rfl) ⟨1878207, by rfl⟩ : syracuseStep 5008553 = 3756415) B3756415
theorem B3339035 : Blo 2225435 3339035 := bstep (se 1 (by rfl) ⟨2504276, by rfl⟩ : syracuseStep 3339035 = 5008553) B5008553
theorem B2226023 : Blo 2225435 2226023 := bstep (se 1 (by rfl) ⟨1669517, by rfl⟩ : syracuseStep 2226023 = 3339035) B3339035
theorem B2504281 : Blo 2225435 2504281 := bbase (se 2 (by rfl) ⟨939105, by rfl⟩ : syracuseStep 2504281 = 1878211) (by norm_num)
theorem B3339041 : Blo 2225435 3339041 := bstep (se 2 (by rfl) ⟨1252140, by rfl⟩ : syracuseStep 3339041 = 2504281) B2504281
theorem B2226027 : Blo 2225435 2226027 := bstep (se 1 (by rfl) ⟨1669520, by rfl⟩ : syracuseStep 2226027 = 3339041) B3339041
theorem B3384605 : Blo 2225435 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B9025613 : Blo 2225435 9025613 := bstep (se 3 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 9025613 = 3384605) B3384605
theorem B6017075 : Blo 2225435 6017075 := bstep (se 1 (by rfl) ⟨4512806, by rfl⟩ : syracuseStep 6017075 = 9025613) B9025613
theorem B4011383 : Blo 2225435 4011383 := bstep (se 1 (by rfl) ⟨3008537, by rfl⟩ : syracuseStep 4011383 = 6017075) B6017075
theorem B10697021 : Blo 2225435 10697021 := bstep (se 3 (by rfl) ⟨2005691, by rfl⟩ : syracuseStep 10697021 = 4011383) B4011383
theorem B7131347 : Blo 2225435 7131347 := bstep (se 1 (by rfl) ⟨5348510, by rfl⟩ : syracuseStep 7131347 = 10697021) B10697021
theorem B4754231 : Blo 2225435 4754231 := bstep (se 1 (by rfl) ⟨3565673, by rfl⟩ : syracuseStep 4754231 = 7131347) B7131347
theorem B3169487 : Blo 2225435 3169487 := bstep (se 1 (by rfl) ⟨2377115, by rfl⟩ : syracuseStep 3169487 = 4754231) B4754231
theorem B8451965 : Blo 2225435 8451965 := bstep (se 3 (by rfl) ⟨1584743, by rfl⟩ : syracuseStep 8451965 = 3169487) B3169487
theorem B5634643 : Blo 2225435 5634643 := bstep (se 1 (by rfl) ⟨4225982, by rfl⟩ : syracuseStep 5634643 = 8451965) B8451965
theorem B7512857 : Blo 2225435 7512857 := bstep (se 2 (by rfl) ⟨2817321, by rfl⟩ : syracuseStep 7512857 = 5634643) B5634643
theorem B5008571 : Blo 2225435 5008571 := bstep (se 1 (by rfl) ⟨3756428, by rfl⟩ : syracuseStep 5008571 = 7512857) B7512857
theorem B3339047 : Blo 2225435 3339047 := bstep (se 1 (by rfl) ⟨2504285, by rfl⟩ : syracuseStep 3339047 = 5008571) B5008571
theorem B2226031 : Blo 2225435 2226031 := bstep (se 1 (by rfl) ⟨1669523, by rfl⟩ : syracuseStep 2226031 = 3339047) B3339047
theorem B3339053 : Blo 2225435 3339053 := bbase (se 3 (by rfl) ⟨626072, by rfl⟩ : syracuseStep 3339053 = 1252145) (by norm_num)
theorem B2226035 : Blo 2225435 2226035 := bstep (se 1 (by rfl) ⟨1669526, by rfl⟩ : syracuseStep 2226035 = 3339053) B3339053
theorem B5008589 : Blo 2225435 5008589 := bbase (se 3 (by rfl) ⟨939110, by rfl⟩ : syracuseStep 5008589 = 1878221) (by norm_num)
theorem B3339059 : Blo 2225435 3339059 := bstep (se 1 (by rfl) ⟨2504294, by rfl⟩ : syracuseStep 3339059 = 5008589) B5008589
theorem B2226039 : Blo 2225435 2226039 := bstep (se 1 (by rfl) ⟨1669529, by rfl⟩ : syracuseStep 2226039 = 3339059) B3339059
theorem B2817337 : Blo 2225435 2817337 := bbase (se 2 (by rfl) ⟨1056501, by rfl⟩ : syracuseStep 2817337 = 2113003) (by norm_num)
theorem B3756449 : Blo 2225435 3756449 := bstep (se 2 (by rfl) ⟨1408668, by rfl⟩ : syracuseStep 3756449 = 2817337) B2817337
theorem B2504299 : Blo 2225435 2504299 := bstep (se 1 (by rfl) ⟨1878224, by rfl⟩ : syracuseStep 2504299 = 3756449) B3756449
theorem B3339065 : Blo 2225435 3339065 := bstep (se 2 (by rfl) ⟨1252149, by rfl⟩ : syracuseStep 3339065 = 2504299) B2504299
theorem B2226043 : Blo 2225435 2226043 := bstep (se 1 (by rfl) ⟨1669532, by rfl⟩ : syracuseStep 2226043 = 3339065) B3339065
theorem B7131397 : Blo 2225435 7131397 := bbase (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) (by norm_num)
theorem B9508529 : Blo 2225435 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B25356077 : Blo 2225435 25356077 := bstep (se 3 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 25356077 = 9508529) B9508529
theorem B16904051 : Blo 2225435 16904051 := bstep (se 1 (by rfl) ⟨12678038, by rfl⟩ : syracuseStep 16904051 = 25356077) B25356077
theorem B11269367 : Blo 2225435 11269367 := bstep (se 1 (by rfl) ⟨8452025, by rfl⟩ : syracuseStep 11269367 = 16904051) B16904051
theorem B7512911 : Blo 2225435 7512911 := bstep (se 1 (by rfl) ⟨5634683, by rfl⟩ : syracuseStep 7512911 = 11269367) B11269367
theorem B5008607 : Blo 2225435 5008607 := bstep (se 1 (by rfl) ⟨3756455, by rfl⟩ : syracuseStep 5008607 = 7512911) B7512911
theorem B3339071 : Blo 2225435 3339071 := bstep (se 1 (by rfl) ⟨2504303, by rfl⟩ : syracuseStep 3339071 = 5008607) B5008607
theorem B2226047 : Blo 2225435 2226047 := bstep (se 1 (by rfl) ⟨1669535, by rfl⟩ : syracuseStep 2226047 = 3339071) B3339071
theorem B3339077 : Blo 2225435 3339077 := bbase (se 4 (by rfl) ⟨313038, by rfl⟩ : syracuseStep 3339077 = 626077) (by norm_num)
theorem B2226051 : Blo 2225435 2226051 := bstep (se 1 (by rfl) ⟨1669538, by rfl⟩ : syracuseStep 2226051 = 3339077) B3339077
theorem B3756469 : Blo 2225435 3756469 := bbase (se 5 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 3756469 = 352169) (by norm_num)
theorem B5008625 : Blo 2225435 5008625 := bstep (se 2 (by rfl) ⟨1878234, by rfl⟩ : syracuseStep 5008625 = 3756469) B3756469
theorem B3339083 : Blo 2225435 3339083 := bstep (se 1 (by rfl) ⟨2504312, by rfl⟩ : syracuseStep 3339083 = 5008625) B5008625
theorem B2226055 : Blo 2225435 2226055 := bstep (se 1 (by rfl) ⟨1669541, by rfl⟩ : syracuseStep 2226055 = 3339083) B3339083
theorem B2504317 : Blo 2225435 2504317 := bbase (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) (by norm_num)
theorem B3339089 : Blo 2225435 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2226059 : Blo 2225435 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B7512965 : Blo 2225435 7512965 := bbase (se 4 (by rfl) ⟨704340, by rfl⟩ : syracuseStep 7512965 = 1408681) (by norm_num)
theorem B5008643 : Blo 2225435 5008643 := bstep (se 1 (by rfl) ⟨3756482, by rfl⟩ : syracuseStep 5008643 = 7512965) B7512965
theorem B3339095 : Blo 2225435 3339095 := bstep (se 1 (by rfl) ⟨2504321, by rfl⟩ : syracuseStep 3339095 = 5008643) B5008643
theorem B2226063 : Blo 2225435 2226063 := bstep (se 1 (by rfl) ⟨1669547, by rfl⟩ : syracuseStep 2226063 = 3339095) B3339095
theorem B3339101 : Blo 2225435 3339101 := bbase (se 3 (by rfl) ⟨626081, by rfl⟩ : syracuseStep 3339101 = 1252163) (by norm_num)
theorem B2226067 : Blo 2225435 2226067 := bstep (se 1 (by rfl) ⟨1669550, by rfl⟩ : syracuseStep 2226067 = 3339101) B3339101
theorem B5008661 : Blo 2225435 5008661 := bbase (se 6 (by rfl) ⟨117390, by rfl⟩ : syracuseStep 5008661 = 234781) (by norm_num)
theorem B3339107 : Blo 2225435 3339107 := bstep (se 1 (by rfl) ⟨2504330, by rfl⟩ : syracuseStep 3339107 = 5008661) B5008661
theorem B2226071 : Blo 2225435 2226071 := bstep (se 1 (by rfl) ⟨1669553, by rfl⟩ : syracuseStep 2226071 = 3339107) B3339107
theorem B8452133 : Blo 2225435 8452133 := bbase (se 4 (by rfl) ⟨792387, by rfl⟩ : syracuseStep 8452133 = 1584775) (by norm_num)
theorem B5634755 : Blo 2225435 5634755 := bstep (se 1 (by rfl) ⟨4226066, by rfl⟩ : syracuseStep 5634755 = 8452133) B8452133
theorem B3756503 : Blo 2225435 3756503 := bstep (se 1 (by rfl) ⟨2817377, by rfl⟩ : syracuseStep 3756503 = 5634755) B5634755
theorem B2504335 : Blo 2225435 2504335 := bstep (se 1 (by rfl) ⟨1878251, by rfl⟩ : syracuseStep 2504335 = 3756503) B3756503
theorem B3339113 : Blo 2225435 3339113 := bstep (se 2 (by rfl) ⟨1252167, by rfl⟩ : syracuseStep 3339113 = 2504335) B2504335
theorem B2226075 : Blo 2225435 2226075 := bstep (se 1 (by rfl) ⟨1669556, by rfl⟩ : syracuseStep 2226075 = 3339113) B3339113
theorem B4754333 : Blo 2225435 4754333 := bbase (se 3 (by rfl) ⟨891437, by rfl⟩ : syracuseStep 4754333 = 1782875) (by norm_num)
theorem B12678221 : Blo 2225435 12678221 := bstep (se 3 (by rfl) ⟨2377166, by rfl⟩ : syracuseStep 12678221 = 4754333) B4754333
theorem B8452147 : Blo 2225435 8452147 := bstep (se 1 (by rfl) ⟨6339110, by rfl⟩ : syracuseStep 8452147 = 12678221) B12678221
theorem B11269529 : Blo 2225435 11269529 := bstep (se 2 (by rfl) ⟨4226073, by rfl⟩ : syracuseStep 11269529 = 8452147) B8452147
theorem B7513019 : Blo 2225435 7513019 := bstep (se 1 (by rfl) ⟨5634764, by rfl⟩ : syracuseStep 7513019 = 11269529) B11269529
theorem B5008679 : Blo 2225435 5008679 := bstep (se 1 (by rfl) ⟨3756509, by rfl⟩ : syracuseStep 5008679 = 7513019) B7513019
theorem B3339119 : Blo 2225435 3339119 := bstep (se 1 (by rfl) ⟨2504339, by rfl⟩ : syracuseStep 3339119 = 5008679) B5008679
theorem B2226079 : Blo 2225435 2226079 := bstep (se 1 (by rfl) ⟨1669559, by rfl⟩ : syracuseStep 2226079 = 3339119) B3339119
theorem B3339125 : Blo 2225435 3339125 := bbase (se 5 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 3339125 = 313043) (by norm_num)
theorem B2226083 : Blo 2225435 2226083 := bstep (se 1 (by rfl) ⟨1669562, by rfl⟩ : syracuseStep 2226083 = 3339125) B3339125
theorem B12034453 : Blo 2225435 12034453 := bbase (se 6 (by rfl) ⟨282057, by rfl⟩ : syracuseStep 12034453 = 564115) (by norm_num)
theorem B16045937 : Blo 2225435 16045937 := bstep (se 2 (by rfl) ⟨6017226, by rfl⟩ : syracuseStep 16045937 = 12034453) B12034453
theorem B10697291 : Blo 2225435 10697291 := bstep (se 1 (by rfl) ⟨8022968, by rfl⟩ : syracuseStep 10697291 = 16045937) B16045937
theorem B7131527 : Blo 2225435 7131527 := bstep (se 1 (by rfl) ⟨5348645, by rfl⟩ : syracuseStep 7131527 = 10697291) B10697291
theorem B4754351 : Blo 2225435 4754351 := bstep (se 1 (by rfl) ⟨3565763, by rfl⟩ : syracuseStep 4754351 = 7131527) B7131527
theorem B3169567 : Blo 2225435 3169567 := bstep (se 1 (by rfl) ⟨2377175, by rfl⟩ : syracuseStep 3169567 = 4754351) B4754351
theorem B4226089 : Blo 2225435 4226089 := bstep (se 2 (by rfl) ⟨1584783, by rfl⟩ : syracuseStep 4226089 = 3169567) B3169567
theorem B5634785 : Blo 2225435 5634785 := bstep (se 2 (by rfl) ⟨2113044, by rfl⟩ : syracuseStep 5634785 = 4226089) B4226089
theorem B3756523 : Blo 2225435 3756523 := bstep (se 1 (by rfl) ⟨2817392, by rfl⟩ : syracuseStep 3756523 = 5634785) B5634785
theorem B5008697 : Blo 2225435 5008697 := bstep (se 2 (by rfl) ⟨1878261, by rfl⟩ : syracuseStep 5008697 = 3756523) B3756523
theorem B3339131 : Blo 2225435 3339131 := bstep (se 1 (by rfl) ⟨2504348, by rfl⟩ : syracuseStep 3339131 = 5008697) B5008697
theorem B2226087 : Blo 2225435 2226087 := bstep (se 1 (by rfl) ⟨1669565, by rfl⟩ : syracuseStep 2226087 = 3339131) B3339131
theorem B2504353 : Blo 2225435 2504353 := bbase (se 2 (by rfl) ⟨939132, by rfl⟩ : syracuseStep 2504353 = 1878265) (by norm_num)
theorem B3339137 : Blo 2225435 3339137 := bstep (se 2 (by rfl) ⟨1252176, by rfl⟩ : syracuseStep 3339137 = 2504353) B2504353
theorem B2226091 : Blo 2225435 2226091 := bstep (se 1 (by rfl) ⟨1669568, by rfl⟩ : syracuseStep 2226091 = 3339137) B3339137
theorem B5634805 : Blo 2225435 5634805 := bbase (se 5 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 5634805 = 528263) (by norm_num)
theorem B7513073 : Blo 2225435 7513073 := bstep (se 2 (by rfl) ⟨2817402, by rfl⟩ : syracuseStep 7513073 = 5634805) B5634805
theorem B5008715 : Blo 2225435 5008715 := bstep (se 1 (by rfl) ⟨3756536, by rfl⟩ : syracuseStep 5008715 = 7513073) B7513073
theorem B3339143 : Blo 2225435 3339143 := bstep (se 1 (by rfl) ⟨2504357, by rfl⟩ : syracuseStep 3339143 = 5008715) B5008715
theorem B2226095 : Blo 2225435 2226095 := bstep (se 1 (by rfl) ⟨1669571, by rfl⟩ : syracuseStep 2226095 = 3339143) B3339143
theorem B3339149 : Blo 2225435 3339149 := bbase (se 3 (by rfl) ⟨626090, by rfl⟩ : syracuseStep 3339149 = 1252181) (by norm_num)
theorem B2226099 : Blo 2225435 2226099 := bstep (se 1 (by rfl) ⟨1669574, by rfl⟩ : syracuseStep 2226099 = 3339149) B3339149
theorem B5008733 : Blo 2225435 5008733 := bbase (se 3 (by rfl) ⟨939137, by rfl⟩ : syracuseStep 5008733 = 1878275) (by norm_num)
theorem B3339155 : Blo 2225435 3339155 := bstep (se 1 (by rfl) ⟨2504366, by rfl⟩ : syracuseStep 3339155 = 5008733) B5008733
theorem B2226103 : Blo 2225435 2226103 := bstep (se 1 (by rfl) ⟨1669577, by rfl⟩ : syracuseStep 2226103 = 3339155) B3339155
theorem B3756557 : Blo 2225435 3756557 := bbase (se 3 (by rfl) ⟨704354, by rfl⟩ : syracuseStep 3756557 = 1408709) (by norm_num)
theorem B2504371 : Blo 2225435 2504371 := bstep (se 1 (by rfl) ⟨1878278, by rfl⟩ : syracuseStep 2504371 = 3756557) B3756557
theorem B3339161 : Blo 2225435 3339161 := bstep (se 2 (by rfl) ⟨1252185, by rfl⟩ : syracuseStep 3339161 = 2504371) B2504371
theorem B2226107 : Blo 2225435 2226107 := bstep (se 1 (by rfl) ⟨1669580, by rfl⟩ : syracuseStep 2226107 = 3339161) B3339161
theorem B2538545 : Blo 2225435 2538545 := bbase (se 2 (by rfl) ⟨951954, by rfl⟩ : syracuseStep 2538545 = 1903909) (by norm_num)
theorem B6769453 : Blo 2225435 6769453 := bstep (se 3 (by rfl) ⟨1269272, by rfl⟩ : syracuseStep 6769453 = 2538545) B2538545
theorem B9025937 : Blo 2225435 9025937 := bstep (se 2 (by rfl) ⟨3384726, by rfl⟩ : syracuseStep 9025937 = 6769453) B6769453
theorem B6017291 : Blo 2225435 6017291 := bstep (se 1 (by rfl) ⟨4512968, by rfl⟩ : syracuseStep 6017291 = 9025937) B9025937
theorem B4011527 : Blo 2225435 4011527 := bstep (se 1 (by rfl) ⟨3008645, by rfl⟩ : syracuseStep 4011527 = 6017291) B6017291
theorem B2674351 : Blo 2225435 2674351 := bstep (se 1 (by rfl) ⟨2005763, by rfl⟩ : syracuseStep 2674351 = 4011527) B4011527
theorem B3565801 : Blo 2225435 3565801 := bstep (se 2 (by rfl) ⟨1337175, by rfl⟩ : syracuseStep 3565801 = 2674351) B2674351
theorem B19017605 : Blo 2225435 19017605 := bstep (se 4 (by rfl) ⟨1782900, by rfl⟩ : syracuseStep 19017605 = 3565801) B3565801
theorem B12678403 : Blo 2225435 12678403 := bstep (se 1 (by rfl) ⟨9508802, by rfl⟩ : syracuseStep 12678403 = 19017605) B19017605
theorem B16904537 : Blo 2225435 16904537 := bstep (se 2 (by rfl) ⟨6339201, by rfl⟩ : syracuseStep 16904537 = 12678403) B12678403
theorem B11269691 : Blo 2225435 11269691 := bstep (se 1 (by rfl) ⟨8452268, by rfl⟩ : syracuseStep 11269691 = 16904537) B16904537
theorem B7513127 : Blo 2225435 7513127 := bstep (se 1 (by rfl) ⟨5634845, by rfl⟩ : syracuseStep 7513127 = 11269691) B11269691
theorem B5008751 : Blo 2225435 5008751 := bstep (se 1 (by rfl) ⟨3756563, by rfl⟩ : syracuseStep 5008751 = 7513127) B7513127
theorem B3339167 : Blo 2225435 3339167 := bstep (se 1 (by rfl) ⟨2504375, by rfl⟩ : syracuseStep 3339167 = 5008751) B5008751
theorem B2226111 : Blo 2225435 2226111 := bstep (se 1 (by rfl) ⟨1669583, by rfl⟩ : syracuseStep 2226111 = 3339167) B3339167
theorem B3339173 : Blo 2225435 3339173 := bbase (se 4 (by rfl) ⟨313047, by rfl⟩ : syracuseStep 3339173 = 626095) (by norm_num)
theorem B2226115 : Blo 2225435 2226115 := bstep (se 1 (by rfl) ⟨1669586, by rfl⟩ : syracuseStep 2226115 = 3339173) B3339173
theorem B2817433 : Blo 2225435 2817433 := bbase (se 2 (by rfl) ⟨1056537, by rfl⟩ : syracuseStep 2817433 = 2113075) (by norm_num)
theorem B3756577 : Blo 2225435 3756577 := bstep (se 2 (by rfl) ⟨1408716, by rfl⟩ : syracuseStep 3756577 = 2817433) B2817433
theorem B5008769 : Blo 2225435 5008769 := bstep (se 2 (by rfl) ⟨1878288, by rfl⟩ : syracuseStep 5008769 = 3756577) B3756577
theorem B3339179 : Blo 2225435 3339179 := bstep (se 1 (by rfl) ⟨2504384, by rfl⟩ : syracuseStep 3339179 = 5008769) B5008769
theorem B2226119 : Blo 2225435 2226119 := bstep (se 1 (by rfl) ⟨1669589, by rfl⟩ : syracuseStep 2226119 = 3339179) B3339179
theorem B2504389 : Blo 2225435 2504389 := bbase (se 4 (by rfl) ⟨234786, by rfl⟩ : syracuseStep 2504389 = 469573) (by norm_num)
theorem B3339185 : Blo 2225435 3339185 := bstep (se 2 (by rfl) ⟨1252194, by rfl⟩ : syracuseStep 3339185 = 2504389) B2504389
theorem B2226123 : Blo 2225435 2226123 := bstep (se 1 (by rfl) ⟨1669592, by rfl⟩ : syracuseStep 2226123 = 3339185) B3339185
theorem B4226165 : Blo 2225435 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B2817443 : Blo 2225435 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B7513181 : Blo 2225435 7513181 := bstep (se 3 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 7513181 = 2817443) B2817443
theorem B5008787 : Blo 2225435 5008787 := bstep (se 1 (by rfl) ⟨3756590, by rfl⟩ : syracuseStep 5008787 = 7513181) B7513181
theorem B3339191 : Blo 2225435 3339191 := bstep (se 1 (by rfl) ⟨2504393, by rfl⟩ : syracuseStep 3339191 = 5008787) B5008787
theorem B2226127 : Blo 2225435 2226127 := bstep (se 1 (by rfl) ⟨1669595, by rfl⟩ : syracuseStep 2226127 = 3339191) B3339191
theorem B3339197 : Blo 2225435 3339197 := bbase (se 3 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 3339197 = 1252199) (by norm_num)
theorem B2226131 : Blo 2225435 2226131 := bstep (se 1 (by rfl) ⟨1669598, by rfl⟩ : syracuseStep 2226131 = 3339197) B3339197
theorem B5008805 : Blo 2225435 5008805 := bbase (se 4 (by rfl) ⟨469575, by rfl⟩ : syracuseStep 5008805 = 939151) (by norm_num)
theorem B3339203 : Blo 2225435 3339203 := bstep (se 1 (by rfl) ⟨2504402, by rfl⟩ : syracuseStep 3339203 = 5008805) B5008805
theorem B2226135 : Blo 2225435 2226135 := bstep (se 1 (by rfl) ⟨1669601, by rfl⟩ : syracuseStep 2226135 = 3339203) B3339203
theorem B5634917 : Blo 2225435 5634917 := bbase (se 4 (by rfl) ⟨528273, by rfl⟩ : syracuseStep 5634917 = 1056547) (by norm_num)
theorem B3756611 : Blo 2225435 3756611 := bstep (se 1 (by rfl) ⟨2817458, by rfl⟩ : syracuseStep 3756611 = 5634917) B5634917
theorem B2504407 : Blo 2225435 2504407 := bstep (se 1 (by rfl) ⟨1878305, by rfl⟩ : syracuseStep 2504407 = 3756611) B3756611
theorem B3339209 : Blo 2225435 3339209 := bstep (se 2 (by rfl) ⟨1252203, by rfl⟩ : syracuseStep 3339209 = 2504407) B2504407
theorem B2226139 : Blo 2225435 2226139 := bstep (se 1 (by rfl) ⟨1669604, by rfl⟩ : syracuseStep 2226139 = 3339209) B3339209
theorem B3565853 : Blo 2225435 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B2377235 : Blo 2225435 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B6339293 : Blo 2225435 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B4226195 : Blo 2225435 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B11269853 : Blo 2225435 11269853 := bstep (se 3 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 11269853 = 4226195) B4226195
theorem B7513235 : Blo 2225435 7513235 := bstep (se 1 (by rfl) ⟨5634926, by rfl⟩ : syracuseStep 7513235 = 11269853) B11269853
theorem B5008823 : Blo 2225435 5008823 := bstep (se 1 (by rfl) ⟨3756617, by rfl⟩ : syracuseStep 5008823 = 7513235) B7513235
theorem B3339215 : Blo 2225435 3339215 := bstep (se 1 (by rfl) ⟨2504411, by rfl⟩ : syracuseStep 3339215 = 5008823) B5008823
theorem B2226143 : Blo 2225435 2226143 := bstep (se 1 (by rfl) ⟨1669607, by rfl⟩ : syracuseStep 2226143 = 3339215) B3339215
theorem B3339221 : Blo 2225435 3339221 := bbase (se 7 (by rfl) ⟨39131, by rfl⟩ : syracuseStep 3339221 = 78263) (by norm_num)
theorem B2226147 : Blo 2225435 2226147 := bstep (se 1 (by rfl) ⟨1669610, by rfl⟩ : syracuseStep 2226147 = 3339221) B3339221
theorem B8452421 : Blo 2225435 8452421 := bbase (se 4 (by rfl) ⟨792414, by rfl⟩ : syracuseStep 8452421 = 1584829) (by norm_num)
theorem B5634947 : Blo 2225435 5634947 := bstep (se 1 (by rfl) ⟨4226210, by rfl⟩ : syracuseStep 5634947 = 8452421) B8452421
theorem B3756631 : Blo 2225435 3756631 := bstep (se 1 (by rfl) ⟨2817473, by rfl⟩ : syracuseStep 3756631 = 5634947) B5634947
theorem B5008841 : Blo 2225435 5008841 := bstep (se 2 (by rfl) ⟨1878315, by rfl⟩ : syracuseStep 5008841 = 3756631) B3756631
theorem B3339227 : Blo 2225435 3339227 := bstep (se 1 (by rfl) ⟨2504420, by rfl⟩ : syracuseStep 3339227 = 5008841) B5008841
theorem B2226151 : Blo 2225435 2226151 := bstep (se 1 (by rfl) ⟨1669613, by rfl⟩ : syracuseStep 2226151 = 3339227) B3339227
theorem B2504425 : Blo 2225435 2504425 := bbase (se 2 (by rfl) ⟨939159, by rfl⟩ : syracuseStep 2504425 = 1878319) (by norm_num)
theorem B3339233 : Blo 2225435 3339233 := bstep (se 2 (by rfl) ⟨1252212, by rfl⟩ : syracuseStep 3339233 = 2504425) B2504425
theorem B2226155 : Blo 2225435 2226155 := bstep (se 1 (by rfl) ⟨1669616, by rfl⟩ : syracuseStep 2226155 = 3339233) B3339233
theorem B12678677 : Blo 2225435 12678677 := bbase (se 6 (by rfl) ⟨297156, by rfl⟩ : syracuseStep 12678677 = 594313) (by norm_num)
theorem B8452451 : Blo 2225435 8452451 := bstep (se 1 (by rfl) ⟨6339338, by rfl⟩ : syracuseStep 8452451 = 12678677) B12678677
theorem B5634967 : Blo 2225435 5634967 := bstep (se 1 (by rfl) ⟨4226225, by rfl⟩ : syracuseStep 5634967 = 8452451) B8452451
theorem B7513289 : Blo 2225435 7513289 := bstep (se 2 (by rfl) ⟨2817483, by rfl⟩ : syracuseStep 7513289 = 5634967) B5634967
theorem B5008859 : Blo 2225435 5008859 := bstep (se 1 (by rfl) ⟨3756644, by rfl⟩ : syracuseStep 5008859 = 7513289) B7513289
theorem B3339239 : Blo 2225435 3339239 := bstep (se 1 (by rfl) ⟨2504429, by rfl⟩ : syracuseStep 3339239 = 5008859) B5008859
theorem B2226159 : Blo 2225435 2226159 := bstep (se 1 (by rfl) ⟨1669619, by rfl⟩ : syracuseStep 2226159 = 3339239) B3339239
theorem B3339245 : Blo 2225435 3339245 := bbase (se 3 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 3339245 = 1252217) (by norm_num)
theorem B2226163 : Blo 2225435 2226163 := bstep (se 1 (by rfl) ⟨1669622, by rfl⟩ : syracuseStep 2226163 = 3339245) B3339245
theorem B5008877 : Blo 2225435 5008877 := bbase (se 3 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 5008877 = 1878329) (by norm_num)
theorem B3339251 : Blo 2225435 3339251 := bstep (se 1 (by rfl) ⟨2504438, by rfl⟩ : syracuseStep 3339251 = 5008877) B5008877
theorem B2226167 : Blo 2225435 2226167 := bstep (se 1 (by rfl) ⟨1669625, by rfl⟩ : syracuseStep 2226167 = 3339251) B3339251
theorem B7131797 : Blo 2225435 7131797 := bbase (se 6 (by rfl) ⟨167151, by rfl⟩ : syracuseStep 7131797 = 334303) (by norm_num)
theorem B4754531 : Blo 2225435 4754531 := bstep (se 1 (by rfl) ⟨3565898, by rfl⟩ : syracuseStep 4754531 = 7131797) B7131797
theorem B3169687 : Blo 2225435 3169687 := bstep (se 1 (by rfl) ⟨2377265, by rfl⟩ : syracuseStep 3169687 = 4754531) B4754531
theorem B4226249 : Blo 2225435 4226249 := bstep (se 2 (by rfl) ⟨1584843, by rfl⟩ : syracuseStep 4226249 = 3169687) B3169687
theorem B2817499 : Blo 2225435 2817499 := bstep (se 1 (by rfl) ⟨2113124, by rfl⟩ : syracuseStep 2817499 = 4226249) B4226249
theorem B3756665 : Blo 2225435 3756665 := bstep (se 2 (by rfl) ⟨1408749, by rfl⟩ : syracuseStep 3756665 = 2817499) B2817499
theorem B2504443 : Blo 2225435 2504443 := bstep (se 1 (by rfl) ⟨1878332, by rfl⟩ : syracuseStep 2504443 = 3756665) B3756665
theorem B3339257 : Blo 2225435 3339257 := bstep (se 2 (by rfl) ⟨1252221, by rfl⟩ : syracuseStep 3339257 = 2504443) B2504443
theorem B2226171 : Blo 2225435 2226171 := bstep (se 1 (by rfl) ⟨1669628, by rfl⟩ : syracuseStep 2226171 = 3339257) B3339257
theorem B2538617 : Blo 2225435 2538617 := bbase (se 2 (by rfl) ⟨951981, by rfl⟩ : syracuseStep 2538617 = 1903963) (by norm_num)
theorem B6769645 : Blo 2225435 6769645 := bstep (se 3 (by rfl) ⟨1269308, by rfl⟩ : syracuseStep 6769645 = 2538617) B2538617
theorem B36104773 : Blo 2225435 36104773 := bstep (se 4 (by rfl) ⟨3384822, by rfl⟩ : syracuseStep 36104773 = 6769645) B6769645
theorem B48139697 : Blo 2225435 48139697 := bstep (se 2 (by rfl) ⟨18052386, by rfl⟩ : syracuseStep 48139697 = 36104773) B36104773
theorem B128372525 : Blo 2225435 128372525 := bstep (se 3 (by rfl) ⟨24069848, by rfl⟩ : syracuseStep 128372525 = 48139697) B48139697
theorem B85581683 : Blo 2225435 85581683 := bstep (se 1 (by rfl) ⟨64186262, by rfl⟩ : syracuseStep 85581683 = 128372525) B128372525
theorem B57054455 : Blo 2225435 57054455 := bstep (se 1 (by rfl) ⟨42790841, by rfl⟩ : syracuseStep 57054455 = 85581683) B85581683
theorem B38036303 : Blo 2225435 38036303 := bstep (se 1 (by rfl) ⟨28527227, by rfl⟩ : syracuseStep 38036303 = 57054455) B57054455
theorem B25357535 : Blo 2225435 25357535 := bstep (se 1 (by rfl) ⟨19018151, by rfl⟩ : syracuseStep 25357535 = 38036303) B38036303
theorem B16905023 : Blo 2225435 16905023 := bstep (se 1 (by rfl) ⟨12678767, by rfl⟩ : syracuseStep 16905023 = 25357535) B25357535
theorem B11270015 : Blo 2225435 11270015 := bstep (se 1 (by rfl) ⟨8452511, by rfl⟩ : syracuseStep 11270015 = 16905023) B16905023
theorem B7513343 : Blo 2225435 7513343 := bstep (se 1 (by rfl) ⟨5635007, by rfl⟩ : syracuseStep 7513343 = 11270015) B11270015
theorem B5008895 : Blo 2225435 5008895 := bstep (se 1 (by rfl) ⟨3756671, by rfl⟩ : syracuseStep 5008895 = 7513343) B7513343
theorem B3339263 : Blo 2225435 3339263 := bstep (se 1 (by rfl) ⟨2504447, by rfl⟩ : syracuseStep 3339263 = 5008895) B5008895
theorem B2226175 : Blo 2225435 2226175 := bstep (se 1 (by rfl) ⟨1669631, by rfl⟩ : syracuseStep 2226175 = 3339263) B3339263
theorem B3339269 : Blo 2225435 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B2226179 : Blo 2225435 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B3756685 : Blo 2225435 3756685 := bbase (se 3 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 3756685 = 1408757) (by norm_num)
theorem B5008913 : Blo 2225435 5008913 := bstep (se 2 (by rfl) ⟨1878342, by rfl⟩ : syracuseStep 5008913 = 3756685) B3756685
theorem B3339275 : Blo 2225435 3339275 := bstep (se 1 (by rfl) ⟨2504456, by rfl⟩ : syracuseStep 3339275 = 5008913) B5008913
theorem B2226183 : Blo 2225435 2226183 := bstep (se 1 (by rfl) ⟨1669637, by rfl⟩ : syracuseStep 2226183 = 3339275) B3339275
theorem B2504461 : Blo 2225435 2504461 := bbase (se 3 (by rfl) ⟨469586, by rfl⟩ : syracuseStep 2504461 = 939173) (by norm_num)
theorem B3339281 : Blo 2225435 3339281 := bstep (se 2 (by rfl) ⟨1252230, by rfl⟩ : syracuseStep 3339281 = 2504461) B2504461
theorem B2226187 : Blo 2225435 2226187 := bstep (se 1 (by rfl) ⟨1669640, by rfl⟩ : syracuseStep 2226187 = 3339281) B3339281
theorem B7513397 : Blo 2225435 7513397 := bbase (se 5 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 7513397 = 704381) (by norm_num)
theorem B5008931 : Blo 2225435 5008931 := bstep (se 1 (by rfl) ⟨3756698, by rfl⟩ : syracuseStep 5008931 = 7513397) B7513397
theorem B3339287 : Blo 2225435 3339287 := bstep (se 1 (by rfl) ⟨2504465, by rfl⟩ : syracuseStep 3339287 = 5008931) B5008931
theorem B2226191 : Blo 2225435 2226191 := bstep (se 1 (by rfl) ⟨1669643, by rfl⟩ : syracuseStep 2226191 = 3339287) B3339287
theorem B3339293 : Blo 2225435 3339293 := bbase (se 3 (by rfl) ⟨626117, by rfl⟩ : syracuseStep 3339293 = 1252235) (by norm_num)
theorem B2226195 : Blo 2225435 2226195 := bstep (se 1 (by rfl) ⟨1669646, by rfl⟩ : syracuseStep 2226195 = 3339293) B3339293
theorem B5008949 : Blo 2225435 5008949 := bbase (se 5 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 5008949 = 469589) (by norm_num)
theorem B3339299 : Blo 2225435 3339299 := bstep (se 1 (by rfl) ⟨2504474, by rfl⟩ : syracuseStep 3339299 = 5008949) B5008949
theorem B2226199 : Blo 2225435 2226199 := bstep (se 1 (by rfl) ⟨1669649, by rfl⟩ : syracuseStep 2226199 = 3339299) B3339299
theorem B3565949 : Blo 2225435 3565949 := bbase (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) (by norm_num)
theorem B9509197 : Blo 2225435 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B12678929 : Blo 2225435 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B8452619 : Blo 2225435 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B5635079 : Blo 2225435 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B3756719 : Blo 2225435 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B2504479 : Blo 2225435 2504479 := bstep (se 1 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 2504479 = 3756719) B3756719
theorem B3339305 : Blo 2225435 3339305 := bstep (se 2 (by rfl) ⟨1252239, by rfl⟩ : syracuseStep 3339305 = 2504479) B2504479
theorem B2226203 : Blo 2225435 2226203 := bstep (se 1 (by rfl) ⟨1669652, by rfl⟩ : syracuseStep 2226203 = 3339305) B3339305
theorem B5348933 : Blo 2225435 5348933 := bbase (se 4 (by rfl) ⟨501462, by rfl⟩ : syracuseStep 5348933 = 1002925) (by norm_num)
theorem B3565955 : Blo 2225435 3565955 := bstep (se 1 (by rfl) ⟨2674466, by rfl⟩ : syracuseStep 3565955 = 5348933) B5348933
theorem B9509213 : Blo 2225435 9509213 := bstep (se 3 (by rfl) ⟨1782977, by rfl⟩ : syracuseStep 9509213 = 3565955) B3565955
theorem B6339475 : Blo 2225435 6339475 := bstep (se 1 (by rfl) ⟨4754606, by rfl⟩ : syracuseStep 6339475 = 9509213) B9509213
theorem B8452633 : Blo 2225435 8452633 := bstep (se 2 (by rfl) ⟨3169737, by rfl⟩ : syracuseStep 8452633 = 6339475) B6339475
theorem B11270177 : Blo 2225435 11270177 := bstep (se 2 (by rfl) ⟨4226316, by rfl⟩ : syracuseStep 11270177 = 8452633) B8452633
theorem B7513451 : Blo 2225435 7513451 := bstep (se 1 (by rfl) ⟨5635088, by rfl⟩ : syracuseStep 7513451 = 11270177) B11270177
theorem B5008967 : Blo 2225435 5008967 := bstep (se 1 (by rfl) ⟨3756725, by rfl⟩ : syracuseStep 5008967 = 7513451) B7513451
theorem B3339311 : Blo 2225435 3339311 := bstep (se 1 (by rfl) ⟨2504483, by rfl⟩ : syracuseStep 3339311 = 5008967) B5008967
theorem B2226207 : Blo 2225435 2226207 := bstep (se 1 (by rfl) ⟨1669655, by rfl⟩ : syracuseStep 2226207 = 3339311) B3339311
theorem B3339317 : Blo 2225435 3339317 := bbase (se 5 (by rfl) ⟨156530, by rfl⟩ : syracuseStep 3339317 = 313061) (by norm_num)
theorem B2226211 : Blo 2225435 2226211 := bstep (se 1 (by rfl) ⟨1669658, by rfl⟩ : syracuseStep 2226211 = 3339317) B3339317
theorem B5635109 : Blo 2225435 5635109 := bbase (se 4 (by rfl) ⟨528291, by rfl⟩ : syracuseStep 5635109 = 1056583) (by norm_num)
theorem B3756739 : Blo 2225435 3756739 := bstep (se 1 (by rfl) ⟨2817554, by rfl⟩ : syracuseStep 3756739 = 5635109) B5635109
theorem B5008985 : Blo 2225435 5008985 := bstep (se 2 (by rfl) ⟨1878369, by rfl⟩ : syracuseStep 5008985 = 3756739) B3756739
theorem B3339323 : Blo 2225435 3339323 := bstep (se 1 (by rfl) ⟨2504492, by rfl⟩ : syracuseStep 3339323 = 5008985) B5008985
theorem B2226215 : Blo 2225435 2226215 := bstep (se 1 (by rfl) ⟨1669661, by rfl⟩ : syracuseStep 2226215 = 3339323) B3339323
theorem B2504497 : Blo 2225435 2504497 := bbase (se 2 (by rfl) ⟨939186, by rfl⟩ : syracuseStep 2504497 = 1878373) (by norm_num)
theorem B3339329 : Blo 2225435 3339329 := bstep (se 2 (by rfl) ⟨1252248, by rfl⟩ : syracuseStep 3339329 = 2504497) B2504497
theorem B2226219 : Blo 2225435 2226219 := bstep (se 1 (by rfl) ⟨1669664, by rfl⟩ : syracuseStep 2226219 = 3339329) B3339329
theorem B3565981 : Blo 2225435 3565981 := bbase (se 3 (by rfl) ⟨668621, by rfl⟩ : syracuseStep 3565981 = 1337243) (by norm_num)
theorem B4754641 : Blo 2225435 4754641 := bstep (se 2 (by rfl) ⟨1782990, by rfl⟩ : syracuseStep 4754641 = 3565981) B3565981
theorem B6339521 : Blo 2225435 6339521 := bstep (se 2 (by rfl) ⟨2377320, by rfl⟩ : syracuseStep 6339521 = 4754641) B4754641
theorem B4226347 : Blo 2225435 4226347 := bstep (se 1 (by rfl) ⟨3169760, by rfl⟩ : syracuseStep 4226347 = 6339521) B6339521
theorem B5635129 : Blo 2225435 5635129 := bstep (se 2 (by rfl) ⟨2113173, by rfl⟩ : syracuseStep 5635129 = 4226347) B4226347
theorem B7513505 : Blo 2225435 7513505 := bstep (se 2 (by rfl) ⟨2817564, by rfl⟩ : syracuseStep 7513505 = 5635129) B5635129
theorem B5009003 : Blo 2225435 5009003 := bstep (se 1 (by rfl) ⟨3756752, by rfl⟩ : syracuseStep 5009003 = 7513505) B7513505
theorem B3339335 : Blo 2225435 3339335 := bstep (se 1 (by rfl) ⟨2504501, by rfl⟩ : syracuseStep 3339335 = 5009003) B5009003
theorem B2226223 : Blo 2225435 2226223 := bstep (se 1 (by rfl) ⟨1669667, by rfl⟩ : syracuseStep 2226223 = 3339335) B3339335
theorem B3339341 : Blo 2225435 3339341 := bbase (se 3 (by rfl) ⟨626126, by rfl⟩ : syracuseStep 3339341 = 1252253) (by norm_num)
theorem B2226227 : Blo 2225435 2226227 := bstep (se 1 (by rfl) ⟨1669670, by rfl⟩ : syracuseStep 2226227 = 3339341) B3339341
theorem B5009021 : Blo 2225435 5009021 := bbase (se 3 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 5009021 = 1878383) (by norm_num)
theorem B3339347 : Blo 2225435 3339347 := bstep (se 1 (by rfl) ⟨2504510, by rfl⟩ : syracuseStep 3339347 = 5009021) B5009021
theorem B2226231 : Blo 2225435 2226231 := bstep (se 1 (by rfl) ⟨1669673, by rfl⟩ : syracuseStep 2226231 = 3339347) B3339347
theorem B3756773 : Blo 2225435 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B2504515 : Blo 2225435 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B3339353 : Blo 2225435 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B2226235 : Blo 2225435 2226235 := bstep (se 1 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 2226235 = 3339353) B3339353
theorem B2674505 : Blo 2225435 2674505 := bbase (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) (by norm_num)
theorem B7132013 : Blo 2225435 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B4754675 : Blo 2225435 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B3169783 : Blo 2225435 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B16905509 : Blo 2225435 16905509 := bstep (se 4 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 16905509 = 3169783) B3169783
theorem B11270339 : Blo 2225435 11270339 := bstep (se 1 (by rfl) ⟨8452754, by rfl⟩ : syracuseStep 11270339 = 16905509) B16905509
theorem B7513559 : Blo 2225435 7513559 := bstep (se 1 (by rfl) ⟨5635169, by rfl⟩ : syracuseStep 7513559 = 11270339) B11270339
theorem B5009039 : Blo 2225435 5009039 := bstep (se 1 (by rfl) ⟨3756779, by rfl⟩ : syracuseStep 5009039 = 7513559) B7513559
theorem B3339359 : Blo 2225435 3339359 := bstep (se 1 (by rfl) ⟨2504519, by rfl⟩ : syracuseStep 3339359 = 5009039) B5009039
theorem B2226239 : Blo 2225435 2226239 := bstep (se 1 (by rfl) ⟨1669679, by rfl⟩ : syracuseStep 2226239 = 3339359) B3339359
theorem B3339365 : Blo 2225435 3339365 := bbase (se 4 (by rfl) ⟨313065, by rfl⟩ : syracuseStep 3339365 = 626131) (by norm_num)
theorem B2226243 : Blo 2225435 2226243 := bstep (se 1 (by rfl) ⟨1669682, by rfl⟩ : syracuseStep 2226243 = 3339365) B3339365
theorem B4754693 : Blo 2225435 4754693 := bbase (se 4 (by rfl) ⟨445752, by rfl⟩ : syracuseStep 4754693 = 891505) (by norm_num)
theorem B3169795 : Blo 2225435 3169795 := bstep (se 1 (by rfl) ⟨2377346, by rfl⟩ : syracuseStep 3169795 = 4754693) B4754693
theorem B4226393 : Blo 2225435 4226393 := bstep (se 2 (by rfl) ⟨1584897, by rfl⟩ : syracuseStep 4226393 = 3169795) B3169795
theorem B2817595 : Blo 2225435 2817595 := bstep (se 1 (by rfl) ⟨2113196, by rfl⟩ : syracuseStep 2817595 = 4226393) B4226393
theorem B3756793 : Blo 2225435 3756793 := bstep (se 2 (by rfl) ⟨1408797, by rfl⟩ : syracuseStep 3756793 = 2817595) B2817595
theorem B5009057 : Blo 2225435 5009057 := bstep (se 2 (by rfl) ⟨1878396, by rfl⟩ : syracuseStep 5009057 = 3756793) B3756793
theorem B3339371 : Blo 2225435 3339371 := bstep (se 1 (by rfl) ⟨2504528, by rfl⟩ : syracuseStep 3339371 = 5009057) B5009057
theorem B2226247 : Blo 2225435 2226247 := bstep (se 1 (by rfl) ⟨1669685, by rfl⟩ : syracuseStep 2226247 = 3339371) B3339371
theorem B2504533 : Blo 2225435 2504533 := bbase (se 9 (by rfl) ⟨7337, by rfl⟩ : syracuseStep 2504533 = 14675) (by norm_num)
theorem B3339377 : Blo 2225435 3339377 := bstep (se 2 (by rfl) ⟨1252266, by rfl⟩ : syracuseStep 3339377 = 2504533) B2504533
theorem B2226251 : Blo 2225435 2226251 := bstep (se 1 (by rfl) ⟨1669688, by rfl⟩ : syracuseStep 2226251 = 3339377) B3339377
theorem B2817605 : Blo 2225435 2817605 := bbase (se 4 (by rfl) ⟨264150, by rfl⟩ : syracuseStep 2817605 = 528301) (by norm_num)
theorem B7513613 : Blo 2225435 7513613 := bstep (se 3 (by rfl) ⟨1408802, by rfl⟩ : syracuseStep 7513613 = 2817605) B2817605
theorem B5009075 : Blo 2225435 5009075 := bstep (se 1 (by rfl) ⟨3756806, by rfl⟩ : syracuseStep 5009075 = 7513613) B7513613
theorem B3339383 : Blo 2225435 3339383 := bstep (se 1 (by rfl) ⟨2504537, by rfl⟩ : syracuseStep 3339383 = 5009075) B5009075
theorem B2226255 : Blo 2225435 2226255 := bstep (se 1 (by rfl) ⟨1669691, by rfl⟩ : syracuseStep 2226255 = 3339383) B3339383
theorem B3339389 : Blo 2225435 3339389 := bbase (se 3 (by rfl) ⟨626135, by rfl⟩ : syracuseStep 3339389 = 1252271) (by norm_num)
theorem B2226259 : Blo 2225435 2226259 := bstep (se 1 (by rfl) ⟨1669694, by rfl⟩ : syracuseStep 2226259 = 3339389) B3339389
theorem B5009093 : Blo 2225435 5009093 := bbase (se 4 (by rfl) ⟨469602, by rfl⟩ : syracuseStep 5009093 = 939205) (by norm_num)
theorem B3339395 : Blo 2225435 3339395 := bstep (se 1 (by rfl) ⟨2504546, by rfl⟩ : syracuseStep 3339395 = 5009093) B5009093
theorem B2226263 : Blo 2225435 2226263 := bstep (se 1 (by rfl) ⟨1669697, by rfl⟩ : syracuseStep 2226263 = 3339395) B3339395
theorem B13027637 : Blo 2225435 13027637 := bbase (se 5 (by rfl) ⟨610670, by rfl⟩ : syracuseStep 13027637 = 1221341) (by norm_num)
theorem B8685091 : Blo 2225435 8685091 := bstep (se 1 (by rfl) ⟨6513818, by rfl⟩ : syracuseStep 8685091 = 13027637) B13027637
theorem B11580121 : Blo 2225435 11580121 := bstep (se 2 (by rfl) ⟨4342545, by rfl⟩ : syracuseStep 11580121 = 8685091) B8685091
theorem B15440161 : Blo 2225435 15440161 := bstep (se 2 (by rfl) ⟨5790060, by rfl⟩ : syracuseStep 15440161 = 11580121) B11580121
theorem B20586881 : Blo 2225435 20586881 := bstep (se 2 (by rfl) ⟨7720080, by rfl⟩ : syracuseStep 20586881 = 15440161) B15440161
theorem B13724587 : Blo 2225435 13724587 := bstep (se 1 (by rfl) ⟨10293440, by rfl⟩ : syracuseStep 13724587 = 20586881) B20586881
theorem B18299449 : Blo 2225435 18299449 := bstep (se 2 (by rfl) ⟨6862293, by rfl⟩ : syracuseStep 18299449 = 13724587) B13724587
theorem B24399265 : Blo 2225435 24399265 := bstep (se 2 (by rfl) ⟨9149724, by rfl⟩ : syracuseStep 24399265 = 18299449) B18299449
theorem B32532353 : Blo 2225435 32532353 := bstep (se 2 (by rfl) ⟨12199632, by rfl⟩ : syracuseStep 32532353 = 24399265) B24399265
theorem B21688235 : Blo 2225435 21688235 := bstep (se 1 (by rfl) ⟨16266176, by rfl⟩ : syracuseStep 21688235 = 32532353) B32532353
theorem B14458823 : Blo 2225435 14458823 := bstep (se 1 (by rfl) ⟨10844117, by rfl⟩ : syracuseStep 14458823 = 21688235) B21688235
theorem B9639215 : Blo 2225435 9639215 := bstep (se 1 (by rfl) ⟨7229411, by rfl⟩ : syracuseStep 9639215 = 14458823) B14458823
theorem B6426143 : Blo 2225435 6426143 := bstep (se 1 (by rfl) ⟨4819607, by rfl⟩ : syracuseStep 6426143 = 9639215) B9639215
theorem B4284095 : Blo 2225435 4284095 := bstep (se 1 (by rfl) ⟨3213071, by rfl⟩ : syracuseStep 4284095 = 6426143) B6426143
theorem B11424253 : Blo 2225435 11424253 := bstep (se 3 (by rfl) ⟨2142047, by rfl⟩ : syracuseStep 11424253 = 4284095) B4284095
theorem B15232337 : Blo 2225435 15232337 := bstep (se 2 (by rfl) ⟨5712126, by rfl⟩ : syracuseStep 15232337 = 11424253) B11424253
theorem B10154891 : Blo 2225435 10154891 := bstep (se 1 (by rfl) ⟨7616168, by rfl⟩ : syracuseStep 10154891 = 15232337) B15232337
theorem B6769927 : Blo 2225435 6769927 := bstep (se 1 (by rfl) ⟨5077445, by rfl⟩ : syracuseStep 6769927 = 10154891) B10154891
theorem B9026569 : Blo 2225435 9026569 := bstep (se 2 (by rfl) ⟨3384963, by rfl⟩ : syracuseStep 9026569 = 6769927) B6769927
theorem B48141701 : Blo 2225435 48141701 := bstep (se 4 (by rfl) ⟨4513284, by rfl⟩ : syracuseStep 48141701 = 9026569) B9026569
theorem B32094467 : Blo 2225435 32094467 := bstep (se 1 (by rfl) ⟨24070850, by rfl⟩ : syracuseStep 32094467 = 48141701) B48141701
theorem B21396311 : Blo 2225435 21396311 := bstep (se 1 (by rfl) ⟨16047233, by rfl⟩ : syracuseStep 21396311 = 32094467) B32094467
theorem B14264207 : Blo 2225435 14264207 := bstep (se 1 (by rfl) ⟨10698155, by rfl⟩ : syracuseStep 14264207 = 21396311) B21396311
theorem B9509471 : Blo 2225435 9509471 := bstep (se 1 (by rfl) ⟨7132103, by rfl⟩ : syracuseStep 9509471 = 14264207) B14264207
theorem B6339647 : Blo 2225435 6339647 := bstep (se 1 (by rfl) ⟨4754735, by rfl⟩ : syracuseStep 6339647 = 9509471) B9509471
theorem B4226431 : Blo 2225435 4226431 := bstep (se 1 (by rfl) ⟨3169823, by rfl⟩ : syracuseStep 4226431 = 6339647) B6339647
theorem B5635241 : Blo 2225435 5635241 := bstep (se 2 (by rfl) ⟨2113215, by rfl⟩ : syracuseStep 5635241 = 4226431) B4226431
theorem B3756827 : Blo 2225435 3756827 := bstep (se 1 (by rfl) ⟨2817620, by rfl⟩ : syracuseStep 3756827 = 5635241) B5635241
theorem B2504551 : Blo 2225435 2504551 := bstep (se 1 (by rfl) ⟨1878413, by rfl⟩ : syracuseStep 2504551 = 3756827) B3756827
theorem B3339401 : Blo 2225435 3339401 := bstep (se 2 (by rfl) ⟨1252275, by rfl⟩ : syracuseStep 3339401 = 2504551) B2504551
theorem B2226267 : Blo 2225435 2226267 := bstep (se 1 (by rfl) ⟨1669700, by rfl⟩ : syracuseStep 2226267 = 3339401) B3339401
theorem B11270501 : Blo 2225435 11270501 := bbase (se 4 (by rfl) ⟨1056609, by rfl⟩ : syracuseStep 11270501 = 2113219) (by norm_num)
theorem B7513667 : Blo 2225435 7513667 := bstep (se 1 (by rfl) ⟨5635250, by rfl⟩ : syracuseStep 7513667 = 11270501) B11270501
theorem B5009111 : Blo 2225435 5009111 := bstep (se 1 (by rfl) ⟨3756833, by rfl⟩ : syracuseStep 5009111 = 7513667) B7513667
theorem B3339407 : Blo 2225435 3339407 := bstep (se 1 (by rfl) ⟨2504555, by rfl⟩ : syracuseStep 3339407 = 5009111) B5009111
theorem B2226271 : Blo 2225435 2226271 := bstep (se 1 (by rfl) ⟨1669703, by rfl⟩ : syracuseStep 2226271 = 3339407) B3339407
theorem B3339413 : Blo 2225435 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B2226275 : Blo 2225435 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B2674553 : Blo 2225435 2674553 := bbase (se 2 (by rfl) ⟨1002957, by rfl⟩ : syracuseStep 2674553 = 2005915) (by norm_num)
theorem B7132141 : Blo 2225435 7132141 := bstep (se 3 (by rfl) ⟨1337276, by rfl⟩ : syracuseStep 7132141 = 2674553) B2674553
theorem B9509521 : Blo 2225435 9509521 := bstep (se 2 (by rfl) ⟨3566070, by rfl⟩ : syracuseStep 9509521 = 7132141) B7132141
theorem B12679361 : Blo 2225435 12679361 := bstep (se 2 (by rfl) ⟨4754760, by rfl⟩ : syracuseStep 12679361 = 9509521) B9509521
theorem B8452907 : Blo 2225435 8452907 := bstep (se 1 (by rfl) ⟨6339680, by rfl⟩ : syracuseStep 8452907 = 12679361) B12679361
theorem B5635271 : Blo 2225435 5635271 := bstep (se 1 (by rfl) ⟨4226453, by rfl⟩ : syracuseStep 5635271 = 8452907) B8452907
theorem B3756847 : Blo 2225435 3756847 := bstep (se 1 (by rfl) ⟨2817635, by rfl⟩ : syracuseStep 3756847 = 5635271) B5635271
theorem B5009129 : Blo 2225435 5009129 := bstep (se 2 (by rfl) ⟨1878423, by rfl⟩ : syracuseStep 5009129 = 3756847) B3756847
theorem B3339419 : Blo 2225435 3339419 := bstep (se 1 (by rfl) ⟨2504564, by rfl⟩ : syracuseStep 3339419 = 5009129) B5009129
theorem B2226279 : Blo 2225435 2226279 := bstep (se 1 (by rfl) ⟨1669709, by rfl⟩ : syracuseStep 2226279 = 3339419) B3339419
theorem B2504569 : Blo 2225435 2504569 := bbase (se 2 (by rfl) ⟨939213, by rfl⟩ : syracuseStep 2504569 = 1878427) (by norm_num)
theorem B3339425 : Blo 2225435 3339425 := bstep (se 2 (by rfl) ⟨1252284, by rfl⟩ : syracuseStep 3339425 = 2504569) B2504569
theorem B2226283 : Blo 2225435 2226283 := bstep (se 1 (by rfl) ⟨1669712, by rfl⟩ : syracuseStep 2226283 = 3339425) B3339425
theorem B5349125 : Blo 2225435 5349125 := bbase (se 4 (by rfl) ⟨501480, by rfl⟩ : syracuseStep 5349125 = 1002961) (by norm_num)
theorem B14264333 : Blo 2225435 14264333 := bstep (se 3 (by rfl) ⟨2674562, by rfl⟩ : syracuseStep 14264333 = 5349125) B5349125
theorem B9509555 : Blo 2225435 9509555 := bstep (se 1 (by rfl) ⟨7132166, by rfl⟩ : syracuseStep 9509555 = 14264333) B14264333
theorem B6339703 : Blo 2225435 6339703 := bstep (se 1 (by rfl) ⟨4754777, by rfl⟩ : syracuseStep 6339703 = 9509555) B9509555
theorem B8452937 : Blo 2225435 8452937 := bstep (se 2 (by rfl) ⟨3169851, by rfl⟩ : syracuseStep 8452937 = 6339703) B6339703
theorem B5635291 : Blo 2225435 5635291 := bstep (se 1 (by rfl) ⟨4226468, by rfl⟩ : syracuseStep 5635291 = 8452937) B8452937
theorem B7513721 : Blo 2225435 7513721 := bstep (se 2 (by rfl) ⟨2817645, by rfl⟩ : syracuseStep 7513721 = 5635291) B5635291
theorem B5009147 : Blo 2225435 5009147 := bstep (se 1 (by rfl) ⟨3756860, by rfl⟩ : syracuseStep 5009147 = 7513721) B7513721
theorem B3339431 : Blo 2225435 3339431 := bstep (se 1 (by rfl) ⟨2504573, by rfl⟩ : syracuseStep 3339431 = 5009147) B5009147
theorem B2226287 : Blo 2225435 2226287 := bstep (se 1 (by rfl) ⟨1669715, by rfl⟩ : syracuseStep 2226287 = 3339431) B3339431
theorem B3339437 : Blo 2225435 3339437 := bbase (se 3 (by rfl) ⟨626144, by rfl⟩ : syracuseStep 3339437 = 1252289) (by norm_num)
theorem B2226291 : Blo 2225435 2226291 := bstep (se 1 (by rfl) ⟨1669718, by rfl⟩ : syracuseStep 2226291 = 3339437) B3339437
theorem B5009165 : Blo 2225435 5009165 := bbase (se 3 (by rfl) ⟨939218, by rfl⟩ : syracuseStep 5009165 = 1878437) (by norm_num)
theorem B3339443 : Blo 2225435 3339443 := bstep (se 1 (by rfl) ⟨2504582, by rfl⟩ : syracuseStep 3339443 = 5009165) B5009165
theorem B2226295 : Blo 2225435 2226295 := bstep (se 1 (by rfl) ⟨1669721, by rfl⟩ : syracuseStep 2226295 = 3339443) B3339443
theorem B2817661 : Blo 2225435 2817661 := bbase (se 3 (by rfl) ⟨528311, by rfl⟩ : syracuseStep 2817661 = 1056623) (by norm_num)
theorem B3756881 : Blo 2225435 3756881 := bstep (se 2 (by rfl) ⟨1408830, by rfl⟩ : syracuseStep 3756881 = 2817661) B2817661
theorem B2504587 : Blo 2225435 2504587 := bstep (se 1 (by rfl) ⟨1878440, by rfl⟩ : syracuseStep 2504587 = 3756881) B3756881
theorem B3339449 : Blo 2225435 3339449 := bstep (se 2 (by rfl) ⟨1252293, by rfl⟩ : syracuseStep 3339449 = 2504587) B2504587
theorem B2226299 : Blo 2225435 2226299 := bstep (se 1 (by rfl) ⟨1669724, by rfl⟩ : syracuseStep 2226299 = 3339449) B3339449
theorem B4513357 : Blo 2225435 4513357 := bbase (se 3 (by rfl) ⟨846254, by rfl⟩ : syracuseStep 4513357 = 1692509) (by norm_num)
theorem B6017809 : Blo 2225435 6017809 := bstep (se 2 (by rfl) ⟨2256678, by rfl⟩ : syracuseStep 6017809 = 4513357) B4513357
theorem B8023745 : Blo 2225435 8023745 := bstep (se 2 (by rfl) ⟨3008904, by rfl⟩ : syracuseStep 8023745 = 6017809) B6017809
theorem B5349163 : Blo 2225435 5349163 := bstep (se 1 (by rfl) ⟨4011872, by rfl⟩ : syracuseStep 5349163 = 8023745) B8023745
theorem B7132217 : Blo 2225435 7132217 := bstep (se 2 (by rfl) ⟨2674581, by rfl⟩ : syracuseStep 7132217 = 5349163) B5349163
theorem B19019245 : Blo 2225435 19019245 := bstep (se 3 (by rfl) ⟨3566108, by rfl⟩ : syracuseStep 19019245 = 7132217) B7132217
theorem B25358993 : Blo 2225435 25358993 := bstep (se 2 (by rfl) ⟨9509622, by rfl⟩ : syracuseStep 25358993 = 19019245) B19019245
theorem B16905995 : Blo 2225435 16905995 := bstep (se 1 (by rfl) ⟨12679496, by rfl⟩ : syracuseStep 16905995 = 25358993) B25358993
theorem B11270663 : Blo 2225435 11270663 := bstep (se 1 (by rfl) ⟨8452997, by rfl⟩ : syracuseStep 11270663 = 16905995) B16905995
theorem B7513775 : Blo 2225435 7513775 := bstep (se 1 (by rfl) ⟨5635331, by rfl⟩ : syracuseStep 7513775 = 11270663) B11270663
theorem B5009183 : Blo 2225435 5009183 := bstep (se 1 (by rfl) ⟨3756887, by rfl⟩ : syracuseStep 5009183 = 7513775) B7513775
theorem B3339455 : Blo 2225435 3339455 := bstep (se 1 (by rfl) ⟨2504591, by rfl⟩ : syracuseStep 3339455 = 5009183) B5009183
theorem B2226303 : Blo 2225435 2226303 := bstep (se 1 (by rfl) ⟨1669727, by rfl⟩ : syracuseStep 2226303 = 3339455) B3339455
theorem B3339461 : Blo 2225435 3339461 := bbase (se 4 (by rfl) ⟨313074, by rfl⟩ : syracuseStep 3339461 = 626149) (by norm_num)
theorem B2226307 : Blo 2225435 2226307 := bstep (se 1 (by rfl) ⟨1669730, by rfl⟩ : syracuseStep 2226307 = 3339461) B3339461
theorem B3756901 : Blo 2225435 3756901 := bbase (se 4 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 3756901 = 704419) (by norm_num)
theorem B5009201 : Blo 2225435 5009201 := bstep (se 2 (by rfl) ⟨1878450, by rfl⟩ : syracuseStep 5009201 = 3756901) B3756901
theorem B3339467 : Blo 2225435 3339467 := bstep (se 1 (by rfl) ⟨2504600, by rfl⟩ : syracuseStep 3339467 = 5009201) B5009201
theorem B2226311 : Blo 2225435 2226311 := bstep (se 1 (by rfl) ⟨1669733, by rfl⟩ : syracuseStep 2226311 = 3339467) B3339467
theorem B2504605 : Blo 2225435 2504605 := bbase (se 3 (by rfl) ⟨469613, by rfl⟩ : syracuseStep 2504605 = 939227) (by norm_num)
theorem B3339473 : Blo 2225435 3339473 := bstep (se 2 (by rfl) ⟨1252302, by rfl⟩ : syracuseStep 3339473 = 2504605) B2504605
theorem B2226315 : Blo 2225435 2226315 := bstep (se 1 (by rfl) ⟨1669736, by rfl⟩ : syracuseStep 2226315 = 3339473) B3339473
theorem B7513829 : Blo 2225435 7513829 := bbase (se 4 (by rfl) ⟨704421, by rfl⟩ : syracuseStep 7513829 = 1408843) (by norm_num)
theorem B5009219 : Blo 2225435 5009219 := bstep (se 1 (by rfl) ⟨3756914, by rfl⟩ : syracuseStep 5009219 = 7513829) B7513829
theorem B3339479 : Blo 2225435 3339479 := bstep (se 1 (by rfl) ⟨2504609, by rfl⟩ : syracuseStep 3339479 = 5009219) B5009219
theorem B2226319 : Blo 2225435 2226319 := bstep (se 1 (by rfl) ⟨1669739, by rfl⟩ : syracuseStep 2226319 = 3339479) B3339479
theorem B3339485 : Blo 2225435 3339485 := bbase (se 3 (by rfl) ⟨626153, by rfl⟩ : syracuseStep 3339485 = 1252307) (by norm_num)
theorem B2226323 : Blo 2225435 2226323 := bstep (se 1 (by rfl) ⟨1669742, by rfl⟩ : syracuseStep 2226323 = 3339485) B3339485
theorem B5009237 : Blo 2225435 5009237 := bbase (se 9 (by rfl) ⟨14675, by rfl⟩ : syracuseStep 5009237 = 29351) (by norm_num)
theorem B3339491 : Blo 2225435 3339491 := bstep (se 1 (by rfl) ⟨2504618, by rfl⟩ : syracuseStep 3339491 = 5009237) B5009237
theorem B2226327 : Blo 2225435 2226327 := bstep (se 1 (by rfl) ⟨1669745, by rfl⟩ : syracuseStep 2226327 = 3339491) B3339491
theorem B6339829 : Blo 2225435 6339829 := bbase (se 5 (by rfl) ⟨297179, by rfl⟩ : syracuseStep 6339829 = 594359) (by norm_num)
theorem B8453105 : Blo 2225435 8453105 := bstep (se 2 (by rfl) ⟨3169914, by rfl⟩ : syracuseStep 8453105 = 6339829) B6339829
theorem B5635403 : Blo 2225435 5635403 := bstep (se 1 (by rfl) ⟨4226552, by rfl⟩ : syracuseStep 5635403 = 8453105) B8453105
theorem B3756935 : Blo 2225435 3756935 := bstep (se 1 (by rfl) ⟨2817701, by rfl⟩ : syracuseStep 3756935 = 5635403) B5635403
theorem B2504623 : Blo 2225435 2504623 := bstep (se 1 (by rfl) ⟨1878467, by rfl⟩ : syracuseStep 2504623 = 3756935) B3756935
theorem B3339497 : Blo 2225435 3339497 := bstep (se 2 (by rfl) ⟨1252311, by rfl⟩ : syracuseStep 3339497 = 2504623) B2504623
theorem B2226331 : Blo 2225435 2226331 := bstep (se 1 (by rfl) ⟨1669748, by rfl⟩ : syracuseStep 2226331 = 3339497) B3339497
theorem B21688885 : Blo 2225435 21688885 := bbase (se 5 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 21688885 = 2033333) (by norm_num)
theorem B28918513 : Blo 2225435 28918513 := bstep (se 2 (by rfl) ⟨10844442, by rfl⟩ : syracuseStep 28918513 = 21688885) B21688885
theorem B38558017 : Blo 2225435 38558017 := bstep (se 2 (by rfl) ⟨14459256, by rfl⟩ : syracuseStep 38558017 = 28918513) B28918513
theorem B51410689 : Blo 2225435 51410689 := bstep (se 2 (by rfl) ⟨19279008, by rfl⟩ : syracuseStep 51410689 = 38558017) B38558017
theorem B274190341 : Blo 2225435 274190341 := bstep (se 4 (by rfl) ⟨25705344, by rfl⟩ : syracuseStep 274190341 = 51410689) B51410689
theorem B365587121 : Blo 2225435 365587121 := bstep (se 2 (by rfl) ⟨137095170, by rfl⟩ : syracuseStep 365587121 = 274190341) B274190341
theorem B243724747 : Blo 2225435 243724747 := bstep (se 1 (by rfl) ⟨182793560, by rfl⟩ : syracuseStep 243724747 = 365587121) B365587121
theorem B324966329 : Blo 2225435 324966329 := bstep (se 2 (by rfl) ⟨121862373, by rfl⟩ : syracuseStep 324966329 = 243724747) B243724747
theorem B216644219 : Blo 2225435 216644219 := bstep (se 1 (by rfl) ⟨162483164, by rfl⟩ : syracuseStep 216644219 = 324966329) B324966329
theorem B144429479 : Blo 2225435 144429479 := bstep (se 1 (by rfl) ⟨108322109, by rfl⟩ : syracuseStep 144429479 = 216644219) B216644219
theorem B96286319 : Blo 2225435 96286319 := bstep (se 1 (by rfl) ⟨72214739, by rfl⟩ : syracuseStep 96286319 = 144429479) B144429479
theorem B64190879 : Blo 2225435 64190879 := bstep (se 1 (by rfl) ⟨48143159, by rfl⟩ : syracuseStep 64190879 = 96286319) B96286319
theorem B42793919 : Blo 2225435 42793919 := bstep (se 1 (by rfl) ⟨32095439, by rfl⟩ : syracuseStep 42793919 = 64190879) B64190879
theorem B28529279 : Blo 2225435 28529279 := bstep (se 1 (by rfl) ⟨21396959, by rfl⟩ : syracuseStep 28529279 = 42793919) B42793919
theorem B19019519 : Blo 2225435 19019519 := bstep (se 1 (by rfl) ⟨14264639, by rfl⟩ : syracuseStep 19019519 = 28529279) B28529279
theorem B12679679 : Blo 2225435 12679679 := bstep (se 1 (by rfl) ⟨9509759, by rfl⟩ : syracuseStep 12679679 = 19019519) B19019519
theorem B8453119 : Blo 2225435 8453119 := bstep (se 1 (by rfl) ⟨6339839, by rfl⟩ : syracuseStep 8453119 = 12679679) B12679679
theorem B11270825 : Blo 2225435 11270825 := bstep (se 2 (by rfl) ⟨4226559, by rfl⟩ : syracuseStep 11270825 = 8453119) B8453119
theorem B7513883 : Blo 2225435 7513883 := bstep (se 1 (by rfl) ⟨5635412, by rfl⟩ : syracuseStep 7513883 = 11270825) B11270825
theorem B5009255 : Blo 2225435 5009255 := bstep (se 1 (by rfl) ⟨3756941, by rfl⟩ : syracuseStep 5009255 = 7513883) B7513883
theorem B3339503 : Blo 2225435 3339503 := bstep (se 1 (by rfl) ⟨2504627, by rfl⟩ : syracuseStep 3339503 = 5009255) B5009255
theorem B2226335 : Blo 2225435 2226335 := bstep (se 1 (by rfl) ⟨1669751, by rfl⟩ : syracuseStep 2226335 = 3339503) B3339503
theorem B3339509 : Blo 2225435 3339509 := bbase (se 5 (by rfl) ⟨156539, by rfl⟩ : syracuseStep 3339509 = 313079) (by norm_num)
theorem B2226339 : Blo 2225435 2226339 := bstep (se 1 (by rfl) ⟨1669754, by rfl⟩ : syracuseStep 2226339 = 3339509) B3339509
theorem B14264693 : Blo 2225435 14264693 := bbase (se 5 (by rfl) ⟨668657, by rfl⟩ : syracuseStep 14264693 = 1337315) (by norm_num)
theorem B9509795 : Blo 2225435 9509795 := bstep (se 1 (by rfl) ⟨7132346, by rfl⟩ : syracuseStep 9509795 = 14264693) B14264693
theorem B6339863 : Blo 2225435 6339863 := bstep (se 1 (by rfl) ⟨4754897, by rfl⟩ : syracuseStep 6339863 = 9509795) B9509795
theorem B4226575 : Blo 2225435 4226575 := bstep (se 1 (by rfl) ⟨3169931, by rfl⟩ : syracuseStep 4226575 = 6339863) B6339863
theorem B5635433 : Blo 2225435 5635433 := bstep (se 2 (by rfl) ⟨2113287, by rfl⟩ : syracuseStep 5635433 = 4226575) B4226575
theorem B3756955 : Blo 2225435 3756955 := bstep (se 1 (by rfl) ⟨2817716, by rfl⟩ : syracuseStep 3756955 = 5635433) B5635433
theorem B5009273 : Blo 2225435 5009273 := bstep (se 2 (by rfl) ⟨1878477, by rfl⟩ : syracuseStep 5009273 = 3756955) B3756955
theorem B3339515 : Blo 2225435 3339515 := bstep (se 1 (by rfl) ⟨2504636, by rfl⟩ : syracuseStep 3339515 = 5009273) B5009273
theorem B2226343 : Blo 2225435 2226343 := bstep (se 1 (by rfl) ⟨1669757, by rfl⟩ : syracuseStep 2226343 = 3339515) B3339515
theorem B2504641 : Blo 2225435 2504641 := bbase (se 2 (by rfl) ⟨939240, by rfl⟩ : syracuseStep 2504641 = 1878481) (by norm_num)
theorem B3339521 : Blo 2225435 3339521 := bstep (se 2 (by rfl) ⟨1252320, by rfl⟩ : syracuseStep 3339521 = 2504641) B2504641
theorem B2226347 : Blo 2225435 2226347 := bstep (se 1 (by rfl) ⟨1669760, by rfl⟩ : syracuseStep 2226347 = 3339521) B3339521
theorem B5635453 : Blo 2225435 5635453 := bbase (se 3 (by rfl) ⟨1056647, by rfl⟩ : syracuseStep 5635453 = 2113295) (by norm_num)
theorem B7513937 : Blo 2225435 7513937 := bstep (se 2 (by rfl) ⟨2817726, by rfl⟩ : syracuseStep 7513937 = 5635453) B5635453
theorem B5009291 : Blo 2225435 5009291 := bstep (se 1 (by rfl) ⟨3756968, by rfl⟩ : syracuseStep 5009291 = 7513937) B7513937
theorem B3339527 : Blo 2225435 3339527 := bstep (se 1 (by rfl) ⟨2504645, by rfl⟩ : syracuseStep 3339527 = 5009291) B5009291
theorem B2226351 : Blo 2225435 2226351 := bstep (se 1 (by rfl) ⟨1669763, by rfl⟩ : syracuseStep 2226351 = 3339527) B3339527
theorem B3339533 : Blo 2225435 3339533 := bbase (se 3 (by rfl) ⟨626162, by rfl⟩ : syracuseStep 3339533 = 1252325) (by norm_num)
theorem B2226355 : Blo 2225435 2226355 := bstep (se 1 (by rfl) ⟨1669766, by rfl⟩ : syracuseStep 2226355 = 3339533) B3339533
theorem B5009309 : Blo 2225435 5009309 := bbase (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) (by norm_num)
theorem B3339539 : Blo 2225435 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B2226359 : Blo 2225435 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B3756989 : Blo 2225435 3756989 := bbase (se 3 (by rfl) ⟨704435, by rfl⟩ : syracuseStep 3756989 = 1408871) (by norm_num)
theorem B2504659 : Blo 2225435 2504659 := bstep (se 1 (by rfl) ⟨1878494, by rfl⟩ : syracuseStep 2504659 = 3756989) B3756989
theorem B3339545 : Blo 2225435 3339545 := bstep (se 2 (by rfl) ⟨1252329, by rfl⟩ : syracuseStep 3339545 = 2504659) B2504659
theorem B2226363 : Blo 2225435 2226363 := bstep (se 1 (by rfl) ⟨1669772, by rfl⟩ : syracuseStep 2226363 = 3339545) B3339545
theorem B12679861 : Blo 2225435 12679861 := bbase (se 5 (by rfl) ⟨594368, by rfl⟩ : syracuseStep 12679861 = 1188737) (by norm_num)
theorem B16906481 : Blo 2225435 16906481 := bstep (se 2 (by rfl) ⟨6339930, by rfl⟩ : syracuseStep 16906481 = 12679861) B12679861
theorem B11270987 : Blo 2225435 11270987 := bstep (se 1 (by rfl) ⟨8453240, by rfl⟩ : syracuseStep 11270987 = 16906481) B16906481
theorem B7513991 : Blo 2225435 7513991 := bstep (se 1 (by rfl) ⟨5635493, by rfl⟩ : syracuseStep 7513991 = 11270987) B11270987
theorem B5009327 : Blo 2225435 5009327 := bstep (se 1 (by rfl) ⟨3756995, by rfl⟩ : syracuseStep 5009327 = 7513991) B7513991
theorem B3339551 : Blo 2225435 3339551 := bstep (se 1 (by rfl) ⟨2504663, by rfl⟩ : syracuseStep 3339551 = 5009327) B5009327
theorem B2226367 : Blo 2225435 2226367 := bstep (se 1 (by rfl) ⟨1669775, by rfl⟩ : syracuseStep 2226367 = 3339551) B3339551
theorem B3339557 : Blo 2225435 3339557 := bbase (se 4 (by rfl) ⟨313083, by rfl⟩ : syracuseStep 3339557 = 626167) (by norm_num)
theorem B2226371 : Blo 2225435 2226371 := bstep (se 1 (by rfl) ⟨1669778, by rfl⟩ : syracuseStep 2226371 = 3339557) B3339557
theorem B2817757 : Blo 2225435 2817757 := bbase (se 3 (by rfl) ⟨528329, by rfl⟩ : syracuseStep 2817757 = 1056659) (by norm_num)
theorem B3757009 : Blo 2225435 3757009 := bstep (se 2 (by rfl) ⟨1408878, by rfl⟩ : syracuseStep 3757009 = 2817757) B2817757
theorem B5009345 : Blo 2225435 5009345 := bstep (se 2 (by rfl) ⟨1878504, by rfl⟩ : syracuseStep 5009345 = 3757009) B3757009
theorem B3339563 : Blo 2225435 3339563 := bstep (se 1 (by rfl) ⟨2504672, by rfl⟩ : syracuseStep 3339563 = 5009345) B5009345
theorem B2226375 : Blo 2225435 2226375 := bstep (se 1 (by rfl) ⟨1669781, by rfl⟩ : syracuseStep 2226375 = 3339563) B3339563
theorem B2504677 : Blo 2225435 2504677 := bbase (se 4 (by rfl) ⟨234813, by rfl⟩ : syracuseStep 2504677 = 469627) (by norm_num)
theorem B3339569 : Blo 2225435 3339569 := bstep (se 2 (by rfl) ⟨1252338, by rfl⟩ : syracuseStep 3339569 = 2504677) B2504677
theorem B2226379 : Blo 2225435 2226379 := bstep (se 1 (by rfl) ⟨1669784, by rfl⟩ : syracuseStep 2226379 = 3339569) B3339569
theorem B12036053 : Blo 2225435 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B8024035 : Blo 2225435 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B10698713 : Blo 2225435 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B7132475 : Blo 2225435 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B4754983 : Blo 2225435 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B6339977 : Blo 2225435 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B4226651 : Blo 2225435 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B2817767 : Blo 2225435 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B7514045 : Blo 2225435 7514045 := bstep (se 3 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 7514045 = 2817767) B2817767
theorem B5009363 : Blo 2225435 5009363 := bstep (se 1 (by rfl) ⟨3757022, by rfl⟩ : syracuseStep 5009363 = 7514045) B7514045
theorem B3339575 : Blo 2225435 3339575 := bstep (se 1 (by rfl) ⟨2504681, by rfl⟩ : syracuseStep 3339575 = 5009363) B5009363
theorem B2226383 : Blo 2225435 2226383 := bstep (se 1 (by rfl) ⟨1669787, by rfl⟩ : syracuseStep 2226383 = 3339575) B3339575
theorem B3339581 : Blo 2225435 3339581 := bbase (se 3 (by rfl) ⟨626171, by rfl⟩ : syracuseStep 3339581 = 1252343) (by norm_num)
theorem B2226387 : Blo 2225435 2226387 := bstep (se 1 (by rfl) ⟨1669790, by rfl⟩ : syracuseStep 2226387 = 3339581) B3339581
theorem B5009381 : Blo 2225435 5009381 := bbase (se 4 (by rfl) ⟨469629, by rfl⟩ : syracuseStep 5009381 = 939259) (by norm_num)
theorem B3339587 : Blo 2225435 3339587 := bstep (se 1 (by rfl) ⟨2504690, by rfl⟩ : syracuseStep 3339587 = 5009381) B5009381
theorem B2226391 : Blo 2225435 2226391 := bstep (se 1 (by rfl) ⟨1669793, by rfl⟩ : syracuseStep 2226391 = 3339587) B3339587
theorem B5635565 : Blo 2225435 5635565 := bbase (se 3 (by rfl) ⟨1056668, by rfl⟩ : syracuseStep 5635565 = 2113337) (by norm_num)
theorem B3757043 : Blo 2225435 3757043 := bstep (se 1 (by rfl) ⟨2817782, by rfl⟩ : syracuseStep 3757043 = 5635565) B5635565
theorem B2504695 : Blo 2225435 2504695 := bstep (se 1 (by rfl) ⟨1878521, by rfl⟩ : syracuseStep 2504695 = 3757043) B3757043
theorem B3339593 : Blo 2225435 3339593 := bstep (se 2 (by rfl) ⟨1252347, by rfl⟩ : syracuseStep 3339593 = 2504695) B2504695
theorem B2226395 : Blo 2225435 2226395 := bstep (se 1 (by rfl) ⟨1669796, by rfl⟩ : syracuseStep 2226395 = 3339593) B3339593
theorem B3385165 : Blo 2225435 3385165 := bbase (se 3 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 3385165 = 1269437) (by norm_num)
theorem B4513553 : Blo 2225435 4513553 := bstep (se 2 (by rfl) ⟨1692582, by rfl⟩ : syracuseStep 4513553 = 3385165) B3385165
theorem B3009035 : Blo 2225435 3009035 := bstep (se 1 (by rfl) ⟨2256776, by rfl⟩ : syracuseStep 3009035 = 4513553) B4513553
theorem B8024093 : Blo 2225435 8024093 := bstep (se 3 (by rfl) ⟨1504517, by rfl⟩ : syracuseStep 8024093 = 3009035) B3009035
theorem B5349395 : Blo 2225435 5349395 := bstep (se 1 (by rfl) ⟨4012046, by rfl⟩ : syracuseStep 5349395 = 8024093) B8024093
theorem B3566263 : Blo 2225435 3566263 := bstep (se 1 (by rfl) ⟨2674697, by rfl⟩ : syracuseStep 3566263 = 5349395) B5349395
theorem B4755017 : Blo 2225435 4755017 := bstep (se 2 (by rfl) ⟨1783131, by rfl⟩ : syracuseStep 4755017 = 3566263) B3566263
theorem B3170011 : Blo 2225435 3170011 := bstep (se 1 (by rfl) ⟨2377508, by rfl⟩ : syracuseStep 3170011 = 4755017) B4755017
theorem B4226681 : Blo 2225435 4226681 := bstep (se 2 (by rfl) ⟨1585005, by rfl⟩ : syracuseStep 4226681 = 3170011) B3170011
theorem B11271149 : Blo 2225435 11271149 := bstep (se 3 (by rfl) ⟨2113340, by rfl⟩ : syracuseStep 11271149 = 4226681) B4226681
theorem B7514099 : Blo 2225435 7514099 := bstep (se 1 (by rfl) ⟨5635574, by rfl⟩ : syracuseStep 7514099 = 11271149) B11271149
theorem B5009399 : Blo 2225435 5009399 := bstep (se 1 (by rfl) ⟨3757049, by rfl⟩ : syracuseStep 5009399 = 7514099) B7514099
theorem B3339599 : Blo 2225435 3339599 := bstep (se 1 (by rfl) ⟨2504699, by rfl⟩ : syracuseStep 3339599 = 5009399) B5009399
theorem B2226399 : Blo 2225435 2226399 := bstep (se 1 (by rfl) ⟨1669799, by rfl⟩ : syracuseStep 2226399 = 3339599) B3339599
theorem B3339605 : Blo 2225435 3339605 := bbase (se 13 (by rfl) ⟨611, by rfl⟩ : syracuseStep 3339605 = 1223) (by norm_num)
theorem B2226403 : Blo 2225435 2226403 := bstep (se 1 (by rfl) ⟨1669802, by rfl⟩ : syracuseStep 2226403 = 3339605) B3339605
theorem B2377517 : Blo 2225435 2377517 := bbase (se 3 (by rfl) ⟨445784, by rfl⟩ : syracuseStep 2377517 = 891569) (by norm_num)
theorem B6340045 : Blo 2225435 6340045 := bstep (se 3 (by rfl) ⟨1188758, by rfl⟩ : syracuseStep 6340045 = 2377517) B2377517
theorem B8453393 : Blo 2225435 8453393 := bstep (se 2 (by rfl) ⟨3170022, by rfl⟩ : syracuseStep 8453393 = 6340045) B6340045
theorem B5635595 : Blo 2225435 5635595 := bstep (se 1 (by rfl) ⟨4226696, by rfl⟩ : syracuseStep 5635595 = 8453393) B8453393
theorem B3757063 : Blo 2225435 3757063 := bstep (se 1 (by rfl) ⟨2817797, by rfl⟩ : syracuseStep 3757063 = 5635595) B5635595
theorem B5009417 : Blo 2225435 5009417 := bstep (se 2 (by rfl) ⟨1878531, by rfl⟩ : syracuseStep 5009417 = 3757063) B3757063
theorem B3339611 : Blo 2225435 3339611 := bstep (se 1 (by rfl) ⟨2504708, by rfl⟩ : syracuseStep 3339611 = 5009417) B5009417
theorem B2226407 : Blo 2225435 2226407 := bstep (se 1 (by rfl) ⟨1669805, by rfl⟩ : syracuseStep 2226407 = 3339611) B3339611
theorem B2504713 : Blo 2225435 2504713 := bbase (se 2 (by rfl) ⟨939267, by rfl⟩ : syracuseStep 2504713 = 1878535) (by norm_num)
theorem B3339617 : Blo 2225435 3339617 := bstep (se 2 (by rfl) ⟨1252356, by rfl⟩ : syracuseStep 3339617 = 2504713) B2504713
theorem B2226411 : Blo 2225435 2226411 := bstep (se 1 (by rfl) ⟨1669808, by rfl⟩ : syracuseStep 2226411 = 3339617) B3339617
theorem B7825925 : Blo 2225435 7825925 := bbase (se 4 (by rfl) ⟨733680, by rfl⟩ : syracuseStep 7825925 = 1467361) (by norm_num)
theorem B5217283 : Blo 2225435 5217283 := bstep (se 1 (by rfl) ⟨3912962, by rfl⟩ : syracuseStep 5217283 = 7825925) B7825925
theorem B27825509 : Blo 2225435 27825509 := bstep (se 4 (by rfl) ⟨2608641, by rfl⟩ : syracuseStep 27825509 = 5217283) B5217283
theorem B18550339 : Blo 2225435 18550339 := bstep (se 1 (by rfl) ⟨13912754, by rfl⟩ : syracuseStep 18550339 = 27825509) B27825509
theorem B98935141 : Blo 2225435 98935141 := bstep (se 4 (by rfl) ⟨9275169, by rfl⟩ : syracuseStep 98935141 = 18550339) B18550339
theorem B131913521 : Blo 2225435 131913521 := bstep (se 2 (by rfl) ⟨49467570, by rfl⟩ : syracuseStep 131913521 = 98935141) B98935141
theorem B87942347 : Blo 2225435 87942347 := bstep (se 1 (by rfl) ⟨65956760, by rfl⟩ : syracuseStep 87942347 = 131913521) B131913521
theorem B58628231 : Blo 2225435 58628231 := bstep (se 1 (by rfl) ⟨43971173, by rfl⟩ : syracuseStep 58628231 = 87942347) B87942347
theorem B39085487 : Blo 2225435 39085487 := bstep (se 1 (by rfl) ⟨29314115, by rfl⟩ : syracuseStep 39085487 = 58628231) B58628231
theorem B26056991 : Blo 2225435 26056991 := bstep (se 1 (by rfl) ⟨19542743, by rfl⟩ : syracuseStep 26056991 = 39085487) B39085487
theorem B69485309 : Blo 2225435 69485309 := bstep (se 3 (by rfl) ⟨13028495, by rfl⟩ : syracuseStep 69485309 = 26056991) B26056991
theorem B46323539 : Blo 2225435 46323539 := bstep (se 1 (by rfl) ⟨34742654, by rfl⟩ : syracuseStep 46323539 = 69485309) B69485309
theorem B30882359 : Blo 2225435 30882359 := bstep (se 1 (by rfl) ⟨23161769, by rfl⟩ : syracuseStep 30882359 = 46323539) B46323539
theorem B20588239 : Blo 2225435 20588239 := bstep (se 1 (by rfl) ⟨15441179, by rfl⟩ : syracuseStep 20588239 = 30882359) B30882359
theorem B27450985 : Blo 2225435 27450985 := bstep (se 2 (by rfl) ⟨10294119, by rfl⟩ : syracuseStep 27450985 = 20588239) B20588239
theorem B36601313 : Blo 2225435 36601313 := bstep (se 2 (by rfl) ⟨13725492, by rfl⟩ : syracuseStep 36601313 = 27450985) B27450985
theorem B97603501 : Blo 2225435 97603501 := bstep (se 3 (by rfl) ⟨18300656, by rfl⟩ : syracuseStep 97603501 = 36601313) B36601313
theorem B130138001 : Blo 2225435 130138001 := bstep (se 2 (by rfl) ⟨48801750, by rfl⟩ : syracuseStep 130138001 = 97603501) B97603501
theorem B86758667 : Blo 2225435 86758667 := bstep (se 1 (by rfl) ⟨65069000, by rfl⟩ : syracuseStep 86758667 = 130138001) B130138001
theorem B57839111 : Blo 2225435 57839111 := bstep (se 1 (by rfl) ⟨43379333, by rfl⟩ : syracuseStep 57839111 = 86758667) B86758667
theorem B38559407 : Blo 2225435 38559407 := bstep (se 1 (by rfl) ⟨28919555, by rfl⟩ : syracuseStep 38559407 = 57839111) B57839111
theorem B102825085 : Blo 2225435 102825085 := bstep (se 3 (by rfl) ⟨19279703, by rfl⟩ : syracuseStep 102825085 = 38559407) B38559407
theorem B137100113 : Blo 2225435 137100113 := bstep (se 2 (by rfl) ⟨51412542, by rfl⟩ : syracuseStep 137100113 = 102825085) B102825085
theorem B91400075 : Blo 2225435 91400075 := bstep (se 1 (by rfl) ⟨68550056, by rfl⟩ : syracuseStep 91400075 = 137100113) B137100113
theorem B60933383 : Blo 2225435 60933383 := bstep (se 1 (by rfl) ⟨45700037, by rfl⟩ : syracuseStep 60933383 = 91400075) B91400075
theorem B40622255 : Blo 2225435 40622255 := bstep (se 1 (by rfl) ⟨30466691, by rfl⟩ : syracuseStep 40622255 = 60933383) B60933383
theorem B27081503 : Blo 2225435 27081503 := bstep (se 1 (by rfl) ⟨20311127, by rfl⟩ : syracuseStep 27081503 = 40622255) B40622255
theorem B18054335 : Blo 2225435 18054335 := bstep (se 1 (by rfl) ⟨13540751, by rfl⟩ : syracuseStep 18054335 = 27081503) B27081503
theorem B12036223 : Blo 2225435 12036223 := bstep (se 1 (by rfl) ⟨9027167, by rfl⟩ : syracuseStep 12036223 = 18054335) B18054335
theorem B16048297 : Blo 2225435 16048297 := bstep (se 2 (by rfl) ⟨6018111, by rfl⟩ : syracuseStep 16048297 = 12036223) B12036223
theorem B21397729 : Blo 2225435 21397729 := bstep (se 2 (by rfl) ⟨8024148, by rfl⟩ : syracuseStep 21397729 = 16048297) B16048297
theorem B28530305 : Blo 2225435 28530305 := bstep (se 2 (by rfl) ⟨10698864, by rfl⟩ : syracuseStep 28530305 = 21397729) B21397729
theorem B19020203 : Blo 2225435 19020203 := bstep (se 1 (by rfl) ⟨14265152, by rfl⟩ : syracuseStep 19020203 = 28530305) B28530305
theorem B12680135 : Blo 2225435 12680135 := bstep (se 1 (by rfl) ⟨9510101, by rfl⟩ : syracuseStep 12680135 = 19020203) B19020203
theorem B8453423 : Blo 2225435 8453423 := bstep (se 1 (by rfl) ⟨6340067, by rfl⟩ : syracuseStep 8453423 = 12680135) B12680135
theorem B5635615 : Blo 2225435 5635615 := bstep (se 1 (by rfl) ⟨4226711, by rfl⟩ : syracuseStep 5635615 = 8453423) B8453423
theorem B7514153 : Blo 2225435 7514153 := bstep (se 2 (by rfl) ⟨2817807, by rfl⟩ : syracuseStep 7514153 = 5635615) B5635615
theorem B5009435 : Blo 2225435 5009435 := bstep (se 1 (by rfl) ⟨3757076, by rfl⟩ : syracuseStep 5009435 = 7514153) B7514153
theorem B3339623 : Blo 2225435 3339623 := bstep (se 1 (by rfl) ⟨2504717, by rfl⟩ : syracuseStep 3339623 = 5009435) B5009435
theorem B2226415 : Blo 2225435 2226415 := bstep (se 1 (by rfl) ⟨1669811, by rfl⟩ : syracuseStep 2226415 = 3339623) B3339623
theorem B3339629 : Blo 2225435 3339629 := bbase (se 3 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 3339629 = 1252361) (by norm_num)
theorem B2226419 : Blo 2225435 2226419 := bstep (se 1 (by rfl) ⟨1669814, by rfl⟩ : syracuseStep 2226419 = 3339629) B3339629
theorem B5009453 : Blo 2225435 5009453 := bbase (se 3 (by rfl) ⟨939272, by rfl⟩ : syracuseStep 5009453 = 1878545) (by norm_num)
theorem B3339635 : Blo 2225435 3339635 := bstep (se 1 (by rfl) ⟨2504726, by rfl⟩ : syracuseStep 3339635 = 5009453) B5009453
theorem B2226423 : Blo 2225435 2226423 := bstep (se 1 (by rfl) ⟨1669817, by rfl⟩ : syracuseStep 2226423 = 3339635) B3339635
theorem B2256805 : Blo 2225435 2256805 := bbase (se 4 (by rfl) ⟨211575, by rfl⟩ : syracuseStep 2256805 = 423151) (by norm_num)
theorem B3009073 : Blo 2225435 3009073 := bstep (se 2 (by rfl) ⟨1128402, by rfl⟩ : syracuseStep 3009073 = 2256805) B2256805
theorem B4012097 : Blo 2225435 4012097 := bstep (se 2 (by rfl) ⟨1504536, by rfl⟩ : syracuseStep 4012097 = 3009073) B3009073
theorem B10698925 : Blo 2225435 10698925 := bstep (se 3 (by rfl) ⟨2006048, by rfl⟩ : syracuseStep 10698925 = 4012097) B4012097
theorem B14265233 : Blo 2225435 14265233 := bstep (se 2 (by rfl) ⟨5349462, by rfl⟩ : syracuseStep 14265233 = 10698925) B10698925
theorem B9510155 : Blo 2225435 9510155 := bstep (se 1 (by rfl) ⟨7132616, by rfl⟩ : syracuseStep 9510155 = 14265233) B14265233
theorem B6340103 : Blo 2225435 6340103 := bstep (se 1 (by rfl) ⟨4755077, by rfl⟩ : syracuseStep 6340103 = 9510155) B9510155
theorem B4226735 : Blo 2225435 4226735 := bstep (se 1 (by rfl) ⟨3170051, by rfl⟩ : syracuseStep 4226735 = 6340103) B6340103
theorem B2817823 : Blo 2225435 2817823 := bstep (se 1 (by rfl) ⟨2113367, by rfl⟩ : syracuseStep 2817823 = 4226735) B4226735
theorem B3757097 : Blo 2225435 3757097 := bstep (se 2 (by rfl) ⟨1408911, by rfl⟩ : syracuseStep 3757097 = 2817823) B2817823
theorem B2504731 : Blo 2225435 2504731 := bstep (se 1 (by rfl) ⟨1878548, by rfl⟩ : syracuseStep 2504731 = 3757097) B3757097
theorem B3339641 : Blo 2225435 3339641 := bstep (se 2 (by rfl) ⟨1252365, by rfl⟩ : syracuseStep 3339641 = 2504731) B2504731
theorem B2226427 : Blo 2225435 2226427 := bstep (se 1 (by rfl) ⟨1669820, by rfl⟩ : syracuseStep 2226427 = 3339641) B3339641
theorem B8568821 : Blo 2225435 8568821 := bbase (se 5 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 8568821 = 803327) (by norm_num)
theorem B5712547 : Blo 2225435 5712547 := bstep (se 1 (by rfl) ⟨4284410, by rfl⟩ : syracuseStep 5712547 = 8568821) B8568821
theorem B7616729 : Blo 2225435 7616729 := bstep (se 2 (by rfl) ⟨2856273, by rfl⟩ : syracuseStep 7616729 = 5712547) B5712547
theorem B5077819 : Blo 2225435 5077819 := bstep (se 1 (by rfl) ⟨3808364, by rfl⟩ : syracuseStep 5077819 = 7616729) B7616729
theorem B6770425 : Blo 2225435 6770425 := bstep (se 2 (by rfl) ⟨2538909, by rfl⟩ : syracuseStep 6770425 = 5077819) B5077819
theorem B9027233 : Blo 2225435 9027233 := bstep (se 2 (by rfl) ⟨3385212, by rfl⟩ : syracuseStep 9027233 = 6770425) B6770425
theorem B6018155 : Blo 2225435 6018155 := bstep (se 1 (by rfl) ⟨4513616, by rfl⟩ : syracuseStep 6018155 = 9027233) B9027233
theorem B4012103 : Blo 2225435 4012103 := bstep (se 1 (by rfl) ⟨3009077, by rfl⟩ : syracuseStep 4012103 = 6018155) B6018155
theorem B10698941 : Blo 2225435 10698941 := bstep (se 3 (by rfl) ⟨2006051, by rfl⟩ : syracuseStep 10698941 = 4012103) B4012103
theorem B7132627 : Blo 2225435 7132627 := bstep (se 1 (by rfl) ⟨5349470, by rfl⟩ : syracuseStep 7132627 = 10698941) B10698941
theorem B38040677 : Blo 2225435 38040677 := bstep (se 4 (by rfl) ⟨3566313, by rfl⟩ : syracuseStep 38040677 = 7132627) B7132627
theorem B25360451 : Blo 2225435 25360451 := bstep (se 1 (by rfl) ⟨19020338, by rfl⟩ : syracuseStep 25360451 = 38040677) B38040677
theorem B16906967 : Blo 2225435 16906967 := bstep (se 1 (by rfl) ⟨12680225, by rfl⟩ : syracuseStep 16906967 = 25360451) B25360451
theorem B11271311 : Blo 2225435 11271311 := bstep (se 1 (by rfl) ⟨8453483, by rfl⟩ : syracuseStep 11271311 = 16906967) B16906967
theorem B7514207 : Blo 2225435 7514207 := bstep (se 1 (by rfl) ⟨5635655, by rfl⟩ : syracuseStep 7514207 = 11271311) B11271311
theorem B5009471 : Blo 2225435 5009471 := bstep (se 1 (by rfl) ⟨3757103, by rfl⟩ : syracuseStep 5009471 = 7514207) B7514207
theorem B3339647 : Blo 2225435 3339647 := bstep (se 1 (by rfl) ⟨2504735, by rfl⟩ : syracuseStep 3339647 = 5009471) B5009471
theorem B2226431 : Blo 2225435 2226431 := bstep (se 1 (by rfl) ⟨1669823, by rfl⟩ : syracuseStep 2226431 = 3339647) B3339647
theorem B3339653 : Blo 2225435 3339653 := bbase (se 4 (by rfl) ⟨313092, by rfl⟩ : syracuseStep 3339653 = 626185) (by norm_num)
theorem B2226435 : Blo 2225435 2226435 := bstep (se 1 (by rfl) ⟨1669826, by rfl⟩ : syracuseStep 2226435 = 3339653) B3339653
theorem B3757117 : Blo 2225435 3757117 := bbase (se 3 (by rfl) ⟨704459, by rfl⟩ : syracuseStep 3757117 = 1408919) (by norm_num)
theorem B5009489 : Blo 2225435 5009489 := bstep (se 2 (by rfl) ⟨1878558, by rfl⟩ : syracuseStep 5009489 = 3757117) B3757117
theorem B3339659 : Blo 2225435 3339659 := bstep (se 1 (by rfl) ⟨2504744, by rfl⟩ : syracuseStep 3339659 = 5009489) B5009489
theorem B2226439 : Blo 2225435 2226439 := bstep (se 1 (by rfl) ⟨1669829, by rfl⟩ : syracuseStep 2226439 = 3339659) B3339659
theorem B2504749 : Blo 2225435 2504749 := bbase (se 3 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 2504749 = 939281) (by norm_num)
theorem B3339665 : Blo 2225435 3339665 := bstep (se 2 (by rfl) ⟨1252374, by rfl⟩ : syracuseStep 3339665 = 2504749) B2504749
theorem B2226443 : Blo 2225435 2226443 := bstep (se 1 (by rfl) ⟨1669832, by rfl⟩ : syracuseStep 2226443 = 3339665) B3339665
theorem B7514261 : Blo 2225435 7514261 := bbase (se 6 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 7514261 = 352231) (by norm_num)
theorem B5009507 : Blo 2225435 5009507 := bstep (se 1 (by rfl) ⟨3757130, by rfl⟩ : syracuseStep 5009507 = 7514261) B7514261
theorem B3339671 : Blo 2225435 3339671 := bstep (se 1 (by rfl) ⟨2504753, by rfl⟩ : syracuseStep 3339671 = 5009507) B5009507
theorem B2226447 : Blo 2225435 2226447 := bstep (se 1 (by rfl) ⟨1669835, by rfl⟩ : syracuseStep 2226447 = 3339671) B3339671
theorem B3339677 : Blo 2225435 3339677 := bbase (se 3 (by rfl) ⟨626189, by rfl⟩ : syracuseStep 3339677 = 1252379) (by norm_num)
theorem B2226451 : Blo 2225435 2226451 := bstep (se 1 (by rfl) ⟨1669838, by rfl⟩ : syracuseStep 2226451 = 3339677) B3339677
theorem B5009525 : Blo 2225435 5009525 := bbase (se 5 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 5009525 = 469643) (by norm_num)
theorem B3339683 : Blo 2225435 3339683 := bstep (se 1 (by rfl) ⟨2504762, by rfl⟩ : syracuseStep 3339683 = 5009525) B5009525
theorem B2226455 : Blo 2225435 2226455 := bstep (se 1 (by rfl) ⟨1669841, by rfl⟩ : syracuseStep 2226455 = 3339683) B3339683
theorem B8024309 : Blo 2225435 8024309 := bbase (se 5 (by rfl) ⟨376139, by rfl⟩ : syracuseStep 8024309 = 752279) (by norm_num)
theorem B5349539 : Blo 2225435 5349539 := bstep (se 1 (by rfl) ⟨4012154, by rfl⟩ : syracuseStep 5349539 = 8024309) B8024309
theorem B3566359 : Blo 2225435 3566359 := bstep (se 1 (by rfl) ⟨2674769, by rfl⟩ : syracuseStep 3566359 = 5349539) B5349539
theorem B19020581 : Blo 2225435 19020581 := bstep (se 4 (by rfl) ⟨1783179, by rfl⟩ : syracuseStep 19020581 = 3566359) B3566359
theorem B12680387 : Blo 2225435 12680387 := bstep (se 1 (by rfl) ⟨9510290, by rfl⟩ : syracuseStep 12680387 = 19020581) B19020581
theorem B8453591 : Blo 2225435 8453591 := bstep (se 1 (by rfl) ⟨6340193, by rfl⟩ : syracuseStep 8453591 = 12680387) B12680387
theorem B5635727 : Blo 2225435 5635727 := bstep (se 1 (by rfl) ⟨4226795, by rfl⟩ : syracuseStep 5635727 = 8453591) B8453591
theorem B3757151 : Blo 2225435 3757151 := bstep (se 1 (by rfl) ⟨2817863, by rfl⟩ : syracuseStep 3757151 = 5635727) B5635727
theorem B2504767 : Blo 2225435 2504767 := bstep (se 1 (by rfl) ⟨1878575, by rfl⟩ : syracuseStep 2504767 = 3757151) B3757151
theorem B3339689 : Blo 2225435 3339689 := bstep (se 2 (by rfl) ⟨1252383, by rfl⟩ : syracuseStep 3339689 = 2504767) B2504767
theorem B2226459 : Blo 2225435 2226459 := bstep (se 1 (by rfl) ⟨1669844, by rfl⟩ : syracuseStep 2226459 = 3339689) B3339689
theorem B8453605 : Blo 2225435 8453605 := bbase (se 4 (by rfl) ⟨792525, by rfl⟩ : syracuseStep 8453605 = 1585051) (by norm_num)
theorem B11271473 : Blo 2225435 11271473 := bstep (se 2 (by rfl) ⟨4226802, by rfl⟩ : syracuseStep 11271473 = 8453605) B8453605
theorem B7514315 : Blo 2225435 7514315 := bstep (se 1 (by rfl) ⟨5635736, by rfl⟩ : syracuseStep 7514315 = 11271473) B11271473
theorem B5009543 : Blo 2225435 5009543 := bstep (se 1 (by rfl) ⟨3757157, by rfl⟩ : syracuseStep 5009543 = 7514315) B7514315
theorem B3339695 : Blo 2225435 3339695 := bstep (se 1 (by rfl) ⟨2504771, by rfl⟩ : syracuseStep 3339695 = 5009543) B5009543
theorem B2226463 : Blo 2225435 2226463 := bstep (se 1 (by rfl) ⟨1669847, by rfl⟩ : syracuseStep 2226463 = 3339695) B3339695
theorem B3339701 : Blo 2225435 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B2226467 : Blo 2225435 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B5635757 : Blo 2225435 5635757 := bbase (se 3 (by rfl) ⟨1056704, by rfl⟩ : syracuseStep 5635757 = 2113409) (by norm_num)
theorem B3757171 : Blo 2225435 3757171 := bstep (se 1 (by rfl) ⟨2817878, by rfl⟩ : syracuseStep 3757171 = 5635757) B5635757
theorem B5009561 : Blo 2225435 5009561 := bstep (se 2 (by rfl) ⟨1878585, by rfl⟩ : syracuseStep 5009561 = 3757171) B3757171
theorem B3339707 : Blo 2225435 3339707 := bstep (se 1 (by rfl) ⟨2504780, by rfl⟩ : syracuseStep 3339707 = 5009561) B5009561
theorem B2226471 : Blo 2225435 2226471 := bstep (se 1 (by rfl) ⟨1669853, by rfl⟩ : syracuseStep 2226471 = 3339707) B3339707
theorem B2504785 : Blo 2225435 2504785 := bbase (se 2 (by rfl) ⟨939294, by rfl⟩ : syracuseStep 2504785 = 1878589) (by norm_num)
theorem B3339713 : Blo 2225435 3339713 := bstep (se 2 (by rfl) ⟨1252392, by rfl⟩ : syracuseStep 3339713 = 2504785) B2504785
theorem B2226475 : Blo 2225435 2226475 := bstep (se 1 (by rfl) ⟨1669856, by rfl⟩ : syracuseStep 2226475 = 3339713) B3339713
theorem B3170125 : Blo 2225435 3170125 := bbase (se 3 (by rfl) ⟨594398, by rfl⟩ : syracuseStep 3170125 = 1188797) (by norm_num)
theorem B4226833 : Blo 2225435 4226833 := bstep (se 2 (by rfl) ⟨1585062, by rfl⟩ : syracuseStep 4226833 = 3170125) B3170125
theorem B5635777 : Blo 2225435 5635777 := bstep (se 2 (by rfl) ⟨2113416, by rfl⟩ : syracuseStep 5635777 = 4226833) B4226833
theorem B7514369 : Blo 2225435 7514369 := bstep (se 2 (by rfl) ⟨2817888, by rfl⟩ : syracuseStep 7514369 = 5635777) B5635777
theorem B5009579 : Blo 2225435 5009579 := bstep (se 1 (by rfl) ⟨3757184, by rfl⟩ : syracuseStep 5009579 = 7514369) B7514369
theorem B3339719 : Blo 2225435 3339719 := bstep (se 1 (by rfl) ⟨2504789, by rfl⟩ : syracuseStep 3339719 = 5009579) B5009579
theorem B2226479 : Blo 2225435 2226479 := bstep (se 1 (by rfl) ⟨1669859, by rfl⟩ : syracuseStep 2226479 = 3339719) B3339719
theorem B3339725 : Blo 2225435 3339725 := bbase (se 3 (by rfl) ⟨626198, by rfl⟩ : syracuseStep 3339725 = 1252397) (by norm_num)
theorem B2226483 : Blo 2225435 2226483 := bstep (se 1 (by rfl) ⟨1669862, by rfl⟩ : syracuseStep 2226483 = 3339725) B3339725
theorem B5009597 : Blo 2225435 5009597 := bbase (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) (by norm_num)
theorem B3339731 : Blo 2225435 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B2226487 : Blo 2225435 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B3757205 : Blo 2225435 3757205 := bbase (se 6 (by rfl) ⟨88059, by rfl⟩ : syracuseStep 3757205 = 176119) (by norm_num)
theorem B2504803 : Blo 2225435 2504803 := bstep (se 1 (by rfl) ⟨1878602, by rfl⟩ : syracuseStep 2504803 = 3757205) B3757205
theorem B3339737 : Blo 2225435 3339737 := bstep (se 2 (by rfl) ⟨1252401, by rfl⟩ : syracuseStep 3339737 = 2504803) B2504803
theorem B2226491 : Blo 2225435 2226491 := bstep (se 1 (by rfl) ⟨1669868, by rfl⟩ : syracuseStep 2226491 = 3339737) B3339737
theorem B8024437 : Blo 2225435 8024437 := bbase (se 5 (by rfl) ⟨376145, by rfl⟩ : syracuseStep 8024437 = 752291) (by norm_num)
theorem B10699249 : Blo 2225435 10699249 := bstep (se 2 (by rfl) ⟨4012218, by rfl⟩ : syracuseStep 10699249 = 8024437) B8024437
theorem B14265665 : Blo 2225435 14265665 := bstep (se 2 (by rfl) ⟨5349624, by rfl⟩ : syracuseStep 14265665 = 10699249) B10699249
theorem B9510443 : Blo 2225435 9510443 := bstep (se 1 (by rfl) ⟨7132832, by rfl⟩ : syracuseStep 9510443 = 14265665) B14265665
theorem B6340295 : Blo 2225435 6340295 := bstep (se 1 (by rfl) ⟨4755221, by rfl⟩ : syracuseStep 6340295 = 9510443) B9510443
theorem B16907453 : Blo 2225435 16907453 := bstep (se 3 (by rfl) ⟨3170147, by rfl⟩ : syracuseStep 16907453 = 6340295) B6340295
theorem B11271635 : Blo 2225435 11271635 := bstep (se 1 (by rfl) ⟨8453726, by rfl⟩ : syracuseStep 11271635 = 16907453) B16907453
theorem B7514423 : Blo 2225435 7514423 := bstep (se 1 (by rfl) ⟨5635817, by rfl⟩ : syracuseStep 7514423 = 11271635) B11271635
theorem B5009615 : Blo 2225435 5009615 := bstep (se 1 (by rfl) ⟨3757211, by rfl⟩ : syracuseStep 5009615 = 7514423) B7514423
theorem B3339743 : Blo 2225435 3339743 := bstep (se 1 (by rfl) ⟨2504807, by rfl⟩ : syracuseStep 3339743 = 5009615) B5009615
theorem B2226495 : Blo 2225435 2226495 := bstep (se 1 (by rfl) ⟨1669871, by rfl⟩ : syracuseStep 2226495 = 3339743) B3339743
theorem B3339749 : Blo 2225435 3339749 := bbase (se 4 (by rfl) ⟨313101, by rfl⟩ : syracuseStep 3339749 = 626203) (by norm_num)
theorem B2226499 : Blo 2225435 2226499 := bstep (se 1 (by rfl) ⟨1669874, by rfl⟩ : syracuseStep 2226499 = 3339749) B3339749
theorem B6770645 : Blo 2225435 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B4513763 : Blo 2225435 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B12036701 : Blo 2225435 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B32097869 : Blo 2225435 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B21398579 : Blo 2225435 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B14265719 : Blo 2225435 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B9510479 : Blo 2225435 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B6340319 : Blo 2225435 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B4226879 : Blo 2225435 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B2817919 : Blo 2225435 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B3757225 : Blo 2225435 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B5009633 : Blo 2225435 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B3339755 : Blo 2225435 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B2226503 : Blo 2225435 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B2504821 : Blo 2225435 2504821 := bbase (se 5 (by rfl) ⟨117413, by rfl⟩ : syracuseStep 2504821 = 234827) (by norm_num)
theorem B3339761 : Blo 2225435 3339761 := bstep (se 2 (by rfl) ⟨1252410, by rfl⟩ : syracuseStep 3339761 = 2504821) B2504821
theorem B2226507 : Blo 2225435 2226507 := bstep (se 1 (by rfl) ⟨1669880, by rfl⟩ : syracuseStep 2226507 = 3339761) B3339761
theorem B2817929 : Blo 2225435 2817929 := bbase (se 2 (by rfl) ⟨1056723, by rfl⟩ : syracuseStep 2817929 = 2113447) (by norm_num)
theorem B7514477 : Blo 2225435 7514477 := bstep (se 3 (by rfl) ⟨1408964, by rfl⟩ : syracuseStep 7514477 = 2817929) B2817929
theorem B5009651 : Blo 2225435 5009651 := bstep (se 1 (by rfl) ⟨3757238, by rfl⟩ : syracuseStep 5009651 = 7514477) B7514477
theorem B3339767 : Blo 2225435 3339767 := bstep (se 1 (by rfl) ⟨2504825, by rfl⟩ : syracuseStep 3339767 = 5009651) B5009651
theorem B2226511 : Blo 2225435 2226511 := bstep (se 1 (by rfl) ⟨1669883, by rfl⟩ : syracuseStep 2226511 = 3339767) B3339767
theorem B3339773 : Blo 2225435 3339773 := bbase (se 3 (by rfl) ⟨626207, by rfl⟩ : syracuseStep 3339773 = 1252415) (by norm_num)
theorem B2226515 : Blo 2225435 2226515 := bstep (se 1 (by rfl) ⟨1669886, by rfl⟩ : syracuseStep 2226515 = 3339773) B3339773
theorem B5009669 : Blo 2225435 5009669 := bbase (se 4 (by rfl) ⟨469656, by rfl⟩ : syracuseStep 5009669 = 939313) (by norm_num)
theorem B3339779 : Blo 2225435 3339779 := bstep (se 1 (by rfl) ⟨2504834, by rfl⟩ : syracuseStep 3339779 = 5009669) B5009669
theorem B2226519 : Blo 2225435 2226519 := bstep (se 1 (by rfl) ⟨1669889, by rfl⟩ : syracuseStep 2226519 = 3339779) B3339779
theorem B4226917 : Blo 2225435 4226917 := bbase (se 4 (by rfl) ⟨396273, by rfl⟩ : syracuseStep 4226917 = 792547) (by norm_num)
theorem B5635889 : Blo 2225435 5635889 := bstep (se 2 (by rfl) ⟨2113458, by rfl⟩ : syracuseStep 5635889 = 4226917) B4226917
theorem B3757259 : Blo 2225435 3757259 := bstep (se 1 (by rfl) ⟨2817944, by rfl⟩ : syracuseStep 3757259 = 5635889) B5635889
theorem B2504839 : Blo 2225435 2504839 := bstep (se 1 (by rfl) ⟨1878629, by rfl⟩ : syracuseStep 2504839 = 3757259) B3757259
theorem B3339785 : Blo 2225435 3339785 := bstep (se 2 (by rfl) ⟨1252419, by rfl⟩ : syracuseStep 3339785 = 2504839) B2504839
theorem B2226523 : Blo 2225435 2226523 := bstep (se 1 (by rfl) ⟨1669892, by rfl⟩ : syracuseStep 2226523 = 3339785) B3339785
theorem B11271797 : Blo 2225435 11271797 := bbase (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) (by norm_num)
theorem B7514531 : Blo 2225435 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B5009687 : Blo 2225435 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B3339791 : Blo 2225435 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B2226527 : Blo 2225435 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B3339797 : Blo 2225435 3339797 := bbase (se 6 (by rfl) ⟨78276, by rfl⟩ : syracuseStep 3339797 = 156553) (by norm_num)
theorem B2226531 : Blo 2225435 2226531 := bstep (se 1 (by rfl) ⟨1669898, by rfl⟩ : syracuseStep 2226531 = 3339797) B3339797
theorem B6018437 : Blo 2225435 6018437 := bbase (se 4 (by rfl) ⟨564228, by rfl⟩ : syracuseStep 6018437 = 1128457) (by norm_num)
theorem B4012291 : Blo 2225435 4012291 := bstep (se 1 (by rfl) ⟨3009218, by rfl⟩ : syracuseStep 4012291 = 6018437) B6018437
theorem B5349721 : Blo 2225435 5349721 := bstep (se 2 (by rfl) ⟨2006145, by rfl⟩ : syracuseStep 5349721 = 4012291) B4012291
theorem B7132961 : Blo 2225435 7132961 := bstep (se 2 (by rfl) ⟨2674860, by rfl⟩ : syracuseStep 7132961 = 5349721) B5349721
theorem B19021229 : Blo 2225435 19021229 := bstep (se 3 (by rfl) ⟨3566480, by rfl⟩ : syracuseStep 19021229 = 7132961) B7132961
theorem B12680819 : Blo 2225435 12680819 := bstep (se 1 (by rfl) ⟨9510614, by rfl⟩ : syracuseStep 12680819 = 19021229) B19021229
theorem B8453879 : Blo 2225435 8453879 := bstep (se 1 (by rfl) ⟨6340409, by rfl⟩ : syracuseStep 8453879 = 12680819) B12680819
theorem B5635919 : Blo 2225435 5635919 := bstep (se 1 (by rfl) ⟨4226939, by rfl⟩ : syracuseStep 5635919 = 8453879) B8453879
theorem B3757279 : Blo 2225435 3757279 := bstep (se 1 (by rfl) ⟨2817959, by rfl⟩ : syracuseStep 3757279 = 5635919) B5635919
theorem B5009705 : Blo 2225435 5009705 := bstep (se 2 (by rfl) ⟨1878639, by rfl⟩ : syracuseStep 5009705 = 3757279) B3757279
theorem B3339803 : Blo 2225435 3339803 := bstep (se 1 (by rfl) ⟨2504852, by rfl⟩ : syracuseStep 3339803 = 5009705) B5009705
theorem B2226535 : Blo 2225435 2226535 := bstep (se 1 (by rfl) ⟨1669901, by rfl⟩ : syracuseStep 2226535 = 3339803) B3339803
theorem B2504857 : Blo 2225435 2504857 := bbase (se 2 (by rfl) ⟨939321, by rfl⟩ : syracuseStep 2504857 = 1878643) (by norm_num)
theorem B3339809 : Blo 2225435 3339809 := bstep (se 2 (by rfl) ⟨1252428, by rfl⟩ : syracuseStep 3339809 = 2504857) B2504857
theorem B2226539 : Blo 2225435 2226539 := bstep (se 1 (by rfl) ⟨1669904, by rfl⟩ : syracuseStep 2226539 = 3339809) B3339809
theorem B8453909 : Blo 2225435 8453909 := bbase (se 6 (by rfl) ⟨198138, by rfl⟩ : syracuseStep 8453909 = 396277) (by norm_num)
theorem B5635939 : Blo 2225435 5635939 := bstep (se 1 (by rfl) ⟨4226954, by rfl⟩ : syracuseStep 5635939 = 8453909) B8453909
theorem B7514585 : Blo 2225435 7514585 := bstep (se 2 (by rfl) ⟨2817969, by rfl⟩ : syracuseStep 7514585 = 5635939) B5635939
theorem B5009723 : Blo 2225435 5009723 := bstep (se 1 (by rfl) ⟨3757292, by rfl⟩ : syracuseStep 5009723 = 7514585) B7514585
theorem B3339815 : Blo 2225435 3339815 := bstep (se 1 (by rfl) ⟨2504861, by rfl⟩ : syracuseStep 3339815 = 5009723) B5009723
theorem B2226543 : Blo 2225435 2226543 := bstep (se 1 (by rfl) ⟨1669907, by rfl⟩ : syracuseStep 2226543 = 3339815) B3339815
theorem B3339821 : Blo 2225435 3339821 := bbase (se 3 (by rfl) ⟨626216, by rfl⟩ : syracuseStep 3339821 = 1252433) (by norm_num)
theorem B2226547 : Blo 2225435 2226547 := bstep (se 1 (by rfl) ⟨1669910, by rfl⟩ : syracuseStep 2226547 = 3339821) B3339821
theorem B5009741 : Blo 2225435 5009741 := bbase (se 3 (by rfl) ⟨939326, by rfl⟩ : syracuseStep 5009741 = 1878653) (by norm_num)
theorem B3339827 : Blo 2225435 3339827 := bstep (se 1 (by rfl) ⟨2504870, by rfl⟩ : syracuseStep 3339827 = 5009741) B5009741
theorem B2226551 : Blo 2225435 2226551 := bstep (se 1 (by rfl) ⟨1669913, by rfl⟩ : syracuseStep 2226551 = 3339827) B3339827
theorem B2817985 : Blo 2225435 2817985 := bbase (se 2 (by rfl) ⟨1056744, by rfl⟩ : syracuseStep 2817985 = 2113489) (by norm_num)
theorem B3757313 : Blo 2225435 3757313 := bstep (se 2 (by rfl) ⟨1408992, by rfl⟩ : syracuseStep 3757313 = 2817985) B2817985
theorem B2504875 : Blo 2225435 2504875 := bstep (se 1 (by rfl) ⟨1878656, by rfl⟩ : syracuseStep 2504875 = 3757313) B3757313
theorem B3339833 : Blo 2225435 3339833 := bstep (se 2 (by rfl) ⟨1252437, by rfl⟩ : syracuseStep 3339833 = 2504875) B2504875
theorem B2226555 : Blo 2225435 2226555 := bstep (se 1 (by rfl) ⟨1669916, by rfl⟩ : syracuseStep 2226555 = 3339833) B3339833
theorem B4513877 : Blo 2225435 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B3009251 : Blo 2225435 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B8024669 : Blo 2225435 8024669 := bstep (se 3 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 8024669 = 3009251) B3009251
theorem B5349779 : Blo 2225435 5349779 := bstep (se 1 (by rfl) ⟨4012334, by rfl⟩ : syracuseStep 5349779 = 8024669) B8024669
theorem B3566519 : Blo 2225435 3566519 := bstep (se 1 (by rfl) ⟨2674889, by rfl⟩ : syracuseStep 3566519 = 5349779) B5349779
theorem B2377679 : Blo 2225435 2377679 := bstep (se 1 (by rfl) ⟨1783259, by rfl⟩ : syracuseStep 2377679 = 3566519) B3566519
theorem B25361909 : Blo 2225435 25361909 := bstep (se 5 (by rfl) ⟨1188839, by rfl⟩ : syracuseStep 25361909 = 2377679) B2377679
theorem B16907939 : Blo 2225435 16907939 := bstep (se 1 (by rfl) ⟨12680954, by rfl⟩ : syracuseStep 16907939 = 25361909) B25361909
theorem B11271959 : Blo 2225435 11271959 := bstep (se 1 (by rfl) ⟨8453969, by rfl⟩ : syracuseStep 11271959 = 16907939) B16907939
theorem B7514639 : Blo 2225435 7514639 := bstep (se 1 (by rfl) ⟨5635979, by rfl⟩ : syracuseStep 7514639 = 11271959) B11271959
theorem B5009759 : Blo 2225435 5009759 := bstep (se 1 (by rfl) ⟨3757319, by rfl⟩ : syracuseStep 5009759 = 7514639) B7514639
theorem B3339839 : Blo 2225435 3339839 := bstep (se 1 (by rfl) ⟨2504879, by rfl⟩ : syracuseStep 3339839 = 5009759) B5009759
theorem B2226559 : Blo 2225435 2226559 := bstep (se 1 (by rfl) ⟨1669919, by rfl⟩ : syracuseStep 2226559 = 3339839) B3339839
theorem B3339845 : Blo 2225435 3339845 := bbase (se 4 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 3339845 = 626221) (by norm_num)
theorem B2226563 : Blo 2225435 2226563 := bstep (se 1 (by rfl) ⟨1669922, by rfl⟩ : syracuseStep 2226563 = 3339845) B3339845
theorem B3757333 : Blo 2225435 3757333 := bbase (se 6 (by rfl) ⟨88062, by rfl⟩ : syracuseStep 3757333 = 176125) (by norm_num)
theorem B5009777 : Blo 2225435 5009777 := bstep (se 2 (by rfl) ⟨1878666, by rfl⟩ : syracuseStep 5009777 = 3757333) B3757333
theorem B3339851 : Blo 2225435 3339851 := bstep (se 1 (by rfl) ⟨2504888, by rfl⟩ : syracuseStep 3339851 = 5009777) B5009777
theorem B2226567 : Blo 2225435 2226567 := bstep (se 1 (by rfl) ⟨1669925, by rfl⟩ : syracuseStep 2226567 = 3339851) B3339851
theorem B2504893 : Blo 2225435 2504893 := bbase (se 3 (by rfl) ⟨469667, by rfl⟩ : syracuseStep 2504893 = 939335) (by norm_num)
theorem B3339857 : Blo 2225435 3339857 := bstep (se 2 (by rfl) ⟨1252446, by rfl⟩ : syracuseStep 3339857 = 2504893) B2504893
theorem B2226571 : Blo 2225435 2226571 := bstep (se 1 (by rfl) ⟨1669928, by rfl⟩ : syracuseStep 2226571 = 3339857) B3339857
theorem B7514693 : Blo 2225435 7514693 := bbase (se 4 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 7514693 = 1409005) (by norm_num)
theorem B5009795 : Blo 2225435 5009795 := bstep (se 1 (by rfl) ⟨3757346, by rfl⟩ : syracuseStep 5009795 = 7514693) B7514693
theorem B3339863 : Blo 2225435 3339863 := bstep (se 1 (by rfl) ⟨2504897, by rfl⟩ : syracuseStep 3339863 = 5009795) B5009795
theorem B2226575 : Blo 2225435 2226575 := bstep (se 1 (by rfl) ⟨1669931, by rfl⟩ : syracuseStep 2226575 = 3339863) B3339863
theorem B3339869 : Blo 2225435 3339869 := bbase (se 3 (by rfl) ⟨626225, by rfl⟩ : syracuseStep 3339869 = 1252451) (by norm_num)
theorem B2226579 : Blo 2225435 2226579 := bstep (se 1 (by rfl) ⟨1669934, by rfl⟩ : syracuseStep 2226579 = 3339869) B3339869
theorem B5009813 : Blo 2225435 5009813 := bbase (se 6 (by rfl) ⟨117417, by rfl⟩ : syracuseStep 5009813 = 234835) (by norm_num)
theorem B3339875 : Blo 2225435 3339875 := bstep (se 1 (by rfl) ⟨2504906, by rfl⟩ : syracuseStep 3339875 = 5009813) B5009813
theorem B2226583 : Blo 2225435 2226583 := bstep (se 1 (by rfl) ⟨1669937, by rfl⟩ : syracuseStep 2226583 = 3339875) B3339875
theorem B6863285 : Blo 2225435 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B4575523 : Blo 2225435 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B6100697 : Blo 2225435 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B16268525 : Blo 2225435 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B10845683 : Blo 2225435 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B7230455 : Blo 2225435 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B4820303 : Blo 2225435 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B3213535 : Blo 2225435 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B4284713 : Blo 2225435 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B2856475 : Blo 2225435 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B3808633 : Blo 2225435 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B5078177 : Blo 2225435 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B3385451 : Blo 2225435 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B2256967 : Blo 2225435 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B12037157 : Blo 2225435 12037157 := bstep (se 4 (by rfl) ⟨1128483, by rfl⟩ : syracuseStep 12037157 = 2256967) B2256967
theorem B8024771 : Blo 2225435 8024771 := bstep (se 1 (by rfl) ⟨6018578, by rfl⟩ : syracuseStep 8024771 = 12037157) B12037157
theorem B5349847 : Blo 2225435 5349847 := bstep (se 1 (by rfl) ⟨4012385, by rfl⟩ : syracuseStep 5349847 = 8024771) B8024771
theorem B7133129 : Blo 2225435 7133129 := bstep (se 2 (by rfl) ⟨2674923, by rfl⟩ : syracuseStep 7133129 = 5349847) B5349847
theorem B4755419 : Blo 2225435 4755419 := bstep (se 1 (by rfl) ⟨3566564, by rfl⟩ : syracuseStep 4755419 = 7133129) B7133129
theorem B3170279 : Blo 2225435 3170279 := bstep (se 1 (by rfl) ⟨2377709, by rfl⟩ : syracuseStep 3170279 = 4755419) B4755419
theorem B8454077 : Blo 2225435 8454077 := bstep (se 3 (by rfl) ⟨1585139, by rfl⟩ : syracuseStep 8454077 = 3170279) B3170279
theorem B5636051 : Blo 2225435 5636051 := bstep (se 1 (by rfl) ⟨4227038, by rfl⟩ : syracuseStep 5636051 = 8454077) B8454077
theorem B3757367 : Blo 2225435 3757367 := bstep (se 1 (by rfl) ⟨2818025, by rfl⟩ : syracuseStep 3757367 = 5636051) B5636051
theorem B2504911 : Blo 2225435 2504911 := bstep (se 1 (by rfl) ⟨1878683, by rfl⟩ : syracuseStep 2504911 = 3757367) B3757367
theorem B3339881 : Blo 2225435 3339881 := bstep (se 2 (by rfl) ⟨1252455, by rfl⟩ : syracuseStep 3339881 = 2504911) B2504911
theorem B2226587 : Blo 2225435 2226587 := bstep (se 1 (by rfl) ⟨1669940, by rfl⟩ : syracuseStep 2226587 = 3339881) B3339881
theorem B9510853 : Blo 2225435 9510853 := bbase (se 4 (by rfl) ⟨891642, by rfl⟩ : syracuseStep 9510853 = 1783285) (by norm_num)
theorem B12681137 : Blo 2225435 12681137 := bstep (se 2 (by rfl) ⟨4755426, by rfl⟩ : syracuseStep 12681137 = 9510853) B9510853
theorem B8454091 : Blo 2225435 8454091 := bstep (se 1 (by rfl) ⟨6340568, by rfl⟩ : syracuseStep 8454091 = 12681137) B12681137
theorem B11272121 : Blo 2225435 11272121 := bstep (se 2 (by rfl) ⟨4227045, by rfl⟩ : syracuseStep 11272121 = 8454091) B8454091
theorem B7514747 : Blo 2225435 7514747 := bstep (se 1 (by rfl) ⟨5636060, by rfl⟩ : syracuseStep 7514747 = 11272121) B11272121
theorem B5009831 : Blo 2225435 5009831 := bstep (se 1 (by rfl) ⟨3757373, by rfl⟩ : syracuseStep 5009831 = 7514747) B7514747
theorem B3339887 : Blo 2225435 3339887 := bstep (se 1 (by rfl) ⟨2504915, by rfl⟩ : syracuseStep 3339887 = 5009831) B5009831
theorem B2226591 : Blo 2225435 2226591 := bstep (se 1 (by rfl) ⟨1669943, by rfl⟩ : syracuseStep 2226591 = 3339887) B3339887
theorem B3339893 : Blo 2225435 3339893 := bbase (se 5 (by rfl) ⟨156557, by rfl⟩ : syracuseStep 3339893 = 313115) (by norm_num)
theorem B2226595 : Blo 2225435 2226595 := bstep (se 1 (by rfl) ⟨1669946, by rfl⟩ : syracuseStep 2226595 = 3339893) B3339893
theorem B4227061 : Blo 2225435 4227061 := bbase (se 5 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 4227061 = 396287) (by norm_num)
theorem B5636081 : Blo 2225435 5636081 := bstep (se 2 (by rfl) ⟨2113530, by rfl⟩ : syracuseStep 5636081 = 4227061) B4227061
theorem B3757387 : Blo 2225435 3757387 := bstep (se 1 (by rfl) ⟨2818040, by rfl⟩ : syracuseStep 3757387 = 5636081) B5636081
theorem B5009849 : Blo 2225435 5009849 := bstep (se 2 (by rfl) ⟨1878693, by rfl⟩ : syracuseStep 5009849 = 3757387) B3757387
theorem B3339899 : Blo 2225435 3339899 := bstep (se 1 (by rfl) ⟨2504924, by rfl⟩ : syracuseStep 3339899 = 5009849) B5009849
theorem B2226599 : Blo 2225435 2226599 := bstep (se 1 (by rfl) ⟨1669949, by rfl⟩ : syracuseStep 2226599 = 3339899) B3339899
theorem B2504929 : Blo 2225435 2504929 := bbase (se 2 (by rfl) ⟨939348, by rfl⟩ : syracuseStep 2504929 = 1878697) (by norm_num)
theorem B3339905 : Blo 2225435 3339905 := bstep (se 2 (by rfl) ⟨1252464, by rfl⟩ : syracuseStep 3339905 = 2504929) B2504929
theorem B2226603 : Blo 2225435 2226603 := bstep (se 1 (by rfl) ⟨1669952, by rfl⟩ : syracuseStep 2226603 = 3339905) B3339905
theorem B5636101 : Blo 2225435 5636101 := bbase (se 4 (by rfl) ⟨528384, by rfl⟩ : syracuseStep 5636101 = 1056769) (by norm_num)
theorem B7514801 : Blo 2225435 7514801 := bstep (se 2 (by rfl) ⟨2818050, by rfl⟩ : syracuseStep 7514801 = 5636101) B5636101
theorem B5009867 : Blo 2225435 5009867 := bstep (se 1 (by rfl) ⟨3757400, by rfl⟩ : syracuseStep 5009867 = 7514801) B7514801
theorem B3339911 : Blo 2225435 3339911 := bstep (se 1 (by rfl) ⟨2504933, by rfl⟩ : syracuseStep 3339911 = 5009867) B5009867
theorem B2226607 : Blo 2225435 2226607 := bstep (se 1 (by rfl) ⟨1669955, by rfl⟩ : syracuseStep 2226607 = 3339911) B3339911
theorem B3339917 : Blo 2225435 3339917 := bbase (se 3 (by rfl) ⟨626234, by rfl⟩ : syracuseStep 3339917 = 1252469) (by norm_num)
theorem B2226611 : Blo 2225435 2226611 := bstep (se 1 (by rfl) ⟨1669958, by rfl⟩ : syracuseStep 2226611 = 3339917) B3339917
theorem B5009885 : Blo 2225435 5009885 := bbase (se 3 (by rfl) ⟨939353, by rfl⟩ : syracuseStep 5009885 = 1878707) (by norm_num)
theorem B3339923 : Blo 2225435 3339923 := bstep (se 1 (by rfl) ⟨2504942, by rfl⟩ : syracuseStep 3339923 = 5009885) B5009885
theorem B2226615 : Blo 2225435 2226615 := bstep (se 1 (by rfl) ⟨1669961, by rfl⟩ : syracuseStep 2226615 = 3339923) B3339923
theorem B3757421 : Blo 2225435 3757421 := bbase (se 3 (by rfl) ⟨704516, by rfl⟩ : syracuseStep 3757421 = 1409033) (by norm_num)
theorem B2504947 : Blo 2225435 2504947 := bstep (se 1 (by rfl) ⟨1878710, by rfl⟩ : syracuseStep 2504947 = 3757421) B3757421
theorem B3339929 : Blo 2225435 3339929 := bstep (se 2 (by rfl) ⟨1252473, by rfl⟩ : syracuseStep 3339929 = 2504947) B2504947
theorem B2226619 : Blo 2225435 2226619 := bstep (se 1 (by rfl) ⟨1669964, by rfl⟩ : syracuseStep 2226619 = 3339929) B3339929
theorem B2544437 : Blo 2225435 2544437 := bbase (se 5 (by rfl) ⟨119270, by rfl⟩ : syracuseStep 2544437 = 238541) (by norm_num)
theorem B6785165 : Blo 2225435 6785165 := bstep (se 3 (by rfl) ⟨1272218, by rfl⟩ : syracuseStep 6785165 = 2544437) B2544437
theorem B18093773 : Blo 2225435 18093773 := bstep (se 3 (by rfl) ⟨3392582, by rfl⟩ : syracuseStep 18093773 = 6785165) B6785165
theorem B12062515 : Blo 2225435 12062515 := bstep (se 1 (by rfl) ⟨9046886, by rfl⟩ : syracuseStep 12062515 = 18093773) B18093773
theorem B16083353 : Blo 2225435 16083353 := bstep (se 2 (by rfl) ⟨6031257, by rfl⟩ : syracuseStep 16083353 = 12062515) B12062515
theorem B10722235 : Blo 2225435 10722235 := bstep (se 1 (by rfl) ⟨8041676, by rfl⟩ : syracuseStep 10722235 = 16083353) B16083353
theorem B14296313 : Blo 2225435 14296313 := bstep (se 2 (by rfl) ⟨5361117, by rfl⟩ : syracuseStep 14296313 = 10722235) B10722235
theorem B9530875 : Blo 2225435 9530875 := bstep (se 1 (by rfl) ⟨7148156, by rfl⟩ : syracuseStep 9530875 = 14296313) B14296313
theorem B50831333 : Blo 2225435 50831333 := bstep (se 4 (by rfl) ⟨4765437, by rfl⟩ : syracuseStep 50831333 = 9530875) B9530875
theorem B33887555 : Blo 2225435 33887555 := bstep (se 1 (by rfl) ⟨25415666, by rfl⟩ : syracuseStep 33887555 = 50831333) B50831333
theorem B22591703 : Blo 2225435 22591703 := bstep (se 1 (by rfl) ⟨16943777, by rfl⟩ : syracuseStep 22591703 = 33887555) B33887555
theorem B15061135 : Blo 2225435 15061135 := bstep (se 1 (by rfl) ⟨11295851, by rfl⟩ : syracuseStep 15061135 = 22591703) B22591703
theorem B20081513 : Blo 2225435 20081513 := bstep (se 2 (by rfl) ⟨7530567, by rfl⟩ : syracuseStep 20081513 = 15061135) B15061135
theorem B13387675 : Blo 2225435 13387675 := bstep (se 1 (by rfl) ⟨10040756, by rfl⟩ : syracuseStep 13387675 = 20081513) B20081513
theorem B17850233 : Blo 2225435 17850233 := bstep (se 2 (by rfl) ⟨6693837, by rfl⟩ : syracuseStep 17850233 = 13387675) B13387675
theorem B47600621 : Blo 2225435 47600621 := bstep (se 3 (by rfl) ⟨8925116, by rfl⟩ : syracuseStep 47600621 = 17850233) B17850233
theorem B31733747 : Blo 2225435 31733747 := bstep (se 1 (by rfl) ⟨23800310, by rfl⟩ : syracuseStep 31733747 = 47600621) B47600621
theorem B21155831 : Blo 2225435 21155831 := bstep (se 1 (by rfl) ⟨15866873, by rfl⟩ : syracuseStep 21155831 = 31733747) B31733747
theorem B14103887 : Blo 2225435 14103887 := bstep (se 1 (by rfl) ⟨10577915, by rfl⟩ : syracuseStep 14103887 = 21155831) B21155831
theorem B150441461 : Blo 2225435 150441461 := bstep (se 5 (by rfl) ⟨7051943, by rfl⟩ : syracuseStep 150441461 = 14103887) B14103887
theorem B100294307 : Blo 2225435 100294307 := bstep (se 1 (by rfl) ⟨75220730, by rfl⟩ : syracuseStep 100294307 = 150441461) B150441461
theorem B66862871 : Blo 2225435 66862871 := bstep (se 1 (by rfl) ⟨50147153, by rfl⟩ : syracuseStep 66862871 = 100294307) B100294307
theorem B44575247 : Blo 2225435 44575247 := bstep (se 1 (by rfl) ⟨33431435, by rfl⟩ : syracuseStep 44575247 = 66862871) B66862871
theorem B29716831 : Blo 2225435 29716831 := bstep (se 1 (by rfl) ⟨22287623, by rfl⟩ : syracuseStep 29716831 = 44575247) B44575247
theorem B39622441 : Blo 2225435 39622441 := bstep (se 2 (by rfl) ⟨14858415, by rfl⟩ : syracuseStep 39622441 = 29716831) B29716831
theorem B52829921 : Blo 2225435 52829921 := bstep (se 2 (by rfl) ⟨19811220, by rfl⟩ : syracuseStep 52829921 = 39622441) B39622441
theorem B35219947 : Blo 2225435 35219947 := bstep (se 1 (by rfl) ⟨26414960, by rfl⟩ : syracuseStep 35219947 = 52829921) B52829921
theorem B46959929 : Blo 2225435 46959929 := bstep (se 2 (by rfl) ⟨17609973, by rfl⟩ : syracuseStep 46959929 = 35219947) B35219947
theorem B31306619 : Blo 2225435 31306619 := bstep (se 1 (by rfl) ⟨23479964, by rfl⟩ : syracuseStep 31306619 = 46959929) B46959929
theorem B83484317 : Blo 2225435 83484317 := bstep (se 3 (by rfl) ⟨15653309, by rfl⟩ : syracuseStep 83484317 = 31306619) B31306619
theorem B222624845 : Blo 2225435 222624845 := bstep (se 3 (by rfl) ⟨41742158, by rfl⟩ : syracuseStep 222624845 = 83484317) B83484317
theorem B148416563 : Blo 2225435 148416563 := bstep (se 1 (by rfl) ⟨111312422, by rfl⟩ : syracuseStep 148416563 = 222624845) B222624845
theorem B98944375 : Blo 2225435 98944375 := bstep (se 1 (by rfl) ⟨74208281, by rfl⟩ : syracuseStep 98944375 = 148416563) B148416563
theorem B131925833 : Blo 2225435 131925833 := bstep (se 2 (by rfl) ⟨49472187, by rfl⟩ : syracuseStep 131925833 = 98944375) B98944375
theorem B87950555 : Blo 2225435 87950555 := bstep (se 1 (by rfl) ⟨65962916, by rfl⟩ : syracuseStep 87950555 = 131925833) B131925833
theorem B58633703 : Blo 2225435 58633703 := bstep (se 1 (by rfl) ⟨43975277, by rfl⟩ : syracuseStep 58633703 = 87950555) B87950555
theorem B39089135 : Blo 2225435 39089135 := bstep (se 1 (by rfl) ⟨29316851, by rfl⟩ : syracuseStep 39089135 = 58633703) B58633703
theorem B26059423 : Blo 2225435 26059423 := bstep (se 1 (by rfl) ⟨19544567, by rfl⟩ : syracuseStep 26059423 = 39089135) B39089135
theorem B34745897 : Blo 2225435 34745897 := bstep (se 2 (by rfl) ⟨13029711, by rfl⟩ : syracuseStep 34745897 = 26059423) B26059423
theorem B23163931 : Blo 2225435 23163931 := bstep (se 1 (by rfl) ⟨17372948, by rfl⟩ : syracuseStep 23163931 = 34745897) B34745897
theorem B30885241 : Blo 2225435 30885241 := bstep (se 2 (by rfl) ⟨11581965, by rfl⟩ : syracuseStep 30885241 = 23163931) B23163931
theorem B41180321 : Blo 2225435 41180321 := bstep (se 2 (by rfl) ⟨15442620, by rfl⟩ : syracuseStep 41180321 = 30885241) B30885241
theorem B27453547 : Blo 2225435 27453547 := bstep (se 1 (by rfl) ⟨20590160, by rfl⟩ : syracuseStep 27453547 = 41180321) B41180321
theorem B36604729 : Blo 2225435 36604729 := bstep (se 2 (by rfl) ⟨13726773, by rfl⟩ : syracuseStep 36604729 = 27453547) B27453547
theorem B195225221 : Blo 2225435 195225221 := bstep (se 4 (by rfl) ⟨18302364, by rfl⟩ : syracuseStep 195225221 = 36604729) B36604729
theorem B130150147 : Blo 2225435 130150147 := bstep (se 1 (by rfl) ⟨97612610, by rfl⟩ : syracuseStep 130150147 = 195225221) B195225221
theorem B173533529 : Blo 2225435 173533529 := bstep (se 2 (by rfl) ⟨65075073, by rfl⟩ : syracuseStep 173533529 = 130150147) B130150147
theorem B115689019 : Blo 2225435 115689019 := bstep (se 1 (by rfl) ⟨86766764, by rfl⟩ : syracuseStep 115689019 = 173533529) B173533529
theorem B154252025 : Blo 2225435 154252025 := bstep (se 2 (by rfl) ⟨57844509, by rfl⟩ : syracuseStep 154252025 = 115689019) B115689019
theorem B102834683 : Blo 2225435 102834683 := bstep (se 1 (by rfl) ⟨77126012, by rfl⟩ : syracuseStep 102834683 = 154252025) B154252025
theorem B68556455 : Blo 2225435 68556455 := bstep (se 1 (by rfl) ⟨51417341, by rfl⟩ : syracuseStep 68556455 = 102834683) B102834683
theorem B45704303 : Blo 2225435 45704303 := bstep (se 1 (by rfl) ⟨34278227, by rfl⟩ : syracuseStep 45704303 = 68556455) B68556455
theorem B30469535 : Blo 2225435 30469535 := bstep (se 1 (by rfl) ⟨22852151, by rfl⟩ : syracuseStep 30469535 = 45704303) B45704303
theorem B20313023 : Blo 2225435 20313023 := bstep (se 1 (by rfl) ⟨15234767, by rfl⟩ : syracuseStep 20313023 = 30469535) B30469535
theorem B54168061 : Blo 2225435 54168061 := bstep (se 3 (by rfl) ⟨10156511, by rfl⟩ : syracuseStep 54168061 = 20313023) B20313023
theorem B72224081 : Blo 2225435 72224081 := bstep (se 2 (by rfl) ⟨27084030, by rfl⟩ : syracuseStep 72224081 = 54168061) B54168061
theorem B48149387 : Blo 2225435 48149387 := bstep (se 1 (by rfl) ⟨36112040, by rfl⟩ : syracuseStep 48149387 = 72224081) B72224081
theorem B32099591 : Blo 2225435 32099591 := bstep (se 1 (by rfl) ⟨24074693, by rfl⟩ : syracuseStep 32099591 = 48149387) B48149387
theorem B21399727 : Blo 2225435 21399727 := bstep (se 1 (by rfl) ⟨16049795, by rfl⟩ : syracuseStep 21399727 = 32099591) B32099591
theorem B28532969 : Blo 2225435 28532969 := bstep (se 2 (by rfl) ⟨10699863, by rfl⟩ : syracuseStep 28532969 = 21399727) B21399727
theorem B19021979 : Blo 2225435 19021979 := bstep (se 1 (by rfl) ⟨14266484, by rfl⟩ : syracuseStep 19021979 = 28532969) B28532969
theorem B12681319 : Blo 2225435 12681319 := bstep (se 1 (by rfl) ⟨9510989, by rfl⟩ : syracuseStep 12681319 = 19021979) B19021979
theorem B16908425 : Blo 2225435 16908425 := bstep (se 2 (by rfl) ⟨6340659, by rfl⟩ : syracuseStep 16908425 = 12681319) B12681319
theorem B11272283 : Blo 2225435 11272283 := bstep (se 1 (by rfl) ⟨8454212, by rfl⟩ : syracuseStep 11272283 = 16908425) B16908425
theorem B7514855 : Blo 2225435 7514855 := bstep (se 1 (by rfl) ⟨5636141, by rfl⟩ : syracuseStep 7514855 = 11272283) B11272283
theorem B5009903 : Blo 2225435 5009903 := bstep (se 1 (by rfl) ⟨3757427, by rfl⟩ : syracuseStep 5009903 = 7514855) B7514855
theorem B3339935 : Blo 2225435 3339935 := bstep (se 1 (by rfl) ⟨2504951, by rfl⟩ : syracuseStep 3339935 = 5009903) B5009903
theorem B2226623 : Blo 2225435 2226623 := bstep (se 1 (by rfl) ⟨1669967, by rfl⟩ : syracuseStep 2226623 = 3339935) B3339935
theorem B3339941 : Blo 2225435 3339941 := bbase (se 4 (by rfl) ⟨313119, by rfl⟩ : syracuseStep 3339941 = 626239) (by norm_num)
theorem B2226627 : Blo 2225435 2226627 := bstep (se 1 (by rfl) ⟨1669970, by rfl⟩ : syracuseStep 2226627 = 3339941) B3339941
theorem B2818081 : Blo 2225435 2818081 := bbase (se 2 (by rfl) ⟨1056780, by rfl⟩ : syracuseStep 2818081 = 2113561) (by norm_num)
theorem B3757441 : Blo 2225435 3757441 := bstep (se 2 (by rfl) ⟨1409040, by rfl⟩ : syracuseStep 3757441 = 2818081) B2818081
theorem B5009921 : Blo 2225435 5009921 := bstep (se 2 (by rfl) ⟨1878720, by rfl⟩ : syracuseStep 5009921 = 3757441) B3757441
theorem B3339947 : Blo 2225435 3339947 := bstep (se 1 (by rfl) ⟨2504960, by rfl⟩ : syracuseStep 3339947 = 5009921) B5009921
theorem B2226631 : Blo 2225435 2226631 := bstep (se 1 (by rfl) ⟨1669973, by rfl⟩ : syracuseStep 2226631 = 3339947) B3339947
theorem B2504965 : Blo 2225435 2504965 := bbase (se 4 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 2504965 = 469681) (by norm_num)
theorem B3339953 : Blo 2225435 3339953 := bstep (se 2 (by rfl) ⟨1252482, by rfl⟩ : syracuseStep 3339953 = 2504965) B2504965
theorem B2226635 : Blo 2225435 2226635 := bstep (se 1 (by rfl) ⟨1669976, by rfl⟩ : syracuseStep 2226635 = 3339953) B3339953
theorem B2377765 : Blo 2225435 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B3170353 : Blo 2225435 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B4227137 : Blo 2225435 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B2818091 : Blo 2225435 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B7514909 : Blo 2225435 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B5009939 : Blo 2225435 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B3339959 : Blo 2225435 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B2226639 : Blo 2225435 2226639 := bstep (se 1 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 2226639 = 3339959) B3339959
theorem B3339965 : Blo 2225435 3339965 := bbase (se 3 (by rfl) ⟨626243, by rfl⟩ : syracuseStep 3339965 = 1252487) (by norm_num)
theorem B2226643 : Blo 2225435 2226643 := bstep (se 1 (by rfl) ⟨1669982, by rfl⟩ : syracuseStep 2226643 = 3339965) B3339965
theorem B5009957 : Blo 2225435 5009957 := bbase (se 4 (by rfl) ⟨469683, by rfl⟩ : syracuseStep 5009957 = 939367) (by norm_num)
theorem B3339971 : Blo 2225435 3339971 := bstep (se 1 (by rfl) ⟨2504978, by rfl⟩ : syracuseStep 3339971 = 5009957) B5009957
theorem B2226647 : Blo 2225435 2226647 := bstep (se 1 (by rfl) ⟨1669985, by rfl⟩ : syracuseStep 2226647 = 3339971) B3339971
theorem B5636213 : Blo 2225435 5636213 := bbase (se 5 (by rfl) ⟨264197, by rfl⟩ : syracuseStep 5636213 = 528395) (by norm_num)
theorem B3757475 : Blo 2225435 3757475 := bstep (se 1 (by rfl) ⟨2818106, by rfl⟩ : syracuseStep 3757475 = 5636213) B5636213
theorem B2504983 : Blo 2225435 2504983 := bstep (se 1 (by rfl) ⟨1878737, by rfl⟩ : syracuseStep 2504983 = 3757475) B3757475
theorem B3339977 : Blo 2225435 3339977 := bstep (se 2 (by rfl) ⟨1252491, by rfl⟩ : syracuseStep 3339977 = 2504983) B2504983
theorem B2226651 : Blo 2225435 2226651 := bstep (se 1 (by rfl) ⟨1669988, by rfl⟩ : syracuseStep 2226651 = 3339977) B3339977
theorem B10156661 : Blo 2225435 10156661 := bbase (se 5 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 10156661 = 952187) (by norm_num)
theorem B6771107 : Blo 2225435 6771107 := bstep (se 1 (by rfl) ⟨5078330, by rfl⟩ : syracuseStep 6771107 = 10156661) B10156661
theorem B4514071 : Blo 2225435 4514071 := bstep (se 1 (by rfl) ⟨3385553, by rfl⟩ : syracuseStep 4514071 = 6771107) B6771107
theorem B6018761 : Blo 2225435 6018761 := bstep (se 2 (by rfl) ⟨2257035, by rfl⟩ : syracuseStep 6018761 = 4514071) B4514071
theorem B4012507 : Blo 2225435 4012507 := bstep (se 1 (by rfl) ⟨3009380, by rfl⟩ : syracuseStep 4012507 = 6018761) B6018761
theorem B21400037 : Blo 2225435 21400037 := bstep (se 4 (by rfl) ⟨2006253, by rfl⟩ : syracuseStep 21400037 = 4012507) B4012507
theorem B14266691 : Blo 2225435 14266691 := bstep (se 1 (by rfl) ⟨10700018, by rfl⟩ : syracuseStep 14266691 = 21400037) B21400037
theorem B9511127 : Blo 2225435 9511127 := bstep (se 1 (by rfl) ⟨7133345, by rfl⟩ : syracuseStep 9511127 = 14266691) B14266691
theorem B6340751 : Blo 2225435 6340751 := bstep (se 1 (by rfl) ⟨4755563, by rfl⟩ : syracuseStep 6340751 = 9511127) B9511127
theorem B4227167 : Blo 2225435 4227167 := bstep (se 1 (by rfl) ⟨3170375, by rfl⟩ : syracuseStep 4227167 = 6340751) B6340751
theorem B11272445 : Blo 2225435 11272445 := bstep (se 3 (by rfl) ⟨2113583, by rfl⟩ : syracuseStep 11272445 = 4227167) B4227167
theorem B7514963 : Blo 2225435 7514963 := bstep (se 1 (by rfl) ⟨5636222, by rfl⟩ : syracuseStep 7514963 = 11272445) B11272445
theorem B5009975 : Blo 2225435 5009975 := bstep (se 1 (by rfl) ⟨3757481, by rfl⟩ : syracuseStep 5009975 = 7514963) B7514963
theorem B3339983 : Blo 2225435 3339983 := bstep (se 1 (by rfl) ⟨2504987, by rfl⟩ : syracuseStep 3339983 = 5009975) B5009975
theorem B2226655 : Blo 2225435 2226655 := bstep (se 1 (by rfl) ⟨1669991, by rfl⟩ : syracuseStep 2226655 = 3339983) B3339983
theorem B3339989 : Blo 2225435 3339989 := bbase (se 7 (by rfl) ⟨39140, by rfl⟩ : syracuseStep 3339989 = 78281) (by norm_num)
theorem B2226659 : Blo 2225435 2226659 := bstep (se 1 (by rfl) ⟨1669994, by rfl⟩ : syracuseStep 2226659 = 3339989) B3339989
theorem B4755581 : Blo 2225435 4755581 := bbase (se 3 (by rfl) ⟨891671, by rfl⟩ : syracuseStep 4755581 = 1783343) (by norm_num)
theorem B3170387 : Blo 2225435 3170387 := bstep (se 1 (by rfl) ⟨2377790, by rfl⟩ : syracuseStep 3170387 = 4755581) B4755581
theorem B8454365 : Blo 2225435 8454365 := bstep (se 3 (by rfl) ⟨1585193, by rfl⟩ : syracuseStep 8454365 = 3170387) B3170387
theorem B5636243 : Blo 2225435 5636243 := bstep (se 1 (by rfl) ⟨4227182, by rfl⟩ : syracuseStep 5636243 = 8454365) B8454365
theorem B3757495 : Blo 2225435 3757495 := bstep (se 1 (by rfl) ⟨2818121, by rfl⟩ : syracuseStep 3757495 = 5636243) B5636243
theorem B5009993 : Blo 2225435 5009993 := bstep (se 2 (by rfl) ⟨1878747, by rfl⟩ : syracuseStep 5009993 = 3757495) B3757495
theorem B3339995 : Blo 2225435 3339995 := bstep (se 1 (by rfl) ⟨2504996, by rfl⟩ : syracuseStep 3339995 = 5009993) B5009993
theorem B2226663 : Blo 2225435 2226663 := bstep (se 1 (by rfl) ⟨1669997, by rfl⟩ : syracuseStep 2226663 = 3339995) B3339995
theorem B2505001 : Blo 2225435 2505001 := bbase (se 2 (by rfl) ⟨939375, by rfl⟩ : syracuseStep 2505001 = 1878751) (by norm_num)
theorem B3340001 : Blo 2225435 3340001 := bstep (se 2 (by rfl) ⟨1252500, by rfl⟩ : syracuseStep 3340001 = 2505001) B2505001
theorem B2226667 : Blo 2225435 2226667 := bstep (se 1 (by rfl) ⟨1670000, by rfl⟩ : syracuseStep 2226667 = 3340001) B3340001
theorem B3050461 : Blo 2225435 3050461 := bbase (se 3 (by rfl) ⟨571961, by rfl⟩ : syracuseStep 3050461 = 1143923) (by norm_num)
theorem B4067281 : Blo 2225435 4067281 := bstep (se 2 (by rfl) ⟨1525230, by rfl⟩ : syracuseStep 4067281 = 3050461) B3050461
theorem B5423041 : Blo 2225435 5423041 := bstep (se 2 (by rfl) ⟨2033640, by rfl⟩ : syracuseStep 5423041 = 4067281) B4067281
theorem B7230721 : Blo 2225435 7230721 := bstep (se 2 (by rfl) ⟨2711520, by rfl⟩ : syracuseStep 7230721 = 5423041) B5423041
theorem B9640961 : Blo 2225435 9640961 := bstep (se 2 (by rfl) ⟨3615360, by rfl⟩ : syracuseStep 9640961 = 7230721) B7230721
theorem B6427307 : Blo 2225435 6427307 := bstep (se 1 (by rfl) ⟨4820480, by rfl⟩ : syracuseStep 6427307 = 9640961) B9640961
theorem B17139485 : Blo 2225435 17139485 := bstep (se 3 (by rfl) ⟨3213653, by rfl⟩ : syracuseStep 17139485 = 6427307) B6427307
theorem B45705293 : Blo 2225435 45705293 := bstep (se 3 (by rfl) ⟨8569742, by rfl⟩ : syracuseStep 45705293 = 17139485) B17139485
theorem B30470195 : Blo 2225435 30470195 := bstep (se 1 (by rfl) ⟨22852646, by rfl⟩ : syracuseStep 30470195 = 45705293) B45705293
theorem B81253853 : Blo 2225435 81253853 := bstep (se 3 (by rfl) ⟨15235097, by rfl⟩ : syracuseStep 81253853 = 30470195) B30470195
theorem B54169235 : Blo 2225435 54169235 := bstep (se 1 (by rfl) ⟨40626926, by rfl⟩ : syracuseStep 54169235 = 81253853) B81253853
theorem B36112823 : Blo 2225435 36112823 := bstep (se 1 (by rfl) ⟨27084617, by rfl⟩ : syracuseStep 36112823 = 54169235) B54169235
theorem B24075215 : Blo 2225435 24075215 := bstep (se 1 (by rfl) ⟨18056411, by rfl⟩ : syracuseStep 24075215 = 36112823) B36112823
theorem B16050143 : Blo 2225435 16050143 := bstep (se 1 (by rfl) ⟨12037607, by rfl⟩ : syracuseStep 16050143 = 24075215) B24075215
theorem B10700095 : Blo 2225435 10700095 := bstep (se 1 (by rfl) ⟨8025071, by rfl⟩ : syracuseStep 10700095 = 16050143) B16050143
theorem B14266793 : Blo 2225435 14266793 := bstep (se 2 (by rfl) ⟨5350047, by rfl⟩ : syracuseStep 14266793 = 10700095) B10700095
theorem B9511195 : Blo 2225435 9511195 := bstep (se 1 (by rfl) ⟨7133396, by rfl⟩ : syracuseStep 9511195 = 14266793) B14266793
theorem B12681593 : Blo 2225435 12681593 := bstep (se 2 (by rfl) ⟨4755597, by rfl⟩ : syracuseStep 12681593 = 9511195) B9511195
theorem B8454395 : Blo 2225435 8454395 := bstep (se 1 (by rfl) ⟨6340796, by rfl⟩ : syracuseStep 8454395 = 12681593) B12681593
theorem B5636263 : Blo 2225435 5636263 := bstep (se 1 (by rfl) ⟨4227197, by rfl⟩ : syracuseStep 5636263 = 8454395) B8454395
theorem B7515017 : Blo 2225435 7515017 := bstep (se 2 (by rfl) ⟨2818131, by rfl⟩ : syracuseStep 7515017 = 5636263) B5636263
theorem B5010011 : Blo 2225435 5010011 := bstep (se 1 (by rfl) ⟨3757508, by rfl⟩ : syracuseStep 5010011 = 7515017) B7515017
theorem B3340007 : Blo 2225435 3340007 := bstep (se 1 (by rfl) ⟨2505005, by rfl⟩ : syracuseStep 3340007 = 5010011) B5010011
theorem B2226671 : Blo 2225435 2226671 := bstep (se 1 (by rfl) ⟨1670003, by rfl⟩ : syracuseStep 2226671 = 3340007) B3340007
theorem B3340013 : Blo 2225435 3340013 := bbase (se 3 (by rfl) ⟨626252, by rfl⟩ : syracuseStep 3340013 = 1252505) (by norm_num)
theorem B2226675 : Blo 2225435 2226675 := bstep (se 1 (by rfl) ⟨1670006, by rfl⟩ : syracuseStep 2226675 = 3340013) B3340013
theorem B5010029 : Blo 2225435 5010029 := bbase (se 3 (by rfl) ⟨939380, by rfl⟩ : syracuseStep 5010029 = 1878761) (by norm_num)
theorem B3340019 : Blo 2225435 3340019 := bstep (se 1 (by rfl) ⟨2505014, by rfl⟩ : syracuseStep 3340019 = 5010029) B5010029
theorem B2226679 : Blo 2225435 2226679 := bstep (se 1 (by rfl) ⟨1670009, by rfl⟩ : syracuseStep 2226679 = 3340019) B3340019
theorem B4227221 : Blo 2225435 4227221 := bbase (se 6 (by rfl) ⟨99075, by rfl⟩ : syracuseStep 4227221 = 198151) (by norm_num)
theorem B2818147 : Blo 2225435 2818147 := bstep (se 1 (by rfl) ⟨2113610, by rfl⟩ : syracuseStep 2818147 = 4227221) B4227221
theorem B3757529 : Blo 2225435 3757529 := bstep (se 2 (by rfl) ⟨1409073, by rfl⟩ : syracuseStep 3757529 = 2818147) B2818147
theorem B2505019 : Blo 2225435 2505019 := bstep (se 1 (by rfl) ⟨1878764, by rfl⟩ : syracuseStep 2505019 = 3757529) B3757529
theorem B3340025 : Blo 2225435 3340025 := bstep (se 2 (by rfl) ⟨1252509, by rfl⟩ : syracuseStep 3340025 = 2505019) B2505019
theorem B2226683 : Blo 2225435 2226683 := bstep (se 1 (by rfl) ⟨1670012, by rfl⟩ : syracuseStep 2226683 = 3340025) B3340025
theorem B2539201 : Blo 2225435 2539201 := bbase (se 2 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 2539201 = 1904401) (by norm_num)
theorem B3385601 : Blo 2225435 3385601 := bstep (se 2 (by rfl) ⟨1269600, by rfl⟩ : syracuseStep 3385601 = 2539201) B2539201
theorem B36113077 : Blo 2225435 36113077 := bstep (se 5 (by rfl) ⟨1692800, by rfl⟩ : syracuseStep 36113077 = 3385601) B3385601
theorem B48150769 : Blo 2225435 48150769 := bstep (se 2 (by rfl) ⟨18056538, by rfl⟩ : syracuseStep 48150769 = 36113077) B36113077
theorem B64201025 : Blo 2225435 64201025 := bstep (se 2 (by rfl) ⟨24075384, by rfl⟩ : syracuseStep 64201025 = 48150769) B48150769
theorem B42800683 : Blo 2225435 42800683 := bstep (se 1 (by rfl) ⟨32100512, by rfl⟩ : syracuseStep 42800683 = 64201025) B64201025
theorem B57067577 : Blo 2225435 57067577 := bstep (se 2 (by rfl) ⟨21400341, by rfl⟩ : syracuseStep 57067577 = 42800683) B42800683
theorem B38045051 : Blo 2225435 38045051 := bstep (se 1 (by rfl) ⟨28533788, by rfl⟩ : syracuseStep 38045051 = 57067577) B57067577
theorem B25363367 : Blo 2225435 25363367 := bstep (se 1 (by rfl) ⟨19022525, by rfl⟩ : syracuseStep 25363367 = 38045051) B38045051
theorem B16908911 : Blo 2225435 16908911 := bstep (se 1 (by rfl) ⟨12681683, by rfl⟩ : syracuseStep 16908911 = 25363367) B25363367
theorem B11272607 : Blo 2225435 11272607 := bstep (se 1 (by rfl) ⟨8454455, by rfl⟩ : syracuseStep 11272607 = 16908911) B16908911
theorem B7515071 : Blo 2225435 7515071 := bstep (se 1 (by rfl) ⟨5636303, by rfl⟩ : syracuseStep 7515071 = 11272607) B11272607
theorem B5010047 : Blo 2225435 5010047 := bstep (se 1 (by rfl) ⟨3757535, by rfl⟩ : syracuseStep 5010047 = 7515071) B7515071
theorem B3340031 : Blo 2225435 3340031 := bstep (se 1 (by rfl) ⟨2505023, by rfl⟩ : syracuseStep 3340031 = 5010047) B5010047
theorem B2226687 : Blo 2225435 2226687 := bstep (se 1 (by rfl) ⟨1670015, by rfl⟩ : syracuseStep 2226687 = 3340031) B3340031
theorem B3340037 : Blo 2225435 3340037 := bbase (se 4 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 3340037 = 626257) (by norm_num)
theorem B2226691 : Blo 2225435 2226691 := bstep (se 1 (by rfl) ⟨1670018, by rfl⟩ : syracuseStep 2226691 = 3340037) B3340037
theorem B3757549 : Blo 2225435 3757549 := bbase (se 3 (by rfl) ⟨704540, by rfl⟩ : syracuseStep 3757549 = 1409081) (by norm_num)
theorem B5010065 : Blo 2225435 5010065 := bstep (se 2 (by rfl) ⟨1878774, by rfl⟩ : syracuseStep 5010065 = 3757549) B3757549
theorem B3340043 : Blo 2225435 3340043 := bstep (se 1 (by rfl) ⟨2505032, by rfl⟩ : syracuseStep 3340043 = 5010065) B5010065
theorem B2226695 : Blo 2225435 2226695 := bstep (se 1 (by rfl) ⟨1670021, by rfl⟩ : syracuseStep 2226695 = 3340043) B3340043
theorem B2505037 : Blo 2225435 2505037 := bbase (se 3 (by rfl) ⟨469694, by rfl⟩ : syracuseStep 2505037 = 939389) (by norm_num)
theorem B3340049 : Blo 2225435 3340049 := bstep (se 2 (by rfl) ⟨1252518, by rfl⟩ : syracuseStep 3340049 = 2505037) B2505037
theorem B2226699 : Blo 2225435 2226699 := bstep (se 1 (by rfl) ⟨1670024, by rfl⟩ : syracuseStep 2226699 = 3340049) B3340049
theorem B7515125 : Blo 2225435 7515125 := bbase (se 5 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 7515125 = 704543) (by norm_num)
theorem B5010083 : Blo 2225435 5010083 := bstep (se 1 (by rfl) ⟨3757562, by rfl⟩ : syracuseStep 5010083 = 7515125) B7515125
theorem B3340055 : Blo 2225435 3340055 := bstep (se 1 (by rfl) ⟨2505041, by rfl⟩ : syracuseStep 3340055 = 5010083) B5010083
theorem B2226703 : Blo 2225435 2226703 := bstep (se 1 (by rfl) ⟨1670027, by rfl⟩ : syracuseStep 2226703 = 3340055) B3340055
theorem B3340061 : Blo 2225435 3340061 := bbase (se 3 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 3340061 = 1252523) (by norm_num)
theorem B2226707 : Blo 2225435 2226707 := bstep (se 1 (by rfl) ⟨1670030, by rfl⟩ : syracuseStep 2226707 = 3340061) B3340061
theorem B5010101 : Blo 2225435 5010101 := bbase (se 5 (by rfl) ⟨234848, by rfl⟩ : syracuseStep 5010101 = 469697) (by norm_num)
theorem B3340067 : Blo 2225435 3340067 := bstep (se 1 (by rfl) ⟨2505050, by rfl⟩ : syracuseStep 3340067 = 5010101) B5010101
theorem B2226711 : Blo 2225435 2226711 := bstep (se 1 (by rfl) ⟨1670033, by rfl⟩ : syracuseStep 2226711 = 3340067) B3340067
theorem B12681845 : Blo 2225435 12681845 := bbase (se 5 (by rfl) ⟨594461, by rfl⟩ : syracuseStep 12681845 = 1188923) (by norm_num)
theorem B8454563 : Blo 2225435 8454563 := bstep (se 1 (by rfl) ⟨6340922, by rfl⟩ : syracuseStep 8454563 = 12681845) B12681845
theorem B5636375 : Blo 2225435 5636375 := bstep (se 1 (by rfl) ⟨4227281, by rfl⟩ : syracuseStep 5636375 = 8454563) B8454563
theorem B3757583 : Blo 2225435 3757583 := bstep (se 1 (by rfl) ⟨2818187, by rfl⟩ : syracuseStep 3757583 = 5636375) B5636375
theorem B2505055 : Blo 2225435 2505055 := bstep (se 1 (by rfl) ⟨1878791, by rfl⟩ : syracuseStep 2505055 = 3757583) B3757583
theorem B3340073 : Blo 2225435 3340073 := bstep (se 2 (by rfl) ⟨1252527, by rfl⟩ : syracuseStep 3340073 = 2505055) B2505055
theorem B2226715 : Blo 2225435 2226715 := bstep (se 1 (by rfl) ⟨1670036, by rfl⟩ : syracuseStep 2226715 = 3340073) B3340073
theorem B6340933 : Blo 2225435 6340933 := bbase (se 4 (by rfl) ⟨594462, by rfl⟩ : syracuseStep 6340933 = 1188925) (by norm_num)
theorem B8454577 : Blo 2225435 8454577 := bstep (se 2 (by rfl) ⟨3170466, by rfl⟩ : syracuseStep 8454577 = 6340933) B6340933
theorem B11272769 : Blo 2225435 11272769 := bstep (se 2 (by rfl) ⟨4227288, by rfl⟩ : syracuseStep 11272769 = 8454577) B8454577
theorem B7515179 : Blo 2225435 7515179 := bstep (se 1 (by rfl) ⟨5636384, by rfl⟩ : syracuseStep 7515179 = 11272769) B11272769
theorem B5010119 : Blo 2225435 5010119 := bstep (se 1 (by rfl) ⟨3757589, by rfl⟩ : syracuseStep 5010119 = 7515179) B7515179
theorem B3340079 : Blo 2225435 3340079 := bstep (se 1 (by rfl) ⟨2505059, by rfl⟩ : syracuseStep 3340079 = 5010119) B5010119
theorem B2226719 : Blo 2225435 2226719 := bstep (se 1 (by rfl) ⟨1670039, by rfl⟩ : syracuseStep 2226719 = 3340079) B3340079
theorem B3340085 : Blo 2225435 3340085 := bbase (se 5 (by rfl) ⟨156566, by rfl⟩ : syracuseStep 3340085 = 313133) (by norm_num)
theorem B2226723 : Blo 2225435 2226723 := bstep (se 1 (by rfl) ⟨1670042, by rfl⟩ : syracuseStep 2226723 = 3340085) B3340085
theorem B5636405 : Blo 2225435 5636405 := bbase (se 5 (by rfl) ⟨264206, by rfl⟩ : syracuseStep 5636405 = 528413) (by norm_num)
theorem B3757603 : Blo 2225435 3757603 := bstep (se 1 (by rfl) ⟨2818202, by rfl⟩ : syracuseStep 3757603 = 5636405) B5636405
theorem B5010137 : Blo 2225435 5010137 := bstep (se 2 (by rfl) ⟨1878801, by rfl⟩ : syracuseStep 5010137 = 3757603) B3757603
theorem B3340091 : Blo 2225435 3340091 := bstep (se 1 (by rfl) ⟨2505068, by rfl⟩ : syracuseStep 3340091 = 5010137) B5010137
theorem B2226727 : Blo 2225435 2226727 := bstep (se 1 (by rfl) ⟨1670045, by rfl⟩ : syracuseStep 2226727 = 3340091) B3340091
theorem B2505073 : Blo 2225435 2505073 := bbase (se 2 (by rfl) ⟨939402, by rfl⟩ : syracuseStep 2505073 = 1878805) (by norm_num)
theorem B3340097 : Blo 2225435 3340097 := bstep (se 2 (by rfl) ⟨1252536, by rfl⟩ : syracuseStep 3340097 = 2505073) B2505073
theorem B2226731 : Blo 2225435 2226731 := bstep (se 1 (by rfl) ⟨1670048, by rfl⟩ : syracuseStep 2226731 = 3340097) B3340097
theorem B2675101 : Blo 2225435 2675101 := bbase (se 3 (by rfl) ⟨501581, by rfl⟩ : syracuseStep 2675101 = 1003163) (by norm_num)
theorem B3566801 : Blo 2225435 3566801 := bstep (se 2 (by rfl) ⟨1337550, by rfl⟩ : syracuseStep 3566801 = 2675101) B2675101
theorem B9511469 : Blo 2225435 9511469 := bstep (se 3 (by rfl) ⟨1783400, by rfl⟩ : syracuseStep 9511469 = 3566801) B3566801
theorem B6340979 : Blo 2225435 6340979 := bstep (se 1 (by rfl) ⟨4755734, by rfl⟩ : syracuseStep 6340979 = 9511469) B9511469
theorem B4227319 : Blo 2225435 4227319 := bstep (se 1 (by rfl) ⟨3170489, by rfl⟩ : syracuseStep 4227319 = 6340979) B6340979
theorem B5636425 : Blo 2225435 5636425 := bstep (se 2 (by rfl) ⟨2113659, by rfl⟩ : syracuseStep 5636425 = 4227319) B4227319
theorem B7515233 : Blo 2225435 7515233 := bstep (se 2 (by rfl) ⟨2818212, by rfl⟩ : syracuseStep 7515233 = 5636425) B5636425
theorem B5010155 : Blo 2225435 5010155 := bstep (se 1 (by rfl) ⟨3757616, by rfl⟩ : syracuseStep 5010155 = 7515233) B7515233
theorem B3340103 : Blo 2225435 3340103 := bstep (se 1 (by rfl) ⟨2505077, by rfl⟩ : syracuseStep 3340103 = 5010155) B5010155
theorem B2226735 : Blo 2225435 2226735 := bstep (se 1 (by rfl) ⟨1670051, by rfl⟩ : syracuseStep 2226735 = 3340103) B3340103
theorem B3340109 : Blo 2225435 3340109 := bbase (se 3 (by rfl) ⟨626270, by rfl⟩ : syracuseStep 3340109 = 1252541) (by norm_num)
theorem B2226739 : Blo 2225435 2226739 := bstep (se 1 (by rfl) ⟨1670054, by rfl⟩ : syracuseStep 2226739 = 3340109) B3340109
theorem B5010173 : Blo 2225435 5010173 := bbase (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) (by norm_num)
theorem B3340115 : Blo 2225435 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B2226743 : Blo 2225435 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B3757637 : Blo 2225435 3757637 := bbase (se 4 (by rfl) ⟨352278, by rfl⟩ : syracuseStep 3757637 = 704557) (by norm_num)
theorem B2505091 : Blo 2225435 2505091 := bstep (se 1 (by rfl) ⟨1878818, by rfl⟩ : syracuseStep 2505091 = 3757637) B3757637
theorem B3340121 : Blo 2225435 3340121 := bstep (se 2 (by rfl) ⟨1252545, by rfl⟩ : syracuseStep 3340121 = 2505091) B2505091
theorem B2226747 : Blo 2225435 2226747 := bstep (se 1 (by rfl) ⟨1670060, by rfl⟩ : syracuseStep 2226747 = 3340121) B3340121
theorem B16909397 : Blo 2225435 16909397 := bbase (se 8 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 16909397 = 198157) (by norm_num)
theorem B11272931 : Blo 2225435 11272931 := bstep (se 1 (by rfl) ⟨8454698, by rfl⟩ : syracuseStep 11272931 = 16909397) B16909397
theorem B7515287 : Blo 2225435 7515287 := bstep (se 1 (by rfl) ⟨5636465, by rfl⟩ : syracuseStep 7515287 = 11272931) B11272931
theorem B5010191 : Blo 2225435 5010191 := bstep (se 1 (by rfl) ⟨3757643, by rfl⟩ : syracuseStep 5010191 = 7515287) B7515287
theorem B3340127 : Blo 2225435 3340127 := bstep (se 1 (by rfl) ⟨2505095, by rfl⟩ : syracuseStep 3340127 = 5010191) B5010191
theorem B2226751 : Blo 2225435 2226751 := bstep (se 1 (by rfl) ⟨1670063, by rfl⟩ : syracuseStep 2226751 = 3340127) B3340127
theorem B3340133 : Blo 2225435 3340133 := bbase (se 4 (by rfl) ⟨313137, by rfl⟩ : syracuseStep 3340133 = 626275) (by norm_num)
theorem B2226755 : Blo 2225435 2226755 := bstep (se 1 (by rfl) ⟨1670066, by rfl⟩ : syracuseStep 2226755 = 3340133) B3340133
theorem B4227365 : Blo 2225435 4227365 := bbase (se 4 (by rfl) ⟨396315, by rfl⟩ : syracuseStep 4227365 = 792631) (by norm_num)
theorem B2818243 : Blo 2225435 2818243 := bstep (se 1 (by rfl) ⟨2113682, by rfl⟩ : syracuseStep 2818243 = 4227365) B4227365
theorem B3757657 : Blo 2225435 3757657 := bstep (se 2 (by rfl) ⟨1409121, by rfl⟩ : syracuseStep 3757657 = 2818243) B2818243
theorem B5010209 : Blo 2225435 5010209 := bstep (se 2 (by rfl) ⟨1878828, by rfl⟩ : syracuseStep 5010209 = 3757657) B3757657
theorem B3340139 : Blo 2225435 3340139 := bstep (se 1 (by rfl) ⟨2505104, by rfl⟩ : syracuseStep 3340139 = 5010209) B5010209
theorem B2226759 : Blo 2225435 2226759 := bstep (se 1 (by rfl) ⟨1670069, by rfl⟩ : syracuseStep 2226759 = 3340139) B3340139
theorem B2505109 : Blo 2225435 2505109 := bbase (se 6 (by rfl) ⟨58713, by rfl⟩ : syracuseStep 2505109 = 117427) (by norm_num)
theorem B3340145 : Blo 2225435 3340145 := bstep (se 2 (by rfl) ⟨1252554, by rfl⟩ : syracuseStep 3340145 = 2505109) B2505109
theorem B2226763 : Blo 2225435 2226763 := bstep (se 1 (by rfl) ⟨1670072, by rfl⟩ : syracuseStep 2226763 = 3340145) B3340145
theorem B2818253 : Blo 2225435 2818253 := bbase (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) (by norm_num)
theorem B7515341 : Blo 2225435 7515341 := bstep (se 3 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 7515341 = 2818253) B2818253
theorem B5010227 : Blo 2225435 5010227 := bstep (se 1 (by rfl) ⟨3757670, by rfl⟩ : syracuseStep 5010227 = 7515341) B7515341
theorem B3340151 : Blo 2225435 3340151 := bstep (se 1 (by rfl) ⟨2505113, by rfl⟩ : syracuseStep 3340151 = 5010227) B5010227
theorem B2226767 : Blo 2225435 2226767 := bstep (se 1 (by rfl) ⟨1670075, by rfl⟩ : syracuseStep 2226767 = 3340151) B3340151
theorem B3340157 : Blo 2225435 3340157 := bbase (se 3 (by rfl) ⟨626279, by rfl⟩ : syracuseStep 3340157 = 1252559) (by norm_num)
theorem B2226771 : Blo 2225435 2226771 := bstep (se 1 (by rfl) ⟨1670078, by rfl⟩ : syracuseStep 2226771 = 3340157) B3340157
theorem B5010245 : Blo 2225435 5010245 := bbase (se 4 (by rfl) ⟨469710, by rfl⟩ : syracuseStep 5010245 = 939421) (by norm_num)
theorem B3340163 : Blo 2225435 3340163 := bstep (se 1 (by rfl) ⟨2505122, by rfl⟩ : syracuseStep 3340163 = 5010245) B5010245
theorem B2226775 : Blo 2225435 2226775 := bstep (se 1 (by rfl) ⟨1670081, by rfl⟩ : syracuseStep 2226775 = 3340163) B3340163
theorem B4755829 : Blo 2225435 4755829 := bbase (se 5 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 4755829 = 445859) (by norm_num)
theorem B6341105 : Blo 2225435 6341105 := bstep (se 2 (by rfl) ⟨2377914, by rfl⟩ : syracuseStep 6341105 = 4755829) B4755829
theorem B4227403 : Blo 2225435 4227403 := bstep (se 1 (by rfl) ⟨3170552, by rfl⟩ : syracuseStep 4227403 = 6341105) B6341105
theorem B5636537 : Blo 2225435 5636537 := bstep (se 2 (by rfl) ⟨2113701, by rfl⟩ : syracuseStep 5636537 = 4227403) B4227403
theorem B3757691 : Blo 2225435 3757691 := bstep (se 1 (by rfl) ⟨2818268, by rfl⟩ : syracuseStep 3757691 = 5636537) B5636537
theorem B2505127 : Blo 2225435 2505127 := bstep (se 1 (by rfl) ⟨1878845, by rfl⟩ : syracuseStep 2505127 = 3757691) B3757691
theorem B3340169 : Blo 2225435 3340169 := bstep (se 2 (by rfl) ⟨1252563, by rfl⟩ : syracuseStep 3340169 = 2505127) B2505127
theorem B2226779 : Blo 2225435 2226779 := bstep (se 1 (by rfl) ⟨1670084, by rfl⟩ : syracuseStep 2226779 = 3340169) B3340169
theorem B11273093 : Blo 2225435 11273093 := bbase (se 4 (by rfl) ⟨1056852, by rfl⟩ : syracuseStep 11273093 = 2113705) (by norm_num)
theorem B7515395 : Blo 2225435 7515395 := bstep (se 1 (by rfl) ⟨5636546, by rfl⟩ : syracuseStep 7515395 = 11273093) B11273093
theorem B5010263 : Blo 2225435 5010263 := bstep (se 1 (by rfl) ⟨3757697, by rfl⟩ : syracuseStep 5010263 = 7515395) B7515395
theorem B3340175 : Blo 2225435 3340175 := bstep (se 1 (by rfl) ⟨2505131, by rfl⟩ : syracuseStep 3340175 = 5010263) B5010263
theorem B2226783 : Blo 2225435 2226783 := bstep (se 1 (by rfl) ⟨1670087, by rfl⟩ : syracuseStep 2226783 = 3340175) B3340175
theorem B3340181 : Blo 2225435 3340181 := bbase (se 6 (by rfl) ⟨78285, by rfl⟩ : syracuseStep 3340181 = 156571) (by norm_num)
theorem B2226787 : Blo 2225435 2226787 := bstep (se 1 (by rfl) ⟨1670090, by rfl⟩ : syracuseStep 2226787 = 3340181) B3340181
theorem B3009565 : Blo 2225435 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B4012753 : Blo 2225435 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B5350337 : Blo 2225435 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B3566891 : Blo 2225435 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B2377927 : Blo 2225435 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B12682277 : Blo 2225435 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B8454851 : Blo 2225435 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B5636567 : Blo 2225435 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B3757711 : Blo 2225435 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B5010281 : Blo 2225435 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B3340187 : Blo 2225435 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B2226791 : Blo 2225435 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B2505145 : Blo 2225435 2505145 := bbase (se 2 (by rfl) ⟨939429, by rfl⟩ : syracuseStep 2505145 = 1878859) (by norm_num)
theorem B3340193 : Blo 2225435 3340193 := bstep (se 2 (by rfl) ⟨1252572, by rfl⟩ : syracuseStep 3340193 = 2505145) B2505145
theorem B2226795 : Blo 2225435 2226795 := bstep (se 1 (by rfl) ⟨1670096, by rfl⟩ : syracuseStep 2226795 = 3340193) B3340193
theorem B2711677 : Blo 2225435 2711677 := bbase (se 3 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 2711677 = 1016879) (by norm_num)
theorem B3615569 : Blo 2225435 3615569 := bstep (se 2 (by rfl) ⟨1355838, by rfl⟩ : syracuseStep 3615569 = 2711677) B2711677
theorem B2410379 : Blo 2225435 2410379 := bstep (se 1 (by rfl) ⟨1807784, by rfl⟩ : syracuseStep 2410379 = 3615569) B3615569
theorem B25710709 : Blo 2225435 25710709 := bstep (se 5 (by rfl) ⟨1205189, by rfl⟩ : syracuseStep 25710709 = 2410379) B2410379
theorem B34280945 : Blo 2225435 34280945 := bstep (se 2 (by rfl) ⟨12855354, by rfl⟩ : syracuseStep 34280945 = 25710709) B25710709
theorem B22853963 : Blo 2225435 22853963 := bstep (se 1 (by rfl) ⟨17140472, by rfl⟩ : syracuseStep 22853963 = 34280945) B34280945
theorem B15235975 : Blo 2225435 15235975 := bstep (se 1 (by rfl) ⟨11426981, by rfl⟩ : syracuseStep 15235975 = 22853963) B22853963
theorem B20314633 : Blo 2225435 20314633 := bstep (se 2 (by rfl) ⟨7617987, by rfl⟩ : syracuseStep 20314633 = 15235975) B15235975
theorem B27086177 : Blo 2225435 27086177 := bstep (se 2 (by rfl) ⟨10157316, by rfl⟩ : syracuseStep 27086177 = 20314633) B20314633
theorem B18057451 : Blo 2225435 18057451 := bstep (se 1 (by rfl) ⟨13543088, by rfl⟩ : syracuseStep 18057451 = 27086177) B27086177
theorem B24076601 : Blo 2225435 24076601 := bstep (se 2 (by rfl) ⟨9028725, by rfl⟩ : syracuseStep 24076601 = 18057451) B18057451
theorem B16051067 : Blo 2225435 16051067 := bstep (se 1 (by rfl) ⟨12038300, by rfl⟩ : syracuseStep 16051067 = 24076601) B24076601
theorem B10700711 : Blo 2225435 10700711 := bstep (se 1 (by rfl) ⟨8025533, by rfl⟩ : syracuseStep 10700711 = 16051067) B16051067
theorem B7133807 : Blo 2225435 7133807 := bstep (se 1 (by rfl) ⟨5350355, by rfl⟩ : syracuseStep 7133807 = 10700711) B10700711
theorem B4755871 : Blo 2225435 4755871 := bstep (se 1 (by rfl) ⟨3566903, by rfl⟩ : syracuseStep 4755871 = 7133807) B7133807
theorem B6341161 : Blo 2225435 6341161 := bstep (se 2 (by rfl) ⟨2377935, by rfl⟩ : syracuseStep 6341161 = 4755871) B4755871
theorem B8454881 : Blo 2225435 8454881 := bstep (se 2 (by rfl) ⟨3170580, by rfl⟩ : syracuseStep 8454881 = 6341161) B6341161
theorem B5636587 : Blo 2225435 5636587 := bstep (se 1 (by rfl) ⟨4227440, by rfl⟩ : syracuseStep 5636587 = 8454881) B8454881
theorem B7515449 : Blo 2225435 7515449 := bstep (se 2 (by rfl) ⟨2818293, by rfl⟩ : syracuseStep 7515449 = 5636587) B5636587
theorem B5010299 : Blo 2225435 5010299 := bstep (se 1 (by rfl) ⟨3757724, by rfl⟩ : syracuseStep 5010299 = 7515449) B7515449
theorem B3340199 : Blo 2225435 3340199 := bstep (se 1 (by rfl) ⟨2505149, by rfl⟩ : syracuseStep 3340199 = 5010299) B5010299
theorem B2226799 : Blo 2225435 2226799 := bstep (se 1 (by rfl) ⟨1670099, by rfl⟩ : syracuseStep 2226799 = 3340199) B3340199
theorem B3340205 : Blo 2225435 3340205 := bbase (se 3 (by rfl) ⟨626288, by rfl⟩ : syracuseStep 3340205 = 1252577) (by norm_num)
theorem B2226803 : Blo 2225435 2226803 := bstep (se 1 (by rfl) ⟨1670102, by rfl⟩ : syracuseStep 2226803 = 3340205) B3340205
theorem B5010317 : Blo 2225435 5010317 := bbase (se 3 (by rfl) ⟨939434, by rfl⟩ : syracuseStep 5010317 = 1878869) (by norm_num)
theorem B3340211 : Blo 2225435 3340211 := bstep (se 1 (by rfl) ⟨2505158, by rfl⟩ : syracuseStep 3340211 = 5010317) B5010317
theorem B2226807 : Blo 2225435 2226807 := bstep (se 1 (by rfl) ⟨1670105, by rfl⟩ : syracuseStep 2226807 = 3340211) B3340211
theorem B2818309 : Blo 2225435 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B3757745 : Blo 2225435 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B2505163 : Blo 2225435 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B3340217 : Blo 2225435 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B2226811 : Blo 2225435 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B4575989 : Blo 2225435 4575989 := bbase (se 5 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 4575989 = 428999) (by norm_num)
theorem B3050659 : Blo 2225435 3050659 := bstep (se 1 (by rfl) ⟨2287994, by rfl⟩ : syracuseStep 3050659 = 4575989) B4575989
theorem B4067545 : Blo 2225435 4067545 := bstep (se 2 (by rfl) ⟨1525329, by rfl⟩ : syracuseStep 4067545 = 3050659) B3050659
theorem B5423393 : Blo 2225435 5423393 := bstep (se 2 (by rfl) ⟨2033772, by rfl⟩ : syracuseStep 5423393 = 4067545) B4067545
theorem B14462381 : Blo 2225435 14462381 := bstep (se 3 (by rfl) ⟨2711696, by rfl⟩ : syracuseStep 14462381 = 5423393) B5423393
theorem B9641587 : Blo 2225435 9641587 := bstep (se 1 (by rfl) ⟨7231190, by rfl⟩ : syracuseStep 9641587 = 14462381) B14462381
theorem B12855449 : Blo 2225435 12855449 := bstep (se 2 (by rfl) ⟨4820793, by rfl⟩ : syracuseStep 12855449 = 9641587) B9641587
theorem B8570299 : Blo 2225435 8570299 := bstep (se 1 (by rfl) ⟨6427724, by rfl⟩ : syracuseStep 8570299 = 12855449) B12855449
theorem B11427065 : Blo 2225435 11427065 := bstep (se 2 (by rfl) ⟨4285149, by rfl⟩ : syracuseStep 11427065 = 8570299) B8570299
theorem B7618043 : Blo 2225435 7618043 := bstep (se 1 (by rfl) ⟨5713532, by rfl⟩ : syracuseStep 7618043 = 11427065) B11427065
theorem B5078695 : Blo 2225435 5078695 := bstep (se 1 (by rfl) ⟨3809021, by rfl⟩ : syracuseStep 5078695 = 7618043) B7618043
theorem B6771593 : Blo 2225435 6771593 := bstep (se 2 (by rfl) ⟨2539347, by rfl⟩ : syracuseStep 6771593 = 5078695) B5078695
theorem B4514395 : Blo 2225435 4514395 := bstep (se 1 (by rfl) ⟨3385796, by rfl⟩ : syracuseStep 4514395 = 6771593) B6771593
theorem B6019193 : Blo 2225435 6019193 := bstep (se 2 (by rfl) ⟨2257197, by rfl⟩ : syracuseStep 6019193 = 4514395) B4514395
theorem B4012795 : Blo 2225435 4012795 := bstep (se 1 (by rfl) ⟨3009596, by rfl⟩ : syracuseStep 4012795 = 6019193) B6019193
theorem B5350393 : Blo 2225435 5350393 := bstep (se 2 (by rfl) ⟨2006397, by rfl⟩ : syracuseStep 5350393 = 4012795) B4012795
theorem B28535429 : Blo 2225435 28535429 := bstep (se 4 (by rfl) ⟨2675196, by rfl⟩ : syracuseStep 28535429 = 5350393) B5350393
theorem B19023619 : Blo 2225435 19023619 := bstep (se 1 (by rfl) ⟨14267714, by rfl⟩ : syracuseStep 19023619 = 28535429) B28535429
theorem B25364825 : Blo 2225435 25364825 := bstep (se 2 (by rfl) ⟨9511809, by rfl⟩ : syracuseStep 25364825 = 19023619) B19023619
theorem B16909883 : Blo 2225435 16909883 := bstep (se 1 (by rfl) ⟨12682412, by rfl⟩ : syracuseStep 16909883 = 25364825) B25364825
theorem B11273255 : Blo 2225435 11273255 := bstep (se 1 (by rfl) ⟨8454941, by rfl⟩ : syracuseStep 11273255 = 16909883) B16909883
theorem B7515503 : Blo 2225435 7515503 := bstep (se 1 (by rfl) ⟨5636627, by rfl⟩ : syracuseStep 7515503 = 11273255) B11273255
theorem B5010335 : Blo 2225435 5010335 := bstep (se 1 (by rfl) ⟨3757751, by rfl⟩ : syracuseStep 5010335 = 7515503) B7515503
theorem B3340223 : Blo 2225435 3340223 := bstep (se 1 (by rfl) ⟨2505167, by rfl⟩ : syracuseStep 3340223 = 5010335) B5010335
theorem B2226815 : Blo 2225435 2226815 := bstep (se 1 (by rfl) ⟨1670111, by rfl⟩ : syracuseStep 2226815 = 3340223) B3340223
theorem B3340229 : Blo 2225435 3340229 := bbase (se 4 (by rfl) ⟨313146, by rfl⟩ : syracuseStep 3340229 = 626293) (by norm_num)
theorem B2226819 : Blo 2225435 2226819 := bstep (se 1 (by rfl) ⟨1670114, by rfl⟩ : syracuseStep 2226819 = 3340229) B3340229
theorem B3757765 : Blo 2225435 3757765 := bbase (se 4 (by rfl) ⟨352290, by rfl⟩ : syracuseStep 3757765 = 704581) (by norm_num)
theorem B5010353 : Blo 2225435 5010353 := bstep (se 2 (by rfl) ⟨1878882, by rfl⟩ : syracuseStep 5010353 = 3757765) B3757765
theorem B3340235 : Blo 2225435 3340235 := bstep (se 1 (by rfl) ⟨2505176, by rfl⟩ : syracuseStep 3340235 = 5010353) B5010353
theorem B2226823 : Blo 2225435 2226823 := bstep (se 1 (by rfl) ⟨1670117, by rfl⟩ : syracuseStep 2226823 = 3340235) B3340235
theorem B2505181 : Blo 2225435 2505181 := bbase (se 3 (by rfl) ⟨469721, by rfl⟩ : syracuseStep 2505181 = 939443) (by norm_num)
theorem B3340241 : Blo 2225435 3340241 := bstep (se 2 (by rfl) ⟨1252590, by rfl⟩ : syracuseStep 3340241 = 2505181) B2505181
theorem B2226827 : Blo 2225435 2226827 := bstep (se 1 (by rfl) ⟨1670120, by rfl⟩ : syracuseStep 2226827 = 3340241) B3340241
theorem B7515557 : Blo 2225435 7515557 := bbase (se 4 (by rfl) ⟨704583, by rfl⟩ : syracuseStep 7515557 = 1409167) (by norm_num)
theorem B5010371 : Blo 2225435 5010371 := bstep (se 1 (by rfl) ⟨3757778, by rfl⟩ : syracuseStep 5010371 = 7515557) B7515557
theorem B3340247 : Blo 2225435 3340247 := bstep (se 1 (by rfl) ⟨2505185, by rfl⟩ : syracuseStep 3340247 = 5010371) B5010371
theorem B2226831 : Blo 2225435 2226831 := bstep (se 1 (by rfl) ⟨1670123, by rfl⟩ : syracuseStep 2226831 = 3340247) B3340247
theorem B3340253 : Blo 2225435 3340253 := bbase (se 3 (by rfl) ⟨626297, by rfl⟩ : syracuseStep 3340253 = 1252595) (by norm_num)
theorem B2226835 : Blo 2225435 2226835 := bstep (se 1 (by rfl) ⟨1670126, by rfl⟩ : syracuseStep 2226835 = 3340253) B3340253
theorem B5010389 : Blo 2225435 5010389 := bbase (se 7 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 5010389 = 117431) (by norm_num)
theorem B3340259 : Blo 2225435 3340259 := bstep (se 1 (by rfl) ⟨2505194, by rfl⟩ : syracuseStep 3340259 = 5010389) B5010389
theorem B2226839 : Blo 2225435 2226839 := bstep (se 1 (by rfl) ⟨1670129, by rfl⟩ : syracuseStep 2226839 = 3340259) B3340259
theorem B21693845 : Blo 2225435 21693845 := bbase (se 6 (by rfl) ⟨508449, by rfl⟩ : syracuseStep 21693845 = 1016899) (by norm_num)
theorem B14462563 : Blo 2225435 14462563 := bstep (se 1 (by rfl) ⟨10846922, by rfl⟩ : syracuseStep 14462563 = 21693845) B21693845
theorem B19283417 : Blo 2225435 19283417 := bstep (se 2 (by rfl) ⟨7231281, by rfl⟩ : syracuseStep 19283417 = 14462563) B14462563
theorem B12855611 : Blo 2225435 12855611 := bstep (se 1 (by rfl) ⟨9641708, by rfl⟩ : syracuseStep 12855611 = 19283417) B19283417
theorem B8570407 : Blo 2225435 8570407 := bstep (se 1 (by rfl) ⟨6427805, by rfl⟩ : syracuseStep 8570407 = 12855611) B12855611
theorem B11427209 : Blo 2225435 11427209 := bstep (se 2 (by rfl) ⟨4285203, by rfl⟩ : syracuseStep 11427209 = 8570407) B8570407
theorem B7618139 : Blo 2225435 7618139 := bstep (se 1 (by rfl) ⟨5713604, by rfl⟩ : syracuseStep 7618139 = 11427209) B11427209
theorem B5078759 : Blo 2225435 5078759 := bstep (se 1 (by rfl) ⟨3809069, by rfl⟩ : syracuseStep 5078759 = 7618139) B7618139
theorem B13543357 : Blo 2225435 13543357 := bstep (se 3 (by rfl) ⟨2539379, by rfl⟩ : syracuseStep 13543357 = 5078759) B5078759
theorem B18057809 : Blo 2225435 18057809 := bstep (se 2 (by rfl) ⟨6771678, by rfl⟩ : syracuseStep 18057809 = 13543357) B13543357
theorem B12038539 : Blo 2225435 12038539 := bstep (se 1 (by rfl) ⟨9028904, by rfl⟩ : syracuseStep 12038539 = 18057809) B18057809
theorem B16051385 : Blo 2225435 16051385 := bstep (se 2 (by rfl) ⟨6019269, by rfl⟩ : syracuseStep 16051385 = 12038539) B12038539
theorem B10700923 : Blo 2225435 10700923 := bstep (se 1 (by rfl) ⟨8025692, by rfl⟩ : syracuseStep 10700923 = 16051385) B16051385
theorem B14267897 : Blo 2225435 14267897 := bstep (se 2 (by rfl) ⟨5350461, by rfl⟩ : syracuseStep 14267897 = 10700923) B10700923
theorem B9511931 : Blo 2225435 9511931 := bstep (se 1 (by rfl) ⟨7133948, by rfl⟩ : syracuseStep 9511931 = 14267897) B14267897
theorem B6341287 : Blo 2225435 6341287 := bstep (se 1 (by rfl) ⟨4755965, by rfl⟩ : syracuseStep 6341287 = 9511931) B9511931
theorem B8455049 : Blo 2225435 8455049 := bstep (se 2 (by rfl) ⟨3170643, by rfl⟩ : syracuseStep 8455049 = 6341287) B6341287
theorem B5636699 : Blo 2225435 5636699 := bstep (se 1 (by rfl) ⟨4227524, by rfl⟩ : syracuseStep 5636699 = 8455049) B8455049
theorem B3757799 : Blo 2225435 3757799 := bstep (se 1 (by rfl) ⟨2818349, by rfl⟩ : syracuseStep 3757799 = 5636699) B5636699
theorem B2505199 : Blo 2225435 2505199 := bstep (se 1 (by rfl) ⟨1878899, by rfl⟩ : syracuseStep 2505199 = 3757799) B3757799
theorem B3340265 : Blo 2225435 3340265 := bstep (se 2 (by rfl) ⟨1252599, by rfl⟩ : syracuseStep 3340265 = 2505199) B2505199
theorem B2226843 : Blo 2225435 2226843 := bstep (se 1 (by rfl) ⟨1670132, by rfl⟩ : syracuseStep 2226843 = 3340265) B3340265
theorem B19023893 : Blo 2225435 19023893 := bbase (se 6 (by rfl) ⟨445872, by rfl⟩ : syracuseStep 19023893 = 891745) (by norm_num)
theorem B12682595 : Blo 2225435 12682595 := bstep (se 1 (by rfl) ⟨9511946, by rfl⟩ : syracuseStep 12682595 = 19023893) B19023893
theorem B8455063 : Blo 2225435 8455063 := bstep (se 1 (by rfl) ⟨6341297, by rfl⟩ : syracuseStep 8455063 = 12682595) B12682595
theorem B11273417 : Blo 2225435 11273417 := bstep (se 2 (by rfl) ⟨4227531, by rfl⟩ : syracuseStep 11273417 = 8455063) B8455063
theorem B7515611 : Blo 2225435 7515611 := bstep (se 1 (by rfl) ⟨5636708, by rfl⟩ : syracuseStep 7515611 = 11273417) B11273417
theorem B5010407 : Blo 2225435 5010407 := bstep (se 1 (by rfl) ⟨3757805, by rfl⟩ : syracuseStep 5010407 = 7515611) B7515611
theorem B3340271 : Blo 2225435 3340271 := bstep (se 1 (by rfl) ⟨2505203, by rfl⟩ : syracuseStep 3340271 = 5010407) B5010407
theorem B2226847 : Blo 2225435 2226847 := bstep (se 1 (by rfl) ⟨1670135, by rfl⟩ : syracuseStep 2226847 = 3340271) B3340271
theorem B3340277 : Blo 2225435 3340277 := bbase (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) (by norm_num)
theorem B2226851 : Blo 2225435 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B10700981 : Blo 2225435 10700981 := bbase (se 5 (by rfl) ⟨501608, by rfl⟩ : syracuseStep 10700981 = 1003217) (by norm_num)
theorem B7133987 : Blo 2225435 7133987 := bstep (se 1 (by rfl) ⟨5350490, by rfl⟩ : syracuseStep 7133987 = 10700981) B10700981
theorem B4755991 : Blo 2225435 4755991 := bstep (se 1 (by rfl) ⟨3566993, by rfl⟩ : syracuseStep 4755991 = 7133987) B7133987
theorem B6341321 : Blo 2225435 6341321 := bstep (se 2 (by rfl) ⟨2377995, by rfl⟩ : syracuseStep 6341321 = 4755991) B4755991
theorem B4227547 : Blo 2225435 4227547 := bstep (se 1 (by rfl) ⟨3170660, by rfl⟩ : syracuseStep 4227547 = 6341321) B6341321
theorem B5636729 : Blo 2225435 5636729 := bstep (se 2 (by rfl) ⟨2113773, by rfl⟩ : syracuseStep 5636729 = 4227547) B4227547
theorem B3757819 : Blo 2225435 3757819 := bstep (se 1 (by rfl) ⟨2818364, by rfl⟩ : syracuseStep 3757819 = 5636729) B5636729
theorem B5010425 : Blo 2225435 5010425 := bstep (se 2 (by rfl) ⟨1878909, by rfl⟩ : syracuseStep 5010425 = 3757819) B3757819
theorem B3340283 : Blo 2225435 3340283 := bstep (se 1 (by rfl) ⟨2505212, by rfl⟩ : syracuseStep 3340283 = 5010425) B5010425
theorem B2226855 : Blo 2225435 2226855 := bstep (se 1 (by rfl) ⟨1670141, by rfl⟩ : syracuseStep 2226855 = 3340283) B3340283
theorem B2505217 : Blo 2225435 2505217 := bbase (se 2 (by rfl) ⟨939456, by rfl⟩ : syracuseStep 2505217 = 1878913) (by norm_num)
theorem B3340289 : Blo 2225435 3340289 := bstep (se 2 (by rfl) ⟨1252608, by rfl⟩ : syracuseStep 3340289 = 2505217) B2505217
theorem B2226859 : Blo 2225435 2226859 := bstep (se 1 (by rfl) ⟨1670144, by rfl⟩ : syracuseStep 2226859 = 3340289) B3340289
theorem B5636749 : Blo 2225435 5636749 := bbase (se 3 (by rfl) ⟨1056890, by rfl⟩ : syracuseStep 5636749 = 2113781) (by norm_num)
theorem B7515665 : Blo 2225435 7515665 := bstep (se 2 (by rfl) ⟨2818374, by rfl⟩ : syracuseStep 7515665 = 5636749) B5636749
theorem B5010443 : Blo 2225435 5010443 := bstep (se 1 (by rfl) ⟨3757832, by rfl⟩ : syracuseStep 5010443 = 7515665) B7515665
theorem B3340295 : Blo 2225435 3340295 := bstep (se 1 (by rfl) ⟨2505221, by rfl⟩ : syracuseStep 3340295 = 5010443) B5010443
theorem B2226863 : Blo 2225435 2226863 := bstep (se 1 (by rfl) ⟨1670147, by rfl⟩ : syracuseStep 2226863 = 3340295) B3340295
theorem B3340301 : Blo 2225435 3340301 := bbase (se 3 (by rfl) ⟨626306, by rfl⟩ : syracuseStep 3340301 = 1252613) (by norm_num)
theorem B2226867 : Blo 2225435 2226867 := bstep (se 1 (by rfl) ⟨1670150, by rfl⟩ : syracuseStep 2226867 = 3340301) B3340301
theorem B5010461 : Blo 2225435 5010461 := bbase (se 3 (by rfl) ⟨939461, by rfl⟩ : syracuseStep 5010461 = 1878923) (by norm_num)
theorem B3340307 : Blo 2225435 3340307 := bstep (se 1 (by rfl) ⟨2505230, by rfl⟩ : syracuseStep 3340307 = 5010461) B5010461
theorem B2226871 : Blo 2225435 2226871 := bstep (se 1 (by rfl) ⟨1670153, by rfl⟩ : syracuseStep 2226871 = 3340307) B3340307
theorem B3757853 : Blo 2225435 3757853 := bbase (se 3 (by rfl) ⟨704597, by rfl⟩ : syracuseStep 3757853 = 1409195) (by norm_num)
theorem B2505235 : Blo 2225435 2505235 := bstep (se 1 (by rfl) ⟨1878926, by rfl⟩ : syracuseStep 2505235 = 3757853) B3757853
theorem B3340313 : Blo 2225435 3340313 := bstep (se 2 (by rfl) ⟨1252617, by rfl⟩ : syracuseStep 3340313 = 2505235) B2505235
theorem B2226875 : Blo 2225435 2226875 := bstep (se 1 (by rfl) ⟨1670156, by rfl⟩ : syracuseStep 2226875 = 3340313) B3340313
theorem B4514525 : Blo 2225435 4514525 := bbase (se 3 (by rfl) ⟨846473, by rfl⟩ : syracuseStep 4514525 = 1692947) (by norm_num)
theorem B3009683 : Blo 2225435 3009683 := bstep (se 1 (by rfl) ⟨2257262, by rfl⟩ : syracuseStep 3009683 = 4514525) B4514525
theorem B8025821 : Blo 2225435 8025821 := bstep (se 3 (by rfl) ⟨1504841, by rfl⟩ : syracuseStep 8025821 = 3009683) B3009683
theorem B5350547 : Blo 2225435 5350547 := bstep (se 1 (by rfl) ⟨4012910, by rfl⟩ : syracuseStep 5350547 = 8025821) B8025821
theorem B14268125 : Blo 2225435 14268125 := bstep (se 3 (by rfl) ⟨2675273, by rfl⟩ : syracuseStep 14268125 = 5350547) B5350547
theorem B9512083 : Blo 2225435 9512083 := bstep (se 1 (by rfl) ⟨7134062, by rfl⟩ : syracuseStep 9512083 = 14268125) B14268125
theorem B12682777 : Blo 2225435 12682777 := bstep (se 2 (by rfl) ⟨4756041, by rfl⟩ : syracuseStep 12682777 = 9512083) B9512083
theorem B16910369 : Blo 2225435 16910369 := bstep (se 2 (by rfl) ⟨6341388, by rfl⟩ : syracuseStep 16910369 = 12682777) B12682777
theorem B11273579 : Blo 2225435 11273579 := bstep (se 1 (by rfl) ⟨8455184, by rfl⟩ : syracuseStep 11273579 = 16910369) B16910369
theorem B7515719 : Blo 2225435 7515719 := bstep (se 1 (by rfl) ⟨5636789, by rfl⟩ : syracuseStep 7515719 = 11273579) B11273579
theorem B5010479 : Blo 2225435 5010479 := bstep (se 1 (by rfl) ⟨3757859, by rfl⟩ : syracuseStep 5010479 = 7515719) B7515719
theorem B3340319 : Blo 2225435 3340319 := bstep (se 1 (by rfl) ⟨2505239, by rfl⟩ : syracuseStep 3340319 = 5010479) B5010479
theorem B2226879 : Blo 2225435 2226879 := bstep (se 1 (by rfl) ⟨1670159, by rfl⟩ : syracuseStep 2226879 = 3340319) B3340319
theorem B3340325 : Blo 2225435 3340325 := bbase (se 4 (by rfl) ⟨313155, by rfl⟩ : syracuseStep 3340325 = 626311) (by norm_num)
theorem B2226883 : Blo 2225435 2226883 := bstep (se 1 (by rfl) ⟨1670162, by rfl⟩ : syracuseStep 2226883 = 3340325) B3340325
theorem B2818405 : Blo 2225435 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B3757873 : Blo 2225435 3757873 := bstep (se 2 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 3757873 = 2818405) B2818405
theorem B5010497 : Blo 2225435 5010497 := bstep (se 2 (by rfl) ⟨1878936, by rfl⟩ : syracuseStep 5010497 = 3757873) B3757873
theorem B3340331 : Blo 2225435 3340331 := bstep (se 1 (by rfl) ⟨2505248, by rfl⟩ : syracuseStep 3340331 = 5010497) B5010497
theorem B2226887 : Blo 2225435 2226887 := bstep (se 1 (by rfl) ⟨1670165, by rfl⟩ : syracuseStep 2226887 = 3340331) B3340331
theorem B2505253 : Blo 2225435 2505253 := bbase (se 4 (by rfl) ⟨234867, by rfl⟩ : syracuseStep 2505253 = 469735) (by norm_num)
theorem B3340337 : Blo 2225435 3340337 := bstep (se 2 (by rfl) ⟨1252626, by rfl⟩ : syracuseStep 3340337 = 2505253) B2505253
theorem B2226891 : Blo 2225435 2226891 := bstep (se 1 (by rfl) ⟨1670168, by rfl⟩ : syracuseStep 2226891 = 3340337) B3340337
theorem B10701173 : Blo 2225435 10701173 := bbase (se 5 (by rfl) ⟨501617, by rfl⟩ : syracuseStep 10701173 = 1003235) (by norm_num)
theorem B7134115 : Blo 2225435 7134115 := bstep (se 1 (by rfl) ⟨5350586, by rfl⟩ : syracuseStep 7134115 = 10701173) B10701173
theorem B9512153 : Blo 2225435 9512153 := bstep (se 2 (by rfl) ⟨3567057, by rfl⟩ : syracuseStep 9512153 = 7134115) B7134115
theorem B6341435 : Blo 2225435 6341435 := bstep (se 1 (by rfl) ⟨4756076, by rfl⟩ : syracuseStep 6341435 = 9512153) B9512153
theorem B4227623 : Blo 2225435 4227623 := bstep (se 1 (by rfl) ⟨3170717, by rfl⟩ : syracuseStep 4227623 = 6341435) B6341435
theorem B2818415 : Blo 2225435 2818415 := bstep (se 1 (by rfl) ⟨2113811, by rfl⟩ : syracuseStep 2818415 = 4227623) B4227623
theorem B7515773 : Blo 2225435 7515773 := bstep (se 3 (by rfl) ⟨1409207, by rfl⟩ : syracuseStep 7515773 = 2818415) B2818415
theorem B5010515 : Blo 2225435 5010515 := bstep (se 1 (by rfl) ⟨3757886, by rfl⟩ : syracuseStep 5010515 = 7515773) B7515773
theorem B3340343 : Blo 2225435 3340343 := bstep (se 1 (by rfl) ⟨2505257, by rfl⟩ : syracuseStep 3340343 = 5010515) B5010515
theorem B2226895 : Blo 2225435 2226895 := bstep (se 1 (by rfl) ⟨1670171, by rfl⟩ : syracuseStep 2226895 = 3340343) B3340343
theorem B3340349 : Blo 2225435 3340349 := bbase (se 3 (by rfl) ⟨626315, by rfl⟩ : syracuseStep 3340349 = 1252631) (by norm_num)
theorem B2226899 : Blo 2225435 2226899 := bstep (se 1 (by rfl) ⟨1670174, by rfl⟩ : syracuseStep 2226899 = 3340349) B3340349
theorem B5010533 : Blo 2225435 5010533 := bbase (se 4 (by rfl) ⟨469737, by rfl⟩ : syracuseStep 5010533 = 939475) (by norm_num)
theorem B3340355 : Blo 2225435 3340355 := bstep (se 1 (by rfl) ⟨2505266, by rfl⟩ : syracuseStep 3340355 = 5010533) B5010533
theorem B2226903 : Blo 2225435 2226903 := bstep (se 1 (by rfl) ⟨1670177, by rfl⟩ : syracuseStep 2226903 = 3340355) B3340355
theorem B5636861 : Blo 2225435 5636861 := bbase (se 3 (by rfl) ⟨1056911, by rfl⟩ : syracuseStep 5636861 = 2113823) (by norm_num)
theorem B3757907 : Blo 2225435 3757907 := bstep (se 1 (by rfl) ⟨2818430, by rfl⟩ : syracuseStep 3757907 = 5636861) B5636861
theorem B2505271 : Blo 2225435 2505271 := bstep (se 1 (by rfl) ⟨1878953, by rfl⟩ : syracuseStep 2505271 = 3757907) B3757907
theorem B3340361 : Blo 2225435 3340361 := bstep (se 2 (by rfl) ⟨1252635, by rfl⟩ : syracuseStep 3340361 = 2505271) B2505271
theorem B2226907 : Blo 2225435 2226907 := bstep (se 1 (by rfl) ⟨1670180, by rfl⟩ : syracuseStep 2226907 = 3340361) B3340361
theorem B4227653 : Blo 2225435 4227653 := bbase (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) (by norm_num)
theorem B11273741 : Blo 2225435 11273741 := bstep (se 3 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 11273741 = 4227653) B4227653
theorem B7515827 : Blo 2225435 7515827 := bstep (se 1 (by rfl) ⟨5636870, by rfl⟩ : syracuseStep 7515827 = 11273741) B11273741
theorem B5010551 : Blo 2225435 5010551 := bstep (se 1 (by rfl) ⟨3757913, by rfl⟩ : syracuseStep 5010551 = 7515827) B7515827
theorem B3340367 : Blo 2225435 3340367 := bstep (se 1 (by rfl) ⟨2505275, by rfl⟩ : syracuseStep 3340367 = 5010551) B5010551
theorem B2226911 : Blo 2225435 2226911 := bstep (se 1 (by rfl) ⟨1670183, by rfl⟩ : syracuseStep 2226911 = 3340367) B3340367
theorem B3340373 : Blo 2225435 3340373 := bbase (se 8 (by rfl) ⟨19572, by rfl⟩ : syracuseStep 3340373 = 39145) (by norm_num)
theorem B2226915 : Blo 2225435 2226915 := bstep (se 1 (by rfl) ⟨1670186, by rfl⟩ : syracuseStep 2226915 = 3340373) B3340373
theorem B5423645 : Blo 2225435 5423645 := bbase (se 3 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 5423645 = 2033867) (by norm_num)
theorem B14463053 : Blo 2225435 14463053 := bstep (se 3 (by rfl) ⟨2711822, by rfl⟩ : syracuseStep 14463053 = 5423645) B5423645
theorem B9642035 : Blo 2225435 9642035 := bstep (se 1 (by rfl) ⟨7231526, by rfl⟩ : syracuseStep 9642035 = 14463053) B14463053
theorem B25712093 : Blo 2225435 25712093 := bstep (se 3 (by rfl) ⟨4821017, by rfl⟩ : syracuseStep 25712093 = 9642035) B9642035
theorem B17141395 : Blo 2225435 17141395 := bstep (se 1 (by rfl) ⟨12856046, by rfl⟩ : syracuseStep 17141395 = 25712093) B25712093
theorem B22855193 : Blo 2225435 22855193 := bstep (se 2 (by rfl) ⟨8570697, by rfl⟩ : syracuseStep 22855193 = 17141395) B17141395
theorem B15236795 : Blo 2225435 15236795 := bstep (se 1 (by rfl) ⟨11427596, by rfl⟩ : syracuseStep 15236795 = 22855193) B22855193
theorem B40631453 : Blo 2225435 40631453 := bstep (se 3 (by rfl) ⟨7618397, by rfl⟩ : syracuseStep 40631453 = 15236795) B15236795
theorem B27087635 : Blo 2225435 27087635 := bstep (se 1 (by rfl) ⟨20315726, by rfl⟩ : syracuseStep 27087635 = 40631453) B40631453
theorem B72233693 : Blo 2225435 72233693 := bstep (se 3 (by rfl) ⟨13543817, by rfl⟩ : syracuseStep 72233693 = 27087635) B27087635
theorem B48155795 : Blo 2225435 48155795 := bstep (se 1 (by rfl) ⟨36116846, by rfl⟩ : syracuseStep 48155795 = 72233693) B72233693
theorem B32103863 : Blo 2225435 32103863 := bstep (se 1 (by rfl) ⟨24077897, by rfl⟩ : syracuseStep 32103863 = 48155795) B48155795
theorem B21402575 : Blo 2225435 21402575 := bstep (se 1 (by rfl) ⟨16051931, by rfl⟩ : syracuseStep 21402575 = 32103863) B32103863
theorem B14268383 : Blo 2225435 14268383 := bstep (se 1 (by rfl) ⟨10701287, by rfl⟩ : syracuseStep 14268383 = 21402575) B21402575
theorem B9512255 : Blo 2225435 9512255 := bstep (se 1 (by rfl) ⟨7134191, by rfl⟩ : syracuseStep 9512255 = 14268383) B14268383
theorem B6341503 : Blo 2225435 6341503 := bstep (se 1 (by rfl) ⟨4756127, by rfl⟩ : syracuseStep 6341503 = 9512255) B9512255
theorem B8455337 : Blo 2225435 8455337 := bstep (se 2 (by rfl) ⟨3170751, by rfl⟩ : syracuseStep 8455337 = 6341503) B6341503
theorem B5636891 : Blo 2225435 5636891 := bstep (se 1 (by rfl) ⟨4227668, by rfl⟩ : syracuseStep 5636891 = 8455337) B8455337
theorem B3757927 : Blo 2225435 3757927 := bstep (se 1 (by rfl) ⟨2818445, by rfl⟩ : syracuseStep 3757927 = 5636891) B5636891
theorem B5010569 : Blo 2225435 5010569 := bstep (se 2 (by rfl) ⟨1878963, by rfl⟩ : syracuseStep 5010569 = 3757927) B3757927
theorem B3340379 : Blo 2225435 3340379 := bstep (se 1 (by rfl) ⟨2505284, by rfl⟩ : syracuseStep 3340379 = 5010569) B5010569
theorem B2226919 : Blo 2225435 2226919 := bstep (se 1 (by rfl) ⟨1670189, by rfl⟩ : syracuseStep 2226919 = 3340379) B3340379
theorem B2505289 : Blo 2225435 2505289 := bbase (se 2 (by rfl) ⟨939483, by rfl⟩ : syracuseStep 2505289 = 1878967) (by norm_num)
theorem B3340385 : Blo 2225435 3340385 := bstep (se 2 (by rfl) ⟨1252644, by rfl⟩ : syracuseStep 3340385 = 2505289) B2505289
theorem B2226923 : Blo 2225435 2226923 := bstep (se 1 (by rfl) ⟨1670192, by rfl⟩ : syracuseStep 2226923 = 3340385) B3340385
theorem B4012997 : Blo 2225435 4012997 := bbase (se 4 (by rfl) ⟨376218, by rfl⟩ : syracuseStep 4012997 = 752437) (by norm_num)
theorem B10701325 : Blo 2225435 10701325 := bstep (se 3 (by rfl) ⟨2006498, by rfl⟩ : syracuseStep 10701325 = 4012997) B4012997
theorem B14268433 : Blo 2225435 14268433 := bstep (se 2 (by rfl) ⟨5350662, by rfl⟩ : syracuseStep 14268433 = 10701325) B10701325
theorem B19024577 : Blo 2225435 19024577 := bstep (se 2 (by rfl) ⟨7134216, by rfl⟩ : syracuseStep 19024577 = 14268433) B14268433
theorem B12683051 : Blo 2225435 12683051 := bstep (se 1 (by rfl) ⟨9512288, by rfl⟩ : syracuseStep 12683051 = 19024577) B19024577
theorem B8455367 : Blo 2225435 8455367 := bstep (se 1 (by rfl) ⟨6341525, by rfl⟩ : syracuseStep 8455367 = 12683051) B12683051
theorem B5636911 : Blo 2225435 5636911 := bstep (se 1 (by rfl) ⟨4227683, by rfl⟩ : syracuseStep 5636911 = 8455367) B8455367
theorem B7515881 : Blo 2225435 7515881 := bstep (se 2 (by rfl) ⟨2818455, by rfl⟩ : syracuseStep 7515881 = 5636911) B5636911
theorem B5010587 : Blo 2225435 5010587 := bstep (se 1 (by rfl) ⟨3757940, by rfl⟩ : syracuseStep 5010587 = 7515881) B7515881
theorem B3340391 : Blo 2225435 3340391 := bstep (se 1 (by rfl) ⟨2505293, by rfl⟩ : syracuseStep 3340391 = 5010587) B5010587
theorem B2226927 : Blo 2225435 2226927 := bstep (se 1 (by rfl) ⟨1670195, by rfl⟩ : syracuseStep 2226927 = 3340391) B3340391
theorem B3340397 : Blo 2225435 3340397 := bbase (se 3 (by rfl) ⟨626324, by rfl⟩ : syracuseStep 3340397 = 1252649) (by norm_num)
theorem B2226931 : Blo 2225435 2226931 := bstep (se 1 (by rfl) ⟨1670198, by rfl⟩ : syracuseStep 2226931 = 3340397) B3340397
theorem B5010605 : Blo 2225435 5010605 := bbase (se 3 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 5010605 = 1878977) (by norm_num)
theorem B3340403 : Blo 2225435 3340403 := bstep (se 1 (by rfl) ⟨2505302, by rfl⟩ : syracuseStep 3340403 = 5010605) B5010605
theorem B2226935 : Blo 2225435 2226935 := bstep (se 1 (by rfl) ⟨1670201, by rfl⟩ : syracuseStep 2226935 = 3340403) B3340403
theorem B5350693 : Blo 2225435 5350693 := bbase (se 4 (by rfl) ⟨501627, by rfl⟩ : syracuseStep 5350693 = 1003255) (by norm_num)
theorem B7134257 : Blo 2225435 7134257 := bstep (se 2 (by rfl) ⟨2675346, by rfl⟩ : syracuseStep 7134257 = 5350693) B5350693
theorem B4756171 : Blo 2225435 4756171 := bstep (se 1 (by rfl) ⟨3567128, by rfl⟩ : syracuseStep 4756171 = 7134257) B7134257
theorem B6341561 : Blo 2225435 6341561 := bstep (se 2 (by rfl) ⟨2378085, by rfl⟩ : syracuseStep 6341561 = 4756171) B4756171
theorem B4227707 : Blo 2225435 4227707 := bstep (se 1 (by rfl) ⟨3170780, by rfl⟩ : syracuseStep 4227707 = 6341561) B6341561
theorem B2818471 : Blo 2225435 2818471 := bstep (se 1 (by rfl) ⟨2113853, by rfl⟩ : syracuseStep 2818471 = 4227707) B4227707
theorem B3757961 : Blo 2225435 3757961 := bstep (se 2 (by rfl) ⟨1409235, by rfl⟩ : syracuseStep 3757961 = 2818471) B2818471
theorem B2505307 : Blo 2225435 2505307 := bstep (se 1 (by rfl) ⟨1878980, by rfl⟩ : syracuseStep 2505307 = 3757961) B3757961
theorem B3340409 : Blo 2225435 3340409 := bstep (se 2 (by rfl) ⟨1252653, by rfl⟩ : syracuseStep 3340409 = 2505307) B2505307
theorem B2226939 : Blo 2225435 2226939 := bstep (se 1 (by rfl) ⟨1670204, by rfl⟩ : syracuseStep 2226939 = 3340409) B3340409
theorem B5713861 : Blo 2225435 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B7618481 : Blo 2225435 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B5078987 : Blo 2225435 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B3385991 : Blo 2225435 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2257327 : Blo 2225435 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B12039077 : Blo 2225435 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B8026051 : Blo 2225435 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B10701401 : Blo 2225435 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B28537069 : Blo 2225435 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B38049425 : Blo 2225435 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B25366283 : Blo 2225435 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B16910855 : Blo 2225435 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B11273903 : Blo 2225435 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B7515935 : Blo 2225435 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B5010623 : Blo 2225435 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B3340415 : Blo 2225435 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B2226943 : Blo 2225435 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B3340421 : Blo 2225435 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B2226947 : Blo 2225435 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B3757981 : Blo 2225435 3757981 := bbase (se 3 (by rfl) ⟨704621, by rfl⟩ : syracuseStep 3757981 = 1409243) (by norm_num)
theorem B5010641 : Blo 2225435 5010641 := bstep (se 2 (by rfl) ⟨1878990, by rfl⟩ : syracuseStep 5010641 = 3757981) B3757981
theorem B3340427 : Blo 2225435 3340427 := bstep (se 1 (by rfl) ⟨2505320, by rfl⟩ : syracuseStep 3340427 = 5010641) B5010641
theorem B2226951 : Blo 2225435 2226951 := bstep (se 1 (by rfl) ⟨1670213, by rfl⟩ : syracuseStep 2226951 = 3340427) B3340427
theorem B2505325 : Blo 2225435 2505325 := bbase (se 3 (by rfl) ⟨469748, by rfl⟩ : syracuseStep 2505325 = 939497) (by norm_num)
theorem B3340433 : Blo 2225435 3340433 := bstep (se 2 (by rfl) ⟨1252662, by rfl⟩ : syracuseStep 3340433 = 2505325) B2505325
theorem B2226955 : Blo 2225435 2226955 := bstep (se 1 (by rfl) ⟨1670216, by rfl⟩ : syracuseStep 2226955 = 3340433) B3340433
theorem B7515989 : Blo 2225435 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B5010659 : Blo 2225435 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B3340439 : Blo 2225435 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B2226959 : Blo 2225435 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B3340445 : Blo 2225435 3340445 := bbase (se 3 (by rfl) ⟨626333, by rfl⟩ : syracuseStep 3340445 = 1252667) (by norm_num)
theorem B2226963 : Blo 2225435 2226963 := bstep (se 1 (by rfl) ⟨1670222, by rfl⟩ : syracuseStep 2226963 = 3340445) B3340445
theorem B5010677 : Blo 2225435 5010677 := bbase (se 5 (by rfl) ⟨234875, by rfl⟩ : syracuseStep 5010677 = 469751) (by norm_num)
theorem B3340451 : Blo 2225435 3340451 := bstep (se 1 (by rfl) ⟨2505338, by rfl⟩ : syracuseStep 3340451 = 5010677) B5010677
theorem B2226967 : Blo 2225435 2226967 := bstep (se 1 (by rfl) ⟨1670225, by rfl⟩ : syracuseStep 2226967 = 3340451) B3340451
theorem B5423773 : Blo 2225435 5423773 := bbase (se 3 (by rfl) ⟨1016957, by rfl⟩ : syracuseStep 5423773 = 2033915) (by norm_num)
theorem B7231697 : Blo 2225435 7231697 := bstep (se 2 (by rfl) ⟨2711886, by rfl⟩ : syracuseStep 7231697 = 5423773) B5423773
theorem B4821131 : Blo 2225435 4821131 := bstep (se 1 (by rfl) ⟨3615848, by rfl⟩ : syracuseStep 4821131 = 7231697) B7231697
theorem B3214087 : Blo 2225435 3214087 := bstep (se 1 (by rfl) ⟨2410565, by rfl⟩ : syracuseStep 3214087 = 4821131) B4821131
theorem B17141797 : Blo 2225435 17141797 := bstep (se 4 (by rfl) ⟨1607043, by rfl⟩ : syracuseStep 17141797 = 3214087) B3214087
theorem B22855729 : Blo 2225435 22855729 := bstep (se 2 (by rfl) ⟨8570898, by rfl⟩ : syracuseStep 22855729 = 17141797) B17141797
theorem B30474305 : Blo 2225435 30474305 := bstep (se 2 (by rfl) ⟨11427864, by rfl⟩ : syracuseStep 30474305 = 22855729) B22855729
theorem B20316203 : Blo 2225435 20316203 := bstep (se 1 (by rfl) ⟨15237152, by rfl⟩ : syracuseStep 20316203 = 30474305) B30474305
theorem B13544135 : Blo 2225435 13544135 := bstep (se 1 (by rfl) ⟨10158101, by rfl⟩ : syracuseStep 13544135 = 20316203) B20316203
theorem B9029423 : Blo 2225435 9029423 := bstep (se 1 (by rfl) ⟨6772067, by rfl⟩ : syracuseStep 9029423 = 13544135) B13544135
theorem B6019615 : Blo 2225435 6019615 := bstep (se 1 (by rfl) ⟨4514711, by rfl⟩ : syracuseStep 6019615 = 9029423) B9029423
theorem B32104613 : Blo 2225435 32104613 := bstep (se 4 (by rfl) ⟨3009807, by rfl⟩ : syracuseStep 32104613 = 6019615) B6019615
theorem B21403075 : Blo 2225435 21403075 := bstep (se 1 (by rfl) ⟨16052306, by rfl⟩ : syracuseStep 21403075 = 32104613) B32104613
theorem B28537433 : Blo 2225435 28537433 := bstep (se 2 (by rfl) ⟨10701537, by rfl⟩ : syracuseStep 28537433 = 21403075) B21403075
theorem B19024955 : Blo 2225435 19024955 := bstep (se 1 (by rfl) ⟨14268716, by rfl⟩ : syracuseStep 19024955 = 28537433) B28537433
theorem B12683303 : Blo 2225435 12683303 := bstep (se 1 (by rfl) ⟨9512477, by rfl⟩ : syracuseStep 12683303 = 19024955) B19024955
theorem B8455535 : Blo 2225435 8455535 := bstep (se 1 (by rfl) ⟨6341651, by rfl⟩ : syracuseStep 8455535 = 12683303) B12683303
theorem B5637023 : Blo 2225435 5637023 := bstep (se 1 (by rfl) ⟨4227767, by rfl⟩ : syracuseStep 5637023 = 8455535) B8455535
theorem B3758015 : Blo 2225435 3758015 := bstep (se 1 (by rfl) ⟨2818511, by rfl⟩ : syracuseStep 3758015 = 5637023) B5637023
theorem B2505343 : Blo 2225435 2505343 := bstep (se 1 (by rfl) ⟨1879007, by rfl⟩ : syracuseStep 2505343 = 3758015) B3758015
theorem B3340457 : Blo 2225435 3340457 := bstep (se 2 (by rfl) ⟨1252671, by rfl⟩ : syracuseStep 3340457 = 2505343) B2505343
theorem B2226971 : Blo 2225435 2226971 := bstep (se 1 (by rfl) ⟨1670228, by rfl⟩ : syracuseStep 2226971 = 3340457) B3340457
theorem B10701557 : Blo 2225435 10701557 := bbase (se 5 (by rfl) ⟨501635, by rfl⟩ : syracuseStep 10701557 = 1003271) (by norm_num)
theorem B7134371 : Blo 2225435 7134371 := bstep (se 1 (by rfl) ⟨5350778, by rfl⟩ : syracuseStep 7134371 = 10701557) B10701557
theorem B4756247 : Blo 2225435 4756247 := bstep (se 1 (by rfl) ⟨3567185, by rfl⟩ : syracuseStep 4756247 = 7134371) B7134371
theorem B3170831 : Blo 2225435 3170831 := bstep (se 1 (by rfl) ⟨2378123, by rfl⟩ : syracuseStep 3170831 = 4756247) B4756247
theorem B8455549 : Blo 2225435 8455549 := bstep (se 3 (by rfl) ⟨1585415, by rfl⟩ : syracuseStep 8455549 = 3170831) B3170831
theorem B11274065 : Blo 2225435 11274065 := bstep (se 2 (by rfl) ⟨4227774, by rfl⟩ : syracuseStep 11274065 = 8455549) B8455549
theorem B7516043 : Blo 2225435 7516043 := bstep (se 1 (by rfl) ⟨5637032, by rfl⟩ : syracuseStep 7516043 = 11274065) B11274065
theorem B5010695 : Blo 2225435 5010695 := bstep (se 1 (by rfl) ⟨3758021, by rfl⟩ : syracuseStep 5010695 = 7516043) B7516043
theorem B3340463 : Blo 2225435 3340463 := bstep (se 1 (by rfl) ⟨2505347, by rfl⟩ : syracuseStep 3340463 = 5010695) B5010695
theorem B2226975 : Blo 2225435 2226975 := bstep (se 1 (by rfl) ⟨1670231, by rfl⟩ : syracuseStep 2226975 = 3340463) B3340463
theorem B3340469 : Blo 2225435 3340469 := bbase (se 5 (by rfl) ⟨156584, by rfl⟩ : syracuseStep 3340469 = 313169) (by norm_num)
theorem B2226979 : Blo 2225435 2226979 := bstep (se 1 (by rfl) ⟨1670234, by rfl⟩ : syracuseStep 2226979 = 3340469) B3340469
theorem B5637053 : Blo 2225435 5637053 := bbase (se 3 (by rfl) ⟨1056947, by rfl⟩ : syracuseStep 5637053 = 2113895) (by norm_num)
theorem B3758035 : Blo 2225435 3758035 := bstep (se 1 (by rfl) ⟨2818526, by rfl⟩ : syracuseStep 3758035 = 5637053) B5637053
theorem B5010713 : Blo 2225435 5010713 := bstep (se 2 (by rfl) ⟨1879017, by rfl⟩ : syracuseStep 5010713 = 3758035) B3758035
theorem B3340475 : Blo 2225435 3340475 := bstep (se 1 (by rfl) ⟨2505356, by rfl⟩ : syracuseStep 3340475 = 5010713) B5010713
theorem B2226983 : Blo 2225435 2226983 := bstep (se 1 (by rfl) ⟨1670237, by rfl⟩ : syracuseStep 2226983 = 3340475) B3340475
theorem B2505361 : Blo 2225435 2505361 := bbase (se 2 (by rfl) ⟨939510, by rfl⟩ : syracuseStep 2505361 = 1879021) (by norm_num)
theorem B3340481 : Blo 2225435 3340481 := bstep (se 2 (by rfl) ⟨1252680, by rfl⟩ : syracuseStep 3340481 = 2505361) B2505361
theorem B2226987 : Blo 2225435 2226987 := bstep (se 1 (by rfl) ⟨1670240, by rfl⟩ : syracuseStep 2226987 = 3340481) B3340481
theorem B4227805 : Blo 2225435 4227805 := bbase (se 3 (by rfl) ⟨792713, by rfl⟩ : syracuseStep 4227805 = 1585427) (by norm_num)
theorem B5637073 : Blo 2225435 5637073 := bstep (se 2 (by rfl) ⟨2113902, by rfl⟩ : syracuseStep 5637073 = 4227805) B4227805
theorem B7516097 : Blo 2225435 7516097 := bstep (se 2 (by rfl) ⟨2818536, by rfl⟩ : syracuseStep 7516097 = 5637073) B5637073
theorem B5010731 : Blo 2225435 5010731 := bstep (se 1 (by rfl) ⟨3758048, by rfl⟩ : syracuseStep 5010731 = 7516097) B7516097
theorem B3340487 : Blo 2225435 3340487 := bstep (se 1 (by rfl) ⟨2505365, by rfl⟩ : syracuseStep 3340487 = 5010731) B5010731
theorem B2226991 : Blo 2225435 2226991 := bstep (se 1 (by rfl) ⟨1670243, by rfl⟩ : syracuseStep 2226991 = 3340487) B3340487
theorem B3340493 : Blo 2225435 3340493 := bbase (se 3 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 3340493 = 1252685) (by norm_num)
theorem B2226995 : Blo 2225435 2226995 := bstep (se 1 (by rfl) ⟨1670246, by rfl⟩ : syracuseStep 2226995 = 3340493) B3340493
theorem B5010749 : Blo 2225435 5010749 := bbase (se 3 (by rfl) ⟨939515, by rfl⟩ : syracuseStep 5010749 = 1879031) (by norm_num)
theorem B3340499 : Blo 2225435 3340499 := bstep (se 1 (by rfl) ⟨2505374, by rfl⟩ : syracuseStep 3340499 = 5010749) B5010749
theorem B2226999 : Blo 2225435 2226999 := bstep (se 1 (by rfl) ⟨1670249, by rfl⟩ : syracuseStep 2226999 = 3340499) B3340499
theorem B3758069 : Blo 2225435 3758069 := bbase (se 5 (by rfl) ⟨176159, by rfl⟩ : syracuseStep 3758069 = 352319) (by norm_num)
theorem B2505379 : Blo 2225435 2505379 := bstep (se 1 (by rfl) ⟨1879034, by rfl⟩ : syracuseStep 2505379 = 3758069) B3758069
theorem B3340505 : Blo 2225435 3340505 := bstep (se 2 (by rfl) ⟨1252689, by rfl⟩ : syracuseStep 3340505 = 2505379) B2505379
theorem B2227003 : Blo 2225435 2227003 := bstep (se 1 (by rfl) ⟨1670252, by rfl⟩ : syracuseStep 2227003 = 3340505) B3340505
theorem B5079133 : Blo 2225435 5079133 := bbase (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) (by norm_num)
theorem B6772177 : Blo 2225435 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B9029569 : Blo 2225435 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B12039425 : Blo 2225435 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B8026283 : Blo 2225435 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B5350855 : Blo 2225435 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B7134473 : Blo 2225435 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B4756315 : Blo 2225435 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B6341753 : Blo 2225435 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B16911341 : Blo 2225435 16911341 := bstep (se 3 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 16911341 = 6341753) B6341753
theorem B11274227 : Blo 2225435 11274227 := bstep (se 1 (by rfl) ⟨8455670, by rfl⟩ : syracuseStep 11274227 = 16911341) B16911341
theorem B7516151 : Blo 2225435 7516151 := bstep (se 1 (by rfl) ⟨5637113, by rfl⟩ : syracuseStep 7516151 = 11274227) B11274227
theorem B5010767 : Blo 2225435 5010767 := bstep (se 1 (by rfl) ⟨3758075, by rfl⟩ : syracuseStep 5010767 = 7516151) B7516151
theorem B3340511 : Blo 2225435 3340511 := bstep (se 1 (by rfl) ⟨2505383, by rfl⟩ : syracuseStep 3340511 = 5010767) B5010767
theorem B2227007 : Blo 2225435 2227007 := bstep (se 1 (by rfl) ⟨1670255, by rfl⟩ : syracuseStep 2227007 = 3340511) B3340511
theorem B3340517 : Blo 2225435 3340517 := bbase (se 4 (by rfl) ⟨313173, by rfl⟩ : syracuseStep 3340517 = 626347) (by norm_num)
theorem B2227011 : Blo 2225435 2227011 := bstep (se 1 (by rfl) ⟨1670258, by rfl⟩ : syracuseStep 2227011 = 3340517) B3340517
theorem B4756333 : Blo 2225435 4756333 := bbase (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) (by norm_num)
theorem B6341777 : Blo 2225435 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B4227851 : Blo 2225435 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B2818567 : Blo 2225435 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3758089 : Blo 2225435 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B5010785 : Blo 2225435 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B3340523 : Blo 2225435 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B2227015 : Blo 2225435 2227015 := bstep (se 1 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 2227015 = 3340523) B3340523
theorem B2505397 : Blo 2225435 2505397 := bbase (se 5 (by rfl) ⟨117440, by rfl⟩ : syracuseStep 2505397 = 234881) (by norm_num)
theorem B3340529 : Blo 2225435 3340529 := bstep (se 2 (by rfl) ⟨1252698, by rfl⟩ : syracuseStep 3340529 = 2505397) B2505397
theorem B2227019 : Blo 2225435 2227019 := bstep (se 1 (by rfl) ⟨1670264, by rfl⟩ : syracuseStep 2227019 = 3340529) B3340529
theorem B2818577 : Blo 2225435 2818577 := bbase (se 2 (by rfl) ⟨1056966, by rfl⟩ : syracuseStep 2818577 = 2113933) (by norm_num)
theorem B7516205 : Blo 2225435 7516205 := bstep (se 3 (by rfl) ⟨1409288, by rfl⟩ : syracuseStep 7516205 = 2818577) B2818577
theorem B5010803 : Blo 2225435 5010803 := bstep (se 1 (by rfl) ⟨3758102, by rfl⟩ : syracuseStep 5010803 = 7516205) B7516205
theorem B3340535 : Blo 2225435 3340535 := bstep (se 1 (by rfl) ⟨2505401, by rfl⟩ : syracuseStep 3340535 = 5010803) B5010803
theorem B2227023 : Blo 2225435 2227023 := bstep (se 1 (by rfl) ⟨1670267, by rfl⟩ : syracuseStep 2227023 = 3340535) B3340535
theorem B3340541 : Blo 2225435 3340541 := bbase (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) (by norm_num)
theorem B2227027 : Blo 2225435 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B5010821 : Blo 2225435 5010821 := bbase (se 4 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 5010821 = 939529) (by norm_num)
theorem B3340547 : Blo 2225435 3340547 := bstep (se 1 (by rfl) ⟨2505410, by rfl⟩ : syracuseStep 3340547 = 5010821) B5010821
theorem B2227031 : Blo 2225435 2227031 := bstep (se 1 (by rfl) ⟨1670273, by rfl⟩ : syracuseStep 2227031 = 3340547) B3340547
theorem B3170917 : Blo 2225435 3170917 := bbase (se 4 (by rfl) ⟨297273, by rfl⟩ : syracuseStep 3170917 = 594547) (by norm_num)
theorem B4227889 : Blo 2225435 4227889 := bstep (se 2 (by rfl) ⟨1585458, by rfl⟩ : syracuseStep 4227889 = 3170917) B3170917
theorem B5637185 : Blo 2225435 5637185 := bstep (se 2 (by rfl) ⟨2113944, by rfl⟩ : syracuseStep 5637185 = 4227889) B4227889
theorem B3758123 : Blo 2225435 3758123 := bstep (se 1 (by rfl) ⟨2818592, by rfl⟩ : syracuseStep 3758123 = 5637185) B5637185
theorem B2505415 : Blo 2225435 2505415 := bstep (se 1 (by rfl) ⟨1879061, by rfl⟩ : syracuseStep 2505415 = 3758123) B3758123
theorem B3340553 : Blo 2225435 3340553 := bstep (se 2 (by rfl) ⟨1252707, by rfl⟩ : syracuseStep 3340553 = 2505415) B2505415
theorem B2227035 : Blo 2225435 2227035 := bstep (se 1 (by rfl) ⟨1670276, by rfl⟩ : syracuseStep 2227035 = 3340553) B3340553
theorem B11274389 : Blo 2225435 11274389 := bbase (se 6 (by rfl) ⟨264243, by rfl⟩ : syracuseStep 11274389 = 528487) (by norm_num)
theorem B7516259 : Blo 2225435 7516259 := bstep (se 1 (by rfl) ⟨5637194, by rfl⟩ : syracuseStep 7516259 = 11274389) B11274389
theorem B5010839 : Blo 2225435 5010839 := bstep (se 1 (by rfl) ⟨3758129, by rfl⟩ : syracuseStep 5010839 = 7516259) B7516259
theorem B3340559 : Blo 2225435 3340559 := bstep (se 1 (by rfl) ⟨2505419, by rfl⟩ : syracuseStep 3340559 = 5010839) B5010839
theorem B2227039 : Blo 2225435 2227039 := bstep (se 1 (by rfl) ⟨1670279, by rfl⟩ : syracuseStep 2227039 = 3340559) B3340559
theorem B3340565 : Blo 2225435 3340565 := bbase (se 6 (by rfl) ⟨78294, by rfl⟩ : syracuseStep 3340565 = 156589) (by norm_num)
theorem B2227043 : Blo 2225435 2227043 := bstep (se 1 (by rfl) ⟨1670282, by rfl⟩ : syracuseStep 2227043 = 3340565) B3340565
theorem B13544597 : Blo 2225435 13544597 := bbase (se 6 (by rfl) ⟨317451, by rfl⟩ : syracuseStep 13544597 = 634903) (by norm_num)
theorem B9029731 : Blo 2225435 9029731 := bstep (se 1 (by rfl) ⟨6772298, by rfl⟩ : syracuseStep 9029731 = 13544597) B13544597
theorem B12039641 : Blo 2225435 12039641 := bstep (se 2 (by rfl) ⟨4514865, by rfl⟩ : syracuseStep 12039641 = 9029731) B9029731
theorem B8026427 : Blo 2225435 8026427 := bstep (se 1 (by rfl) ⟨6019820, by rfl⟩ : syracuseStep 8026427 = 12039641) B12039641
theorem B5350951 : Blo 2225435 5350951 := bstep (se 1 (by rfl) ⟨4013213, by rfl⟩ : syracuseStep 5350951 = 8026427) B8026427
theorem B28538405 : Blo 2225435 28538405 := bstep (se 4 (by rfl) ⟨2675475, by rfl⟩ : syracuseStep 28538405 = 5350951) B5350951
theorem B19025603 : Blo 2225435 19025603 := bstep (se 1 (by rfl) ⟨14269202, by rfl⟩ : syracuseStep 19025603 = 28538405) B28538405
theorem B12683735 : Blo 2225435 12683735 := bstep (se 1 (by rfl) ⟨9512801, by rfl⟩ : syracuseStep 12683735 = 19025603) B19025603
theorem B8455823 : Blo 2225435 8455823 := bstep (se 1 (by rfl) ⟨6341867, by rfl⟩ : syracuseStep 8455823 = 12683735) B12683735
theorem B5637215 : Blo 2225435 5637215 := bstep (se 1 (by rfl) ⟨4227911, by rfl⟩ : syracuseStep 5637215 = 8455823) B8455823
theorem B3758143 : Blo 2225435 3758143 := bstep (se 1 (by rfl) ⟨2818607, by rfl⟩ : syracuseStep 3758143 = 5637215) B5637215
theorem B5010857 : Blo 2225435 5010857 := bstep (se 2 (by rfl) ⟨1879071, by rfl⟩ : syracuseStep 5010857 = 3758143) B3758143
theorem B3340571 : Blo 2225435 3340571 := bstep (se 1 (by rfl) ⟨2505428, by rfl⟩ : syracuseStep 3340571 = 5010857) B5010857
theorem B2227047 : Blo 2225435 2227047 := bstep (se 1 (by rfl) ⟨1670285, by rfl⟩ : syracuseStep 2227047 = 3340571) B3340571
theorem B2505433 : Blo 2225435 2505433 := bbase (se 2 (by rfl) ⟨939537, by rfl⟩ : syracuseStep 2505433 = 1879075) (by norm_num)
theorem B3340577 : Blo 2225435 3340577 := bstep (se 2 (by rfl) ⟨1252716, by rfl⟩ : syracuseStep 3340577 = 2505433) B2505433
theorem B2227051 : Blo 2225435 2227051 := bstep (se 1 (by rfl) ⟨1670288, by rfl⟩ : syracuseStep 2227051 = 3340577) B3340577
theorem B2378209 : Blo 2225435 2378209 := bbase (se 2 (by rfl) ⟨891828, by rfl⟩ : syracuseStep 2378209 = 1783657) (by norm_num)
theorem B3170945 : Blo 2225435 3170945 := bstep (se 2 (by rfl) ⟨1189104, by rfl⟩ : syracuseStep 3170945 = 2378209) B2378209
theorem B8455853 : Blo 2225435 8455853 := bstep (se 3 (by rfl) ⟨1585472, by rfl⟩ : syracuseStep 8455853 = 3170945) B3170945
theorem B5637235 : Blo 2225435 5637235 := bstep (se 1 (by rfl) ⟨4227926, by rfl⟩ : syracuseStep 5637235 = 8455853) B8455853
theorem B7516313 : Blo 2225435 7516313 := bstep (se 2 (by rfl) ⟨2818617, by rfl⟩ : syracuseStep 7516313 = 5637235) B5637235
theorem B5010875 : Blo 2225435 5010875 := bstep (se 1 (by rfl) ⟨3758156, by rfl⟩ : syracuseStep 5010875 = 7516313) B7516313
theorem B3340583 : Blo 2225435 3340583 := bstep (se 1 (by rfl) ⟨2505437, by rfl⟩ : syracuseStep 3340583 = 5010875) B5010875
theorem B2227055 : Blo 2225435 2227055 := bstep (se 1 (by rfl) ⟨1670291, by rfl⟩ : syracuseStep 2227055 = 3340583) B3340583
theorem B3340589 : Blo 2225435 3340589 := bbase (se 3 (by rfl) ⟨626360, by rfl⟩ : syracuseStep 3340589 = 1252721) (by norm_num)
theorem B2227059 : Blo 2225435 2227059 := bstep (se 1 (by rfl) ⟨1670294, by rfl⟩ : syracuseStep 2227059 = 3340589) B3340589
theorem B5010893 : Blo 2225435 5010893 := bbase (se 3 (by rfl) ⟨939542, by rfl⟩ : syracuseStep 5010893 = 1879085) (by norm_num)
theorem B3340595 : Blo 2225435 3340595 := bstep (se 1 (by rfl) ⟨2505446, by rfl⟩ : syracuseStep 3340595 = 5010893) B5010893
theorem B2227063 : Blo 2225435 2227063 := bstep (se 1 (by rfl) ⟨1670297, by rfl⟩ : syracuseStep 2227063 = 3340595) B3340595
theorem B2818633 : Blo 2225435 2818633 := bbase (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) (by norm_num)
theorem B3758177 : Blo 2225435 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B2505451 : Blo 2225435 2505451 := bstep (se 1 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 2505451 = 3758177) B3758177
theorem B3340601 : Blo 2225435 3340601 := bstep (se 2 (by rfl) ⟨1252725, by rfl⟩ : syracuseStep 3340601 = 2505451) B2505451
theorem B2227067 : Blo 2225435 2227067 := bstep (se 1 (by rfl) ⟨1670300, by rfl⟩ : syracuseStep 2227067 = 3340601) B3340601
theorem B5714189 : Blo 2225435 5714189 := bbase (se 3 (by rfl) ⟨1071410, by rfl⟩ : syracuseStep 5714189 = 2142821) (by norm_num)
theorem B3809459 : Blo 2225435 3809459 := bstep (se 1 (by rfl) ⟨2857094, by rfl⟩ : syracuseStep 3809459 = 5714189) B5714189
theorem B2539639 : Blo 2225435 2539639 := bstep (se 1 (by rfl) ⟨1904729, by rfl⟩ : syracuseStep 2539639 = 3809459) B3809459
theorem B13544741 : Blo 2225435 13544741 := bstep (se 4 (by rfl) ⟨1269819, by rfl⟩ : syracuseStep 13544741 = 2539639) B2539639
theorem B9029827 : Blo 2225435 9029827 := bstep (se 1 (by rfl) ⟨6772370, by rfl⟩ : syracuseStep 9029827 = 13544741) B13544741
theorem B12039769 : Blo 2225435 12039769 := bstep (se 2 (by rfl) ⟨4514913, by rfl⟩ : syracuseStep 12039769 = 9029827) B9029827
theorem B16053025 : Blo 2225435 16053025 := bstep (se 2 (by rfl) ⟨6019884, by rfl⟩ : syracuseStep 16053025 = 12039769) B12039769
theorem B21404033 : Blo 2225435 21404033 := bstep (se 2 (by rfl) ⟨8026512, by rfl⟩ : syracuseStep 21404033 = 16053025) B16053025
theorem B14269355 : Blo 2225435 14269355 := bstep (se 1 (by rfl) ⟨10702016, by rfl⟩ : syracuseStep 14269355 = 21404033) B21404033
theorem B9512903 : Blo 2225435 9512903 := bstep (se 1 (by rfl) ⟨7134677, by rfl⟩ : syracuseStep 9512903 = 14269355) B14269355
theorem B25367741 : Blo 2225435 25367741 := bstep (se 3 (by rfl) ⟨4756451, by rfl⟩ : syracuseStep 25367741 = 9512903) B9512903
theorem B16911827 : Blo 2225435 16911827 := bstep (se 1 (by rfl) ⟨12683870, by rfl⟩ : syracuseStep 16911827 = 25367741) B25367741
theorem B11274551 : Blo 2225435 11274551 := bstep (se 1 (by rfl) ⟨8455913, by rfl⟩ : syracuseStep 11274551 = 16911827) B16911827
theorem B7516367 : Blo 2225435 7516367 := bstep (se 1 (by rfl) ⟨5637275, by rfl⟩ : syracuseStep 7516367 = 11274551) B11274551
theorem B5010911 : Blo 2225435 5010911 := bstep (se 1 (by rfl) ⟨3758183, by rfl⟩ : syracuseStep 5010911 = 7516367) B7516367
theorem B3340607 : Blo 2225435 3340607 := bstep (se 1 (by rfl) ⟨2505455, by rfl⟩ : syracuseStep 3340607 = 5010911) B5010911
theorem B2227071 : Blo 2225435 2227071 := bstep (se 1 (by rfl) ⟨1670303, by rfl⟩ : syracuseStep 2227071 = 3340607) B3340607
theorem B3340613 : Blo 2225435 3340613 := bbase (se 4 (by rfl) ⟨313182, by rfl⟩ : syracuseStep 3340613 = 626365) (by norm_num)
theorem B2227075 : Blo 2225435 2227075 := bstep (se 1 (by rfl) ⟨1670306, by rfl⟩ : syracuseStep 2227075 = 3340613) B3340613
theorem B3758197 : Blo 2225435 3758197 := bbase (se 5 (by rfl) ⟨176165, by rfl⟩ : syracuseStep 3758197 = 352331) (by norm_num)
theorem B5010929 : Blo 2225435 5010929 := bstep (se 2 (by rfl) ⟨1879098, by rfl⟩ : syracuseStep 5010929 = 3758197) B3758197
theorem B3340619 : Blo 2225435 3340619 := bstep (se 1 (by rfl) ⟨2505464, by rfl⟩ : syracuseStep 3340619 = 5010929) B5010929
theorem B2227079 : Blo 2225435 2227079 := bstep (se 1 (by rfl) ⟨1670309, by rfl⟩ : syracuseStep 2227079 = 3340619) B3340619
theorem B2505469 : Blo 2225435 2505469 := bbase (se 3 (by rfl) ⟨469775, by rfl⟩ : syracuseStep 2505469 = 939551) (by norm_num)
theorem B3340625 : Blo 2225435 3340625 := bstep (se 2 (by rfl) ⟨1252734, by rfl⟩ : syracuseStep 3340625 = 2505469) B2505469
theorem B2227083 : Blo 2225435 2227083 := bstep (se 1 (by rfl) ⟨1670312, by rfl⟩ : syracuseStep 2227083 = 3340625) B3340625
theorem B7516421 : Blo 2225435 7516421 := bbase (se 4 (by rfl) ⟨704664, by rfl⟩ : syracuseStep 7516421 = 1409329) (by norm_num)
theorem B5010947 : Blo 2225435 5010947 := bstep (se 1 (by rfl) ⟨3758210, by rfl⟩ : syracuseStep 5010947 = 7516421) B7516421
theorem B3340631 : Blo 2225435 3340631 := bstep (se 1 (by rfl) ⟨2505473, by rfl⟩ : syracuseStep 3340631 = 5010947) B5010947
theorem B2227087 : Blo 2225435 2227087 := bstep (se 1 (by rfl) ⟨1670315, by rfl⟩ : syracuseStep 2227087 = 3340631) B3340631
theorem B3340637 : Blo 2225435 3340637 := bbase (se 3 (by rfl) ⟨626369, by rfl⟩ : syracuseStep 3340637 = 1252739) (by norm_num)
theorem B2227091 : Blo 2225435 2227091 := bstep (se 1 (by rfl) ⟨1670318, by rfl⟩ : syracuseStep 2227091 = 3340637) B3340637
theorem B5010965 : Blo 2225435 5010965 := bbase (se 6 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 5010965 = 234889) (by norm_num)
theorem B3340643 : Blo 2225435 3340643 := bstep (se 1 (by rfl) ⟨2505482, by rfl⟩ : syracuseStep 3340643 = 5010965) B5010965
theorem B2227095 : Blo 2225435 2227095 := bstep (se 1 (by rfl) ⟨1670321, by rfl⟩ : syracuseStep 2227095 = 3340643) B3340643
theorem B8456021 : Blo 2225435 8456021 := bbase (se 9 (by rfl) ⟨24773, by rfl⟩ : syracuseStep 8456021 = 49547) (by norm_num)
theorem B5637347 : Blo 2225435 5637347 := bstep (se 1 (by rfl) ⟨4228010, by rfl⟩ : syracuseStep 5637347 = 8456021) B8456021
theorem B3758231 : Blo 2225435 3758231 := bstep (se 1 (by rfl) ⟨2818673, by rfl⟩ : syracuseStep 3758231 = 5637347) B5637347
theorem B2505487 : Blo 2225435 2505487 := bstep (se 1 (by rfl) ⟨1879115, by rfl⟩ : syracuseStep 2505487 = 3758231) B3758231
theorem B3340649 : Blo 2225435 3340649 := bstep (se 2 (by rfl) ⟨1252743, by rfl⟩ : syracuseStep 3340649 = 2505487) B2505487
theorem B2227099 : Blo 2225435 2227099 := bstep (se 1 (by rfl) ⟨1670324, by rfl⟩ : syracuseStep 2227099 = 3340649) B3340649
theorem B12684053 : Blo 2225435 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B8456035 : Blo 2225435 8456035 := bstep (se 1 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 8456035 = 12684053) B12684053
theorem B11274713 : Blo 2225435 11274713 := bstep (se 2 (by rfl) ⟨4228017, by rfl⟩ : syracuseStep 11274713 = 8456035) B8456035
theorem B7516475 : Blo 2225435 7516475 := bstep (se 1 (by rfl) ⟨5637356, by rfl⟩ : syracuseStep 7516475 = 11274713) B11274713
theorem B5010983 : Blo 2225435 5010983 := bstep (se 1 (by rfl) ⟨3758237, by rfl⟩ : syracuseStep 5010983 = 7516475) B7516475
theorem B3340655 : Blo 2225435 3340655 := bstep (se 1 (by rfl) ⟨2505491, by rfl⟩ : syracuseStep 3340655 = 5010983) B5010983
theorem B2227103 : Blo 2225435 2227103 := bstep (se 1 (by rfl) ⟨1670327, by rfl⟩ : syracuseStep 2227103 = 3340655) B3340655
theorem B3340661 : Blo 2225435 3340661 := bbase (se 5 (by rfl) ⟨156593, by rfl⟩ : syracuseStep 3340661 = 313187) (by norm_num)
theorem B2227107 : Blo 2225435 2227107 := bstep (se 1 (by rfl) ⟨1670330, by rfl⟩ : syracuseStep 2227107 = 3340661) B3340661
theorem B2378269 : Blo 2225435 2378269 := bbase (se 3 (by rfl) ⟨445925, by rfl⟩ : syracuseStep 2378269 = 891851) (by norm_num)
theorem B3171025 : Blo 2225435 3171025 := bstep (se 2 (by rfl) ⟨1189134, by rfl⟩ : syracuseStep 3171025 = 2378269) B2378269
theorem B4228033 : Blo 2225435 4228033 := bstep (se 2 (by rfl) ⟨1585512, by rfl⟩ : syracuseStep 4228033 = 3171025) B3171025
theorem B5637377 : Blo 2225435 5637377 := bstep (se 2 (by rfl) ⟨2114016, by rfl⟩ : syracuseStep 5637377 = 4228033) B4228033
theorem B3758251 : Blo 2225435 3758251 := bstep (se 1 (by rfl) ⟨2818688, by rfl⟩ : syracuseStep 3758251 = 5637377) B5637377
theorem B5011001 : Blo 2225435 5011001 := bstep (se 2 (by rfl) ⟨1879125, by rfl⟩ : syracuseStep 5011001 = 3758251) B3758251
theorem B3340667 : Blo 2225435 3340667 := bstep (se 1 (by rfl) ⟨2505500, by rfl⟩ : syracuseStep 3340667 = 5011001) B5011001
theorem B2227111 : Blo 2225435 2227111 := bstep (se 1 (by rfl) ⟨1670333, by rfl⟩ : syracuseStep 2227111 = 3340667) B3340667
theorem B2505505 : Blo 2225435 2505505 := bbase (se 2 (by rfl) ⟨939564, by rfl⟩ : syracuseStep 2505505 = 1879129) (by norm_num)
theorem B3340673 : Blo 2225435 3340673 := bstep (se 2 (by rfl) ⟨1252752, by rfl⟩ : syracuseStep 3340673 = 2505505) B2505505
theorem B2227115 : Blo 2225435 2227115 := bstep (se 1 (by rfl) ⟨1670336, by rfl⟩ : syracuseStep 2227115 = 3340673) B3340673
theorem B5637397 : Blo 2225435 5637397 := bbase (se 6 (by rfl) ⟨132126, by rfl⟩ : syracuseStep 5637397 = 264253) (by norm_num)
theorem B7516529 : Blo 2225435 7516529 := bstep (se 2 (by rfl) ⟨2818698, by rfl⟩ : syracuseStep 7516529 = 5637397) B5637397
theorem B5011019 : Blo 2225435 5011019 := bstep (se 1 (by rfl) ⟨3758264, by rfl⟩ : syracuseStep 5011019 = 7516529) B7516529
theorem B3340679 : Blo 2225435 3340679 := bstep (se 1 (by rfl) ⟨2505509, by rfl⟩ : syracuseStep 3340679 = 5011019) B5011019
theorem B2227119 : Blo 2225435 2227119 := bstep (se 1 (by rfl) ⟨1670339, by rfl⟩ : syracuseStep 2227119 = 3340679) B3340679
theorem B3340685 : Blo 2225435 3340685 := bbase (se 3 (by rfl) ⟨626378, by rfl⟩ : syracuseStep 3340685 = 1252757) (by norm_num)
theorem B2227123 : Blo 2225435 2227123 := bstep (se 1 (by rfl) ⟨1670342, by rfl⟩ : syracuseStep 2227123 = 3340685) B3340685
theorem B5011037 : Blo 2225435 5011037 := bbase (se 3 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 5011037 = 1879139) (by norm_num)
theorem B3340691 : Blo 2225435 3340691 := bstep (se 1 (by rfl) ⟨2505518, by rfl⟩ : syracuseStep 3340691 = 5011037) B5011037
theorem B2227127 : Blo 2225435 2227127 := bstep (se 1 (by rfl) ⟨1670345, by rfl⟩ : syracuseStep 2227127 = 3340691) B3340691
theorem B3758285 : Blo 2225435 3758285 := bbase (se 3 (by rfl) ⟨704678, by rfl⟩ : syracuseStep 3758285 = 1409357) (by norm_num)
theorem B2505523 : Blo 2225435 2505523 := bstep (se 1 (by rfl) ⟨1879142, by rfl⟩ : syracuseStep 2505523 = 3758285) B3758285
theorem B3340697 : Blo 2225435 3340697 := bstep (se 2 (by rfl) ⟨1252761, by rfl⟩ : syracuseStep 3340697 = 2505523) B2505523
theorem B2227131 : Blo 2225435 2227131 := bstep (se 1 (by rfl) ⟨1670348, by rfl⟩ : syracuseStep 2227131 = 3340697) B3340697
theorem B2675581 : Blo 2225435 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B14269765 : Blo 2225435 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B19026353 : Blo 2225435 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B12684235 : Blo 2225435 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B16912313 : Blo 2225435 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B11274875 : Blo 2225435 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B7516583 : Blo 2225435 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B5011055 : Blo 2225435 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B3340703 : Blo 2225435 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B2227135 : Blo 2225435 2227135 := bstep (se 1 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 2227135 = 3340703) B3340703
theorem B3340709 : Blo 2225435 3340709 := bbase (se 4 (by rfl) ⟨313191, by rfl⟩ : syracuseStep 3340709 = 626383) (by norm_num)
theorem B2227139 : Blo 2225435 2227139 := bstep (se 1 (by rfl) ⟨1670354, by rfl⟩ : syracuseStep 2227139 = 3340709) B3340709
theorem B2818729 : Blo 2225435 2818729 := bbase (se 2 (by rfl) ⟨1057023, by rfl⟩ : syracuseStep 2818729 = 2114047) (by norm_num)
theorem B3758305 : Blo 2225435 3758305 := bstep (se 2 (by rfl) ⟨1409364, by rfl⟩ : syracuseStep 3758305 = 2818729) B2818729
theorem B5011073 : Blo 2225435 5011073 := bstep (se 2 (by rfl) ⟨1879152, by rfl⟩ : syracuseStep 5011073 = 3758305) B3758305
theorem B3340715 : Blo 2225435 3340715 := bstep (se 1 (by rfl) ⟨2505536, by rfl⟩ : syracuseStep 3340715 = 5011073) B5011073
theorem B2227143 : Blo 2225435 2227143 := bstep (se 1 (by rfl) ⟨1670357, by rfl⟩ : syracuseStep 2227143 = 3340715) B3340715
theorem B2505541 : Blo 2225435 2505541 := bbase (se 4 (by rfl) ⟨234894, by rfl⟩ : syracuseStep 2505541 = 469789) (by norm_num)
theorem B3340721 : Blo 2225435 3340721 := bstep (se 2 (by rfl) ⟨1252770, by rfl⟩ : syracuseStep 3340721 = 2505541) B2505541
theorem B2227147 : Blo 2225435 2227147 := bstep (se 1 (by rfl) ⟨1670360, by rfl⟩ : syracuseStep 2227147 = 3340721) B3340721
theorem B4228109 : Blo 2225435 4228109 := bbase (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) (by norm_num)
theorem B2818739 : Blo 2225435 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B7516637 : Blo 2225435 7516637 := bstep (se 3 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 7516637 = 2818739) B2818739
theorem B5011091 : Blo 2225435 5011091 := bstep (se 1 (by rfl) ⟨3758318, by rfl⟩ : syracuseStep 5011091 = 7516637) B7516637
theorem B3340727 : Blo 2225435 3340727 := bstep (se 1 (by rfl) ⟨2505545, by rfl⟩ : syracuseStep 3340727 = 5011091) B5011091
theorem B2227151 : Blo 2225435 2227151 := bstep (se 1 (by rfl) ⟨1670363, by rfl⟩ : syracuseStep 2227151 = 3340727) B3340727
theorem B3340733 : Blo 2225435 3340733 := bbase (se 3 (by rfl) ⟨626387, by rfl⟩ : syracuseStep 3340733 = 1252775) (by norm_num)
theorem B2227155 : Blo 2225435 2227155 := bstep (se 1 (by rfl) ⟨1670366, by rfl⟩ : syracuseStep 2227155 = 3340733) B3340733
theorem B5011109 : Blo 2225435 5011109 := bbase (se 4 (by rfl) ⟨469791, by rfl⟩ : syracuseStep 5011109 = 939583) (by norm_num)
theorem B3340739 : Blo 2225435 3340739 := bstep (se 1 (by rfl) ⟨2505554, by rfl⟩ : syracuseStep 3340739 = 5011109) B5011109
theorem B2227159 : Blo 2225435 2227159 := bstep (se 1 (by rfl) ⟨1670369, by rfl⟩ : syracuseStep 2227159 = 3340739) B3340739
theorem B5637509 : Blo 2225435 5637509 := bbase (se 4 (by rfl) ⟨528516, by rfl⟩ : syracuseStep 5637509 = 1057033) (by norm_num)
theorem B3758339 : Blo 2225435 3758339 := bstep (se 1 (by rfl) ⟨2818754, by rfl⟩ : syracuseStep 3758339 = 5637509) B5637509
theorem B2505559 : Blo 2225435 2505559 := bstep (se 1 (by rfl) ⟨1879169, by rfl⟩ : syracuseStep 2505559 = 3758339) B3758339
theorem B3340745 : Blo 2225435 3340745 := bstep (se 2 (by rfl) ⟨1252779, by rfl⟩ : syracuseStep 3340745 = 2505559) B2505559
theorem B2227163 : Blo 2225435 2227163 := bstep (se 1 (by rfl) ⟨1670372, by rfl⟩ : syracuseStep 2227163 = 3340745) B3340745
theorem B3567493 : Blo 2225435 3567493 := bbase (se 4 (by rfl) ⟨334452, by rfl⟩ : syracuseStep 3567493 = 668905) (by norm_num)
theorem B4756657 : Blo 2225435 4756657 := bstep (se 2 (by rfl) ⟨1783746, by rfl⟩ : syracuseStep 4756657 = 3567493) B3567493
theorem B6342209 : Blo 2225435 6342209 := bstep (se 2 (by rfl) ⟨2378328, by rfl⟩ : syracuseStep 6342209 = 4756657) B4756657
theorem B4228139 : Blo 2225435 4228139 := bstep (se 1 (by rfl) ⟨3171104, by rfl⟩ : syracuseStep 4228139 = 6342209) B6342209
theorem B11275037 : Blo 2225435 11275037 := bstep (se 3 (by rfl) ⟨2114069, by rfl⟩ : syracuseStep 11275037 = 4228139) B4228139
theorem B7516691 : Blo 2225435 7516691 := bstep (se 1 (by rfl) ⟨5637518, by rfl⟩ : syracuseStep 7516691 = 11275037) B11275037
theorem B5011127 : Blo 2225435 5011127 := bstep (se 1 (by rfl) ⟨3758345, by rfl⟩ : syracuseStep 5011127 = 7516691) B7516691
theorem B3340751 : Blo 2225435 3340751 := bstep (se 1 (by rfl) ⟨2505563, by rfl⟩ : syracuseStep 3340751 = 5011127) B5011127
theorem B2227167 : Blo 2225435 2227167 := bstep (se 1 (by rfl) ⟨1670375, by rfl⟩ : syracuseStep 2227167 = 3340751) B3340751
theorem B3340757 : Blo 2225435 3340757 := bbase (se 7 (by rfl) ⟨39149, by rfl⟩ : syracuseStep 3340757 = 78299) (by norm_num)
theorem B2227171 : Blo 2225435 2227171 := bstep (se 1 (by rfl) ⟨1670378, by rfl⟩ : syracuseStep 2227171 = 3340757) B3340757
theorem B8456309 : Blo 2225435 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B5637539 : Blo 2225435 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B3758359 : Blo 2225435 3758359 := bstep (se 1 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 3758359 = 5637539) B5637539
theorem B5011145 : Blo 2225435 5011145 := bstep (se 2 (by rfl) ⟨1879179, by rfl⟩ : syracuseStep 5011145 = 3758359) B3758359
theorem B3340763 : Blo 2225435 3340763 := bstep (se 1 (by rfl) ⟨2505572, by rfl⟩ : syracuseStep 3340763 = 5011145) B5011145
theorem B2227175 : Blo 2225435 2227175 := bstep (se 1 (by rfl) ⟨1670381, by rfl⟩ : syracuseStep 2227175 = 3340763) B3340763
theorem B2505577 : Blo 2225435 2505577 := bbase (se 2 (by rfl) ⟨939591, by rfl⟩ : syracuseStep 2505577 = 1879183) (by norm_num)
theorem B3340769 : Blo 2225435 3340769 := bstep (se 2 (by rfl) ⟨1252788, by rfl⟩ : syracuseStep 3340769 = 2505577) B2505577
theorem B2227179 : Blo 2225435 2227179 := bstep (se 1 (by rfl) ⟨1670384, by rfl⟩ : syracuseStep 2227179 = 3340769) B3340769
theorem B3386357 : Blo 2225435 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2257571 : Blo 2225435 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B6020189 : Blo 2225435 6020189 := bstep (se 3 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 6020189 = 2257571) B2257571
theorem B4013459 : Blo 2225435 4013459 := bstep (se 1 (by rfl) ⟨3010094, by rfl⟩ : syracuseStep 4013459 = 6020189) B6020189
theorem B2675639 : Blo 2225435 2675639 := bstep (se 1 (by rfl) ⟨2006729, by rfl⟩ : syracuseStep 2675639 = 4013459) B4013459
theorem B7135037 : Blo 2225435 7135037 := bstep (se 3 (by rfl) ⟨1337819, by rfl⟩ : syracuseStep 7135037 = 2675639) B2675639
theorem B4756691 : Blo 2225435 4756691 := bstep (se 1 (by rfl) ⟨3567518, by rfl⟩ : syracuseStep 4756691 = 7135037) B7135037
theorem B12684509 : Blo 2225435 12684509 := bstep (se 3 (by rfl) ⟨2378345, by rfl⟩ : syracuseStep 12684509 = 4756691) B4756691
theorem B8456339 : Blo 2225435 8456339 := bstep (se 1 (by rfl) ⟨6342254, by rfl⟩ : syracuseStep 8456339 = 12684509) B12684509
theorem B5637559 : Blo 2225435 5637559 := bstep (se 1 (by rfl) ⟨4228169, by rfl⟩ : syracuseStep 5637559 = 8456339) B8456339
theorem B7516745 : Blo 2225435 7516745 := bstep (se 2 (by rfl) ⟨2818779, by rfl⟩ : syracuseStep 7516745 = 5637559) B5637559
theorem B5011163 : Blo 2225435 5011163 := bstep (se 1 (by rfl) ⟨3758372, by rfl⟩ : syracuseStep 5011163 = 7516745) B7516745
theorem B3340775 : Blo 2225435 3340775 := bstep (se 1 (by rfl) ⟨2505581, by rfl⟩ : syracuseStep 3340775 = 5011163) B5011163
theorem B2227183 : Blo 2225435 2227183 := bstep (se 1 (by rfl) ⟨1670387, by rfl⟩ : syracuseStep 2227183 = 3340775) B3340775
theorem B3340781 : Blo 2225435 3340781 := bbase (se 3 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 3340781 = 1252793) (by norm_num)
theorem B2227187 : Blo 2225435 2227187 := bstep (se 1 (by rfl) ⟨1670390, by rfl⟩ : syracuseStep 2227187 = 3340781) B3340781
theorem B5011181 : Blo 2225435 5011181 := bbase (se 3 (by rfl) ⟨939596, by rfl⟩ : syracuseStep 5011181 = 1879193) (by norm_num)
theorem B3340787 : Blo 2225435 3340787 := bstep (se 1 (by rfl) ⟨2505590, by rfl⟩ : syracuseStep 3340787 = 5011181) B5011181
theorem B2227191 : Blo 2225435 2227191 := bstep (se 1 (by rfl) ⟨1670393, by rfl⟩ : syracuseStep 2227191 = 3340787) B3340787
theorem B5351309 : Blo 2225435 5351309 := bbase (se 3 (by rfl) ⟨1003370, by rfl⟩ : syracuseStep 5351309 = 2006741) (by norm_num)
theorem B3567539 : Blo 2225435 3567539 := bstep (se 1 (by rfl) ⟨2675654, by rfl⟩ : syracuseStep 3567539 = 5351309) B5351309
theorem B2378359 : Blo 2225435 2378359 := bstep (se 1 (by rfl) ⟨1783769, by rfl⟩ : syracuseStep 2378359 = 3567539) B3567539
theorem B3171145 : Blo 2225435 3171145 := bstep (se 2 (by rfl) ⟨1189179, by rfl⟩ : syracuseStep 3171145 = 2378359) B2378359
theorem B4228193 : Blo 2225435 4228193 := bstep (se 2 (by rfl) ⟨1585572, by rfl⟩ : syracuseStep 4228193 = 3171145) B3171145
theorem B2818795 : Blo 2225435 2818795 := bstep (se 1 (by rfl) ⟨2114096, by rfl⟩ : syracuseStep 2818795 = 4228193) B4228193
theorem B3758393 : Blo 2225435 3758393 := bstep (se 2 (by rfl) ⟨1409397, by rfl⟩ : syracuseStep 3758393 = 2818795) B2818795
theorem B2505595 : Blo 2225435 2505595 := bstep (se 1 (by rfl) ⟨1879196, by rfl⟩ : syracuseStep 2505595 = 3758393) B3758393
theorem B3340793 : Blo 2225435 3340793 := bstep (se 2 (by rfl) ⟨1252797, by rfl⟩ : syracuseStep 3340793 = 2505595) B2505595
theorem B2227195 : Blo 2225435 2227195 := bstep (se 1 (by rfl) ⟨1670396, by rfl⟩ : syracuseStep 2227195 = 3340793) B3340793
theorem B44586773 : Blo 2225435 44586773 := bbase (se 6 (by rfl) ⟨1045002, by rfl⟩ : syracuseStep 44586773 = 2090005) (by norm_num)
theorem B29724515 : Blo 2225435 29724515 := bstep (se 1 (by rfl) ⟨22293386, by rfl⟩ : syracuseStep 29724515 = 44586773) B44586773
theorem B19816343 : Blo 2225435 19816343 := bstep (se 1 (by rfl) ⟨14862257, by rfl⟩ : syracuseStep 19816343 = 29724515) B29724515
theorem B13210895 : Blo 2225435 13210895 := bstep (se 1 (by rfl) ⟨9908171, by rfl⟩ : syracuseStep 13210895 = 19816343) B19816343
theorem B8807263 : Blo 2225435 8807263 := bstep (se 1 (by rfl) ⟨6605447, by rfl⟩ : syracuseStep 8807263 = 13210895) B13210895
theorem B46972069 : Blo 2225435 46972069 := bstep (se 4 (by rfl) ⟨4403631, by rfl⟩ : syracuseStep 46972069 = 8807263) B8807263
theorem B250517701 : Blo 2225435 250517701 := bstep (se 4 (by rfl) ⟨23486034, by rfl⟩ : syracuseStep 250517701 = 46972069) B46972069
theorem B334023601 : Blo 2225435 334023601 := bstep (se 2 (by rfl) ⟨125258850, by rfl⟩ : syracuseStep 334023601 = 250517701) B250517701
theorem B445364801 : Blo 2225435 445364801 := bstep (se 2 (by rfl) ⟨167011800, by rfl⟩ : syracuseStep 445364801 = 334023601) B334023601
theorem B296909867 : Blo 2225435 296909867 := bstep (se 1 (by rfl) ⟨222682400, by rfl⟩ : syracuseStep 296909867 = 445364801) B445364801
theorem B197939911 : Blo 2225435 197939911 := bstep (se 1 (by rfl) ⟨148454933, by rfl⟩ : syracuseStep 197939911 = 296909867) B296909867
theorem B263919881 : Blo 2225435 263919881 := bstep (se 2 (by rfl) ⟨98969955, by rfl⟩ : syracuseStep 263919881 = 197939911) B197939911
theorem B175946587 : Blo 2225435 175946587 := bstep (se 1 (by rfl) ⟨131959940, by rfl⟩ : syracuseStep 175946587 = 263919881) B263919881
theorem B938381797 : Blo 2225435 938381797 := bstep (se 4 (by rfl) ⟨87973293, by rfl⟩ : syracuseStep 938381797 = 175946587) B175946587
theorem B1251175729 : Blo 2225435 1251175729 := bstep (se 2 (by rfl) ⟨469190898, by rfl⟩ : syracuseStep 1251175729 = 938381797) B938381797
theorem B1668234305 : Blo 2225435 1668234305 := bstep (se 2 (by rfl) ⟨625587864, by rfl⟩ : syracuseStep 1668234305 = 1251175729) B1251175729
theorem B1112156203 : Blo 2225435 1112156203 := bstep (se 1 (by rfl) ⟨834117152, by rfl⟩ : syracuseStep 1112156203 = 1668234305) B1668234305
theorem B1482874937 : Blo 2225435 1482874937 := bstep (se 2 (by rfl) ⟨556078101, by rfl⟩ : syracuseStep 1482874937 = 1112156203) B1112156203
theorem B988583291 : Blo 2225435 988583291 := bstep (se 1 (by rfl) ⟨741437468, by rfl⟩ : syracuseStep 988583291 = 1482874937) B1482874937
theorem B659055527 : Blo 2225435 659055527 := bstep (se 1 (by rfl) ⟨494291645, by rfl⟩ : syracuseStep 659055527 = 988583291) B988583291
theorem B439370351 : Blo 2225435 439370351 := bstep (se 1 (by rfl) ⟨329527763, by rfl⟩ : syracuseStep 439370351 = 659055527) B659055527
theorem B292913567 : Blo 2225435 292913567 := bstep (se 1 (by rfl) ⟨219685175, by rfl⟩ : syracuseStep 292913567 = 439370351) B439370351
theorem B195275711 : Blo 2225435 195275711 := bstep (se 1 (by rfl) ⟨146456783, by rfl⟩ : syracuseStep 195275711 = 292913567) B292913567
theorem B130183807 : Blo 2225435 130183807 := bstep (se 1 (by rfl) ⟨97637855, by rfl⟩ : syracuseStep 130183807 = 195275711) B195275711
theorem B173578409 : Blo 2225435 173578409 := bstep (se 2 (by rfl) ⟨65091903, by rfl⟩ : syracuseStep 173578409 = 130183807) B130183807
theorem B115718939 : Blo 2225435 115718939 := bstep (se 1 (by rfl) ⟨86789204, by rfl⟩ : syracuseStep 115718939 = 173578409) B173578409
theorem B77145959 : Blo 2225435 77145959 := bstep (se 1 (by rfl) ⟨57859469, by rfl⟩ : syracuseStep 77145959 = 115718939) B115718939
theorem B51430639 : Blo 2225435 51430639 := bstep (se 1 (by rfl) ⟨38572979, by rfl⟩ : syracuseStep 51430639 = 77145959) B77145959
theorem B68574185 : Blo 2225435 68574185 := bstep (se 2 (by rfl) ⟨25715319, by rfl⟩ : syracuseStep 68574185 = 51430639) B51430639
theorem B45716123 : Blo 2225435 45716123 := bstep (se 1 (by rfl) ⟨34287092, by rfl⟩ : syracuseStep 45716123 = 68574185) B68574185
theorem B121909661 : Blo 2225435 121909661 := bstep (se 3 (by rfl) ⟨22858061, by rfl⟩ : syracuseStep 121909661 = 45716123) B45716123
theorem B81273107 : Blo 2225435 81273107 := bstep (se 1 (by rfl) ⟨60954830, by rfl⟩ : syracuseStep 81273107 = 121909661) B121909661
theorem B54182071 : Blo 2225435 54182071 := bstep (se 1 (by rfl) ⟨40636553, by rfl⟩ : syracuseStep 54182071 = 81273107) B81273107
theorem B72242761 : Blo 2225435 72242761 := bstep (se 2 (by rfl) ⟨27091035, by rfl⟩ : syracuseStep 72242761 = 54182071) B54182071
theorem B96323681 : Blo 2225435 96323681 := bstep (se 2 (by rfl) ⟨36121380, by rfl⟩ : syracuseStep 96323681 = 72242761) B72242761
theorem B64215787 : Blo 2225435 64215787 := bstep (se 1 (by rfl) ⟨48161840, by rfl⟩ : syracuseStep 64215787 = 96323681) B96323681
theorem B85621049 : Blo 2225435 85621049 := bstep (se 2 (by rfl) ⟨32107893, by rfl⟩ : syracuseStep 85621049 = 64215787) B64215787
theorem B57080699 : Blo 2225435 57080699 := bstep (se 1 (by rfl) ⟨42810524, by rfl⟩ : syracuseStep 57080699 = 85621049) B85621049
theorem B38053799 : Blo 2225435 38053799 := bstep (se 1 (by rfl) ⟨28540349, by rfl⟩ : syracuseStep 38053799 = 57080699) B57080699
theorem B25369199 : Blo 2225435 25369199 := bstep (se 1 (by rfl) ⟨19026899, by rfl⟩ : syracuseStep 25369199 = 38053799) B38053799
theorem B16912799 : Blo 2225435 16912799 := bstep (se 1 (by rfl) ⟨12684599, by rfl⟩ : syracuseStep 16912799 = 25369199) B25369199
theorem B11275199 : Blo 2225435 11275199 := bstep (se 1 (by rfl) ⟨8456399, by rfl⟩ : syracuseStep 11275199 = 16912799) B16912799
theorem B7516799 : Blo 2225435 7516799 := bstep (se 1 (by rfl) ⟨5637599, by rfl⟩ : syracuseStep 7516799 = 11275199) B11275199
theorem B5011199 : Blo 2225435 5011199 := bstep (se 1 (by rfl) ⟨3758399, by rfl⟩ : syracuseStep 5011199 = 7516799) B7516799
theorem B3340799 : Blo 2225435 3340799 := bstep (se 1 (by rfl) ⟨2505599, by rfl⟩ : syracuseStep 3340799 = 5011199) B5011199
theorem B2227199 : Blo 2225435 2227199 := bstep (se 1 (by rfl) ⟨1670399, by rfl⟩ : syracuseStep 2227199 = 3340799) B3340799
theorem B3340805 : Blo 2225435 3340805 := bbase (se 4 (by rfl) ⟨313200, by rfl⟩ : syracuseStep 3340805 = 626401) (by norm_num)
theorem B2227203 : Blo 2225435 2227203 := bstep (se 1 (by rfl) ⟨1670402, by rfl⟩ : syracuseStep 2227203 = 3340805) B3340805
theorem B3758413 : Blo 2225435 3758413 := bbase (se 3 (by rfl) ⟨704702, by rfl⟩ : syracuseStep 3758413 = 1409405) (by norm_num)
theorem B5011217 : Blo 2225435 5011217 := bstep (se 2 (by rfl) ⟨1879206, by rfl⟩ : syracuseStep 5011217 = 3758413) B3758413
theorem B3340811 : Blo 2225435 3340811 := bstep (se 1 (by rfl) ⟨2505608, by rfl⟩ : syracuseStep 3340811 = 5011217) B5011217
theorem B2227207 : Blo 2225435 2227207 := bstep (se 1 (by rfl) ⟨1670405, by rfl⟩ : syracuseStep 2227207 = 3340811) B3340811
theorem B2505613 : Blo 2225435 2505613 := bbase (se 3 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 2505613 = 939605) (by norm_num)
theorem B3340817 : Blo 2225435 3340817 := bstep (se 2 (by rfl) ⟨1252806, by rfl⟩ : syracuseStep 3340817 = 2505613) B2505613
theorem B2227211 : Blo 2225435 2227211 := bstep (se 1 (by rfl) ⟨1670408, by rfl⟩ : syracuseStep 2227211 = 3340817) B3340817
theorem B7516853 : Blo 2225435 7516853 := bbase (se 5 (by rfl) ⟨352352, by rfl⟩ : syracuseStep 7516853 = 704705) (by norm_num)
theorem B5011235 : Blo 2225435 5011235 := bstep (se 1 (by rfl) ⟨3758426, by rfl⟩ : syracuseStep 5011235 = 7516853) B7516853
theorem B3340823 : Blo 2225435 3340823 := bstep (se 1 (by rfl) ⟨2505617, by rfl⟩ : syracuseStep 3340823 = 5011235) B5011235
theorem B2227215 : Blo 2225435 2227215 := bstep (se 1 (by rfl) ⟨1670411, by rfl⟩ : syracuseStep 2227215 = 3340823) B3340823
theorem B3340829 : Blo 2225435 3340829 := bbase (se 3 (by rfl) ⟨626405, by rfl⟩ : syracuseStep 3340829 = 1252811) (by norm_num)
theorem B2227219 : Blo 2225435 2227219 := bstep (se 1 (by rfl) ⟨1670414, by rfl⟩ : syracuseStep 2227219 = 3340829) B3340829
theorem B5011253 : Blo 2225435 5011253 := bbase (se 5 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 5011253 = 469805) (by norm_num)
theorem B3340835 : Blo 2225435 3340835 := bstep (se 1 (by rfl) ⟨2505626, by rfl⟩ : syracuseStep 3340835 = 5011253) B5011253
theorem B2227223 : Blo 2225435 2227223 := bstep (se 1 (by rfl) ⟨1670417, by rfl⟩ : syracuseStep 2227223 = 3340835) B3340835
theorem B14270357 : Blo 2225435 14270357 := bbase (se 6 (by rfl) ⟨334461, by rfl⟩ : syracuseStep 14270357 = 668923) (by norm_num)
theorem B9513571 : Blo 2225435 9513571 := bstep (se 1 (by rfl) ⟨7135178, by rfl⟩ : syracuseStep 9513571 = 14270357) B14270357
theorem B12684761 : Blo 2225435 12684761 := bstep (se 2 (by rfl) ⟨4756785, by rfl⟩ : syracuseStep 12684761 = 9513571) B9513571
theorem B8456507 : Blo 2225435 8456507 := bstep (se 1 (by rfl) ⟨6342380, by rfl⟩ : syracuseStep 8456507 = 12684761) B12684761
theorem B5637671 : Blo 2225435 5637671 := bstep (se 1 (by rfl) ⟨4228253, by rfl⟩ : syracuseStep 5637671 = 8456507) B8456507
theorem B3758447 : Blo 2225435 3758447 := bstep (se 1 (by rfl) ⟨2818835, by rfl⟩ : syracuseStep 3758447 = 5637671) B5637671
theorem B2505631 : Blo 2225435 2505631 := bstep (se 1 (by rfl) ⟨1879223, by rfl⟩ : syracuseStep 2505631 = 3758447) B3758447
theorem B3340841 : Blo 2225435 3340841 := bstep (se 2 (by rfl) ⟨1252815, by rfl⟩ : syracuseStep 3340841 = 2505631) B2505631
theorem B2227227 : Blo 2225435 2227227 := bstep (se 1 (by rfl) ⟨1670420, by rfl⟩ : syracuseStep 2227227 = 3340841) B3340841
theorem B8688853 : Blo 2225435 8688853 := bbase (se 7 (by rfl) ⟨101822, by rfl⟩ : syracuseStep 8688853 = 203645) (by norm_num)
theorem B46340549 : Blo 2225435 46340549 := bstep (se 4 (by rfl) ⟨4344426, by rfl⟩ : syracuseStep 46340549 = 8688853) B8688853
theorem B30893699 : Blo 2225435 30893699 := bstep (se 1 (by rfl) ⟨23170274, by rfl⟩ : syracuseStep 30893699 = 46340549) B46340549
theorem B20595799 : Blo 2225435 20595799 := bstep (se 1 (by rfl) ⟨15446849, by rfl⟩ : syracuseStep 20595799 = 30893699) B30893699
theorem B27461065 : Blo 2225435 27461065 := bstep (se 2 (by rfl) ⟨10297899, by rfl⟩ : syracuseStep 27461065 = 20595799) B20595799
theorem B36614753 : Blo 2225435 36614753 := bstep (se 2 (by rfl) ⟨13730532, by rfl⟩ : syracuseStep 36614753 = 27461065) B27461065
theorem B24409835 : Blo 2225435 24409835 := bstep (se 1 (by rfl) ⟨18307376, by rfl⟩ : syracuseStep 24409835 = 36614753) B36614753
theorem B16273223 : Blo 2225435 16273223 := bstep (se 1 (by rfl) ⟨12204917, by rfl⟩ : syracuseStep 16273223 = 24409835) B24409835
theorem B10848815 : Blo 2225435 10848815 := bstep (se 1 (by rfl) ⟨8136611, by rfl⟩ : syracuseStep 10848815 = 16273223) B16273223
theorem B7232543 : Blo 2225435 7232543 := bstep (se 1 (by rfl) ⟨5424407, by rfl⟩ : syracuseStep 7232543 = 10848815) B10848815
theorem B4821695 : Blo 2225435 4821695 := bstep (se 1 (by rfl) ⟨3616271, by rfl⟩ : syracuseStep 4821695 = 7232543) B7232543
theorem B3214463 : Blo 2225435 3214463 := bstep (se 1 (by rfl) ⟨2410847, by rfl⟩ : syracuseStep 3214463 = 4821695) B4821695
theorem B8571901 : Blo 2225435 8571901 := bstep (se 3 (by rfl) ⟨1607231, by rfl⟩ : syracuseStep 8571901 = 3214463) B3214463
theorem B11429201 : Blo 2225435 11429201 := bstep (se 2 (by rfl) ⟨4285950, by rfl⟩ : syracuseStep 11429201 = 8571901) B8571901
theorem B7619467 : Blo 2225435 7619467 := bstep (se 1 (by rfl) ⟨5714600, by rfl⟩ : syracuseStep 7619467 = 11429201) B11429201
theorem B10159289 : Blo 2225435 10159289 := bstep (se 2 (by rfl) ⟨3809733, by rfl⟩ : syracuseStep 10159289 = 7619467) B7619467
theorem B6772859 : Blo 2225435 6772859 := bstep (se 1 (by rfl) ⟨5079644, by rfl⟩ : syracuseStep 6772859 = 10159289) B10159289
theorem B4515239 : Blo 2225435 4515239 := bstep (se 1 (by rfl) ⟨3386429, by rfl⟩ : syracuseStep 4515239 = 6772859) B6772859
theorem B3010159 : Blo 2225435 3010159 := bstep (se 1 (by rfl) ⟨2257619, by rfl⟩ : syracuseStep 3010159 = 4515239) B4515239
theorem B4013545 : Blo 2225435 4013545 := bstep (se 2 (by rfl) ⟨1505079, by rfl⟩ : syracuseStep 4013545 = 3010159) B3010159
theorem B5351393 : Blo 2225435 5351393 := bstep (se 2 (by rfl) ⟨2006772, by rfl⟩ : syracuseStep 5351393 = 4013545) B4013545
theorem B14270381 : Blo 2225435 14270381 := bstep (se 3 (by rfl) ⟨2675696, by rfl⟩ : syracuseStep 14270381 = 5351393) B5351393
theorem B9513587 : Blo 2225435 9513587 := bstep (se 1 (by rfl) ⟨7135190, by rfl⟩ : syracuseStep 9513587 = 14270381) B14270381
theorem B6342391 : Blo 2225435 6342391 := bstep (se 1 (by rfl) ⟨4756793, by rfl⟩ : syracuseStep 6342391 = 9513587) B9513587
theorem B8456521 : Blo 2225435 8456521 := bstep (se 2 (by rfl) ⟨3171195, by rfl⟩ : syracuseStep 8456521 = 6342391) B6342391
theorem B11275361 : Blo 2225435 11275361 := bstep (se 2 (by rfl) ⟨4228260, by rfl⟩ : syracuseStep 11275361 = 8456521) B8456521
theorem B7516907 : Blo 2225435 7516907 := bstep (se 1 (by rfl) ⟨5637680, by rfl⟩ : syracuseStep 7516907 = 11275361) B11275361
theorem B5011271 : Blo 2225435 5011271 := bstep (se 1 (by rfl) ⟨3758453, by rfl⟩ : syracuseStep 5011271 = 7516907) B7516907
theorem B3340847 : Blo 2225435 3340847 := bstep (se 1 (by rfl) ⟨2505635, by rfl⟩ : syracuseStep 3340847 = 5011271) B5011271
theorem B2227231 : Blo 2225435 2227231 := bstep (se 1 (by rfl) ⟨1670423, by rfl⟩ : syracuseStep 2227231 = 3340847) B3340847
theorem B3340853 : Blo 2225435 3340853 := bbase (se 5 (by rfl) ⟨156602, by rfl⟩ : syracuseStep 3340853 = 313205) (by norm_num)
theorem B2227235 : Blo 2225435 2227235 := bstep (se 1 (by rfl) ⟨1670426, by rfl⟩ : syracuseStep 2227235 = 3340853) B3340853
theorem B5637701 : Blo 2225435 5637701 := bbase (se 4 (by rfl) ⟨528534, by rfl⟩ : syracuseStep 5637701 = 1057069) (by norm_num)
theorem B3758467 : Blo 2225435 3758467 := bstep (se 1 (by rfl) ⟨2818850, by rfl⟩ : syracuseStep 3758467 = 5637701) B5637701
theorem B5011289 : Blo 2225435 5011289 := bstep (se 2 (by rfl) ⟨1879233, by rfl⟩ : syracuseStep 5011289 = 3758467) B3758467
theorem B3340859 : Blo 2225435 3340859 := bstep (se 1 (by rfl) ⟨2505644, by rfl⟩ : syracuseStep 3340859 = 5011289) B5011289
theorem B2227239 : Blo 2225435 2227239 := bstep (se 1 (by rfl) ⟨1670429, by rfl⟩ : syracuseStep 2227239 = 3340859) B3340859
theorem B2505649 : Blo 2225435 2505649 := bbase (se 2 (by rfl) ⟨939618, by rfl⟩ : syracuseStep 2505649 = 1879237) (by norm_num)
theorem B3340865 : Blo 2225435 3340865 := bstep (se 2 (by rfl) ⟨1252824, by rfl⟩ : syracuseStep 3340865 = 2505649) B2505649
theorem B2227243 : Blo 2225435 2227243 := bstep (se 1 (by rfl) ⟨1670432, by rfl⟩ : syracuseStep 2227243 = 3340865) B3340865
theorem B6342437 : Blo 2225435 6342437 := bbase (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) (by norm_num)
theorem B4228291 : Blo 2225435 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B5637721 : Blo 2225435 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B7516961 : Blo 2225435 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B5011307 : Blo 2225435 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B3340871 : Blo 2225435 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B2227247 : Blo 2225435 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B3340877 : Blo 2225435 3340877 := bbase (se 3 (by rfl) ⟨626414, by rfl⟩ : syracuseStep 3340877 = 1252829) (by norm_num)
theorem B2227251 : Blo 2225435 2227251 := bstep (se 1 (by rfl) ⟨1670438, by rfl⟩ : syracuseStep 2227251 = 3340877) B3340877
theorem B5011325 : Blo 2225435 5011325 := bbase (se 3 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 5011325 = 1879247) (by norm_num)
theorem B3340883 : Blo 2225435 3340883 := bstep (se 1 (by rfl) ⟨2505662, by rfl⟩ : syracuseStep 3340883 = 5011325) B5011325
theorem B2227255 : Blo 2225435 2227255 := bstep (se 1 (by rfl) ⟨1670441, by rfl⟩ : syracuseStep 2227255 = 3340883) B3340883
theorem B3758501 : Blo 2225435 3758501 := bbase (se 4 (by rfl) ⟨352359, by rfl⟩ : syracuseStep 3758501 = 704719) (by norm_num)
theorem B2505667 : Blo 2225435 2505667 := bstep (se 1 (by rfl) ⟨1879250, by rfl⟩ : syracuseStep 2505667 = 3758501) B3758501
theorem B3340889 : Blo 2225435 3340889 := bstep (se 2 (by rfl) ⟨1252833, by rfl⟩ : syracuseStep 3340889 = 2505667) B2505667
theorem B2227259 : Blo 2225435 2227259 := bstep (se 1 (by rfl) ⟨1670444, by rfl⟩ : syracuseStep 2227259 = 3340889) B3340889
theorem B11429365 : Blo 2225435 11429365 := bbase (se 5 (by rfl) ⟨535751, by rfl⟩ : syracuseStep 11429365 = 1071503) (by norm_num)
theorem B15239153 : Blo 2225435 15239153 := bstep (se 2 (by rfl) ⟨5714682, by rfl⟩ : syracuseStep 15239153 = 11429365) B11429365
theorem B10159435 : Blo 2225435 10159435 := bstep (se 1 (by rfl) ⟨7619576, by rfl⟩ : syracuseStep 10159435 = 15239153) B15239153
theorem B13545913 : Blo 2225435 13545913 := bstep (se 2 (by rfl) ⟨5079717, by rfl⟩ : syracuseStep 13545913 = 10159435) B10159435
theorem B18061217 : Blo 2225435 18061217 := bstep (se 2 (by rfl) ⟨6772956, by rfl⟩ : syracuseStep 18061217 = 13545913) B13545913
theorem B12040811 : Blo 2225435 12040811 := bstep (se 1 (by rfl) ⟨9030608, by rfl⟩ : syracuseStep 12040811 = 18061217) B18061217
theorem B8027207 : Blo 2225435 8027207 := bstep (se 1 (by rfl) ⟨6020405, by rfl⟩ : syracuseStep 8027207 = 12040811) B12040811
theorem B5351471 : Blo 2225435 5351471 := bstep (se 1 (by rfl) ⟨4013603, by rfl⟩ : syracuseStep 5351471 = 8027207) B8027207
theorem B3567647 : Blo 2225435 3567647 := bstep (se 1 (by rfl) ⟨2675735, by rfl⟩ : syracuseStep 3567647 = 5351471) B5351471
theorem B2378431 : Blo 2225435 2378431 := bstep (se 1 (by rfl) ⟨1783823, by rfl⟩ : syracuseStep 2378431 = 3567647) B3567647
theorem B3171241 : Blo 2225435 3171241 := bstep (se 2 (by rfl) ⟨1189215, by rfl⟩ : syracuseStep 3171241 = 2378431) B2378431
theorem B16913285 : Blo 2225435 16913285 := bstep (se 4 (by rfl) ⟨1585620, by rfl⟩ : syracuseStep 16913285 = 3171241) B3171241
theorem B11275523 : Blo 2225435 11275523 := bstep (se 1 (by rfl) ⟨8456642, by rfl⟩ : syracuseStep 11275523 = 16913285) B16913285
theorem B7517015 : Blo 2225435 7517015 := bstep (se 1 (by rfl) ⟨5637761, by rfl⟩ : syracuseStep 7517015 = 11275523) B11275523
theorem B5011343 : Blo 2225435 5011343 := bstep (se 1 (by rfl) ⟨3758507, by rfl⟩ : syracuseStep 5011343 = 7517015) B7517015
theorem B3340895 : Blo 2225435 3340895 := bstep (se 1 (by rfl) ⟨2505671, by rfl⟩ : syracuseStep 3340895 = 5011343) B5011343
theorem B2227263 : Blo 2225435 2227263 := bstep (se 1 (by rfl) ⟨1670447, by rfl⟩ : syracuseStep 2227263 = 3340895) B3340895
theorem B3340901 : Blo 2225435 3340901 := bbase (se 4 (by rfl) ⟨313209, by rfl⟩ : syracuseStep 3340901 = 626419) (by norm_num)
theorem B2227267 : Blo 2225435 2227267 := bstep (se 1 (by rfl) ⟨1670450, by rfl⟩ : syracuseStep 2227267 = 3340901) B3340901
theorem B3171253 : Blo 2225435 3171253 := bbase (se 5 (by rfl) ⟨148652, by rfl⟩ : syracuseStep 3171253 = 297305) (by norm_num)
theorem B4228337 : Blo 2225435 4228337 := bstep (se 2 (by rfl) ⟨1585626, by rfl⟩ : syracuseStep 4228337 = 3171253) B3171253
theorem B2818891 : Blo 2225435 2818891 := bstep (se 1 (by rfl) ⟨2114168, by rfl⟩ : syracuseStep 2818891 = 4228337) B4228337
theorem B3758521 : Blo 2225435 3758521 := bstep (se 2 (by rfl) ⟨1409445, by rfl⟩ : syracuseStep 3758521 = 2818891) B2818891
theorem B5011361 : Blo 2225435 5011361 := bstep (se 2 (by rfl) ⟨1879260, by rfl⟩ : syracuseStep 5011361 = 3758521) B3758521
theorem B3340907 : Blo 2225435 3340907 := bstep (se 1 (by rfl) ⟨2505680, by rfl⟩ : syracuseStep 3340907 = 5011361) B5011361
theorem B2227271 : Blo 2225435 2227271 := bstep (se 1 (by rfl) ⟨1670453, by rfl⟩ : syracuseStep 2227271 = 3340907) B3340907
theorem B2505685 : Blo 2225435 2505685 := bbase (se 7 (by rfl) ⟨29363, by rfl⟩ : syracuseStep 2505685 = 58727) (by norm_num)
theorem B3340913 : Blo 2225435 3340913 := bstep (se 2 (by rfl) ⟨1252842, by rfl⟩ : syracuseStep 3340913 = 2505685) B2505685
theorem B2227275 : Blo 2225435 2227275 := bstep (se 1 (by rfl) ⟨1670456, by rfl⟩ : syracuseStep 2227275 = 3340913) B3340913
theorem B2818901 : Blo 2225435 2818901 := bbase (se 9 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 2818901 = 16517) (by norm_num)
theorem B7517069 : Blo 2225435 7517069 := bstep (se 3 (by rfl) ⟨1409450, by rfl⟩ : syracuseStep 7517069 = 2818901) B2818901
theorem B5011379 : Blo 2225435 5011379 := bstep (se 1 (by rfl) ⟨3758534, by rfl⟩ : syracuseStep 5011379 = 7517069) B7517069
theorem B3340919 : Blo 2225435 3340919 := bstep (se 1 (by rfl) ⟨2505689, by rfl⟩ : syracuseStep 3340919 = 5011379) B5011379
theorem B2227279 : Blo 2225435 2227279 := bstep (se 1 (by rfl) ⟨1670459, by rfl⟩ : syracuseStep 2227279 = 3340919) B3340919
theorem B3340925 : Blo 2225435 3340925 := bbase (se 3 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 3340925 = 1252847) (by norm_num)
theorem B2227283 : Blo 2225435 2227283 := bstep (se 1 (by rfl) ⟨1670462, by rfl⟩ : syracuseStep 2227283 = 3340925) B3340925
theorem B5011397 : Blo 2225435 5011397 := bbase (se 4 (by rfl) ⟨469818, by rfl⟩ : syracuseStep 5011397 = 939637) (by norm_num)
theorem B3340931 : Blo 2225435 3340931 := bstep (se 1 (by rfl) ⟨2505698, by rfl⟩ : syracuseStep 3340931 = 5011397) B5011397
theorem B2227287 : Blo 2225435 2227287 := bstep (se 1 (by rfl) ⟨1670465, by rfl⟩ : syracuseStep 2227287 = 3340931) B3340931
theorem B9513845 : Blo 2225435 9513845 := bbase (se 5 (by rfl) ⟨445961, by rfl⟩ : syracuseStep 9513845 = 891923) (by norm_num)
theorem B6342563 : Blo 2225435 6342563 := bstep (se 1 (by rfl) ⟨4756922, by rfl⟩ : syracuseStep 6342563 = 9513845) B9513845
theorem B4228375 : Blo 2225435 4228375 := bstep (se 1 (by rfl) ⟨3171281, by rfl⟩ : syracuseStep 4228375 = 6342563) B6342563
theorem B5637833 : Blo 2225435 5637833 := bstep (se 2 (by rfl) ⟨2114187, by rfl⟩ : syracuseStep 5637833 = 4228375) B4228375
theorem B3758555 : Blo 2225435 3758555 := bstep (se 1 (by rfl) ⟨2818916, by rfl⟩ : syracuseStep 3758555 = 5637833) B5637833
theorem B2505703 : Blo 2225435 2505703 := bstep (se 1 (by rfl) ⟨1879277, by rfl⟩ : syracuseStep 2505703 = 3758555) B3758555
theorem B3340937 : Blo 2225435 3340937 := bstep (se 2 (by rfl) ⟨1252851, by rfl⟩ : syracuseStep 3340937 = 2505703) B2505703
theorem B2227291 : Blo 2225435 2227291 := bstep (se 1 (by rfl) ⟨1670468, by rfl⟩ : syracuseStep 2227291 = 3340937) B3340937
theorem B11275685 : Blo 2225435 11275685 := bbase (se 4 (by rfl) ⟨1057095, by rfl⟩ : syracuseStep 11275685 = 2114191) (by norm_num)
theorem B7517123 : Blo 2225435 7517123 := bstep (se 1 (by rfl) ⟨5637842, by rfl⟩ : syracuseStep 7517123 = 11275685) B11275685
theorem B5011415 : Blo 2225435 5011415 := bstep (se 1 (by rfl) ⟨3758561, by rfl⟩ : syracuseStep 5011415 = 7517123) B7517123
theorem B3340943 : Blo 2225435 3340943 := bstep (se 1 (by rfl) ⟨2505707, by rfl⟩ : syracuseStep 3340943 = 5011415) B5011415
theorem B2227295 : Blo 2225435 2227295 := bstep (se 1 (by rfl) ⟨1670471, by rfl⟩ : syracuseStep 2227295 = 3340943) B3340943
theorem B3340949 : Blo 2225435 3340949 := bbase (se 6 (by rfl) ⟨78303, by rfl⟩ : syracuseStep 3340949 = 156607) (by norm_num)
theorem B2227299 : Blo 2225435 2227299 := bstep (se 1 (by rfl) ⟨1670474, by rfl⟩ : syracuseStep 2227299 = 3340949) B3340949
theorem B4344565 : Blo 2225435 4344565 := bbase (se 5 (by rfl) ⟨203651, by rfl⟩ : syracuseStep 4344565 = 407303) (by norm_num)
theorem B5792753 : Blo 2225435 5792753 := bstep (se 2 (by rfl) ⟨2172282, by rfl⟩ : syracuseStep 5792753 = 4344565) B4344565
theorem B15447341 : Blo 2225435 15447341 := bstep (se 3 (by rfl) ⟨2896376, by rfl⟩ : syracuseStep 15447341 = 5792753) B5792753
theorem B10298227 : Blo 2225435 10298227 := bstep (se 1 (by rfl) ⟨7723670, by rfl⟩ : syracuseStep 10298227 = 15447341) B15447341
theorem B13730969 : Blo 2225435 13730969 := bstep (se 2 (by rfl) ⟨5149113, by rfl⟩ : syracuseStep 13730969 = 10298227) B10298227
theorem B9153979 : Blo 2225435 9153979 := bstep (se 1 (by rfl) ⟨6865484, by rfl⟩ : syracuseStep 9153979 = 13730969) B13730969
theorem B48821221 : Blo 2225435 48821221 := bstep (se 4 (by rfl) ⟨4576989, by rfl⟩ : syracuseStep 48821221 = 9153979) B9153979
theorem B260379845 : Blo 2225435 260379845 := bstep (se 4 (by rfl) ⟨24410610, by rfl⟩ : syracuseStep 260379845 = 48821221) B48821221
theorem B173586563 : Blo 2225435 173586563 := bstep (se 1 (by rfl) ⟨130189922, by rfl⟩ : syracuseStep 173586563 = 260379845) B260379845
theorem B115724375 : Blo 2225435 115724375 := bstep (se 1 (by rfl) ⟨86793281, by rfl⟩ : syracuseStep 115724375 = 173586563) B173586563
theorem B77149583 : Blo 2225435 77149583 := bstep (se 1 (by rfl) ⟨57862187, by rfl⟩ : syracuseStep 77149583 = 115724375) B115724375
theorem B51433055 : Blo 2225435 51433055 := bstep (se 1 (by rfl) ⟨38574791, by rfl⟩ : syracuseStep 51433055 = 77149583) B77149583
theorem B34288703 : Blo 2225435 34288703 := bstep (se 1 (by rfl) ⟨25716527, by rfl⟩ : syracuseStep 34288703 = 51433055) B51433055
theorem B22859135 : Blo 2225435 22859135 := bstep (se 1 (by rfl) ⟨17144351, by rfl⟩ : syracuseStep 22859135 = 34288703) B34288703
theorem B15239423 : Blo 2225435 15239423 := bstep (se 1 (by rfl) ⟨11429567, by rfl⟩ : syracuseStep 15239423 = 22859135) B22859135
theorem B10159615 : Blo 2225435 10159615 := bstep (se 1 (by rfl) ⟨7619711, by rfl⟩ : syracuseStep 10159615 = 15239423) B15239423
theorem B13546153 : Blo 2225435 13546153 := bstep (se 2 (by rfl) ⟨5079807, by rfl⟩ : syracuseStep 13546153 = 10159615) B10159615
theorem B18061537 : Blo 2225435 18061537 := bstep (se 2 (by rfl) ⟨6773076, by rfl⟩ : syracuseStep 18061537 = 13546153) B13546153
theorem B24082049 : Blo 2225435 24082049 := bstep (se 2 (by rfl) ⟨9030768, by rfl⟩ : syracuseStep 24082049 = 18061537) B18061537
theorem B16054699 : Blo 2225435 16054699 := bstep (se 1 (by rfl) ⟨12041024, by rfl⟩ : syracuseStep 16054699 = 24082049) B24082049
theorem B21406265 : Blo 2225435 21406265 := bstep (se 2 (by rfl) ⟨8027349, by rfl⟩ : syracuseStep 21406265 = 16054699) B16054699
theorem B14270843 : Blo 2225435 14270843 := bstep (se 1 (by rfl) ⟨10703132, by rfl⟩ : syracuseStep 14270843 = 21406265) B21406265
theorem B9513895 : Blo 2225435 9513895 := bstep (se 1 (by rfl) ⟨7135421, by rfl⟩ : syracuseStep 9513895 = 14270843) B14270843
theorem B12685193 : Blo 2225435 12685193 := bstep (se 2 (by rfl) ⟨4756947, by rfl⟩ : syracuseStep 12685193 = 9513895) B9513895
theorem B8456795 : Blo 2225435 8456795 := bstep (se 1 (by rfl) ⟨6342596, by rfl⟩ : syracuseStep 8456795 = 12685193) B12685193
theorem B5637863 : Blo 2225435 5637863 := bstep (se 1 (by rfl) ⟨4228397, by rfl⟩ : syracuseStep 5637863 = 8456795) B8456795
theorem B3758575 : Blo 2225435 3758575 := bstep (se 1 (by rfl) ⟨2818931, by rfl⟩ : syracuseStep 3758575 = 5637863) B5637863
theorem B5011433 : Blo 2225435 5011433 := bstep (se 2 (by rfl) ⟨1879287, by rfl⟩ : syracuseStep 5011433 = 3758575) B3758575
theorem B3340955 : Blo 2225435 3340955 := bstep (se 1 (by rfl) ⟨2505716, by rfl⟩ : syracuseStep 3340955 = 5011433) B5011433
theorem B2227303 : Blo 2225435 2227303 := bstep (se 1 (by rfl) ⟨1670477, by rfl⟩ : syracuseStep 2227303 = 3340955) B3340955
theorem B2505721 : Blo 2225435 2505721 := bbase (se 2 (by rfl) ⟨939645, by rfl⟩ : syracuseStep 2505721 = 1879291) (by norm_num)
theorem B3340961 : Blo 2225435 3340961 := bstep (se 2 (by rfl) ⟨1252860, by rfl⟩ : syracuseStep 3340961 = 2505721) B2505721
theorem B2227307 : Blo 2225435 2227307 := bstep (se 1 (by rfl) ⟨1670480, by rfl⟩ : syracuseStep 2227307 = 3340961) B3340961
theorem B4821869 : Blo 2225435 4821869 := bbase (se 3 (by rfl) ⟨904100, by rfl⟩ : syracuseStep 4821869 = 1808201) (by norm_num)
theorem B3214579 : Blo 2225435 3214579 := bstep (se 1 (by rfl) ⟨2410934, by rfl⟩ : syracuseStep 3214579 = 4821869) B4821869
theorem B4286105 : Blo 2225435 4286105 := bstep (se 2 (by rfl) ⟨1607289, by rfl⟩ : syracuseStep 4286105 = 3214579) B3214579
theorem B2857403 : Blo 2225435 2857403 := bstep (se 1 (by rfl) ⟨2143052, by rfl⟩ : syracuseStep 2857403 = 4286105) B4286105
theorem B7619741 : Blo 2225435 7619741 := bstep (se 3 (by rfl) ⟨1428701, by rfl⟩ : syracuseStep 7619741 = 2857403) B2857403
theorem B5079827 : Blo 2225435 5079827 := bstep (se 1 (by rfl) ⟨3809870, by rfl⟩ : syracuseStep 5079827 = 7619741) B7619741
theorem B3386551 : Blo 2225435 3386551 := bstep (se 1 (by rfl) ⟨2539913, by rfl⟩ : syracuseStep 3386551 = 5079827) B5079827
theorem B4515401 : Blo 2225435 4515401 := bstep (se 2 (by rfl) ⟨1693275, by rfl⟩ : syracuseStep 4515401 = 3386551) B3386551
theorem B3010267 : Blo 2225435 3010267 := bstep (se 1 (by rfl) ⟨2257700, by rfl⟩ : syracuseStep 3010267 = 4515401) B4515401
theorem B16054757 : Blo 2225435 16054757 := bstep (se 4 (by rfl) ⟨1505133, by rfl⟩ : syracuseStep 16054757 = 3010267) B3010267
theorem B10703171 : Blo 2225435 10703171 := bstep (se 1 (by rfl) ⟨8027378, by rfl⟩ : syracuseStep 10703171 = 16054757) B16054757
theorem B7135447 : Blo 2225435 7135447 := bstep (se 1 (by rfl) ⟨5351585, by rfl⟩ : syracuseStep 7135447 = 10703171) B10703171
theorem B9513929 : Blo 2225435 9513929 := bstep (se 2 (by rfl) ⟨3567723, by rfl⟩ : syracuseStep 9513929 = 7135447) B7135447
theorem B6342619 : Blo 2225435 6342619 := bstep (se 1 (by rfl) ⟨4756964, by rfl⟩ : syracuseStep 6342619 = 9513929) B9513929
theorem B8456825 : Blo 2225435 8456825 := bstep (se 2 (by rfl) ⟨3171309, by rfl⟩ : syracuseStep 8456825 = 6342619) B6342619
theorem B5637883 : Blo 2225435 5637883 := bstep (se 1 (by rfl) ⟨4228412, by rfl⟩ : syracuseStep 5637883 = 8456825) B8456825
theorem B7517177 : Blo 2225435 7517177 := bstep (se 2 (by rfl) ⟨2818941, by rfl⟩ : syracuseStep 7517177 = 5637883) B5637883
theorem B5011451 : Blo 2225435 5011451 := bstep (se 1 (by rfl) ⟨3758588, by rfl⟩ : syracuseStep 5011451 = 7517177) B7517177
theorem B3340967 : Blo 2225435 3340967 := bstep (se 1 (by rfl) ⟨2505725, by rfl⟩ : syracuseStep 3340967 = 5011451) B5011451
theorem B2227311 : Blo 2225435 2227311 := bstep (se 1 (by rfl) ⟨1670483, by rfl⟩ : syracuseStep 2227311 = 3340967) B3340967
theorem B3340973 : Blo 2225435 3340973 := bbase (se 3 (by rfl) ⟨626432, by rfl⟩ : syracuseStep 3340973 = 1252865) (by norm_num)
theorem B2227315 : Blo 2225435 2227315 := bstep (se 1 (by rfl) ⟨1670486, by rfl⟩ : syracuseStep 2227315 = 3340973) B3340973
theorem B5011469 : Blo 2225435 5011469 := bbase (se 3 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 5011469 = 1879301) (by norm_num)
theorem B3340979 : Blo 2225435 3340979 := bstep (se 1 (by rfl) ⟨2505734, by rfl⟩ : syracuseStep 3340979 = 5011469) B5011469
theorem B2227319 : Blo 2225435 2227319 := bstep (se 1 (by rfl) ⟨1670489, by rfl⟩ : syracuseStep 2227319 = 3340979) B3340979
theorem B2818957 : Blo 2225435 2818957 := bbase (se 3 (by rfl) ⟨528554, by rfl⟩ : syracuseStep 2818957 = 1057109) (by norm_num)
theorem B3758609 : Blo 2225435 3758609 := bstep (se 2 (by rfl) ⟨1409478, by rfl⟩ : syracuseStep 3758609 = 2818957) B2818957
theorem B2505739 : Blo 2225435 2505739 := bstep (se 1 (by rfl) ⟨1879304, by rfl⟩ : syracuseStep 2505739 = 3758609) B3758609
theorem B3340985 : Blo 2225435 3340985 := bstep (se 2 (by rfl) ⟨1252869, by rfl⟩ : syracuseStep 3340985 = 2505739) B2505739
theorem B2227323 : Blo 2225435 2227323 := bstep (se 1 (by rfl) ⟨1670492, by rfl⟩ : syracuseStep 2227323 = 3340985) B3340985
theorem B2288521 : Blo 2225435 2288521 := bbase (se 2 (by rfl) ⟨858195, by rfl⟩ : syracuseStep 2288521 = 1716391) (by norm_num)
theorem B3051361 : Blo 2225435 3051361 := bstep (se 2 (by rfl) ⟨1144260, by rfl⟩ : syracuseStep 3051361 = 2288521) B2288521
theorem B4068481 : Blo 2225435 4068481 := bstep (se 2 (by rfl) ⟨1525680, by rfl⟩ : syracuseStep 4068481 = 3051361) B3051361
theorem B5424641 : Blo 2225435 5424641 := bstep (se 2 (by rfl) ⟨2034240, by rfl⟩ : syracuseStep 5424641 = 4068481) B4068481
theorem B3616427 : Blo 2225435 3616427 := bstep (se 1 (by rfl) ⟨2712320, by rfl⟩ : syracuseStep 3616427 = 5424641) B5424641
theorem B9643805 : Blo 2225435 9643805 := bstep (se 3 (by rfl) ⟨1808213, by rfl⟩ : syracuseStep 9643805 = 3616427) B3616427
theorem B6429203 : Blo 2225435 6429203 := bstep (se 1 (by rfl) ⟨4821902, by rfl⟩ : syracuseStep 6429203 = 9643805) B9643805
theorem B4286135 : Blo 2225435 4286135 := bstep (se 1 (by rfl) ⟨3214601, by rfl⟩ : syracuseStep 4286135 = 6429203) B6429203
theorem B2857423 : Blo 2225435 2857423 := bstep (se 1 (by rfl) ⟨2143067, by rfl⟩ : syracuseStep 2857423 = 4286135) B4286135
theorem B3809897 : Blo 2225435 3809897 := bstep (se 2 (by rfl) ⟨1428711, by rfl⟩ : syracuseStep 3809897 = 2857423) B2857423
theorem B2539931 : Blo 2225435 2539931 := bstep (se 1 (by rfl) ⟨1904948, by rfl⟩ : syracuseStep 2539931 = 3809897) B3809897
theorem B6773149 : Blo 2225435 6773149 := bstep (se 3 (by rfl) ⟨1269965, by rfl⟩ : syracuseStep 6773149 = 2539931) B2539931
theorem B9030865 : Blo 2225435 9030865 := bstep (se 2 (by rfl) ⟨3386574, by rfl⟩ : syracuseStep 9030865 = 6773149) B6773149
theorem B12041153 : Blo 2225435 12041153 := bstep (se 2 (by rfl) ⟨4515432, by rfl⟩ : syracuseStep 12041153 = 9030865) B9030865
theorem B8027435 : Blo 2225435 8027435 := bstep (se 1 (by rfl) ⟨6020576, by rfl⟩ : syracuseStep 8027435 = 12041153) B12041153
theorem B21406493 : Blo 2225435 21406493 := bstep (se 3 (by rfl) ⟨4013717, by rfl⟩ : syracuseStep 21406493 = 8027435) B8027435
theorem B14270995 : Blo 2225435 14270995 := bstep (se 1 (by rfl) ⟨10703246, by rfl⟩ : syracuseStep 14270995 = 21406493) B21406493
theorem B19027993 : Blo 2225435 19027993 := bstep (se 2 (by rfl) ⟨7135497, by rfl⟩ : syracuseStep 19027993 = 14270995) B14270995
theorem B25370657 : Blo 2225435 25370657 := bstep (se 2 (by rfl) ⟨9513996, by rfl⟩ : syracuseStep 25370657 = 19027993) B19027993
theorem B16913771 : Blo 2225435 16913771 := bstep (se 1 (by rfl) ⟨12685328, by rfl⟩ : syracuseStep 16913771 = 25370657) B25370657
theorem B11275847 : Blo 2225435 11275847 := bstep (se 1 (by rfl) ⟨8456885, by rfl⟩ : syracuseStep 11275847 = 16913771) B16913771
theorem B7517231 : Blo 2225435 7517231 := bstep (se 1 (by rfl) ⟨5637923, by rfl⟩ : syracuseStep 7517231 = 11275847) B11275847
theorem B5011487 : Blo 2225435 5011487 := bstep (se 1 (by rfl) ⟨3758615, by rfl⟩ : syracuseStep 5011487 = 7517231) B7517231
theorem B3340991 : Blo 2225435 3340991 := bstep (se 1 (by rfl) ⟨2505743, by rfl⟩ : syracuseStep 3340991 = 5011487) B5011487
theorem B2227327 : Blo 2225435 2227327 := bstep (se 1 (by rfl) ⟨1670495, by rfl⟩ : syracuseStep 2227327 = 3340991) B3340991
theorem B3340997 : Blo 2225435 3340997 := bbase (se 4 (by rfl) ⟨313218, by rfl⟩ : syracuseStep 3340997 = 626437) (by norm_num)
theorem B2227331 : Blo 2225435 2227331 := bstep (se 1 (by rfl) ⟨1670498, by rfl⟩ : syracuseStep 2227331 = 3340997) B3340997
theorem B3758629 : Blo 2225435 3758629 := bbase (se 4 (by rfl) ⟨352371, by rfl⟩ : syracuseStep 3758629 = 704743) (by norm_num)
theorem B5011505 : Blo 2225435 5011505 := bstep (se 2 (by rfl) ⟨1879314, by rfl⟩ : syracuseStep 5011505 = 3758629) B3758629
theorem B3341003 : Blo 2225435 3341003 := bstep (se 1 (by rfl) ⟨2505752, by rfl⟩ : syracuseStep 3341003 = 5011505) B5011505
theorem B2227335 : Blo 2225435 2227335 := bstep (se 1 (by rfl) ⟨1670501, by rfl⟩ : syracuseStep 2227335 = 3341003) B3341003
theorem B2505757 : Blo 2225435 2505757 := bbase (se 3 (by rfl) ⟨469829, by rfl⟩ : syracuseStep 2505757 = 939659) (by norm_num)
theorem B3341009 : Blo 2225435 3341009 := bstep (se 2 (by rfl) ⟨1252878, by rfl⟩ : syracuseStep 3341009 = 2505757) B2505757
theorem B2227339 : Blo 2225435 2227339 := bstep (se 1 (by rfl) ⟨1670504, by rfl⟩ : syracuseStep 2227339 = 3341009) B3341009
theorem B7517285 : Blo 2225435 7517285 := bbase (se 4 (by rfl) ⟨704745, by rfl⟩ : syracuseStep 7517285 = 1409491) (by norm_num)
theorem B5011523 : Blo 2225435 5011523 := bstep (se 1 (by rfl) ⟨3758642, by rfl⟩ : syracuseStep 5011523 = 7517285) B7517285
theorem B3341015 : Blo 2225435 3341015 := bstep (se 1 (by rfl) ⟨2505761, by rfl⟩ : syracuseStep 3341015 = 5011523) B5011523
theorem B2227343 : Blo 2225435 2227343 := bstep (se 1 (by rfl) ⟨1670507, by rfl⟩ : syracuseStep 2227343 = 3341015) B3341015
theorem B3341021 : Blo 2225435 3341021 := bbase (se 3 (by rfl) ⟨626441, by rfl⟩ : syracuseStep 3341021 = 1252883) (by norm_num)
theorem B2227347 : Blo 2225435 2227347 := bstep (se 1 (by rfl) ⟨1670510, by rfl⟩ : syracuseStep 2227347 = 3341021) B3341021
theorem B5011541 : Blo 2225435 5011541 := bbase (se 8 (by rfl) ⟨29364, by rfl⟩ : syracuseStep 5011541 = 58729) (by norm_num)
theorem B3341027 : Blo 2225435 3341027 := bstep (se 1 (by rfl) ⟨2505770, by rfl⟩ : syracuseStep 3341027 = 5011541) B5011541
theorem B2227351 : Blo 2225435 2227351 := bstep (se 1 (by rfl) ⟨1670513, by rfl⟩ : syracuseStep 2227351 = 3341027) B3341027
theorem B7135589 : Blo 2225435 7135589 := bbase (se 4 (by rfl) ⟨668961, by rfl⟩ : syracuseStep 7135589 = 1337923) (by norm_num)
theorem B4757059 : Blo 2225435 4757059 := bstep (se 1 (by rfl) ⟨3567794, by rfl⟩ : syracuseStep 4757059 = 7135589) B7135589
theorem B6342745 : Blo 2225435 6342745 := bstep (se 2 (by rfl) ⟨2378529, by rfl⟩ : syracuseStep 6342745 = 4757059) B4757059
theorem B8456993 : Blo 2225435 8456993 := bstep (se 2 (by rfl) ⟨3171372, by rfl⟩ : syracuseStep 8456993 = 6342745) B6342745
theorem B5637995 : Blo 2225435 5637995 := bstep (se 1 (by rfl) ⟨4228496, by rfl⟩ : syracuseStep 5637995 = 8456993) B8456993
theorem B3758663 : Blo 2225435 3758663 := bstep (se 1 (by rfl) ⟨2818997, by rfl⟩ : syracuseStep 3758663 = 5637995) B5637995
theorem B2505775 : Blo 2225435 2505775 := bstep (se 1 (by rfl) ⟨1879331, by rfl⟩ : syracuseStep 2505775 = 3758663) B3758663
theorem B3341033 : Blo 2225435 3341033 := bstep (se 2 (by rfl) ⟨1252887, by rfl⟩ : syracuseStep 3341033 = 2505775) B2505775
theorem B2227355 : Blo 2225435 2227355 := bstep (se 1 (by rfl) ⟨1670516, by rfl⟩ : syracuseStep 2227355 = 3341033) B3341033
theorem B3432829 : Blo 2225435 3432829 := bbase (se 3 (by rfl) ⟨643655, by rfl⟩ : syracuseStep 3432829 = 1287311) (by norm_num)
theorem B4577105 : Blo 2225435 4577105 := bstep (se 2 (by rfl) ⟨1716414, by rfl⟩ : syracuseStep 4577105 = 3432829) B3432829
theorem B12205613 : Blo 2225435 12205613 := bstep (se 3 (by rfl) ⟨2288552, by rfl⟩ : syracuseStep 12205613 = 4577105) B4577105
theorem B32548301 : Blo 2225435 32548301 := bstep (se 3 (by rfl) ⟨6102806, by rfl⟩ : syracuseStep 32548301 = 12205613) B12205613
theorem B21698867 : Blo 2225435 21698867 := bstep (se 1 (by rfl) ⟨16274150, by rfl⟩ : syracuseStep 21698867 = 32548301) B32548301
theorem B57863645 : Blo 2225435 57863645 := bstep (se 3 (by rfl) ⟨10849433, by rfl⟩ : syracuseStep 57863645 = 21698867) B21698867
theorem B38575763 : Blo 2225435 38575763 := bstep (se 1 (by rfl) ⟨28931822, by rfl⟩ : syracuseStep 38575763 = 57863645) B57863645
theorem B25717175 : Blo 2225435 25717175 := bstep (se 1 (by rfl) ⟨19287881, by rfl⟩ : syracuseStep 25717175 = 38575763) B38575763
theorem B17144783 : Blo 2225435 17144783 := bstep (se 1 (by rfl) ⟨12858587, by rfl⟩ : syracuseStep 17144783 = 25717175) B25717175
theorem B11429855 : Blo 2225435 11429855 := bstep (se 1 (by rfl) ⟨8572391, by rfl⟩ : syracuseStep 11429855 = 17144783) B17144783
theorem B7619903 : Blo 2225435 7619903 := bstep (se 1 (by rfl) ⟨5714927, by rfl⟩ : syracuseStep 7619903 = 11429855) B11429855
theorem B5079935 : Blo 2225435 5079935 := bstep (se 1 (by rfl) ⟨3809951, by rfl⟩ : syracuseStep 5079935 = 7619903) B7619903
theorem B13546493 : Blo 2225435 13546493 := bstep (se 3 (by rfl) ⟨2539967, by rfl⟩ : syracuseStep 13546493 = 5079935) B5079935
theorem B9030995 : Blo 2225435 9030995 := bstep (se 1 (by rfl) ⟨6773246, by rfl⟩ : syracuseStep 9030995 = 13546493) B13546493
theorem B6020663 : Blo 2225435 6020663 := bstep (se 1 (by rfl) ⟨4515497, by rfl⟩ : syracuseStep 6020663 = 9030995) B9030995
theorem B16055101 : Blo 2225435 16055101 := bstep (se 3 (by rfl) ⟨3010331, by rfl⟩ : syracuseStep 16055101 = 6020663) B6020663
theorem B21406801 : Blo 2225435 21406801 := bstep (se 2 (by rfl) ⟨8027550, by rfl⟩ : syracuseStep 21406801 = 16055101) B16055101
theorem B28542401 : Blo 2225435 28542401 := bstep (se 2 (by rfl) ⟨10703400, by rfl⟩ : syracuseStep 28542401 = 21406801) B21406801
theorem B19028267 : Blo 2225435 19028267 := bstep (se 1 (by rfl) ⟨14271200, by rfl⟩ : syracuseStep 19028267 = 28542401) B28542401
theorem B12685511 : Blo 2225435 12685511 := bstep (se 1 (by rfl) ⟨9514133, by rfl⟩ : syracuseStep 12685511 = 19028267) B19028267
theorem B8457007 : Blo 2225435 8457007 := bstep (se 1 (by rfl) ⟨6342755, by rfl⟩ : syracuseStep 8457007 = 12685511) B12685511
theorem B11276009 : Blo 2225435 11276009 := bstep (se 2 (by rfl) ⟨4228503, by rfl⟩ : syracuseStep 11276009 = 8457007) B8457007
theorem B7517339 : Blo 2225435 7517339 := bstep (se 1 (by rfl) ⟨5638004, by rfl⟩ : syracuseStep 7517339 = 11276009) B11276009
theorem B5011559 : Blo 2225435 5011559 := bstep (se 1 (by rfl) ⟨3758669, by rfl⟩ : syracuseStep 5011559 = 7517339) B7517339
theorem B3341039 : Blo 2225435 3341039 := bstep (se 1 (by rfl) ⟨2505779, by rfl⟩ : syracuseStep 3341039 = 5011559) B5011559
theorem B2227359 : Blo 2225435 2227359 := bstep (se 1 (by rfl) ⟨1670519, by rfl⟩ : syracuseStep 2227359 = 3341039) B3341039
theorem B3341045 : Blo 2225435 3341045 := bbase (se 5 (by rfl) ⟨156611, by rfl⟩ : syracuseStep 3341045 = 313223) (by norm_num)
theorem B2227363 : Blo 2225435 2227363 := bstep (se 1 (by rfl) ⟨1670522, by rfl⟩ : syracuseStep 2227363 = 3341045) B3341045
theorem B4286213 : Blo 2225435 4286213 := bbase (se 4 (by rfl) ⟨401832, by rfl⟩ : syracuseStep 4286213 = 803665) (by norm_num)
theorem B2857475 : Blo 2225435 2857475 := bstep (se 1 (by rfl) ⟨2143106, by rfl⟩ : syracuseStep 2857475 = 4286213) B4286213
theorem B7619933 : Blo 2225435 7619933 := bstep (se 3 (by rfl) ⟨1428737, by rfl⟩ : syracuseStep 7619933 = 2857475) B2857475
theorem B5079955 : Blo 2225435 5079955 := bstep (se 1 (by rfl) ⟨3809966, by rfl⟩ : syracuseStep 5079955 = 7619933) B7619933
theorem B6773273 : Blo 2225435 6773273 := bstep (se 2 (by rfl) ⟨2539977, by rfl⟩ : syracuseStep 6773273 = 5079955) B5079955
theorem B4515515 : Blo 2225435 4515515 := bstep (se 1 (by rfl) ⟨3386636, by rfl⟩ : syracuseStep 4515515 = 6773273) B6773273
theorem B3010343 : Blo 2225435 3010343 := bstep (se 1 (by rfl) ⟨2257757, by rfl⟩ : syracuseStep 3010343 = 4515515) B4515515
theorem B8027581 : Blo 2225435 8027581 := bstep (se 3 (by rfl) ⟨1505171, by rfl⟩ : syracuseStep 8027581 = 3010343) B3010343
theorem B10703441 : Blo 2225435 10703441 := bstep (se 2 (by rfl) ⟨4013790, by rfl⟩ : syracuseStep 10703441 = 8027581) B8027581
theorem B7135627 : Blo 2225435 7135627 := bstep (se 1 (by rfl) ⟨5351720, by rfl⟩ : syracuseStep 7135627 = 10703441) B10703441
theorem B9514169 : Blo 2225435 9514169 := bstep (se 2 (by rfl) ⟨3567813, by rfl⟩ : syracuseStep 9514169 = 7135627) B7135627
theorem B6342779 : Blo 2225435 6342779 := bstep (se 1 (by rfl) ⟨4757084, by rfl⟩ : syracuseStep 6342779 = 9514169) B9514169
theorem B4228519 : Blo 2225435 4228519 := bstep (se 1 (by rfl) ⟨3171389, by rfl⟩ : syracuseStep 4228519 = 6342779) B6342779
theorem B5638025 : Blo 2225435 5638025 := bstep (se 2 (by rfl) ⟨2114259, by rfl⟩ : syracuseStep 5638025 = 4228519) B4228519
theorem B3758683 : Blo 2225435 3758683 := bstep (se 1 (by rfl) ⟨2819012, by rfl⟩ : syracuseStep 3758683 = 5638025) B5638025
theorem B5011577 : Blo 2225435 5011577 := bstep (se 2 (by rfl) ⟨1879341, by rfl⟩ : syracuseStep 5011577 = 3758683) B3758683
theorem B3341051 : Blo 2225435 3341051 := bstep (se 1 (by rfl) ⟨2505788, by rfl⟩ : syracuseStep 3341051 = 5011577) B5011577
theorem B2227367 : Blo 2225435 2227367 := bstep (se 1 (by rfl) ⟨1670525, by rfl⟩ : syracuseStep 2227367 = 3341051) B3341051
theorem B2505793 : Blo 2225435 2505793 := bbase (se 2 (by rfl) ⟨939672, by rfl⟩ : syracuseStep 2505793 = 1879345) (by norm_num)
theorem B3341057 : Blo 2225435 3341057 := bstep (se 2 (by rfl) ⟨1252896, by rfl⟩ : syracuseStep 3341057 = 2505793) B2505793
theorem B2227371 : Blo 2225435 2227371 := bstep (se 1 (by rfl) ⟨1670528, by rfl⟩ : syracuseStep 2227371 = 3341057) B3341057
theorem B5638045 : Blo 2225435 5638045 := bbase (se 3 (by rfl) ⟨1057133, by rfl⟩ : syracuseStep 5638045 = 2114267) (by norm_num)
theorem B7517393 : Blo 2225435 7517393 := bstep (se 2 (by rfl) ⟨2819022, by rfl⟩ : syracuseStep 7517393 = 5638045) B5638045
theorem B5011595 : Blo 2225435 5011595 := bstep (se 1 (by rfl) ⟨3758696, by rfl⟩ : syracuseStep 5011595 = 7517393) B7517393
theorem B3341063 : Blo 2225435 3341063 := bstep (se 1 (by rfl) ⟨2505797, by rfl⟩ : syracuseStep 3341063 = 5011595) B5011595
theorem B2227375 : Blo 2225435 2227375 := bstep (se 1 (by rfl) ⟨1670531, by rfl⟩ : syracuseStep 2227375 = 3341063) B3341063
theorem B3341069 : Blo 2225435 3341069 := bbase (se 3 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 3341069 = 1252901) (by norm_num)
theorem B2227379 : Blo 2225435 2227379 := bstep (se 1 (by rfl) ⟨1670534, by rfl⟩ : syracuseStep 2227379 = 3341069) B3341069
theorem B5011613 : Blo 2225435 5011613 := bbase (se 3 (by rfl) ⟨939677, by rfl⟩ : syracuseStep 5011613 = 1879355) (by norm_num)
theorem B3341075 : Blo 2225435 3341075 := bstep (se 1 (by rfl) ⟨2505806, by rfl⟩ : syracuseStep 3341075 = 5011613) B5011613
theorem B2227383 : Blo 2225435 2227383 := bstep (se 1 (by rfl) ⟨1670537, by rfl⟩ : syracuseStep 2227383 = 3341075) B3341075
theorem B3758717 : Blo 2225435 3758717 := bbase (se 3 (by rfl) ⟨704759, by rfl⟩ : syracuseStep 3758717 = 1409519) (by norm_num)
theorem B2505811 : Blo 2225435 2505811 := bstep (se 1 (by rfl) ⟨1879358, by rfl⟩ : syracuseStep 2505811 = 3758717) B3758717
theorem B3341081 : Blo 2225435 3341081 := bstep (se 2 (by rfl) ⟨1252905, by rfl⟩ : syracuseStep 3341081 = 2505811) B2505811
theorem B2227387 : Blo 2225435 2227387 := bstep (se 1 (by rfl) ⟨1670540, by rfl⟩ : syracuseStep 2227387 = 3341081) B3341081
theorem B8572517 : Blo 2225435 8572517 := bbase (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) (by norm_num)
theorem B5715011 : Blo 2225435 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B3810007 : Blo 2225435 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B5080009 : Blo 2225435 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B6773345 : Blo 2225435 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B4515563 : Blo 2225435 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B3010375 : Blo 2225435 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B16055333 : Blo 2225435 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B10703555 : Blo 2225435 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B7135703 : Blo 2225435 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B4757135 : Blo 2225435 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B12685693 : Blo 2225435 12685693 := bstep (se 3 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 12685693 = 4757135) B4757135
theorem B16914257 : Blo 2225435 16914257 := bstep (se 2 (by rfl) ⟨6342846, by rfl⟩ : syracuseStep 16914257 = 12685693) B12685693
theorem B11276171 : Blo 2225435 11276171 := bstep (se 1 (by rfl) ⟨8457128, by rfl⟩ : syracuseStep 11276171 = 16914257) B16914257
theorem B7517447 : Blo 2225435 7517447 := bstep (se 1 (by rfl) ⟨5638085, by rfl⟩ : syracuseStep 7517447 = 11276171) B11276171
theorem B5011631 : Blo 2225435 5011631 := bstep (se 1 (by rfl) ⟨3758723, by rfl⟩ : syracuseStep 5011631 = 7517447) B7517447
theorem B3341087 : Blo 2225435 3341087 := bstep (se 1 (by rfl) ⟨2505815, by rfl⟩ : syracuseStep 3341087 = 5011631) B5011631
theorem B2227391 : Blo 2225435 2227391 := bstep (se 1 (by rfl) ⟨1670543, by rfl⟩ : syracuseStep 2227391 = 3341087) B3341087
theorem B3341093 : Blo 2225435 3341093 := bbase (se 4 (by rfl) ⟨313227, by rfl⟩ : syracuseStep 3341093 = 626455) (by norm_num)
theorem B2227395 : Blo 2225435 2227395 := bstep (se 1 (by rfl) ⟨1670546, by rfl⟩ : syracuseStep 2227395 = 3341093) B3341093
theorem B2819053 : Blo 2225435 2819053 := bbase (se 3 (by rfl) ⟨528572, by rfl⟩ : syracuseStep 2819053 = 1057145) (by norm_num)
theorem B3758737 : Blo 2225435 3758737 := bstep (se 2 (by rfl) ⟨1409526, by rfl⟩ : syracuseStep 3758737 = 2819053) B2819053
theorem B5011649 : Blo 2225435 5011649 := bstep (se 2 (by rfl) ⟨1879368, by rfl⟩ : syracuseStep 5011649 = 3758737) B3758737
theorem B3341099 : Blo 2225435 3341099 := bstep (se 1 (by rfl) ⟨2505824, by rfl⟩ : syracuseStep 3341099 = 5011649) B5011649
theorem B2227399 : Blo 2225435 2227399 := bstep (se 1 (by rfl) ⟨1670549, by rfl⟩ : syracuseStep 2227399 = 3341099) B3341099
theorem B2505829 : Blo 2225435 2505829 := bbase (se 4 (by rfl) ⟨234921, by rfl⟩ : syracuseStep 2505829 = 469843) (by norm_num)
theorem B3341105 : Blo 2225435 3341105 := bstep (se 2 (by rfl) ⟨1252914, by rfl⟩ : syracuseStep 3341105 = 2505829) B2505829
theorem B2227403 : Blo 2225435 2227403 := bstep (se 1 (by rfl) ⟨1670552, by rfl⟩ : syracuseStep 2227403 = 3341105) B3341105
theorem B2378585 : Blo 2225435 2378585 := bbase (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) (by norm_num)
theorem B6342893 : Blo 2225435 6342893 := bstep (se 3 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 6342893 = 2378585) B2378585
theorem B4228595 : Blo 2225435 4228595 := bstep (se 1 (by rfl) ⟨3171446, by rfl⟩ : syracuseStep 4228595 = 6342893) B6342893
theorem B2819063 : Blo 2225435 2819063 := bstep (se 1 (by rfl) ⟨2114297, by rfl⟩ : syracuseStep 2819063 = 4228595) B4228595
theorem B7517501 : Blo 2225435 7517501 := bstep (se 3 (by rfl) ⟨1409531, by rfl⟩ : syracuseStep 7517501 = 2819063) B2819063
theorem B5011667 : Blo 2225435 5011667 := bstep (se 1 (by rfl) ⟨3758750, by rfl⟩ : syracuseStep 5011667 = 7517501) B7517501
theorem B3341111 : Blo 2225435 3341111 := bstep (se 1 (by rfl) ⟨2505833, by rfl⟩ : syracuseStep 3341111 = 5011667) B5011667
theorem B2227407 : Blo 2225435 2227407 := bstep (se 1 (by rfl) ⟨1670555, by rfl⟩ : syracuseStep 2227407 = 3341111) B3341111
theorem B3341117 : Blo 2225435 3341117 := bbase (se 3 (by rfl) ⟨626459, by rfl⟩ : syracuseStep 3341117 = 1252919) (by norm_num)
theorem B2227411 : Blo 2225435 2227411 := bstep (se 1 (by rfl) ⟨1670558, by rfl⟩ : syracuseStep 2227411 = 3341117) B3341117
theorem B5011685 : Blo 2225435 5011685 := bbase (se 4 (by rfl) ⟨469845, by rfl⟩ : syracuseStep 5011685 = 939691) (by norm_num)
theorem B3341123 : Blo 2225435 3341123 := bstep (se 1 (by rfl) ⟨2505842, by rfl⟩ : syracuseStep 3341123 = 5011685) B5011685
theorem B2227415 : Blo 2225435 2227415 := bstep (se 1 (by rfl) ⟨1670561, by rfl⟩ : syracuseStep 2227415 = 3341123) B3341123
theorem B5638157 : Blo 2225435 5638157 := bbase (se 3 (by rfl) ⟨1057154, by rfl⟩ : syracuseStep 5638157 = 2114309) (by norm_num)
theorem B3758771 : Blo 2225435 3758771 := bstep (se 1 (by rfl) ⟨2819078, by rfl⟩ : syracuseStep 3758771 = 5638157) B5638157
theorem B2505847 : Blo 2225435 2505847 := bstep (se 1 (by rfl) ⟨1879385, by rfl⟩ : syracuseStep 2505847 = 3758771) B3758771
theorem B3341129 : Blo 2225435 3341129 := bstep (se 2 (by rfl) ⟨1252923, by rfl⟩ : syracuseStep 3341129 = 2505847) B2505847
theorem B2227419 : Blo 2225435 2227419 := bstep (se 1 (by rfl) ⟨1670564, by rfl⟩ : syracuseStep 2227419 = 3341129) B3341129
theorem B3171469 : Blo 2225435 3171469 := bbase (se 3 (by rfl) ⟨594650, by rfl⟩ : syracuseStep 3171469 = 1189301) (by norm_num)
theorem B4228625 : Blo 2225435 4228625 := bstep (se 2 (by rfl) ⟨1585734, by rfl⟩ : syracuseStep 4228625 = 3171469) B3171469
theorem B11276333 : Blo 2225435 11276333 := bstep (se 3 (by rfl) ⟨2114312, by rfl⟩ : syracuseStep 11276333 = 4228625) B4228625
theorem B7517555 : Blo 2225435 7517555 := bstep (se 1 (by rfl) ⟨5638166, by rfl⟩ : syracuseStep 7517555 = 11276333) B11276333
theorem B5011703 : Blo 2225435 5011703 := bstep (se 1 (by rfl) ⟨3758777, by rfl⟩ : syracuseStep 5011703 = 7517555) B7517555
theorem B3341135 : Blo 2225435 3341135 := bstep (se 1 (by rfl) ⟨2505851, by rfl⟩ : syracuseStep 3341135 = 5011703) B5011703
theorem B2227423 : Blo 2225435 2227423 := bstep (se 1 (by rfl) ⟨1670567, by rfl⟩ : syracuseStep 2227423 = 3341135) B3341135
theorem B3341141 : Blo 2225435 3341141 := bbase (se 9 (by rfl) ⟨9788, by rfl⟩ : syracuseStep 3341141 = 19577) (by norm_num)
theorem B2227427 : Blo 2225435 2227427 := bstep (se 1 (by rfl) ⟨1670570, by rfl⟩ : syracuseStep 2227427 = 3341141) B3341141
theorem B4757221 : Blo 2225435 4757221 := bbase (se 4 (by rfl) ⟨445989, by rfl⟩ : syracuseStep 4757221 = 891979) (by norm_num)
theorem B6342961 : Blo 2225435 6342961 := bstep (se 2 (by rfl) ⟨2378610, by rfl⟩ : syracuseStep 6342961 = 4757221) B4757221
theorem B8457281 : Blo 2225435 8457281 := bstep (se 2 (by rfl) ⟨3171480, by rfl⟩ : syracuseStep 8457281 = 6342961) B6342961
theorem B5638187 : Blo 2225435 5638187 := bstep (se 1 (by rfl) ⟨4228640, by rfl⟩ : syracuseStep 5638187 = 8457281) B8457281
theorem B3758791 : Blo 2225435 3758791 := bstep (se 1 (by rfl) ⟨2819093, by rfl⟩ : syracuseStep 3758791 = 5638187) B5638187
theorem B5011721 : Blo 2225435 5011721 := bstep (se 2 (by rfl) ⟨1879395, by rfl⟩ : syracuseStep 5011721 = 3758791) B3758791
theorem B3341147 : Blo 2225435 3341147 := bstep (se 1 (by rfl) ⟨2505860, by rfl⟩ : syracuseStep 3341147 = 5011721) B5011721
theorem B2227431 : Blo 2225435 2227431 := bstep (se 1 (by rfl) ⟨1670573, by rfl⟩ : syracuseStep 2227431 = 3341147) B3341147
theorem B2505865 : Blo 2225435 2505865 := bbase (se 2 (by rfl) ⟨939699, by rfl⟩ : syracuseStep 2505865 = 1879399) (by norm_num)
theorem B3341153 : Blo 2225435 3341153 := bstep (se 2 (by rfl) ⟨1252932, by rfl⟩ : syracuseStep 3341153 = 2505865) B2505865
theorem B2227435 : Blo 2225435 2227435 := bstep (se 1 (by rfl) ⟨1670576, by rfl⟩ : syracuseStep 2227435 = 3341153) B3341153
theorem C0 (j : ℕ) (h1 : 556358 ≤ j) (h2 : j ≤ 556858) : Blo 2225435 (4 * j + 3) := by
  interval_cases j
  · exact B2225435
  · exact B2225439
  · exact B2225443
  · exact B2225447
  · exact B2225451
  · exact B2225455
  · exact B2225459
  · exact B2225463
  · exact B2225467
  · exact B2225471
  · exact B2225475
  · exact B2225479
  · exact B2225483
  · exact B2225487
  · exact B2225491
  · exact B2225495
  · exact B2225499
  · exact B2225503
  · exact B2225507
  · exact B2225511
  · exact B2225515
  · exact B2225519
  · exact B2225523
  · exact B2225527
  · exact B2225531
  · exact B2225535
  · exact B2225539
  · exact B2225543
  · exact B2225547
  · exact B2225551
  · exact B2225555
  · exact B2225559
  · exact B2225563
  · exact B2225567
  · exact B2225571
  · exact B2225575
  · exact B2225579
  · exact B2225583
  · exact B2225587
  · exact B2225591
  · exact B2225595
  · exact B2225599
  · exact B2225603
  · exact B2225607
  · exact B2225611
  · exact B2225615
  · exact B2225619
  · exact B2225623
  · exact B2225627
  · exact B2225631
  · exact B2225635
  · exact B2225639
  · exact B2225643
  · exact B2225647
  · exact B2225651
  · exact B2225655
  · exact B2225659
  · exact B2225663
  · exact B2225667
  · exact B2225671
  · exact B2225675
  · exact B2225679
  · exact B2225683
  · exact B2225687
  · exact B2225691
  · exact B2225695
  · exact B2225699
  · exact B2225703
  · exact B2225707
  · exact B2225711
  · exact B2225715
  · exact B2225719
  · exact B2225723
  · exact B2225727
  · exact B2225731
  · exact B2225735
  · exact B2225739
  · exact B2225743
  · exact B2225747
  · exact B2225751
  · exact B2225755
  · exact B2225759
  · exact B2225763
  · exact B2225767
  · exact B2225771
  · exact B2225775
  · exact B2225779
  · exact B2225783
  · exact B2225787
  · exact B2225791
  · exact B2225795
  · exact B2225799
  · exact B2225803
  · exact B2225807
  · exact B2225811
  · exact B2225815
  · exact B2225819
  · exact B2225823
  · exact B2225827
  · exact B2225831
  · exact B2225835
  · exact B2225839
  · exact B2225843
  · exact B2225847
  · exact B2225851
  · exact B2225855
  · exact B2225859
  · exact B2225863
  · exact B2225867
  · exact B2225871
  · exact B2225875
  · exact B2225879
  · exact B2225883
  · exact B2225887
  · exact B2225891
  · exact B2225895
  · exact B2225899
  · exact B2225903
  · exact B2225907
  · exact B2225911
  · exact B2225915
  · exact B2225919
  · exact B2225923
  · exact B2225927
  · exact B2225931
  · exact B2225935
  · exact B2225939
  · exact B2225943
  · exact B2225947
  · exact B2225951
  · exact B2225955
  · exact B2225959
  · exact B2225963
  · exact B2225967
  · exact B2225971
  · exact B2225975
  · exact B2225979
  · exact B2225983
  · exact B2225987
  · exact B2225991
  · exact B2225995
  · exact B2225999
  · exact B2226003
  · exact B2226007
  · exact B2226011
  · exact B2226015
  · exact B2226019
  · exact B2226023
  · exact B2226027
  · exact B2226031
  · exact B2226035
  · exact B2226039
  · exact B2226043
  · exact B2226047
  · exact B2226051
  · exact B2226055
  · exact B2226059
  · exact B2226063
  · exact B2226067
  · exact B2226071
  · exact B2226075
  · exact B2226079
  · exact B2226083
  · exact B2226087
  · exact B2226091
  · exact B2226095
  · exact B2226099
  · exact B2226103
  · exact B2226107
  · exact B2226111
  · exact B2226115
  · exact B2226119
  · exact B2226123
  · exact B2226127
  · exact B2226131
  · exact B2226135
  · exact B2226139
  · exact B2226143
  · exact B2226147
  · exact B2226151
  · exact B2226155
  · exact B2226159
  · exact B2226163
  · exact B2226167
  · exact B2226171
  · exact B2226175
  · exact B2226179
  · exact B2226183
  · exact B2226187
  · exact B2226191
  · exact B2226195
  · exact B2226199
  · exact B2226203
  · exact B2226207
  · exact B2226211
  · exact B2226215
  · exact B2226219
  · exact B2226223
  · exact B2226227
  · exact B2226231
  · exact B2226235
  · exact B2226239
  · exact B2226243
  · exact B2226247
  · exact B2226251
  · exact B2226255
  · exact B2226259
  · exact B2226263
  · exact B2226267
  · exact B2226271
  · exact B2226275
  · exact B2226279
  · exact B2226283
  · exact B2226287
  · exact B2226291
  · exact B2226295
  · exact B2226299
  · exact B2226303
  · exact B2226307
  · exact B2226311
  · exact B2226315
  · exact B2226319
  · exact B2226323
  · exact B2226327
  · exact B2226331
  · exact B2226335
  · exact B2226339
  · exact B2226343
  · exact B2226347
  · exact B2226351
  · exact B2226355
  · exact B2226359
  · exact B2226363
  · exact B2226367
  · exact B2226371
  · exact B2226375
  · exact B2226379
  · exact B2226383
  · exact B2226387
  · exact B2226391
  · exact B2226395
  · exact B2226399
  · exact B2226403
  · exact B2226407
  · exact B2226411
  · exact B2226415
  · exact B2226419
  · exact B2226423
  · exact B2226427
  · exact B2226431
  · exact B2226435
  · exact B2226439
  · exact B2226443
  · exact B2226447
  · exact B2226451
  · exact B2226455
  · exact B2226459
  · exact B2226463
  · exact B2226467
  · exact B2226471
  · exact B2226475
  · exact B2226479
  · exact B2226483
  · exact B2226487
  · exact B2226491
  · exact B2226495
  · exact B2226499
  · exact B2226503
  · exact B2226507
  · exact B2226511
  · exact B2226515
  · exact B2226519
  · exact B2226523
  · exact B2226527
  · exact B2226531
  · exact B2226535
  · exact B2226539
  · exact B2226543
  · exact B2226547
  · exact B2226551
  · exact B2226555
  · exact B2226559
  · exact B2226563
  · exact B2226567
  · exact B2226571
  · exact B2226575
  · exact B2226579
  · exact B2226583
  · exact B2226587
  · exact B2226591
  · exact B2226595
  · exact B2226599
  · exact B2226603
  · exact B2226607
  · exact B2226611
  · exact B2226615
  · exact B2226619
  · exact B2226623
  · exact B2226627
  · exact B2226631
  · exact B2226635
  · exact B2226639
  · exact B2226643
  · exact B2226647
  · exact B2226651
  · exact B2226655
  · exact B2226659
  · exact B2226663
  · exact B2226667
  · exact B2226671
  · exact B2226675
  · exact B2226679
  · exact B2226683
  · exact B2226687
  · exact B2226691
  · exact B2226695
  · exact B2226699
  · exact B2226703
  · exact B2226707
  · exact B2226711
  · exact B2226715
  · exact B2226719
  · exact B2226723
  · exact B2226727
  · exact B2226731
  · exact B2226735
  · exact B2226739
  · exact B2226743
  · exact B2226747
  · exact B2226751
  · exact B2226755
  · exact B2226759
  · exact B2226763
  · exact B2226767
  · exact B2226771
  · exact B2226775
  · exact B2226779
  · exact B2226783
  · exact B2226787
  · exact B2226791
  · exact B2226795
  · exact B2226799
  · exact B2226803
  · exact B2226807
  · exact B2226811
  · exact B2226815
  · exact B2226819
  · exact B2226823
  · exact B2226827
  · exact B2226831
  · exact B2226835
  · exact B2226839
  · exact B2226843
  · exact B2226847
  · exact B2226851
  · exact B2226855
  · exact B2226859
  · exact B2226863
  · exact B2226867
  · exact B2226871
  · exact B2226875
  · exact B2226879
  · exact B2226883
  · exact B2226887
  · exact B2226891
  · exact B2226895
  · exact B2226899
  · exact B2226903
  · exact B2226907
  · exact B2226911
  · exact B2226915
  · exact B2226919
  · exact B2226923
  · exact B2226927
  · exact B2226931
  · exact B2226935
  · exact B2226939
  · exact B2226943
  · exact B2226947
  · exact B2226951
  · exact B2226955
  · exact B2226959
  · exact B2226963
  · exact B2226967
  · exact B2226971
  · exact B2226975
  · exact B2226979
  · exact B2226983
  · exact B2226987
  · exact B2226991
  · exact B2226995
  · exact B2226999
  · exact B2227003
  · exact B2227007
  · exact B2227011
  · exact B2227015
  · exact B2227019
  · exact B2227023
  · exact B2227027
  · exact B2227031
  · exact B2227035
  · exact B2227039
  · exact B2227043
  · exact B2227047
  · exact B2227051
  · exact B2227055
  · exact B2227059
  · exact B2227063
  · exact B2227067
  · exact B2227071
  · exact B2227075
  · exact B2227079
  · exact B2227083
  · exact B2227087
  · exact B2227091
  · exact B2227095
  · exact B2227099
  · exact B2227103
  · exact B2227107
  · exact B2227111
  · exact B2227115
  · exact B2227119
  · exact B2227123
  · exact B2227127
  · exact B2227131
  · exact B2227135
  · exact B2227139
  · exact B2227143
  · exact B2227147
  · exact B2227151
  · exact B2227155
  · exact B2227159
  · exact B2227163
  · exact B2227167
  · exact B2227171
  · exact B2227175
  · exact B2227179
  · exact B2227183
  · exact B2227187
  · exact B2227191
  · exact B2227195
  · exact B2227199
  · exact B2227203
  · exact B2227207
  · exact B2227211
  · exact B2227215
  · exact B2227219
  · exact B2227223
  · exact B2227227
  · exact B2227231
  · exact B2227235
  · exact B2227239
  · exact B2227243
  · exact B2227247
  · exact B2227251
  · exact B2227255
  · exact B2227259
  · exact B2227263
  · exact B2227267
  · exact B2227271
  · exact B2227275
  · exact B2227279
  · exact B2227283
  · exact B2227287
  · exact B2227291
  · exact B2227295
  · exact B2227299
  · exact B2227303
  · exact B2227307
  · exact B2227311
  · exact B2227315
  · exact B2227319
  · exact B2227323
  · exact B2227327
  · exact B2227331
  · exact B2227335
  · exact B2227339
  · exact B2227343
  · exact B2227347
  · exact B2227351
  · exact B2227355
  · exact B2227359
  · exact B2227363
  · exact B2227367
  · exact B2227371
  · exact B2227375
  · exact B2227379
  · exact B2227383
  · exact B2227387
  · exact B2227391
  · exact B2227395
  · exact B2227399
  · exact B2227403
  · exact B2227407
  · exact B2227411
  · exact B2227415
  · exact B2227419
  · exact B2227423
  · exact B2227427
  · exact B2227431
  · exact B2227435
theorem solution (m : ℕ) (hlo : 2225435 ≤ m) (hhi : m ≤ 2227435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 556358 ≤ j := by omega
    have hj2 : j ≤ 556858 := by omega
    have hb : Blo 2225435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
