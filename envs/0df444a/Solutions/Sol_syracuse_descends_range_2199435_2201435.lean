-- Prove2me | solution 1 for syracuse_descends_range_2199435_2201435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:16.932865+00:00
-- url     : https://prove2.me/submissions/8945cbd9-1813-413f-a9df-beb0664e9daf

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

theorem B2474365 : Blo 2199435 2474365 := bbase (se 3 (by rfl) ⟨463943, by rfl⟩ : syracuseStep 2474365 = 927887) (by norm_num)
theorem B3299153 : Blo 2199435 3299153 := bstep (se 2 (by rfl) ⟨1237182, by rfl⟩ : syracuseStep 3299153 = 2474365) B2474365
theorem B2199435 : Blo 2199435 2199435 := bstep (se 1 (by rfl) ⟨1649576, by rfl⟩ : syracuseStep 2199435 = 3299153) B3299153
theorem B7423109 : Blo 2199435 7423109 := bbase (se 4 (by rfl) ⟨695916, by rfl⟩ : syracuseStep 7423109 = 1391833) (by norm_num)
theorem B4948739 : Blo 2199435 4948739 := bstep (se 1 (by rfl) ⟨3711554, by rfl⟩ : syracuseStep 4948739 = 7423109) B7423109
theorem B3299159 : Blo 2199435 3299159 := bstep (se 1 (by rfl) ⟨2474369, by rfl⟩ : syracuseStep 3299159 = 4948739) B4948739
theorem B2199439 : Blo 2199435 2199439 := bstep (se 1 (by rfl) ⟨1649579, by rfl⟩ : syracuseStep 2199439 = 3299159) B3299159
theorem B3299165 : Blo 2199435 3299165 := bbase (se 3 (by rfl) ⟨618593, by rfl⟩ : syracuseStep 3299165 = 1237187) (by norm_num)
theorem B2199443 : Blo 2199435 2199443 := bstep (se 1 (by rfl) ⟨1649582, by rfl⟩ : syracuseStep 2199443 = 3299165) B3299165
theorem B4948757 : Blo 2199435 4948757 := bbase (se 6 (by rfl) ⟨115986, by rfl⟩ : syracuseStep 4948757 = 231973) (by norm_num)
theorem B3299171 : Blo 2199435 3299171 := bstep (se 1 (by rfl) ⟨2474378, by rfl⟩ : syracuseStep 3299171 = 4948757) B4948757
theorem B2199447 : Blo 2199435 2199447 := bstep (se 1 (by rfl) ⟨1649585, by rfl⟩ : syracuseStep 2199447 = 3299171) B3299171
theorem B8351045 : Blo 2199435 8351045 := bbase (se 4 (by rfl) ⟨782910, by rfl⟩ : syracuseStep 8351045 = 1565821) (by norm_num)
theorem B5567363 : Blo 2199435 5567363 := bstep (se 1 (by rfl) ⟨4175522, by rfl⟩ : syracuseStep 5567363 = 8351045) B8351045
theorem B3711575 : Blo 2199435 3711575 := bstep (se 1 (by rfl) ⟨2783681, by rfl⟩ : syracuseStep 3711575 = 5567363) B5567363
theorem B2474383 : Blo 2199435 2474383 := bstep (se 1 (by rfl) ⟨1855787, by rfl⟩ : syracuseStep 2474383 = 3711575) B3711575
theorem B3299177 : Blo 2199435 3299177 := bstep (se 2 (by rfl) ⟨1237191, by rfl⟩ : syracuseStep 3299177 = 2474383) B2474383
theorem B2199451 : Blo 2199435 2199451 := bstep (se 1 (by rfl) ⟨1649588, by rfl⟩ : syracuseStep 2199451 = 3299177) B3299177
theorem B3762221 : Blo 2199435 3762221 := bbase (se 3 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 3762221 = 1410833) (by norm_num)
theorem B10032589 : Blo 2199435 10032589 := bstep (se 3 (by rfl) ⟨1881110, by rfl⟩ : syracuseStep 10032589 = 3762221) B3762221
theorem B53507141 : Blo 2199435 53507141 := bstep (se 4 (by rfl) ⟨5016294, by rfl⟩ : syracuseStep 53507141 = 10032589) B10032589
theorem B35671427 : Blo 2199435 35671427 := bstep (se 1 (by rfl) ⟨26753570, by rfl⟩ : syracuseStep 35671427 = 53507141) B53507141
theorem B23780951 : Blo 2199435 23780951 := bstep (se 1 (by rfl) ⟨17835713, by rfl⟩ : syracuseStep 23780951 = 35671427) B35671427
theorem B15853967 : Blo 2199435 15853967 := bstep (se 1 (by rfl) ⟨11890475, by rfl⟩ : syracuseStep 15853967 = 23780951) B23780951
theorem B10569311 : Blo 2199435 10569311 := bstep (se 1 (by rfl) ⟨7926983, by rfl⟩ : syracuseStep 10569311 = 15853967) B15853967
theorem B7046207 : Blo 2199435 7046207 := bstep (se 1 (by rfl) ⟨5284655, by rfl⟩ : syracuseStep 7046207 = 10569311) B10569311
theorem B4697471 : Blo 2199435 4697471 := bstep (se 1 (by rfl) ⟨3523103, by rfl⟩ : syracuseStep 4697471 = 7046207) B7046207
theorem B12526589 : Blo 2199435 12526589 := bstep (se 3 (by rfl) ⟨2348735, by rfl⟩ : syracuseStep 12526589 = 4697471) B4697471
theorem B8351059 : Blo 2199435 8351059 := bstep (se 1 (by rfl) ⟨6263294, by rfl⟩ : syracuseStep 8351059 = 12526589) B12526589
theorem B11134745 : Blo 2199435 11134745 := bstep (se 2 (by rfl) ⟨4175529, by rfl⟩ : syracuseStep 11134745 = 8351059) B8351059
theorem B7423163 : Blo 2199435 7423163 := bstep (se 1 (by rfl) ⟨5567372, by rfl⟩ : syracuseStep 7423163 = 11134745) B11134745
theorem B4948775 : Blo 2199435 4948775 := bstep (se 1 (by rfl) ⟨3711581, by rfl⟩ : syracuseStep 4948775 = 7423163) B7423163
theorem B3299183 : Blo 2199435 3299183 := bstep (se 1 (by rfl) ⟨2474387, by rfl⟩ : syracuseStep 3299183 = 4948775) B4948775
theorem B2199455 : Blo 2199435 2199455 := bstep (se 1 (by rfl) ⟨1649591, by rfl⟩ : syracuseStep 2199455 = 3299183) B3299183
theorem B3299189 : Blo 2199435 3299189 := bbase (se 5 (by rfl) ⟨154649, by rfl⟩ : syracuseStep 3299189 = 309299) (by norm_num)
theorem B2199459 : Blo 2199435 2199459 := bstep (se 1 (by rfl) ⟨1649594, by rfl⟩ : syracuseStep 2199459 = 3299189) B3299189
theorem B3523117 : Blo 2199435 3523117 := bbase (se 3 (by rfl) ⟨660584, by rfl⟩ : syracuseStep 3523117 = 1321169) (by norm_num)
theorem B4697489 : Blo 2199435 4697489 := bstep (se 2 (by rfl) ⟨1761558, by rfl⟩ : syracuseStep 4697489 = 3523117) B3523117
theorem B3131659 : Blo 2199435 3131659 := bstep (se 1 (by rfl) ⟨2348744, by rfl⟩ : syracuseStep 3131659 = 4697489) B4697489
theorem B4175545 : Blo 2199435 4175545 := bstep (se 2 (by rfl) ⟨1565829, by rfl⟩ : syracuseStep 4175545 = 3131659) B3131659
theorem B5567393 : Blo 2199435 5567393 := bstep (se 2 (by rfl) ⟨2087772, by rfl⟩ : syracuseStep 5567393 = 4175545) B4175545
theorem B3711595 : Blo 2199435 3711595 := bstep (se 1 (by rfl) ⟨2783696, by rfl⟩ : syracuseStep 3711595 = 5567393) B5567393
theorem B4948793 : Blo 2199435 4948793 := bstep (se 2 (by rfl) ⟨1855797, by rfl⟩ : syracuseStep 4948793 = 3711595) B3711595
theorem B3299195 : Blo 2199435 3299195 := bstep (se 1 (by rfl) ⟨2474396, by rfl⟩ : syracuseStep 3299195 = 4948793) B4948793
theorem B2199463 : Blo 2199435 2199463 := bstep (se 1 (by rfl) ⟨1649597, by rfl⟩ : syracuseStep 2199463 = 3299195) B3299195
theorem B2474401 : Blo 2199435 2474401 := bbase (se 2 (by rfl) ⟨927900, by rfl⟩ : syracuseStep 2474401 = 1855801) (by norm_num)
theorem B3299201 : Blo 2199435 3299201 := bstep (se 2 (by rfl) ⟨1237200, by rfl⟩ : syracuseStep 3299201 = 2474401) B2474401
theorem B2199467 : Blo 2199435 2199467 := bstep (se 1 (by rfl) ⟨1649600, by rfl⟩ : syracuseStep 2199467 = 3299201) B3299201
theorem B5567413 : Blo 2199435 5567413 := bbase (se 5 (by rfl) ⟨260972, by rfl⟩ : syracuseStep 5567413 = 521945) (by norm_num)
theorem B7423217 : Blo 2199435 7423217 := bstep (se 2 (by rfl) ⟨2783706, by rfl⟩ : syracuseStep 7423217 = 5567413) B5567413
theorem B4948811 : Blo 2199435 4948811 := bstep (se 1 (by rfl) ⟨3711608, by rfl⟩ : syracuseStep 4948811 = 7423217) B7423217
theorem B3299207 : Blo 2199435 3299207 := bstep (se 1 (by rfl) ⟨2474405, by rfl⟩ : syracuseStep 3299207 = 4948811) B4948811
theorem B2199471 : Blo 2199435 2199471 := bstep (se 1 (by rfl) ⟨1649603, by rfl⟩ : syracuseStep 2199471 = 3299207) B3299207
theorem B3299213 : Blo 2199435 3299213 := bbase (se 3 (by rfl) ⟨618602, by rfl⟩ : syracuseStep 3299213 = 1237205) (by norm_num)
theorem B2199475 : Blo 2199435 2199475 := bstep (se 1 (by rfl) ⟨1649606, by rfl⟩ : syracuseStep 2199475 = 3299213) B3299213
theorem B4948829 : Blo 2199435 4948829 := bbase (se 3 (by rfl) ⟨927905, by rfl⟩ : syracuseStep 4948829 = 1855811) (by norm_num)
theorem B3299219 : Blo 2199435 3299219 := bstep (se 1 (by rfl) ⟨2474414, by rfl⟩ : syracuseStep 3299219 = 4948829) B4948829
theorem B2199479 : Blo 2199435 2199479 := bstep (se 1 (by rfl) ⟨1649609, by rfl⟩ : syracuseStep 2199479 = 3299219) B3299219
theorem B3711629 : Blo 2199435 3711629 := bbase (se 3 (by rfl) ⟨695930, by rfl⟩ : syracuseStep 3711629 = 1391861) (by norm_num)
theorem B2474419 : Blo 2199435 2474419 := bstep (se 1 (by rfl) ⟨1855814, by rfl⟩ : syracuseStep 2474419 = 3711629) B3711629
theorem B3299225 : Blo 2199435 3299225 := bstep (se 2 (by rfl) ⟨1237209, by rfl⟩ : syracuseStep 3299225 = 2474419) B2474419
theorem B2199483 : Blo 2199435 2199483 := bstep (se 1 (by rfl) ⟨1649612, by rfl⟩ : syracuseStep 2199483 = 3299225) B3299225
theorem B7046309 : Blo 2199435 7046309 := bbase (se 4 (by rfl) ⟨660591, by rfl⟩ : syracuseStep 7046309 = 1321183) (by norm_num)
theorem B18790157 : Blo 2199435 18790157 := bstep (se 3 (by rfl) ⟨3523154, by rfl⟩ : syracuseStep 18790157 = 7046309) B7046309
theorem B12526771 : Blo 2199435 12526771 := bstep (se 1 (by rfl) ⟨9395078, by rfl⟩ : syracuseStep 12526771 = 18790157) B18790157
theorem B16702361 : Blo 2199435 16702361 := bstep (se 2 (by rfl) ⟨6263385, by rfl⟩ : syracuseStep 16702361 = 12526771) B12526771
theorem B11134907 : Blo 2199435 11134907 := bstep (se 1 (by rfl) ⟨8351180, by rfl⟩ : syracuseStep 11134907 = 16702361) B16702361
theorem B7423271 : Blo 2199435 7423271 := bstep (se 1 (by rfl) ⟨5567453, by rfl⟩ : syracuseStep 7423271 = 11134907) B11134907
theorem B4948847 : Blo 2199435 4948847 := bstep (se 1 (by rfl) ⟨3711635, by rfl⟩ : syracuseStep 4948847 = 7423271) B7423271
theorem B3299231 : Blo 2199435 3299231 := bstep (se 1 (by rfl) ⟨2474423, by rfl⟩ : syracuseStep 3299231 = 4948847) B4948847
theorem B2199487 : Blo 2199435 2199487 := bstep (se 1 (by rfl) ⟨1649615, by rfl⟩ : syracuseStep 2199487 = 3299231) B3299231
theorem B3299237 : Blo 2199435 3299237 := bbase (se 4 (by rfl) ⟨309303, by rfl⟩ : syracuseStep 3299237 = 618607) (by norm_num)
theorem B2199491 : Blo 2199435 2199491 := bstep (se 1 (by rfl) ⟨1649618, by rfl⟩ : syracuseStep 2199491 = 3299237) B3299237
theorem B2783737 : Blo 2199435 2783737 := bbase (se 2 (by rfl) ⟨1043901, by rfl⟩ : syracuseStep 2783737 = 2087803) (by norm_num)
theorem B3711649 : Blo 2199435 3711649 := bstep (se 2 (by rfl) ⟨1391868, by rfl⟩ : syracuseStep 3711649 = 2783737) B2783737
theorem B4948865 : Blo 2199435 4948865 := bstep (se 2 (by rfl) ⟨1855824, by rfl⟩ : syracuseStep 4948865 = 3711649) B3711649
theorem B3299243 : Blo 2199435 3299243 := bstep (se 1 (by rfl) ⟨2474432, by rfl⟩ : syracuseStep 3299243 = 4948865) B4948865
theorem B2199495 : Blo 2199435 2199495 := bstep (se 1 (by rfl) ⟨1649621, by rfl⟩ : syracuseStep 2199495 = 3299243) B3299243
theorem B2474437 : Blo 2199435 2474437 := bbase (se 4 (by rfl) ⟨231978, by rfl⟩ : syracuseStep 2474437 = 463957) (by norm_num)
theorem B3299249 : Blo 2199435 3299249 := bstep (se 2 (by rfl) ⟨1237218, by rfl⟩ : syracuseStep 3299249 = 2474437) B2474437
theorem B2199499 : Blo 2199435 2199499 := bstep (se 1 (by rfl) ⟨1649624, by rfl⟩ : syracuseStep 2199499 = 3299249) B3299249
theorem B4175621 : Blo 2199435 4175621 := bbase (se 4 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 4175621 = 782929) (by norm_num)
theorem B2783747 : Blo 2199435 2783747 := bstep (se 1 (by rfl) ⟨2087810, by rfl⟩ : syracuseStep 2783747 = 4175621) B4175621
theorem B7423325 : Blo 2199435 7423325 := bstep (se 3 (by rfl) ⟨1391873, by rfl⟩ : syracuseStep 7423325 = 2783747) B2783747
theorem B4948883 : Blo 2199435 4948883 := bstep (se 1 (by rfl) ⟨3711662, by rfl⟩ : syracuseStep 4948883 = 7423325) B7423325
theorem B3299255 : Blo 2199435 3299255 := bstep (se 1 (by rfl) ⟨2474441, by rfl⟩ : syracuseStep 3299255 = 4948883) B4948883
theorem B2199503 : Blo 2199435 2199503 := bstep (se 1 (by rfl) ⟨1649627, by rfl⟩ : syracuseStep 2199503 = 3299255) B3299255
theorem B3299261 : Blo 2199435 3299261 := bbase (se 3 (by rfl) ⟨618611, by rfl⟩ : syracuseStep 3299261 = 1237223) (by norm_num)
theorem B2199507 : Blo 2199435 2199507 := bstep (se 1 (by rfl) ⟨1649630, by rfl⟩ : syracuseStep 2199507 = 3299261) B3299261
theorem B4948901 : Blo 2199435 4948901 := bbase (se 4 (by rfl) ⟨463959, by rfl⟩ : syracuseStep 4948901 = 927919) (by norm_num)
theorem B3299267 : Blo 2199435 3299267 := bstep (se 1 (by rfl) ⟨2474450, by rfl⟩ : syracuseStep 3299267 = 4948901) B4948901
theorem B2199511 : Blo 2199435 2199511 := bstep (se 1 (by rfl) ⟨1649633, by rfl⟩ : syracuseStep 2199511 = 3299267) B3299267
theorem B5567525 : Blo 2199435 5567525 := bbase (se 4 (by rfl) ⟨521955, by rfl⟩ : syracuseStep 5567525 = 1043911) (by norm_num)
theorem B3711683 : Blo 2199435 3711683 := bstep (se 1 (by rfl) ⟨2783762, by rfl⟩ : syracuseStep 3711683 = 5567525) B5567525
theorem B2474455 : Blo 2199435 2474455 := bstep (se 1 (by rfl) ⟨1855841, by rfl⟩ : syracuseStep 2474455 = 3711683) B3711683
theorem B3299273 : Blo 2199435 3299273 := bstep (se 2 (by rfl) ⟨1237227, by rfl⟩ : syracuseStep 3299273 = 2474455) B2474455
theorem B2199515 : Blo 2199435 2199515 := bstep (se 1 (by rfl) ⟨1649636, by rfl⟩ : syracuseStep 2199515 = 3299273) B3299273
theorem B6263477 : Blo 2199435 6263477 := bbase (se 5 (by rfl) ⟨293600, by rfl⟩ : syracuseStep 6263477 = 587201) (by norm_num)
theorem B4175651 : Blo 2199435 4175651 := bstep (se 1 (by rfl) ⟨3131738, by rfl⟩ : syracuseStep 4175651 = 6263477) B6263477
theorem B11135069 : Blo 2199435 11135069 := bstep (se 3 (by rfl) ⟨2087825, by rfl⟩ : syracuseStep 11135069 = 4175651) B4175651
theorem B7423379 : Blo 2199435 7423379 := bstep (se 1 (by rfl) ⟨5567534, by rfl⟩ : syracuseStep 7423379 = 11135069) B11135069
theorem B4948919 : Blo 2199435 4948919 := bstep (se 1 (by rfl) ⟨3711689, by rfl⟩ : syracuseStep 4948919 = 7423379) B7423379
theorem B3299279 : Blo 2199435 3299279 := bstep (se 1 (by rfl) ⟨2474459, by rfl⟩ : syracuseStep 3299279 = 4948919) B4948919
theorem B2199519 : Blo 2199435 2199519 := bstep (se 1 (by rfl) ⟨1649639, by rfl⟩ : syracuseStep 2199519 = 3299279) B3299279
theorem B3299285 : Blo 2199435 3299285 := bbase (se 7 (by rfl) ⟨38663, by rfl⟩ : syracuseStep 3299285 = 77327) (by norm_num)
theorem B2199523 : Blo 2199435 2199523 := bstep (se 1 (by rfl) ⟨1649642, by rfl⟩ : syracuseStep 2199523 = 3299285) B3299285
theorem B8351333 : Blo 2199435 8351333 := bbase (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) (by norm_num)
theorem B5567555 : Blo 2199435 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B3711703 : Blo 2199435 3711703 := bstep (se 1 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 3711703 = 5567555) B5567555
theorem B4948937 : Blo 2199435 4948937 := bstep (se 2 (by rfl) ⟨1855851, by rfl⟩ : syracuseStep 4948937 = 3711703) B3711703
theorem B3299291 : Blo 2199435 3299291 := bstep (se 1 (by rfl) ⟨2474468, by rfl⟩ : syracuseStep 3299291 = 4948937) B4948937
theorem B2199527 : Blo 2199435 2199527 := bstep (se 1 (by rfl) ⟨1649645, by rfl⟩ : syracuseStep 2199527 = 3299291) B3299291
theorem B2474473 : Blo 2199435 2474473 := bbase (se 2 (by rfl) ⟨927927, by rfl⟩ : syracuseStep 2474473 = 1855855) (by norm_num)
theorem B3299297 : Blo 2199435 3299297 := bstep (se 2 (by rfl) ⟨1237236, by rfl⟩ : syracuseStep 3299297 = 2474473) B2474473
theorem B2199531 : Blo 2199435 2199531 := bstep (se 1 (by rfl) ⟨1649648, by rfl⟩ : syracuseStep 2199531 = 3299297) B3299297
theorem B2348821 : Blo 2199435 2348821 := bbase (se 6 (by rfl) ⟨55050, by rfl⟩ : syracuseStep 2348821 = 110101) (by norm_num)
theorem B12527045 : Blo 2199435 12527045 := bstep (se 4 (by rfl) ⟨1174410, by rfl⟩ : syracuseStep 12527045 = 2348821) B2348821
theorem B8351363 : Blo 2199435 8351363 := bstep (se 1 (by rfl) ⟨6263522, by rfl⟩ : syracuseStep 8351363 = 12527045) B12527045
theorem B5567575 : Blo 2199435 5567575 := bstep (se 1 (by rfl) ⟨4175681, by rfl⟩ : syracuseStep 5567575 = 8351363) B8351363
theorem B7423433 : Blo 2199435 7423433 := bstep (se 2 (by rfl) ⟨2783787, by rfl⟩ : syracuseStep 7423433 = 5567575) B5567575
theorem B4948955 : Blo 2199435 4948955 := bstep (se 1 (by rfl) ⟨3711716, by rfl⟩ : syracuseStep 4948955 = 7423433) B7423433
theorem B3299303 : Blo 2199435 3299303 := bstep (se 1 (by rfl) ⟨2474477, by rfl⟩ : syracuseStep 3299303 = 4948955) B4948955
theorem B2199535 : Blo 2199435 2199535 := bstep (se 1 (by rfl) ⟨1649651, by rfl⟩ : syracuseStep 2199535 = 3299303) B3299303
theorem B3299309 : Blo 2199435 3299309 := bbase (se 3 (by rfl) ⟨618620, by rfl⟩ : syracuseStep 3299309 = 1237241) (by norm_num)
theorem B2199539 : Blo 2199435 2199539 := bstep (se 1 (by rfl) ⟨1649654, by rfl⟩ : syracuseStep 2199539 = 3299309) B3299309
theorem B4948973 : Blo 2199435 4948973 := bbase (se 3 (by rfl) ⟨927932, by rfl⟩ : syracuseStep 4948973 = 1855865) (by norm_num)
theorem B3299315 : Blo 2199435 3299315 := bstep (se 1 (by rfl) ⟨2474486, by rfl⟩ : syracuseStep 3299315 = 4948973) B4948973
theorem B2199543 : Blo 2199435 2199543 := bstep (se 1 (by rfl) ⟨1649657, by rfl⟩ : syracuseStep 2199543 = 3299315) B3299315
theorem B4697669 : Blo 2199435 4697669 := bbase (se 4 (by rfl) ⟨440406, by rfl⟩ : syracuseStep 4697669 = 880813) (by norm_num)
theorem B3131779 : Blo 2199435 3131779 := bstep (se 1 (by rfl) ⟨2348834, by rfl⟩ : syracuseStep 3131779 = 4697669) B4697669
theorem B4175705 : Blo 2199435 4175705 := bstep (se 2 (by rfl) ⟨1565889, by rfl⟩ : syracuseStep 4175705 = 3131779) B3131779
theorem B2783803 : Blo 2199435 2783803 := bstep (se 1 (by rfl) ⟨2087852, by rfl⟩ : syracuseStep 2783803 = 4175705) B4175705
theorem B3711737 : Blo 2199435 3711737 := bstep (se 2 (by rfl) ⟨1391901, by rfl⟩ : syracuseStep 3711737 = 2783803) B2783803
theorem B2474491 : Blo 2199435 2474491 := bstep (se 1 (by rfl) ⟨1855868, by rfl⟩ : syracuseStep 2474491 = 3711737) B3711737
theorem B3299321 : Blo 2199435 3299321 := bstep (se 2 (by rfl) ⟨1237245, by rfl⟩ : syracuseStep 3299321 = 2474491) B2474491
theorem B2199547 : Blo 2199435 2199547 := bstep (se 1 (by rfl) ⟨1649660, by rfl⟩ : syracuseStep 2199547 = 3299321) B3299321
theorem B12384373 : Blo 2199435 12384373 := bbase (se 5 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 12384373 = 1161035) (by norm_num)
theorem B16512497 : Blo 2199435 16512497 := bstep (se 2 (by rfl) ⟨6192186, by rfl⟩ : syracuseStep 16512497 = 12384373) B12384373
theorem B11008331 : Blo 2199435 11008331 := bstep (se 1 (by rfl) ⟨8256248, by rfl⟩ : syracuseStep 11008331 = 16512497) B16512497
theorem B7338887 : Blo 2199435 7338887 := bstep (se 1 (by rfl) ⟨5504165, by rfl⟩ : syracuseStep 7338887 = 11008331) B11008331
theorem B4892591 : Blo 2199435 4892591 := bstep (se 1 (by rfl) ⟨3669443, by rfl⟩ : syracuseStep 4892591 = 7338887) B7338887
theorem B3261727 : Blo 2199435 3261727 := bstep (se 1 (by rfl) ⟨2446295, by rfl⟩ : syracuseStep 3261727 = 4892591) B4892591
theorem B17395877 : Blo 2199435 17395877 := bstep (se 4 (by rfl) ⟨1630863, by rfl⟩ : syracuseStep 17395877 = 3261727) B3261727
theorem B11597251 : Blo 2199435 11597251 := bstep (se 1 (by rfl) ⟨8697938, by rfl⟩ : syracuseStep 11597251 = 17395877) B17395877
theorem B15463001 : Blo 2199435 15463001 := bstep (se 2 (by rfl) ⟨5798625, by rfl⟩ : syracuseStep 15463001 = 11597251) B11597251
theorem B41234669 : Blo 2199435 41234669 := bstep (se 3 (by rfl) ⟨7731500, by rfl⟩ : syracuseStep 41234669 = 15463001) B15463001
theorem B27489779 : Blo 2199435 27489779 := bstep (se 1 (by rfl) ⟨20617334, by rfl⟩ : syracuseStep 27489779 = 41234669) B41234669
theorem B18326519 : Blo 2199435 18326519 := bstep (se 1 (by rfl) ⟨13744889, by rfl⟩ : syracuseStep 18326519 = 27489779) B27489779
theorem B12217679 : Blo 2199435 12217679 := bstep (se 1 (by rfl) ⟨9163259, by rfl⟩ : syracuseStep 12217679 = 18326519) B18326519
theorem B8145119 : Blo 2199435 8145119 := bstep (se 1 (by rfl) ⟨6108839, by rfl⟩ : syracuseStep 8145119 = 12217679) B12217679
theorem B5430079 : Blo 2199435 5430079 := bstep (se 1 (by rfl) ⟨4072559, by rfl⟩ : syracuseStep 5430079 = 8145119) B8145119
theorem B28960421 : Blo 2199435 28960421 := bstep (se 4 (by rfl) ⟨2715039, by rfl⟩ : syracuseStep 28960421 = 5430079) B5430079
theorem B77227789 : Blo 2199435 77227789 := bstep (se 3 (by rfl) ⟨14480210, by rfl⟩ : syracuseStep 77227789 = 28960421) B28960421
theorem B102970385 : Blo 2199435 102970385 := bstep (se 2 (by rfl) ⟨38613894, by rfl⟩ : syracuseStep 102970385 = 77227789) B77227789
theorem B68646923 : Blo 2199435 68646923 := bstep (se 1 (by rfl) ⟨51485192, by rfl⟩ : syracuseStep 68646923 = 102970385) B102970385
theorem B45764615 : Blo 2199435 45764615 := bstep (se 1 (by rfl) ⟨34323461, by rfl⟩ : syracuseStep 45764615 = 68646923) B68646923
theorem B30509743 : Blo 2199435 30509743 := bstep (se 1 (by rfl) ⟨22882307, by rfl⟩ : syracuseStep 30509743 = 45764615) B45764615
theorem B40679657 : Blo 2199435 40679657 := bstep (se 2 (by rfl) ⟨15254871, by rfl⟩ : syracuseStep 40679657 = 30509743) B30509743
theorem B27119771 : Blo 2199435 27119771 := bstep (se 1 (by rfl) ⟨20339828, by rfl⟩ : syracuseStep 27119771 = 40679657) B40679657
theorem B18079847 : Blo 2199435 18079847 := bstep (se 1 (by rfl) ⟨13559885, by rfl⟩ : syracuseStep 18079847 = 27119771) B27119771
theorem B12053231 : Blo 2199435 12053231 := bstep (se 1 (by rfl) ⟨9039923, by rfl⟩ : syracuseStep 12053231 = 18079847) B18079847
theorem B8035487 : Blo 2199435 8035487 := bstep (se 1 (by rfl) ⟨6026615, by rfl⟩ : syracuseStep 8035487 = 12053231) B12053231
theorem B5356991 : Blo 2199435 5356991 := bstep (se 1 (by rfl) ⟨4017743, by rfl⟩ : syracuseStep 5356991 = 8035487) B8035487
theorem B3571327 : Blo 2199435 3571327 := bstep (se 1 (by rfl) ⟨2678495, by rfl⟩ : syracuseStep 3571327 = 5356991) B5356991
theorem B4761769 : Blo 2199435 4761769 := bstep (se 2 (by rfl) ⟨1785663, by rfl⟩ : syracuseStep 4761769 = 3571327) B3571327
theorem B6349025 : Blo 2199435 6349025 := bstep (se 2 (by rfl) ⟨2380884, by rfl⟩ : syracuseStep 6349025 = 4761769) B4761769
theorem B4232683 : Blo 2199435 4232683 := bstep (se 1 (by rfl) ⟨3174512, by rfl⟩ : syracuseStep 4232683 = 6349025) B6349025
theorem B5643577 : Blo 2199435 5643577 := bstep (se 2 (by rfl) ⟨2116341, by rfl⟩ : syracuseStep 5643577 = 4232683) B4232683
theorem B7524769 : Blo 2199435 7524769 := bstep (se 2 (by rfl) ⟨2821788, by rfl⟩ : syracuseStep 7524769 = 5643577) B5643577
theorem B10033025 : Blo 2199435 10033025 := bstep (se 2 (by rfl) ⟨3762384, by rfl⟩ : syracuseStep 10033025 = 7524769) B7524769
theorem B26754733 : Blo 2199435 26754733 := bstep (se 3 (by rfl) ⟨5016512, by rfl⟩ : syracuseStep 26754733 = 10033025) B10033025
theorem B35672977 : Blo 2199435 35672977 := bstep (se 2 (by rfl) ⟨13377366, by rfl⟩ : syracuseStep 35672977 = 26754733) B26754733
theorem B190255877 : Blo 2199435 190255877 := bstep (se 4 (by rfl) ⟨17836488, by rfl⟩ : syracuseStep 190255877 = 35672977) B35672977
theorem B126837251 : Blo 2199435 126837251 := bstep (se 1 (by rfl) ⟨95127938, by rfl⟩ : syracuseStep 126837251 = 190255877) B190255877
theorem B84558167 : Blo 2199435 84558167 := bstep (se 1 (by rfl) ⟨63418625, by rfl⟩ : syracuseStep 84558167 = 126837251) B126837251
theorem B56372111 : Blo 2199435 56372111 := bstep (se 1 (by rfl) ⟨42279083, by rfl⟩ : syracuseStep 56372111 = 84558167) B84558167
theorem B37581407 : Blo 2199435 37581407 := bstep (se 1 (by rfl) ⟨28186055, by rfl⟩ : syracuseStep 37581407 = 56372111) B56372111
theorem B25054271 : Blo 2199435 25054271 := bstep (se 1 (by rfl) ⟨18790703, by rfl⟩ : syracuseStep 25054271 = 37581407) B37581407
theorem B16702847 : Blo 2199435 16702847 := bstep (se 1 (by rfl) ⟨12527135, by rfl⟩ : syracuseStep 16702847 = 25054271) B25054271
theorem B11135231 : Blo 2199435 11135231 := bstep (se 1 (by rfl) ⟨8351423, by rfl⟩ : syracuseStep 11135231 = 16702847) B16702847
theorem B7423487 : Blo 2199435 7423487 := bstep (se 1 (by rfl) ⟨5567615, by rfl⟩ : syracuseStep 7423487 = 11135231) B11135231
theorem B4948991 : Blo 2199435 4948991 := bstep (se 1 (by rfl) ⟨3711743, by rfl⟩ : syracuseStep 4948991 = 7423487) B7423487
theorem B3299327 : Blo 2199435 3299327 := bstep (se 1 (by rfl) ⟨2474495, by rfl⟩ : syracuseStep 3299327 = 4948991) B4948991
theorem B2199551 : Blo 2199435 2199551 := bstep (se 1 (by rfl) ⟨1649663, by rfl⟩ : syracuseStep 2199551 = 3299327) B3299327
theorem B3299333 : Blo 2199435 3299333 := bbase (se 4 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 3299333 = 618625) (by norm_num)
theorem B2199555 : Blo 2199435 2199555 := bstep (se 1 (by rfl) ⟨1649666, by rfl⟩ : syracuseStep 2199555 = 3299333) B3299333
theorem B3711757 : Blo 2199435 3711757 := bbase (se 3 (by rfl) ⟨695954, by rfl⟩ : syracuseStep 3711757 = 1391909) (by norm_num)
theorem B4949009 : Blo 2199435 4949009 := bstep (se 2 (by rfl) ⟨1855878, by rfl⟩ : syracuseStep 4949009 = 3711757) B3711757
theorem B3299339 : Blo 2199435 3299339 := bstep (se 1 (by rfl) ⟨2474504, by rfl⟩ : syracuseStep 3299339 = 4949009) B4949009
theorem B2199559 : Blo 2199435 2199559 := bstep (se 1 (by rfl) ⟨1649669, by rfl⟩ : syracuseStep 2199559 = 3299339) B3299339
theorem B2474509 : Blo 2199435 2474509 := bbase (se 3 (by rfl) ⟨463970, by rfl⟩ : syracuseStep 2474509 = 927941) (by norm_num)
theorem B3299345 : Blo 2199435 3299345 := bstep (se 2 (by rfl) ⟨1237254, by rfl⟩ : syracuseStep 3299345 = 2474509) B2474509
theorem B2199563 : Blo 2199435 2199563 := bstep (se 1 (by rfl) ⟨1649672, by rfl⟩ : syracuseStep 2199563 = 3299345) B3299345
theorem B7423541 : Blo 2199435 7423541 := bbase (se 5 (by rfl) ⟨347978, by rfl⟩ : syracuseStep 7423541 = 695957) (by norm_num)
theorem B4949027 : Blo 2199435 4949027 := bstep (se 1 (by rfl) ⟨3711770, by rfl⟩ : syracuseStep 4949027 = 7423541) B7423541
theorem B3299351 : Blo 2199435 3299351 := bstep (se 1 (by rfl) ⟨2474513, by rfl⟩ : syracuseStep 3299351 = 4949027) B4949027
theorem B2199567 : Blo 2199435 2199567 := bstep (se 1 (by rfl) ⟨1649675, by rfl⟩ : syracuseStep 2199567 = 3299351) B3299351
theorem B3299357 : Blo 2199435 3299357 := bbase (se 3 (by rfl) ⟨618629, by rfl⟩ : syracuseStep 3299357 = 1237259) (by norm_num)
theorem B2199571 : Blo 2199435 2199571 := bstep (se 1 (by rfl) ⟨1649678, by rfl⟩ : syracuseStep 2199571 = 3299357) B3299357
theorem B4949045 : Blo 2199435 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B3299363 : Blo 2199435 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B2199575 : Blo 2199435 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B2642477 : Blo 2199435 2642477 := bbase (se 3 (by rfl) ⟨495464, by rfl⟩ : syracuseStep 2642477 = 990929) (by norm_num)
theorem B7046605 : Blo 2199435 7046605 := bstep (se 3 (by rfl) ⟨1321238, by rfl⟩ : syracuseStep 7046605 = 2642477) B2642477
theorem B9395473 : Blo 2199435 9395473 := bstep (se 2 (by rfl) ⟨3523302, by rfl⟩ : syracuseStep 9395473 = 7046605) B7046605
theorem B12527297 : Blo 2199435 12527297 := bstep (se 2 (by rfl) ⟨4697736, by rfl⟩ : syracuseStep 12527297 = 9395473) B9395473
theorem B8351531 : Blo 2199435 8351531 := bstep (se 1 (by rfl) ⟨6263648, by rfl⟩ : syracuseStep 8351531 = 12527297) B12527297
theorem B5567687 : Blo 2199435 5567687 := bstep (se 1 (by rfl) ⟨4175765, by rfl⟩ : syracuseStep 5567687 = 8351531) B8351531
theorem B3711791 : Blo 2199435 3711791 := bstep (se 1 (by rfl) ⟨2783843, by rfl⟩ : syracuseStep 3711791 = 5567687) B5567687
theorem B2474527 : Blo 2199435 2474527 := bstep (se 1 (by rfl) ⟨1855895, by rfl⟩ : syracuseStep 2474527 = 3711791) B3711791
theorem B3299369 : Blo 2199435 3299369 := bstep (se 2 (by rfl) ⟨1237263, by rfl⟩ : syracuseStep 3299369 = 2474527) B2474527
theorem B2199579 : Blo 2199435 2199579 := bstep (se 1 (by rfl) ⟨1649684, by rfl⟩ : syracuseStep 2199579 = 3299369) B3299369
theorem B7927445 : Blo 2199435 7927445 := bbase (se 6 (by rfl) ⟨185799, by rfl⟩ : syracuseStep 7927445 = 371599) (by norm_num)
theorem B5284963 : Blo 2199435 5284963 := bstep (se 1 (by rfl) ⟨3963722, by rfl⟩ : syracuseStep 5284963 = 7927445) B7927445
theorem B7046617 : Blo 2199435 7046617 := bstep (se 2 (by rfl) ⟨2642481, by rfl⟩ : syracuseStep 7046617 = 5284963) B5284963
theorem B9395489 : Blo 2199435 9395489 := bstep (se 2 (by rfl) ⟨3523308, by rfl⟩ : syracuseStep 9395489 = 7046617) B7046617
theorem B6263659 : Blo 2199435 6263659 := bstep (se 1 (by rfl) ⟨4697744, by rfl⟩ : syracuseStep 6263659 = 9395489) B9395489
theorem B8351545 : Blo 2199435 8351545 := bstep (se 2 (by rfl) ⟨3131829, by rfl⟩ : syracuseStep 8351545 = 6263659) B6263659
theorem B11135393 : Blo 2199435 11135393 := bstep (se 2 (by rfl) ⟨4175772, by rfl⟩ : syracuseStep 11135393 = 8351545) B8351545
theorem B7423595 : Blo 2199435 7423595 := bstep (se 1 (by rfl) ⟨5567696, by rfl⟩ : syracuseStep 7423595 = 11135393) B11135393
theorem B4949063 : Blo 2199435 4949063 := bstep (se 1 (by rfl) ⟨3711797, by rfl⟩ : syracuseStep 4949063 = 7423595) B7423595
theorem B3299375 : Blo 2199435 3299375 := bstep (se 1 (by rfl) ⟨2474531, by rfl⟩ : syracuseStep 3299375 = 4949063) B4949063
theorem B2199583 : Blo 2199435 2199583 := bstep (se 1 (by rfl) ⟨1649687, by rfl⟩ : syracuseStep 2199583 = 3299375) B3299375
theorem B3299381 : Blo 2199435 3299381 := bbase (se 5 (by rfl) ⟨154658, by rfl⟩ : syracuseStep 3299381 = 309317) (by norm_num)
theorem B2199587 : Blo 2199435 2199587 := bstep (se 1 (by rfl) ⟨1649690, by rfl⟩ : syracuseStep 2199587 = 3299381) B3299381
theorem B5567717 : Blo 2199435 5567717 := bbase (se 4 (by rfl) ⟨521973, by rfl⟩ : syracuseStep 5567717 = 1043947) (by norm_num)
theorem B3711811 : Blo 2199435 3711811 := bstep (se 1 (by rfl) ⟨2783858, by rfl⟩ : syracuseStep 3711811 = 5567717) B5567717
theorem B4949081 : Blo 2199435 4949081 := bstep (se 2 (by rfl) ⟨1855905, by rfl⟩ : syracuseStep 4949081 = 3711811) B3711811
theorem B3299387 : Blo 2199435 3299387 := bstep (se 1 (by rfl) ⟨2474540, by rfl⟩ : syracuseStep 3299387 = 4949081) B4949081
theorem B2199591 : Blo 2199435 2199591 := bstep (se 1 (by rfl) ⟨1649693, by rfl⟩ : syracuseStep 2199591 = 3299387) B3299387
theorem B2474545 : Blo 2199435 2474545 := bbase (se 2 (by rfl) ⟨927954, by rfl⟩ : syracuseStep 2474545 = 1855909) (by norm_num)
theorem B3299393 : Blo 2199435 3299393 := bstep (se 2 (by rfl) ⟨1237272, by rfl⟩ : syracuseStep 3299393 = 2474545) B2474545
theorem B2199595 : Blo 2199435 2199595 := bstep (se 1 (by rfl) ⟨1649696, by rfl⟩ : syracuseStep 2199595 = 3299393) B3299393
theorem B2642501 : Blo 2199435 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B7046669 : Blo 2199435 7046669 := bstep (se 3 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 7046669 = 2642501) B2642501
theorem B4697779 : Blo 2199435 4697779 := bstep (se 1 (by rfl) ⟨3523334, by rfl⟩ : syracuseStep 4697779 = 7046669) B7046669
theorem B6263705 : Blo 2199435 6263705 := bstep (se 2 (by rfl) ⟨2348889, by rfl⟩ : syracuseStep 6263705 = 4697779) B4697779
theorem B4175803 : Blo 2199435 4175803 := bstep (se 1 (by rfl) ⟨3131852, by rfl⟩ : syracuseStep 4175803 = 6263705) B6263705
theorem B5567737 : Blo 2199435 5567737 := bstep (se 2 (by rfl) ⟨2087901, by rfl⟩ : syracuseStep 5567737 = 4175803) B4175803
theorem B7423649 : Blo 2199435 7423649 := bstep (se 2 (by rfl) ⟨2783868, by rfl⟩ : syracuseStep 7423649 = 5567737) B5567737
theorem B4949099 : Blo 2199435 4949099 := bstep (se 1 (by rfl) ⟨3711824, by rfl⟩ : syracuseStep 4949099 = 7423649) B7423649
theorem B3299399 : Blo 2199435 3299399 := bstep (se 1 (by rfl) ⟨2474549, by rfl⟩ : syracuseStep 3299399 = 4949099) B4949099
theorem B2199599 : Blo 2199435 2199599 := bstep (se 1 (by rfl) ⟨1649699, by rfl⟩ : syracuseStep 2199599 = 3299399) B3299399
theorem B3299405 : Blo 2199435 3299405 := bbase (se 3 (by rfl) ⟨618638, by rfl⟩ : syracuseStep 3299405 = 1237277) (by norm_num)
theorem B2199603 : Blo 2199435 2199603 := bstep (se 1 (by rfl) ⟨1649702, by rfl⟩ : syracuseStep 2199603 = 3299405) B3299405
theorem B4949117 : Blo 2199435 4949117 := bbase (se 3 (by rfl) ⟨927959, by rfl⟩ : syracuseStep 4949117 = 1855919) (by norm_num)
theorem B3299411 : Blo 2199435 3299411 := bstep (se 1 (by rfl) ⟨2474558, by rfl⟩ : syracuseStep 3299411 = 4949117) B4949117
theorem B2199607 : Blo 2199435 2199607 := bstep (se 1 (by rfl) ⟨1649705, by rfl⟩ : syracuseStep 2199607 = 3299411) B3299411
theorem B3711845 : Blo 2199435 3711845 := bbase (se 4 (by rfl) ⟨347985, by rfl⟩ : syracuseStep 3711845 = 695971) (by norm_num)
theorem B2474563 : Blo 2199435 2474563 := bstep (se 1 (by rfl) ⟨1855922, by rfl⟩ : syracuseStep 2474563 = 3711845) B3711845
theorem B3299417 : Blo 2199435 3299417 := bstep (se 2 (by rfl) ⟨1237281, by rfl⟩ : syracuseStep 3299417 = 2474563) B2474563
theorem B2199611 : Blo 2199435 2199611 := bstep (se 1 (by rfl) ⟨1649708, by rfl⟩ : syracuseStep 2199611 = 3299417) B3299417
theorem B4697813 : Blo 2199435 4697813 := bbase (se 7 (by rfl) ⟨55052, by rfl⟩ : syracuseStep 4697813 = 110105) (by norm_num)
theorem B3131875 : Blo 2199435 3131875 := bstep (se 1 (by rfl) ⟨2348906, by rfl⟩ : syracuseStep 3131875 = 4697813) B4697813
theorem B16703333 : Blo 2199435 16703333 := bstep (se 4 (by rfl) ⟨1565937, by rfl⟩ : syracuseStep 16703333 = 3131875) B3131875
theorem B11135555 : Blo 2199435 11135555 := bstep (se 1 (by rfl) ⟨8351666, by rfl⟩ : syracuseStep 11135555 = 16703333) B16703333
theorem B7423703 : Blo 2199435 7423703 := bstep (se 1 (by rfl) ⟨5567777, by rfl⟩ : syracuseStep 7423703 = 11135555) B11135555
theorem B4949135 : Blo 2199435 4949135 := bstep (se 1 (by rfl) ⟨3711851, by rfl⟩ : syracuseStep 4949135 = 7423703) B7423703
theorem B3299423 : Blo 2199435 3299423 := bstep (se 1 (by rfl) ⟨2474567, by rfl⟩ : syracuseStep 3299423 = 4949135) B4949135
theorem B2199615 : Blo 2199435 2199615 := bstep (se 1 (by rfl) ⟨1649711, by rfl⟩ : syracuseStep 2199615 = 3299423) B3299423
theorem B3299429 : Blo 2199435 3299429 := bbase (se 4 (by rfl) ⟨309321, by rfl⟩ : syracuseStep 3299429 = 618643) (by norm_num)
theorem B2199619 : Blo 2199435 2199619 := bstep (se 1 (by rfl) ⟨1649714, by rfl⟩ : syracuseStep 2199619 = 3299429) B3299429
theorem B2234297 : Blo 2199435 2234297 := bbase (se 2 (by rfl) ⟨837861, by rfl⟩ : syracuseStep 2234297 = 1675723) (by norm_num)
theorem B5958125 : Blo 2199435 5958125 := bstep (se 3 (by rfl) ⟨1117148, by rfl⟩ : syracuseStep 5958125 = 2234297) B2234297
theorem B3972083 : Blo 2199435 3972083 := bstep (se 1 (by rfl) ⟨2979062, by rfl⟩ : syracuseStep 3972083 = 5958125) B5958125
theorem B42368885 : Blo 2199435 42368885 := bstep (se 5 (by rfl) ⟨1986041, by rfl⟩ : syracuseStep 42368885 = 3972083) B3972083
theorem B28245923 : Blo 2199435 28245923 := bstep (se 1 (by rfl) ⟨21184442, by rfl⟩ : syracuseStep 28245923 = 42368885) B42368885
theorem B18830615 : Blo 2199435 18830615 := bstep (se 1 (by rfl) ⟨14122961, by rfl⟩ : syracuseStep 18830615 = 28245923) B28245923
theorem B50214973 : Blo 2199435 50214973 := bstep (se 3 (by rfl) ⟨9415307, by rfl⟩ : syracuseStep 50214973 = 18830615) B18830615
theorem B66953297 : Blo 2199435 66953297 := bstep (se 2 (by rfl) ⟨25107486, by rfl⟩ : syracuseStep 66953297 = 50214973) B50214973
theorem B44635531 : Blo 2199435 44635531 := bstep (se 1 (by rfl) ⟨33476648, by rfl⟩ : syracuseStep 44635531 = 66953297) B66953297
theorem B59514041 : Blo 2199435 59514041 := bstep (se 2 (by rfl) ⟨22317765, by rfl⟩ : syracuseStep 59514041 = 44635531) B44635531
theorem B39676027 : Blo 2199435 39676027 := bstep (se 1 (by rfl) ⟨29757020, by rfl⟩ : syracuseStep 39676027 = 59514041) B59514041
theorem B52901369 : Blo 2199435 52901369 := bstep (se 2 (by rfl) ⟨19838013, by rfl⟩ : syracuseStep 52901369 = 39676027) B39676027
theorem B35267579 : Blo 2199435 35267579 := bstep (se 1 (by rfl) ⟨26450684, by rfl⟩ : syracuseStep 35267579 = 52901369) B52901369
theorem B23511719 : Blo 2199435 23511719 := bstep (se 1 (by rfl) ⟨17633789, by rfl⟩ : syracuseStep 23511719 = 35267579) B35267579
theorem B62697917 : Blo 2199435 62697917 := bstep (se 3 (by rfl) ⟨11755859, by rfl⟩ : syracuseStep 62697917 = 23511719) B23511719
theorem B41798611 : Blo 2199435 41798611 := bstep (se 1 (by rfl) ⟨31348958, by rfl⟩ : syracuseStep 41798611 = 62697917) B62697917
theorem B222925925 : Blo 2199435 222925925 := bstep (se 4 (by rfl) ⟨20899305, by rfl⟩ : syracuseStep 222925925 = 41798611) B41798611
theorem B148617283 : Blo 2199435 148617283 := bstep (se 1 (by rfl) ⟨111462962, by rfl⟩ : syracuseStep 148617283 = 222925925) B222925925
theorem B198156377 : Blo 2199435 198156377 := bstep (se 2 (by rfl) ⟨74308641, by rfl⟩ : syracuseStep 198156377 = 148617283) B148617283
theorem B132104251 : Blo 2199435 132104251 := bstep (se 1 (by rfl) ⟨99078188, by rfl⟩ : syracuseStep 132104251 = 198156377) B198156377
theorem B176139001 : Blo 2199435 176139001 := bstep (se 2 (by rfl) ⟨66052125, by rfl⟩ : syracuseStep 176139001 = 132104251) B132104251
theorem B939408005 : Blo 2199435 939408005 := bstep (se 4 (by rfl) ⟨88069500, by rfl⟩ : syracuseStep 939408005 = 176139001) B176139001
theorem B626272003 : Blo 2199435 626272003 := bstep (se 1 (by rfl) ⟨469704002, by rfl⟩ : syracuseStep 626272003 = 939408005) B939408005
theorem B835029337 : Blo 2199435 835029337 := bstep (se 2 (by rfl) ⟨313136001, by rfl⟩ : syracuseStep 835029337 = 626272003) B626272003
theorem B1113372449 : Blo 2199435 1113372449 := bstep (se 2 (by rfl) ⟨417514668, by rfl⟩ : syracuseStep 1113372449 = 835029337) B835029337
theorem B742248299 : Blo 2199435 742248299 := bstep (se 1 (by rfl) ⟨556686224, by rfl⟩ : syracuseStep 742248299 = 1113372449) B1113372449
theorem B494832199 : Blo 2199435 494832199 := bstep (se 1 (by rfl) ⟨371124149, by rfl⟩ : syracuseStep 494832199 = 742248299) B742248299
theorem B659776265 : Blo 2199435 659776265 := bstep (se 2 (by rfl) ⟨247416099, by rfl⟩ : syracuseStep 659776265 = 494832199) B494832199
theorem B439850843 : Blo 2199435 439850843 := bstep (se 1 (by rfl) ⟨329888132, by rfl⟩ : syracuseStep 439850843 = 659776265) B659776265
theorem B293233895 : Blo 2199435 293233895 := bstep (se 1 (by rfl) ⟨219925421, by rfl⟩ : syracuseStep 293233895 = 439850843) B439850843
theorem B195489263 : Blo 2199435 195489263 := bstep (se 1 (by rfl) ⟨146616947, by rfl⟩ : syracuseStep 195489263 = 293233895) B293233895
theorem B130326175 : Blo 2199435 130326175 := bstep (se 1 (by rfl) ⟨97744631, by rfl⟩ : syracuseStep 130326175 = 195489263) B195489263
theorem B695072933 : Blo 2199435 695072933 := bstep (se 4 (by rfl) ⟨65163087, by rfl⟩ : syracuseStep 695072933 = 130326175) B130326175
theorem B463381955 : Blo 2199435 463381955 := bstep (se 1 (by rfl) ⟨347536466, by rfl⟩ : syracuseStep 463381955 = 695072933) B695072933
theorem B308921303 : Blo 2199435 308921303 := bstep (se 1 (by rfl) ⟨231690977, by rfl⟩ : syracuseStep 308921303 = 463381955) B463381955
theorem B205947535 : Blo 2199435 205947535 := bstep (se 1 (by rfl) ⟨154460651, by rfl⟩ : syracuseStep 205947535 = 308921303) B308921303
theorem B274596713 : Blo 2199435 274596713 := bstep (se 2 (by rfl) ⟨102973767, by rfl⟩ : syracuseStep 274596713 = 205947535) B205947535
theorem B183064475 : Blo 2199435 183064475 := bstep (se 1 (by rfl) ⟨137298356, by rfl⟩ : syracuseStep 183064475 = 274596713) B274596713
theorem B122042983 : Blo 2199435 122042983 := bstep (se 1 (by rfl) ⟨91532237, by rfl⟩ : syracuseStep 122042983 = 183064475) B183064475
theorem B162723977 : Blo 2199435 162723977 := bstep (se 2 (by rfl) ⟨61021491, by rfl⟩ : syracuseStep 162723977 = 122042983) B122042983
theorem B108482651 : Blo 2199435 108482651 := bstep (se 1 (by rfl) ⟨81361988, by rfl⟩ : syracuseStep 108482651 = 162723977) B162723977
theorem B72321767 : Blo 2199435 72321767 := bstep (se 1 (by rfl) ⟨54241325, by rfl⟩ : syracuseStep 72321767 = 108482651) B108482651
theorem B48214511 : Blo 2199435 48214511 := bstep (se 1 (by rfl) ⟨36160883, by rfl⟩ : syracuseStep 48214511 = 72321767) B72321767
theorem B32143007 : Blo 2199435 32143007 := bstep (se 1 (by rfl) ⟨24107255, by rfl⟩ : syracuseStep 32143007 = 48214511) B48214511
theorem B21428671 : Blo 2199435 21428671 := bstep (se 1 (by rfl) ⟨16071503, by rfl⟩ : syracuseStep 21428671 = 32143007) B32143007
theorem B28571561 : Blo 2199435 28571561 := bstep (se 2 (by rfl) ⟨10714335, by rfl⟩ : syracuseStep 28571561 = 21428671) B21428671
theorem B19047707 : Blo 2199435 19047707 := bstep (se 1 (by rfl) ⟨14285780, by rfl⟩ : syracuseStep 19047707 = 28571561) B28571561
theorem B12698471 : Blo 2199435 12698471 := bstep (se 1 (by rfl) ⟨9523853, by rfl⟩ : syracuseStep 12698471 = 19047707) B19047707
theorem B8465647 : Blo 2199435 8465647 := bstep (se 1 (by rfl) ⟨6349235, by rfl⟩ : syracuseStep 8465647 = 12698471) B12698471
theorem B11287529 : Blo 2199435 11287529 := bstep (se 2 (by rfl) ⟨4232823, by rfl⟩ : syracuseStep 11287529 = 8465647) B8465647
theorem B7525019 : Blo 2199435 7525019 := bstep (se 1 (by rfl) ⟨5643764, by rfl⟩ : syracuseStep 7525019 = 11287529) B11287529
theorem B20066717 : Blo 2199435 20066717 := bstep (se 3 (by rfl) ⟨3762509, by rfl⟩ : syracuseStep 20066717 = 7525019) B7525019
theorem B13377811 : Blo 2199435 13377811 := bstep (se 1 (by rfl) ⟨10033358, by rfl⟩ : syracuseStep 13377811 = 20066717) B20066717
theorem B17837081 : Blo 2199435 17837081 := bstep (se 2 (by rfl) ⟨6688905, by rfl⟩ : syracuseStep 17837081 = 13377811) B13377811
theorem B11891387 : Blo 2199435 11891387 := bstep (se 1 (by rfl) ⟨8918540, by rfl⟩ : syracuseStep 11891387 = 17837081) B17837081
theorem B7927591 : Blo 2199435 7927591 := bstep (se 1 (by rfl) ⟨5945693, by rfl⟩ : syracuseStep 7927591 = 11891387) B11891387
theorem B10570121 : Blo 2199435 10570121 := bstep (se 2 (by rfl) ⟨3963795, by rfl⟩ : syracuseStep 10570121 = 7927591) B7927591
theorem B7046747 : Blo 2199435 7046747 := bstep (se 1 (by rfl) ⟨5285060, by rfl⟩ : syracuseStep 7046747 = 10570121) B10570121
theorem B4697831 : Blo 2199435 4697831 := bstep (se 1 (by rfl) ⟨3523373, by rfl⟩ : syracuseStep 4697831 = 7046747) B7046747
theorem B3131887 : Blo 2199435 3131887 := bstep (se 1 (by rfl) ⟨2348915, by rfl⟩ : syracuseStep 3131887 = 4697831) B4697831
theorem B4175849 : Blo 2199435 4175849 := bstep (se 2 (by rfl) ⟨1565943, by rfl⟩ : syracuseStep 4175849 = 3131887) B3131887
theorem B2783899 : Blo 2199435 2783899 := bstep (se 1 (by rfl) ⟨2087924, by rfl⟩ : syracuseStep 2783899 = 4175849) B4175849
theorem B3711865 : Blo 2199435 3711865 := bstep (se 2 (by rfl) ⟨1391949, by rfl⟩ : syracuseStep 3711865 = 2783899) B2783899
theorem B4949153 : Blo 2199435 4949153 := bstep (se 2 (by rfl) ⟨1855932, by rfl⟩ : syracuseStep 4949153 = 3711865) B3711865
theorem B3299435 : Blo 2199435 3299435 := bstep (se 1 (by rfl) ⟨2474576, by rfl⟩ : syracuseStep 3299435 = 4949153) B4949153
theorem B2199623 : Blo 2199435 2199623 := bstep (se 1 (by rfl) ⟨1649717, by rfl⟩ : syracuseStep 2199623 = 3299435) B3299435
theorem B2474581 : Blo 2199435 2474581 := bbase (se 8 (by rfl) ⟨14499, by rfl⟩ : syracuseStep 2474581 = 28999) (by norm_num)
theorem B3299441 : Blo 2199435 3299441 := bstep (se 2 (by rfl) ⟨1237290, by rfl⟩ : syracuseStep 3299441 = 2474581) B2474581
theorem B2199627 : Blo 2199435 2199627 := bstep (se 1 (by rfl) ⟨1649720, by rfl⟩ : syracuseStep 2199627 = 3299441) B3299441
theorem B2783909 : Blo 2199435 2783909 := bbase (se 4 (by rfl) ⟨260991, by rfl⟩ : syracuseStep 2783909 = 521983) (by norm_num)
theorem B7423757 : Blo 2199435 7423757 := bstep (se 3 (by rfl) ⟨1391954, by rfl⟩ : syracuseStep 7423757 = 2783909) B2783909
theorem B4949171 : Blo 2199435 4949171 := bstep (se 1 (by rfl) ⟨3711878, by rfl⟩ : syracuseStep 4949171 = 7423757) B7423757
theorem B3299447 : Blo 2199435 3299447 := bstep (se 1 (by rfl) ⟨2474585, by rfl⟩ : syracuseStep 3299447 = 4949171) B4949171
theorem B2199631 : Blo 2199435 2199631 := bstep (se 1 (by rfl) ⟨1649723, by rfl⟩ : syracuseStep 2199631 = 3299447) B3299447
theorem B3299453 : Blo 2199435 3299453 := bbase (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) (by norm_num)
theorem B2199635 : Blo 2199435 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B4949189 : Blo 2199435 4949189 := bbase (se 4 (by rfl) ⟨463986, by rfl⟩ : syracuseStep 4949189 = 927973) (by norm_num)
theorem B3299459 : Blo 2199435 3299459 := bstep (se 1 (by rfl) ⟨2474594, by rfl⟩ : syracuseStep 3299459 = 4949189) B4949189
theorem B2199639 : Blo 2199435 2199639 := bstep (se 1 (by rfl) ⟨1649729, by rfl⟩ : syracuseStep 2199639 = 3299459) B3299459
theorem B14093621 : Blo 2199435 14093621 := bbase (se 5 (by rfl) ⟨660638, by rfl⟩ : syracuseStep 14093621 = 1321277) (by norm_num)
theorem B9395747 : Blo 2199435 9395747 := bstep (se 1 (by rfl) ⟨7046810, by rfl⟩ : syracuseStep 9395747 = 14093621) B14093621
theorem B6263831 : Blo 2199435 6263831 := bstep (se 1 (by rfl) ⟨4697873, by rfl⟩ : syracuseStep 6263831 = 9395747) B9395747
theorem B4175887 : Blo 2199435 4175887 := bstep (se 1 (by rfl) ⟨3131915, by rfl⟩ : syracuseStep 4175887 = 6263831) B6263831
theorem B5567849 : Blo 2199435 5567849 := bstep (se 2 (by rfl) ⟨2087943, by rfl⟩ : syracuseStep 5567849 = 4175887) B4175887
theorem B3711899 : Blo 2199435 3711899 := bstep (se 1 (by rfl) ⟨2783924, by rfl⟩ : syracuseStep 3711899 = 5567849) B5567849
theorem B2474599 : Blo 2199435 2474599 := bstep (se 1 (by rfl) ⟨1855949, by rfl⟩ : syracuseStep 2474599 = 3711899) B3711899
theorem B3299465 : Blo 2199435 3299465 := bstep (se 2 (by rfl) ⟨1237299, by rfl⟩ : syracuseStep 3299465 = 2474599) B2474599
theorem B2199643 : Blo 2199435 2199643 := bstep (se 1 (by rfl) ⟨1649732, by rfl⟩ : syracuseStep 2199643 = 3299465) B3299465
theorem B11135717 : Blo 2199435 11135717 := bbase (se 4 (by rfl) ⟨1043973, by rfl⟩ : syracuseStep 11135717 = 2087947) (by norm_num)
theorem B7423811 : Blo 2199435 7423811 := bstep (se 1 (by rfl) ⟨5567858, by rfl⟩ : syracuseStep 7423811 = 11135717) B11135717
theorem B4949207 : Blo 2199435 4949207 := bstep (se 1 (by rfl) ⟨3711905, by rfl⟩ : syracuseStep 4949207 = 7423811) B7423811
theorem B3299471 : Blo 2199435 3299471 := bstep (se 1 (by rfl) ⟨2474603, by rfl⟩ : syracuseStep 3299471 = 4949207) B4949207
theorem B2199647 : Blo 2199435 2199647 := bstep (se 1 (by rfl) ⟨1649735, by rfl⟩ : syracuseStep 2199647 = 3299471) B3299471
theorem B3299477 : Blo 2199435 3299477 := bbase (se 6 (by rfl) ⟨77331, by rfl⟩ : syracuseStep 3299477 = 154663) (by norm_num)
theorem B2199651 : Blo 2199435 2199651 := bstep (se 1 (by rfl) ⟨1649738, by rfl⟩ : syracuseStep 2199651 = 3299477) B3299477
theorem B9395797 : Blo 2199435 9395797 := bbase (se 8 (by rfl) ⟨55053, by rfl⟩ : syracuseStep 9395797 = 110107) (by norm_num)
theorem B12527729 : Blo 2199435 12527729 := bstep (se 2 (by rfl) ⟨4697898, by rfl⟩ : syracuseStep 12527729 = 9395797) B9395797
theorem B8351819 : Blo 2199435 8351819 := bstep (se 1 (by rfl) ⟨6263864, by rfl⟩ : syracuseStep 8351819 = 12527729) B12527729
theorem B5567879 : Blo 2199435 5567879 := bstep (se 1 (by rfl) ⟨4175909, by rfl⟩ : syracuseStep 5567879 = 8351819) B8351819
theorem B3711919 : Blo 2199435 3711919 := bstep (se 1 (by rfl) ⟨2783939, by rfl⟩ : syracuseStep 3711919 = 5567879) B5567879
theorem B4949225 : Blo 2199435 4949225 := bstep (se 2 (by rfl) ⟨1855959, by rfl⟩ : syracuseStep 4949225 = 3711919) B3711919
theorem B3299483 : Blo 2199435 3299483 := bstep (se 1 (by rfl) ⟨2474612, by rfl⟩ : syracuseStep 3299483 = 4949225) B4949225
theorem B2199655 : Blo 2199435 2199655 := bstep (se 1 (by rfl) ⟨1649741, by rfl⟩ : syracuseStep 2199655 = 3299483) B3299483
theorem B2474617 : Blo 2199435 2474617 := bbase (se 2 (by rfl) ⟨927981, by rfl⟩ : syracuseStep 2474617 = 1855963) (by norm_num)
theorem B3299489 : Blo 2199435 3299489 := bstep (se 2 (by rfl) ⟨1237308, by rfl⟩ : syracuseStep 3299489 = 2474617) B2474617
theorem B2199659 : Blo 2199435 2199659 := bstep (se 1 (by rfl) ⟨1649744, by rfl⟩ : syracuseStep 2199659 = 3299489) B3299489
theorem B7927733 : Blo 2199435 7927733 := bbase (se 5 (by rfl) ⟨371612, by rfl⟩ : syracuseStep 7927733 = 743225) (by norm_num)
theorem B21140621 : Blo 2199435 21140621 := bstep (se 3 (by rfl) ⟨3963866, by rfl⟩ : syracuseStep 21140621 = 7927733) B7927733
theorem B14093747 : Blo 2199435 14093747 := bstep (se 1 (by rfl) ⟨10570310, by rfl⟩ : syracuseStep 14093747 = 21140621) B21140621
theorem B9395831 : Blo 2199435 9395831 := bstep (se 1 (by rfl) ⟨7046873, by rfl⟩ : syracuseStep 9395831 = 14093747) B14093747
theorem B6263887 : Blo 2199435 6263887 := bstep (se 1 (by rfl) ⟨4697915, by rfl⟩ : syracuseStep 6263887 = 9395831) B9395831
theorem B8351849 : Blo 2199435 8351849 := bstep (se 2 (by rfl) ⟨3131943, by rfl⟩ : syracuseStep 8351849 = 6263887) B6263887
theorem B5567899 : Blo 2199435 5567899 := bstep (se 1 (by rfl) ⟨4175924, by rfl⟩ : syracuseStep 5567899 = 8351849) B8351849
theorem B7423865 : Blo 2199435 7423865 := bstep (se 2 (by rfl) ⟨2783949, by rfl⟩ : syracuseStep 7423865 = 5567899) B5567899
theorem B4949243 : Blo 2199435 4949243 := bstep (se 1 (by rfl) ⟨3711932, by rfl⟩ : syracuseStep 4949243 = 7423865) B7423865
theorem B3299495 : Blo 2199435 3299495 := bstep (se 1 (by rfl) ⟨2474621, by rfl⟩ : syracuseStep 3299495 = 4949243) B4949243
theorem B2199663 : Blo 2199435 2199663 := bstep (se 1 (by rfl) ⟨1649747, by rfl⟩ : syracuseStep 2199663 = 3299495) B3299495
theorem B3299501 : Blo 2199435 3299501 := bbase (se 3 (by rfl) ⟨618656, by rfl⟩ : syracuseStep 3299501 = 1237313) (by norm_num)
theorem B2199667 : Blo 2199435 2199667 := bstep (se 1 (by rfl) ⟨1649750, by rfl⟩ : syracuseStep 2199667 = 3299501) B3299501
theorem B4949261 : Blo 2199435 4949261 := bbase (se 3 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 4949261 = 1855973) (by norm_num)
theorem B3299507 : Blo 2199435 3299507 := bstep (se 1 (by rfl) ⟨2474630, by rfl⟩ : syracuseStep 3299507 = 4949261) B4949261
theorem B2199671 : Blo 2199435 2199671 := bstep (se 1 (by rfl) ⟨1649753, by rfl⟩ : syracuseStep 2199671 = 3299507) B3299507
theorem B2783965 : Blo 2199435 2783965 := bbase (se 3 (by rfl) ⟨521993, by rfl⟩ : syracuseStep 2783965 = 1043987) (by norm_num)
theorem B3711953 : Blo 2199435 3711953 := bstep (se 2 (by rfl) ⟨1391982, by rfl⟩ : syracuseStep 3711953 = 2783965) B2783965
theorem B2474635 : Blo 2199435 2474635 := bstep (se 1 (by rfl) ⟨1855976, by rfl⟩ : syracuseStep 2474635 = 3711953) B3711953
theorem B3299513 : Blo 2199435 3299513 := bstep (se 2 (by rfl) ⟨1237317, by rfl⟩ : syracuseStep 3299513 = 2474635) B2474635
theorem B2199675 : Blo 2199435 2199675 := bstep (se 1 (by rfl) ⟨1649756, by rfl⟩ : syracuseStep 2199675 = 3299513) B3299513
theorem B18791797 : Blo 2199435 18791797 := bbase (se 5 (by rfl) ⟨880865, by rfl⟩ : syracuseStep 18791797 = 1761731) (by norm_num)
theorem B25055729 : Blo 2199435 25055729 := bstep (se 2 (by rfl) ⟨9395898, by rfl⟩ : syracuseStep 25055729 = 18791797) B18791797
theorem B16703819 : Blo 2199435 16703819 := bstep (se 1 (by rfl) ⟨12527864, by rfl⟩ : syracuseStep 16703819 = 25055729) B25055729
theorem B11135879 : Blo 2199435 11135879 := bstep (se 1 (by rfl) ⟨8351909, by rfl⟩ : syracuseStep 11135879 = 16703819) B16703819
theorem B7423919 : Blo 2199435 7423919 := bstep (se 1 (by rfl) ⟨5567939, by rfl⟩ : syracuseStep 7423919 = 11135879) B11135879
theorem B4949279 : Blo 2199435 4949279 := bstep (se 1 (by rfl) ⟨3711959, by rfl⟩ : syracuseStep 4949279 = 7423919) B7423919
theorem B3299519 : Blo 2199435 3299519 := bstep (se 1 (by rfl) ⟨2474639, by rfl⟩ : syracuseStep 3299519 = 4949279) B4949279
theorem B2199679 : Blo 2199435 2199679 := bstep (se 1 (by rfl) ⟨1649759, by rfl⟩ : syracuseStep 2199679 = 3299519) B3299519
theorem B3299525 : Blo 2199435 3299525 := bbase (se 4 (by rfl) ⟨309330, by rfl⟩ : syracuseStep 3299525 = 618661) (by norm_num)
theorem B2199683 : Blo 2199435 2199683 := bstep (se 1 (by rfl) ⟨1649762, by rfl⟩ : syracuseStep 2199683 = 3299525) B3299525
theorem B3711973 : Blo 2199435 3711973 := bbase (se 4 (by rfl) ⟨347997, by rfl⟩ : syracuseStep 3711973 = 695995) (by norm_num)
theorem B4949297 : Blo 2199435 4949297 := bstep (se 2 (by rfl) ⟨1855986, by rfl⟩ : syracuseStep 4949297 = 3711973) B3711973
theorem B3299531 : Blo 2199435 3299531 := bstep (se 1 (by rfl) ⟨2474648, by rfl⟩ : syracuseStep 3299531 = 4949297) B4949297
theorem B2199687 : Blo 2199435 2199687 := bstep (se 1 (by rfl) ⟨1649765, by rfl⟩ : syracuseStep 2199687 = 3299531) B3299531
theorem B2474653 : Blo 2199435 2474653 := bbase (se 3 (by rfl) ⟨463997, by rfl⟩ : syracuseStep 2474653 = 927995) (by norm_num)
theorem B3299537 : Blo 2199435 3299537 := bstep (se 2 (by rfl) ⟨1237326, by rfl⟩ : syracuseStep 3299537 = 2474653) B2474653
theorem B2199691 : Blo 2199435 2199691 := bstep (se 1 (by rfl) ⟨1649768, by rfl⟩ : syracuseStep 2199691 = 3299537) B3299537
theorem B7423973 : Blo 2199435 7423973 := bbase (se 4 (by rfl) ⟨695997, by rfl⟩ : syracuseStep 7423973 = 1391995) (by norm_num)
theorem B4949315 : Blo 2199435 4949315 := bstep (se 1 (by rfl) ⟨3711986, by rfl⟩ : syracuseStep 4949315 = 7423973) B7423973
theorem B3299543 : Blo 2199435 3299543 := bstep (se 1 (by rfl) ⟨2474657, by rfl⟩ : syracuseStep 3299543 = 4949315) B4949315
theorem B2199695 : Blo 2199435 2199695 := bstep (se 1 (by rfl) ⟨1649771, by rfl⟩ : syracuseStep 2199695 = 3299543) B3299543
theorem B3299549 : Blo 2199435 3299549 := bbase (se 3 (by rfl) ⟨618665, by rfl⟩ : syracuseStep 3299549 = 1237331) (by norm_num)
theorem B2199699 : Blo 2199435 2199699 := bstep (se 1 (by rfl) ⟨1649774, by rfl⟩ : syracuseStep 2199699 = 3299549) B3299549
theorem B4949333 : Blo 2199435 4949333 := bbase (se 12 (by rfl) ⟨1812, by rfl⟩ : syracuseStep 4949333 = 3625) (by norm_num)
theorem B3299555 : Blo 2199435 3299555 := bstep (se 1 (by rfl) ⟨2474666, by rfl⟩ : syracuseStep 3299555 = 4949333) B4949333
theorem B2199703 : Blo 2199435 2199703 := bstep (se 1 (by rfl) ⟨1649777, by rfl⟩ : syracuseStep 2199703 = 3299555) B3299555
theorem B2349005 : Blo 2199435 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B6264013 : Blo 2199435 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B8352017 : Blo 2199435 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B5568011 : Blo 2199435 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3712007 : Blo 2199435 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B2474671 : Blo 2199435 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B3299561 : Blo 2199435 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B2199707 : Blo 2199435 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B5643989 : Blo 2199435 5643989 := bbase (se 7 (by rfl) ⟨66140, by rfl⟩ : syracuseStep 5643989 = 132281) (by norm_num)
theorem B3762659 : Blo 2199435 3762659 := bstep (se 1 (by rfl) ⟨2821994, by rfl⟩ : syracuseStep 3762659 = 5643989) B5643989
theorem B10033757 : Blo 2199435 10033757 := bstep (se 3 (by rfl) ⟨1881329, by rfl⟩ : syracuseStep 10033757 = 3762659) B3762659
theorem B6689171 : Blo 2199435 6689171 := bstep (se 1 (by rfl) ⟨5016878, by rfl⟩ : syracuseStep 6689171 = 10033757) B10033757
theorem B4459447 : Blo 2199435 4459447 := bstep (se 1 (by rfl) ⟨3344585, by rfl⟩ : syracuseStep 4459447 = 6689171) B6689171
theorem B5945929 : Blo 2199435 5945929 := bstep (se 2 (by rfl) ⟨2229723, by rfl⟩ : syracuseStep 5945929 = 4459447) B4459447
theorem B31711621 : Blo 2199435 31711621 := bstep (se 4 (by rfl) ⟨2972964, by rfl⟩ : syracuseStep 31711621 = 5945929) B5945929
theorem B42282161 : Blo 2199435 42282161 := bstep (se 2 (by rfl) ⟨15855810, by rfl⟩ : syracuseStep 42282161 = 31711621) B31711621
theorem B28188107 : Blo 2199435 28188107 := bstep (se 1 (by rfl) ⟨21141080, by rfl⟩ : syracuseStep 28188107 = 42282161) B42282161
theorem B18792071 : Blo 2199435 18792071 := bstep (se 1 (by rfl) ⟨14094053, by rfl⟩ : syracuseStep 18792071 = 28188107) B28188107
theorem B12528047 : Blo 2199435 12528047 := bstep (se 1 (by rfl) ⟨9396035, by rfl⟩ : syracuseStep 12528047 = 18792071) B18792071
theorem B8352031 : Blo 2199435 8352031 := bstep (se 1 (by rfl) ⟨6264023, by rfl⟩ : syracuseStep 8352031 = 12528047) B12528047
theorem B11136041 : Blo 2199435 11136041 := bstep (se 2 (by rfl) ⟨4176015, by rfl⟩ : syracuseStep 11136041 = 8352031) B8352031
theorem B7424027 : Blo 2199435 7424027 := bstep (se 1 (by rfl) ⟨5568020, by rfl⟩ : syracuseStep 7424027 = 11136041) B11136041
theorem B4949351 : Blo 2199435 4949351 := bstep (se 1 (by rfl) ⟨3712013, by rfl⟩ : syracuseStep 4949351 = 7424027) B7424027
theorem B3299567 : Blo 2199435 3299567 := bstep (se 1 (by rfl) ⟨2474675, by rfl⟩ : syracuseStep 3299567 = 4949351) B4949351
theorem B2199711 : Blo 2199435 2199711 := bstep (se 1 (by rfl) ⟨1649783, by rfl⟩ : syracuseStep 2199711 = 3299567) B3299567
theorem B3299573 : Blo 2199435 3299573 := bbase (se 5 (by rfl) ⟨154667, by rfl⟩ : syracuseStep 3299573 = 309335) (by norm_num)
theorem B2199715 : Blo 2199435 2199715 := bstep (se 1 (by rfl) ⟨1649786, by rfl⟩ : syracuseStep 2199715 = 3299573) B3299573
theorem B5721013 : Blo 2199435 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B7628017 : Blo 2199435 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B10170689 : Blo 2199435 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B27121837 : Blo 2199435 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B36162449 : Blo 2199435 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B24108299 : Blo 2199435 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B16072199 : Blo 2199435 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B10714799 : Blo 2199435 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B28572797 : Blo 2199435 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B19048531 : Blo 2199435 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B25398041 : Blo 2199435 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B270912437 : Blo 2199435 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B180608291 : Blo 2199435 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B120405527 : Blo 2199435 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B80270351 : Blo 2199435 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B53513567 : Blo 2199435 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B35675711 : Blo 2199435 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B23783807 : Blo 2199435 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B15855871 : Blo 2199435 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B21141161 : Blo 2199435 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B14094107 : Blo 2199435 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B9396071 : Blo 2199435 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B6264047 : Blo 2199435 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B4176031 : Blo 2199435 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B5568041 : Blo 2199435 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B3712027 : Blo 2199435 3712027 := bstep (se 1 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 3712027 = 5568041) B5568041
theorem B4949369 : Blo 2199435 4949369 := bstep (se 2 (by rfl) ⟨1856013, by rfl⟩ : syracuseStep 4949369 = 3712027) B3712027
theorem B3299579 : Blo 2199435 3299579 := bstep (se 1 (by rfl) ⟨2474684, by rfl⟩ : syracuseStep 3299579 = 4949369) B4949369
theorem B2199719 : Blo 2199435 2199719 := bstep (se 1 (by rfl) ⟨1649789, by rfl⟩ : syracuseStep 2199719 = 3299579) B3299579
theorem B2474689 : Blo 2199435 2474689 := bbase (se 2 (by rfl) ⟨928008, by rfl⟩ : syracuseStep 2474689 = 1856017) (by norm_num)
theorem B3299585 : Blo 2199435 3299585 := bstep (se 2 (by rfl) ⟨1237344, by rfl⟩ : syracuseStep 3299585 = 2474689) B2474689
theorem B2199723 : Blo 2199435 2199723 := bstep (se 1 (by rfl) ⟨1649792, by rfl⟩ : syracuseStep 2199723 = 3299585) B3299585
theorem B5568061 : Blo 2199435 5568061 := bbase (se 3 (by rfl) ⟨1044011, by rfl⟩ : syracuseStep 5568061 = 2088023) (by norm_num)
theorem B7424081 : Blo 2199435 7424081 := bstep (se 2 (by rfl) ⟨2784030, by rfl⟩ : syracuseStep 7424081 = 5568061) B5568061
theorem B4949387 : Blo 2199435 4949387 := bstep (se 1 (by rfl) ⟨3712040, by rfl⟩ : syracuseStep 4949387 = 7424081) B7424081
theorem B3299591 : Blo 2199435 3299591 := bstep (se 1 (by rfl) ⟨2474693, by rfl⟩ : syracuseStep 3299591 = 4949387) B4949387
theorem B2199727 : Blo 2199435 2199727 := bstep (se 1 (by rfl) ⟨1649795, by rfl⟩ : syracuseStep 2199727 = 3299591) B3299591
theorem B3299597 : Blo 2199435 3299597 := bbase (se 3 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 3299597 = 1237349) (by norm_num)
theorem B2199731 : Blo 2199435 2199731 := bstep (se 1 (by rfl) ⟨1649798, by rfl⟩ : syracuseStep 2199731 = 3299597) B3299597
theorem B4949405 : Blo 2199435 4949405 := bbase (se 3 (by rfl) ⟨928013, by rfl⟩ : syracuseStep 4949405 = 1856027) (by norm_num)
theorem B3299603 : Blo 2199435 3299603 := bstep (se 1 (by rfl) ⟨2474702, by rfl⟩ : syracuseStep 3299603 = 4949405) B4949405
theorem B2199735 : Blo 2199435 2199735 := bstep (se 1 (by rfl) ⟨1649801, by rfl⟩ : syracuseStep 2199735 = 3299603) B3299603
theorem B3712061 : Blo 2199435 3712061 := bbase (se 3 (by rfl) ⟨696011, by rfl⟩ : syracuseStep 3712061 = 1392023) (by norm_num)
theorem B2474707 : Blo 2199435 2474707 := bstep (se 1 (by rfl) ⟨1856030, by rfl⟩ : syracuseStep 2474707 = 3712061) B3712061
theorem B3299609 : Blo 2199435 3299609 := bstep (se 2 (by rfl) ⟨1237353, by rfl⟩ : syracuseStep 3299609 = 2474707) B2474707
theorem B2199739 : Blo 2199435 2199739 := bstep (se 1 (by rfl) ⟨1649804, by rfl⟩ : syracuseStep 2199739 = 3299609) B3299609
theorem B3523565 : Blo 2199435 3523565 := bbase (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) (by norm_num)
theorem B2349043 : Blo 2199435 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B12528229 : Blo 2199435 12528229 := bstep (se 4 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 12528229 = 2349043) B2349043
theorem B16704305 : Blo 2199435 16704305 := bstep (se 2 (by rfl) ⟨6264114, by rfl⟩ : syracuseStep 16704305 = 12528229) B12528229
theorem B11136203 : Blo 2199435 11136203 := bstep (se 1 (by rfl) ⟨8352152, by rfl⟩ : syracuseStep 11136203 = 16704305) B16704305
theorem B7424135 : Blo 2199435 7424135 := bstep (se 1 (by rfl) ⟨5568101, by rfl⟩ : syracuseStep 7424135 = 11136203) B11136203
theorem B4949423 : Blo 2199435 4949423 := bstep (se 1 (by rfl) ⟨3712067, by rfl⟩ : syracuseStep 4949423 = 7424135) B7424135
theorem B3299615 : Blo 2199435 3299615 := bstep (se 1 (by rfl) ⟨2474711, by rfl⟩ : syracuseStep 3299615 = 4949423) B4949423
theorem B2199743 : Blo 2199435 2199743 := bstep (se 1 (by rfl) ⟨1649807, by rfl⟩ : syracuseStep 2199743 = 3299615) B3299615
theorem B3299621 : Blo 2199435 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B2199747 : Blo 2199435 2199747 := bstep (se 1 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 2199747 = 3299621) B3299621
theorem B2784061 : Blo 2199435 2784061 := bbase (se 3 (by rfl) ⟨522011, by rfl⟩ : syracuseStep 2784061 = 1044023) (by norm_num)
theorem B3712081 : Blo 2199435 3712081 := bstep (se 2 (by rfl) ⟨1392030, by rfl⟩ : syracuseStep 3712081 = 2784061) B2784061
theorem B4949441 : Blo 2199435 4949441 := bstep (se 2 (by rfl) ⟨1856040, by rfl⟩ : syracuseStep 4949441 = 3712081) B3712081
theorem B3299627 : Blo 2199435 3299627 := bstep (se 1 (by rfl) ⟨2474720, by rfl⟩ : syracuseStep 3299627 = 4949441) B4949441
theorem B2199751 : Blo 2199435 2199751 := bstep (se 1 (by rfl) ⟨1649813, by rfl⟩ : syracuseStep 2199751 = 3299627) B3299627
theorem B2474725 : Blo 2199435 2474725 := bbase (se 4 (by rfl) ⟨232005, by rfl⟩ : syracuseStep 2474725 = 464011) (by norm_num)
theorem B3299633 : Blo 2199435 3299633 := bstep (se 2 (by rfl) ⟨1237362, by rfl⟩ : syracuseStep 3299633 = 2474725) B2474725
theorem B2199755 : Blo 2199435 2199755 := bstep (se 1 (by rfl) ⟨1649816, by rfl⟩ : syracuseStep 2199755 = 3299633) B3299633
theorem B2229773 : Blo 2199435 2229773 := bbase (se 3 (by rfl) ⟨418082, by rfl⟩ : syracuseStep 2229773 = 836165) (by norm_num)
theorem B5946061 : Blo 2199435 5946061 := bstep (se 3 (by rfl) ⟨1114886, by rfl⟩ : syracuseStep 5946061 = 2229773) B2229773
theorem B7928081 : Blo 2199435 7928081 := bstep (se 2 (by rfl) ⟨2973030, by rfl⟩ : syracuseStep 7928081 = 5946061) B5946061
theorem B5285387 : Blo 2199435 5285387 := bstep (se 1 (by rfl) ⟨3964040, by rfl⟩ : syracuseStep 5285387 = 7928081) B7928081
theorem B3523591 : Blo 2199435 3523591 := bstep (se 1 (by rfl) ⟨2642693, by rfl⟩ : syracuseStep 3523591 = 5285387) B5285387
theorem B4698121 : Blo 2199435 4698121 := bstep (se 2 (by rfl) ⟨1761795, by rfl⟩ : syracuseStep 4698121 = 3523591) B3523591
theorem B6264161 : Blo 2199435 6264161 := bstep (se 2 (by rfl) ⟨2349060, by rfl⟩ : syracuseStep 6264161 = 4698121) B4698121
theorem B4176107 : Blo 2199435 4176107 := bstep (se 1 (by rfl) ⟨3132080, by rfl⟩ : syracuseStep 4176107 = 6264161) B6264161
theorem B2784071 : Blo 2199435 2784071 := bstep (se 1 (by rfl) ⟨2088053, by rfl⟩ : syracuseStep 2784071 = 4176107) B4176107
theorem B7424189 : Blo 2199435 7424189 := bstep (se 3 (by rfl) ⟨1392035, by rfl⟩ : syracuseStep 7424189 = 2784071) B2784071
theorem B4949459 : Blo 2199435 4949459 := bstep (se 1 (by rfl) ⟨3712094, by rfl⟩ : syracuseStep 4949459 = 7424189) B7424189
theorem B3299639 : Blo 2199435 3299639 := bstep (se 1 (by rfl) ⟨2474729, by rfl⟩ : syracuseStep 3299639 = 4949459) B4949459
theorem B2199759 : Blo 2199435 2199759 := bstep (se 1 (by rfl) ⟨1649819, by rfl⟩ : syracuseStep 2199759 = 3299639) B3299639
theorem B3299645 : Blo 2199435 3299645 := bbase (se 3 (by rfl) ⟨618683, by rfl⟩ : syracuseStep 3299645 = 1237367) (by norm_num)
theorem B2199763 : Blo 2199435 2199763 := bstep (se 1 (by rfl) ⟨1649822, by rfl⟩ : syracuseStep 2199763 = 3299645) B3299645
theorem B4949477 : Blo 2199435 4949477 := bbase (se 4 (by rfl) ⟨464013, by rfl⟩ : syracuseStep 4949477 = 928027) (by norm_num)
theorem B3299651 : Blo 2199435 3299651 := bstep (se 1 (by rfl) ⟨2474738, by rfl⟩ : syracuseStep 3299651 = 4949477) B4949477
theorem B2199767 : Blo 2199435 2199767 := bstep (se 1 (by rfl) ⟨1649825, by rfl⟩ : syracuseStep 2199767 = 3299651) B3299651
theorem B5568173 : Blo 2199435 5568173 := bbase (se 3 (by rfl) ⟨1044032, by rfl⟩ : syracuseStep 5568173 = 2088065) (by norm_num)
theorem B3712115 : Blo 2199435 3712115 := bstep (se 1 (by rfl) ⟨2784086, by rfl⟩ : syracuseStep 3712115 = 5568173) B5568173
theorem B2474743 : Blo 2199435 2474743 := bstep (se 1 (by rfl) ⟨1856057, by rfl⟩ : syracuseStep 2474743 = 3712115) B3712115
theorem B3299657 : Blo 2199435 3299657 := bstep (se 2 (by rfl) ⟨1237371, by rfl⟩ : syracuseStep 3299657 = 2474743) B2474743
theorem B2199771 : Blo 2199435 2199771 := bstep (se 1 (by rfl) ⟨1649828, by rfl⟩ : syracuseStep 2199771 = 3299657) B3299657
theorem B3964069 : Blo 2199435 3964069 := bbase (se 4 (by rfl) ⟨371631, by rfl⟩ : syracuseStep 3964069 = 743263) (by norm_num)
theorem B5285425 : Blo 2199435 5285425 := bstep (se 2 (by rfl) ⟨1982034, by rfl⟩ : syracuseStep 5285425 = 3964069) B3964069
theorem B7047233 : Blo 2199435 7047233 := bstep (se 2 (by rfl) ⟨2642712, by rfl⟩ : syracuseStep 7047233 = 5285425) B5285425
theorem B4698155 : Blo 2199435 4698155 := bstep (se 1 (by rfl) ⟨3523616, by rfl⟩ : syracuseStep 4698155 = 7047233) B7047233
theorem B3132103 : Blo 2199435 3132103 := bstep (se 1 (by rfl) ⟨2349077, by rfl⟩ : syracuseStep 3132103 = 4698155) B4698155
theorem B4176137 : Blo 2199435 4176137 := bstep (se 2 (by rfl) ⟨1566051, by rfl⟩ : syracuseStep 4176137 = 3132103) B3132103
theorem B11136365 : Blo 2199435 11136365 := bstep (se 3 (by rfl) ⟨2088068, by rfl⟩ : syracuseStep 11136365 = 4176137) B4176137
theorem B7424243 : Blo 2199435 7424243 := bstep (se 1 (by rfl) ⟨5568182, by rfl⟩ : syracuseStep 7424243 = 11136365) B11136365
theorem B4949495 : Blo 2199435 4949495 := bstep (se 1 (by rfl) ⟨3712121, by rfl⟩ : syracuseStep 4949495 = 7424243) B7424243
theorem B3299663 : Blo 2199435 3299663 := bstep (se 1 (by rfl) ⟨2474747, by rfl⟩ : syracuseStep 3299663 = 4949495) B4949495
theorem B2199775 : Blo 2199435 2199775 := bstep (se 1 (by rfl) ⟨1649831, by rfl⟩ : syracuseStep 2199775 = 3299663) B3299663
theorem B3299669 : Blo 2199435 3299669 := bbase (se 10 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 3299669 = 9667) (by norm_num)
theorem B2199779 : Blo 2199435 2199779 := bstep (se 1 (by rfl) ⟨1649834, by rfl⟩ : syracuseStep 2199779 = 3299669) B3299669
theorem B6264229 : Blo 2199435 6264229 := bbase (se 4 (by rfl) ⟨587271, by rfl⟩ : syracuseStep 6264229 = 1174543) (by norm_num)
theorem B8352305 : Blo 2199435 8352305 := bstep (se 2 (by rfl) ⟨3132114, by rfl⟩ : syracuseStep 8352305 = 6264229) B6264229
theorem B5568203 : Blo 2199435 5568203 := bstep (se 1 (by rfl) ⟨4176152, by rfl⟩ : syracuseStep 5568203 = 8352305) B8352305
theorem B3712135 : Blo 2199435 3712135 := bstep (se 1 (by rfl) ⟨2784101, by rfl⟩ : syracuseStep 3712135 = 5568203) B5568203
theorem B4949513 : Blo 2199435 4949513 := bstep (se 2 (by rfl) ⟨1856067, by rfl⟩ : syracuseStep 4949513 = 3712135) B3712135
theorem B3299675 : Blo 2199435 3299675 := bstep (se 1 (by rfl) ⟨2474756, by rfl⟩ : syracuseStep 3299675 = 4949513) B4949513
theorem B2199783 : Blo 2199435 2199783 := bstep (se 1 (by rfl) ⟨1649837, by rfl⟩ : syracuseStep 2199783 = 3299675) B3299675
theorem B2474761 : Blo 2199435 2474761 := bbase (se 2 (by rfl) ⟨928035, by rfl⟩ : syracuseStep 2474761 = 1856071) (by norm_num)
theorem B3299681 : Blo 2199435 3299681 := bstep (se 2 (by rfl) ⟨1237380, by rfl⟩ : syracuseStep 3299681 = 2474761) B2474761
theorem B2199787 : Blo 2199435 2199787 := bstep (se 1 (by rfl) ⟨1649840, by rfl⟩ : syracuseStep 2199787 = 3299681) B3299681
theorem B2229805 : Blo 2199435 2229805 := bbase (se 3 (by rfl) ⟨418088, by rfl⟩ : syracuseStep 2229805 = 836177) (by norm_num)
theorem B2973073 : Blo 2199435 2973073 := bstep (se 2 (by rfl) ⟨1114902, by rfl⟩ : syracuseStep 2973073 = 2229805) B2229805
theorem B3964097 : Blo 2199435 3964097 := bstep (se 2 (by rfl) ⟨1486536, by rfl⟩ : syracuseStep 3964097 = 2973073) B2973073
theorem B10570925 : Blo 2199435 10570925 := bstep (se 3 (by rfl) ⟨1982048, by rfl⟩ : syracuseStep 10570925 = 3964097) B3964097
theorem B28189133 : Blo 2199435 28189133 := bstep (se 3 (by rfl) ⟨5285462, by rfl⟩ : syracuseStep 28189133 = 10570925) B10570925
theorem B18792755 : Blo 2199435 18792755 := bstep (se 1 (by rfl) ⟨14094566, by rfl⟩ : syracuseStep 18792755 = 28189133) B28189133
theorem B12528503 : Blo 2199435 12528503 := bstep (se 1 (by rfl) ⟨9396377, by rfl⟩ : syracuseStep 12528503 = 18792755) B18792755
theorem B8352335 : Blo 2199435 8352335 := bstep (se 1 (by rfl) ⟨6264251, by rfl⟩ : syracuseStep 8352335 = 12528503) B12528503
theorem B5568223 : Blo 2199435 5568223 := bstep (se 1 (by rfl) ⟨4176167, by rfl⟩ : syracuseStep 5568223 = 8352335) B8352335
theorem B7424297 : Blo 2199435 7424297 := bstep (se 2 (by rfl) ⟨2784111, by rfl⟩ : syracuseStep 7424297 = 5568223) B5568223
theorem B4949531 : Blo 2199435 4949531 := bstep (se 1 (by rfl) ⟨3712148, by rfl⟩ : syracuseStep 4949531 = 7424297) B7424297
theorem B3299687 : Blo 2199435 3299687 := bstep (se 1 (by rfl) ⟨2474765, by rfl⟩ : syracuseStep 3299687 = 4949531) B4949531
theorem B2199791 : Blo 2199435 2199791 := bstep (se 1 (by rfl) ⟨1649843, by rfl⟩ : syracuseStep 2199791 = 3299687) B3299687
theorem B3299693 : Blo 2199435 3299693 := bbase (se 3 (by rfl) ⟨618692, by rfl⟩ : syracuseStep 3299693 = 1237385) (by norm_num)
theorem B2199795 : Blo 2199435 2199795 := bstep (se 1 (by rfl) ⟨1649846, by rfl⟩ : syracuseStep 2199795 = 3299693) B3299693
theorem B4949549 : Blo 2199435 4949549 := bbase (se 3 (by rfl) ⟨928040, by rfl⟩ : syracuseStep 4949549 = 1856081) (by norm_num)
theorem B3299699 : Blo 2199435 3299699 := bstep (se 1 (by rfl) ⟨2474774, by rfl⟩ : syracuseStep 3299699 = 4949549) B4949549
theorem B2199799 : Blo 2199435 2199799 := bstep (se 1 (by rfl) ⟨1649849, by rfl⟩ : syracuseStep 2199799 = 3299699) B3299699
theorem B2822113 : Blo 2199435 2822113 := bbase (se 2 (by rfl) ⟨1058292, by rfl⟩ : syracuseStep 2822113 = 2116585) (by norm_num)
theorem B3762817 : Blo 2199435 3762817 := bstep (se 2 (by rfl) ⟨1411056, by rfl⟩ : syracuseStep 3762817 = 2822113) B2822113
theorem B20068357 : Blo 2199435 20068357 := bstep (se 4 (by rfl) ⟨1881408, by rfl⟩ : syracuseStep 20068357 = 3762817) B3762817
theorem B26757809 : Blo 2199435 26757809 := bstep (se 2 (by rfl) ⟨10034178, by rfl⟩ : syracuseStep 26757809 = 20068357) B20068357
theorem B17838539 : Blo 2199435 17838539 := bstep (se 1 (by rfl) ⟨13378904, by rfl⟩ : syracuseStep 17838539 = 26757809) B26757809
theorem B11892359 : Blo 2199435 11892359 := bstep (se 1 (by rfl) ⟨8919269, by rfl⟩ : syracuseStep 11892359 = 17838539) B17838539
theorem B31712957 : Blo 2199435 31712957 := bstep (se 3 (by rfl) ⟨5946179, by rfl⟩ : syracuseStep 31712957 = 11892359) B11892359
theorem B21141971 : Blo 2199435 21141971 := bstep (se 1 (by rfl) ⟨15856478, by rfl⟩ : syracuseStep 21141971 = 31712957) B31712957
theorem B14094647 : Blo 2199435 14094647 := bstep (se 1 (by rfl) ⟨10570985, by rfl⟩ : syracuseStep 14094647 = 21141971) B21141971
theorem B9396431 : Blo 2199435 9396431 := bstep (se 1 (by rfl) ⟨7047323, by rfl⟩ : syracuseStep 9396431 = 14094647) B14094647
theorem B6264287 : Blo 2199435 6264287 := bstep (se 1 (by rfl) ⟨4698215, by rfl⟩ : syracuseStep 6264287 = 9396431) B9396431
theorem B4176191 : Blo 2199435 4176191 := bstep (se 1 (by rfl) ⟨3132143, by rfl⟩ : syracuseStep 4176191 = 6264287) B6264287
theorem B2784127 : Blo 2199435 2784127 := bstep (se 1 (by rfl) ⟨2088095, by rfl⟩ : syracuseStep 2784127 = 4176191) B4176191
theorem B3712169 : Blo 2199435 3712169 := bstep (se 2 (by rfl) ⟨1392063, by rfl⟩ : syracuseStep 3712169 = 2784127) B2784127
theorem B2474779 : Blo 2199435 2474779 := bstep (se 1 (by rfl) ⟨1856084, by rfl⟩ : syracuseStep 2474779 = 3712169) B3712169
theorem B3299705 : Blo 2199435 3299705 := bstep (se 2 (by rfl) ⟨1237389, by rfl⟩ : syracuseStep 3299705 = 2474779) B2474779
theorem B2199803 : Blo 2199435 2199803 := bstep (se 1 (by rfl) ⟨1649852, by rfl⟩ : syracuseStep 2199803 = 3299705) B3299705
theorem B5285501 : Blo 2199435 5285501 := bbase (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) (by norm_num)
theorem B3523667 : Blo 2199435 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B37585781 : Blo 2199435 37585781 := bstep (se 5 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 37585781 = 3523667) B3523667
theorem B25057187 : Blo 2199435 25057187 := bstep (se 1 (by rfl) ⟨18792890, by rfl⟩ : syracuseStep 25057187 = 37585781) B37585781
theorem B16704791 : Blo 2199435 16704791 := bstep (se 1 (by rfl) ⟨12528593, by rfl⟩ : syracuseStep 16704791 = 25057187) B25057187
theorem B11136527 : Blo 2199435 11136527 := bstep (se 1 (by rfl) ⟨8352395, by rfl⟩ : syracuseStep 11136527 = 16704791) B16704791
theorem B7424351 : Blo 2199435 7424351 := bstep (se 1 (by rfl) ⟨5568263, by rfl⟩ : syracuseStep 7424351 = 11136527) B11136527
theorem B4949567 : Blo 2199435 4949567 := bstep (se 1 (by rfl) ⟨3712175, by rfl⟩ : syracuseStep 4949567 = 7424351) B7424351
theorem B3299711 : Blo 2199435 3299711 := bstep (se 1 (by rfl) ⟨2474783, by rfl⟩ : syracuseStep 3299711 = 4949567) B4949567
theorem B2199807 : Blo 2199435 2199807 := bstep (se 1 (by rfl) ⟨1649855, by rfl⟩ : syracuseStep 2199807 = 3299711) B3299711
theorem B3299717 : Blo 2199435 3299717 := bbase (se 4 (by rfl) ⟨309348, by rfl⟩ : syracuseStep 3299717 = 618697) (by norm_num)
theorem B2199811 : Blo 2199435 2199811 := bstep (se 1 (by rfl) ⟨1649858, by rfl⟩ : syracuseStep 2199811 = 3299717) B3299717
theorem B3712189 : Blo 2199435 3712189 := bbase (se 3 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 3712189 = 1392071) (by norm_num)
theorem B4949585 : Blo 2199435 4949585 := bstep (se 2 (by rfl) ⟨1856094, by rfl⟩ : syracuseStep 4949585 = 3712189) B3712189
theorem B3299723 : Blo 2199435 3299723 := bstep (se 1 (by rfl) ⟨2474792, by rfl⟩ : syracuseStep 3299723 = 4949585) B4949585
theorem B2199815 : Blo 2199435 2199815 := bstep (se 1 (by rfl) ⟨1649861, by rfl⟩ : syracuseStep 2199815 = 3299723) B3299723
theorem B2474797 : Blo 2199435 2474797 := bbase (se 3 (by rfl) ⟨464024, by rfl⟩ : syracuseStep 2474797 = 928049) (by norm_num)
theorem B3299729 : Blo 2199435 3299729 := bstep (se 2 (by rfl) ⟨1237398, by rfl⟩ : syracuseStep 3299729 = 2474797) B2474797
theorem B2199819 : Blo 2199435 2199819 := bstep (se 1 (by rfl) ⟨1649864, by rfl⟩ : syracuseStep 2199819 = 3299729) B3299729
theorem B7424405 : Blo 2199435 7424405 := bbase (se 6 (by rfl) ⟨174009, by rfl⟩ : syracuseStep 7424405 = 348019) (by norm_num)
theorem B4949603 : Blo 2199435 4949603 := bstep (se 1 (by rfl) ⟨3712202, by rfl⟩ : syracuseStep 4949603 = 7424405) B7424405
theorem B3299735 : Blo 2199435 3299735 := bstep (se 1 (by rfl) ⟨2474801, by rfl⟩ : syracuseStep 3299735 = 4949603) B4949603
theorem B2199823 : Blo 2199435 2199823 := bstep (se 1 (by rfl) ⟨1649867, by rfl⟩ : syracuseStep 2199823 = 3299735) B3299735
theorem B3299741 : Blo 2199435 3299741 := bbase (se 3 (by rfl) ⟨618701, by rfl⟩ : syracuseStep 3299741 = 1237403) (by norm_num)
theorem B2199827 : Blo 2199435 2199827 := bstep (se 1 (by rfl) ⟨1649870, by rfl⟩ : syracuseStep 2199827 = 3299741) B3299741
theorem B4949621 : Blo 2199435 4949621 := bbase (se 5 (by rfl) ⟨232013, by rfl⟩ : syracuseStep 4949621 = 464027) (by norm_num)
theorem B3299747 : Blo 2199435 3299747 := bstep (se 1 (by rfl) ⟨2474810, by rfl⟩ : syracuseStep 3299747 = 4949621) B4949621
theorem B2199831 : Blo 2199435 2199831 := bstep (se 1 (by rfl) ⟨1649873, by rfl⟩ : syracuseStep 2199831 = 3299747) B3299747
theorem B2973133 : Blo 2199435 2973133 := bbase (se 3 (by rfl) ⟨557462, by rfl⟩ : syracuseStep 2973133 = 1114925) (by norm_num)
theorem B3964177 : Blo 2199435 3964177 := bstep (se 2 (by rfl) ⟨1486566, by rfl⟩ : syracuseStep 3964177 = 2973133) B2973133
theorem B5285569 : Blo 2199435 5285569 := bstep (se 2 (by rfl) ⟨1982088, by rfl⟩ : syracuseStep 5285569 = 3964177) B3964177
theorem B7047425 : Blo 2199435 7047425 := bstep (se 2 (by rfl) ⟨2642784, by rfl⟩ : syracuseStep 7047425 = 5285569) B5285569
theorem B18793133 : Blo 2199435 18793133 := bstep (se 3 (by rfl) ⟨3523712, by rfl⟩ : syracuseStep 18793133 = 7047425) B7047425
theorem B12528755 : Blo 2199435 12528755 := bstep (se 1 (by rfl) ⟨9396566, by rfl⟩ : syracuseStep 12528755 = 18793133) B18793133
theorem B8352503 : Blo 2199435 8352503 := bstep (se 1 (by rfl) ⟨6264377, by rfl⟩ : syracuseStep 8352503 = 12528755) B12528755
theorem B5568335 : Blo 2199435 5568335 := bstep (se 1 (by rfl) ⟨4176251, by rfl⟩ : syracuseStep 5568335 = 8352503) B8352503
theorem B3712223 : Blo 2199435 3712223 := bstep (se 1 (by rfl) ⟨2784167, by rfl⟩ : syracuseStep 3712223 = 5568335) B5568335
theorem B2474815 : Blo 2199435 2474815 := bstep (se 1 (by rfl) ⟨1856111, by rfl⟩ : syracuseStep 2474815 = 3712223) B3712223
theorem B3299753 : Blo 2199435 3299753 := bstep (se 2 (by rfl) ⟨1237407, by rfl⟩ : syracuseStep 3299753 = 2474815) B2474815
theorem B2199835 : Blo 2199435 2199835 := bstep (se 1 (by rfl) ⟨1649876, by rfl⟩ : syracuseStep 2199835 = 3299753) B3299753
theorem B8352517 : Blo 2199435 8352517 := bbase (se 4 (by rfl) ⟨783048, by rfl⟩ : syracuseStep 8352517 = 1566097) (by norm_num)
theorem B11136689 : Blo 2199435 11136689 := bstep (se 2 (by rfl) ⟨4176258, by rfl⟩ : syracuseStep 11136689 = 8352517) B8352517
theorem B7424459 : Blo 2199435 7424459 := bstep (se 1 (by rfl) ⟨5568344, by rfl⟩ : syracuseStep 7424459 = 11136689) B11136689
theorem B4949639 : Blo 2199435 4949639 := bstep (se 1 (by rfl) ⟨3712229, by rfl⟩ : syracuseStep 4949639 = 7424459) B7424459
theorem B3299759 : Blo 2199435 3299759 := bstep (se 1 (by rfl) ⟨2474819, by rfl⟩ : syracuseStep 3299759 = 4949639) B4949639
theorem B2199839 : Blo 2199435 2199839 := bstep (se 1 (by rfl) ⟨1649879, by rfl⟩ : syracuseStep 2199839 = 3299759) B3299759
theorem B3299765 : Blo 2199435 3299765 := bbase (se 5 (by rfl) ⟨154676, by rfl⟩ : syracuseStep 3299765 = 309353) (by norm_num)
theorem B2199843 : Blo 2199435 2199843 := bstep (se 1 (by rfl) ⟨1649882, by rfl⟩ : syracuseStep 2199843 = 3299765) B3299765
theorem B5568365 : Blo 2199435 5568365 := bbase (se 3 (by rfl) ⟨1044068, by rfl⟩ : syracuseStep 5568365 = 2088137) (by norm_num)
theorem B3712243 : Blo 2199435 3712243 := bstep (se 1 (by rfl) ⟨2784182, by rfl⟩ : syracuseStep 3712243 = 5568365) B5568365
theorem B4949657 : Blo 2199435 4949657 := bstep (se 2 (by rfl) ⟨1856121, by rfl⟩ : syracuseStep 4949657 = 3712243) B3712243
theorem B3299771 : Blo 2199435 3299771 := bstep (se 1 (by rfl) ⟨2474828, by rfl⟩ : syracuseStep 3299771 = 4949657) B4949657
theorem B2199847 : Blo 2199435 2199847 := bstep (se 1 (by rfl) ⟨1649885, by rfl⟩ : syracuseStep 2199847 = 3299771) B3299771
theorem B2474833 : Blo 2199435 2474833 := bbase (se 2 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 2474833 = 1856125) (by norm_num)
theorem B3299777 : Blo 2199435 3299777 := bstep (se 2 (by rfl) ⟨1237416, by rfl⟩ : syracuseStep 3299777 = 2474833) B2474833
theorem B2199851 : Blo 2199435 2199851 := bstep (se 1 (by rfl) ⟨1649888, by rfl⟩ : syracuseStep 2199851 = 3299777) B3299777
theorem B2642809 : Blo 2199435 2642809 := bbase (se 2 (by rfl) ⟨991053, by rfl⟩ : syracuseStep 2642809 = 1982107) (by norm_num)
theorem B3523745 : Blo 2199435 3523745 := bstep (se 2 (by rfl) ⟨1321404, by rfl⟩ : syracuseStep 3523745 = 2642809) B2642809
theorem B2349163 : Blo 2199435 2349163 := bstep (se 1 (by rfl) ⟨1761872, by rfl⟩ : syracuseStep 2349163 = 3523745) B3523745
theorem B3132217 : Blo 2199435 3132217 := bstep (se 2 (by rfl) ⟨1174581, by rfl⟩ : syracuseStep 3132217 = 2349163) B2349163
theorem B4176289 : Blo 2199435 4176289 := bstep (se 2 (by rfl) ⟨1566108, by rfl⟩ : syracuseStep 4176289 = 3132217) B3132217
theorem B5568385 : Blo 2199435 5568385 := bstep (se 2 (by rfl) ⟨2088144, by rfl⟩ : syracuseStep 5568385 = 4176289) B4176289
theorem B7424513 : Blo 2199435 7424513 := bstep (se 2 (by rfl) ⟨2784192, by rfl⟩ : syracuseStep 7424513 = 5568385) B5568385
theorem B4949675 : Blo 2199435 4949675 := bstep (se 1 (by rfl) ⟨3712256, by rfl⟩ : syracuseStep 4949675 = 7424513) B7424513
theorem B3299783 : Blo 2199435 3299783 := bstep (se 1 (by rfl) ⟨2474837, by rfl⟩ : syracuseStep 3299783 = 4949675) B4949675
theorem B2199855 : Blo 2199435 2199855 := bstep (se 1 (by rfl) ⟨1649891, by rfl⟩ : syracuseStep 2199855 = 3299783) B3299783
theorem B3299789 : Blo 2199435 3299789 := bbase (se 3 (by rfl) ⟨618710, by rfl⟩ : syracuseStep 3299789 = 1237421) (by norm_num)
theorem B2199859 : Blo 2199435 2199859 := bstep (se 1 (by rfl) ⟨1649894, by rfl⟩ : syracuseStep 2199859 = 3299789) B3299789
theorem B4949693 : Blo 2199435 4949693 := bbase (se 3 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 4949693 = 1856135) (by norm_num)
theorem B3299795 : Blo 2199435 3299795 := bstep (se 1 (by rfl) ⟨2474846, by rfl⟩ : syracuseStep 3299795 = 4949693) B4949693
theorem B2199863 : Blo 2199435 2199863 := bstep (se 1 (by rfl) ⟨1649897, by rfl⟩ : syracuseStep 2199863 = 3299795) B3299795
theorem B3712277 : Blo 2199435 3712277 := bbase (se 6 (by rfl) ⟨87006, by rfl⟩ : syracuseStep 3712277 = 174013) (by norm_num)
theorem B2474851 : Blo 2199435 2474851 := bstep (se 1 (by rfl) ⟨1856138, by rfl⟩ : syracuseStep 2474851 = 3712277) B3712277
theorem B3299801 : Blo 2199435 3299801 := bstep (se 2 (by rfl) ⟨1237425, by rfl⟩ : syracuseStep 3299801 = 2474851) B2474851
theorem B2199867 : Blo 2199435 2199867 := bstep (se 1 (by rfl) ⟨1649900, by rfl⟩ : syracuseStep 2199867 = 3299801) B3299801
theorem B19049845 : Blo 2199435 19049845 := bbase (se 5 (by rfl) ⟨892961, by rfl⟩ : syracuseStep 19049845 = 1785923) (by norm_num)
theorem B25399793 : Blo 2199435 25399793 := bstep (se 2 (by rfl) ⟨9524922, by rfl⟩ : syracuseStep 25399793 = 19049845) B19049845
theorem B16933195 : Blo 2199435 16933195 := bstep (se 1 (by rfl) ⟨12699896, by rfl⟩ : syracuseStep 16933195 = 25399793) B25399793
theorem B90310373 : Blo 2199435 90310373 := bstep (se 4 (by rfl) ⟨8466597, by rfl⟩ : syracuseStep 90310373 = 16933195) B16933195
theorem B60206915 : Blo 2199435 60206915 := bstep (se 1 (by rfl) ⟨45155186, by rfl⟩ : syracuseStep 60206915 = 90310373) B90310373
theorem B40137943 : Blo 2199435 40137943 := bstep (se 1 (by rfl) ⟨30103457, by rfl⟩ : syracuseStep 40137943 = 60206915) B60206915
theorem B53517257 : Blo 2199435 53517257 := bstep (se 2 (by rfl) ⟨20068971, by rfl⟩ : syracuseStep 53517257 = 40137943) B40137943
theorem B35678171 : Blo 2199435 35678171 := bstep (se 1 (by rfl) ⟨26758628, by rfl⟩ : syracuseStep 35678171 = 53517257) B53517257
theorem B23785447 : Blo 2199435 23785447 := bstep (se 1 (by rfl) ⟨17839085, by rfl⟩ : syracuseStep 23785447 = 35678171) B35678171
theorem B31713929 : Blo 2199435 31713929 := bstep (se 2 (by rfl) ⟨11892723, by rfl⟩ : syracuseStep 31713929 = 23785447) B23785447
theorem B21142619 : Blo 2199435 21142619 := bstep (se 1 (by rfl) ⟨15856964, by rfl⟩ : syracuseStep 21142619 = 31713929) B31713929
theorem B14095079 : Blo 2199435 14095079 := bstep (se 1 (by rfl) ⟨10571309, by rfl⟩ : syracuseStep 14095079 = 21142619) B21142619
theorem B9396719 : Blo 2199435 9396719 := bstep (se 1 (by rfl) ⟨7047539, by rfl⟩ : syracuseStep 9396719 = 14095079) B14095079
theorem B6264479 : Blo 2199435 6264479 := bstep (se 1 (by rfl) ⟨4698359, by rfl⟩ : syracuseStep 6264479 = 9396719) B9396719
theorem B16705277 : Blo 2199435 16705277 := bstep (se 3 (by rfl) ⟨3132239, by rfl⟩ : syracuseStep 16705277 = 6264479) B6264479
theorem B11136851 : Blo 2199435 11136851 := bstep (se 1 (by rfl) ⟨8352638, by rfl⟩ : syracuseStep 11136851 = 16705277) B16705277
theorem B7424567 : Blo 2199435 7424567 := bstep (se 1 (by rfl) ⟨5568425, by rfl⟩ : syracuseStep 7424567 = 11136851) B11136851
theorem B4949711 : Blo 2199435 4949711 := bstep (se 1 (by rfl) ⟨3712283, by rfl⟩ : syracuseStep 4949711 = 7424567) B7424567
theorem B3299807 : Blo 2199435 3299807 := bstep (se 1 (by rfl) ⟨2474855, by rfl⟩ : syracuseStep 3299807 = 4949711) B4949711
theorem B2199871 : Blo 2199435 2199871 := bstep (se 1 (by rfl) ⟨1649903, by rfl⟩ : syracuseStep 2199871 = 3299807) B3299807
theorem B3299813 : Blo 2199435 3299813 := bbase (se 4 (by rfl) ⟨309357, by rfl⟩ : syracuseStep 3299813 = 618715) (by norm_num)
theorem B2199875 : Blo 2199435 2199875 := bstep (se 1 (by rfl) ⟨1649906, by rfl⟩ : syracuseStep 2199875 = 3299813) B3299813
theorem B4459789 : Blo 2199435 4459789 := bbase (se 3 (by rfl) ⟨836210, by rfl⟩ : syracuseStep 4459789 = 1672421) (by norm_num)
theorem B5946385 : Blo 2199435 5946385 := bstep (se 2 (by rfl) ⟨2229894, by rfl⟩ : syracuseStep 5946385 = 4459789) B4459789
theorem B7928513 : Blo 2199435 7928513 := bstep (se 2 (by rfl) ⟨2973192, by rfl⟩ : syracuseStep 7928513 = 5946385) B5946385
theorem B5285675 : Blo 2199435 5285675 := bstep (se 1 (by rfl) ⟨3964256, by rfl⟩ : syracuseStep 5285675 = 7928513) B7928513
theorem B14095133 : Blo 2199435 14095133 := bstep (se 3 (by rfl) ⟨2642837, by rfl⟩ : syracuseStep 14095133 = 5285675) B5285675
theorem B9396755 : Blo 2199435 9396755 := bstep (se 1 (by rfl) ⟨7047566, by rfl⟩ : syracuseStep 9396755 = 14095133) B14095133
theorem B6264503 : Blo 2199435 6264503 := bstep (se 1 (by rfl) ⟨4698377, by rfl⟩ : syracuseStep 6264503 = 9396755) B9396755
theorem B4176335 : Blo 2199435 4176335 := bstep (se 1 (by rfl) ⟨3132251, by rfl⟩ : syracuseStep 4176335 = 6264503) B6264503
theorem B2784223 : Blo 2199435 2784223 := bstep (se 1 (by rfl) ⟨2088167, by rfl⟩ : syracuseStep 2784223 = 4176335) B4176335
theorem B3712297 : Blo 2199435 3712297 := bstep (se 2 (by rfl) ⟨1392111, by rfl⟩ : syracuseStep 3712297 = 2784223) B2784223
theorem B4949729 : Blo 2199435 4949729 := bstep (se 2 (by rfl) ⟨1856148, by rfl⟩ : syracuseStep 4949729 = 3712297) B3712297
theorem B3299819 : Blo 2199435 3299819 := bstep (se 1 (by rfl) ⟨2474864, by rfl⟩ : syracuseStep 3299819 = 4949729) B4949729
theorem B2199879 : Blo 2199435 2199879 := bstep (se 1 (by rfl) ⟨1649909, by rfl⟩ : syracuseStep 2199879 = 3299819) B3299819
theorem B2474869 : Blo 2199435 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B3299825 : Blo 2199435 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B2199883 : Blo 2199435 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B2784233 : Blo 2199435 2784233 := bbase (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) (by norm_num)
theorem B7424621 : Blo 2199435 7424621 := bstep (se 3 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 7424621 = 2784233) B2784233
theorem B4949747 : Blo 2199435 4949747 := bstep (se 1 (by rfl) ⟨3712310, by rfl⟩ : syracuseStep 4949747 = 7424621) B7424621
theorem B3299831 : Blo 2199435 3299831 := bstep (se 1 (by rfl) ⟨2474873, by rfl⟩ : syracuseStep 3299831 = 4949747) B4949747
theorem B2199887 : Blo 2199435 2199887 := bstep (se 1 (by rfl) ⟨1649915, by rfl⟩ : syracuseStep 2199887 = 3299831) B3299831
theorem B3299837 : Blo 2199435 3299837 := bbase (se 3 (by rfl) ⟨618719, by rfl⟩ : syracuseStep 3299837 = 1237439) (by norm_num)
theorem B2199891 : Blo 2199435 2199891 := bstep (se 1 (by rfl) ⟨1649918, by rfl⟩ : syracuseStep 2199891 = 3299837) B3299837
theorem B4949765 : Blo 2199435 4949765 := bbase (se 4 (by rfl) ⟨464040, by rfl⟩ : syracuseStep 4949765 = 928081) (by norm_num)
theorem B3299843 : Blo 2199435 3299843 := bstep (se 1 (by rfl) ⟨2474882, by rfl⟩ : syracuseStep 3299843 = 4949765) B4949765
theorem B2199895 : Blo 2199435 2199895 := bstep (se 1 (by rfl) ⟨1649921, by rfl⟩ : syracuseStep 2199895 = 3299843) B3299843
theorem B4176373 : Blo 2199435 4176373 := bbase (se 5 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 4176373 = 391535) (by norm_num)
theorem B5568497 : Blo 2199435 5568497 := bstep (se 2 (by rfl) ⟨2088186, by rfl⟩ : syracuseStep 5568497 = 4176373) B4176373
theorem B3712331 : Blo 2199435 3712331 := bstep (se 1 (by rfl) ⟨2784248, by rfl⟩ : syracuseStep 3712331 = 5568497) B5568497
theorem B2474887 : Blo 2199435 2474887 := bstep (se 1 (by rfl) ⟨1856165, by rfl⟩ : syracuseStep 2474887 = 3712331) B3712331
theorem B3299849 : Blo 2199435 3299849 := bstep (se 2 (by rfl) ⟨1237443, by rfl⟩ : syracuseStep 3299849 = 2474887) B2474887
theorem B2199899 : Blo 2199435 2199899 := bstep (se 1 (by rfl) ⟨1649924, by rfl⟩ : syracuseStep 2199899 = 3299849) B3299849
theorem B11137013 : Blo 2199435 11137013 := bbase (se 5 (by rfl) ⟨522047, by rfl⟩ : syracuseStep 11137013 = 1044095) (by norm_num)
theorem B7424675 : Blo 2199435 7424675 := bstep (se 1 (by rfl) ⟨5568506, by rfl⟩ : syracuseStep 7424675 = 11137013) B11137013
theorem B4949783 : Blo 2199435 4949783 := bstep (se 1 (by rfl) ⟨3712337, by rfl⟩ : syracuseStep 4949783 = 7424675) B7424675
theorem B3299855 : Blo 2199435 3299855 := bstep (se 1 (by rfl) ⟨2474891, by rfl⟩ : syracuseStep 3299855 = 4949783) B4949783
theorem B2199903 : Blo 2199435 2199903 := bstep (se 1 (by rfl) ⟨1649927, by rfl⟩ : syracuseStep 2199903 = 3299855) B3299855
theorem B3299861 : Blo 2199435 3299861 := bbase (se 6 (by rfl) ⟨77340, by rfl⟩ : syracuseStep 3299861 = 154681) (by norm_num)
theorem B2199907 : Blo 2199435 2199907 := bstep (se 1 (by rfl) ⟨1649930, by rfl⟩ : syracuseStep 2199907 = 3299861) B3299861
theorem B18793781 : Blo 2199435 18793781 := bbase (se 5 (by rfl) ⟨880958, by rfl⟩ : syracuseStep 18793781 = 1761917) (by norm_num)
theorem B12529187 : Blo 2199435 12529187 := bstep (se 1 (by rfl) ⟨9396890, by rfl⟩ : syracuseStep 12529187 = 18793781) B18793781
theorem B8352791 : Blo 2199435 8352791 := bstep (se 1 (by rfl) ⟨6264593, by rfl⟩ : syracuseStep 8352791 = 12529187) B12529187
theorem B5568527 : Blo 2199435 5568527 := bstep (se 1 (by rfl) ⟨4176395, by rfl⟩ : syracuseStep 5568527 = 8352791) B8352791
theorem B3712351 : Blo 2199435 3712351 := bstep (se 1 (by rfl) ⟨2784263, by rfl⟩ : syracuseStep 3712351 = 5568527) B5568527
theorem B4949801 : Blo 2199435 4949801 := bstep (se 2 (by rfl) ⟨1856175, by rfl⟩ : syracuseStep 4949801 = 3712351) B3712351
theorem B3299867 : Blo 2199435 3299867 := bstep (se 1 (by rfl) ⟨2474900, by rfl⟩ : syracuseStep 3299867 = 4949801) B4949801
theorem B2199911 : Blo 2199435 2199911 := bstep (se 1 (by rfl) ⟨1649933, by rfl⟩ : syracuseStep 2199911 = 3299867) B3299867
theorem B2474905 : Blo 2199435 2474905 := bbase (se 2 (by rfl) ⟨928089, by rfl⟩ : syracuseStep 2474905 = 1856179) (by norm_num)
theorem B3299873 : Blo 2199435 3299873 := bstep (se 2 (by rfl) ⟨1237452, by rfl⟩ : syracuseStep 3299873 = 2474905) B2474905
theorem B2199915 : Blo 2199435 2199915 := bstep (se 1 (by rfl) ⟨1649936, by rfl⟩ : syracuseStep 2199915 = 3299873) B3299873
theorem B8352821 : Blo 2199435 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B5568547 : Blo 2199435 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B7424729 : Blo 2199435 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B4949819 : Blo 2199435 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B3299879 : Blo 2199435 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B2199919 : Blo 2199435 2199919 := bstep (se 1 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 2199919 = 3299879) B3299879
theorem B3299885 : Blo 2199435 3299885 := bbase (se 3 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 3299885 = 1237457) (by norm_num)
theorem B2199923 : Blo 2199435 2199923 := bstep (se 1 (by rfl) ⟨1649942, by rfl⟩ : syracuseStep 2199923 = 3299885) B3299885
theorem B4949837 : Blo 2199435 4949837 := bbase (se 3 (by rfl) ⟨928094, by rfl⟩ : syracuseStep 4949837 = 1856189) (by norm_num)
theorem B3299891 : Blo 2199435 3299891 := bstep (se 1 (by rfl) ⟨2474918, by rfl⟩ : syracuseStep 3299891 = 4949837) B4949837
theorem B2199927 : Blo 2199435 2199927 := bstep (se 1 (by rfl) ⟨1649945, by rfl⟩ : syracuseStep 2199927 = 3299891) B3299891
theorem B2784289 : Blo 2199435 2784289 := bbase (se 2 (by rfl) ⟨1044108, by rfl⟩ : syracuseStep 2784289 = 2088217) (by norm_num)
theorem B3712385 : Blo 2199435 3712385 := bstep (se 2 (by rfl) ⟨1392144, by rfl⟩ : syracuseStep 3712385 = 2784289) B2784289
theorem B2474923 : Blo 2199435 2474923 := bstep (se 1 (by rfl) ⟨1856192, by rfl⟩ : syracuseStep 2474923 = 3712385) B3712385
theorem B3299897 : Blo 2199435 3299897 := bstep (se 2 (by rfl) ⟨1237461, by rfl⟩ : syracuseStep 3299897 = 2474923) B2474923
theorem B2199931 : Blo 2199435 2199931 := bstep (se 1 (by rfl) ⟨1649948, by rfl⟩ : syracuseStep 2199931 = 3299897) B3299897
theorem B25058645 : Blo 2199435 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B16705763 : Blo 2199435 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B11137175 : Blo 2199435 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B7424783 : Blo 2199435 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B4949855 : Blo 2199435 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B3299903 : Blo 2199435 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B2199935 : Blo 2199435 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B3299909 : Blo 2199435 3299909 := bbase (se 4 (by rfl) ⟨309366, by rfl⟩ : syracuseStep 3299909 = 618733) (by norm_num)
theorem B2199939 : Blo 2199435 2199939 := bstep (se 1 (by rfl) ⟨1649954, by rfl⟩ : syracuseStep 2199939 = 3299909) B3299909
theorem B3712405 : Blo 2199435 3712405 := bbase (se 6 (by rfl) ⟨87009, by rfl⟩ : syracuseStep 3712405 = 174019) (by norm_num)
theorem B4949873 : Blo 2199435 4949873 := bstep (se 2 (by rfl) ⟨1856202, by rfl⟩ : syracuseStep 4949873 = 3712405) B3712405
theorem B3299915 : Blo 2199435 3299915 := bstep (se 1 (by rfl) ⟨2474936, by rfl⟩ : syracuseStep 3299915 = 4949873) B4949873
theorem B2199943 : Blo 2199435 2199943 := bstep (se 1 (by rfl) ⟨1649957, by rfl⟩ : syracuseStep 2199943 = 3299915) B3299915
theorem B2474941 : Blo 2199435 2474941 := bbase (se 3 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 2474941 = 928103) (by norm_num)
theorem B3299921 : Blo 2199435 3299921 := bstep (se 2 (by rfl) ⟨1237470, by rfl⟩ : syracuseStep 3299921 = 2474941) B2474941
theorem B2199947 : Blo 2199435 2199947 := bstep (se 1 (by rfl) ⟨1649960, by rfl⟩ : syracuseStep 2199947 = 3299921) B3299921
theorem B7424837 : Blo 2199435 7424837 := bbase (se 4 (by rfl) ⟨696078, by rfl⟩ : syracuseStep 7424837 = 1392157) (by norm_num)
theorem B4949891 : Blo 2199435 4949891 := bstep (se 1 (by rfl) ⟨3712418, by rfl⟩ : syracuseStep 4949891 = 7424837) B7424837
theorem B3299927 : Blo 2199435 3299927 := bstep (se 1 (by rfl) ⟨2474945, by rfl⟩ : syracuseStep 3299927 = 4949891) B4949891
theorem B2199951 : Blo 2199435 2199951 := bstep (se 1 (by rfl) ⟨1649963, by rfl⟩ : syracuseStep 2199951 = 3299927) B3299927
theorem B3299933 : Blo 2199435 3299933 := bbase (se 3 (by rfl) ⟨618737, by rfl⟩ : syracuseStep 3299933 = 1237475) (by norm_num)
theorem B2199955 : Blo 2199435 2199955 := bstep (se 1 (by rfl) ⟨1649966, by rfl⟩ : syracuseStep 2199955 = 3299933) B3299933
theorem B4949909 : Blo 2199435 4949909 := bbase (se 6 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 4949909 = 232027) (by norm_num)
theorem B3299939 : Blo 2199435 3299939 := bstep (se 1 (by rfl) ⟨2474954, by rfl⟩ : syracuseStep 3299939 = 4949909) B4949909
theorem B2199959 : Blo 2199435 2199959 := bstep (se 1 (by rfl) ⟨1649969, by rfl⟩ : syracuseStep 2199959 = 3299939) B3299939
theorem B4698557 : Blo 2199435 4698557 := bbase (se 3 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 4698557 = 1761959) (by norm_num)
theorem B3132371 : Blo 2199435 3132371 := bstep (se 1 (by rfl) ⟨2349278, by rfl⟩ : syracuseStep 3132371 = 4698557) B4698557
theorem B8352989 : Blo 2199435 8352989 := bstep (se 3 (by rfl) ⟨1566185, by rfl⟩ : syracuseStep 8352989 = 3132371) B3132371
theorem B5568659 : Blo 2199435 5568659 := bstep (se 1 (by rfl) ⟨4176494, by rfl⟩ : syracuseStep 5568659 = 8352989) B8352989
theorem B3712439 : Blo 2199435 3712439 := bstep (se 1 (by rfl) ⟨2784329, by rfl⟩ : syracuseStep 3712439 = 5568659) B5568659
theorem B2474959 : Blo 2199435 2474959 := bstep (se 1 (by rfl) ⟨1856219, by rfl⟩ : syracuseStep 2474959 = 3712439) B3712439
theorem B3299945 : Blo 2199435 3299945 := bstep (se 2 (by rfl) ⟨1237479, by rfl⟩ : syracuseStep 3299945 = 2474959) B2474959
theorem B2199963 : Blo 2199435 2199963 := bstep (se 1 (by rfl) ⟨1649972, by rfl⟩ : syracuseStep 2199963 = 3299945) B3299945
theorem B22578581 : Blo 2199435 22578581 := bbase (se 6 (by rfl) ⟨529185, by rfl⟩ : syracuseStep 22578581 = 1058371) (by norm_num)
theorem B15052387 : Blo 2199435 15052387 := bstep (se 1 (by rfl) ⟨11289290, by rfl⟩ : syracuseStep 15052387 = 22578581) B22578581
theorem B20069849 : Blo 2199435 20069849 := bstep (se 2 (by rfl) ⟨7526193, by rfl⟩ : syracuseStep 20069849 = 15052387) B15052387
theorem B13379899 : Blo 2199435 13379899 := bstep (se 1 (by rfl) ⟨10034924, by rfl⟩ : syracuseStep 13379899 = 20069849) B20069849
theorem B17839865 : Blo 2199435 17839865 := bstep (se 2 (by rfl) ⟨6689949, by rfl⟩ : syracuseStep 17839865 = 13379899) B13379899
theorem B11893243 : Blo 2199435 11893243 := bstep (se 1 (by rfl) ⟨8919932, by rfl⟩ : syracuseStep 11893243 = 17839865) B17839865
theorem B15857657 : Blo 2199435 15857657 := bstep (se 2 (by rfl) ⟨5946621, by rfl⟩ : syracuseStep 15857657 = 11893243) B11893243
theorem B10571771 : Blo 2199435 10571771 := bstep (se 1 (by rfl) ⟨7928828, by rfl⟩ : syracuseStep 10571771 = 15857657) B15857657
theorem B7047847 : Blo 2199435 7047847 := bstep (se 1 (by rfl) ⟨5285885, by rfl⟩ : syracuseStep 7047847 = 10571771) B10571771
theorem B9397129 : Blo 2199435 9397129 := bstep (se 2 (by rfl) ⟨3523923, by rfl⟩ : syracuseStep 9397129 = 7047847) B7047847
theorem B12529505 : Blo 2199435 12529505 := bstep (se 2 (by rfl) ⟨4698564, by rfl⟩ : syracuseStep 12529505 = 9397129) B9397129
theorem B8353003 : Blo 2199435 8353003 := bstep (se 1 (by rfl) ⟨6264752, by rfl⟩ : syracuseStep 8353003 = 12529505) B12529505
theorem B11137337 : Blo 2199435 11137337 := bstep (se 2 (by rfl) ⟨4176501, by rfl⟩ : syracuseStep 11137337 = 8353003) B8353003
theorem B7424891 : Blo 2199435 7424891 := bstep (se 1 (by rfl) ⟨5568668, by rfl⟩ : syracuseStep 7424891 = 11137337) B11137337
theorem B4949927 : Blo 2199435 4949927 := bstep (se 1 (by rfl) ⟨3712445, by rfl⟩ : syracuseStep 4949927 = 7424891) B7424891
theorem B3299951 : Blo 2199435 3299951 := bstep (se 1 (by rfl) ⟨2474963, by rfl⟩ : syracuseStep 3299951 = 4949927) B4949927
theorem B2199967 : Blo 2199435 2199967 := bstep (se 1 (by rfl) ⟨1649975, by rfl⟩ : syracuseStep 2199967 = 3299951) B3299951
theorem B3299957 : Blo 2199435 3299957 := bbase (se 5 (by rfl) ⟨154685, by rfl⟩ : syracuseStep 3299957 = 309371) (by norm_num)
theorem B2199971 : Blo 2199435 2199971 := bstep (se 1 (by rfl) ⟨1649978, by rfl⟩ : syracuseStep 2199971 = 3299957) B3299957
theorem B4176517 : Blo 2199435 4176517 := bbase (se 4 (by rfl) ⟨391548, by rfl⟩ : syracuseStep 4176517 = 783097) (by norm_num)
theorem B5568689 : Blo 2199435 5568689 := bstep (se 2 (by rfl) ⟨2088258, by rfl⟩ : syracuseStep 5568689 = 4176517) B4176517
theorem B3712459 : Blo 2199435 3712459 := bstep (se 1 (by rfl) ⟨2784344, by rfl⟩ : syracuseStep 3712459 = 5568689) B5568689
theorem B4949945 : Blo 2199435 4949945 := bstep (se 2 (by rfl) ⟨1856229, by rfl⟩ : syracuseStep 4949945 = 3712459) B3712459
theorem B3299963 : Blo 2199435 3299963 := bstep (se 1 (by rfl) ⟨2474972, by rfl⟩ : syracuseStep 3299963 = 4949945) B4949945
theorem B2199975 : Blo 2199435 2199975 := bstep (se 1 (by rfl) ⟨1649981, by rfl⟩ : syracuseStep 2199975 = 3299963) B3299963
theorem B2474977 : Blo 2199435 2474977 := bbase (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) (by norm_num)
theorem B3299969 : Blo 2199435 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B2199979 : Blo 2199435 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B5568709 : Blo 2199435 5568709 := bbase (se 4 (by rfl) ⟨522066, by rfl⟩ : syracuseStep 5568709 = 1044133) (by norm_num)
theorem B7424945 : Blo 2199435 7424945 := bstep (se 2 (by rfl) ⟨2784354, by rfl⟩ : syracuseStep 7424945 = 5568709) B5568709
theorem B4949963 : Blo 2199435 4949963 := bstep (se 1 (by rfl) ⟨3712472, by rfl⟩ : syracuseStep 4949963 = 7424945) B7424945
theorem B3299975 : Blo 2199435 3299975 := bstep (se 1 (by rfl) ⟨2474981, by rfl⟩ : syracuseStep 3299975 = 4949963) B4949963
theorem B2199983 : Blo 2199435 2199983 := bstep (se 1 (by rfl) ⟨1649987, by rfl⟩ : syracuseStep 2199983 = 3299975) B3299975
theorem B3299981 : Blo 2199435 3299981 := bbase (se 3 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 3299981 = 1237493) (by norm_num)
theorem B2199987 : Blo 2199435 2199987 := bstep (se 1 (by rfl) ⟨1649990, by rfl⟩ : syracuseStep 2199987 = 3299981) B3299981
theorem B4949981 : Blo 2199435 4949981 := bbase (se 3 (by rfl) ⟨928121, by rfl⟩ : syracuseStep 4949981 = 1856243) (by norm_num)
theorem B3299987 : Blo 2199435 3299987 := bstep (se 1 (by rfl) ⟨2474990, by rfl⟩ : syracuseStep 3299987 = 4949981) B4949981
theorem B2199991 : Blo 2199435 2199991 := bstep (se 1 (by rfl) ⟨1649993, by rfl⟩ : syracuseStep 2199991 = 3299987) B3299987
theorem B3712493 : Blo 2199435 3712493 := bbase (se 3 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 3712493 = 1392185) (by norm_num)
theorem B2474995 : Blo 2199435 2474995 := bstep (se 1 (by rfl) ⟨1856246, by rfl⟩ : syracuseStep 2474995 = 3712493) B3712493
theorem B3299993 : Blo 2199435 3299993 := bstep (se 2 (by rfl) ⟨1237497, by rfl⟩ : syracuseStep 3299993 = 2474995) B2474995
theorem B2199995 : Blo 2199435 2199995 := bstep (se 1 (by rfl) ⟨1649996, by rfl⟩ : syracuseStep 2199995 = 3299993) B3299993
theorem B2642981 : Blo 2199435 2642981 := bbase (se 4 (by rfl) ⟨247779, by rfl⟩ : syracuseStep 2642981 = 495559) (by norm_num)
theorem B28191797 : Blo 2199435 28191797 := bstep (se 5 (by rfl) ⟨1321490, by rfl⟩ : syracuseStep 28191797 = 2642981) B2642981
theorem B18794531 : Blo 2199435 18794531 := bstep (se 1 (by rfl) ⟨14095898, by rfl⟩ : syracuseStep 18794531 = 28191797) B28191797
theorem B12529687 : Blo 2199435 12529687 := bstep (se 1 (by rfl) ⟨9397265, by rfl⟩ : syracuseStep 12529687 = 18794531) B18794531
theorem B16706249 : Blo 2199435 16706249 := bstep (se 2 (by rfl) ⟨6264843, by rfl⟩ : syracuseStep 16706249 = 12529687) B12529687
theorem B11137499 : Blo 2199435 11137499 := bstep (se 1 (by rfl) ⟨8353124, by rfl⟩ : syracuseStep 11137499 = 16706249) B16706249
theorem B7424999 : Blo 2199435 7424999 := bstep (se 1 (by rfl) ⟨5568749, by rfl⟩ : syracuseStep 7424999 = 11137499) B11137499
theorem B4949999 : Blo 2199435 4949999 := bstep (se 1 (by rfl) ⟨3712499, by rfl⟩ : syracuseStep 4949999 = 7424999) B7424999
theorem B3299999 : Blo 2199435 3299999 := bstep (se 1 (by rfl) ⟨2474999, by rfl⟩ : syracuseStep 3299999 = 4949999) B4949999
theorem B2199999 : Blo 2199435 2199999 := bstep (se 1 (by rfl) ⟨1649999, by rfl⟩ : syracuseStep 2199999 = 3299999) B3299999
theorem B3300005 : Blo 2199435 3300005 := bbase (se 4 (by rfl) ⟨309375, by rfl⟩ : syracuseStep 3300005 = 618751) (by norm_num)
theorem B2200003 : Blo 2199435 2200003 := bstep (se 1 (by rfl) ⟨1650002, by rfl⟩ : syracuseStep 2200003 = 3300005) B3300005
theorem B2784385 : Blo 2199435 2784385 := bbase (se 2 (by rfl) ⟨1044144, by rfl⟩ : syracuseStep 2784385 = 2088289) (by norm_num)
theorem B3712513 : Blo 2199435 3712513 := bstep (se 2 (by rfl) ⟨1392192, by rfl⟩ : syracuseStep 3712513 = 2784385) B2784385
theorem B4950017 : Blo 2199435 4950017 := bstep (se 2 (by rfl) ⟨1856256, by rfl⟩ : syracuseStep 4950017 = 3712513) B3712513
theorem B3300011 : Blo 2199435 3300011 := bstep (se 1 (by rfl) ⟨2475008, by rfl⟩ : syracuseStep 3300011 = 4950017) B4950017
theorem B2200007 : Blo 2199435 2200007 := bstep (se 1 (by rfl) ⟨1650005, by rfl⟩ : syracuseStep 2200007 = 3300011) B3300011
theorem B2475013 : Blo 2199435 2475013 := bbase (se 4 (by rfl) ⟨232032, by rfl⟩ : syracuseStep 2475013 = 464065) (by norm_num)
theorem B3300017 : Blo 2199435 3300017 := bstep (se 2 (by rfl) ⟨1237506, by rfl⟩ : syracuseStep 3300017 = 2475013) B2475013
theorem B2200011 : Blo 2199435 2200011 := bstep (se 1 (by rfl) ⟨1650008, by rfl⟩ : syracuseStep 2200011 = 3300017) B3300017
theorem B3132445 : Blo 2199435 3132445 := bbase (se 3 (by rfl) ⟨587333, by rfl⟩ : syracuseStep 3132445 = 1174667) (by norm_num)
theorem B4176593 : Blo 2199435 4176593 := bstep (se 2 (by rfl) ⟨1566222, by rfl⟩ : syracuseStep 4176593 = 3132445) B3132445
theorem B2784395 : Blo 2199435 2784395 := bstep (se 1 (by rfl) ⟨2088296, by rfl⟩ : syracuseStep 2784395 = 4176593) B4176593
theorem B7425053 : Blo 2199435 7425053 := bstep (se 3 (by rfl) ⟨1392197, by rfl⟩ : syracuseStep 7425053 = 2784395) B2784395
theorem B4950035 : Blo 2199435 4950035 := bstep (se 1 (by rfl) ⟨3712526, by rfl⟩ : syracuseStep 4950035 = 7425053) B7425053
theorem B3300023 : Blo 2199435 3300023 := bstep (se 1 (by rfl) ⟨2475017, by rfl⟩ : syracuseStep 3300023 = 4950035) B4950035
theorem B2200015 : Blo 2199435 2200015 := bstep (se 1 (by rfl) ⟨1650011, by rfl⟩ : syracuseStep 2200015 = 3300023) B3300023
theorem B3300029 : Blo 2199435 3300029 := bbase (se 3 (by rfl) ⟨618755, by rfl⟩ : syracuseStep 3300029 = 1237511) (by norm_num)
theorem B2200019 : Blo 2199435 2200019 := bstep (se 1 (by rfl) ⟨1650014, by rfl⟩ : syracuseStep 2200019 = 3300029) B3300029
theorem B4950053 : Blo 2199435 4950053 := bbase (se 4 (by rfl) ⟨464067, by rfl⟩ : syracuseStep 4950053 = 928135) (by norm_num)
theorem B3300035 : Blo 2199435 3300035 := bstep (se 1 (by rfl) ⟨2475026, by rfl⟩ : syracuseStep 3300035 = 4950053) B4950053
theorem B2200023 : Blo 2199435 2200023 := bstep (se 1 (by rfl) ⟨1650017, by rfl⟩ : syracuseStep 2200023 = 3300035) B3300035
theorem B5568821 : Blo 2199435 5568821 := bbase (se 5 (by rfl) ⟨261038, by rfl⟩ : syracuseStep 5568821 = 522077) (by norm_num)
theorem B3712547 : Blo 2199435 3712547 := bstep (se 1 (by rfl) ⟨2784410, by rfl⟩ : syracuseStep 3712547 = 5568821) B5568821
theorem B2475031 : Blo 2199435 2475031 := bstep (se 1 (by rfl) ⟨1856273, by rfl⟩ : syracuseStep 2475031 = 3712547) B3712547
theorem B3300041 : Blo 2199435 3300041 := bstep (se 2 (by rfl) ⟨1237515, by rfl⟩ : syracuseStep 3300041 = 2475031) B2475031
theorem B2200027 : Blo 2199435 2200027 := bstep (se 1 (by rfl) ⟨1650020, by rfl⟩ : syracuseStep 2200027 = 3300041) B3300041
theorem B7144213 : Blo 2199435 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B9525617 : Blo 2199435 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B6350411 : Blo 2199435 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B16934429 : Blo 2199435 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B11289619 : Blo 2199435 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B15052825 : Blo 2199435 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B20070433 : Blo 2199435 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B26760577 : Blo 2199435 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B35680769 : Blo 2199435 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B23787179 : Blo 2199435 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B15858119 : Blo 2199435 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B10572079 : Blo 2199435 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B14096105 : Blo 2199435 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B9397403 : Blo 2199435 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B6264935 : Blo 2199435 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B4176623 : Blo 2199435 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B11137661 : Blo 2199435 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B7425107 : Blo 2199435 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B4950071 : Blo 2199435 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B3300047 : Blo 2199435 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B2200031 : Blo 2199435 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B3300053 : Blo 2199435 3300053 := bbase (se 7 (by rfl) ⟨38672, by rfl⟩ : syracuseStep 3300053 = 77345) (by norm_num)
theorem B2200035 : Blo 2199435 2200035 := bstep (se 1 (by rfl) ⟨1650026, by rfl⟩ : syracuseStep 2200035 = 3300053) B3300053
theorem B3345085 : Blo 2199435 3345085 := bbase (se 3 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 3345085 = 1254407) (by norm_num)
theorem B4460113 : Blo 2199435 4460113 := bstep (se 2 (by rfl) ⟨1672542, by rfl⟩ : syracuseStep 4460113 = 3345085) B3345085
theorem B23787269 : Blo 2199435 23787269 := bstep (se 4 (by rfl) ⟨2230056, by rfl⟩ : syracuseStep 23787269 = 4460113) B4460113
theorem B15858179 : Blo 2199435 15858179 := bstep (se 1 (by rfl) ⟨11893634, by rfl⟩ : syracuseStep 15858179 = 23787269) B23787269
theorem B10572119 : Blo 2199435 10572119 := bstep (se 1 (by rfl) ⟨7929089, by rfl⟩ : syracuseStep 10572119 = 15858179) B15858179
theorem B7048079 : Blo 2199435 7048079 := bstep (se 1 (by rfl) ⟨5286059, by rfl⟩ : syracuseStep 7048079 = 10572119) B10572119
theorem B4698719 : Blo 2199435 4698719 := bstep (se 1 (by rfl) ⟨3524039, by rfl⟩ : syracuseStep 4698719 = 7048079) B7048079
theorem B3132479 : Blo 2199435 3132479 := bstep (se 1 (by rfl) ⟨2349359, by rfl⟩ : syracuseStep 3132479 = 4698719) B4698719
theorem B8353277 : Blo 2199435 8353277 := bstep (se 3 (by rfl) ⟨1566239, by rfl⟩ : syracuseStep 8353277 = 3132479) B3132479
theorem B5568851 : Blo 2199435 5568851 := bstep (se 1 (by rfl) ⟨4176638, by rfl⟩ : syracuseStep 5568851 = 8353277) B8353277
theorem B3712567 : Blo 2199435 3712567 := bstep (se 1 (by rfl) ⟨2784425, by rfl⟩ : syracuseStep 3712567 = 5568851) B5568851
theorem B4950089 : Blo 2199435 4950089 := bstep (se 2 (by rfl) ⟨1856283, by rfl⟩ : syracuseStep 4950089 = 3712567) B3712567
theorem B3300059 : Blo 2199435 3300059 := bstep (se 1 (by rfl) ⟨2475044, by rfl⟩ : syracuseStep 3300059 = 4950089) B4950089
theorem B2200039 : Blo 2199435 2200039 := bstep (se 1 (by rfl) ⟨1650029, by rfl⟩ : syracuseStep 2200039 = 3300059) B3300059
theorem B2475049 : Blo 2199435 2475049 := bbase (se 2 (by rfl) ⟨928143, by rfl⟩ : syracuseStep 2475049 = 1856287) (by norm_num)
theorem B3300065 : Blo 2199435 3300065 := bstep (se 2 (by rfl) ⟨1237524, by rfl⟩ : syracuseStep 3300065 = 2475049) B2475049
theorem B2200043 : Blo 2199435 2200043 := bstep (se 1 (by rfl) ⟨1650032, by rfl⟩ : syracuseStep 2200043 = 3300065) B3300065
theorem B11289701 : Blo 2199435 11289701 := bbase (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) (by norm_num)
theorem B7526467 : Blo 2199435 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B10035289 : Blo 2199435 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B13380385 : Blo 2199435 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B17840513 : Blo 2199435 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B47574701 : Blo 2199435 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B31716467 : Blo 2199435 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B21144311 : Blo 2199435 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B14096207 : Blo 2199435 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B9397471 : Blo 2199435 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B12529961 : Blo 2199435 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B8353307 : Blo 2199435 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B5568871 : Blo 2199435 5568871 := bstep (se 1 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 5568871 = 8353307) B8353307
theorem B7425161 : Blo 2199435 7425161 := bstep (se 2 (by rfl) ⟨2784435, by rfl⟩ : syracuseStep 7425161 = 5568871) B5568871
theorem B4950107 : Blo 2199435 4950107 := bstep (se 1 (by rfl) ⟨3712580, by rfl⟩ : syracuseStep 4950107 = 7425161) B7425161
theorem B3300071 : Blo 2199435 3300071 := bstep (se 1 (by rfl) ⟨2475053, by rfl⟩ : syracuseStep 3300071 = 4950107) B4950107
theorem B2200047 : Blo 2199435 2200047 := bstep (se 1 (by rfl) ⟨1650035, by rfl⟩ : syracuseStep 2200047 = 3300071) B3300071
theorem B3300077 : Blo 2199435 3300077 := bbase (se 3 (by rfl) ⟨618764, by rfl⟩ : syracuseStep 3300077 = 1237529) (by norm_num)
theorem B2200051 : Blo 2199435 2200051 := bstep (se 1 (by rfl) ⟨1650038, by rfl⟩ : syracuseStep 2200051 = 3300077) B3300077
theorem B4950125 : Blo 2199435 4950125 := bbase (se 3 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 4950125 = 1856297) (by norm_num)
theorem B3300083 : Blo 2199435 3300083 := bstep (se 1 (by rfl) ⟨2475062, by rfl⟩ : syracuseStep 3300083 = 4950125) B4950125
theorem B2200055 : Blo 2199435 2200055 := bstep (se 1 (by rfl) ⟨1650041, by rfl⟩ : syracuseStep 2200055 = 3300083) B3300083
theorem B4176677 : Blo 2199435 4176677 := bbase (se 4 (by rfl) ⟨391563, by rfl⟩ : syracuseStep 4176677 = 783127) (by norm_num)
theorem B2784451 : Blo 2199435 2784451 := bstep (se 1 (by rfl) ⟨2088338, by rfl⟩ : syracuseStep 2784451 = 4176677) B4176677
theorem B3712601 : Blo 2199435 3712601 := bstep (se 2 (by rfl) ⟨1392225, by rfl⟩ : syracuseStep 3712601 = 2784451) B2784451
theorem B2475067 : Blo 2199435 2475067 := bstep (se 1 (by rfl) ⟨1856300, by rfl⟩ : syracuseStep 2475067 = 3712601) B3712601
theorem B3300089 : Blo 2199435 3300089 := bstep (se 2 (by rfl) ⟨1237533, by rfl⟩ : syracuseStep 3300089 = 2475067) B2475067
theorem B2200059 : Blo 2199435 2200059 := bstep (se 1 (by rfl) ⟨1650044, by rfl⟩ : syracuseStep 2200059 = 3300089) B3300089
theorem B18084053 : Blo 2199435 18084053 := bbase (se 7 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 18084053 = 423845) (by norm_num)
theorem B12056035 : Blo 2199435 12056035 := bstep (se 1 (by rfl) ⟨9042026, by rfl⟩ : syracuseStep 12056035 = 18084053) B18084053
theorem B16074713 : Blo 2199435 16074713 := bstep (se 2 (by rfl) ⟨6028017, by rfl⟩ : syracuseStep 16074713 = 12056035) B12056035
theorem B10716475 : Blo 2199435 10716475 := bstep (se 1 (by rfl) ⟨8037356, by rfl⟩ : syracuseStep 10716475 = 16074713) B16074713
theorem B14288633 : Blo 2199435 14288633 := bstep (se 2 (by rfl) ⟨5358237, by rfl⟩ : syracuseStep 14288633 = 10716475) B10716475
theorem B9525755 : Blo 2199435 9525755 := bstep (se 1 (by rfl) ⟨7144316, by rfl⟩ : syracuseStep 9525755 = 14288633) B14288633
theorem B6350503 : Blo 2199435 6350503 := bstep (se 1 (by rfl) ⟨4762877, by rfl⟩ : syracuseStep 6350503 = 9525755) B9525755
theorem B8467337 : Blo 2199435 8467337 := bstep (se 2 (by rfl) ⟨3175251, by rfl⟩ : syracuseStep 8467337 = 6350503) B6350503
theorem B5644891 : Blo 2199435 5644891 := bstep (se 1 (by rfl) ⟨4233668, by rfl⟩ : syracuseStep 5644891 = 8467337) B8467337
theorem B7526521 : Blo 2199435 7526521 := bstep (se 2 (by rfl) ⟨2822445, by rfl⟩ : syracuseStep 7526521 = 5644891) B5644891
theorem B10035361 : Blo 2199435 10035361 := bstep (se 2 (by rfl) ⟨3763260, by rfl⟩ : syracuseStep 10035361 = 7526521) B7526521
theorem B13380481 : Blo 2199435 13380481 := bstep (se 2 (by rfl) ⟨5017680, by rfl⟩ : syracuseStep 13380481 = 10035361) B10035361
theorem B17840641 : Blo 2199435 17840641 := bstep (se 2 (by rfl) ⟨6690240, by rfl⟩ : syracuseStep 17840641 = 13380481) B13380481
theorem B23787521 : Blo 2199435 23787521 := bstep (se 2 (by rfl) ⟨8920320, by rfl⟩ : syracuseStep 23787521 = 17840641) B17840641
theorem B15858347 : Blo 2199435 15858347 := bstep (se 1 (by rfl) ⟨11893760, by rfl⟩ : syracuseStep 15858347 = 23787521) B23787521
theorem B42288925 : Blo 2199435 42288925 := bstep (se 3 (by rfl) ⟨7929173, by rfl⟩ : syracuseStep 42288925 = 15858347) B15858347
theorem B56385233 : Blo 2199435 56385233 := bstep (se 2 (by rfl) ⟨21144462, by rfl⟩ : syracuseStep 56385233 = 42288925) B42288925
theorem B37590155 : Blo 2199435 37590155 := bstep (se 1 (by rfl) ⟨28192616, by rfl⟩ : syracuseStep 37590155 = 56385233) B56385233
theorem B25060103 : Blo 2199435 25060103 := bstep (se 1 (by rfl) ⟨18795077, by rfl⟩ : syracuseStep 25060103 = 37590155) B37590155
theorem B16706735 : Blo 2199435 16706735 := bstep (se 1 (by rfl) ⟨12530051, by rfl⟩ : syracuseStep 16706735 = 25060103) B25060103
theorem B11137823 : Blo 2199435 11137823 := bstep (se 1 (by rfl) ⟨8353367, by rfl⟩ : syracuseStep 11137823 = 16706735) B16706735
theorem B7425215 : Blo 2199435 7425215 := bstep (se 1 (by rfl) ⟨5568911, by rfl⟩ : syracuseStep 7425215 = 11137823) B11137823
theorem B4950143 : Blo 2199435 4950143 := bstep (se 1 (by rfl) ⟨3712607, by rfl⟩ : syracuseStep 4950143 = 7425215) B7425215
theorem B3300095 : Blo 2199435 3300095 := bstep (se 1 (by rfl) ⟨2475071, by rfl⟩ : syracuseStep 3300095 = 4950143) B4950143
theorem B2200063 : Blo 2199435 2200063 := bstep (se 1 (by rfl) ⟨1650047, by rfl⟩ : syracuseStep 2200063 = 3300095) B3300095
theorem B3300101 : Blo 2199435 3300101 := bbase (se 4 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 3300101 = 618769) (by norm_num)
theorem B2200067 : Blo 2199435 2200067 := bstep (se 1 (by rfl) ⟨1650050, by rfl⟩ : syracuseStep 2200067 = 3300101) B3300101
theorem B3712621 : Blo 2199435 3712621 := bbase (se 3 (by rfl) ⟨696116, by rfl⟩ : syracuseStep 3712621 = 1392233) (by norm_num)
theorem B4950161 : Blo 2199435 4950161 := bstep (se 2 (by rfl) ⟨1856310, by rfl⟩ : syracuseStep 4950161 = 3712621) B3712621
theorem B3300107 : Blo 2199435 3300107 := bstep (se 1 (by rfl) ⟨2475080, by rfl⟩ : syracuseStep 3300107 = 4950161) B4950161
theorem B2200071 : Blo 2199435 2200071 := bstep (se 1 (by rfl) ⟨1650053, by rfl⟩ : syracuseStep 2200071 = 3300107) B3300107
theorem B2475085 : Blo 2199435 2475085 := bbase (se 3 (by rfl) ⟨464078, by rfl⟩ : syracuseStep 2475085 = 928157) (by norm_num)
theorem B3300113 : Blo 2199435 3300113 := bstep (se 2 (by rfl) ⟨1237542, by rfl⟩ : syracuseStep 3300113 = 2475085) B2475085
theorem B2200075 : Blo 2199435 2200075 := bstep (se 1 (by rfl) ⟨1650056, by rfl⟩ : syracuseStep 2200075 = 3300113) B3300113
theorem B7425269 : Blo 2199435 7425269 := bbase (se 5 (by rfl) ⟨348059, by rfl⟩ : syracuseStep 7425269 = 696119) (by norm_num)
theorem B4950179 : Blo 2199435 4950179 := bstep (se 1 (by rfl) ⟨3712634, by rfl⟩ : syracuseStep 4950179 = 7425269) B7425269
theorem B3300119 : Blo 2199435 3300119 := bstep (se 1 (by rfl) ⟨2475089, by rfl⟩ : syracuseStep 3300119 = 4950179) B4950179
theorem B2200079 : Blo 2199435 2200079 := bstep (se 1 (by rfl) ⟨1650059, by rfl⟩ : syracuseStep 2200079 = 3300119) B3300119
theorem B3300125 : Blo 2199435 3300125 := bbase (se 3 (by rfl) ⟨618773, by rfl⟩ : syracuseStep 3300125 = 1237547) (by norm_num)
theorem B2200083 : Blo 2199435 2200083 := bstep (se 1 (by rfl) ⟨1650062, by rfl⟩ : syracuseStep 2200083 = 3300125) B3300125
theorem B4950197 : Blo 2199435 4950197 := bbase (se 5 (by rfl) ⟨232040, by rfl⟩ : syracuseStep 4950197 = 464081) (by norm_num)
theorem B3300131 : Blo 2199435 3300131 := bstep (se 1 (by rfl) ⟨2475098, by rfl⟩ : syracuseStep 3300131 = 4950197) B4950197
theorem B2200087 : Blo 2199435 2200087 := bstep (se 1 (by rfl) ⟨1650065, by rfl⟩ : syracuseStep 2200087 = 3300131) B3300131
theorem B4233725 : Blo 2199435 4233725 := bbase (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) (by norm_num)
theorem B2822483 : Blo 2199435 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B7526621 : Blo 2199435 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B20070989 : Blo 2199435 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B13380659 : Blo 2199435 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B8920439 : Blo 2199435 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B5946959 : Blo 2199435 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B3964639 : Blo 2199435 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B5286185 : Blo 2199435 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B3524123 : Blo 2199435 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B2349415 : Blo 2199435 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B12530213 : Blo 2199435 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B8353475 : Blo 2199435 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B5568983 : Blo 2199435 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B3712655 : Blo 2199435 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B2475103 : Blo 2199435 2475103 := bstep (se 1 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 2475103 = 3712655) B3712655
theorem B3300137 : Blo 2199435 3300137 := bstep (se 2 (by rfl) ⟨1237551, by rfl⟩ : syracuseStep 3300137 = 2475103) B2475103
theorem B2200091 : Blo 2199435 2200091 := bstep (se 1 (by rfl) ⟨1650068, by rfl⟩ : syracuseStep 2200091 = 3300137) B3300137
theorem B2643097 : Blo 2199435 2643097 := bbase (se 2 (by rfl) ⟨991161, by rfl⟩ : syracuseStep 2643097 = 1982323) (by norm_num)
theorem B3524129 : Blo 2199435 3524129 := bstep (se 2 (by rfl) ⟨1321548, by rfl⟩ : syracuseStep 3524129 = 2643097) B2643097
theorem B2349419 : Blo 2199435 2349419 := bstep (se 1 (by rfl) ⟨1762064, by rfl⟩ : syracuseStep 2349419 = 3524129) B3524129
theorem B6265117 : Blo 2199435 6265117 := bstep (se 3 (by rfl) ⟨1174709, by rfl⟩ : syracuseStep 6265117 = 2349419) B2349419
theorem B8353489 : Blo 2199435 8353489 := bstep (se 2 (by rfl) ⟨3132558, by rfl⟩ : syracuseStep 8353489 = 6265117) B6265117
theorem B11137985 : Blo 2199435 11137985 := bstep (se 2 (by rfl) ⟨4176744, by rfl⟩ : syracuseStep 11137985 = 8353489) B8353489
theorem B7425323 : Blo 2199435 7425323 := bstep (se 1 (by rfl) ⟨5568992, by rfl⟩ : syracuseStep 7425323 = 11137985) B11137985
theorem B4950215 : Blo 2199435 4950215 := bstep (se 1 (by rfl) ⟨3712661, by rfl⟩ : syracuseStep 4950215 = 7425323) B7425323
theorem B3300143 : Blo 2199435 3300143 := bstep (se 1 (by rfl) ⟨2475107, by rfl⟩ : syracuseStep 3300143 = 4950215) B4950215
theorem B2200095 : Blo 2199435 2200095 := bstep (se 1 (by rfl) ⟨1650071, by rfl⟩ : syracuseStep 2200095 = 3300143) B3300143
theorem B3300149 : Blo 2199435 3300149 := bbase (se 5 (by rfl) ⟨154694, by rfl⟩ : syracuseStep 3300149 = 309389) (by norm_num)
theorem B2200099 : Blo 2199435 2200099 := bstep (se 1 (by rfl) ⟨1650074, by rfl⟩ : syracuseStep 2200099 = 3300149) B3300149
theorem B5569013 : Blo 2199435 5569013 := bbase (se 5 (by rfl) ⟨261047, by rfl⟩ : syracuseStep 5569013 = 522095) (by norm_num)
theorem B3712675 : Blo 2199435 3712675 := bstep (se 1 (by rfl) ⟨2784506, by rfl⟩ : syracuseStep 3712675 = 5569013) B5569013
theorem B4950233 : Blo 2199435 4950233 := bstep (se 2 (by rfl) ⟨1856337, by rfl⟩ : syracuseStep 4950233 = 3712675) B3712675
theorem B3300155 : Blo 2199435 3300155 := bstep (se 1 (by rfl) ⟨2475116, by rfl⟩ : syracuseStep 3300155 = 4950233) B4950233
theorem B2200103 : Blo 2199435 2200103 := bstep (se 1 (by rfl) ⟨1650077, by rfl⟩ : syracuseStep 2200103 = 3300155) B3300155
theorem B2475121 : Blo 2199435 2475121 := bbase (se 2 (by rfl) ⟨928170, by rfl⟩ : syracuseStep 2475121 = 1856341) (by norm_num)
theorem B3300161 : Blo 2199435 3300161 := bstep (se 2 (by rfl) ⟨1237560, by rfl⟩ : syracuseStep 3300161 = 2475121) B2475121
theorem B2200107 : Blo 2199435 2200107 := bstep (se 1 (by rfl) ⟨1650080, by rfl⟩ : syracuseStep 2200107 = 3300161) B3300161
theorem B7048309 : Blo 2199435 7048309 := bbase (se 5 (by rfl) ⟨330389, by rfl⟩ : syracuseStep 7048309 = 660779) (by norm_num)
theorem B9397745 : Blo 2199435 9397745 := bstep (se 2 (by rfl) ⟨3524154, by rfl⟩ : syracuseStep 9397745 = 7048309) B7048309
theorem B6265163 : Blo 2199435 6265163 := bstep (se 1 (by rfl) ⟨4698872, by rfl⟩ : syracuseStep 6265163 = 9397745) B9397745
theorem B4176775 : Blo 2199435 4176775 := bstep (se 1 (by rfl) ⟨3132581, by rfl⟩ : syracuseStep 4176775 = 6265163) B6265163
theorem B5569033 : Blo 2199435 5569033 := bstep (se 2 (by rfl) ⟨2088387, by rfl⟩ : syracuseStep 5569033 = 4176775) B4176775
theorem B7425377 : Blo 2199435 7425377 := bstep (se 2 (by rfl) ⟨2784516, by rfl⟩ : syracuseStep 7425377 = 5569033) B5569033
theorem B4950251 : Blo 2199435 4950251 := bstep (se 1 (by rfl) ⟨3712688, by rfl⟩ : syracuseStep 4950251 = 7425377) B7425377
theorem B3300167 : Blo 2199435 3300167 := bstep (se 1 (by rfl) ⟨2475125, by rfl⟩ : syracuseStep 3300167 = 4950251) B4950251
theorem B2200111 : Blo 2199435 2200111 := bstep (se 1 (by rfl) ⟨1650083, by rfl⟩ : syracuseStep 2200111 = 3300167) B3300167
theorem B3300173 : Blo 2199435 3300173 := bbase (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) (by norm_num)
theorem B2200115 : Blo 2199435 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B4950269 : Blo 2199435 4950269 := bbase (se 3 (by rfl) ⟨928175, by rfl⟩ : syracuseStep 4950269 = 1856351) (by norm_num)
theorem B3300179 : Blo 2199435 3300179 := bstep (se 1 (by rfl) ⟨2475134, by rfl⟩ : syracuseStep 3300179 = 4950269) B4950269
theorem B2200119 : Blo 2199435 2200119 := bstep (se 1 (by rfl) ⟨1650089, by rfl⟩ : syracuseStep 2200119 = 3300179) B3300179
theorem B3712709 : Blo 2199435 3712709 := bbase (se 4 (by rfl) ⟨348066, by rfl⟩ : syracuseStep 3712709 = 696133) (by norm_num)
theorem B2475139 : Blo 2199435 2475139 := bstep (se 1 (by rfl) ⟨1856354, by rfl⟩ : syracuseStep 2475139 = 3712709) B3712709
theorem B3300185 : Blo 2199435 3300185 := bstep (se 2 (by rfl) ⟨1237569, by rfl⟩ : syracuseStep 3300185 = 2475139) B2475139
theorem B2200123 : Blo 2199435 2200123 := bstep (se 1 (by rfl) ⟨1650092, by rfl⟩ : syracuseStep 2200123 = 3300185) B3300185
theorem B16707221 : Blo 2199435 16707221 := bbase (se 6 (by rfl) ⟨391575, by rfl⟩ : syracuseStep 16707221 = 783151) (by norm_num)
theorem B11138147 : Blo 2199435 11138147 := bstep (se 1 (by rfl) ⟨8353610, by rfl⟩ : syracuseStep 11138147 = 16707221) B16707221
theorem B7425431 : Blo 2199435 7425431 := bstep (se 1 (by rfl) ⟨5569073, by rfl⟩ : syracuseStep 7425431 = 11138147) B11138147
theorem B4950287 : Blo 2199435 4950287 := bstep (se 1 (by rfl) ⟨3712715, by rfl⟩ : syracuseStep 4950287 = 7425431) B7425431
theorem B3300191 : Blo 2199435 3300191 := bstep (se 1 (by rfl) ⟨2475143, by rfl⟩ : syracuseStep 3300191 = 4950287) B4950287
theorem B2200127 : Blo 2199435 2200127 := bstep (se 1 (by rfl) ⟨1650095, by rfl⟩ : syracuseStep 2200127 = 3300191) B3300191
theorem B3300197 : Blo 2199435 3300197 := bbase (se 4 (by rfl) ⟨309393, by rfl⟩ : syracuseStep 3300197 = 618787) (by norm_num)
theorem B2200131 : Blo 2199435 2200131 := bstep (se 1 (by rfl) ⟨1650098, by rfl⟩ : syracuseStep 2200131 = 3300197) B3300197
theorem B4176821 : Blo 2199435 4176821 := bbase (se 5 (by rfl) ⟨195788, by rfl⟩ : syracuseStep 4176821 = 391577) (by norm_num)
theorem B2784547 : Blo 2199435 2784547 := bstep (se 1 (by rfl) ⟨2088410, by rfl⟩ : syracuseStep 2784547 = 4176821) B4176821
theorem B3712729 : Blo 2199435 3712729 := bstep (se 2 (by rfl) ⟨1392273, by rfl⟩ : syracuseStep 3712729 = 2784547) B2784547
theorem B4950305 : Blo 2199435 4950305 := bstep (se 2 (by rfl) ⟨1856364, by rfl⟩ : syracuseStep 4950305 = 3712729) B3712729
theorem B3300203 : Blo 2199435 3300203 := bstep (se 1 (by rfl) ⟨2475152, by rfl⟩ : syracuseStep 3300203 = 4950305) B4950305
theorem B2200135 : Blo 2199435 2200135 := bstep (se 1 (by rfl) ⟨1650101, by rfl⟩ : syracuseStep 2200135 = 3300203) B3300203
theorem B2475157 : Blo 2199435 2475157 := bbase (se 6 (by rfl) ⟨58011, by rfl⟩ : syracuseStep 2475157 = 116023) (by norm_num)
theorem B3300209 : Blo 2199435 3300209 := bstep (se 2 (by rfl) ⟨1237578, by rfl⟩ : syracuseStep 3300209 = 2475157) B2475157
theorem B2200139 : Blo 2199435 2200139 := bstep (se 1 (by rfl) ⟨1650104, by rfl⟩ : syracuseStep 2200139 = 3300209) B3300209
theorem B2784557 : Blo 2199435 2784557 := bbase (se 3 (by rfl) ⟨522104, by rfl⟩ : syracuseStep 2784557 = 1044209) (by norm_num)
theorem B7425485 : Blo 2199435 7425485 := bstep (se 3 (by rfl) ⟨1392278, by rfl⟩ : syracuseStep 7425485 = 2784557) B2784557
theorem B4950323 : Blo 2199435 4950323 := bstep (se 1 (by rfl) ⟨3712742, by rfl⟩ : syracuseStep 4950323 = 7425485) B7425485
theorem B3300215 : Blo 2199435 3300215 := bstep (se 1 (by rfl) ⟨2475161, by rfl⟩ : syracuseStep 3300215 = 4950323) B4950323
theorem B2200143 : Blo 2199435 2200143 := bstep (se 1 (by rfl) ⟨1650107, by rfl⟩ : syracuseStep 2200143 = 3300215) B3300215
theorem B3300221 : Blo 2199435 3300221 := bbase (se 3 (by rfl) ⟨618791, by rfl⟩ : syracuseStep 3300221 = 1237583) (by norm_num)
theorem B2200147 : Blo 2199435 2200147 := bstep (se 1 (by rfl) ⟨1650110, by rfl⟩ : syracuseStep 2200147 = 3300221) B3300221
theorem B4950341 : Blo 2199435 4950341 := bbase (se 4 (by rfl) ⟨464094, by rfl⟩ : syracuseStep 4950341 = 928189) (by norm_num)
theorem B3300227 : Blo 2199435 3300227 := bstep (se 1 (by rfl) ⟨2475170, by rfl⟩ : syracuseStep 3300227 = 4950341) B4950341
theorem B2200151 : Blo 2199435 2200151 := bstep (se 1 (by rfl) ⟨1650113, by rfl⟩ : syracuseStep 2200151 = 3300227) B3300227
theorem B10572677 : Blo 2199435 10572677 := bbase (se 4 (by rfl) ⟨991188, by rfl⟩ : syracuseStep 10572677 = 1982377) (by norm_num)
theorem B7048451 : Blo 2199435 7048451 := bstep (se 1 (by rfl) ⟨5286338, by rfl⟩ : syracuseStep 7048451 = 10572677) B10572677
theorem B4698967 : Blo 2199435 4698967 := bstep (se 1 (by rfl) ⟨3524225, by rfl⟩ : syracuseStep 4698967 = 7048451) B7048451
theorem B6265289 : Blo 2199435 6265289 := bstep (se 2 (by rfl) ⟨2349483, by rfl⟩ : syracuseStep 6265289 = 4698967) B4698967
theorem B4176859 : Blo 2199435 4176859 := bstep (se 1 (by rfl) ⟨3132644, by rfl⟩ : syracuseStep 4176859 = 6265289) B6265289
theorem B5569145 : Blo 2199435 5569145 := bstep (se 2 (by rfl) ⟨2088429, by rfl⟩ : syracuseStep 5569145 = 4176859) B4176859
theorem B3712763 : Blo 2199435 3712763 := bstep (se 1 (by rfl) ⟨2784572, by rfl⟩ : syracuseStep 3712763 = 5569145) B5569145
theorem B2475175 : Blo 2199435 2475175 := bstep (se 1 (by rfl) ⟨1856381, by rfl⟩ : syracuseStep 2475175 = 3712763) B3712763
theorem B3300233 : Blo 2199435 3300233 := bstep (se 2 (by rfl) ⟨1237587, by rfl⟩ : syracuseStep 3300233 = 2475175) B2475175
theorem B2200155 : Blo 2199435 2200155 := bstep (se 1 (by rfl) ⟨1650116, by rfl⟩ : syracuseStep 2200155 = 3300233) B3300233
theorem B11138309 : Blo 2199435 11138309 := bbase (se 4 (by rfl) ⟨1044216, by rfl⟩ : syracuseStep 11138309 = 2088433) (by norm_num)
theorem B7425539 : Blo 2199435 7425539 := bstep (se 1 (by rfl) ⟨5569154, by rfl⟩ : syracuseStep 7425539 = 11138309) B11138309
theorem B4950359 : Blo 2199435 4950359 := bstep (se 1 (by rfl) ⟨3712769, by rfl⟩ : syracuseStep 4950359 = 7425539) B7425539
theorem B3300239 : Blo 2199435 3300239 := bstep (se 1 (by rfl) ⟨2475179, by rfl⟩ : syracuseStep 3300239 = 4950359) B4950359
theorem B2200159 : Blo 2199435 2200159 := bstep (se 1 (by rfl) ⟨1650119, by rfl⟩ : syracuseStep 2200159 = 3300239) B3300239
theorem B3300245 : Blo 2199435 3300245 := bbase (se 6 (by rfl) ⟨77349, by rfl⟩ : syracuseStep 3300245 = 154699) (by norm_num)
theorem B2200163 : Blo 2199435 2200163 := bstep (se 1 (by rfl) ⟨1650122, by rfl⟩ : syracuseStep 2200163 = 3300245) B3300245
theorem B12530645 : Blo 2199435 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B8353763 : Blo 2199435 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B5569175 : Blo 2199435 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B3712783 : Blo 2199435 3712783 := bstep (se 1 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 3712783 = 5569175) B5569175
theorem B4950377 : Blo 2199435 4950377 := bstep (se 2 (by rfl) ⟨1856391, by rfl⟩ : syracuseStep 4950377 = 3712783) B3712783
theorem B3300251 : Blo 2199435 3300251 := bstep (se 1 (by rfl) ⟨2475188, by rfl⟩ : syracuseStep 3300251 = 4950377) B4950377
theorem B2200167 : Blo 2199435 2200167 := bstep (se 1 (by rfl) ⟨1650125, by rfl⟩ : syracuseStep 2200167 = 3300251) B3300251
theorem B2475193 : Blo 2199435 2475193 := bbase (se 2 (by rfl) ⟨928197, by rfl⟩ : syracuseStep 2475193 = 1856395) (by norm_num)
theorem B3300257 : Blo 2199435 3300257 := bstep (se 2 (by rfl) ⟨1237596, by rfl⟩ : syracuseStep 3300257 = 2475193) B2475193
theorem B2200171 : Blo 2199435 2200171 := bstep (se 1 (by rfl) ⟨1650128, by rfl⟩ : syracuseStep 2200171 = 3300257) B3300257
theorem B2643193 : Blo 2199435 2643193 := bbase (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) (by norm_num)
theorem B3524257 : Blo 2199435 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B4699009 : Blo 2199435 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B6265345 : Blo 2199435 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B8353793 : Blo 2199435 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B5569195 : Blo 2199435 5569195 := bstep (se 1 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 5569195 = 8353793) B8353793
theorem B7425593 : Blo 2199435 7425593 := bstep (se 2 (by rfl) ⟨2784597, by rfl⟩ : syracuseStep 7425593 = 5569195) B5569195
theorem B4950395 : Blo 2199435 4950395 := bstep (se 1 (by rfl) ⟨3712796, by rfl⟩ : syracuseStep 4950395 = 7425593) B7425593
theorem B3300263 : Blo 2199435 3300263 := bstep (se 1 (by rfl) ⟨2475197, by rfl⟩ : syracuseStep 3300263 = 4950395) B4950395
theorem B2200175 : Blo 2199435 2200175 := bstep (se 1 (by rfl) ⟨1650131, by rfl⟩ : syracuseStep 2200175 = 3300263) B3300263
theorem B3300269 : Blo 2199435 3300269 := bbase (se 3 (by rfl) ⟨618800, by rfl⟩ : syracuseStep 3300269 = 1237601) (by norm_num)
theorem B2200179 : Blo 2199435 2200179 := bstep (se 1 (by rfl) ⟨1650134, by rfl⟩ : syracuseStep 2200179 = 3300269) B3300269
theorem B4950413 : Blo 2199435 4950413 := bbase (se 3 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 4950413 = 1856405) (by norm_num)
theorem B3300275 : Blo 2199435 3300275 := bstep (se 1 (by rfl) ⟨2475206, by rfl⟩ : syracuseStep 3300275 = 4950413) B4950413
theorem B2200183 : Blo 2199435 2200183 := bstep (se 1 (by rfl) ⟨1650137, by rfl⟩ : syracuseStep 2200183 = 3300275) B3300275
theorem B2784613 : Blo 2199435 2784613 := bbase (se 4 (by rfl) ⟨261057, by rfl⟩ : syracuseStep 2784613 = 522115) (by norm_num)
theorem B3712817 : Blo 2199435 3712817 := bstep (se 2 (by rfl) ⟨1392306, by rfl⟩ : syracuseStep 3712817 = 2784613) B2784613
theorem B2475211 : Blo 2199435 2475211 := bstep (se 1 (by rfl) ⟨1856408, by rfl⟩ : syracuseStep 2475211 = 3712817) B3712817
theorem B3300281 : Blo 2199435 3300281 := bstep (se 2 (by rfl) ⟨1237605, by rfl⟩ : syracuseStep 3300281 = 2475211) B2475211
theorem B2200187 : Blo 2199435 2200187 := bstep (se 1 (by rfl) ⟨1650140, by rfl⟩ : syracuseStep 2200187 = 3300281) B3300281
theorem B11894453 : Blo 2199435 11894453 := bbase (se 5 (by rfl) ⟨557552, by rfl⟩ : syracuseStep 11894453 = 1115105) (by norm_num)
theorem B7929635 : Blo 2199435 7929635 := bstep (se 1 (by rfl) ⟨5947226, by rfl⟩ : syracuseStep 7929635 = 11894453) B11894453
theorem B21145693 : Blo 2199435 21145693 := bstep (se 3 (by rfl) ⟨3964817, by rfl⟩ : syracuseStep 21145693 = 7929635) B7929635
theorem B28194257 : Blo 2199435 28194257 := bstep (se 2 (by rfl) ⟨10572846, by rfl⟩ : syracuseStep 28194257 = 21145693) B21145693
theorem B18796171 : Blo 2199435 18796171 := bstep (se 1 (by rfl) ⟨14097128, by rfl⟩ : syracuseStep 18796171 = 28194257) B28194257
theorem B25061561 : Blo 2199435 25061561 := bstep (se 2 (by rfl) ⟨9398085, by rfl⟩ : syracuseStep 25061561 = 18796171) B18796171
theorem B16707707 : Blo 2199435 16707707 := bstep (se 1 (by rfl) ⟨12530780, by rfl⟩ : syracuseStep 16707707 = 25061561) B25061561
theorem B11138471 : Blo 2199435 11138471 := bstep (se 1 (by rfl) ⟨8353853, by rfl⟩ : syracuseStep 11138471 = 16707707) B16707707
theorem B7425647 : Blo 2199435 7425647 := bstep (se 1 (by rfl) ⟨5569235, by rfl⟩ : syracuseStep 7425647 = 11138471) B11138471
theorem B4950431 : Blo 2199435 4950431 := bstep (se 1 (by rfl) ⟨3712823, by rfl⟩ : syracuseStep 4950431 = 7425647) B7425647
theorem B3300287 : Blo 2199435 3300287 := bstep (se 1 (by rfl) ⟨2475215, by rfl⟩ : syracuseStep 3300287 = 4950431) B4950431
theorem B2200191 : Blo 2199435 2200191 := bstep (se 1 (by rfl) ⟨1650143, by rfl⟩ : syracuseStep 2200191 = 3300287) B3300287
theorem B3300293 : Blo 2199435 3300293 := bbase (se 4 (by rfl) ⟨309402, by rfl⟩ : syracuseStep 3300293 = 618805) (by norm_num)
theorem B2200195 : Blo 2199435 2200195 := bstep (se 1 (by rfl) ⟨1650146, by rfl⟩ : syracuseStep 2200195 = 3300293) B3300293
theorem B3712837 : Blo 2199435 3712837 := bbase (se 4 (by rfl) ⟨348078, by rfl⟩ : syracuseStep 3712837 = 696157) (by norm_num)
theorem B4950449 : Blo 2199435 4950449 := bstep (se 2 (by rfl) ⟨1856418, by rfl⟩ : syracuseStep 4950449 = 3712837) B3712837
theorem B3300299 : Blo 2199435 3300299 := bstep (se 1 (by rfl) ⟨2475224, by rfl⟩ : syracuseStep 3300299 = 4950449) B4950449
theorem B2200199 : Blo 2199435 2200199 := bstep (se 1 (by rfl) ⟨1650149, by rfl⟩ : syracuseStep 2200199 = 3300299) B3300299
theorem B2475229 : Blo 2199435 2475229 := bbase (se 3 (by rfl) ⟨464105, by rfl⟩ : syracuseStep 2475229 = 928211) (by norm_num)
theorem B3300305 : Blo 2199435 3300305 := bstep (se 2 (by rfl) ⟨1237614, by rfl⟩ : syracuseStep 3300305 = 2475229) B2475229
theorem B2200203 : Blo 2199435 2200203 := bstep (se 1 (by rfl) ⟨1650152, by rfl⟩ : syracuseStep 2200203 = 3300305) B3300305
theorem B7425701 : Blo 2199435 7425701 := bbase (se 4 (by rfl) ⟨696159, by rfl⟩ : syracuseStep 7425701 = 1392319) (by norm_num)
theorem B4950467 : Blo 2199435 4950467 := bstep (se 1 (by rfl) ⟨3712850, by rfl⟩ : syracuseStep 4950467 = 7425701) B7425701
theorem B3300311 : Blo 2199435 3300311 := bstep (se 1 (by rfl) ⟨2475233, by rfl⟩ : syracuseStep 3300311 = 4950467) B4950467
theorem B2200207 : Blo 2199435 2200207 := bstep (se 1 (by rfl) ⟨1650155, by rfl⟩ : syracuseStep 2200207 = 3300311) B3300311
theorem B3300317 : Blo 2199435 3300317 := bbase (se 3 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 3300317 = 1237619) (by norm_num)
theorem B2200211 : Blo 2199435 2200211 := bstep (se 1 (by rfl) ⟨1650158, by rfl⟩ : syracuseStep 2200211 = 3300317) B3300317
theorem B4950485 : Blo 2199435 4950485 := bbase (se 7 (by rfl) ⟨58013, by rfl⟩ : syracuseStep 4950485 = 116027) (by norm_num)
theorem B3300323 : Blo 2199435 3300323 := bstep (se 1 (by rfl) ⟨2475242, by rfl⟩ : syracuseStep 3300323 = 4950485) B4950485
theorem B2200215 : Blo 2199435 2200215 := bstep (se 1 (by rfl) ⟨1650161, by rfl⟩ : syracuseStep 2200215 = 3300323) B3300323
theorem B80288597 : Blo 2199435 80288597 := bbase (se 9 (by rfl) ⟨235220, by rfl⟩ : syracuseStep 80288597 = 470441) (by norm_num)
theorem B53525731 : Blo 2199435 53525731 := bstep (se 1 (by rfl) ⟨40144298, by rfl⟩ : syracuseStep 53525731 = 80288597) B80288597
theorem B71367641 : Blo 2199435 71367641 := bstep (se 2 (by rfl) ⟨26762865, by rfl⟩ : syracuseStep 71367641 = 53525731) B53525731
theorem B47578427 : Blo 2199435 47578427 := bstep (se 1 (by rfl) ⟨35683820, by rfl⟩ : syracuseStep 47578427 = 71367641) B71367641
theorem B31718951 : Blo 2199435 31718951 := bstep (se 1 (by rfl) ⟨23789213, by rfl⟩ : syracuseStep 31718951 = 47578427) B47578427
theorem B21145967 : Blo 2199435 21145967 := bstep (se 1 (by rfl) ⟨15859475, by rfl⟩ : syracuseStep 21145967 = 31718951) B31718951
theorem B14097311 : Blo 2199435 14097311 := bstep (se 1 (by rfl) ⟨10572983, by rfl⟩ : syracuseStep 14097311 = 21145967) B21145967
theorem B9398207 : Blo 2199435 9398207 := bstep (se 1 (by rfl) ⟨7048655, by rfl⟩ : syracuseStep 9398207 = 14097311) B14097311
theorem B6265471 : Blo 2199435 6265471 := bstep (se 1 (by rfl) ⟨4699103, by rfl⟩ : syracuseStep 6265471 = 9398207) B9398207
theorem B8353961 : Blo 2199435 8353961 := bstep (se 2 (by rfl) ⟨3132735, by rfl⟩ : syracuseStep 8353961 = 6265471) B6265471
theorem B5569307 : Blo 2199435 5569307 := bstep (se 1 (by rfl) ⟨4176980, by rfl⟩ : syracuseStep 5569307 = 8353961) B8353961
theorem B3712871 : Blo 2199435 3712871 := bstep (se 1 (by rfl) ⟨2784653, by rfl⟩ : syracuseStep 3712871 = 5569307) B5569307
theorem B2475247 : Blo 2199435 2475247 := bstep (se 1 (by rfl) ⟨1856435, by rfl⟩ : syracuseStep 2475247 = 3712871) B3712871
theorem B3300329 : Blo 2199435 3300329 := bstep (se 2 (by rfl) ⟨1237623, by rfl⟩ : syracuseStep 3300329 = 2475247) B2475247
theorem B2200219 : Blo 2199435 2200219 := bstep (se 1 (by rfl) ⟨1650164, by rfl⟩ : syracuseStep 2200219 = 3300329) B3300329
theorem B17841941 : Blo 2199435 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B11894627 : Blo 2199435 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B7929751 : Blo 2199435 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B10573001 : Blo 2199435 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B7048667 : Blo 2199435 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B18796445 : Blo 2199435 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B12530963 : Blo 2199435 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B8353975 : Blo 2199435 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B11138633 : Blo 2199435 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B7425755 : Blo 2199435 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B4950503 : Blo 2199435 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B3300335 : Blo 2199435 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2200223 : Blo 2199435 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B3300341 : Blo 2199435 3300341 := bbase (se 5 (by rfl) ⟨154703, by rfl⟩ : syracuseStep 3300341 = 309407) (by norm_num)
theorem B2200227 : Blo 2199435 2200227 := bstep (se 1 (by rfl) ⟨1650170, by rfl⟩ : syracuseStep 2200227 = 3300341) B3300341
theorem B10036133 : Blo 2199435 10036133 := bbase (se 4 (by rfl) ⟨940887, by rfl⟩ : syracuseStep 10036133 = 1881775) (by norm_num)
theorem B6690755 : Blo 2199435 6690755 := bstep (se 1 (by rfl) ⟨5018066, by rfl⟩ : syracuseStep 6690755 = 10036133) B10036133
theorem B4460503 : Blo 2199435 4460503 := bstep (se 1 (by rfl) ⟨3345377, by rfl⟩ : syracuseStep 4460503 = 6690755) B6690755
theorem B5947337 : Blo 2199435 5947337 := bstep (se 2 (by rfl) ⟨2230251, by rfl⟩ : syracuseStep 5947337 = 4460503) B4460503
theorem B3964891 : Blo 2199435 3964891 := bstep (se 1 (by rfl) ⟨2973668, by rfl⟩ : syracuseStep 3964891 = 5947337) B5947337
theorem B5286521 : Blo 2199435 5286521 := bstep (se 2 (by rfl) ⟨1982445, by rfl⟩ : syracuseStep 5286521 = 3964891) B3964891
theorem B3524347 : Blo 2199435 3524347 := bstep (se 1 (by rfl) ⟨2643260, by rfl⟩ : syracuseStep 3524347 = 5286521) B5286521
theorem B4699129 : Blo 2199435 4699129 := bstep (se 2 (by rfl) ⟨1762173, by rfl⟩ : syracuseStep 4699129 = 3524347) B3524347
theorem B6265505 : Blo 2199435 6265505 := bstep (se 2 (by rfl) ⟨2349564, by rfl⟩ : syracuseStep 6265505 = 4699129) B4699129
theorem B4177003 : Blo 2199435 4177003 := bstep (se 1 (by rfl) ⟨3132752, by rfl⟩ : syracuseStep 4177003 = 6265505) B6265505
theorem B5569337 : Blo 2199435 5569337 := bstep (se 2 (by rfl) ⟨2088501, by rfl⟩ : syracuseStep 5569337 = 4177003) B4177003
theorem B3712891 : Blo 2199435 3712891 := bstep (se 1 (by rfl) ⟨2784668, by rfl⟩ : syracuseStep 3712891 = 5569337) B5569337
theorem B4950521 : Blo 2199435 4950521 := bstep (se 2 (by rfl) ⟨1856445, by rfl⟩ : syracuseStep 4950521 = 3712891) B3712891
theorem B3300347 : Blo 2199435 3300347 := bstep (se 1 (by rfl) ⟨2475260, by rfl⟩ : syracuseStep 3300347 = 4950521) B4950521
theorem B2200231 : Blo 2199435 2200231 := bstep (se 1 (by rfl) ⟨1650173, by rfl⟩ : syracuseStep 2200231 = 3300347) B3300347
theorem B2475265 : Blo 2199435 2475265 := bbase (se 2 (by rfl) ⟨928224, by rfl⟩ : syracuseStep 2475265 = 1856449) (by norm_num)
theorem B3300353 : Blo 2199435 3300353 := bstep (se 2 (by rfl) ⟨1237632, by rfl⟩ : syracuseStep 3300353 = 2475265) B2475265
theorem B2200235 : Blo 2199435 2200235 := bstep (se 1 (by rfl) ⟨1650176, by rfl⟩ : syracuseStep 2200235 = 3300353) B3300353
theorem B5569357 : Blo 2199435 5569357 := bbase (se 3 (by rfl) ⟨1044254, by rfl⟩ : syracuseStep 5569357 = 2088509) (by norm_num)
theorem B7425809 : Blo 2199435 7425809 := bstep (se 2 (by rfl) ⟨2784678, by rfl⟩ : syracuseStep 7425809 = 5569357) B5569357
theorem B4950539 : Blo 2199435 4950539 := bstep (se 1 (by rfl) ⟨3712904, by rfl⟩ : syracuseStep 4950539 = 7425809) B7425809
theorem B3300359 : Blo 2199435 3300359 := bstep (se 1 (by rfl) ⟨2475269, by rfl⟩ : syracuseStep 3300359 = 4950539) B4950539
theorem B2200239 : Blo 2199435 2200239 := bstep (se 1 (by rfl) ⟨1650179, by rfl⟩ : syracuseStep 2200239 = 3300359) B3300359
theorem B3300365 : Blo 2199435 3300365 := bbase (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) (by norm_num)
theorem B2200243 : Blo 2199435 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B4950557 : Blo 2199435 4950557 := bbase (se 3 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 4950557 = 1856459) (by norm_num)
theorem B3300371 : Blo 2199435 3300371 := bstep (se 1 (by rfl) ⟨2475278, by rfl⟩ : syracuseStep 3300371 = 4950557) B4950557
theorem B2200247 : Blo 2199435 2200247 := bstep (se 1 (by rfl) ⟨1650185, by rfl⟩ : syracuseStep 2200247 = 3300371) B3300371
theorem B3712925 : Blo 2199435 3712925 := bbase (se 3 (by rfl) ⟨696173, by rfl⟩ : syracuseStep 3712925 = 1392347) (by norm_num)
theorem B2475283 : Blo 2199435 2475283 := bstep (se 1 (by rfl) ⟨1856462, by rfl⟩ : syracuseStep 2475283 = 3712925) B3712925
theorem B3300377 : Blo 2199435 3300377 := bstep (se 2 (by rfl) ⟨1237641, by rfl⟩ : syracuseStep 3300377 = 2475283) B2475283
theorem B2200251 : Blo 2199435 2200251 := bstep (se 1 (by rfl) ⟨1650188, by rfl⟩ : syracuseStep 2200251 = 3300377) B3300377
theorem B3964933 : Blo 2199435 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B21146309 : Blo 2199435 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B14097539 : Blo 2199435 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B9398359 : Blo 2199435 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B12531145 : Blo 2199435 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B16708193 : Blo 2199435 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B11138795 : Blo 2199435 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B7425863 : Blo 2199435 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B4950575 : Blo 2199435 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B3300383 : Blo 2199435 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B2200255 : Blo 2199435 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B3300389 : Blo 2199435 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B2200259 : Blo 2199435 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B2784709 : Blo 2199435 2784709 := bbase (se 4 (by rfl) ⟨261066, by rfl⟩ : syracuseStep 2784709 = 522133) (by norm_num)
theorem B3712945 : Blo 2199435 3712945 := bstep (se 2 (by rfl) ⟨1392354, by rfl⟩ : syracuseStep 3712945 = 2784709) B2784709
theorem B4950593 : Blo 2199435 4950593 := bstep (se 2 (by rfl) ⟨1856472, by rfl⟩ : syracuseStep 4950593 = 3712945) B3712945
theorem B3300395 : Blo 2199435 3300395 := bstep (se 1 (by rfl) ⟨2475296, by rfl⟩ : syracuseStep 3300395 = 4950593) B4950593
theorem B2200263 : Blo 2199435 2200263 := bstep (se 1 (by rfl) ⟨1650197, by rfl⟩ : syracuseStep 2200263 = 3300395) B3300395
theorem B2475301 : Blo 2199435 2475301 := bbase (se 4 (by rfl) ⟨232059, by rfl⟩ : syracuseStep 2475301 = 464119) (by norm_num)
theorem B3300401 : Blo 2199435 3300401 := bstep (se 2 (by rfl) ⟨1237650, by rfl⟩ : syracuseStep 3300401 = 2475301) B2475301
theorem B2200267 : Blo 2199435 2200267 := bstep (se 1 (by rfl) ⟨1650200, by rfl⟩ : syracuseStep 2200267 = 3300401) B3300401
theorem B5947445 : Blo 2199435 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B3964963 : Blo 2199435 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B5286617 : Blo 2199435 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B3524411 : Blo 2199435 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B9398429 : Blo 2199435 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B6265619 : Blo 2199435 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B4177079 : Blo 2199435 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B2784719 : Blo 2199435 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B7425917 : Blo 2199435 7425917 := bstep (se 3 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 7425917 = 2784719) B2784719
theorem B4950611 : Blo 2199435 4950611 := bstep (se 1 (by rfl) ⟨3712958, by rfl⟩ : syracuseStep 4950611 = 7425917) B7425917
theorem B3300407 : Blo 2199435 3300407 := bstep (se 1 (by rfl) ⟨2475305, by rfl⟩ : syracuseStep 3300407 = 4950611) B4950611
theorem B2200271 : Blo 2199435 2200271 := bstep (se 1 (by rfl) ⟨1650203, by rfl⟩ : syracuseStep 2200271 = 3300407) B3300407
theorem B3300413 : Blo 2199435 3300413 := bbase (se 3 (by rfl) ⟨618827, by rfl⟩ : syracuseStep 3300413 = 1237655) (by norm_num)
theorem B2200275 : Blo 2199435 2200275 := bstep (se 1 (by rfl) ⟨1650206, by rfl⟩ : syracuseStep 2200275 = 3300413) B3300413
theorem B4950629 : Blo 2199435 4950629 := bbase (se 4 (by rfl) ⟨464121, by rfl⟩ : syracuseStep 4950629 = 928243) (by norm_num)
theorem B3300419 : Blo 2199435 3300419 := bstep (se 1 (by rfl) ⟨2475314, by rfl⟩ : syracuseStep 3300419 = 4950629) B4950629
theorem B2200279 : Blo 2199435 2200279 := bstep (se 1 (by rfl) ⟨1650209, by rfl⟩ : syracuseStep 2200279 = 3300419) B3300419
theorem B5569469 : Blo 2199435 5569469 := bbase (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) (by norm_num)
theorem B3712979 : Blo 2199435 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B2475319 : Blo 2199435 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B3300425 : Blo 2199435 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B2200283 : Blo 2199435 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B4177109 : Blo 2199435 4177109 := bbase (se 7 (by rfl) ⟨48950, by rfl⟩ : syracuseStep 4177109 = 97901) (by norm_num)
theorem B11138957 : Blo 2199435 11138957 := bstep (se 3 (by rfl) ⟨2088554, by rfl⟩ : syracuseStep 11138957 = 4177109) B4177109
theorem B7425971 : Blo 2199435 7425971 := bstep (se 1 (by rfl) ⟨5569478, by rfl⟩ : syracuseStep 7425971 = 11138957) B11138957
theorem B4950647 : Blo 2199435 4950647 := bstep (se 1 (by rfl) ⟨3712985, by rfl⟩ : syracuseStep 4950647 = 7425971) B7425971
theorem B3300431 : Blo 2199435 3300431 := bstep (se 1 (by rfl) ⟨2475323, by rfl⟩ : syracuseStep 3300431 = 4950647) B4950647
theorem B2200287 : Blo 2199435 2200287 := bstep (se 1 (by rfl) ⟨1650215, by rfl⟩ : syracuseStep 2200287 = 3300431) B3300431
theorem B3300437 : Blo 2199435 3300437 := bbase (se 8 (by rfl) ⟨19338, by rfl⟩ : syracuseStep 3300437 = 38677) (by norm_num)
theorem B2200291 : Blo 2199435 2200291 := bstep (se 1 (by rfl) ⟨1650218, by rfl⟩ : syracuseStep 2200291 = 3300437) B3300437
theorem B2643337 : Blo 2199435 2643337 := bbase (se 2 (by rfl) ⟨991251, by rfl⟩ : syracuseStep 2643337 = 1982503) (by norm_num)
theorem B14097797 : Blo 2199435 14097797 := bstep (se 4 (by rfl) ⟨1321668, by rfl⟩ : syracuseStep 14097797 = 2643337) B2643337
theorem B9398531 : Blo 2199435 9398531 := bstep (se 1 (by rfl) ⟨7048898, by rfl⟩ : syracuseStep 9398531 = 14097797) B14097797
theorem B6265687 : Blo 2199435 6265687 := bstep (se 1 (by rfl) ⟨4699265, by rfl⟩ : syracuseStep 6265687 = 9398531) B9398531
theorem B8354249 : Blo 2199435 8354249 := bstep (se 2 (by rfl) ⟨3132843, by rfl⟩ : syracuseStep 8354249 = 6265687) B6265687
theorem B5569499 : Blo 2199435 5569499 := bstep (se 1 (by rfl) ⟨4177124, by rfl⟩ : syracuseStep 5569499 = 8354249) B8354249
theorem B3712999 : Blo 2199435 3712999 := bstep (se 1 (by rfl) ⟨2784749, by rfl⟩ : syracuseStep 3712999 = 5569499) B5569499
theorem B4950665 : Blo 2199435 4950665 := bstep (se 2 (by rfl) ⟨1856499, by rfl⟩ : syracuseStep 4950665 = 3712999) B3712999
theorem B3300443 : Blo 2199435 3300443 := bstep (se 1 (by rfl) ⟨2475332, by rfl⟩ : syracuseStep 3300443 = 4950665) B4950665
theorem B2200295 : Blo 2199435 2200295 := bstep (se 1 (by rfl) ⟨1650221, by rfl⟩ : syracuseStep 2200295 = 3300443) B3300443
theorem B2475337 : Blo 2199435 2475337 := bbase (se 2 (by rfl) ⟨928251, by rfl⟩ : syracuseStep 2475337 = 1856503) (by norm_num)
theorem B3300449 : Blo 2199435 3300449 := bstep (se 2 (by rfl) ⟨1237668, by rfl⟩ : syracuseStep 3300449 = 2475337) B2475337
theorem B2200299 : Blo 2199435 2200299 := bstep (se 1 (by rfl) ⟨1650224, by rfl⟩ : syracuseStep 2200299 = 3300449) B3300449
theorem B19053589 : Blo 2199435 19053589 := bbase (se 6 (by rfl) ⟨446568, by rfl⟩ : syracuseStep 19053589 = 893137) (by norm_num)
theorem B25404785 : Blo 2199435 25404785 := bstep (se 2 (by rfl) ⟨9526794, by rfl⟩ : syracuseStep 25404785 = 19053589) B19053589
theorem B16936523 : Blo 2199435 16936523 := bstep (se 1 (by rfl) ⟨12702392, by rfl⟩ : syracuseStep 16936523 = 25404785) B25404785
theorem B11291015 : Blo 2199435 11291015 := bstep (se 1 (by rfl) ⟨8468261, by rfl⟩ : syracuseStep 11291015 = 16936523) B16936523
theorem B7527343 : Blo 2199435 7527343 := bstep (se 1 (by rfl) ⟨5645507, by rfl⟩ : syracuseStep 7527343 = 11291015) B11291015
theorem B10036457 : Blo 2199435 10036457 := bstep (se 2 (by rfl) ⟨3763671, by rfl⟩ : syracuseStep 10036457 = 7527343) B7527343
theorem B6690971 : Blo 2199435 6690971 := bstep (se 1 (by rfl) ⟨5018228, by rfl⟩ : syracuseStep 6690971 = 10036457) B10036457
theorem B17842589 : Blo 2199435 17842589 := bstep (se 3 (by rfl) ⟨3345485, by rfl⟩ : syracuseStep 17842589 = 6690971) B6690971
theorem B11895059 : Blo 2199435 11895059 := bstep (se 1 (by rfl) ⟨8921294, by rfl⟩ : syracuseStep 11895059 = 17842589) B17842589
theorem B31720157 : Blo 2199435 31720157 := bstep (se 3 (by rfl) ⟨5947529, by rfl⟩ : syracuseStep 31720157 = 11895059) B11895059
theorem B21146771 : Blo 2199435 21146771 := bstep (se 1 (by rfl) ⟨15860078, by rfl⟩ : syracuseStep 21146771 = 31720157) B31720157
theorem B14097847 : Blo 2199435 14097847 := bstep (se 1 (by rfl) ⟨10573385, by rfl⟩ : syracuseStep 14097847 = 21146771) B21146771
theorem B18797129 : Blo 2199435 18797129 := bstep (se 2 (by rfl) ⟨7048923, by rfl⟩ : syracuseStep 18797129 = 14097847) B14097847
theorem B12531419 : Blo 2199435 12531419 := bstep (se 1 (by rfl) ⟨9398564, by rfl⟩ : syracuseStep 12531419 = 18797129) B18797129
theorem B8354279 : Blo 2199435 8354279 := bstep (se 1 (by rfl) ⟨6265709, by rfl⟩ : syracuseStep 8354279 = 12531419) B12531419
theorem B5569519 : Blo 2199435 5569519 := bstep (se 1 (by rfl) ⟨4177139, by rfl⟩ : syracuseStep 5569519 = 8354279) B8354279
theorem B7426025 : Blo 2199435 7426025 := bstep (se 2 (by rfl) ⟨2784759, by rfl⟩ : syracuseStep 7426025 = 5569519) B5569519
theorem B4950683 : Blo 2199435 4950683 := bstep (se 1 (by rfl) ⟨3713012, by rfl⟩ : syracuseStep 4950683 = 7426025) B7426025
theorem B3300455 : Blo 2199435 3300455 := bstep (se 1 (by rfl) ⟨2475341, by rfl⟩ : syracuseStep 3300455 = 4950683) B4950683
theorem B2200303 : Blo 2199435 2200303 := bstep (se 1 (by rfl) ⟨1650227, by rfl⟩ : syracuseStep 2200303 = 3300455) B3300455
theorem B3300461 : Blo 2199435 3300461 := bbase (se 3 (by rfl) ⟨618836, by rfl⟩ : syracuseStep 3300461 = 1237673) (by norm_num)
theorem B2200307 : Blo 2199435 2200307 := bstep (se 1 (by rfl) ⟨1650230, by rfl⟩ : syracuseStep 2200307 = 3300461) B3300461
theorem B4950701 : Blo 2199435 4950701 := bbase (se 3 (by rfl) ⟨928256, by rfl⟩ : syracuseStep 4950701 = 1856513) (by norm_num)
theorem B3300467 : Blo 2199435 3300467 := bstep (se 1 (by rfl) ⟨2475350, by rfl⟩ : syracuseStep 3300467 = 4950701) B4950701
theorem B2200311 : Blo 2199435 2200311 := bstep (se 1 (by rfl) ⟨1650233, by rfl⟩ : syracuseStep 2200311 = 3300467) B3300467
theorem B4699309 : Blo 2199435 4699309 := bbase (se 3 (by rfl) ⟨881120, by rfl⟩ : syracuseStep 4699309 = 1762241) (by norm_num)
theorem B6265745 : Blo 2199435 6265745 := bstep (se 2 (by rfl) ⟨2349654, by rfl⟩ : syracuseStep 6265745 = 4699309) B4699309
theorem B4177163 : Blo 2199435 4177163 := bstep (se 1 (by rfl) ⟨3132872, by rfl⟩ : syracuseStep 4177163 = 6265745) B6265745
theorem B2784775 : Blo 2199435 2784775 := bstep (se 1 (by rfl) ⟨2088581, by rfl⟩ : syracuseStep 2784775 = 4177163) B4177163
theorem B3713033 : Blo 2199435 3713033 := bstep (se 2 (by rfl) ⟨1392387, by rfl⟩ : syracuseStep 3713033 = 2784775) B2784775
theorem B2475355 : Blo 2199435 2475355 := bstep (se 1 (by rfl) ⟨1856516, by rfl⟩ : syracuseStep 2475355 = 3713033) B3713033
theorem B3300473 : Blo 2199435 3300473 := bstep (se 2 (by rfl) ⟨1237677, by rfl⟩ : syracuseStep 3300473 = 2475355) B2475355
theorem B2200315 : Blo 2199435 2200315 := bstep (se 1 (by rfl) ⟨1650236, by rfl⟩ : syracuseStep 2200315 = 3300473) B3300473
theorem B7527397 : Blo 2199435 7527397 := bbase (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) (by norm_num)
theorem B10036529 : Blo 2199435 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B6691019 : Blo 2199435 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B17842717 : Blo 2199435 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B23790289 : Blo 2199435 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B31720385 : Blo 2199435 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B21146923 : Blo 2199435 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B28195897 : Blo 2199435 28195897 := bstep (se 2 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 28195897 = 21146923) B21146923
theorem B37594529 : Blo 2199435 37594529 := bstep (se 2 (by rfl) ⟨14097948, by rfl⟩ : syracuseStep 37594529 = 28195897) B28195897
theorem B25063019 : Blo 2199435 25063019 := bstep (se 1 (by rfl) ⟨18797264, by rfl⟩ : syracuseStep 25063019 = 37594529) B37594529
theorem B16708679 : Blo 2199435 16708679 := bstep (se 1 (by rfl) ⟨12531509, by rfl⟩ : syracuseStep 16708679 = 25063019) B25063019
theorem B11139119 : Blo 2199435 11139119 := bstep (se 1 (by rfl) ⟨8354339, by rfl⟩ : syracuseStep 11139119 = 16708679) B16708679
theorem B7426079 : Blo 2199435 7426079 := bstep (se 1 (by rfl) ⟨5569559, by rfl⟩ : syracuseStep 7426079 = 11139119) B11139119
theorem B4950719 : Blo 2199435 4950719 := bstep (se 1 (by rfl) ⟨3713039, by rfl⟩ : syracuseStep 4950719 = 7426079) B7426079
theorem B3300479 : Blo 2199435 3300479 := bstep (se 1 (by rfl) ⟨2475359, by rfl⟩ : syracuseStep 3300479 = 4950719) B4950719
theorem B2200319 : Blo 2199435 2200319 := bstep (se 1 (by rfl) ⟨1650239, by rfl⟩ : syracuseStep 2200319 = 3300479) B3300479
theorem B3300485 : Blo 2199435 3300485 := bbase (se 4 (by rfl) ⟨309420, by rfl⟩ : syracuseStep 3300485 = 618841) (by norm_num)
theorem B2200323 : Blo 2199435 2200323 := bstep (se 1 (by rfl) ⟨1650242, by rfl⟩ : syracuseStep 2200323 = 3300485) B3300485
theorem B3713053 : Blo 2199435 3713053 := bbase (se 3 (by rfl) ⟨696197, by rfl⟩ : syracuseStep 3713053 = 1392395) (by norm_num)
theorem B4950737 : Blo 2199435 4950737 := bstep (se 2 (by rfl) ⟨1856526, by rfl⟩ : syracuseStep 4950737 = 3713053) B3713053
theorem B3300491 : Blo 2199435 3300491 := bstep (se 1 (by rfl) ⟨2475368, by rfl⟩ : syracuseStep 3300491 = 4950737) B4950737
theorem B2200327 : Blo 2199435 2200327 := bstep (se 1 (by rfl) ⟨1650245, by rfl⟩ : syracuseStep 2200327 = 3300491) B3300491
theorem B2475373 : Blo 2199435 2475373 := bbase (se 3 (by rfl) ⟨464132, by rfl⟩ : syracuseStep 2475373 = 928265) (by norm_num)
theorem B3300497 : Blo 2199435 3300497 := bstep (se 2 (by rfl) ⟨1237686, by rfl⟩ : syracuseStep 3300497 = 2475373) B2475373
theorem B2200331 : Blo 2199435 2200331 := bstep (se 1 (by rfl) ⟨1650248, by rfl⟩ : syracuseStep 2200331 = 3300497) B3300497
theorem B7426133 : Blo 2199435 7426133 := bbase (se 8 (by rfl) ⟨43512, by rfl⟩ : syracuseStep 7426133 = 87025) (by norm_num)
theorem B4950755 : Blo 2199435 4950755 := bstep (se 1 (by rfl) ⟨3713066, by rfl⟩ : syracuseStep 4950755 = 7426133) B7426133
theorem B3300503 : Blo 2199435 3300503 := bstep (se 1 (by rfl) ⟨2475377, by rfl⟩ : syracuseStep 3300503 = 4950755) B4950755
theorem B2200335 : Blo 2199435 2200335 := bstep (se 1 (by rfl) ⟨1650251, by rfl⟩ : syracuseStep 2200335 = 3300503) B3300503
theorem B3300509 : Blo 2199435 3300509 := bbase (se 3 (by rfl) ⟨618845, by rfl⟩ : syracuseStep 3300509 = 1237691) (by norm_num)
theorem B2200339 : Blo 2199435 2200339 := bstep (se 1 (by rfl) ⟨1650254, by rfl⟩ : syracuseStep 2200339 = 3300509) B3300509
theorem B4950773 : Blo 2199435 4950773 := bbase (se 5 (by rfl) ⟨232067, by rfl⟩ : syracuseStep 4950773 = 464135) (by norm_num)
theorem B3300515 : Blo 2199435 3300515 := bstep (se 1 (by rfl) ⟨2475386, by rfl⟩ : syracuseStep 3300515 = 4950773) B4950773
theorem B2200343 : Blo 2199435 2200343 := bstep (se 1 (by rfl) ⟨1650257, by rfl⟩ : syracuseStep 2200343 = 3300515) B3300515
theorem B2509165 : Blo 2199435 2509165 := bbase (se 3 (by rfl) ⟨470468, by rfl⟩ : syracuseStep 2509165 = 940937) (by norm_num)
theorem B3345553 : Blo 2199435 3345553 := bstep (se 2 (by rfl) ⟨1254582, by rfl⟩ : syracuseStep 3345553 = 2509165) B2509165
theorem B17842949 : Blo 2199435 17842949 := bstep (se 4 (by rfl) ⟨1672776, by rfl⟩ : syracuseStep 17842949 = 3345553) B3345553
theorem B11895299 : Blo 2199435 11895299 := bstep (se 1 (by rfl) ⟨8921474, by rfl⟩ : syracuseStep 11895299 = 17842949) B17842949
theorem B7930199 : Blo 2199435 7930199 := bstep (se 1 (by rfl) ⟨5947649, by rfl⟩ : syracuseStep 7930199 = 11895299) B11895299
theorem B5286799 : Blo 2199435 5286799 := bstep (se 1 (by rfl) ⟨3965099, by rfl⟩ : syracuseStep 5286799 = 7930199) B7930199
theorem B28196261 : Blo 2199435 28196261 := bstep (se 4 (by rfl) ⟨2643399, by rfl⟩ : syracuseStep 28196261 = 5286799) B5286799
theorem B18797507 : Blo 2199435 18797507 := bstep (se 1 (by rfl) ⟨14098130, by rfl⟩ : syracuseStep 18797507 = 28196261) B28196261
theorem B12531671 : Blo 2199435 12531671 := bstep (se 1 (by rfl) ⟨9398753, by rfl⟩ : syracuseStep 12531671 = 18797507) B18797507
theorem B8354447 : Blo 2199435 8354447 := bstep (se 1 (by rfl) ⟨6265835, by rfl⟩ : syracuseStep 8354447 = 12531671) B12531671
theorem B5569631 : Blo 2199435 5569631 := bstep (se 1 (by rfl) ⟨4177223, by rfl⟩ : syracuseStep 5569631 = 8354447) B8354447
theorem B3713087 : Blo 2199435 3713087 := bstep (se 1 (by rfl) ⟨2784815, by rfl⟩ : syracuseStep 3713087 = 5569631) B5569631
theorem B2475391 : Blo 2199435 2475391 := bstep (se 1 (by rfl) ⟨1856543, by rfl⟩ : syracuseStep 2475391 = 3713087) B3713087
theorem B3300521 : Blo 2199435 3300521 := bstep (se 2 (by rfl) ⟨1237695, by rfl⟩ : syracuseStep 3300521 = 2475391) B2475391
theorem B2200347 : Blo 2199435 2200347 := bstep (se 1 (by rfl) ⟨1650260, by rfl⟩ : syracuseStep 2200347 = 3300521) B3300521
theorem B2230373 : Blo 2199435 2230373 := bbase (se 4 (by rfl) ⟨209097, by rfl⟩ : syracuseStep 2230373 = 418195) (by norm_num)
theorem B5947661 : Blo 2199435 5947661 := bstep (se 3 (by rfl) ⟨1115186, by rfl⟩ : syracuseStep 5947661 = 2230373) B2230373
theorem B3965107 : Blo 2199435 3965107 := bstep (se 1 (by rfl) ⟨2973830, by rfl⟩ : syracuseStep 3965107 = 5947661) B5947661
theorem B5286809 : Blo 2199435 5286809 := bstep (se 2 (by rfl) ⟨1982553, by rfl⟩ : syracuseStep 5286809 = 3965107) B3965107
theorem B3524539 : Blo 2199435 3524539 := bstep (se 1 (by rfl) ⟨2643404, by rfl⟩ : syracuseStep 3524539 = 5286809) B5286809
theorem B4699385 : Blo 2199435 4699385 := bstep (se 2 (by rfl) ⟨1762269, by rfl⟩ : syracuseStep 4699385 = 3524539) B3524539
theorem B3132923 : Blo 2199435 3132923 := bstep (se 1 (by rfl) ⟨2349692, by rfl⟩ : syracuseStep 3132923 = 4699385) B4699385
theorem B8354461 : Blo 2199435 8354461 := bstep (se 3 (by rfl) ⟨1566461, by rfl⟩ : syracuseStep 8354461 = 3132923) B3132923
theorem B11139281 : Blo 2199435 11139281 := bstep (se 2 (by rfl) ⟨4177230, by rfl⟩ : syracuseStep 11139281 = 8354461) B8354461
theorem B7426187 : Blo 2199435 7426187 := bstep (se 1 (by rfl) ⟨5569640, by rfl⟩ : syracuseStep 7426187 = 11139281) B11139281
theorem B4950791 : Blo 2199435 4950791 := bstep (se 1 (by rfl) ⟨3713093, by rfl⟩ : syracuseStep 4950791 = 7426187) B7426187
theorem B3300527 : Blo 2199435 3300527 := bstep (se 1 (by rfl) ⟨2475395, by rfl⟩ : syracuseStep 3300527 = 4950791) B4950791
theorem B2200351 : Blo 2199435 2200351 := bstep (se 1 (by rfl) ⟨1650263, by rfl⟩ : syracuseStep 2200351 = 3300527) B3300527
theorem B3300533 : Blo 2199435 3300533 := bbase (se 5 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 3300533 = 309425) (by norm_num)
theorem B2200355 : Blo 2199435 2200355 := bstep (se 1 (by rfl) ⟨1650266, by rfl⟩ : syracuseStep 2200355 = 3300533) B3300533
theorem B5569661 : Blo 2199435 5569661 := bbase (se 3 (by rfl) ⟨1044311, by rfl⟩ : syracuseStep 5569661 = 2088623) (by norm_num)
theorem B3713107 : Blo 2199435 3713107 := bstep (se 1 (by rfl) ⟨2784830, by rfl⟩ : syracuseStep 3713107 = 5569661) B5569661
theorem B4950809 : Blo 2199435 4950809 := bstep (se 2 (by rfl) ⟨1856553, by rfl⟩ : syracuseStep 4950809 = 3713107) B3713107
theorem B3300539 : Blo 2199435 3300539 := bstep (se 1 (by rfl) ⟨2475404, by rfl⟩ : syracuseStep 3300539 = 4950809) B4950809
theorem B2200359 : Blo 2199435 2200359 := bstep (se 1 (by rfl) ⟨1650269, by rfl⟩ : syracuseStep 2200359 = 3300539) B3300539
theorem B2475409 : Blo 2199435 2475409 := bbase (se 2 (by rfl) ⟨928278, by rfl⟩ : syracuseStep 2475409 = 1856557) (by norm_num)
theorem B3300545 : Blo 2199435 3300545 := bstep (se 2 (by rfl) ⟨1237704, by rfl⟩ : syracuseStep 3300545 = 2475409) B2475409
theorem B2200363 : Blo 2199435 2200363 := bstep (se 1 (by rfl) ⟨1650272, by rfl⟩ : syracuseStep 2200363 = 3300545) B3300545
theorem B4177261 : Blo 2199435 4177261 := bbase (se 3 (by rfl) ⟨783236, by rfl⟩ : syracuseStep 4177261 = 1566473) (by norm_num)
theorem B5569681 : Blo 2199435 5569681 := bstep (se 2 (by rfl) ⟨2088630, by rfl⟩ : syracuseStep 5569681 = 4177261) B4177261
theorem B7426241 : Blo 2199435 7426241 := bstep (se 2 (by rfl) ⟨2784840, by rfl⟩ : syracuseStep 7426241 = 5569681) B5569681
theorem B4950827 : Blo 2199435 4950827 := bstep (se 1 (by rfl) ⟨3713120, by rfl⟩ : syracuseStep 4950827 = 7426241) B7426241
theorem B3300551 : Blo 2199435 3300551 := bstep (se 1 (by rfl) ⟨2475413, by rfl⟩ : syracuseStep 3300551 = 4950827) B4950827
theorem B2200367 : Blo 2199435 2200367 := bstep (se 1 (by rfl) ⟨1650275, by rfl⟩ : syracuseStep 2200367 = 3300551) B3300551
theorem B3300557 : Blo 2199435 3300557 := bbase (se 3 (by rfl) ⟨618854, by rfl⟩ : syracuseStep 3300557 = 1237709) (by norm_num)
theorem B2200371 : Blo 2199435 2200371 := bstep (se 1 (by rfl) ⟨1650278, by rfl⟩ : syracuseStep 2200371 = 3300557) B3300557
theorem B4950845 : Blo 2199435 4950845 := bbase (se 3 (by rfl) ⟨928283, by rfl⟩ : syracuseStep 4950845 = 1856567) (by norm_num)
theorem B3300563 : Blo 2199435 3300563 := bstep (se 1 (by rfl) ⟨2475422, by rfl⟩ : syracuseStep 3300563 = 4950845) B4950845
theorem B2200375 : Blo 2199435 2200375 := bstep (se 1 (by rfl) ⟨1650281, by rfl⟩ : syracuseStep 2200375 = 3300563) B3300563
theorem B3713141 : Blo 2199435 3713141 := bbase (se 5 (by rfl) ⟨174053, by rfl⟩ : syracuseStep 3713141 = 348107) (by norm_num)
theorem B2475427 : Blo 2199435 2475427 := bstep (se 1 (by rfl) ⟨1856570, by rfl⟩ : syracuseStep 2475427 = 3713141) B3713141
theorem B3300569 : Blo 2199435 3300569 := bstep (se 2 (by rfl) ⟨1237713, by rfl⟩ : syracuseStep 3300569 = 2475427) B2475427
theorem B2200379 : Blo 2199435 2200379 := bstep (se 1 (by rfl) ⟨1650284, by rfl⟩ : syracuseStep 2200379 = 3300569) B3300569
theorem B4699453 : Blo 2199435 4699453 := bbase (se 3 (by rfl) ⟨881147, by rfl⟩ : syracuseStep 4699453 = 1762295) (by norm_num)
theorem B6265937 : Blo 2199435 6265937 := bstep (se 2 (by rfl) ⟨2349726, by rfl⟩ : syracuseStep 6265937 = 4699453) B4699453
theorem B16709165 : Blo 2199435 16709165 := bstep (se 3 (by rfl) ⟨3132968, by rfl⟩ : syracuseStep 16709165 = 6265937) B6265937
theorem B11139443 : Blo 2199435 11139443 := bstep (se 1 (by rfl) ⟨8354582, by rfl⟩ : syracuseStep 11139443 = 16709165) B16709165
theorem B7426295 : Blo 2199435 7426295 := bstep (se 1 (by rfl) ⟨5569721, by rfl⟩ : syracuseStep 7426295 = 11139443) B11139443
theorem B4950863 : Blo 2199435 4950863 := bstep (se 1 (by rfl) ⟨3713147, by rfl⟩ : syracuseStep 4950863 = 7426295) B7426295
theorem B3300575 : Blo 2199435 3300575 := bstep (se 1 (by rfl) ⟨2475431, by rfl⟩ : syracuseStep 3300575 = 4950863) B4950863
theorem B2200383 : Blo 2199435 2200383 := bstep (se 1 (by rfl) ⟨1650287, by rfl⟩ : syracuseStep 2200383 = 3300575) B3300575
theorem B3300581 : Blo 2199435 3300581 := bbase (se 4 (by rfl) ⟨309429, by rfl⟩ : syracuseStep 3300581 = 618859) (by norm_num)
theorem B2200387 : Blo 2199435 2200387 := bstep (se 1 (by rfl) ⟨1650290, by rfl⟩ : syracuseStep 2200387 = 3300581) B3300581
theorem B5086901 : Blo 2199435 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B13565069 : Blo 2199435 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B9043379 : Blo 2199435 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B6028919 : Blo 2199435 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B4019279 : Blo 2199435 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B10718077 : Blo 2199435 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B14290769 : Blo 2199435 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B38108717 : Blo 2199435 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B25405811 : Blo 2199435 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B16937207 : Blo 2199435 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B11291471 : Blo 2199435 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B7527647 : Blo 2199435 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B5018431 : Blo 2199435 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B6691241 : Blo 2199435 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B4460827 : Blo 2199435 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B5947769 : Blo 2199435 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B15860717 : Blo 2199435 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B10573811 : Blo 2199435 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B7049207 : Blo 2199435 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B4699471 : Blo 2199435 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B6265961 : Blo 2199435 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B4177307 : Blo 2199435 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B2784871 : Blo 2199435 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B3713161 : Blo 2199435 3713161 := bstep (se 2 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 3713161 = 2784871) B2784871
theorem B4950881 : Blo 2199435 4950881 := bstep (se 2 (by rfl) ⟨1856580, by rfl⟩ : syracuseStep 4950881 = 3713161) B3713161
theorem B3300587 : Blo 2199435 3300587 := bstep (se 1 (by rfl) ⟨2475440, by rfl⟩ : syracuseStep 3300587 = 4950881) B4950881
theorem B2200391 : Blo 2199435 2200391 := bstep (se 1 (by rfl) ⟨1650293, by rfl⟩ : syracuseStep 2200391 = 3300587) B3300587
theorem B2475445 : Blo 2199435 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B3300593 : Blo 2199435 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B2200395 : Blo 2199435 2200395 := bstep (se 1 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 2200395 = 3300593) B3300593
theorem B2784881 : Blo 2199435 2784881 := bbase (se 2 (by rfl) ⟨1044330, by rfl⟩ : syracuseStep 2784881 = 2088661) (by norm_num)
theorem B7426349 : Blo 2199435 7426349 := bstep (se 3 (by rfl) ⟨1392440, by rfl⟩ : syracuseStep 7426349 = 2784881) B2784881
theorem B4950899 : Blo 2199435 4950899 := bstep (se 1 (by rfl) ⟨3713174, by rfl⟩ : syracuseStep 4950899 = 7426349) B7426349
theorem B3300599 : Blo 2199435 3300599 := bstep (se 1 (by rfl) ⟨2475449, by rfl⟩ : syracuseStep 3300599 = 4950899) B4950899
theorem B2200399 : Blo 2199435 2200399 := bstep (se 1 (by rfl) ⟨1650299, by rfl⟩ : syracuseStep 2200399 = 3300599) B3300599
theorem B3300605 : Blo 2199435 3300605 := bbase (se 3 (by rfl) ⟨618863, by rfl⟩ : syracuseStep 3300605 = 1237727) (by norm_num)
theorem B2200403 : Blo 2199435 2200403 := bstep (se 1 (by rfl) ⟨1650302, by rfl⟩ : syracuseStep 2200403 = 3300605) B3300605
theorem B4950917 : Blo 2199435 4950917 := bbase (se 4 (by rfl) ⟨464148, by rfl⟩ : syracuseStep 4950917 = 928297) (by norm_num)
theorem B3300611 : Blo 2199435 3300611 := bstep (se 1 (by rfl) ⟨2475458, by rfl⟩ : syracuseStep 3300611 = 4950917) B4950917
theorem B2200407 : Blo 2199435 2200407 := bstep (se 1 (by rfl) ⟨1650305, by rfl⟩ : syracuseStep 2200407 = 3300611) B3300611
theorem B2349757 : Blo 2199435 2349757 := bbase (se 3 (by rfl) ⟨440579, by rfl⟩ : syracuseStep 2349757 = 881159) (by norm_num)
theorem B3133009 : Blo 2199435 3133009 := bstep (se 2 (by rfl) ⟨1174878, by rfl⟩ : syracuseStep 3133009 = 2349757) B2349757
theorem B4177345 : Blo 2199435 4177345 := bstep (se 2 (by rfl) ⟨1566504, by rfl⟩ : syracuseStep 4177345 = 3133009) B3133009
theorem B5569793 : Blo 2199435 5569793 := bstep (se 2 (by rfl) ⟨2088672, by rfl⟩ : syracuseStep 5569793 = 4177345) B4177345
theorem B3713195 : Blo 2199435 3713195 := bstep (se 1 (by rfl) ⟨2784896, by rfl⟩ : syracuseStep 3713195 = 5569793) B5569793
theorem B2475463 : Blo 2199435 2475463 := bstep (se 1 (by rfl) ⟨1856597, by rfl⟩ : syracuseStep 2475463 = 3713195) B3713195
theorem B3300617 : Blo 2199435 3300617 := bstep (se 2 (by rfl) ⟨1237731, by rfl⟩ : syracuseStep 3300617 = 2475463) B2475463
theorem B2200411 : Blo 2199435 2200411 := bstep (se 1 (by rfl) ⟨1650308, by rfl⟩ : syracuseStep 2200411 = 3300617) B3300617
theorem B11139605 : Blo 2199435 11139605 := bbase (se 6 (by rfl) ⟨261084, by rfl⟩ : syracuseStep 11139605 = 522169) (by norm_num)
theorem B7426403 : Blo 2199435 7426403 := bstep (se 1 (by rfl) ⟨5569802, by rfl⟩ : syracuseStep 7426403 = 11139605) B11139605
theorem B4950935 : Blo 2199435 4950935 := bstep (se 1 (by rfl) ⟨3713201, by rfl⟩ : syracuseStep 4950935 = 7426403) B7426403
theorem B3300623 : Blo 2199435 3300623 := bstep (se 1 (by rfl) ⟨2475467, by rfl⟩ : syracuseStep 3300623 = 4950935) B4950935
theorem B2200415 : Blo 2199435 2200415 := bstep (se 1 (by rfl) ⟨1650311, by rfl⟩ : syracuseStep 2200415 = 3300623) B3300623
theorem B3300629 : Blo 2199435 3300629 := bbase (se 6 (by rfl) ⟨77358, by rfl⟩ : syracuseStep 3300629 = 154717) (by norm_num)
theorem B2200419 : Blo 2199435 2200419 := bstep (se 1 (by rfl) ⟨1650314, by rfl⟩ : syracuseStep 2200419 = 3300629) B3300629
theorem B21147925 : Blo 2199435 21147925 := bbase (se 6 (by rfl) ⟨495654, by rfl⟩ : syracuseStep 21147925 = 991309) (by norm_num)
theorem B28197233 : Blo 2199435 28197233 := bstep (se 2 (by rfl) ⟨10573962, by rfl⟩ : syracuseStep 28197233 = 21147925) B21147925
theorem B18798155 : Blo 2199435 18798155 := bstep (se 1 (by rfl) ⟨14098616, by rfl⟩ : syracuseStep 18798155 = 28197233) B28197233
theorem B12532103 : Blo 2199435 12532103 := bstep (se 1 (by rfl) ⟨9399077, by rfl⟩ : syracuseStep 12532103 = 18798155) B18798155
theorem B8354735 : Blo 2199435 8354735 := bstep (se 1 (by rfl) ⟨6266051, by rfl⟩ : syracuseStep 8354735 = 12532103) B12532103
theorem B5569823 : Blo 2199435 5569823 := bstep (se 1 (by rfl) ⟨4177367, by rfl⟩ : syracuseStep 5569823 = 8354735) B8354735
theorem B3713215 : Blo 2199435 3713215 := bstep (se 1 (by rfl) ⟨2784911, by rfl⟩ : syracuseStep 3713215 = 5569823) B5569823
theorem B4950953 : Blo 2199435 4950953 := bstep (se 2 (by rfl) ⟨1856607, by rfl⟩ : syracuseStep 4950953 = 3713215) B3713215
theorem B3300635 : Blo 2199435 3300635 := bstep (se 1 (by rfl) ⟨2475476, by rfl⟩ : syracuseStep 3300635 = 4950953) B4950953
theorem B2200423 : Blo 2199435 2200423 := bstep (se 1 (by rfl) ⟨1650317, by rfl⟩ : syracuseStep 2200423 = 3300635) B3300635
theorem B2475481 : Blo 2199435 2475481 := bbase (se 2 (by rfl) ⟨928305, by rfl⟩ : syracuseStep 2475481 = 1856611) (by norm_num)
theorem B3300641 : Blo 2199435 3300641 := bstep (se 2 (by rfl) ⟨1237740, by rfl⟩ : syracuseStep 3300641 = 2475481) B2475481
theorem B2200427 : Blo 2199435 2200427 := bstep (se 1 (by rfl) ⟨1650320, by rfl⟩ : syracuseStep 2200427 = 3300641) B3300641
theorem B3133037 : Blo 2199435 3133037 := bbase (se 3 (by rfl) ⟨587444, by rfl⟩ : syracuseStep 3133037 = 1174889) (by norm_num)
theorem B8354765 : Blo 2199435 8354765 := bstep (se 3 (by rfl) ⟨1566518, by rfl⟩ : syracuseStep 8354765 = 3133037) B3133037
theorem B5569843 : Blo 2199435 5569843 := bstep (se 1 (by rfl) ⟨4177382, by rfl⟩ : syracuseStep 5569843 = 8354765) B8354765
theorem B7426457 : Blo 2199435 7426457 := bstep (se 2 (by rfl) ⟨2784921, by rfl⟩ : syracuseStep 7426457 = 5569843) B5569843
theorem B4950971 : Blo 2199435 4950971 := bstep (se 1 (by rfl) ⟨3713228, by rfl⟩ : syracuseStep 4950971 = 7426457) B7426457
theorem B3300647 : Blo 2199435 3300647 := bstep (se 1 (by rfl) ⟨2475485, by rfl⟩ : syracuseStep 3300647 = 4950971) B4950971
theorem B2200431 : Blo 2199435 2200431 := bstep (se 1 (by rfl) ⟨1650323, by rfl⟩ : syracuseStep 2200431 = 3300647) B3300647
theorem B3300653 : Blo 2199435 3300653 := bbase (se 3 (by rfl) ⟨618872, by rfl⟩ : syracuseStep 3300653 = 1237745) (by norm_num)
theorem B2200435 : Blo 2199435 2200435 := bstep (se 1 (by rfl) ⟨1650326, by rfl⟩ : syracuseStep 2200435 = 3300653) B3300653
theorem B4950989 : Blo 2199435 4950989 := bbase (se 3 (by rfl) ⟨928310, by rfl⟩ : syracuseStep 4950989 = 1856621) (by norm_num)
theorem B3300659 : Blo 2199435 3300659 := bstep (se 1 (by rfl) ⟨2475494, by rfl⟩ : syracuseStep 3300659 = 4950989) B4950989
theorem B2200439 : Blo 2199435 2200439 := bstep (se 1 (by rfl) ⟨1650329, by rfl⟩ : syracuseStep 2200439 = 3300659) B3300659
theorem B2784937 : Blo 2199435 2784937 := bbase (se 2 (by rfl) ⟨1044351, by rfl⟩ : syracuseStep 2784937 = 2088703) (by norm_num)
theorem B3713249 : Blo 2199435 3713249 := bstep (se 2 (by rfl) ⟨1392468, by rfl⟩ : syracuseStep 3713249 = 2784937) B2784937
theorem B2475499 : Blo 2199435 2475499 := bstep (se 1 (by rfl) ⟨1856624, by rfl⟩ : syracuseStep 2475499 = 3713249) B3713249
theorem B3300665 : Blo 2199435 3300665 := bstep (se 2 (by rfl) ⟨1237749, by rfl⟩ : syracuseStep 3300665 = 2475499) B2475499
theorem B2200443 : Blo 2199435 2200443 := bstep (se 1 (by rfl) ⟨1650332, by rfl⟩ : syracuseStep 2200443 = 3300665) B3300665
theorem B20074229 : Blo 2199435 20074229 := bbase (se 5 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 20074229 = 1881959) (by norm_num)
theorem B13382819 : Blo 2199435 13382819 := bstep (se 1 (by rfl) ⟨10037114, by rfl⟩ : syracuseStep 13382819 = 20074229) B20074229
theorem B8921879 : Blo 2199435 8921879 := bstep (se 1 (by rfl) ⟨6691409, by rfl⟩ : syracuseStep 8921879 = 13382819) B13382819
theorem B5947919 : Blo 2199435 5947919 := bstep (se 1 (by rfl) ⟨4460939, by rfl⟩ : syracuseStep 5947919 = 8921879) B8921879
theorem B3965279 : Blo 2199435 3965279 := bstep (se 1 (by rfl) ⟨2973959, by rfl⟩ : syracuseStep 3965279 = 5947919) B5947919
theorem B10574077 : Blo 2199435 10574077 := bstep (se 3 (by rfl) ⟨1982639, by rfl⟩ : syracuseStep 10574077 = 3965279) B3965279
theorem B14098769 : Blo 2199435 14098769 := bstep (se 2 (by rfl) ⟨5287038, by rfl⟩ : syracuseStep 14098769 = 10574077) B10574077
theorem B9399179 : Blo 2199435 9399179 := bstep (se 1 (by rfl) ⟨7049384, by rfl⟩ : syracuseStep 9399179 = 14098769) B14098769
theorem B25064477 : Blo 2199435 25064477 := bstep (se 3 (by rfl) ⟨4699589, by rfl⟩ : syracuseStep 25064477 = 9399179) B9399179
theorem B16709651 : Blo 2199435 16709651 := bstep (se 1 (by rfl) ⟨12532238, by rfl⟩ : syracuseStep 16709651 = 25064477) B25064477
theorem B11139767 : Blo 2199435 11139767 := bstep (se 1 (by rfl) ⟨8354825, by rfl⟩ : syracuseStep 11139767 = 16709651) B16709651
theorem B7426511 : Blo 2199435 7426511 := bstep (se 1 (by rfl) ⟨5569883, by rfl⟩ : syracuseStep 7426511 = 11139767) B11139767
theorem B4951007 : Blo 2199435 4951007 := bstep (se 1 (by rfl) ⟨3713255, by rfl⟩ : syracuseStep 4951007 = 7426511) B7426511
theorem B3300671 : Blo 2199435 3300671 := bstep (se 1 (by rfl) ⟨2475503, by rfl⟩ : syracuseStep 3300671 = 4951007) B4951007
theorem B2200447 : Blo 2199435 2200447 := bstep (se 1 (by rfl) ⟨1650335, by rfl⟩ : syracuseStep 2200447 = 3300671) B3300671
theorem B3300677 : Blo 2199435 3300677 := bbase (se 4 (by rfl) ⟨309438, by rfl⟩ : syracuseStep 3300677 = 618877) (by norm_num)
theorem B2200451 : Blo 2199435 2200451 := bstep (se 1 (by rfl) ⟨1650338, by rfl⟩ : syracuseStep 2200451 = 3300677) B3300677
theorem B3713269 : Blo 2199435 3713269 := bbase (se 5 (by rfl) ⟨174059, by rfl⟩ : syracuseStep 3713269 = 348119) (by norm_num)
theorem B4951025 : Blo 2199435 4951025 := bstep (se 2 (by rfl) ⟨1856634, by rfl⟩ : syracuseStep 4951025 = 3713269) B3713269
theorem B3300683 : Blo 2199435 3300683 := bstep (se 1 (by rfl) ⟨2475512, by rfl⟩ : syracuseStep 3300683 = 4951025) B4951025
theorem B2200455 : Blo 2199435 2200455 := bstep (se 1 (by rfl) ⟨1650341, by rfl⟩ : syracuseStep 2200455 = 3300683) B3300683
theorem B2475517 : Blo 2199435 2475517 := bbase (se 3 (by rfl) ⟨464159, by rfl⟩ : syracuseStep 2475517 = 928319) (by norm_num)
theorem B3300689 : Blo 2199435 3300689 := bstep (se 2 (by rfl) ⟨1237758, by rfl⟩ : syracuseStep 3300689 = 2475517) B2475517
theorem B2200459 : Blo 2199435 2200459 := bstep (se 1 (by rfl) ⟨1650344, by rfl⟩ : syracuseStep 2200459 = 3300689) B3300689
theorem B7426565 : Blo 2199435 7426565 := bbase (se 4 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 7426565 = 1392481) (by norm_num)
theorem B4951043 : Blo 2199435 4951043 := bstep (se 1 (by rfl) ⟨3713282, by rfl⟩ : syracuseStep 4951043 = 7426565) B7426565
theorem B3300695 : Blo 2199435 3300695 := bstep (se 1 (by rfl) ⟨2475521, by rfl⟩ : syracuseStep 3300695 = 4951043) B4951043
theorem B2200463 : Blo 2199435 2200463 := bstep (se 1 (by rfl) ⟨1650347, by rfl⟩ : syracuseStep 2200463 = 3300695) B3300695
theorem B3300701 : Blo 2199435 3300701 := bbase (se 3 (by rfl) ⟨618881, by rfl⟩ : syracuseStep 3300701 = 1237763) (by norm_num)
theorem B2200467 : Blo 2199435 2200467 := bstep (se 1 (by rfl) ⟨1650350, by rfl⟩ : syracuseStep 2200467 = 3300701) B3300701
theorem B4951061 : Blo 2199435 4951061 := bbase (se 6 (by rfl) ⟨116040, by rfl⟩ : syracuseStep 4951061 = 232081) (by norm_num)
theorem B3300707 : Blo 2199435 3300707 := bstep (se 1 (by rfl) ⟨2475530, by rfl⟩ : syracuseStep 3300707 = 4951061) B4951061
theorem B2200471 : Blo 2199435 2200471 := bstep (se 1 (by rfl) ⟨1650353, by rfl⟩ : syracuseStep 2200471 = 3300707) B3300707
theorem B8354933 : Blo 2199435 8354933 := bbase (se 5 (by rfl) ⟨391637, by rfl⟩ : syracuseStep 8354933 = 783275) (by norm_num)
theorem B5569955 : Blo 2199435 5569955 := bstep (se 1 (by rfl) ⟨4177466, by rfl⟩ : syracuseStep 5569955 = 8354933) B8354933
theorem B3713303 : Blo 2199435 3713303 := bstep (se 1 (by rfl) ⟨2784977, by rfl⟩ : syracuseStep 3713303 = 5569955) B5569955
theorem B2475535 : Blo 2199435 2475535 := bstep (se 1 (by rfl) ⟨1856651, by rfl⟩ : syracuseStep 2475535 = 3713303) B3713303
theorem B3300713 : Blo 2199435 3300713 := bstep (se 2 (by rfl) ⟨1237767, by rfl⟩ : syracuseStep 3300713 = 2475535) B2475535
theorem B2200475 : Blo 2199435 2200475 := bstep (se 1 (by rfl) ⟨1650356, by rfl⟩ : syracuseStep 2200475 = 3300713) B3300713
theorem B2349829 : Blo 2199435 2349829 := bbase (se 4 (by rfl) ⟨220296, by rfl⟩ : syracuseStep 2349829 = 440593) (by norm_num)
theorem B12532421 : Blo 2199435 12532421 := bstep (se 4 (by rfl) ⟨1174914, by rfl⟩ : syracuseStep 12532421 = 2349829) B2349829
theorem B8354947 : Blo 2199435 8354947 := bstep (se 1 (by rfl) ⟨6266210, by rfl⟩ : syracuseStep 8354947 = 12532421) B12532421
theorem B11139929 : Blo 2199435 11139929 := bstep (se 2 (by rfl) ⟨4177473, by rfl⟩ : syracuseStep 11139929 = 8354947) B8354947
theorem B7426619 : Blo 2199435 7426619 := bstep (se 1 (by rfl) ⟨5569964, by rfl⟩ : syracuseStep 7426619 = 11139929) B11139929
theorem B4951079 : Blo 2199435 4951079 := bstep (se 1 (by rfl) ⟨3713309, by rfl⟩ : syracuseStep 4951079 = 7426619) B7426619
theorem B3300719 : Blo 2199435 3300719 := bstep (se 1 (by rfl) ⟨2475539, by rfl⟩ : syracuseStep 3300719 = 4951079) B4951079
theorem B2200479 : Blo 2199435 2200479 := bstep (se 1 (by rfl) ⟨1650359, by rfl⟩ : syracuseStep 2200479 = 3300719) B3300719
theorem B3300725 : Blo 2199435 3300725 := bbase (se 5 (by rfl) ⟨154721, by rfl⟩ : syracuseStep 3300725 = 309443) (by norm_num)
theorem B2200483 : Blo 2199435 2200483 := bstep (se 1 (by rfl) ⟨1650362, by rfl⟩ : syracuseStep 2200483 = 3300725) B3300725
theorem B3133117 : Blo 2199435 3133117 := bbase (se 3 (by rfl) ⟨587459, by rfl⟩ : syracuseStep 3133117 = 1174919) (by norm_num)
theorem B4177489 : Blo 2199435 4177489 := bstep (se 2 (by rfl) ⟨1566558, by rfl⟩ : syracuseStep 4177489 = 3133117) B3133117
theorem B5569985 : Blo 2199435 5569985 := bstep (se 2 (by rfl) ⟨2088744, by rfl⟩ : syracuseStep 5569985 = 4177489) B4177489
theorem B3713323 : Blo 2199435 3713323 := bstep (se 1 (by rfl) ⟨2784992, by rfl⟩ : syracuseStep 3713323 = 5569985) B5569985
theorem B4951097 : Blo 2199435 4951097 := bstep (se 2 (by rfl) ⟨1856661, by rfl⟩ : syracuseStep 4951097 = 3713323) B3713323
theorem B3300731 : Blo 2199435 3300731 := bstep (se 1 (by rfl) ⟨2475548, by rfl⟩ : syracuseStep 3300731 = 4951097) B4951097
theorem B2200487 : Blo 2199435 2200487 := bstep (se 1 (by rfl) ⟨1650365, by rfl⟩ : syracuseStep 2200487 = 3300731) B3300731
theorem B2475553 : Blo 2199435 2475553 := bbase (se 2 (by rfl) ⟨928332, by rfl⟩ : syracuseStep 2475553 = 1856665) (by norm_num)
theorem B3300737 : Blo 2199435 3300737 := bstep (se 2 (by rfl) ⟨1237776, by rfl⟩ : syracuseStep 3300737 = 2475553) B2475553
theorem B2200491 : Blo 2199435 2200491 := bstep (se 1 (by rfl) ⟨1650368, by rfl⟩ : syracuseStep 2200491 = 3300737) B3300737
theorem B5570005 : Blo 2199435 5570005 := bbase (se 7 (by rfl) ⟨65273, by rfl⟩ : syracuseStep 5570005 = 130547) (by norm_num)
theorem B7426673 : Blo 2199435 7426673 := bstep (se 2 (by rfl) ⟨2785002, by rfl⟩ : syracuseStep 7426673 = 5570005) B5570005
theorem B4951115 : Blo 2199435 4951115 := bstep (se 1 (by rfl) ⟨3713336, by rfl⟩ : syracuseStep 4951115 = 7426673) B7426673
theorem B3300743 : Blo 2199435 3300743 := bstep (se 1 (by rfl) ⟨2475557, by rfl⟩ : syracuseStep 3300743 = 4951115) B4951115
theorem B2200495 : Blo 2199435 2200495 := bstep (se 1 (by rfl) ⟨1650371, by rfl⟩ : syracuseStep 2200495 = 3300743) B3300743
theorem B3300749 : Blo 2199435 3300749 := bbase (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) (by norm_num)
theorem B2200499 : Blo 2199435 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B4951133 : Blo 2199435 4951133 := bbase (se 3 (by rfl) ⟨928337, by rfl⟩ : syracuseStep 4951133 = 1856675) (by norm_num)
theorem B3300755 : Blo 2199435 3300755 := bstep (se 1 (by rfl) ⟨2475566, by rfl⟩ : syracuseStep 3300755 = 4951133) B4951133
theorem B2200503 : Blo 2199435 2200503 := bstep (se 1 (by rfl) ⟨1650377, by rfl⟩ : syracuseStep 2200503 = 3300755) B3300755
theorem B3713357 : Blo 2199435 3713357 := bbase (se 3 (by rfl) ⟨696254, by rfl⟩ : syracuseStep 3713357 = 1392509) (by norm_num)
theorem B2475571 : Blo 2199435 2475571 := bstep (se 1 (by rfl) ⟨1856678, by rfl⟩ : syracuseStep 2475571 = 3713357) B3713357
theorem B3300761 : Blo 2199435 3300761 := bstep (se 2 (by rfl) ⟨1237785, by rfl⟩ : syracuseStep 3300761 = 2475571) B2475571
theorem B2200507 : Blo 2199435 2200507 := bstep (se 1 (by rfl) ⟨1650380, by rfl⟩ : syracuseStep 2200507 = 3300761) B3300761
theorem B6351797 : Blo 2199435 6351797 := bbase (se 5 (by rfl) ⟨297740, by rfl⟩ : syracuseStep 6351797 = 595481) (by norm_num)
theorem B4234531 : Blo 2199435 4234531 := bstep (se 1 (by rfl) ⟨3175898, by rfl⟩ : syracuseStep 4234531 = 6351797) B6351797
theorem B5646041 : Blo 2199435 5646041 := bstep (se 2 (by rfl) ⟨2117265, by rfl⟩ : syracuseStep 5646041 = 4234531) B4234531
theorem B3764027 : Blo 2199435 3764027 := bstep (se 1 (by rfl) ⟨2823020, by rfl⟩ : syracuseStep 3764027 = 5646041) B5646041
theorem B10037405 : Blo 2199435 10037405 := bstep (se 3 (by rfl) ⟨1882013, by rfl⟩ : syracuseStep 10037405 = 3764027) B3764027
theorem B26766413 : Blo 2199435 26766413 := bstep (se 3 (by rfl) ⟨5018702, by rfl⟩ : syracuseStep 26766413 = 10037405) B10037405
theorem B17844275 : Blo 2199435 17844275 := bstep (se 1 (by rfl) ⟨13383206, by rfl⟩ : syracuseStep 17844275 = 26766413) B26766413
theorem B11896183 : Blo 2199435 11896183 := bstep (se 1 (by rfl) ⟨8922137, by rfl⟩ : syracuseStep 11896183 = 17844275) B17844275
theorem B15861577 : Blo 2199435 15861577 := bstep (se 2 (by rfl) ⟨5948091, by rfl⟩ : syracuseStep 15861577 = 11896183) B11896183
theorem B21148769 : Blo 2199435 21148769 := bstep (se 2 (by rfl) ⟨7930788, by rfl⟩ : syracuseStep 21148769 = 15861577) B15861577
theorem B14099179 : Blo 2199435 14099179 := bstep (se 1 (by rfl) ⟨10574384, by rfl⟩ : syracuseStep 14099179 = 21148769) B21148769
theorem B18798905 : Blo 2199435 18798905 := bstep (se 2 (by rfl) ⟨7049589, by rfl⟩ : syracuseStep 18798905 = 14099179) B14099179
theorem B12532603 : Blo 2199435 12532603 := bstep (se 1 (by rfl) ⟨9399452, by rfl⟩ : syracuseStep 12532603 = 18798905) B18798905
theorem B16710137 : Blo 2199435 16710137 := bstep (se 2 (by rfl) ⟨6266301, by rfl⟩ : syracuseStep 16710137 = 12532603) B12532603
theorem B11140091 : Blo 2199435 11140091 := bstep (se 1 (by rfl) ⟨8355068, by rfl⟩ : syracuseStep 11140091 = 16710137) B16710137
theorem B7426727 : Blo 2199435 7426727 := bstep (se 1 (by rfl) ⟨5570045, by rfl⟩ : syracuseStep 7426727 = 11140091) B11140091
theorem B4951151 : Blo 2199435 4951151 := bstep (se 1 (by rfl) ⟨3713363, by rfl⟩ : syracuseStep 4951151 = 7426727) B7426727
theorem B3300767 : Blo 2199435 3300767 := bstep (se 1 (by rfl) ⟨2475575, by rfl⟩ : syracuseStep 3300767 = 4951151) B4951151
theorem B2200511 : Blo 2199435 2200511 := bstep (se 1 (by rfl) ⟨1650383, by rfl⟩ : syracuseStep 2200511 = 3300767) B3300767
theorem B3300773 : Blo 2199435 3300773 := bbase (se 4 (by rfl) ⟨309447, by rfl⟩ : syracuseStep 3300773 = 618895) (by norm_num)
theorem B2200515 : Blo 2199435 2200515 := bstep (se 1 (by rfl) ⟨1650386, by rfl⟩ : syracuseStep 2200515 = 3300773) B3300773
theorem B2785033 : Blo 2199435 2785033 := bbase (se 2 (by rfl) ⟨1044387, by rfl⟩ : syracuseStep 2785033 = 2088775) (by norm_num)
theorem B3713377 : Blo 2199435 3713377 := bstep (se 2 (by rfl) ⟨1392516, by rfl⟩ : syracuseStep 3713377 = 2785033) B2785033
theorem B4951169 : Blo 2199435 4951169 := bstep (se 2 (by rfl) ⟨1856688, by rfl⟩ : syracuseStep 4951169 = 3713377) B3713377
theorem B3300779 : Blo 2199435 3300779 := bstep (se 1 (by rfl) ⟨2475584, by rfl⟩ : syracuseStep 3300779 = 4951169) B4951169
theorem B2200519 : Blo 2199435 2200519 := bstep (se 1 (by rfl) ⟨1650389, by rfl⟩ : syracuseStep 2200519 = 3300779) B3300779
theorem B2475589 : Blo 2199435 2475589 := bbase (se 4 (by rfl) ⟨232086, by rfl⟩ : syracuseStep 2475589 = 464173) (by norm_num)
theorem B3300785 : Blo 2199435 3300785 := bstep (se 2 (by rfl) ⟨1237794, by rfl⟩ : syracuseStep 3300785 = 2475589) B2475589
theorem B2200523 : Blo 2199435 2200523 := bstep (se 1 (by rfl) ⟨1650392, by rfl⟩ : syracuseStep 2200523 = 3300785) B3300785
theorem B4177565 : Blo 2199435 4177565 := bbase (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) (by norm_num)
theorem B2785043 : Blo 2199435 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B7426781 : Blo 2199435 7426781 := bstep (se 3 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 7426781 = 2785043) B2785043
theorem B4951187 : Blo 2199435 4951187 := bstep (se 1 (by rfl) ⟨3713390, by rfl⟩ : syracuseStep 4951187 = 7426781) B7426781
theorem B3300791 : Blo 2199435 3300791 := bstep (se 1 (by rfl) ⟨2475593, by rfl⟩ : syracuseStep 3300791 = 4951187) B4951187
theorem B2200527 : Blo 2199435 2200527 := bstep (se 1 (by rfl) ⟨1650395, by rfl⟩ : syracuseStep 2200527 = 3300791) B3300791
theorem B3300797 : Blo 2199435 3300797 := bbase (se 3 (by rfl) ⟨618899, by rfl⟩ : syracuseStep 3300797 = 1237799) (by norm_num)
theorem B2200531 : Blo 2199435 2200531 := bstep (se 1 (by rfl) ⟨1650398, by rfl⟩ : syracuseStep 2200531 = 3300797) B3300797
theorem B4951205 : Blo 2199435 4951205 := bbase (se 4 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 4951205 = 928351) (by norm_num)
theorem B3300803 : Blo 2199435 3300803 := bstep (se 1 (by rfl) ⟨2475602, by rfl⟩ : syracuseStep 3300803 = 4951205) B4951205
theorem B2200535 : Blo 2199435 2200535 := bstep (se 1 (by rfl) ⟨1650401, by rfl⟩ : syracuseStep 2200535 = 3300803) B3300803
theorem B5570117 : Blo 2199435 5570117 := bbase (se 4 (by rfl) ⟨522198, by rfl⟩ : syracuseStep 5570117 = 1044397) (by norm_num)
theorem B3713411 : Blo 2199435 3713411 := bstep (se 1 (by rfl) ⟨2785058, by rfl⟩ : syracuseStep 3713411 = 5570117) B5570117
theorem B2475607 : Blo 2199435 2475607 := bstep (se 1 (by rfl) ⟨1856705, by rfl⟩ : syracuseStep 2475607 = 3713411) B3713411
theorem B3300809 : Blo 2199435 3300809 := bstep (se 2 (by rfl) ⟨1237803, by rfl⟩ : syracuseStep 3300809 = 2475607) B2475607
theorem B2200539 : Blo 2199435 2200539 := bstep (se 1 (by rfl) ⟨1650404, by rfl⟩ : syracuseStep 2200539 = 3300809) B3300809
theorem B3965453 : Blo 2199435 3965453 := bbase (se 3 (by rfl) ⟨743522, by rfl⟩ : syracuseStep 3965453 = 1487045) (by norm_num)
theorem B2643635 : Blo 2199435 2643635 := bstep (se 1 (by rfl) ⟨1982726, by rfl⟩ : syracuseStep 2643635 = 3965453) B3965453
theorem B7049693 : Blo 2199435 7049693 := bstep (se 3 (by rfl) ⟨1321817, by rfl⟩ : syracuseStep 7049693 = 2643635) B2643635
theorem B4699795 : Blo 2199435 4699795 := bstep (se 1 (by rfl) ⟨3524846, by rfl⟩ : syracuseStep 4699795 = 7049693) B7049693
theorem B6266393 : Blo 2199435 6266393 := bstep (se 2 (by rfl) ⟨2349897, by rfl⟩ : syracuseStep 6266393 = 4699795) B4699795
theorem B4177595 : Blo 2199435 4177595 := bstep (se 1 (by rfl) ⟨3133196, by rfl⟩ : syracuseStep 4177595 = 6266393) B6266393
theorem B11140253 : Blo 2199435 11140253 := bstep (se 3 (by rfl) ⟨2088797, by rfl⟩ : syracuseStep 11140253 = 4177595) B4177595
theorem B7426835 : Blo 2199435 7426835 := bstep (se 1 (by rfl) ⟨5570126, by rfl⟩ : syracuseStep 7426835 = 11140253) B11140253
theorem B4951223 : Blo 2199435 4951223 := bstep (se 1 (by rfl) ⟨3713417, by rfl⟩ : syracuseStep 4951223 = 7426835) B7426835
theorem B3300815 : Blo 2199435 3300815 := bstep (se 1 (by rfl) ⟨2475611, by rfl⟩ : syracuseStep 3300815 = 4951223) B4951223
theorem B2200543 : Blo 2199435 2200543 := bstep (se 1 (by rfl) ⟨1650407, by rfl⟩ : syracuseStep 2200543 = 3300815) B3300815
theorem B3300821 : Blo 2199435 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B2200547 : Blo 2199435 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B8355221 : Blo 2199435 8355221 := bbase (se 6 (by rfl) ⟨195825, by rfl⟩ : syracuseStep 8355221 = 391651) (by norm_num)
theorem B5570147 : Blo 2199435 5570147 := bstep (se 1 (by rfl) ⟨4177610, by rfl⟩ : syracuseStep 5570147 = 8355221) B8355221
theorem B3713431 : Blo 2199435 3713431 := bstep (se 1 (by rfl) ⟨2785073, by rfl⟩ : syracuseStep 3713431 = 5570147) B5570147
theorem B4951241 : Blo 2199435 4951241 := bstep (se 2 (by rfl) ⟨1856715, by rfl⟩ : syracuseStep 4951241 = 3713431) B3713431
theorem B3300827 : Blo 2199435 3300827 := bstep (se 1 (by rfl) ⟨2475620, by rfl⟩ : syracuseStep 3300827 = 4951241) B4951241
theorem B2200551 : Blo 2199435 2200551 := bstep (se 1 (by rfl) ⟨1650413, by rfl⟩ : syracuseStep 2200551 = 3300827) B3300827
theorem B2475625 : Blo 2199435 2475625 := bbase (se 2 (by rfl) ⟨928359, by rfl⟩ : syracuseStep 2475625 = 1856719) (by norm_num)
theorem B3300833 : Blo 2199435 3300833 := bstep (se 2 (by rfl) ⟨1237812, by rfl⟩ : syracuseStep 3300833 = 2475625) B2475625
theorem B2200555 : Blo 2199435 2200555 := bstep (se 1 (by rfl) ⟨1650416, by rfl⟩ : syracuseStep 2200555 = 3300833) B3300833
theorem B4699829 : Blo 2199435 4699829 := bbase (se 5 (by rfl) ⟨220304, by rfl⟩ : syracuseStep 4699829 = 440609) (by norm_num)
theorem B12532877 : Blo 2199435 12532877 := bstep (se 3 (by rfl) ⟨2349914, by rfl⟩ : syracuseStep 12532877 = 4699829) B4699829
theorem B8355251 : Blo 2199435 8355251 := bstep (se 1 (by rfl) ⟨6266438, by rfl⟩ : syracuseStep 8355251 = 12532877) B12532877
theorem B5570167 : Blo 2199435 5570167 := bstep (se 1 (by rfl) ⟨4177625, by rfl⟩ : syracuseStep 5570167 = 8355251) B8355251
theorem B7426889 : Blo 2199435 7426889 := bstep (se 2 (by rfl) ⟨2785083, by rfl⟩ : syracuseStep 7426889 = 5570167) B5570167
theorem B4951259 : Blo 2199435 4951259 := bstep (se 1 (by rfl) ⟨3713444, by rfl⟩ : syracuseStep 4951259 = 7426889) B7426889
theorem B3300839 : Blo 2199435 3300839 := bstep (se 1 (by rfl) ⟨2475629, by rfl⟩ : syracuseStep 3300839 = 4951259) B4951259
theorem B2200559 : Blo 2199435 2200559 := bstep (se 1 (by rfl) ⟨1650419, by rfl⟩ : syracuseStep 2200559 = 3300839) B3300839
theorem B3300845 : Blo 2199435 3300845 := bbase (se 3 (by rfl) ⟨618908, by rfl⟩ : syracuseStep 3300845 = 1237817) (by norm_num)
theorem B2200563 : Blo 2199435 2200563 := bstep (se 1 (by rfl) ⟨1650422, by rfl⟩ : syracuseStep 2200563 = 3300845) B3300845
theorem B4951277 : Blo 2199435 4951277 := bbase (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) (by norm_num)
theorem B3300851 : Blo 2199435 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B2200567 : Blo 2199435 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B3133237 : Blo 2199435 3133237 := bbase (se 5 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 3133237 = 293741) (by norm_num)
theorem B4177649 : Blo 2199435 4177649 := bstep (se 2 (by rfl) ⟨1566618, by rfl⟩ : syracuseStep 4177649 = 3133237) B3133237
theorem B2785099 : Blo 2199435 2785099 := bstep (se 1 (by rfl) ⟨2088824, by rfl⟩ : syracuseStep 2785099 = 4177649) B4177649
theorem B3713465 : Blo 2199435 3713465 := bstep (se 2 (by rfl) ⟨1392549, by rfl⟩ : syracuseStep 3713465 = 2785099) B2785099
theorem B2475643 : Blo 2199435 2475643 := bstep (se 1 (by rfl) ⟨1856732, by rfl⟩ : syracuseStep 2475643 = 3713465) B3713465
theorem B3300857 : Blo 2199435 3300857 := bstep (se 2 (by rfl) ⟨1237821, by rfl⟩ : syracuseStep 3300857 = 2475643) B2475643
theorem B2200571 : Blo 2199435 2200571 := bstep (se 1 (by rfl) ⟨1650428, by rfl⟩ : syracuseStep 2200571 = 3300857) B3300857
theorem B26767189 : Blo 2199435 26767189 := bbase (se 9 (by rfl) ⟨78419, by rfl⟩ : syracuseStep 26767189 = 156839) (by norm_num)
theorem B35689585 : Blo 2199435 35689585 := bstep (se 2 (by rfl) ⟨13383594, by rfl⟩ : syracuseStep 35689585 = 26767189) B26767189
theorem B47586113 : Blo 2199435 47586113 := bstep (se 2 (by rfl) ⟨17844792, by rfl⟩ : syracuseStep 47586113 = 35689585) B35689585
theorem B31724075 : Blo 2199435 31724075 := bstep (se 1 (by rfl) ⟨23793056, by rfl⟩ : syracuseStep 31724075 = 47586113) B47586113
theorem B84597533 : Blo 2199435 84597533 := bstep (se 3 (by rfl) ⟨15862037, by rfl⟩ : syracuseStep 84597533 = 31724075) B31724075
theorem B56398355 : Blo 2199435 56398355 := bstep (se 1 (by rfl) ⟨42298766, by rfl⟩ : syracuseStep 56398355 = 84597533) B84597533
theorem B37598903 : Blo 2199435 37598903 := bstep (se 1 (by rfl) ⟨28199177, by rfl⟩ : syracuseStep 37598903 = 56398355) B56398355
theorem B25065935 : Blo 2199435 25065935 := bstep (se 1 (by rfl) ⟨18799451, by rfl⟩ : syracuseStep 25065935 = 37598903) B37598903
theorem B16710623 : Blo 2199435 16710623 := bstep (se 1 (by rfl) ⟨12532967, by rfl⟩ : syracuseStep 16710623 = 25065935) B25065935
theorem B11140415 : Blo 2199435 11140415 := bstep (se 1 (by rfl) ⟨8355311, by rfl⟩ : syracuseStep 11140415 = 16710623) B16710623
theorem B7426943 : Blo 2199435 7426943 := bstep (se 1 (by rfl) ⟨5570207, by rfl⟩ : syracuseStep 7426943 = 11140415) B11140415
theorem B4951295 : Blo 2199435 4951295 := bstep (se 1 (by rfl) ⟨3713471, by rfl⟩ : syracuseStep 4951295 = 7426943) B7426943
theorem B3300863 : Blo 2199435 3300863 := bstep (se 1 (by rfl) ⟨2475647, by rfl⟩ : syracuseStep 3300863 = 4951295) B4951295
theorem B2200575 : Blo 2199435 2200575 := bstep (se 1 (by rfl) ⟨1650431, by rfl⟩ : syracuseStep 2200575 = 3300863) B3300863
theorem B3300869 : Blo 2199435 3300869 := bbase (se 4 (by rfl) ⟨309456, by rfl⟩ : syracuseStep 3300869 = 618913) (by norm_num)
theorem B2200579 : Blo 2199435 2200579 := bstep (se 1 (by rfl) ⟨1650434, by rfl⟩ : syracuseStep 2200579 = 3300869) B3300869
theorem B3713485 : Blo 2199435 3713485 := bbase (se 3 (by rfl) ⟨696278, by rfl⟩ : syracuseStep 3713485 = 1392557) (by norm_num)
theorem B4951313 : Blo 2199435 4951313 := bstep (se 2 (by rfl) ⟨1856742, by rfl⟩ : syracuseStep 4951313 = 3713485) B3713485
theorem B3300875 : Blo 2199435 3300875 := bstep (se 1 (by rfl) ⟨2475656, by rfl⟩ : syracuseStep 3300875 = 4951313) B4951313
theorem B2200583 : Blo 2199435 2200583 := bstep (se 1 (by rfl) ⟨1650437, by rfl⟩ : syracuseStep 2200583 = 3300875) B3300875
theorem B2475661 : Blo 2199435 2475661 := bbase (se 3 (by rfl) ⟨464186, by rfl⟩ : syracuseStep 2475661 = 928373) (by norm_num)
theorem B3300881 : Blo 2199435 3300881 := bstep (se 2 (by rfl) ⟨1237830, by rfl⟩ : syracuseStep 3300881 = 2475661) B2475661
theorem B2200587 : Blo 2199435 2200587 := bstep (se 1 (by rfl) ⟨1650440, by rfl⟩ : syracuseStep 2200587 = 3300881) B3300881
theorem B7426997 : Blo 2199435 7426997 := bbase (se 5 (by rfl) ⟨348140, by rfl⟩ : syracuseStep 7426997 = 696281) (by norm_num)
theorem B4951331 : Blo 2199435 4951331 := bstep (se 1 (by rfl) ⟨3713498, by rfl⟩ : syracuseStep 4951331 = 7426997) B7426997
theorem B3300887 : Blo 2199435 3300887 := bstep (se 1 (by rfl) ⟨2475665, by rfl⟩ : syracuseStep 3300887 = 4951331) B4951331
theorem B2200591 : Blo 2199435 2200591 := bstep (se 1 (by rfl) ⟨1650443, by rfl⟩ : syracuseStep 2200591 = 3300887) B3300887
theorem B3300893 : Blo 2199435 3300893 := bbase (se 3 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 3300893 = 1237835) (by norm_num)
theorem B2200595 : Blo 2199435 2200595 := bstep (se 1 (by rfl) ⟨1650446, by rfl⟩ : syracuseStep 2200595 = 3300893) B3300893
theorem B4951349 : Blo 2199435 4951349 := bbase (se 5 (by rfl) ⟨232094, by rfl⟩ : syracuseStep 4951349 = 464189) (by norm_num)
theorem B3300899 : Blo 2199435 3300899 := bstep (se 1 (by rfl) ⟨2475674, by rfl⟩ : syracuseStep 3300899 = 4951349) B4951349
theorem B2200599 : Blo 2199435 2200599 := bstep (se 1 (by rfl) ⟨1650449, by rfl⟩ : syracuseStep 2200599 = 3300899) B3300899
theorem B23793365 : Blo 2199435 23793365 := bbase (se 7 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 23793365 = 557657) (by norm_num)
theorem B15862243 : Blo 2199435 15862243 := bstep (se 1 (by rfl) ⟨11896682, by rfl⟩ : syracuseStep 15862243 = 23793365) B23793365
theorem B21149657 : Blo 2199435 21149657 := bstep (se 2 (by rfl) ⟨7931121, by rfl⟩ : syracuseStep 21149657 = 15862243) B15862243
theorem B14099771 : Blo 2199435 14099771 := bstep (se 1 (by rfl) ⟨10574828, by rfl⟩ : syracuseStep 14099771 = 21149657) B21149657
theorem B9399847 : Blo 2199435 9399847 := bstep (se 1 (by rfl) ⟨7049885, by rfl⟩ : syracuseStep 9399847 = 14099771) B14099771
theorem B12533129 : Blo 2199435 12533129 := bstep (se 2 (by rfl) ⟨4699923, by rfl⟩ : syracuseStep 12533129 = 9399847) B9399847
theorem B8355419 : Blo 2199435 8355419 := bstep (se 1 (by rfl) ⟨6266564, by rfl⟩ : syracuseStep 8355419 = 12533129) B12533129
theorem B5570279 : Blo 2199435 5570279 := bstep (se 1 (by rfl) ⟨4177709, by rfl⟩ : syracuseStep 5570279 = 8355419) B8355419
theorem B3713519 : Blo 2199435 3713519 := bstep (se 1 (by rfl) ⟨2785139, by rfl⟩ : syracuseStep 3713519 = 5570279) B5570279
theorem B2475679 : Blo 2199435 2475679 := bstep (se 1 (by rfl) ⟨1856759, by rfl⟩ : syracuseStep 2475679 = 3713519) B3713519
theorem B3300905 : Blo 2199435 3300905 := bstep (se 2 (by rfl) ⟨1237839, by rfl⟩ : syracuseStep 3300905 = 2475679) B2475679
theorem B2200603 : Blo 2199435 2200603 := bstep (se 1 (by rfl) ⟨1650452, by rfl⟩ : syracuseStep 2200603 = 3300905) B3300905
theorem B4829053 : Blo 2199435 4829053 := bbase (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) (by norm_num)
theorem B6438737 : Blo 2199435 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B17169965 : Blo 2199435 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B11446643 : Blo 2199435 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B30524381 : Blo 2199435 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B20349587 : Blo 2199435 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B54265565 : Blo 2199435 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B36177043 : Blo 2199435 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B48236057 : Blo 2199435 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B32157371 : Blo 2199435 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B85752989 : Blo 2199435 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B57168659 : Blo 2199435 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B38112439 : Blo 2199435 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B50816585 : Blo 2199435 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B135510893 : Blo 2199435 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B90340595 : Blo 2199435 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B60227063 : Blo 2199435 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B40151375 : Blo 2199435 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B26767583 : Blo 2199435 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B17845055 : Blo 2199435 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B11896703 : Blo 2199435 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B7931135 : Blo 2199435 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B21149693 : Blo 2199435 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B14099795 : Blo 2199435 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B9399863 : Blo 2199435 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B6266575 : Blo 2199435 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B8355433 : Blo 2199435 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B11140577 : Blo 2199435 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B7427051 : Blo 2199435 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B4951367 : Blo 2199435 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B3300911 : Blo 2199435 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B2200607 : Blo 2199435 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B3300917 : Blo 2199435 3300917 := bbase (se 5 (by rfl) ⟨154730, by rfl⟩ : syracuseStep 3300917 = 309461) (by norm_num)
theorem B2200611 : Blo 2199435 2200611 := bstep (se 1 (by rfl) ⟨1650458, by rfl⟩ : syracuseStep 2200611 = 3300917) B3300917
theorem B5570309 : Blo 2199435 5570309 := bbase (se 4 (by rfl) ⟨522216, by rfl⟩ : syracuseStep 5570309 = 1044433) (by norm_num)
theorem B3713539 : Blo 2199435 3713539 := bstep (se 1 (by rfl) ⟨2785154, by rfl⟩ : syracuseStep 3713539 = 5570309) B5570309
theorem B4951385 : Blo 2199435 4951385 := bstep (se 2 (by rfl) ⟨1856769, by rfl⟩ : syracuseStep 4951385 = 3713539) B3713539
theorem B3300923 : Blo 2199435 3300923 := bstep (se 1 (by rfl) ⟨2475692, by rfl⟩ : syracuseStep 3300923 = 4951385) B4951385
theorem B2200615 : Blo 2199435 2200615 := bstep (se 1 (by rfl) ⟨1650461, by rfl⟩ : syracuseStep 2200615 = 3300923) B3300923
theorem B2475697 : Blo 2199435 2475697 := bbase (se 2 (by rfl) ⟨928386, by rfl⟩ : syracuseStep 2475697 = 1856773) (by norm_num)
theorem B3300929 : Blo 2199435 3300929 := bstep (se 2 (by rfl) ⟨1237848, by rfl⟩ : syracuseStep 3300929 = 2475697) B2475697
theorem B2200619 : Blo 2199435 2200619 := bstep (se 1 (by rfl) ⟨1650464, by rfl⟩ : syracuseStep 2200619 = 3300929) B3300929
theorem B13383893 : Blo 2199435 13383893 := bbase (se 7 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 13383893 = 313685) (by norm_num)
theorem B8922595 : Blo 2199435 8922595 := bstep (se 1 (by rfl) ⟨6691946, by rfl⟩ : syracuseStep 8922595 = 13383893) B13383893
theorem B11896793 : Blo 2199435 11896793 := bstep (se 2 (by rfl) ⟨4461297, by rfl⟩ : syracuseStep 11896793 = 8922595) B8922595
theorem B7931195 : Blo 2199435 7931195 := bstep (se 1 (by rfl) ⟨5948396, by rfl⟩ : syracuseStep 7931195 = 11896793) B11896793
theorem B5287463 : Blo 2199435 5287463 := bstep (se 1 (by rfl) ⟨3965597, by rfl⟩ : syracuseStep 5287463 = 7931195) B7931195
theorem B3524975 : Blo 2199435 3524975 := bstep (se 1 (by rfl) ⟨2643731, by rfl⟩ : syracuseStep 3524975 = 5287463) B5287463
theorem B2349983 : Blo 2199435 2349983 := bstep (se 1 (by rfl) ⟨1762487, by rfl⟩ : syracuseStep 2349983 = 3524975) B3524975
theorem B6266621 : Blo 2199435 6266621 := bstep (se 3 (by rfl) ⟨1174991, by rfl⟩ : syracuseStep 6266621 = 2349983) B2349983
theorem B4177747 : Blo 2199435 4177747 := bstep (se 1 (by rfl) ⟨3133310, by rfl⟩ : syracuseStep 4177747 = 6266621) B6266621
theorem B5570329 : Blo 2199435 5570329 := bstep (se 2 (by rfl) ⟨2088873, by rfl⟩ : syracuseStep 5570329 = 4177747) B4177747
theorem B7427105 : Blo 2199435 7427105 := bstep (se 2 (by rfl) ⟨2785164, by rfl⟩ : syracuseStep 7427105 = 5570329) B5570329
theorem B4951403 : Blo 2199435 4951403 := bstep (se 1 (by rfl) ⟨3713552, by rfl⟩ : syracuseStep 4951403 = 7427105) B7427105
theorem B3300935 : Blo 2199435 3300935 := bstep (se 1 (by rfl) ⟨2475701, by rfl⟩ : syracuseStep 3300935 = 4951403) B4951403
theorem B2200623 : Blo 2199435 2200623 := bstep (se 1 (by rfl) ⟨1650467, by rfl⟩ : syracuseStep 2200623 = 3300935) B3300935
theorem B3300941 : Blo 2199435 3300941 := bbase (se 3 (by rfl) ⟨618926, by rfl⟩ : syracuseStep 3300941 = 1237853) (by norm_num)
theorem B2200627 : Blo 2199435 2200627 := bstep (se 1 (by rfl) ⟨1650470, by rfl⟩ : syracuseStep 2200627 = 3300941) B3300941
theorem B4951421 : Blo 2199435 4951421 := bbase (se 3 (by rfl) ⟨928391, by rfl⟩ : syracuseStep 4951421 = 1856783) (by norm_num)
theorem B3300947 : Blo 2199435 3300947 := bstep (se 1 (by rfl) ⟨2475710, by rfl⟩ : syracuseStep 3300947 = 4951421) B4951421
theorem B2200631 : Blo 2199435 2200631 := bstep (se 1 (by rfl) ⟨1650473, by rfl⟩ : syracuseStep 2200631 = 3300947) B3300947
theorem B3713573 : Blo 2199435 3713573 := bbase (se 4 (by rfl) ⟨348147, by rfl⟩ : syracuseStep 3713573 = 696295) (by norm_num)
theorem B2475715 : Blo 2199435 2475715 := bstep (se 1 (by rfl) ⟨1856786, by rfl⟩ : syracuseStep 2475715 = 3713573) B3713573
theorem B3300953 : Blo 2199435 3300953 := bstep (se 2 (by rfl) ⟨1237857, by rfl⟩ : syracuseStep 3300953 = 2475715) B2475715
theorem B2200635 : Blo 2199435 2200635 := bstep (se 1 (by rfl) ⟨1650476, by rfl⟩ : syracuseStep 2200635 = 3300953) B3300953
theorem B3133333 : Blo 2199435 3133333 := bbase (se 6 (by rfl) ⟨73437, by rfl⟩ : syracuseStep 3133333 = 146875) (by norm_num)
theorem B16711109 : Blo 2199435 16711109 := bstep (se 4 (by rfl) ⟨1566666, by rfl⟩ : syracuseStep 16711109 = 3133333) B3133333
theorem B11140739 : Blo 2199435 11140739 := bstep (se 1 (by rfl) ⟨8355554, by rfl⟩ : syracuseStep 11140739 = 16711109) B16711109
theorem B7427159 : Blo 2199435 7427159 := bstep (se 1 (by rfl) ⟨5570369, by rfl⟩ : syracuseStep 7427159 = 11140739) B11140739
theorem B4951439 : Blo 2199435 4951439 := bstep (se 1 (by rfl) ⟨3713579, by rfl⟩ : syracuseStep 4951439 = 7427159) B7427159
theorem B3300959 : Blo 2199435 3300959 := bstep (se 1 (by rfl) ⟨2475719, by rfl⟩ : syracuseStep 3300959 = 4951439) B4951439
theorem B2200639 : Blo 2199435 2200639 := bstep (se 1 (by rfl) ⟨1650479, by rfl⟩ : syracuseStep 2200639 = 3300959) B3300959
theorem B3300965 : Blo 2199435 3300965 := bbase (se 4 (by rfl) ⟨309465, by rfl⟩ : syracuseStep 3300965 = 618931) (by norm_num)
theorem B2200643 : Blo 2199435 2200643 := bstep (se 1 (by rfl) ⟨1650482, by rfl⟩ : syracuseStep 2200643 = 3300965) B3300965
theorem B2350009 : Blo 2199435 2350009 := bbase (se 2 (by rfl) ⟨881253, by rfl⟩ : syracuseStep 2350009 = 1762507) (by norm_num)
theorem B3133345 : Blo 2199435 3133345 := bstep (se 2 (by rfl) ⟨1175004, by rfl⟩ : syracuseStep 3133345 = 2350009) B2350009
theorem B4177793 : Blo 2199435 4177793 := bstep (se 2 (by rfl) ⟨1566672, by rfl⟩ : syracuseStep 4177793 = 3133345) B3133345
theorem B2785195 : Blo 2199435 2785195 := bstep (se 1 (by rfl) ⟨2088896, by rfl⟩ : syracuseStep 2785195 = 4177793) B4177793
theorem B3713593 : Blo 2199435 3713593 := bstep (se 2 (by rfl) ⟨1392597, by rfl⟩ : syracuseStep 3713593 = 2785195) B2785195
theorem B4951457 : Blo 2199435 4951457 := bstep (se 2 (by rfl) ⟨1856796, by rfl⟩ : syracuseStep 4951457 = 3713593) B3713593
theorem B3300971 : Blo 2199435 3300971 := bstep (se 1 (by rfl) ⟨2475728, by rfl⟩ : syracuseStep 3300971 = 4951457) B4951457
theorem B2200647 : Blo 2199435 2200647 := bstep (se 1 (by rfl) ⟨1650485, by rfl⟩ : syracuseStep 2200647 = 3300971) B3300971
theorem B2475733 : Blo 2199435 2475733 := bbase (se 7 (by rfl) ⟨29012, by rfl⟩ : syracuseStep 2475733 = 58025) (by norm_num)
theorem B3300977 : Blo 2199435 3300977 := bstep (se 2 (by rfl) ⟨1237866, by rfl⟩ : syracuseStep 3300977 = 2475733) B2475733
theorem B2200651 : Blo 2199435 2200651 := bstep (se 1 (by rfl) ⟨1650488, by rfl⟩ : syracuseStep 2200651 = 3300977) B3300977
theorem B2785205 : Blo 2199435 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B7427213 : Blo 2199435 7427213 := bstep (se 3 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 7427213 = 2785205) B2785205
theorem B4951475 : Blo 2199435 4951475 := bstep (se 1 (by rfl) ⟨3713606, by rfl⟩ : syracuseStep 4951475 = 7427213) B7427213
theorem B3300983 : Blo 2199435 3300983 := bstep (se 1 (by rfl) ⟨2475737, by rfl⟩ : syracuseStep 3300983 = 4951475) B4951475
theorem B2200655 : Blo 2199435 2200655 := bstep (se 1 (by rfl) ⟨1650491, by rfl⟩ : syracuseStep 2200655 = 3300983) B3300983
theorem B3300989 : Blo 2199435 3300989 := bbase (se 3 (by rfl) ⟨618935, by rfl⟩ : syracuseStep 3300989 = 1237871) (by norm_num)
theorem B2200659 : Blo 2199435 2200659 := bstep (se 1 (by rfl) ⟨1650494, by rfl⟩ : syracuseStep 2200659 = 3300989) B3300989
theorem B4951493 : Blo 2199435 4951493 := bbase (se 4 (by rfl) ⟨464202, by rfl⟩ : syracuseStep 4951493 = 928405) (by norm_num)
theorem B3300995 : Blo 2199435 3300995 := bstep (se 1 (by rfl) ⟨2475746, by rfl⟩ : syracuseStep 3300995 = 4951493) B4951493
theorem B2200663 : Blo 2199435 2200663 := bstep (se 1 (by rfl) ⟨1650497, by rfl⟩ : syracuseStep 2200663 = 3300995) B3300995
theorem B8922773 : Blo 2199435 8922773 := bbase (se 6 (by rfl) ⟨209127, by rfl⟩ : syracuseStep 8922773 = 418255) (by norm_num)
theorem B5948515 : Blo 2199435 5948515 := bstep (se 1 (by rfl) ⟨4461386, by rfl⟩ : syracuseStep 5948515 = 8922773) B8922773
theorem B7931353 : Blo 2199435 7931353 := bstep (se 2 (by rfl) ⟨2974257, by rfl⟩ : syracuseStep 7931353 = 5948515) B5948515
theorem B10575137 : Blo 2199435 10575137 := bstep (se 2 (by rfl) ⟨3965676, by rfl⟩ : syracuseStep 10575137 = 7931353) B7931353
theorem B7050091 : Blo 2199435 7050091 := bstep (se 1 (by rfl) ⟨5287568, by rfl⟩ : syracuseStep 7050091 = 10575137) B10575137
theorem B9400121 : Blo 2199435 9400121 := bstep (se 2 (by rfl) ⟨3525045, by rfl⟩ : syracuseStep 9400121 = 7050091) B7050091
theorem B6266747 : Blo 2199435 6266747 := bstep (se 1 (by rfl) ⟨4700060, by rfl⟩ : syracuseStep 6266747 = 9400121) B9400121
theorem B4177831 : Blo 2199435 4177831 := bstep (se 1 (by rfl) ⟨3133373, by rfl⟩ : syracuseStep 4177831 = 6266747) B6266747
theorem B5570441 : Blo 2199435 5570441 := bstep (se 2 (by rfl) ⟨2088915, by rfl⟩ : syracuseStep 5570441 = 4177831) B4177831
theorem B3713627 : Blo 2199435 3713627 := bstep (se 1 (by rfl) ⟨2785220, by rfl⟩ : syracuseStep 3713627 = 5570441) B5570441
theorem B2475751 : Blo 2199435 2475751 := bstep (se 1 (by rfl) ⟨1856813, by rfl⟩ : syracuseStep 2475751 = 3713627) B3713627
theorem B3301001 : Blo 2199435 3301001 := bstep (se 2 (by rfl) ⟨1237875, by rfl⟩ : syracuseStep 3301001 = 2475751) B2475751
theorem B2200667 : Blo 2199435 2200667 := bstep (se 1 (by rfl) ⟨1650500, by rfl⟩ : syracuseStep 2200667 = 3301001) B3301001
theorem B11140901 : Blo 2199435 11140901 := bbase (se 4 (by rfl) ⟨1044459, by rfl⟩ : syracuseStep 11140901 = 2088919) (by norm_num)
theorem B7427267 : Blo 2199435 7427267 := bstep (se 1 (by rfl) ⟨5570450, by rfl⟩ : syracuseStep 7427267 = 11140901) B11140901
theorem B4951511 : Blo 2199435 4951511 := bstep (se 1 (by rfl) ⟨3713633, by rfl⟩ : syracuseStep 4951511 = 7427267) B7427267
theorem B3301007 : Blo 2199435 3301007 := bstep (se 1 (by rfl) ⟨2475755, by rfl⟩ : syracuseStep 3301007 = 4951511) B4951511
theorem B2200671 : Blo 2199435 2200671 := bstep (se 1 (by rfl) ⟨1650503, by rfl⟩ : syracuseStep 2200671 = 3301007) B3301007
theorem B3301013 : Blo 2199435 3301013 := bbase (se 6 (by rfl) ⟨77367, by rfl⟩ : syracuseStep 3301013 = 154735) (by norm_num)
theorem B2200675 : Blo 2199435 2200675 := bstep (se 1 (by rfl) ⟨1650506, by rfl⟩ : syracuseStep 2200675 = 3301013) B3301013
theorem B2230705 : Blo 2199435 2230705 := bbase (se 2 (by rfl) ⟨836514, by rfl⟩ : syracuseStep 2230705 = 1673029) (by norm_num)
theorem B11897093 : Blo 2199435 11897093 := bstep (se 4 (by rfl) ⟨1115352, by rfl⟩ : syracuseStep 11897093 = 2230705) B2230705
theorem B7931395 : Blo 2199435 7931395 := bstep (se 1 (by rfl) ⟨5948546, by rfl⟩ : syracuseStep 7931395 = 11897093) B11897093
theorem B10575193 : Blo 2199435 10575193 := bstep (se 2 (by rfl) ⟨3965697, by rfl⟩ : syracuseStep 10575193 = 7931395) B7931395
theorem B14100257 : Blo 2199435 14100257 := bstep (se 2 (by rfl) ⟨5287596, by rfl⟩ : syracuseStep 14100257 = 10575193) B10575193
theorem B9400171 : Blo 2199435 9400171 := bstep (se 1 (by rfl) ⟨7050128, by rfl⟩ : syracuseStep 9400171 = 14100257) B14100257
theorem B12533561 : Blo 2199435 12533561 := bstep (se 2 (by rfl) ⟨4700085, by rfl⟩ : syracuseStep 12533561 = 9400171) B9400171
theorem B8355707 : Blo 2199435 8355707 := bstep (se 1 (by rfl) ⟨6266780, by rfl⟩ : syracuseStep 8355707 = 12533561) B12533561
theorem B5570471 : Blo 2199435 5570471 := bstep (se 1 (by rfl) ⟨4177853, by rfl⟩ : syracuseStep 5570471 = 8355707) B8355707
theorem B3713647 : Blo 2199435 3713647 := bstep (se 1 (by rfl) ⟨2785235, by rfl⟩ : syracuseStep 3713647 = 5570471) B5570471
theorem B4951529 : Blo 2199435 4951529 := bstep (se 2 (by rfl) ⟨1856823, by rfl⟩ : syracuseStep 4951529 = 3713647) B3713647
theorem B3301019 : Blo 2199435 3301019 := bstep (se 1 (by rfl) ⟨2475764, by rfl⟩ : syracuseStep 3301019 = 4951529) B4951529
theorem B2200679 : Blo 2199435 2200679 := bstep (se 1 (by rfl) ⟨1650509, by rfl⟩ : syracuseStep 2200679 = 3301019) B3301019
theorem B2475769 : Blo 2199435 2475769 := bbase (se 2 (by rfl) ⟨928413, by rfl⟩ : syracuseStep 2475769 = 1856827) (by norm_num)
theorem B3301025 : Blo 2199435 3301025 := bstep (se 2 (by rfl) ⟨1237884, by rfl⟩ : syracuseStep 3301025 = 2475769) B2475769
theorem B2200683 : Blo 2199435 2200683 := bstep (se 1 (by rfl) ⟨1650512, by rfl⟩ : syracuseStep 2200683 = 3301025) B3301025
theorem B3525077 : Blo 2199435 3525077 := bbase (se 7 (by rfl) ⟨41309, by rfl⟩ : syracuseStep 3525077 = 82619) (by norm_num)
theorem B9400205 : Blo 2199435 9400205 := bstep (se 3 (by rfl) ⟨1762538, by rfl⟩ : syracuseStep 9400205 = 3525077) B3525077
theorem B6266803 : Blo 2199435 6266803 := bstep (se 1 (by rfl) ⟨4700102, by rfl⟩ : syracuseStep 6266803 = 9400205) B9400205
theorem B8355737 : Blo 2199435 8355737 := bstep (se 2 (by rfl) ⟨3133401, by rfl⟩ : syracuseStep 8355737 = 6266803) B6266803
theorem B5570491 : Blo 2199435 5570491 := bstep (se 1 (by rfl) ⟨4177868, by rfl⟩ : syracuseStep 5570491 = 8355737) B8355737
theorem B7427321 : Blo 2199435 7427321 := bstep (se 2 (by rfl) ⟨2785245, by rfl⟩ : syracuseStep 7427321 = 5570491) B5570491
theorem B4951547 : Blo 2199435 4951547 := bstep (se 1 (by rfl) ⟨3713660, by rfl⟩ : syracuseStep 4951547 = 7427321) B7427321
theorem B3301031 : Blo 2199435 3301031 := bstep (se 1 (by rfl) ⟨2475773, by rfl⟩ : syracuseStep 3301031 = 4951547) B4951547
theorem B2200687 : Blo 2199435 2200687 := bstep (se 1 (by rfl) ⟨1650515, by rfl⟩ : syracuseStep 2200687 = 3301031) B3301031
theorem B3301037 : Blo 2199435 3301037 := bbase (se 3 (by rfl) ⟨618944, by rfl⟩ : syracuseStep 3301037 = 1237889) (by norm_num)
theorem B2200691 : Blo 2199435 2200691 := bstep (se 1 (by rfl) ⟨1650518, by rfl⟩ : syracuseStep 2200691 = 3301037) B3301037
theorem B4951565 : Blo 2199435 4951565 := bbase (se 3 (by rfl) ⟨928418, by rfl⟩ : syracuseStep 4951565 = 1856837) (by norm_num)
theorem B3301043 : Blo 2199435 3301043 := bstep (se 1 (by rfl) ⟨2475782, by rfl⟩ : syracuseStep 3301043 = 4951565) B4951565
theorem B2200695 : Blo 2199435 2200695 := bstep (se 1 (by rfl) ⟨1650521, by rfl⟩ : syracuseStep 2200695 = 3301043) B3301043
theorem B2785261 : Blo 2199435 2785261 := bbase (se 3 (by rfl) ⟨522236, by rfl⟩ : syracuseStep 2785261 = 1044473) (by norm_num)
theorem B3713681 : Blo 2199435 3713681 := bstep (se 2 (by rfl) ⟨1392630, by rfl⟩ : syracuseStep 3713681 = 2785261) B2785261
theorem B2475787 : Blo 2199435 2475787 := bstep (se 1 (by rfl) ⟨1856840, by rfl⟩ : syracuseStep 2475787 = 3713681) B3713681
theorem B3301049 : Blo 2199435 3301049 := bstep (se 2 (by rfl) ⟨1237893, by rfl⟩ : syracuseStep 3301049 = 2475787) B2475787
theorem B2200699 : Blo 2199435 2200699 := bstep (se 1 (by rfl) ⟨1650524, by rfl⟩ : syracuseStep 2200699 = 3301049) B3301049
theorem B2230729 : Blo 2199435 2230729 := bbase (se 2 (by rfl) ⟨836523, by rfl⟩ : syracuseStep 2230729 = 1673047) (by norm_num)
theorem B11897221 : Blo 2199435 11897221 := bstep (se 4 (by rfl) ⟨1115364, by rfl⟩ : syracuseStep 11897221 = 2230729) B2230729
theorem B15862961 : Blo 2199435 15862961 := bstep (se 2 (by rfl) ⟨5948610, by rfl⟩ : syracuseStep 15862961 = 11897221) B11897221
theorem B10575307 : Blo 2199435 10575307 := bstep (se 1 (by rfl) ⟨7931480, by rfl⟩ : syracuseStep 10575307 = 15862961) B15862961
theorem B14100409 : Blo 2199435 14100409 := bstep (se 2 (by rfl) ⟨5287653, by rfl⟩ : syracuseStep 14100409 = 10575307) B10575307
theorem B18800545 : Blo 2199435 18800545 := bstep (se 2 (by rfl) ⟨7050204, by rfl⟩ : syracuseStep 18800545 = 14100409) B14100409
theorem B25067393 : Blo 2199435 25067393 := bstep (se 2 (by rfl) ⟨9400272, by rfl⟩ : syracuseStep 25067393 = 18800545) B18800545
theorem B16711595 : Blo 2199435 16711595 := bstep (se 1 (by rfl) ⟨12533696, by rfl⟩ : syracuseStep 16711595 = 25067393) B25067393
theorem B11141063 : Blo 2199435 11141063 := bstep (se 1 (by rfl) ⟨8355797, by rfl⟩ : syracuseStep 11141063 = 16711595) B16711595
theorem B7427375 : Blo 2199435 7427375 := bstep (se 1 (by rfl) ⟨5570531, by rfl⟩ : syracuseStep 7427375 = 11141063) B11141063
theorem B4951583 : Blo 2199435 4951583 := bstep (se 1 (by rfl) ⟨3713687, by rfl⟩ : syracuseStep 4951583 = 7427375) B7427375
theorem B3301055 : Blo 2199435 3301055 := bstep (se 1 (by rfl) ⟨2475791, by rfl⟩ : syracuseStep 3301055 = 4951583) B4951583
theorem B2200703 : Blo 2199435 2200703 := bstep (se 1 (by rfl) ⟨1650527, by rfl⟩ : syracuseStep 2200703 = 3301055) B3301055
theorem B3301061 : Blo 2199435 3301061 := bbase (se 4 (by rfl) ⟨309474, by rfl⟩ : syracuseStep 3301061 = 618949) (by norm_num)
theorem B2200707 : Blo 2199435 2200707 := bstep (se 1 (by rfl) ⟨1650530, by rfl⟩ : syracuseStep 2200707 = 3301061) B3301061
theorem B3713701 : Blo 2199435 3713701 := bbase (se 4 (by rfl) ⟨348159, by rfl⟩ : syracuseStep 3713701 = 696319) (by norm_num)
theorem B4951601 : Blo 2199435 4951601 := bstep (se 2 (by rfl) ⟨1856850, by rfl⟩ : syracuseStep 4951601 = 3713701) B3713701
theorem B3301067 : Blo 2199435 3301067 := bstep (se 1 (by rfl) ⟨2475800, by rfl⟩ : syracuseStep 3301067 = 4951601) B4951601
theorem B2200711 : Blo 2199435 2200711 := bstep (se 1 (by rfl) ⟨1650533, by rfl⟩ : syracuseStep 2200711 = 3301067) B3301067
theorem B2475805 : Blo 2199435 2475805 := bbase (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) (by norm_num)
theorem B3301073 : Blo 2199435 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B2200715 : Blo 2199435 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B7427429 : Blo 2199435 7427429 := bbase (se 4 (by rfl) ⟨696321, by rfl⟩ : syracuseStep 7427429 = 1392643) (by norm_num)
theorem B4951619 : Blo 2199435 4951619 := bstep (se 1 (by rfl) ⟨3713714, by rfl⟩ : syracuseStep 4951619 = 7427429) B7427429
theorem B3301079 : Blo 2199435 3301079 := bstep (se 1 (by rfl) ⟨2475809, by rfl⟩ : syracuseStep 3301079 = 4951619) B4951619
theorem B2200719 : Blo 2199435 2200719 := bstep (se 1 (by rfl) ⟨1650539, by rfl⟩ : syracuseStep 2200719 = 3301079) B3301079
theorem B3301085 : Blo 2199435 3301085 := bbase (se 3 (by rfl) ⟨618953, by rfl⟩ : syracuseStep 3301085 = 1237907) (by norm_num)
theorem B2200723 : Blo 2199435 2200723 := bstep (se 1 (by rfl) ⟨1650542, by rfl⟩ : syracuseStep 2200723 = 3301085) B3301085
theorem B4951637 : Blo 2199435 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B3301091 : Blo 2199435 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B2200727 : Blo 2199435 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B4700197 : Blo 2199435 4700197 := bbase (se 4 (by rfl) ⟨440643, by rfl⟩ : syracuseStep 4700197 = 881287) (by norm_num)
theorem B6266929 : Blo 2199435 6266929 := bstep (se 2 (by rfl) ⟨2350098, by rfl⟩ : syracuseStep 6266929 = 4700197) B4700197
theorem B8355905 : Blo 2199435 8355905 := bstep (se 2 (by rfl) ⟨3133464, by rfl⟩ : syracuseStep 8355905 = 6266929) B6266929
theorem B5570603 : Blo 2199435 5570603 := bstep (se 1 (by rfl) ⟨4177952, by rfl⟩ : syracuseStep 5570603 = 8355905) B8355905
theorem B3713735 : Blo 2199435 3713735 := bstep (se 1 (by rfl) ⟨2785301, by rfl⟩ : syracuseStep 3713735 = 5570603) B5570603
theorem B2475823 : Blo 2199435 2475823 := bstep (se 1 (by rfl) ⟨1856867, by rfl⟩ : syracuseStep 2475823 = 3713735) B3713735
theorem B3301097 : Blo 2199435 3301097 := bstep (se 2 (by rfl) ⟨1237911, by rfl⟩ : syracuseStep 3301097 = 2475823) B2475823
theorem B2200731 : Blo 2199435 2200731 := bstep (se 1 (by rfl) ⟨1650548, by rfl⟩ : syracuseStep 2200731 = 3301097) B3301097
theorem B10575461 : Blo 2199435 10575461 := bbase (se 4 (by rfl) ⟨991449, by rfl⟩ : syracuseStep 10575461 = 1982899) (by norm_num)
theorem B28201229 : Blo 2199435 28201229 := bstep (se 3 (by rfl) ⟨5287730, by rfl⟩ : syracuseStep 28201229 = 10575461) B10575461
theorem B18800819 : Blo 2199435 18800819 := bstep (se 1 (by rfl) ⟨14100614, by rfl⟩ : syracuseStep 18800819 = 28201229) B28201229
theorem B12533879 : Blo 2199435 12533879 := bstep (se 1 (by rfl) ⟨9400409, by rfl⟩ : syracuseStep 12533879 = 18800819) B18800819
theorem B8355919 : Blo 2199435 8355919 := bstep (se 1 (by rfl) ⟨6266939, by rfl⟩ : syracuseStep 8355919 = 12533879) B12533879
theorem B11141225 : Blo 2199435 11141225 := bstep (se 2 (by rfl) ⟨4177959, by rfl⟩ : syracuseStep 11141225 = 8355919) B8355919
theorem B7427483 : Blo 2199435 7427483 := bstep (se 1 (by rfl) ⟨5570612, by rfl⟩ : syracuseStep 7427483 = 11141225) B11141225
theorem B4951655 : Blo 2199435 4951655 := bstep (se 1 (by rfl) ⟨3713741, by rfl⟩ : syracuseStep 4951655 = 7427483) B7427483
theorem B3301103 : Blo 2199435 3301103 := bstep (se 1 (by rfl) ⟨2475827, by rfl⟩ : syracuseStep 3301103 = 4951655) B4951655
theorem B2200735 : Blo 2199435 2200735 := bstep (se 1 (by rfl) ⟨1650551, by rfl⟩ : syracuseStep 2200735 = 3301103) B3301103
theorem B3301109 : Blo 2199435 3301109 := bbase (se 5 (by rfl) ⟨154739, by rfl⟩ : syracuseStep 3301109 = 309479) (by norm_num)
theorem B2200739 : Blo 2199435 2200739 := bstep (se 1 (by rfl) ⟨1650554, by rfl⟩ : syracuseStep 2200739 = 3301109) B3301109
theorem B6352469 : Blo 2199435 6352469 := bbase (se 8 (by rfl) ⟨37221, by rfl⟩ : syracuseStep 6352469 = 74443) (by norm_num)
theorem B4234979 : Blo 2199435 4234979 := bstep (se 1 (by rfl) ⟨3176234, by rfl⟩ : syracuseStep 4234979 = 6352469) B6352469
theorem B2823319 : Blo 2199435 2823319 := bstep (se 1 (by rfl) ⟨2117489, by rfl⟩ : syracuseStep 2823319 = 4234979) B4234979
theorem B15057701 : Blo 2199435 15057701 := bstep (se 4 (by rfl) ⟨1411659, by rfl⟩ : syracuseStep 15057701 = 2823319) B2823319
theorem B10038467 : Blo 2199435 10038467 := bstep (se 1 (by rfl) ⟨7528850, by rfl⟩ : syracuseStep 10038467 = 15057701) B15057701
theorem B6692311 : Blo 2199435 6692311 := bstep (se 1 (by rfl) ⟨5019233, by rfl⟩ : syracuseStep 6692311 = 10038467) B10038467
theorem B8923081 : Blo 2199435 8923081 := bstep (se 2 (by rfl) ⟨3346155, by rfl⟩ : syracuseStep 8923081 = 6692311) B6692311
theorem B11897441 : Blo 2199435 11897441 := bstep (se 2 (by rfl) ⟨4461540, by rfl⟩ : syracuseStep 11897441 = 8923081) B8923081
theorem B7931627 : Blo 2199435 7931627 := bstep (se 1 (by rfl) ⟨5948720, by rfl⟩ : syracuseStep 7931627 = 11897441) B11897441
theorem B5287751 : Blo 2199435 5287751 := bstep (se 1 (by rfl) ⟨3965813, by rfl⟩ : syracuseStep 5287751 = 7931627) B7931627
theorem B3525167 : Blo 2199435 3525167 := bstep (se 1 (by rfl) ⟨2643875, by rfl⟩ : syracuseStep 3525167 = 5287751) B5287751
theorem B9400445 : Blo 2199435 9400445 := bstep (se 3 (by rfl) ⟨1762583, by rfl⟩ : syracuseStep 9400445 = 3525167) B3525167
theorem B6266963 : Blo 2199435 6266963 := bstep (se 1 (by rfl) ⟨4700222, by rfl⟩ : syracuseStep 6266963 = 9400445) B9400445
theorem B4177975 : Blo 2199435 4177975 := bstep (se 1 (by rfl) ⟨3133481, by rfl⟩ : syracuseStep 4177975 = 6266963) B6266963
theorem B5570633 : Blo 2199435 5570633 := bstep (se 2 (by rfl) ⟨2088987, by rfl⟩ : syracuseStep 5570633 = 4177975) B4177975
theorem B3713755 : Blo 2199435 3713755 := bstep (se 1 (by rfl) ⟨2785316, by rfl⟩ : syracuseStep 3713755 = 5570633) B5570633
theorem B4951673 : Blo 2199435 4951673 := bstep (se 2 (by rfl) ⟨1856877, by rfl⟩ : syracuseStep 4951673 = 3713755) B3713755
theorem B3301115 : Blo 2199435 3301115 := bstep (se 1 (by rfl) ⟨2475836, by rfl⟩ : syracuseStep 3301115 = 4951673) B4951673
theorem B2200743 : Blo 2199435 2200743 := bstep (se 1 (by rfl) ⟨1650557, by rfl⟩ : syracuseStep 2200743 = 3301115) B3301115
theorem B2475841 : Blo 2199435 2475841 := bbase (se 2 (by rfl) ⟨928440, by rfl⟩ : syracuseStep 2475841 = 1856881) (by norm_num)
theorem B3301121 : Blo 2199435 3301121 := bstep (se 2 (by rfl) ⟨1237920, by rfl⟩ : syracuseStep 3301121 = 2475841) B2475841
theorem B2200747 : Blo 2199435 2200747 := bstep (se 1 (by rfl) ⟨1650560, by rfl⟩ : syracuseStep 2200747 = 3301121) B3301121
theorem B5570653 : Blo 2199435 5570653 := bbase (se 3 (by rfl) ⟨1044497, by rfl⟩ : syracuseStep 5570653 = 2088995) (by norm_num)
theorem B7427537 : Blo 2199435 7427537 := bstep (se 2 (by rfl) ⟨2785326, by rfl⟩ : syracuseStep 7427537 = 5570653) B5570653
theorem B4951691 : Blo 2199435 4951691 := bstep (se 1 (by rfl) ⟨3713768, by rfl⟩ : syracuseStep 4951691 = 7427537) B7427537
theorem B3301127 : Blo 2199435 3301127 := bstep (se 1 (by rfl) ⟨2475845, by rfl⟩ : syracuseStep 3301127 = 4951691) B4951691
theorem B2200751 : Blo 2199435 2200751 := bstep (se 1 (by rfl) ⟨1650563, by rfl⟩ : syracuseStep 2200751 = 3301127) B3301127
theorem B3301133 : Blo 2199435 3301133 := bbase (se 3 (by rfl) ⟨618962, by rfl⟩ : syracuseStep 3301133 = 1237925) (by norm_num)
theorem B2200755 : Blo 2199435 2200755 := bstep (se 1 (by rfl) ⟨1650566, by rfl⟩ : syracuseStep 2200755 = 3301133) B3301133
theorem B4951709 : Blo 2199435 4951709 := bbase (se 3 (by rfl) ⟨928445, by rfl⟩ : syracuseStep 4951709 = 1856891) (by norm_num)
theorem B3301139 : Blo 2199435 3301139 := bstep (se 1 (by rfl) ⟨2475854, by rfl⟩ : syracuseStep 3301139 = 4951709) B4951709
theorem B2200759 : Blo 2199435 2200759 := bstep (se 1 (by rfl) ⟨1650569, by rfl⟩ : syracuseStep 2200759 = 3301139) B3301139
theorem B3713789 : Blo 2199435 3713789 := bbase (se 3 (by rfl) ⟨696335, by rfl⟩ : syracuseStep 3713789 = 1392671) (by norm_num)
theorem B2475859 : Blo 2199435 2475859 := bstep (se 1 (by rfl) ⟨1856894, by rfl⟩ : syracuseStep 2475859 = 3713789) B3713789
theorem B3301145 : Blo 2199435 3301145 := bstep (se 2 (by rfl) ⟨1237929, by rfl⟩ : syracuseStep 3301145 = 2475859) B2475859
theorem B2200763 : Blo 2199435 2200763 := bstep (se 1 (by rfl) ⟨1650572, by rfl⟩ : syracuseStep 2200763 = 3301145) B3301145
theorem B3525205 : Blo 2199435 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B4700273 : Blo 2199435 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B12534061 : Blo 2199435 12534061 := bstep (se 3 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 12534061 = 4700273) B4700273
theorem B16712081 : Blo 2199435 16712081 := bstep (se 2 (by rfl) ⟨6267030, by rfl⟩ : syracuseStep 16712081 = 12534061) B12534061
theorem B11141387 : Blo 2199435 11141387 := bstep (se 1 (by rfl) ⟨8356040, by rfl⟩ : syracuseStep 11141387 = 16712081) B16712081
theorem B7427591 : Blo 2199435 7427591 := bstep (se 1 (by rfl) ⟨5570693, by rfl⟩ : syracuseStep 7427591 = 11141387) B11141387
theorem B4951727 : Blo 2199435 4951727 := bstep (se 1 (by rfl) ⟨3713795, by rfl⟩ : syracuseStep 4951727 = 7427591) B7427591
theorem B3301151 : Blo 2199435 3301151 := bstep (se 1 (by rfl) ⟨2475863, by rfl⟩ : syracuseStep 3301151 = 4951727) B4951727
theorem B2200767 : Blo 2199435 2200767 := bstep (se 1 (by rfl) ⟨1650575, by rfl⟩ : syracuseStep 2200767 = 3301151) B3301151
theorem B3301157 : Blo 2199435 3301157 := bbase (se 4 (by rfl) ⟨309483, by rfl⟩ : syracuseStep 3301157 = 618967) (by norm_num)
theorem B2200771 : Blo 2199435 2200771 := bstep (se 1 (by rfl) ⟨1650578, by rfl⟩ : syracuseStep 2200771 = 3301157) B3301157
theorem B2785357 : Blo 2199435 2785357 := bbase (se 3 (by rfl) ⟨522254, by rfl⟩ : syracuseStep 2785357 = 1044509) (by norm_num)
theorem B3713809 : Blo 2199435 3713809 := bstep (se 2 (by rfl) ⟨1392678, by rfl⟩ : syracuseStep 3713809 = 2785357) B2785357
theorem B4951745 : Blo 2199435 4951745 := bstep (se 2 (by rfl) ⟨1856904, by rfl⟩ : syracuseStep 4951745 = 3713809) B3713809
theorem B3301163 : Blo 2199435 3301163 := bstep (se 1 (by rfl) ⟨2475872, by rfl⟩ : syracuseStep 3301163 = 4951745) B4951745
theorem B2200775 : Blo 2199435 2200775 := bstep (se 1 (by rfl) ⟨1650581, by rfl⟩ : syracuseStep 2200775 = 3301163) B3301163
theorem B2475877 : Blo 2199435 2475877 := bbase (se 4 (by rfl) ⟨232113, by rfl⟩ : syracuseStep 2475877 = 464227) (by norm_num)
theorem B3301169 : Blo 2199435 3301169 := bstep (se 2 (by rfl) ⟨1237938, by rfl⟩ : syracuseStep 3301169 = 2475877) B2475877
theorem B2200779 : Blo 2199435 2200779 := bstep (se 1 (by rfl) ⟨1650584, by rfl⟩ : syracuseStep 2200779 = 3301169) B3301169
theorem B6267077 : Blo 2199435 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B4178051 : Blo 2199435 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B2785367 : Blo 2199435 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B7427645 : Blo 2199435 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B4951763 : Blo 2199435 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B3301175 : Blo 2199435 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B2200783 : Blo 2199435 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B3301181 : Blo 2199435 3301181 := bbase (se 3 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 3301181 = 1237943) (by norm_num)
theorem B2200787 : Blo 2199435 2200787 := bstep (se 1 (by rfl) ⟨1650590, by rfl⟩ : syracuseStep 2200787 = 3301181) B3301181
theorem B4951781 : Blo 2199435 4951781 := bbase (se 4 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 4951781 = 928459) (by norm_num)
theorem B3301187 : Blo 2199435 3301187 := bstep (se 1 (by rfl) ⟨2475890, by rfl⟩ : syracuseStep 3301187 = 4951781) B4951781
theorem B2200791 : Blo 2199435 2200791 := bstep (se 1 (by rfl) ⟨1650593, by rfl⟩ : syracuseStep 2200791 = 3301187) B3301187
theorem B5570765 : Blo 2199435 5570765 := bbase (se 3 (by rfl) ⟨1044518, by rfl⟩ : syracuseStep 5570765 = 2089037) (by norm_num)
theorem B3713843 : Blo 2199435 3713843 := bstep (se 1 (by rfl) ⟨2785382, by rfl⟩ : syracuseStep 3713843 = 5570765) B5570765
theorem B2475895 : Blo 2199435 2475895 := bstep (se 1 (by rfl) ⟨1856921, by rfl⟩ : syracuseStep 2475895 = 3713843) B3713843
theorem B3301193 : Blo 2199435 3301193 := bstep (se 2 (by rfl) ⟨1237947, by rfl⟩ : syracuseStep 3301193 = 2475895) B2475895
theorem B2200795 : Blo 2199435 2200795 := bstep (se 1 (by rfl) ⟨1650596, by rfl⟩ : syracuseStep 2200795 = 3301193) B3301193
theorem B10038725 : Blo 2199435 10038725 := bbase (se 4 (by rfl) ⟨941130, by rfl⟩ : syracuseStep 10038725 = 1882261) (by norm_num)
theorem B6692483 : Blo 2199435 6692483 := bstep (se 1 (by rfl) ⟨5019362, by rfl⟩ : syracuseStep 6692483 = 10038725) B10038725
theorem B4461655 : Blo 2199435 4461655 := bstep (se 1 (by rfl) ⟨3346241, by rfl⟩ : syracuseStep 4461655 = 6692483) B6692483
theorem B5948873 : Blo 2199435 5948873 := bstep (se 2 (by rfl) ⟨2230827, by rfl⟩ : syracuseStep 5948873 = 4461655) B4461655
theorem B3965915 : Blo 2199435 3965915 := bstep (se 1 (by rfl) ⟨2974436, by rfl⟩ : syracuseStep 3965915 = 5948873) B5948873
theorem B2643943 : Blo 2199435 2643943 := bstep (se 1 (by rfl) ⟨1982957, by rfl⟩ : syracuseStep 2643943 = 3965915) B3965915
theorem B3525257 : Blo 2199435 3525257 := bstep (se 2 (by rfl) ⟨1321971, by rfl⟩ : syracuseStep 3525257 = 2643943) B2643943
theorem B2350171 : Blo 2199435 2350171 := bstep (se 1 (by rfl) ⟨1762628, by rfl⟩ : syracuseStep 2350171 = 3525257) B3525257
theorem B3133561 : Blo 2199435 3133561 := bstep (se 2 (by rfl) ⟨1175085, by rfl⟩ : syracuseStep 3133561 = 2350171) B2350171
theorem B4178081 : Blo 2199435 4178081 := bstep (se 2 (by rfl) ⟨1566780, by rfl⟩ : syracuseStep 4178081 = 3133561) B3133561
theorem B11141549 : Blo 2199435 11141549 := bstep (se 3 (by rfl) ⟨2089040, by rfl⟩ : syracuseStep 11141549 = 4178081) B4178081
theorem B7427699 : Blo 2199435 7427699 := bstep (se 1 (by rfl) ⟨5570774, by rfl⟩ : syracuseStep 7427699 = 11141549) B11141549
theorem B4951799 : Blo 2199435 4951799 := bstep (se 1 (by rfl) ⟨3713849, by rfl⟩ : syracuseStep 4951799 = 7427699) B7427699
theorem B3301199 : Blo 2199435 3301199 := bstep (se 1 (by rfl) ⟨2475899, by rfl⟩ : syracuseStep 3301199 = 4951799) B4951799
theorem B2200799 : Blo 2199435 2200799 := bstep (se 1 (by rfl) ⟨1650599, by rfl⟩ : syracuseStep 2200799 = 3301199) B3301199
theorem B3301205 : Blo 2199435 3301205 := bbase (se 9 (by rfl) ⟨9671, by rfl⟩ : syracuseStep 3301205 = 19343) (by norm_num)
theorem B2200803 : Blo 2199435 2200803 := bstep (se 1 (by rfl) ⟨1650602, by rfl⟩ : syracuseStep 2200803 = 3301205) B3301205
theorem B3346253 : Blo 2199435 3346253 := bbase (se 3 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 3346253 = 1254845) (by norm_num)
theorem B2230835 : Blo 2199435 2230835 := bstep (se 1 (by rfl) ⟨1673126, by rfl⟩ : syracuseStep 2230835 = 3346253) B3346253
theorem B5948893 : Blo 2199435 5948893 := bstep (se 3 (by rfl) ⟨1115417, by rfl⟩ : syracuseStep 5948893 = 2230835) B2230835
theorem B7931857 : Blo 2199435 7931857 := bstep (se 2 (by rfl) ⟨2974446, by rfl⟩ : syracuseStep 7931857 = 5948893) B5948893
theorem B10575809 : Blo 2199435 10575809 := bstep (se 2 (by rfl) ⟨3965928, by rfl⟩ : syracuseStep 10575809 = 7931857) B7931857
theorem B7050539 : Blo 2199435 7050539 := bstep (se 1 (by rfl) ⟨5287904, by rfl⟩ : syracuseStep 7050539 = 10575809) B10575809
theorem B4700359 : Blo 2199435 4700359 := bstep (se 1 (by rfl) ⟨3525269, by rfl⟩ : syracuseStep 4700359 = 7050539) B7050539
theorem B6267145 : Blo 2199435 6267145 := bstep (se 2 (by rfl) ⟨2350179, by rfl⟩ : syracuseStep 6267145 = 4700359) B4700359
theorem B8356193 : Blo 2199435 8356193 := bstep (se 2 (by rfl) ⟨3133572, by rfl⟩ : syracuseStep 8356193 = 6267145) B6267145
theorem B5570795 : Blo 2199435 5570795 := bstep (se 1 (by rfl) ⟨4178096, by rfl⟩ : syracuseStep 5570795 = 8356193) B8356193
theorem B3713863 : Blo 2199435 3713863 := bstep (se 1 (by rfl) ⟨2785397, by rfl⟩ : syracuseStep 3713863 = 5570795) B5570795
theorem B4951817 : Blo 2199435 4951817 := bstep (se 2 (by rfl) ⟨1856931, by rfl⟩ : syracuseStep 4951817 = 3713863) B3713863
theorem B3301211 : Blo 2199435 3301211 := bstep (se 1 (by rfl) ⟨2475908, by rfl⟩ : syracuseStep 3301211 = 4951817) B4951817
theorem B2200807 : Blo 2199435 2200807 := bstep (se 1 (by rfl) ⟨1650605, by rfl⟩ : syracuseStep 2200807 = 3301211) B3301211
theorem B2475913 : Blo 2199435 2475913 := bbase (se 2 (by rfl) ⟨928467, by rfl⟩ : syracuseStep 2475913 = 1856935) (by norm_num)
theorem B3301217 : Blo 2199435 3301217 := bstep (se 2 (by rfl) ⟨1237956, by rfl⟩ : syracuseStep 3301217 = 2475913) B2475913
theorem B2200811 : Blo 2199435 2200811 := bstep (se 1 (by rfl) ⟨1650608, by rfl⟩ : syracuseStep 2200811 = 3301217) B3301217
theorem B4461685 : Blo 2199435 4461685 := bbase (se 5 (by rfl) ⟨209141, by rfl⟩ : syracuseStep 4461685 = 418283) (by norm_num)
theorem B95182613 : Blo 2199435 95182613 := bstep (se 6 (by rfl) ⟨2230842, by rfl⟩ : syracuseStep 95182613 = 4461685) B4461685
theorem B63455075 : Blo 2199435 63455075 := bstep (se 1 (by rfl) ⟨47591306, by rfl⟩ : syracuseStep 63455075 = 95182613) B95182613
theorem B42303383 : Blo 2199435 42303383 := bstep (se 1 (by rfl) ⟨31727537, by rfl⟩ : syracuseStep 42303383 = 63455075) B63455075
theorem B28202255 : Blo 2199435 28202255 := bstep (se 1 (by rfl) ⟨21151691, by rfl⟩ : syracuseStep 28202255 = 42303383) B42303383
theorem B18801503 : Blo 2199435 18801503 := bstep (se 1 (by rfl) ⟨14101127, by rfl⟩ : syracuseStep 18801503 = 28202255) B28202255
theorem B12534335 : Blo 2199435 12534335 := bstep (se 1 (by rfl) ⟨9400751, by rfl⟩ : syracuseStep 12534335 = 18801503) B18801503
theorem B8356223 : Blo 2199435 8356223 := bstep (se 1 (by rfl) ⟨6267167, by rfl⟩ : syracuseStep 8356223 = 12534335) B12534335
theorem B5570815 : Blo 2199435 5570815 := bstep (se 1 (by rfl) ⟨4178111, by rfl⟩ : syracuseStep 5570815 = 8356223) B8356223
theorem B7427753 : Blo 2199435 7427753 := bstep (se 2 (by rfl) ⟨2785407, by rfl⟩ : syracuseStep 7427753 = 5570815) B5570815
theorem B4951835 : Blo 2199435 4951835 := bstep (se 1 (by rfl) ⟨3713876, by rfl⟩ : syracuseStep 4951835 = 7427753) B7427753
theorem B3301223 : Blo 2199435 3301223 := bstep (se 1 (by rfl) ⟨2475917, by rfl⟩ : syracuseStep 3301223 = 4951835) B4951835
theorem B2200815 : Blo 2199435 2200815 := bstep (se 1 (by rfl) ⟨1650611, by rfl⟩ : syracuseStep 2200815 = 3301223) B3301223
theorem B3301229 : Blo 2199435 3301229 := bbase (se 3 (by rfl) ⟨618980, by rfl⟩ : syracuseStep 3301229 = 1237961) (by norm_num)
theorem B2200819 : Blo 2199435 2200819 := bstep (se 1 (by rfl) ⟨1650614, by rfl⟩ : syracuseStep 2200819 = 3301229) B3301229
theorem B4951853 : Blo 2199435 4951853 := bbase (se 3 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 4951853 = 1856945) (by norm_num)
theorem B3301235 : Blo 2199435 3301235 := bstep (se 1 (by rfl) ⟨2475926, by rfl⟩ : syracuseStep 3301235 = 4951853) B4951853
theorem B2200823 : Blo 2199435 2200823 := bstep (se 1 (by rfl) ⟨1650617, by rfl⟩ : syracuseStep 2200823 = 3301235) B3301235
theorem B9400805 : Blo 2199435 9400805 := bbase (se 4 (by rfl) ⟨881325, by rfl⟩ : syracuseStep 9400805 = 1762651) (by norm_num)
theorem B6267203 : Blo 2199435 6267203 := bstep (se 1 (by rfl) ⟨4700402, by rfl⟩ : syracuseStep 6267203 = 9400805) B9400805
theorem B4178135 : Blo 2199435 4178135 := bstep (se 1 (by rfl) ⟨3133601, by rfl⟩ : syracuseStep 4178135 = 6267203) B6267203
theorem B2785423 : Blo 2199435 2785423 := bstep (se 1 (by rfl) ⟨2089067, by rfl⟩ : syracuseStep 2785423 = 4178135) B4178135
theorem B3713897 : Blo 2199435 3713897 := bstep (se 2 (by rfl) ⟨1392711, by rfl⟩ : syracuseStep 3713897 = 2785423) B2785423
theorem B2475931 : Blo 2199435 2475931 := bstep (se 1 (by rfl) ⟨1856948, by rfl⟩ : syracuseStep 2475931 = 3713897) B3713897
theorem B3301241 : Blo 2199435 3301241 := bstep (se 2 (by rfl) ⟨1237965, by rfl⟩ : syracuseStep 3301241 = 2475931) B2475931
theorem B2200827 : Blo 2199435 2200827 := bstep (se 1 (by rfl) ⟨1650620, by rfl⟩ : syracuseStep 2200827 = 3301241) B3301241
theorem B2509717 : Blo 2199435 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B3346289 : Blo 2199435 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B2230859 : Blo 2199435 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B5948957 : Blo 2199435 5948957 := bstep (se 3 (by rfl) ⟨1115429, by rfl⟩ : syracuseStep 5948957 = 2230859) B2230859
theorem B3965971 : Blo 2199435 3965971 := bstep (se 1 (by rfl) ⟨2974478, by rfl⟩ : syracuseStep 3965971 = 5948957) B5948957
theorem B5287961 : Blo 2199435 5287961 := bstep (se 2 (by rfl) ⟨1982985, by rfl⟩ : syracuseStep 5287961 = 3965971) B3965971
theorem B14101229 : Blo 2199435 14101229 := bstep (se 3 (by rfl) ⟨2643980, by rfl⟩ : syracuseStep 14101229 = 5287961) B5287961
theorem B37603277 : Blo 2199435 37603277 := bstep (se 3 (by rfl) ⟨7050614, by rfl⟩ : syracuseStep 37603277 = 14101229) B14101229
theorem B25068851 : Blo 2199435 25068851 := bstep (se 1 (by rfl) ⟨18801638, by rfl⟩ : syracuseStep 25068851 = 37603277) B37603277
theorem B16712567 : Blo 2199435 16712567 := bstep (se 1 (by rfl) ⟨12534425, by rfl⟩ : syracuseStep 16712567 = 25068851) B25068851
theorem B11141711 : Blo 2199435 11141711 := bstep (se 1 (by rfl) ⟨8356283, by rfl⟩ : syracuseStep 11141711 = 16712567) B16712567
theorem B7427807 : Blo 2199435 7427807 := bstep (se 1 (by rfl) ⟨5570855, by rfl⟩ : syracuseStep 7427807 = 11141711) B11141711
theorem B4951871 : Blo 2199435 4951871 := bstep (se 1 (by rfl) ⟨3713903, by rfl⟩ : syracuseStep 4951871 = 7427807) B7427807
theorem B3301247 : Blo 2199435 3301247 := bstep (se 1 (by rfl) ⟨2475935, by rfl⟩ : syracuseStep 3301247 = 4951871) B4951871
theorem B2200831 : Blo 2199435 2200831 := bstep (se 1 (by rfl) ⟨1650623, by rfl⟩ : syracuseStep 2200831 = 3301247) B3301247
theorem B3301253 : Blo 2199435 3301253 := bbase (se 4 (by rfl) ⟨309492, by rfl⟩ : syracuseStep 3301253 = 618985) (by norm_num)
theorem B2200835 : Blo 2199435 2200835 := bstep (se 1 (by rfl) ⟨1650626, by rfl⟩ : syracuseStep 2200835 = 3301253) B3301253
theorem B3713917 : Blo 2199435 3713917 := bbase (se 3 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 3713917 = 1392719) (by norm_num)
theorem B4951889 : Blo 2199435 4951889 := bstep (se 2 (by rfl) ⟨1856958, by rfl⟩ : syracuseStep 4951889 = 3713917) B3713917
theorem B3301259 : Blo 2199435 3301259 := bstep (se 1 (by rfl) ⟨2475944, by rfl⟩ : syracuseStep 3301259 = 4951889) B4951889
theorem B2200839 : Blo 2199435 2200839 := bstep (se 1 (by rfl) ⟨1650629, by rfl⟩ : syracuseStep 2200839 = 3301259) B3301259
theorem B2475949 : Blo 2199435 2475949 := bbase (se 3 (by rfl) ⟨464240, by rfl⟩ : syracuseStep 2475949 = 928481) (by norm_num)
theorem B3301265 : Blo 2199435 3301265 := bstep (se 2 (by rfl) ⟨1237974, by rfl⟩ : syracuseStep 3301265 = 2475949) B2475949
theorem B2200843 : Blo 2199435 2200843 := bstep (se 1 (by rfl) ⟨1650632, by rfl⟩ : syracuseStep 2200843 = 3301265) B3301265
theorem B7427861 : Blo 2199435 7427861 := bbase (se 6 (by rfl) ⟨174090, by rfl⟩ : syracuseStep 7427861 = 348181) (by norm_num)
theorem B4951907 : Blo 2199435 4951907 := bstep (se 1 (by rfl) ⟨3713930, by rfl⟩ : syracuseStep 4951907 = 7427861) B7427861
theorem B3301271 : Blo 2199435 3301271 := bstep (se 1 (by rfl) ⟨2475953, by rfl⟩ : syracuseStep 3301271 = 4951907) B4951907
theorem B2200847 : Blo 2199435 2200847 := bstep (se 1 (by rfl) ⟨1650635, by rfl⟩ : syracuseStep 2200847 = 3301271) B3301271
theorem B3301277 : Blo 2199435 3301277 := bbase (se 3 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 3301277 = 1237979) (by norm_num)
theorem B2200851 : Blo 2199435 2200851 := bstep (se 1 (by rfl) ⟨1650638, by rfl⟩ : syracuseStep 2200851 = 3301277) B3301277
theorem B4951925 : Blo 2199435 4951925 := bbase (se 5 (by rfl) ⟨232121, by rfl⟩ : syracuseStep 4951925 = 464243) (by norm_num)
theorem B3301283 : Blo 2199435 3301283 := bstep (se 1 (by rfl) ⟨2475962, by rfl⟩ : syracuseStep 3301283 = 4951925) B4951925
theorem B2200855 : Blo 2199435 2200855 := bstep (se 1 (by rfl) ⟨1650641, by rfl⟩ : syracuseStep 2200855 = 3301283) B3301283
theorem B21152117 : Blo 2199435 21152117 := bbase (se 5 (by rfl) ⟨991505, by rfl⟩ : syracuseStep 21152117 = 1983011) (by norm_num)
theorem B14101411 : Blo 2199435 14101411 := bstep (se 1 (by rfl) ⟨10576058, by rfl⟩ : syracuseStep 14101411 = 21152117) B21152117
theorem B18801881 : Blo 2199435 18801881 := bstep (se 2 (by rfl) ⟨7050705, by rfl⟩ : syracuseStep 18801881 = 14101411) B14101411
theorem B12534587 : Blo 2199435 12534587 := bstep (se 1 (by rfl) ⟨9400940, by rfl⟩ : syracuseStep 12534587 = 18801881) B18801881
theorem B8356391 : Blo 2199435 8356391 := bstep (se 1 (by rfl) ⟨6267293, by rfl⟩ : syracuseStep 8356391 = 12534587) B12534587
theorem B5570927 : Blo 2199435 5570927 := bstep (se 1 (by rfl) ⟨4178195, by rfl⟩ : syracuseStep 5570927 = 8356391) B8356391
theorem B3713951 : Blo 2199435 3713951 := bstep (se 1 (by rfl) ⟨2785463, by rfl⟩ : syracuseStep 3713951 = 5570927) B5570927
theorem B2475967 : Blo 2199435 2475967 := bstep (se 1 (by rfl) ⟨1856975, by rfl⟩ : syracuseStep 2475967 = 3713951) B3713951
theorem B3301289 : Blo 2199435 3301289 := bstep (se 2 (by rfl) ⟨1237983, by rfl⟩ : syracuseStep 3301289 = 2475967) B2475967
theorem B2200859 : Blo 2199435 2200859 := bstep (se 1 (by rfl) ⟨1650644, by rfl⟩ : syracuseStep 2200859 = 3301289) B3301289
theorem B8356405 : Blo 2199435 8356405 := bbase (se 5 (by rfl) ⟨391706, by rfl⟩ : syracuseStep 8356405 = 783413) (by norm_num)
theorem B11141873 : Blo 2199435 11141873 := bstep (se 2 (by rfl) ⟨4178202, by rfl⟩ : syracuseStep 11141873 = 8356405) B8356405
theorem B7427915 : Blo 2199435 7427915 := bstep (se 1 (by rfl) ⟨5570936, by rfl⟩ : syracuseStep 7427915 = 11141873) B11141873
theorem B4951943 : Blo 2199435 4951943 := bstep (se 1 (by rfl) ⟨3713957, by rfl⟩ : syracuseStep 4951943 = 7427915) B7427915
theorem B3301295 : Blo 2199435 3301295 := bstep (se 1 (by rfl) ⟨2475971, by rfl⟩ : syracuseStep 3301295 = 4951943) B4951943
theorem B2200863 : Blo 2199435 2200863 := bstep (se 1 (by rfl) ⟨1650647, by rfl⟩ : syracuseStep 2200863 = 3301295) B3301295
theorem B3301301 : Blo 2199435 3301301 := bbase (se 5 (by rfl) ⟨154748, by rfl⟩ : syracuseStep 3301301 = 309497) (by norm_num)
theorem B2200867 : Blo 2199435 2200867 := bstep (se 1 (by rfl) ⟨1650650, by rfl⟩ : syracuseStep 2200867 = 3301301) B3301301
theorem B5570957 : Blo 2199435 5570957 := bbase (se 3 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 5570957 = 2089109) (by norm_num)
theorem B3713971 : Blo 2199435 3713971 := bstep (se 1 (by rfl) ⟨2785478, by rfl⟩ : syracuseStep 3713971 = 5570957) B5570957
theorem B4951961 : Blo 2199435 4951961 := bstep (se 2 (by rfl) ⟨1856985, by rfl⟩ : syracuseStep 4951961 = 3713971) B3713971
theorem B3301307 : Blo 2199435 3301307 := bstep (se 1 (by rfl) ⟨2475980, by rfl⟩ : syracuseStep 3301307 = 4951961) B4951961
theorem B2200871 : Blo 2199435 2200871 := bstep (se 1 (by rfl) ⟨1650653, by rfl⟩ : syracuseStep 2200871 = 3301307) B3301307
theorem B2475985 : Blo 2199435 2475985 := bbase (se 2 (by rfl) ⟨928494, by rfl⟩ : syracuseStep 2475985 = 1856989) (by norm_num)
theorem B3301313 : Blo 2199435 3301313 := bstep (se 2 (by rfl) ⟨1237992, by rfl⟩ : syracuseStep 3301313 = 2475985) B2475985
theorem B2200875 : Blo 2199435 2200875 := bstep (se 1 (by rfl) ⟨1650656, by rfl⟩ : syracuseStep 2200875 = 3301313) B3301313
theorem B5646989 : Blo 2199435 5646989 := bbase (se 3 (by rfl) ⟨1058810, by rfl⟩ : syracuseStep 5646989 = 2117621) (by norm_num)
theorem B3764659 : Blo 2199435 3764659 := bstep (se 1 (by rfl) ⟨2823494, by rfl⟩ : syracuseStep 3764659 = 5646989) B5646989
theorem B5019545 : Blo 2199435 5019545 := bstep (se 2 (by rfl) ⟨1882329, by rfl⟩ : syracuseStep 5019545 = 3764659) B3764659
theorem B3346363 : Blo 2199435 3346363 := bstep (se 1 (by rfl) ⟨2509772, by rfl⟩ : syracuseStep 3346363 = 5019545) B5019545
theorem B4461817 : Blo 2199435 4461817 := bstep (se 2 (by rfl) ⟨1673181, by rfl⟩ : syracuseStep 4461817 = 3346363) B3346363
theorem B5949089 : Blo 2199435 5949089 := bstep (se 2 (by rfl) ⟨2230908, by rfl⟩ : syracuseStep 5949089 = 4461817) B4461817
theorem B3966059 : Blo 2199435 3966059 := bstep (se 1 (by rfl) ⟨2974544, by rfl⟩ : syracuseStep 3966059 = 5949089) B5949089
theorem B2644039 : Blo 2199435 2644039 := bstep (se 1 (by rfl) ⟨1983029, by rfl⟩ : syracuseStep 2644039 = 3966059) B3966059
theorem B3525385 : Blo 2199435 3525385 := bstep (se 2 (by rfl) ⟨1322019, by rfl⟩ : syracuseStep 3525385 = 2644039) B2644039
theorem B4700513 : Blo 2199435 4700513 := bstep (se 2 (by rfl) ⟨1762692, by rfl⟩ : syracuseStep 4700513 = 3525385) B3525385
theorem B3133675 : Blo 2199435 3133675 := bstep (se 1 (by rfl) ⟨2350256, by rfl⟩ : syracuseStep 3133675 = 4700513) B4700513
theorem B4178233 : Blo 2199435 4178233 := bstep (se 2 (by rfl) ⟨1566837, by rfl⟩ : syracuseStep 4178233 = 3133675) B3133675
theorem B5570977 : Blo 2199435 5570977 := bstep (se 2 (by rfl) ⟨2089116, by rfl⟩ : syracuseStep 5570977 = 4178233) B4178233
theorem B7427969 : Blo 2199435 7427969 := bstep (se 2 (by rfl) ⟨2785488, by rfl⟩ : syracuseStep 7427969 = 5570977) B5570977
theorem B4951979 : Blo 2199435 4951979 := bstep (se 1 (by rfl) ⟨3713984, by rfl⟩ : syracuseStep 4951979 = 7427969) B7427969
theorem B3301319 : Blo 2199435 3301319 := bstep (se 1 (by rfl) ⟨2475989, by rfl⟩ : syracuseStep 3301319 = 4951979) B4951979
theorem B2200879 : Blo 2199435 2200879 := bstep (se 1 (by rfl) ⟨1650659, by rfl⟩ : syracuseStep 2200879 = 3301319) B3301319
theorem B3301325 : Blo 2199435 3301325 := bbase (se 3 (by rfl) ⟨618998, by rfl⟩ : syracuseStep 3301325 = 1237997) (by norm_num)
theorem B2200883 : Blo 2199435 2200883 := bstep (se 1 (by rfl) ⟨1650662, by rfl⟩ : syracuseStep 2200883 = 3301325) B3301325
theorem B4951997 : Blo 2199435 4951997 := bbase (se 3 (by rfl) ⟨928499, by rfl⟩ : syracuseStep 4951997 = 1856999) (by norm_num)
theorem B3301331 : Blo 2199435 3301331 := bstep (se 1 (by rfl) ⟨2475998, by rfl⟩ : syracuseStep 3301331 = 4951997) B4951997
theorem B2200887 : Blo 2199435 2200887 := bstep (se 1 (by rfl) ⟨1650665, by rfl⟩ : syracuseStep 2200887 = 3301331) B3301331
theorem B3714005 : Blo 2199435 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B2476003 : Blo 2199435 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B3301337 : Blo 2199435 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B2200891 : Blo 2199435 2200891 := bstep (se 1 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 2200891 = 3301337) B3301337
theorem B9401093 : Blo 2199435 9401093 := bbase (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) (by norm_num)
theorem B6267395 : Blo 2199435 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B16713053 : Blo 2199435 16713053 := bstep (se 3 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 16713053 = 6267395) B6267395
theorem B11142035 : Blo 2199435 11142035 := bstep (se 1 (by rfl) ⟨8356526, by rfl⟩ : syracuseStep 11142035 = 16713053) B16713053
theorem B7428023 : Blo 2199435 7428023 := bstep (se 1 (by rfl) ⟨5571017, by rfl⟩ : syracuseStep 7428023 = 11142035) B11142035
theorem B4952015 : Blo 2199435 4952015 := bstep (se 1 (by rfl) ⟨3714011, by rfl⟩ : syracuseStep 4952015 = 7428023) B7428023
theorem B3301343 : Blo 2199435 3301343 := bstep (se 1 (by rfl) ⟨2476007, by rfl⟩ : syracuseStep 3301343 = 4952015) B4952015
theorem B2200895 : Blo 2199435 2200895 := bstep (se 1 (by rfl) ⟨1650671, by rfl⟩ : syracuseStep 2200895 = 3301343) B3301343
theorem B3301349 : Blo 2199435 3301349 := bbase (se 4 (by rfl) ⟨309501, by rfl⟩ : syracuseStep 3301349 = 619003) (by norm_num)
theorem B2200899 : Blo 2199435 2200899 := bstep (se 1 (by rfl) ⟨1650674, by rfl⟩ : syracuseStep 2200899 = 3301349) B3301349
theorem B9529397 : Blo 2199435 9529397 := bbase (se 5 (by rfl) ⟨446690, by rfl⟩ : syracuseStep 9529397 = 893381) (by norm_num)
theorem B6352931 : Blo 2199435 6352931 := bstep (se 1 (by rfl) ⟨4764698, by rfl⟩ : syracuseStep 6352931 = 9529397) B9529397
theorem B4235287 : Blo 2199435 4235287 := bstep (se 1 (by rfl) ⟨3176465, by rfl⟩ : syracuseStep 4235287 = 6352931) B6352931
theorem B5647049 : Blo 2199435 5647049 := bstep (se 2 (by rfl) ⟨2117643, by rfl⟩ : syracuseStep 5647049 = 4235287) B4235287
theorem B3764699 : Blo 2199435 3764699 := bstep (se 1 (by rfl) ⟨2823524, by rfl⟩ : syracuseStep 3764699 = 5647049) B5647049
theorem B2509799 : Blo 2199435 2509799 := bstep (se 1 (by rfl) ⟨1882349, by rfl⟩ : syracuseStep 2509799 = 3764699) B3764699
theorem B6692797 : Blo 2199435 6692797 := bstep (se 3 (by rfl) ⟨1254899, by rfl⟩ : syracuseStep 6692797 = 2509799) B2509799
theorem B35694917 : Blo 2199435 35694917 := bstep (se 4 (by rfl) ⟨3346398, by rfl⟩ : syracuseStep 35694917 = 6692797) B6692797
theorem B23796611 : Blo 2199435 23796611 := bstep (se 1 (by rfl) ⟨17847458, by rfl⟩ : syracuseStep 23796611 = 35694917) B35694917
theorem B15864407 : Blo 2199435 15864407 := bstep (se 1 (by rfl) ⟨11898305, by rfl⟩ : syracuseStep 15864407 = 23796611) B23796611
theorem B10576271 : Blo 2199435 10576271 := bstep (se 1 (by rfl) ⟨7932203, by rfl⟩ : syracuseStep 10576271 = 15864407) B15864407
theorem B7050847 : Blo 2199435 7050847 := bstep (se 1 (by rfl) ⟨5288135, by rfl⟩ : syracuseStep 7050847 = 10576271) B10576271
theorem B9401129 : Blo 2199435 9401129 := bstep (se 2 (by rfl) ⟨3525423, by rfl⟩ : syracuseStep 9401129 = 7050847) B7050847
theorem B6267419 : Blo 2199435 6267419 := bstep (se 1 (by rfl) ⟨4700564, by rfl⟩ : syracuseStep 6267419 = 9401129) B9401129
theorem B4178279 : Blo 2199435 4178279 := bstep (se 1 (by rfl) ⟨3133709, by rfl⟩ : syracuseStep 4178279 = 6267419) B6267419
theorem B2785519 : Blo 2199435 2785519 := bstep (se 1 (by rfl) ⟨2089139, by rfl⟩ : syracuseStep 2785519 = 4178279) B4178279
theorem B3714025 : Blo 2199435 3714025 := bstep (se 2 (by rfl) ⟨1392759, by rfl⟩ : syracuseStep 3714025 = 2785519) B2785519
theorem B4952033 : Blo 2199435 4952033 := bstep (se 2 (by rfl) ⟨1857012, by rfl⟩ : syracuseStep 4952033 = 3714025) B3714025
theorem B3301355 : Blo 2199435 3301355 := bstep (se 1 (by rfl) ⟨2476016, by rfl⟩ : syracuseStep 3301355 = 4952033) B4952033
theorem B2200903 : Blo 2199435 2200903 := bstep (se 1 (by rfl) ⟨1650677, by rfl⟩ : syracuseStep 2200903 = 3301355) B3301355
theorem B2476021 : Blo 2199435 2476021 := bbase (se 5 (by rfl) ⟨116063, by rfl⟩ : syracuseStep 2476021 = 232127) (by norm_num)
theorem B3301361 : Blo 2199435 3301361 := bstep (se 2 (by rfl) ⟨1238010, by rfl⟩ : syracuseStep 3301361 = 2476021) B2476021
theorem B2200907 : Blo 2199435 2200907 := bstep (se 1 (by rfl) ⟨1650680, by rfl⟩ : syracuseStep 2200907 = 3301361) B3301361
theorem B2785529 : Blo 2199435 2785529 := bbase (se 2 (by rfl) ⟨1044573, by rfl⟩ : syracuseStep 2785529 = 2089147) (by norm_num)
theorem B7428077 : Blo 2199435 7428077 := bstep (se 3 (by rfl) ⟨1392764, by rfl⟩ : syracuseStep 7428077 = 2785529) B2785529
theorem B4952051 : Blo 2199435 4952051 := bstep (se 1 (by rfl) ⟨3714038, by rfl⟩ : syracuseStep 4952051 = 7428077) B7428077
theorem B3301367 : Blo 2199435 3301367 := bstep (se 1 (by rfl) ⟨2476025, by rfl⟩ : syracuseStep 3301367 = 4952051) B4952051
theorem B2200911 : Blo 2199435 2200911 := bstep (se 1 (by rfl) ⟨1650683, by rfl⟩ : syracuseStep 2200911 = 3301367) B3301367
theorem B3301373 : Blo 2199435 3301373 := bbase (se 3 (by rfl) ⟨619007, by rfl⟩ : syracuseStep 3301373 = 1238015) (by norm_num)
theorem B2200915 : Blo 2199435 2200915 := bstep (se 1 (by rfl) ⟨1650686, by rfl⟩ : syracuseStep 2200915 = 3301373) B3301373
theorem B4952069 : Blo 2199435 4952069 := bbase (se 4 (by rfl) ⟨464256, by rfl⟩ : syracuseStep 4952069 = 928513) (by norm_num)
theorem B3301379 : Blo 2199435 3301379 := bstep (se 1 (by rfl) ⟨2476034, by rfl⟩ : syracuseStep 3301379 = 4952069) B4952069
theorem B2200919 : Blo 2199435 2200919 := bstep (se 1 (by rfl) ⟨1650689, by rfl⟩ : syracuseStep 2200919 = 3301379) B3301379
theorem B4178317 : Blo 2199435 4178317 := bbase (se 3 (by rfl) ⟨783434, by rfl⟩ : syracuseStep 4178317 = 1566869) (by norm_num)
theorem B5571089 : Blo 2199435 5571089 := bstep (se 2 (by rfl) ⟨2089158, by rfl⟩ : syracuseStep 5571089 = 4178317) B4178317
theorem B3714059 : Blo 2199435 3714059 := bstep (se 1 (by rfl) ⟨2785544, by rfl⟩ : syracuseStep 3714059 = 5571089) B5571089
theorem B2476039 : Blo 2199435 2476039 := bstep (se 1 (by rfl) ⟨1857029, by rfl⟩ : syracuseStep 2476039 = 3714059) B3714059
theorem B3301385 : Blo 2199435 3301385 := bstep (se 2 (by rfl) ⟨1238019, by rfl⟩ : syracuseStep 3301385 = 2476039) B2476039
theorem B2200923 : Blo 2199435 2200923 := bstep (se 1 (by rfl) ⟨1650692, by rfl⟩ : syracuseStep 2200923 = 3301385) B3301385
theorem B11142197 : Blo 2199435 11142197 := bbase (se 5 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 11142197 = 1044581) (by norm_num)
theorem B7428131 : Blo 2199435 7428131 := bstep (se 1 (by rfl) ⟨5571098, by rfl⟩ : syracuseStep 7428131 = 11142197) B11142197
theorem B4952087 : Blo 2199435 4952087 := bstep (se 1 (by rfl) ⟨3714065, by rfl⟩ : syracuseStep 4952087 = 7428131) B7428131
theorem B3301391 : Blo 2199435 3301391 := bstep (se 1 (by rfl) ⟨2476043, by rfl⟩ : syracuseStep 3301391 = 4952087) B4952087
theorem B2200927 : Blo 2199435 2200927 := bstep (se 1 (by rfl) ⟨1650695, by rfl⟩ : syracuseStep 2200927 = 3301391) B3301391
theorem B3301397 : Blo 2199435 3301397 := bbase (se 6 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 3301397 = 154753) (by norm_num)
theorem B2200931 : Blo 2199435 2200931 := bstep (se 1 (by rfl) ⟨1650698, by rfl⟩ : syracuseStep 2200931 = 3301397) B3301397
theorem B2823565 : Blo 2199435 2823565 := bbase (se 3 (by rfl) ⟨529418, by rfl⟩ : syracuseStep 2823565 = 1058837) (by norm_num)
theorem B3764753 : Blo 2199435 3764753 := bstep (se 2 (by rfl) ⟨1411782, by rfl⟩ : syracuseStep 3764753 = 2823565) B2823565
theorem B2509835 : Blo 2199435 2509835 := bstep (se 1 (by rfl) ⟨1882376, by rfl⟩ : syracuseStep 2509835 = 3764753) B3764753
theorem B26771573 : Blo 2199435 26771573 := bstep (se 5 (by rfl) ⟨1254917, by rfl⟩ : syracuseStep 26771573 = 2509835) B2509835
theorem B17847715 : Blo 2199435 17847715 := bstep (se 1 (by rfl) ⟨13385786, by rfl⟩ : syracuseStep 17847715 = 26771573) B26771573
theorem B23796953 : Blo 2199435 23796953 := bstep (se 2 (by rfl) ⟨8923857, by rfl⟩ : syracuseStep 23796953 = 17847715) B17847715
theorem B15864635 : Blo 2199435 15864635 := bstep (se 1 (by rfl) ⟨11898476, by rfl⟩ : syracuseStep 15864635 = 23796953) B23796953
theorem B10576423 : Blo 2199435 10576423 := bstep (se 1 (by rfl) ⟨7932317, by rfl⟩ : syracuseStep 10576423 = 15864635) B15864635
theorem B14101897 : Blo 2199435 14101897 := bstep (se 2 (by rfl) ⟨5288211, by rfl⟩ : syracuseStep 14101897 = 10576423) B10576423
theorem B18802529 : Blo 2199435 18802529 := bstep (se 2 (by rfl) ⟨7050948, by rfl⟩ : syracuseStep 18802529 = 14101897) B14101897
theorem B12535019 : Blo 2199435 12535019 := bstep (se 1 (by rfl) ⟨9401264, by rfl⟩ : syracuseStep 12535019 = 18802529) B18802529
theorem B8356679 : Blo 2199435 8356679 := bstep (se 1 (by rfl) ⟨6267509, by rfl⟩ : syracuseStep 8356679 = 12535019) B12535019
theorem B5571119 : Blo 2199435 5571119 := bstep (se 1 (by rfl) ⟨4178339, by rfl⟩ : syracuseStep 5571119 = 8356679) B8356679
theorem B3714079 : Blo 2199435 3714079 := bstep (se 1 (by rfl) ⟨2785559, by rfl⟩ : syracuseStep 3714079 = 5571119) B5571119
theorem B4952105 : Blo 2199435 4952105 := bstep (se 2 (by rfl) ⟨1857039, by rfl⟩ : syracuseStep 4952105 = 3714079) B3714079
theorem B3301403 : Blo 2199435 3301403 := bstep (se 1 (by rfl) ⟨2476052, by rfl⟩ : syracuseStep 3301403 = 4952105) B4952105
theorem B2200935 : Blo 2199435 2200935 := bstep (se 1 (by rfl) ⟨1650701, by rfl⟩ : syracuseStep 2200935 = 3301403) B3301403
theorem B2476057 : Blo 2199435 2476057 := bbase (se 2 (by rfl) ⟨928521, by rfl⟩ : syracuseStep 2476057 = 1857043) (by norm_num)
theorem B3301409 : Blo 2199435 3301409 := bstep (se 2 (by rfl) ⟨1238028, by rfl⟩ : syracuseStep 3301409 = 2476057) B2476057
theorem B2200939 : Blo 2199435 2200939 := bstep (se 1 (by rfl) ⟨1650704, by rfl⟩ : syracuseStep 2200939 = 3301409) B3301409
theorem B8356709 : Blo 2199435 8356709 := bbase (se 4 (by rfl) ⟨783441, by rfl⟩ : syracuseStep 8356709 = 1566883) (by norm_num)
theorem B5571139 : Blo 2199435 5571139 := bstep (se 1 (by rfl) ⟨4178354, by rfl⟩ : syracuseStep 5571139 = 8356709) B8356709
theorem B7428185 : Blo 2199435 7428185 := bstep (se 2 (by rfl) ⟨2785569, by rfl⟩ : syracuseStep 7428185 = 5571139) B5571139
theorem B4952123 : Blo 2199435 4952123 := bstep (se 1 (by rfl) ⟨3714092, by rfl⟩ : syracuseStep 4952123 = 7428185) B7428185
theorem B3301415 : Blo 2199435 3301415 := bstep (se 1 (by rfl) ⟨2476061, by rfl⟩ : syracuseStep 3301415 = 4952123) B4952123
theorem B2200943 : Blo 2199435 2200943 := bstep (se 1 (by rfl) ⟨1650707, by rfl⟩ : syracuseStep 2200943 = 3301415) B3301415
theorem B3301421 : Blo 2199435 3301421 := bbase (se 3 (by rfl) ⟨619016, by rfl⟩ : syracuseStep 3301421 = 1238033) (by norm_num)
theorem B2200947 : Blo 2199435 2200947 := bstep (se 1 (by rfl) ⟨1650710, by rfl⟩ : syracuseStep 2200947 = 3301421) B3301421
theorem B4952141 : Blo 2199435 4952141 := bbase (se 3 (by rfl) ⟨928526, by rfl⟩ : syracuseStep 4952141 = 1857053) (by norm_num)
theorem B3301427 : Blo 2199435 3301427 := bstep (se 1 (by rfl) ⟨2476070, by rfl⟩ : syracuseStep 3301427 = 4952141) B4952141
theorem B2200951 : Blo 2199435 2200951 := bstep (se 1 (by rfl) ⟨1650713, by rfl⟩ : syracuseStep 2200951 = 3301427) B3301427
theorem B2785585 : Blo 2199435 2785585 := bbase (se 2 (by rfl) ⟨1044594, by rfl⟩ : syracuseStep 2785585 = 2089189) (by norm_num)
theorem B3714113 : Blo 2199435 3714113 := bstep (se 2 (by rfl) ⟨1392792, by rfl⟩ : syracuseStep 3714113 = 2785585) B2785585
theorem B2476075 : Blo 2199435 2476075 := bstep (se 1 (by rfl) ⟨1857056, by rfl⟩ : syracuseStep 2476075 = 3714113) B3714113
theorem B3301433 : Blo 2199435 3301433 := bstep (se 2 (by rfl) ⟨1238037, by rfl⟩ : syracuseStep 3301433 = 2476075) B2476075
theorem B2200955 : Blo 2199435 2200955 := bstep (se 1 (by rfl) ⟨1650716, by rfl⟩ : syracuseStep 2200955 = 3301433) B3301433
theorem B5288269 : Blo 2199435 5288269 := bbase (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) (by norm_num)
theorem B7051025 : Blo 2199435 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B4700683 : Blo 2199435 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B25070309 : Blo 2199435 25070309 := bstep (se 4 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 25070309 = 4700683) B4700683
theorem B16713539 : Blo 2199435 16713539 := bstep (se 1 (by rfl) ⟨12535154, by rfl⟩ : syracuseStep 16713539 = 25070309) B25070309
theorem B11142359 : Blo 2199435 11142359 := bstep (se 1 (by rfl) ⟨8356769, by rfl⟩ : syracuseStep 11142359 = 16713539) B16713539
theorem B7428239 : Blo 2199435 7428239 := bstep (se 1 (by rfl) ⟨5571179, by rfl⟩ : syracuseStep 7428239 = 11142359) B11142359
theorem B4952159 : Blo 2199435 4952159 := bstep (se 1 (by rfl) ⟨3714119, by rfl⟩ : syracuseStep 4952159 = 7428239) B7428239
theorem B3301439 : Blo 2199435 3301439 := bstep (se 1 (by rfl) ⟨2476079, by rfl⟩ : syracuseStep 3301439 = 4952159) B4952159
theorem B2200959 : Blo 2199435 2200959 := bstep (se 1 (by rfl) ⟨1650719, by rfl⟩ : syracuseStep 2200959 = 3301439) B3301439
theorem B3301445 : Blo 2199435 3301445 := bbase (se 4 (by rfl) ⟨309510, by rfl⟩ : syracuseStep 3301445 = 619021) (by norm_num)
theorem B2200963 : Blo 2199435 2200963 := bstep (se 1 (by rfl) ⟨1650722, by rfl⟩ : syracuseStep 2200963 = 3301445) B3301445
theorem B3714133 : Blo 2199435 3714133 := bbase (se 8 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 3714133 = 43525) (by norm_num)
theorem B4952177 : Blo 2199435 4952177 := bstep (se 2 (by rfl) ⟨1857066, by rfl⟩ : syracuseStep 4952177 = 3714133) B3714133
theorem B3301451 : Blo 2199435 3301451 := bstep (se 1 (by rfl) ⟨2476088, by rfl⟩ : syracuseStep 3301451 = 4952177) B4952177
theorem B2200967 : Blo 2199435 2200967 := bstep (se 1 (by rfl) ⟨1650725, by rfl⟩ : syracuseStep 2200967 = 3301451) B3301451
theorem B2476093 : Blo 2199435 2476093 := bbase (se 3 (by rfl) ⟨464267, by rfl⟩ : syracuseStep 2476093 = 928535) (by norm_num)
theorem B3301457 : Blo 2199435 3301457 := bstep (se 2 (by rfl) ⟨1238046, by rfl⟩ : syracuseStep 3301457 = 2476093) B2476093
theorem B2200971 : Blo 2199435 2200971 := bstep (se 1 (by rfl) ⟨1650728, by rfl⟩ : syracuseStep 2200971 = 3301457) B3301457
theorem B7428293 : Blo 2199435 7428293 := bbase (se 4 (by rfl) ⟨696402, by rfl⟩ : syracuseStep 7428293 = 1392805) (by norm_num)
theorem B4952195 : Blo 2199435 4952195 := bstep (se 1 (by rfl) ⟨3714146, by rfl⟩ : syracuseStep 4952195 = 7428293) B7428293
theorem B3301463 : Blo 2199435 3301463 := bstep (se 1 (by rfl) ⟨2476097, by rfl⟩ : syracuseStep 3301463 = 4952195) B4952195
theorem B2200975 : Blo 2199435 2200975 := bstep (se 1 (by rfl) ⟨1650731, by rfl⟩ : syracuseStep 2200975 = 3301463) B3301463
theorem B3301469 : Blo 2199435 3301469 := bbase (se 3 (by rfl) ⟨619025, by rfl⟩ : syracuseStep 3301469 = 1238051) (by norm_num)
theorem B2200979 : Blo 2199435 2200979 := bstep (se 1 (by rfl) ⟨1650734, by rfl⟩ : syracuseStep 2200979 = 3301469) B3301469
theorem B4952213 : Blo 2199435 4952213 := bbase (se 6 (by rfl) ⟨116067, by rfl⟩ : syracuseStep 4952213 = 232135) (by norm_num)
theorem B3301475 : Blo 2199435 3301475 := bstep (se 1 (by rfl) ⟨2476106, by rfl⟩ : syracuseStep 3301475 = 4952213) B4952213
theorem B2200983 : Blo 2199435 2200983 := bstep (se 1 (by rfl) ⟨1650737, by rfl⟩ : syracuseStep 2200983 = 3301475) B3301475
theorem B3133829 : Blo 2199435 3133829 := bbase (se 4 (by rfl) ⟨293796, by rfl⟩ : syracuseStep 3133829 = 587593) (by norm_num)
theorem B8356877 : Blo 2199435 8356877 := bstep (se 3 (by rfl) ⟨1566914, by rfl⟩ : syracuseStep 8356877 = 3133829) B3133829
theorem B5571251 : Blo 2199435 5571251 := bstep (se 1 (by rfl) ⟨4178438, by rfl⟩ : syracuseStep 5571251 = 8356877) B8356877
theorem B3714167 : Blo 2199435 3714167 := bstep (se 1 (by rfl) ⟨2785625, by rfl⟩ : syracuseStep 3714167 = 5571251) B5571251
theorem B2476111 : Blo 2199435 2476111 := bstep (se 1 (by rfl) ⟨1857083, by rfl⟩ : syracuseStep 2476111 = 3714167) B3714167
theorem B3301481 : Blo 2199435 3301481 := bstep (se 2 (by rfl) ⟨1238055, by rfl⟩ : syracuseStep 3301481 = 2476111) B2476111
theorem B2200987 : Blo 2199435 2200987 := bstep (se 1 (by rfl) ⟨1650740, by rfl⟩ : syracuseStep 2200987 = 3301481) B3301481
theorem B2614037 : Blo 2199435 2614037 := bbase (se 6 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 2614037 = 122533) (by norm_num)
theorem B6970765 : Blo 2199435 6970765 := bstep (se 3 (by rfl) ⟨1307018, by rfl⟩ : syracuseStep 6970765 = 2614037) B2614037
theorem B9294353 : Blo 2199435 9294353 := bstep (se 2 (by rfl) ⟨3485382, by rfl⟩ : syracuseStep 9294353 = 6970765) B6970765
theorem B6196235 : Blo 2199435 6196235 := bstep (se 1 (by rfl) ⟨4647176, by rfl⟩ : syracuseStep 6196235 = 9294353) B9294353
theorem B16523293 : Blo 2199435 16523293 := bstep (se 3 (by rfl) ⟨3098117, by rfl⟩ : syracuseStep 16523293 = 6196235) B6196235
theorem B22031057 : Blo 2199435 22031057 := bstep (se 2 (by rfl) ⟨8261646, by rfl⟩ : syracuseStep 22031057 = 16523293) B16523293
theorem B14687371 : Blo 2199435 14687371 := bstep (se 1 (by rfl) ⟨11015528, by rfl⟩ : syracuseStep 14687371 = 22031057) B22031057
theorem B78332645 : Blo 2199435 78332645 := bstep (se 4 (by rfl) ⟨7343685, by rfl⟩ : syracuseStep 78332645 = 14687371) B14687371
theorem B52221763 : Blo 2199435 52221763 := bstep (se 1 (by rfl) ⟨39166322, by rfl⟩ : syracuseStep 52221763 = 78332645) B78332645
theorem B278516069 : Blo 2199435 278516069 := bstep (se 4 (by rfl) ⟨26110881, by rfl⟩ : syracuseStep 278516069 = 52221763) B52221763
theorem B185677379 : Blo 2199435 185677379 := bstep (se 1 (by rfl) ⟨139258034, by rfl⟩ : syracuseStep 185677379 = 278516069) B278516069
theorem B123784919 : Blo 2199435 123784919 := bstep (se 1 (by rfl) ⟨92838689, by rfl⟩ : syracuseStep 123784919 = 185677379) B185677379
theorem B82523279 : Blo 2199435 82523279 := bstep (se 1 (by rfl) ⟨61892459, by rfl⟩ : syracuseStep 82523279 = 123784919) B123784919
theorem B55015519 : Blo 2199435 55015519 := bstep (se 1 (by rfl) ⟨41261639, by rfl⟩ : syracuseStep 55015519 = 82523279) B82523279
theorem B73354025 : Blo 2199435 73354025 := bstep (se 2 (by rfl) ⟨27507759, by rfl⟩ : syracuseStep 73354025 = 55015519) B55015519
theorem B195610733 : Blo 2199435 195610733 := bstep (se 3 (by rfl) ⟨36677012, by rfl⟩ : syracuseStep 195610733 = 73354025) B73354025
theorem B130407155 : Blo 2199435 130407155 := bstep (se 1 (by rfl) ⟨97805366, by rfl⟩ : syracuseStep 130407155 = 195610733) B195610733
theorem B86938103 : Blo 2199435 86938103 := bstep (se 1 (by rfl) ⟨65203577, by rfl⟩ : syracuseStep 86938103 = 130407155) B130407155
theorem B57958735 : Blo 2199435 57958735 := bstep (se 1 (by rfl) ⟨43469051, by rfl⟩ : syracuseStep 57958735 = 86938103) B86938103
theorem B77278313 : Blo 2199435 77278313 := bstep (se 2 (by rfl) ⟨28979367, by rfl⟩ : syracuseStep 77278313 = 57958735) B57958735
theorem B51518875 : Blo 2199435 51518875 := bstep (se 1 (by rfl) ⟨38639156, by rfl⟩ : syracuseStep 51518875 = 77278313) B77278313
theorem B68691833 : Blo 2199435 68691833 := bstep (se 2 (by rfl) ⟨25759437, by rfl⟩ : syracuseStep 68691833 = 51518875) B51518875
theorem B45794555 : Blo 2199435 45794555 := bstep (se 1 (by rfl) ⟨34345916, by rfl⟩ : syracuseStep 45794555 = 68691833) B68691833
theorem B30529703 : Blo 2199435 30529703 := bstep (se 1 (by rfl) ⟨22897277, by rfl⟩ : syracuseStep 30529703 = 45794555) B45794555
theorem B81412541 : Blo 2199435 81412541 := bstep (se 3 (by rfl) ⟨15264851, by rfl⟩ : syracuseStep 81412541 = 30529703) B30529703
theorem B54275027 : Blo 2199435 54275027 := bstep (se 1 (by rfl) ⟨40706270, by rfl⟩ : syracuseStep 54275027 = 81412541) B81412541
theorem B144733405 : Blo 2199435 144733405 := bstep (se 3 (by rfl) ⟨27137513, by rfl⟩ : syracuseStep 144733405 = 54275027) B54275027
theorem B192977873 : Blo 2199435 192977873 := bstep (se 2 (by rfl) ⟨72366702, by rfl⟩ : syracuseStep 192977873 = 144733405) B144733405
theorem B128651915 : Blo 2199435 128651915 := bstep (se 1 (by rfl) ⟨96488936, by rfl⟩ : syracuseStep 128651915 = 192977873) B192977873
theorem B343071773 : Blo 2199435 343071773 := bstep (se 3 (by rfl) ⟨64325957, by rfl⟩ : syracuseStep 343071773 = 128651915) B128651915
theorem B228714515 : Blo 2199435 228714515 := bstep (se 1 (by rfl) ⟨171535886, by rfl⟩ : syracuseStep 228714515 = 343071773) B343071773
theorem B152476343 : Blo 2199435 152476343 := bstep (se 1 (by rfl) ⟨114357257, by rfl⟩ : syracuseStep 152476343 = 228714515) B228714515
theorem B101650895 : Blo 2199435 101650895 := bstep (se 1 (by rfl) ⟨76238171, by rfl⟩ : syracuseStep 101650895 = 152476343) B152476343
theorem B67767263 : Blo 2199435 67767263 := bstep (se 1 (by rfl) ⟨50825447, by rfl⟩ : syracuseStep 67767263 = 101650895) B101650895
theorem B45178175 : Blo 2199435 45178175 := bstep (se 1 (by rfl) ⟨33883631, by rfl⟩ : syracuseStep 45178175 = 67767263) B67767263
theorem B120475133 : Blo 2199435 120475133 := bstep (se 3 (by rfl) ⟨22589087, by rfl⟩ : syracuseStep 120475133 = 45178175) B45178175
theorem B80316755 : Blo 2199435 80316755 := bstep (se 1 (by rfl) ⟨60237566, by rfl⟩ : syracuseStep 80316755 = 120475133) B120475133
theorem B53544503 : Blo 2199435 53544503 := bstep (se 1 (by rfl) ⟨40158377, by rfl⟩ : syracuseStep 53544503 = 80316755) B80316755
theorem B35696335 : Blo 2199435 35696335 := bstep (se 1 (by rfl) ⟨26772251, by rfl⟩ : syracuseStep 35696335 = 53544503) B53544503
theorem B47595113 : Blo 2199435 47595113 := bstep (se 2 (by rfl) ⟨17848167, by rfl⟩ : syracuseStep 47595113 = 35696335) B35696335
theorem B31730075 : Blo 2199435 31730075 := bstep (se 1 (by rfl) ⟨23797556, by rfl⟩ : syracuseStep 31730075 = 47595113) B47595113
theorem B21153383 : Blo 2199435 21153383 := bstep (se 1 (by rfl) ⟨15865037, by rfl⟩ : syracuseStep 21153383 = 31730075) B31730075
theorem B14102255 : Blo 2199435 14102255 := bstep (se 1 (by rfl) ⟨10576691, by rfl⟩ : syracuseStep 14102255 = 21153383) B21153383
theorem B9401503 : Blo 2199435 9401503 := bstep (se 1 (by rfl) ⟨7051127, by rfl⟩ : syracuseStep 9401503 = 14102255) B14102255
theorem B12535337 : Blo 2199435 12535337 := bstep (se 2 (by rfl) ⟨4700751, by rfl⟩ : syracuseStep 12535337 = 9401503) B9401503
theorem B8356891 : Blo 2199435 8356891 := bstep (se 1 (by rfl) ⟨6267668, by rfl⟩ : syracuseStep 8356891 = 12535337) B12535337
theorem B11142521 : Blo 2199435 11142521 := bstep (se 2 (by rfl) ⟨4178445, by rfl⟩ : syracuseStep 11142521 = 8356891) B8356891
theorem B7428347 : Blo 2199435 7428347 := bstep (se 1 (by rfl) ⟨5571260, by rfl⟩ : syracuseStep 7428347 = 11142521) B11142521
theorem B4952231 : Blo 2199435 4952231 := bstep (se 1 (by rfl) ⟨3714173, by rfl⟩ : syracuseStep 4952231 = 7428347) B7428347
theorem B3301487 : Blo 2199435 3301487 := bstep (se 1 (by rfl) ⟨2476115, by rfl⟩ : syracuseStep 3301487 = 4952231) B4952231
theorem B2200991 : Blo 2199435 2200991 := bstep (se 1 (by rfl) ⟨1650743, by rfl⟩ : syracuseStep 2200991 = 3301487) B3301487
theorem B3301493 : Blo 2199435 3301493 := bbase (se 5 (by rfl) ⟨154757, by rfl⟩ : syracuseStep 3301493 = 309515) (by norm_num)
theorem B2200995 : Blo 2199435 2200995 := bstep (se 1 (by rfl) ⟨1650746, by rfl⟩ : syracuseStep 2200995 = 3301493) B3301493
theorem B4178461 : Blo 2199435 4178461 := bbase (se 3 (by rfl) ⟨783461, by rfl⟩ : syracuseStep 4178461 = 1566923) (by norm_num)
theorem B5571281 : Blo 2199435 5571281 := bstep (se 2 (by rfl) ⟨2089230, by rfl⟩ : syracuseStep 5571281 = 4178461) B4178461
theorem B3714187 : Blo 2199435 3714187 := bstep (se 1 (by rfl) ⟨2785640, by rfl⟩ : syracuseStep 3714187 = 5571281) B5571281
theorem B4952249 : Blo 2199435 4952249 := bstep (se 2 (by rfl) ⟨1857093, by rfl⟩ : syracuseStep 4952249 = 3714187) B3714187
theorem B3301499 : Blo 2199435 3301499 := bstep (se 1 (by rfl) ⟨2476124, by rfl⟩ : syracuseStep 3301499 = 4952249) B4952249
theorem B2200999 : Blo 2199435 2200999 := bstep (se 1 (by rfl) ⟨1650749, by rfl⟩ : syracuseStep 2200999 = 3301499) B3301499
theorem B2476129 : Blo 2199435 2476129 := bbase (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) (by norm_num)
theorem B3301505 : Blo 2199435 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B2201003 : Blo 2199435 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B5571301 : Blo 2199435 5571301 := bbase (se 4 (by rfl) ⟨522309, by rfl⟩ : syracuseStep 5571301 = 1044619) (by norm_num)
theorem B7428401 : Blo 2199435 7428401 := bstep (se 2 (by rfl) ⟨2785650, by rfl⟩ : syracuseStep 7428401 = 5571301) B5571301
theorem B4952267 : Blo 2199435 4952267 := bstep (se 1 (by rfl) ⟨3714200, by rfl⟩ : syracuseStep 4952267 = 7428401) B7428401
theorem B3301511 : Blo 2199435 3301511 := bstep (se 1 (by rfl) ⟨2476133, by rfl⟩ : syracuseStep 3301511 = 4952267) B4952267
theorem B2201007 : Blo 2199435 2201007 := bstep (se 1 (by rfl) ⟨1650755, by rfl⟩ : syracuseStep 2201007 = 3301511) B3301511
theorem B3301517 : Blo 2199435 3301517 := bbase (se 3 (by rfl) ⟨619034, by rfl⟩ : syracuseStep 3301517 = 1238069) (by norm_num)
theorem B2201011 : Blo 2199435 2201011 := bstep (se 1 (by rfl) ⟨1650758, by rfl⟩ : syracuseStep 2201011 = 3301517) B3301517
theorem B4952285 : Blo 2199435 4952285 := bbase (se 3 (by rfl) ⟨928553, by rfl⟩ : syracuseStep 4952285 = 1857107) (by norm_num)
theorem B3301523 : Blo 2199435 3301523 := bstep (se 1 (by rfl) ⟨2476142, by rfl⟩ : syracuseStep 3301523 = 4952285) B4952285
theorem B2201015 : Blo 2199435 2201015 := bstep (se 1 (by rfl) ⟨1650761, by rfl⟩ : syracuseStep 2201015 = 3301523) B3301523
theorem B3714221 : Blo 2199435 3714221 := bbase (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) (by norm_num)
theorem B2476147 : Blo 2199435 2476147 := bstep (se 1 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 2476147 = 3714221) B3714221
theorem B3301529 : Blo 2199435 3301529 := bstep (se 2 (by rfl) ⟨1238073, by rfl⟩ : syracuseStep 3301529 = 2476147) B2476147
theorem B2201019 : Blo 2199435 2201019 := bstep (se 1 (by rfl) ⟨1650764, by rfl⟩ : syracuseStep 2201019 = 3301529) B3301529
theorem B8924213 : Blo 2199435 8924213 := bbase (se 5 (by rfl) ⟨418322, by rfl⟩ : syracuseStep 8924213 = 836645) (by norm_num)
theorem B23797901 : Blo 2199435 23797901 := bstep (se 3 (by rfl) ⟨4462106, by rfl⟩ : syracuseStep 23797901 = 8924213) B8924213
theorem B63461069 : Blo 2199435 63461069 := bstep (se 3 (by rfl) ⟨11898950, by rfl⟩ : syracuseStep 63461069 = 23797901) B23797901
theorem B42307379 : Blo 2199435 42307379 := bstep (se 1 (by rfl) ⟨31730534, by rfl⟩ : syracuseStep 42307379 = 63461069) B63461069
theorem B28204919 : Blo 2199435 28204919 := bstep (se 1 (by rfl) ⟨21153689, by rfl⟩ : syracuseStep 28204919 = 42307379) B42307379
theorem B18803279 : Blo 2199435 18803279 := bstep (se 1 (by rfl) ⟨14102459, by rfl⟩ : syracuseStep 18803279 = 28204919) B28204919
theorem B12535519 : Blo 2199435 12535519 := bstep (se 1 (by rfl) ⟨9401639, by rfl⟩ : syracuseStep 12535519 = 18803279) B18803279
theorem B16714025 : Blo 2199435 16714025 := bstep (se 2 (by rfl) ⟨6267759, by rfl⟩ : syracuseStep 16714025 = 12535519) B12535519
theorem B11142683 : Blo 2199435 11142683 := bstep (se 1 (by rfl) ⟨8357012, by rfl⟩ : syracuseStep 11142683 = 16714025) B16714025
theorem B7428455 : Blo 2199435 7428455 := bstep (se 1 (by rfl) ⟨5571341, by rfl⟩ : syracuseStep 7428455 = 11142683) B11142683
theorem B4952303 : Blo 2199435 4952303 := bstep (se 1 (by rfl) ⟨3714227, by rfl⟩ : syracuseStep 4952303 = 7428455) B7428455
theorem B3301535 : Blo 2199435 3301535 := bstep (se 1 (by rfl) ⟨2476151, by rfl⟩ : syracuseStep 3301535 = 4952303) B4952303
theorem B2201023 : Blo 2199435 2201023 := bstep (se 1 (by rfl) ⟨1650767, by rfl⟩ : syracuseStep 2201023 = 3301535) B3301535
theorem B3301541 : Blo 2199435 3301541 := bbase (se 4 (by rfl) ⟨309519, by rfl⟩ : syracuseStep 3301541 = 619039) (by norm_num)
theorem B2201027 : Blo 2199435 2201027 := bstep (se 1 (by rfl) ⟨1650770, by rfl⟩ : syracuseStep 2201027 = 3301541) B3301541
theorem B2785681 : Blo 2199435 2785681 := bbase (se 2 (by rfl) ⟨1044630, by rfl⟩ : syracuseStep 2785681 = 2089261) (by norm_num)
theorem B3714241 : Blo 2199435 3714241 := bstep (se 2 (by rfl) ⟨1392840, by rfl⟩ : syracuseStep 3714241 = 2785681) B2785681
theorem B4952321 : Blo 2199435 4952321 := bstep (se 2 (by rfl) ⟨1857120, by rfl⟩ : syracuseStep 4952321 = 3714241) B3714241
theorem B3301547 : Blo 2199435 3301547 := bstep (se 1 (by rfl) ⟨2476160, by rfl⟩ : syracuseStep 3301547 = 4952321) B4952321
theorem B2201031 : Blo 2199435 2201031 := bstep (se 1 (by rfl) ⟨1650773, by rfl⟩ : syracuseStep 2201031 = 3301547) B3301547
theorem B2476165 : Blo 2199435 2476165 := bbase (se 4 (by rfl) ⟨232140, by rfl⟩ : syracuseStep 2476165 = 464281) (by norm_num)
theorem B3301553 : Blo 2199435 3301553 := bstep (se 2 (by rfl) ⟨1238082, by rfl⟩ : syracuseStep 3301553 = 2476165) B2476165
theorem B2201035 : Blo 2199435 2201035 := bstep (se 1 (by rfl) ⟨1650776, by rfl⟩ : syracuseStep 2201035 = 3301553) B3301553
theorem B4462141 : Blo 2199435 4462141 := bbase (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) (by norm_num)
theorem B5949521 : Blo 2199435 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B3966347 : Blo 2199435 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B10576925 : Blo 2199435 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B7051283 : Blo 2199435 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B4700855 : Blo 2199435 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B3133903 : Blo 2199435 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B4178537 : Blo 2199435 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2785691 : Blo 2199435 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B7428509 : Blo 2199435 7428509 := bstep (se 3 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 7428509 = 2785691) B2785691
theorem B4952339 : Blo 2199435 4952339 := bstep (se 1 (by rfl) ⟨3714254, by rfl⟩ : syracuseStep 4952339 = 7428509) B7428509
theorem B3301559 : Blo 2199435 3301559 := bstep (se 1 (by rfl) ⟨2476169, by rfl⟩ : syracuseStep 3301559 = 4952339) B4952339
theorem B2201039 : Blo 2199435 2201039 := bstep (se 1 (by rfl) ⟨1650779, by rfl⟩ : syracuseStep 2201039 = 3301559) B3301559
theorem B3301565 : Blo 2199435 3301565 := bbase (se 3 (by rfl) ⟨619043, by rfl⟩ : syracuseStep 3301565 = 1238087) (by norm_num)
theorem B2201043 : Blo 2199435 2201043 := bstep (se 1 (by rfl) ⟨1650782, by rfl⟩ : syracuseStep 2201043 = 3301565) B3301565
theorem B4952357 : Blo 2199435 4952357 := bbase (se 4 (by rfl) ⟨464283, by rfl⟩ : syracuseStep 4952357 = 928567) (by norm_num)
theorem B3301571 : Blo 2199435 3301571 := bstep (se 1 (by rfl) ⟨2476178, by rfl⟩ : syracuseStep 3301571 = 4952357) B4952357
theorem B2201047 : Blo 2199435 2201047 := bstep (se 1 (by rfl) ⟨1650785, by rfl⟩ : syracuseStep 2201047 = 3301571) B3301571
theorem B5571413 : Blo 2199435 5571413 := bbase (se 9 (by rfl) ⟨16322, by rfl⟩ : syracuseStep 5571413 = 32645) (by norm_num)
theorem B3714275 : Blo 2199435 3714275 := bstep (se 1 (by rfl) ⟨2785706, by rfl⟩ : syracuseStep 3714275 = 5571413) B5571413
theorem B2476183 : Blo 2199435 2476183 := bstep (se 1 (by rfl) ⟨1857137, by rfl⟩ : syracuseStep 2476183 = 3714275) B3714275
theorem B3301577 : Blo 2199435 3301577 := bstep (se 2 (by rfl) ⟨1238091, by rfl⟩ : syracuseStep 3301577 = 2476183) B2476183
theorem B2201051 : Blo 2199435 2201051 := bstep (se 1 (by rfl) ⟨1650788, by rfl⟩ : syracuseStep 2201051 = 3301577) B3301577
theorem B7051333 : Blo 2199435 7051333 := bbase (se 4 (by rfl) ⟨661062, by rfl⟩ : syracuseStep 7051333 = 1322125) (by norm_num)
theorem B9401777 : Blo 2199435 9401777 := bstep (se 2 (by rfl) ⟨3525666, by rfl⟩ : syracuseStep 9401777 = 7051333) B7051333
theorem B6267851 : Blo 2199435 6267851 := bstep (se 1 (by rfl) ⟨4700888, by rfl⟩ : syracuseStep 6267851 = 9401777) B9401777
theorem B4178567 : Blo 2199435 4178567 := bstep (se 1 (by rfl) ⟨3133925, by rfl⟩ : syracuseStep 4178567 = 6267851) B6267851
theorem B11142845 : Blo 2199435 11142845 := bstep (se 3 (by rfl) ⟨2089283, by rfl⟩ : syracuseStep 11142845 = 4178567) B4178567
theorem B7428563 : Blo 2199435 7428563 := bstep (se 1 (by rfl) ⟨5571422, by rfl⟩ : syracuseStep 7428563 = 11142845) B11142845
theorem B4952375 : Blo 2199435 4952375 := bstep (se 1 (by rfl) ⟨3714281, by rfl⟩ : syracuseStep 4952375 = 7428563) B7428563
theorem B3301583 : Blo 2199435 3301583 := bstep (se 1 (by rfl) ⟨2476187, by rfl⟩ : syracuseStep 3301583 = 4952375) B4952375
theorem B2201055 : Blo 2199435 2201055 := bstep (se 1 (by rfl) ⟨1650791, by rfl⟩ : syracuseStep 2201055 = 3301583) B3301583
theorem B3301589 : Blo 2199435 3301589 := bbase (se 7 (by rfl) ⟨38690, by rfl⟩ : syracuseStep 3301589 = 77381) (by norm_num)
theorem B2201059 : Blo 2199435 2201059 := bstep (se 1 (by rfl) ⟨1650794, by rfl⟩ : syracuseStep 2201059 = 3301589) B3301589
theorem B2350453 : Blo 2199435 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B3133937 : Blo 2199435 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B8357165 : Blo 2199435 8357165 := bstep (se 3 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 8357165 = 3133937) B3133937
theorem B5571443 : Blo 2199435 5571443 := bstep (se 1 (by rfl) ⟨4178582, by rfl⟩ : syracuseStep 5571443 = 8357165) B8357165
theorem B3714295 : Blo 2199435 3714295 := bstep (se 1 (by rfl) ⟨2785721, by rfl⟩ : syracuseStep 3714295 = 5571443) B5571443
theorem B4952393 : Blo 2199435 4952393 := bstep (se 2 (by rfl) ⟨1857147, by rfl⟩ : syracuseStep 4952393 = 3714295) B3714295
theorem B3301595 : Blo 2199435 3301595 := bstep (se 1 (by rfl) ⟨2476196, by rfl⟩ : syracuseStep 3301595 = 4952393) B4952393
theorem B2201063 : Blo 2199435 2201063 := bstep (se 1 (by rfl) ⟨1650797, by rfl⟩ : syracuseStep 2201063 = 3301595) B3301595
theorem B2476201 : Blo 2199435 2476201 := bbase (se 2 (by rfl) ⟨928575, by rfl⟩ : syracuseStep 2476201 = 1857151) (by norm_num)
theorem B3301601 : Blo 2199435 3301601 := bstep (se 2 (by rfl) ⟨1238100, by rfl⟩ : syracuseStep 3301601 = 2476201) B2476201
theorem B2201067 : Blo 2199435 2201067 := bstep (se 1 (by rfl) ⟨1650800, by rfl⟩ : syracuseStep 2201067 = 3301601) B3301601
theorem B9401845 : Blo 2199435 9401845 := bbase (se 5 (by rfl) ⟨440711, by rfl⟩ : syracuseStep 9401845 = 881423) (by norm_num)
theorem B12535793 : Blo 2199435 12535793 := bstep (se 2 (by rfl) ⟨4700922, by rfl⟩ : syracuseStep 12535793 = 9401845) B9401845
theorem B8357195 : Blo 2199435 8357195 := bstep (se 1 (by rfl) ⟨6267896, by rfl⟩ : syracuseStep 8357195 = 12535793) B12535793
theorem B5571463 : Blo 2199435 5571463 := bstep (se 1 (by rfl) ⟨4178597, by rfl⟩ : syracuseStep 5571463 = 8357195) B8357195
theorem B7428617 : Blo 2199435 7428617 := bstep (se 2 (by rfl) ⟨2785731, by rfl⟩ : syracuseStep 7428617 = 5571463) B5571463
theorem B4952411 : Blo 2199435 4952411 := bstep (se 1 (by rfl) ⟨3714308, by rfl⟩ : syracuseStep 4952411 = 7428617) B7428617
theorem B3301607 : Blo 2199435 3301607 := bstep (se 1 (by rfl) ⟨2476205, by rfl⟩ : syracuseStep 3301607 = 4952411) B4952411
theorem B2201071 : Blo 2199435 2201071 := bstep (se 1 (by rfl) ⟨1650803, by rfl⟩ : syracuseStep 2201071 = 3301607) B3301607
theorem B3301613 : Blo 2199435 3301613 := bbase (se 3 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 3301613 = 1238105) (by norm_num)
theorem B2201075 : Blo 2199435 2201075 := bstep (se 1 (by rfl) ⟨1650806, by rfl⟩ : syracuseStep 2201075 = 3301613) B3301613
theorem B4952429 : Blo 2199435 4952429 := bbase (se 3 (by rfl) ⟨928580, by rfl⟩ : syracuseStep 4952429 = 1857161) (by norm_num)
theorem B3301619 : Blo 2199435 3301619 := bstep (se 1 (by rfl) ⟨2476214, by rfl⟩ : syracuseStep 3301619 = 4952429) B4952429
theorem B2201079 : Blo 2199435 2201079 := bstep (se 1 (by rfl) ⟨1650809, by rfl⟩ : syracuseStep 2201079 = 3301619) B3301619
theorem B4178621 : Blo 2199435 4178621 := bbase (se 3 (by rfl) ⟨783491, by rfl⟩ : syracuseStep 4178621 = 1566983) (by norm_num)
theorem B2785747 : Blo 2199435 2785747 := bstep (se 1 (by rfl) ⟨2089310, by rfl⟩ : syracuseStep 2785747 = 4178621) B4178621
theorem B3714329 : Blo 2199435 3714329 := bstep (se 2 (by rfl) ⟨1392873, by rfl⟩ : syracuseStep 3714329 = 2785747) B2785747
theorem B2476219 : Blo 2199435 2476219 := bstep (se 1 (by rfl) ⟨1857164, by rfl⟩ : syracuseStep 2476219 = 3714329) B3714329
theorem B3301625 : Blo 2199435 3301625 := bstep (se 2 (by rfl) ⟨1238109, by rfl⟩ : syracuseStep 3301625 = 2476219) B2476219
theorem B2201083 : Blo 2199435 2201083 := bstep (se 1 (by rfl) ⟨1650812, by rfl⟩ : syracuseStep 2201083 = 3301625) B3301625
theorem B56411477 : Blo 2199435 56411477 := bbase (se 12 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 56411477 = 41317) (by norm_num)
theorem B37607651 : Blo 2199435 37607651 := bstep (se 1 (by rfl) ⟨28205738, by rfl⟩ : syracuseStep 37607651 = 56411477) B56411477
theorem B25071767 : Blo 2199435 25071767 := bstep (se 1 (by rfl) ⟨18803825, by rfl⟩ : syracuseStep 25071767 = 37607651) B37607651
theorem B16714511 : Blo 2199435 16714511 := bstep (se 1 (by rfl) ⟨12535883, by rfl⟩ : syracuseStep 16714511 = 25071767) B25071767
theorem B11143007 : Blo 2199435 11143007 := bstep (se 1 (by rfl) ⟨8357255, by rfl⟩ : syracuseStep 11143007 = 16714511) B16714511
theorem B7428671 : Blo 2199435 7428671 := bstep (se 1 (by rfl) ⟨5571503, by rfl⟩ : syracuseStep 7428671 = 11143007) B11143007
theorem B4952447 : Blo 2199435 4952447 := bstep (se 1 (by rfl) ⟨3714335, by rfl⟩ : syracuseStep 4952447 = 7428671) B7428671
theorem B3301631 : Blo 2199435 3301631 := bstep (se 1 (by rfl) ⟨2476223, by rfl⟩ : syracuseStep 3301631 = 4952447) B4952447
theorem B2201087 : Blo 2199435 2201087 := bstep (se 1 (by rfl) ⟨1650815, by rfl⟩ : syracuseStep 2201087 = 3301631) B3301631
theorem B3301637 : Blo 2199435 3301637 := bbase (se 4 (by rfl) ⟨309528, by rfl⟩ : syracuseStep 3301637 = 619057) (by norm_num)
theorem B2201091 : Blo 2199435 2201091 := bstep (se 1 (by rfl) ⟨1650818, by rfl⟩ : syracuseStep 2201091 = 3301637) B3301637
theorem B3714349 : Blo 2199435 3714349 := bbase (se 3 (by rfl) ⟨696440, by rfl⟩ : syracuseStep 3714349 = 1392881) (by norm_num)
theorem B4952465 : Blo 2199435 4952465 := bstep (se 2 (by rfl) ⟨1857174, by rfl⟩ : syracuseStep 4952465 = 3714349) B3714349
theorem B3301643 : Blo 2199435 3301643 := bstep (se 1 (by rfl) ⟨2476232, by rfl⟩ : syracuseStep 3301643 = 4952465) B4952465
theorem B2201095 : Blo 2199435 2201095 := bstep (se 1 (by rfl) ⟨1650821, by rfl⟩ : syracuseStep 2201095 = 3301643) B3301643
theorem B2476237 : Blo 2199435 2476237 := bbase (se 3 (by rfl) ⟨464294, by rfl⟩ : syracuseStep 2476237 = 928589) (by norm_num)
theorem B3301649 : Blo 2199435 3301649 := bstep (se 2 (by rfl) ⟨1238118, by rfl⟩ : syracuseStep 3301649 = 2476237) B2476237
theorem B2201099 : Blo 2199435 2201099 := bstep (se 1 (by rfl) ⟨1650824, by rfl⟩ : syracuseStep 2201099 = 3301649) B3301649
theorem B7428725 : Blo 2199435 7428725 := bbase (se 5 (by rfl) ⟨348221, by rfl⟩ : syracuseStep 7428725 = 696443) (by norm_num)
theorem B4952483 : Blo 2199435 4952483 := bstep (se 1 (by rfl) ⟨3714362, by rfl⟩ : syracuseStep 4952483 = 7428725) B7428725
theorem B3301655 : Blo 2199435 3301655 := bstep (se 1 (by rfl) ⟨2476241, by rfl⟩ : syracuseStep 3301655 = 4952483) B4952483
theorem B2201103 : Blo 2199435 2201103 := bstep (se 1 (by rfl) ⟨1650827, by rfl⟩ : syracuseStep 2201103 = 3301655) B3301655
theorem B3301661 : Blo 2199435 3301661 := bbase (se 3 (by rfl) ⟨619061, by rfl⟩ : syracuseStep 3301661 = 1238123) (by norm_num)
theorem B2201107 : Blo 2199435 2201107 := bstep (se 1 (by rfl) ⟨1650830, by rfl⟩ : syracuseStep 2201107 = 3301661) B3301661
theorem B4952501 : Blo 2199435 4952501 := bbase (se 5 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 4952501 = 464297) (by norm_num)
theorem B3301667 : Blo 2199435 3301667 := bstep (se 1 (by rfl) ⟨2476250, by rfl⟩ : syracuseStep 3301667 = 4952501) B4952501
theorem B2201111 : Blo 2199435 2201111 := bstep (se 1 (by rfl) ⟨1650833, by rfl⟩ : syracuseStep 2201111 = 3301667) B3301667
theorem B5288645 : Blo 2199435 5288645 := bbase (se 4 (by rfl) ⟨495810, by rfl⟩ : syracuseStep 5288645 = 991621) (by norm_num)
theorem B3525763 : Blo 2199435 3525763 := bstep (se 1 (by rfl) ⟨2644322, by rfl⟩ : syracuseStep 3525763 = 5288645) B5288645
theorem B4701017 : Blo 2199435 4701017 := bstep (se 2 (by rfl) ⟨1762881, by rfl⟩ : syracuseStep 4701017 = 3525763) B3525763
theorem B12536045 : Blo 2199435 12536045 := bstep (se 3 (by rfl) ⟨2350508, by rfl⟩ : syracuseStep 12536045 = 4701017) B4701017
theorem B8357363 : Blo 2199435 8357363 := bstep (se 1 (by rfl) ⟨6268022, by rfl⟩ : syracuseStep 8357363 = 12536045) B12536045
theorem B5571575 : Blo 2199435 5571575 := bstep (se 1 (by rfl) ⟨4178681, by rfl⟩ : syracuseStep 5571575 = 8357363) B8357363
theorem B3714383 : Blo 2199435 3714383 := bstep (se 1 (by rfl) ⟨2785787, by rfl⟩ : syracuseStep 3714383 = 5571575) B5571575
theorem B2476255 : Blo 2199435 2476255 := bstep (se 1 (by rfl) ⟨1857191, by rfl⟩ : syracuseStep 2476255 = 3714383) B3714383
theorem B3301673 : Blo 2199435 3301673 := bstep (se 2 (by rfl) ⟨1238127, by rfl⟩ : syracuseStep 3301673 = 2476255) B2476255
theorem B2201115 : Blo 2199435 2201115 := bstep (se 1 (by rfl) ⟨1650836, by rfl⟩ : syracuseStep 2201115 = 3301673) B3301673
theorem B5360813 : Blo 2199435 5360813 := bbase (se 3 (by rfl) ⟨1005152, by rfl⟩ : syracuseStep 5360813 = 2010305) (by norm_num)
theorem B3573875 : Blo 2199435 3573875 := bstep (se 1 (by rfl) ⟨2680406, by rfl⟩ : syracuseStep 3573875 = 5360813) B5360813
theorem B2382583 : Blo 2199435 2382583 := bstep (se 1 (by rfl) ⟨1786937, by rfl⟩ : syracuseStep 2382583 = 3573875) B3573875
theorem B3176777 : Blo 2199435 3176777 := bstep (se 2 (by rfl) ⟨1191291, by rfl⟩ : syracuseStep 3176777 = 2382583) B2382583
theorem B8471405 : Blo 2199435 8471405 := bstep (se 3 (by rfl) ⟨1588388, by rfl⟩ : syracuseStep 8471405 = 3176777) B3176777
theorem B22590413 : Blo 2199435 22590413 := bstep (se 3 (by rfl) ⟨4235702, by rfl⟩ : syracuseStep 22590413 = 8471405) B8471405
theorem B15060275 : Blo 2199435 15060275 := bstep (se 1 (by rfl) ⟨11295206, by rfl⟩ : syracuseStep 15060275 = 22590413) B22590413
theorem B10040183 : Blo 2199435 10040183 := bstep (se 1 (by rfl) ⟨7530137, by rfl⟩ : syracuseStep 10040183 = 15060275) B15060275
theorem B6693455 : Blo 2199435 6693455 := bstep (se 1 (by rfl) ⟨5020091, by rfl⟩ : syracuseStep 6693455 = 10040183) B10040183
theorem B4462303 : Blo 2199435 4462303 := bstep (se 1 (by rfl) ⟨3346727, by rfl⟩ : syracuseStep 4462303 = 6693455) B6693455
theorem B5949737 : Blo 2199435 5949737 := bstep (se 2 (by rfl) ⟨2231151, by rfl⟩ : syracuseStep 5949737 = 4462303) B4462303
theorem B3966491 : Blo 2199435 3966491 := bstep (se 1 (by rfl) ⟨2974868, by rfl⟩ : syracuseStep 3966491 = 5949737) B5949737
theorem B2644327 : Blo 2199435 2644327 := bstep (se 1 (by rfl) ⟨1983245, by rfl⟩ : syracuseStep 2644327 = 3966491) B3966491
theorem B3525769 : Blo 2199435 3525769 := bstep (se 2 (by rfl) ⟨1322163, by rfl⟩ : syracuseStep 3525769 = 2644327) B2644327
theorem B4701025 : Blo 2199435 4701025 := bstep (se 2 (by rfl) ⟨1762884, by rfl⟩ : syracuseStep 4701025 = 3525769) B3525769
theorem B6268033 : Blo 2199435 6268033 := bstep (se 2 (by rfl) ⟨2350512, by rfl⟩ : syracuseStep 6268033 = 4701025) B4701025
theorem B8357377 : Blo 2199435 8357377 := bstep (se 2 (by rfl) ⟨3134016, by rfl⟩ : syracuseStep 8357377 = 6268033) B6268033
theorem B11143169 : Blo 2199435 11143169 := bstep (se 2 (by rfl) ⟨4178688, by rfl⟩ : syracuseStep 11143169 = 8357377) B8357377
theorem B7428779 : Blo 2199435 7428779 := bstep (se 1 (by rfl) ⟨5571584, by rfl⟩ : syracuseStep 7428779 = 11143169) B11143169
theorem B4952519 : Blo 2199435 4952519 := bstep (se 1 (by rfl) ⟨3714389, by rfl⟩ : syracuseStep 4952519 = 7428779) B7428779
theorem B3301679 : Blo 2199435 3301679 := bstep (se 1 (by rfl) ⟨2476259, by rfl⟩ : syracuseStep 3301679 = 4952519) B4952519
theorem B2201119 : Blo 2199435 2201119 := bstep (se 1 (by rfl) ⟨1650839, by rfl⟩ : syracuseStep 2201119 = 3301679) B3301679
theorem B3301685 : Blo 2199435 3301685 := bbase (se 5 (by rfl) ⟨154766, by rfl⟩ : syracuseStep 3301685 = 309533) (by norm_num)
theorem B2201123 : Blo 2199435 2201123 := bstep (se 1 (by rfl) ⟨1650842, by rfl⟩ : syracuseStep 2201123 = 3301685) B3301685
theorem B5571605 : Blo 2199435 5571605 := bbase (se 6 (by rfl) ⟨130584, by rfl⟩ : syracuseStep 5571605 = 261169) (by norm_num)
theorem B3714403 : Blo 2199435 3714403 := bstep (se 1 (by rfl) ⟨2785802, by rfl⟩ : syracuseStep 3714403 = 5571605) B5571605
theorem B4952537 : Blo 2199435 4952537 := bstep (se 2 (by rfl) ⟨1857201, by rfl⟩ : syracuseStep 4952537 = 3714403) B3714403
theorem B3301691 : Blo 2199435 3301691 := bstep (se 1 (by rfl) ⟨2476268, by rfl⟩ : syracuseStep 3301691 = 4952537) B4952537
theorem B2201127 : Blo 2199435 2201127 := bstep (se 1 (by rfl) ⟨1650845, by rfl⟩ : syracuseStep 2201127 = 3301691) B3301691
theorem B2476273 : Blo 2199435 2476273 := bbase (se 2 (by rfl) ⟨928602, by rfl⟩ : syracuseStep 2476273 = 1857205) (by norm_num)
theorem B3301697 : Blo 2199435 3301697 := bstep (se 2 (by rfl) ⟨1238136, by rfl⟩ : syracuseStep 3301697 = 2476273) B2476273
theorem B2201131 : Blo 2199435 2201131 := bstep (se 1 (by rfl) ⟨1650848, by rfl⟩ : syracuseStep 2201131 = 3301697) B3301697
theorem B3264077 : Blo 2199435 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B8704205 : Blo 2199435 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B5802803 : Blo 2199435 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B3868535 : Blo 2199435 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B2579023 : Blo 2199435 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B3438697 : Blo 2199435 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B4584929 : Blo 2199435 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B48905909 : Blo 2199435 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B32603939 : Blo 2199435 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B21735959 : Blo 2199435 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B57962557 : Blo 2199435 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B77283409 : Blo 2199435 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B103044545 : Blo 2199435 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B68696363 : Blo 2199435 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B45797575 : Blo 2199435 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B61063433 : Blo 2199435 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B40708955 : Blo 2199435 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B27139303 : Blo 2199435 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B36185737 : Blo 2199435 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B48247649 : Blo 2199435 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B32165099 : Blo 2199435 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B21443399 : Blo 2199435 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B14295599 : Blo 2199435 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B9530399 : Blo 2199435 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B25414397 : Blo 2199435 25414397 := bstep (se 3 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 25414397 = 9530399) B9530399
theorem B16942931 : Blo 2199435 16942931 := bstep (se 1 (by rfl) ⟨12707198, by rfl⟩ : syracuseStep 16942931 = 25414397) B25414397
theorem B11295287 : Blo 2199435 11295287 := bstep (se 1 (by rfl) ⟨8471465, by rfl⟩ : syracuseStep 11295287 = 16942931) B16942931
theorem B7530191 : Blo 2199435 7530191 := bstep (se 1 (by rfl) ⟨5647643, by rfl⟩ : syracuseStep 7530191 = 11295287) B11295287
theorem B5020127 : Blo 2199435 5020127 := bstep (se 1 (by rfl) ⟨3765095, by rfl⟩ : syracuseStep 5020127 = 7530191) B7530191
theorem B3346751 : Blo 2199435 3346751 := bstep (se 1 (by rfl) ⟨2510063, by rfl⟩ : syracuseStep 3346751 = 5020127) B5020127
theorem B8924669 : Blo 2199435 8924669 := bstep (se 3 (by rfl) ⟨1673375, by rfl⟩ : syracuseStep 8924669 = 3346751) B3346751
theorem B5949779 : Blo 2199435 5949779 := bstep (se 1 (by rfl) ⟨4462334, by rfl⟩ : syracuseStep 5949779 = 8924669) B8924669
theorem B15866077 : Blo 2199435 15866077 := bstep (se 3 (by rfl) ⟨2974889, by rfl⟩ : syracuseStep 15866077 = 5949779) B5949779
theorem B21154769 : Blo 2199435 21154769 := bstep (se 2 (by rfl) ⟨7933038, by rfl⟩ : syracuseStep 21154769 = 15866077) B15866077
theorem B14103179 : Blo 2199435 14103179 := bstep (se 1 (by rfl) ⟨10577384, by rfl⟩ : syracuseStep 14103179 = 21154769) B21154769
theorem B9402119 : Blo 2199435 9402119 := bstep (se 1 (by rfl) ⟨7051589, by rfl⟩ : syracuseStep 9402119 = 14103179) B14103179
theorem B6268079 : Blo 2199435 6268079 := bstep (se 1 (by rfl) ⟨4701059, by rfl⟩ : syracuseStep 6268079 = 9402119) B9402119
theorem B4178719 : Blo 2199435 4178719 := bstep (se 1 (by rfl) ⟨3134039, by rfl⟩ : syracuseStep 4178719 = 6268079) B6268079
theorem B5571625 : Blo 2199435 5571625 := bstep (se 2 (by rfl) ⟨2089359, by rfl⟩ : syracuseStep 5571625 = 4178719) B4178719
theorem B7428833 : Blo 2199435 7428833 := bstep (se 2 (by rfl) ⟨2785812, by rfl⟩ : syracuseStep 7428833 = 5571625) B5571625
theorem B4952555 : Blo 2199435 4952555 := bstep (se 1 (by rfl) ⟨3714416, by rfl⟩ : syracuseStep 4952555 = 7428833) B7428833
theorem B3301703 : Blo 2199435 3301703 := bstep (se 1 (by rfl) ⟨2476277, by rfl⟩ : syracuseStep 3301703 = 4952555) B4952555
theorem B2201135 : Blo 2199435 2201135 := bstep (se 1 (by rfl) ⟨1650851, by rfl⟩ : syracuseStep 2201135 = 3301703) B3301703
theorem B3301709 : Blo 2199435 3301709 := bbase (se 3 (by rfl) ⟨619070, by rfl⟩ : syracuseStep 3301709 = 1238141) (by norm_num)
theorem B2201139 : Blo 2199435 2201139 := bstep (se 1 (by rfl) ⟨1650854, by rfl⟩ : syracuseStep 2201139 = 3301709) B3301709
theorem B4952573 : Blo 2199435 4952573 := bbase (se 3 (by rfl) ⟨928607, by rfl⟩ : syracuseStep 4952573 = 1857215) (by norm_num)
theorem B3301715 : Blo 2199435 3301715 := bstep (se 1 (by rfl) ⟨2476286, by rfl⟩ : syracuseStep 3301715 = 4952573) B4952573
theorem B2201143 : Blo 2199435 2201143 := bstep (se 1 (by rfl) ⟨1650857, by rfl⟩ : syracuseStep 2201143 = 3301715) B3301715
theorem B3714437 : Blo 2199435 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B2476291 : Blo 2199435 2476291 := bstep (se 1 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 2476291 = 3714437) B3714437
theorem B3301721 : Blo 2199435 3301721 := bstep (se 2 (by rfl) ⟨1238145, by rfl⟩ : syracuseStep 3301721 = 2476291) B2476291
theorem B2201147 : Blo 2199435 2201147 := bstep (se 1 (by rfl) ⟨1650860, by rfl⟩ : syracuseStep 2201147 = 3301721) B3301721
theorem B16714997 : Blo 2199435 16714997 := bbase (se 5 (by rfl) ⟨783515, by rfl⟩ : syracuseStep 16714997 = 1567031) (by norm_num)
theorem B11143331 : Blo 2199435 11143331 := bstep (se 1 (by rfl) ⟨8357498, by rfl⟩ : syracuseStep 11143331 = 16714997) B16714997
theorem B7428887 : Blo 2199435 7428887 := bstep (se 1 (by rfl) ⟨5571665, by rfl⟩ : syracuseStep 7428887 = 11143331) B11143331
theorem B4952591 : Blo 2199435 4952591 := bstep (se 1 (by rfl) ⟨3714443, by rfl⟩ : syracuseStep 4952591 = 7428887) B7428887
theorem B3301727 : Blo 2199435 3301727 := bstep (se 1 (by rfl) ⟨2476295, by rfl⟩ : syracuseStep 3301727 = 4952591) B4952591
theorem B2201151 : Blo 2199435 2201151 := bstep (se 1 (by rfl) ⟨1650863, by rfl⟩ : syracuseStep 2201151 = 3301727) B3301727
theorem B3301733 : Blo 2199435 3301733 := bbase (se 4 (by rfl) ⟨309537, by rfl⟩ : syracuseStep 3301733 = 619075) (by norm_num)
theorem B2201155 : Blo 2199435 2201155 := bstep (se 1 (by rfl) ⟨1650866, by rfl⟩ : syracuseStep 2201155 = 3301733) B3301733
theorem B4178765 : Blo 2199435 4178765 := bbase (se 3 (by rfl) ⟨783518, by rfl⟩ : syracuseStep 4178765 = 1567037) (by norm_num)
theorem B2785843 : Blo 2199435 2785843 := bstep (se 1 (by rfl) ⟨2089382, by rfl⟩ : syracuseStep 2785843 = 4178765) B4178765
theorem B3714457 : Blo 2199435 3714457 := bstep (se 2 (by rfl) ⟨1392921, by rfl⟩ : syracuseStep 3714457 = 2785843) B2785843
theorem B4952609 : Blo 2199435 4952609 := bstep (se 2 (by rfl) ⟨1857228, by rfl⟩ : syracuseStep 4952609 = 3714457) B3714457
theorem B3301739 : Blo 2199435 3301739 := bstep (se 1 (by rfl) ⟨2476304, by rfl⟩ : syracuseStep 3301739 = 4952609) B4952609
theorem B2201159 : Blo 2199435 2201159 := bstep (se 1 (by rfl) ⟨1650869, by rfl⟩ : syracuseStep 2201159 = 3301739) B3301739
theorem B2476309 : Blo 2199435 2476309 := bbase (se 6 (by rfl) ⟨58038, by rfl⟩ : syracuseStep 2476309 = 116077) (by norm_num)
theorem B3301745 : Blo 2199435 3301745 := bstep (se 2 (by rfl) ⟨1238154, by rfl⟩ : syracuseStep 3301745 = 2476309) B2476309
theorem B2201163 : Blo 2199435 2201163 := bstep (se 1 (by rfl) ⟨1650872, by rfl⟩ : syracuseStep 2201163 = 3301745) B3301745
theorem B2785853 : Blo 2199435 2785853 := bbase (se 3 (by rfl) ⟨522347, by rfl⟩ : syracuseStep 2785853 = 1044695) (by norm_num)
theorem B7428941 : Blo 2199435 7428941 := bstep (se 3 (by rfl) ⟨1392926, by rfl⟩ : syracuseStep 7428941 = 2785853) B2785853
theorem B4952627 : Blo 2199435 4952627 := bstep (se 1 (by rfl) ⟨3714470, by rfl⟩ : syracuseStep 4952627 = 7428941) B7428941
theorem B3301751 : Blo 2199435 3301751 := bstep (se 1 (by rfl) ⟨2476313, by rfl⟩ : syracuseStep 3301751 = 4952627) B4952627
theorem B2201167 : Blo 2199435 2201167 := bstep (se 1 (by rfl) ⟨1650875, by rfl⟩ : syracuseStep 2201167 = 3301751) B3301751
theorem B3301757 : Blo 2199435 3301757 := bbase (se 3 (by rfl) ⟨619079, by rfl⟩ : syracuseStep 3301757 = 1238159) (by norm_num)
theorem B2201171 : Blo 2199435 2201171 := bstep (se 1 (by rfl) ⟨1650878, by rfl⟩ : syracuseStep 2201171 = 3301757) B3301757
theorem B4952645 : Blo 2199435 4952645 := bbase (se 4 (by rfl) ⟨464310, by rfl⟩ : syracuseStep 4952645 = 928621) (by norm_num)
theorem B3301763 : Blo 2199435 3301763 := bstep (se 1 (by rfl) ⟨2476322, by rfl⟩ : syracuseStep 3301763 = 4952645) B4952645
theorem B2201175 : Blo 2199435 2201175 := bstep (se 1 (by rfl) ⟨1650881, by rfl⟩ : syracuseStep 2201175 = 3301763) B3301763
theorem B2350577 : Blo 2199435 2350577 := bbase (se 2 (by rfl) ⟨881466, by rfl⟩ : syracuseStep 2350577 = 1762933) (by norm_num)
theorem B6268205 : Blo 2199435 6268205 := bstep (se 3 (by rfl) ⟨1175288, by rfl⟩ : syracuseStep 6268205 = 2350577) B2350577
theorem B4178803 : Blo 2199435 4178803 := bstep (se 1 (by rfl) ⟨3134102, by rfl⟩ : syracuseStep 4178803 = 6268205) B6268205
theorem B5571737 : Blo 2199435 5571737 := bstep (se 2 (by rfl) ⟨2089401, by rfl⟩ : syracuseStep 5571737 = 4178803) B4178803
theorem B3714491 : Blo 2199435 3714491 := bstep (se 1 (by rfl) ⟨2785868, by rfl⟩ : syracuseStep 3714491 = 5571737) B5571737
theorem B2476327 : Blo 2199435 2476327 := bstep (se 1 (by rfl) ⟨1857245, by rfl⟩ : syracuseStep 2476327 = 3714491) B3714491
theorem B3301769 : Blo 2199435 3301769 := bstep (se 2 (by rfl) ⟨1238163, by rfl⟩ : syracuseStep 3301769 = 2476327) B2476327
theorem B2201179 : Blo 2199435 2201179 := bstep (se 1 (by rfl) ⟨1650884, by rfl⟩ : syracuseStep 2201179 = 3301769) B3301769
theorem B11143493 : Blo 2199435 11143493 := bbase (se 4 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 11143493 = 2089405) (by norm_num)
theorem B7428995 : Blo 2199435 7428995 := bstep (se 1 (by rfl) ⟨5571746, by rfl⟩ : syracuseStep 7428995 = 11143493) B11143493
theorem B4952663 : Blo 2199435 4952663 := bstep (se 1 (by rfl) ⟨3714497, by rfl⟩ : syracuseStep 4952663 = 7428995) B7428995
theorem B3301775 : Blo 2199435 3301775 := bstep (se 1 (by rfl) ⟨2476331, by rfl⟩ : syracuseStep 3301775 = 4952663) B4952663
theorem B2201183 : Blo 2199435 2201183 := bstep (se 1 (by rfl) ⟨1650887, by rfl⟩ : syracuseStep 2201183 = 3301775) B3301775
theorem B3301781 : Blo 2199435 3301781 := bbase (se 6 (by rfl) ⟨77385, by rfl⟩ : syracuseStep 3301781 = 154771) (by norm_num)
theorem B2201187 : Blo 2199435 2201187 := bstep (se 1 (by rfl) ⟨1650890, by rfl⟩ : syracuseStep 2201187 = 3301781) B3301781
theorem B5724845 : Blo 2199435 5724845 := bbase (se 3 (by rfl) ⟨1073408, by rfl⟩ : syracuseStep 5724845 = 2146817) (by norm_num)
theorem B3816563 : Blo 2199435 3816563 := bstep (se 1 (by rfl) ⟨2862422, by rfl⟩ : syracuseStep 3816563 = 5724845) B5724845
theorem B10177501 : Blo 2199435 10177501 := bstep (se 3 (by rfl) ⟨1908281, by rfl⟩ : syracuseStep 10177501 = 3816563) B3816563
theorem B13570001 : Blo 2199435 13570001 := bstep (se 2 (by rfl) ⟨5088750, by rfl⟩ : syracuseStep 13570001 = 10177501) B10177501
theorem B9046667 : Blo 2199435 9046667 := bstep (se 1 (by rfl) ⟨6785000, by rfl⟩ : syracuseStep 9046667 = 13570001) B13570001
theorem B6031111 : Blo 2199435 6031111 := bstep (se 1 (by rfl) ⟨4523333, by rfl⟩ : syracuseStep 6031111 = 9046667) B9046667
theorem B8041481 : Blo 2199435 8041481 := bstep (se 2 (by rfl) ⟨3015555, by rfl⟩ : syracuseStep 8041481 = 6031111) B6031111
theorem B5360987 : Blo 2199435 5360987 := bstep (se 1 (by rfl) ⟨4020740, by rfl⟩ : syracuseStep 5360987 = 8041481) B8041481
theorem B3573991 : Blo 2199435 3573991 := bstep (se 1 (by rfl) ⟨2680493, by rfl⟩ : syracuseStep 3573991 = 5360987) B5360987
theorem B4765321 : Blo 2199435 4765321 := bstep (se 2 (by rfl) ⟨1786995, by rfl⟩ : syracuseStep 4765321 = 3573991) B3573991
theorem B25415045 : Blo 2199435 25415045 := bstep (se 4 (by rfl) ⟨2382660, by rfl⟩ : syracuseStep 25415045 = 4765321) B4765321
theorem B16943363 : Blo 2199435 16943363 := bstep (se 1 (by rfl) ⟨12707522, by rfl⟩ : syracuseStep 16943363 = 25415045) B25415045
theorem B11295575 : Blo 2199435 11295575 := bstep (se 1 (by rfl) ⟨8471681, by rfl⟩ : syracuseStep 11295575 = 16943363) B16943363
theorem B7530383 : Blo 2199435 7530383 := bstep (se 1 (by rfl) ⟨5647787, by rfl⟩ : syracuseStep 7530383 = 11295575) B11295575
theorem B5020255 : Blo 2199435 5020255 := bstep (se 1 (by rfl) ⟨3765191, by rfl⟩ : syracuseStep 5020255 = 7530383) B7530383
theorem B6693673 : Blo 2199435 6693673 := bstep (se 2 (by rfl) ⟨2510127, by rfl⟩ : syracuseStep 6693673 = 5020255) B5020255
theorem B8924897 : Blo 2199435 8924897 := bstep (se 2 (by rfl) ⟨3346836, by rfl⟩ : syracuseStep 8924897 = 6693673) B6693673
theorem B5949931 : Blo 2199435 5949931 := bstep (se 1 (by rfl) ⟨4462448, by rfl⟩ : syracuseStep 5949931 = 8924897) B8924897
theorem B7933241 : Blo 2199435 7933241 := bstep (se 2 (by rfl) ⟨2974965, by rfl⟩ : syracuseStep 7933241 = 5949931) B5949931
theorem B5288827 : Blo 2199435 5288827 := bstep (se 1 (by rfl) ⟨3966620, by rfl⟩ : syracuseStep 5288827 = 7933241) B7933241
theorem B7051769 : Blo 2199435 7051769 := bstep (se 2 (by rfl) ⟨2644413, by rfl⟩ : syracuseStep 7051769 = 5288827) B5288827
theorem B4701179 : Blo 2199435 4701179 := bstep (se 1 (by rfl) ⟨3525884, by rfl⟩ : syracuseStep 4701179 = 7051769) B7051769
theorem B12536477 : Blo 2199435 12536477 := bstep (se 3 (by rfl) ⟨2350589, by rfl⟩ : syracuseStep 12536477 = 4701179) B4701179
theorem B8357651 : Blo 2199435 8357651 := bstep (se 1 (by rfl) ⟨6268238, by rfl⟩ : syracuseStep 8357651 = 12536477) B12536477
theorem B5571767 : Blo 2199435 5571767 := bstep (se 1 (by rfl) ⟨4178825, by rfl⟩ : syracuseStep 5571767 = 8357651) B8357651
theorem B3714511 : Blo 2199435 3714511 := bstep (se 1 (by rfl) ⟨2785883, by rfl⟩ : syracuseStep 3714511 = 5571767) B5571767
theorem B4952681 : Blo 2199435 4952681 := bstep (se 2 (by rfl) ⟨1857255, by rfl⟩ : syracuseStep 4952681 = 3714511) B3714511
theorem B3301787 : Blo 2199435 3301787 := bstep (se 1 (by rfl) ⟨2476340, by rfl⟩ : syracuseStep 3301787 = 4952681) B4952681
theorem B2201191 : Blo 2199435 2201191 := bstep (se 1 (by rfl) ⟨1650893, by rfl⟩ : syracuseStep 2201191 = 3301787) B3301787
theorem B2476345 : Blo 2199435 2476345 := bbase (se 2 (by rfl) ⟨928629, by rfl⟩ : syracuseStep 2476345 = 1857259) (by norm_num)
theorem B3301793 : Blo 2199435 3301793 := bstep (se 2 (by rfl) ⟨1238172, by rfl⟩ : syracuseStep 3301793 = 2476345) B2476345
theorem B2201195 : Blo 2199435 2201195 := bstep (se 1 (by rfl) ⟨1650896, by rfl⟩ : syracuseStep 2201195 = 3301793) B3301793
theorem B6268261 : Blo 2199435 6268261 := bbase (se 4 (by rfl) ⟨587649, by rfl⟩ : syracuseStep 6268261 = 1175299) (by norm_num)
theorem B8357681 : Blo 2199435 8357681 := bstep (se 2 (by rfl) ⟨3134130, by rfl⟩ : syracuseStep 8357681 = 6268261) B6268261
theorem B5571787 : Blo 2199435 5571787 := bstep (se 1 (by rfl) ⟨4178840, by rfl⟩ : syracuseStep 5571787 = 8357681) B8357681
theorem B7429049 : Blo 2199435 7429049 := bstep (se 2 (by rfl) ⟨2785893, by rfl⟩ : syracuseStep 7429049 = 5571787) B5571787
theorem B4952699 : Blo 2199435 4952699 := bstep (se 1 (by rfl) ⟨3714524, by rfl⟩ : syracuseStep 4952699 = 7429049) B7429049
theorem B3301799 : Blo 2199435 3301799 := bstep (se 1 (by rfl) ⟨2476349, by rfl⟩ : syracuseStep 3301799 = 4952699) B4952699
theorem B2201199 : Blo 2199435 2201199 := bstep (se 1 (by rfl) ⟨1650899, by rfl⟩ : syracuseStep 2201199 = 3301799) B3301799
theorem B3301805 : Blo 2199435 3301805 := bbase (se 3 (by rfl) ⟨619088, by rfl⟩ : syracuseStep 3301805 = 1238177) (by norm_num)
theorem B2201203 : Blo 2199435 2201203 := bstep (se 1 (by rfl) ⟨1650902, by rfl⟩ : syracuseStep 2201203 = 3301805) B3301805
theorem B4952717 : Blo 2199435 4952717 := bbase (se 3 (by rfl) ⟨928634, by rfl⟩ : syracuseStep 4952717 = 1857269) (by norm_num)
theorem B3301811 : Blo 2199435 3301811 := bstep (se 1 (by rfl) ⟨2476358, by rfl⟩ : syracuseStep 3301811 = 4952717) B4952717
theorem B2201207 : Blo 2199435 2201207 := bstep (se 1 (by rfl) ⟨1650905, by rfl⟩ : syracuseStep 2201207 = 3301811) B3301811
theorem B2785909 : Blo 2199435 2785909 := bbase (se 5 (by rfl) ⟨130589, by rfl⟩ : syracuseStep 2785909 = 261179) (by norm_num)
theorem B3714545 : Blo 2199435 3714545 := bstep (se 2 (by rfl) ⟨1392954, by rfl⟩ : syracuseStep 3714545 = 2785909) B2785909
theorem B2476363 : Blo 2199435 2476363 := bstep (se 1 (by rfl) ⟨1857272, by rfl⟩ : syracuseStep 2476363 = 3714545) B3714545
theorem B3301817 : Blo 2199435 3301817 := bstep (se 2 (by rfl) ⟨1238181, by rfl⟩ : syracuseStep 3301817 = 2476363) B2476363
theorem B2201211 : Blo 2199435 2201211 := bstep (se 1 (by rfl) ⟨1650908, by rfl⟩ : syracuseStep 2201211 = 3301817) B3301817
theorem B2415193 : Blo 2199435 2415193 := bbase (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) (by norm_num)
theorem B12881029 : Blo 2199435 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B17174705 : Blo 2199435 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B183196853 : Blo 2199435 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B122131235 : Blo 2199435 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B81420823 : Blo 2199435 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B108561097 : Blo 2199435 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B144748129 : Blo 2199435 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B192997505 : Blo 2199435 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B514660013 : Blo 2199435 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B343106675 : Blo 2199435 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B228737783 : Blo 2199435 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B152491855 : Blo 2199435 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B203322473 : Blo 2199435 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B135548315 : Blo 2199435 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B90365543 : Blo 2199435 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B60243695 : Blo 2199435 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B40162463 : Blo 2199435 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B26774975 : Blo 2199435 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B17849983 : Blo 2199435 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B23799977 : Blo 2199435 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B15866651 : Blo 2199435 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B42311069 : Blo 2199435 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B28207379 : Blo 2199435 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B18804919 : Blo 2199435 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B25073225 : Blo 2199435 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B16715483 : Blo 2199435 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B11143655 : Blo 2199435 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B7429103 : Blo 2199435 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B4952735 : Blo 2199435 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B3301823 : Blo 2199435 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B2201215 : Blo 2199435 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B3301829 : Blo 2199435 3301829 := bbase (se 4 (by rfl) ⟨309546, by rfl⟩ : syracuseStep 3301829 = 619093) (by norm_num)
theorem B2201219 : Blo 2199435 2201219 := bstep (se 1 (by rfl) ⟨1650914, by rfl⟩ : syracuseStep 2201219 = 3301829) B3301829
theorem B3714565 : Blo 2199435 3714565 := bbase (se 4 (by rfl) ⟨348240, by rfl⟩ : syracuseStep 3714565 = 696481) (by norm_num)
theorem B4952753 : Blo 2199435 4952753 := bstep (se 2 (by rfl) ⟨1857282, by rfl⟩ : syracuseStep 4952753 = 3714565) B3714565
theorem B3301835 : Blo 2199435 3301835 := bstep (se 1 (by rfl) ⟨2476376, by rfl⟩ : syracuseStep 3301835 = 4952753) B4952753
theorem B2201223 : Blo 2199435 2201223 := bstep (se 1 (by rfl) ⟨1650917, by rfl⟩ : syracuseStep 2201223 = 3301835) B3301835
theorem B2476381 : Blo 2199435 2476381 := bbase (se 3 (by rfl) ⟨464321, by rfl⟩ : syracuseStep 2476381 = 928643) (by norm_num)
theorem B3301841 : Blo 2199435 3301841 := bstep (se 2 (by rfl) ⟨1238190, by rfl⟩ : syracuseStep 3301841 = 2476381) B2476381
theorem B2201227 : Blo 2199435 2201227 := bstep (se 1 (by rfl) ⟨1650920, by rfl⟩ : syracuseStep 2201227 = 3301841) B3301841
theorem B7429157 : Blo 2199435 7429157 := bbase (se 4 (by rfl) ⟨696483, by rfl⟩ : syracuseStep 7429157 = 1392967) (by norm_num)
theorem B4952771 : Blo 2199435 4952771 := bstep (se 1 (by rfl) ⟨3714578, by rfl⟩ : syracuseStep 4952771 = 7429157) B7429157
theorem B3301847 : Blo 2199435 3301847 := bstep (se 1 (by rfl) ⟨2476385, by rfl⟩ : syracuseStep 3301847 = 4952771) B4952771
theorem B2201231 : Blo 2199435 2201231 := bstep (se 1 (by rfl) ⟨1650923, by rfl⟩ : syracuseStep 2201231 = 3301847) B3301847
theorem B3301853 : Blo 2199435 3301853 := bbase (se 3 (by rfl) ⟨619097, by rfl⟩ : syracuseStep 3301853 = 1238195) (by norm_num)
theorem B2201235 : Blo 2199435 2201235 := bstep (se 1 (by rfl) ⟨1650926, by rfl⟩ : syracuseStep 2201235 = 3301853) B3301853
theorem B4952789 : Blo 2199435 4952789 := bbase (se 7 (by rfl) ⟨58040, by rfl⟩ : syracuseStep 4952789 = 116081) (by norm_num)
theorem B3301859 : Blo 2199435 3301859 := bstep (se 1 (by rfl) ⟨2476394, by rfl⟩ : syracuseStep 3301859 = 4952789) B4952789
theorem B2201239 : Blo 2199435 2201239 := bstep (se 1 (by rfl) ⟨1650929, by rfl⟩ : syracuseStep 2201239 = 3301859) B3301859
theorem B9402581 : Blo 2199435 9402581 := bbase (se 7 (by rfl) ⟨110186, by rfl⟩ : syracuseStep 9402581 = 220373) (by norm_num)
theorem B6268387 : Blo 2199435 6268387 := bstep (se 1 (by rfl) ⟨4701290, by rfl⟩ : syracuseStep 6268387 = 9402581) B9402581
theorem B8357849 : Blo 2199435 8357849 := bstep (se 2 (by rfl) ⟨3134193, by rfl⟩ : syracuseStep 8357849 = 6268387) B6268387
theorem B5571899 : Blo 2199435 5571899 := bstep (se 1 (by rfl) ⟨4178924, by rfl⟩ : syracuseStep 5571899 = 8357849) B8357849
theorem B3714599 : Blo 2199435 3714599 := bstep (se 1 (by rfl) ⟨2785949, by rfl⟩ : syracuseStep 3714599 = 5571899) B5571899
theorem B2476399 : Blo 2199435 2476399 := bstep (se 1 (by rfl) ⟨1857299, by rfl⟩ : syracuseStep 2476399 = 3714599) B3714599
theorem B3301865 : Blo 2199435 3301865 := bstep (se 2 (by rfl) ⟨1238199, by rfl⟩ : syracuseStep 3301865 = 2476399) B2476399
theorem B2201243 : Blo 2199435 2201243 := bstep (se 1 (by rfl) ⟨1650932, by rfl⟩ : syracuseStep 2201243 = 3301865) B3301865
theorem B9530885 : Blo 2199435 9530885 := bbase (se 4 (by rfl) ⟨893520, by rfl⟩ : syracuseStep 9530885 = 1787041) (by norm_num)
theorem B6353923 : Blo 2199435 6353923 := bstep (se 1 (by rfl) ⟨4765442, by rfl⟩ : syracuseStep 6353923 = 9530885) B9530885
theorem B8471897 : Blo 2199435 8471897 := bstep (se 2 (by rfl) ⟨3176961, by rfl⟩ : syracuseStep 8471897 = 6353923) B6353923
theorem B5647931 : Blo 2199435 5647931 := bstep (se 1 (by rfl) ⟨4235948, by rfl⟩ : syracuseStep 5647931 = 8471897) B8471897
theorem B3765287 : Blo 2199435 3765287 := bstep (se 1 (by rfl) ⟨2823965, by rfl⟩ : syracuseStep 3765287 = 5647931) B5647931
theorem B2510191 : Blo 2199435 2510191 := bstep (se 1 (by rfl) ⟨1882643, by rfl⟩ : syracuseStep 2510191 = 3765287) B3765287
theorem B3346921 : Blo 2199435 3346921 := bstep (se 2 (by rfl) ⟨1255095, by rfl⟩ : syracuseStep 3346921 = 2510191) B2510191
theorem B4462561 : Blo 2199435 4462561 := bstep (se 2 (by rfl) ⟨1673460, by rfl⟩ : syracuseStep 4462561 = 3346921) B3346921
theorem B5950081 : Blo 2199435 5950081 := bstep (se 2 (by rfl) ⟨2231280, by rfl⟩ : syracuseStep 5950081 = 4462561) B4462561
theorem B31733765 : Blo 2199435 31733765 := bstep (se 4 (by rfl) ⟨2975040, by rfl⟩ : syracuseStep 31733765 = 5950081) B5950081
theorem B21155843 : Blo 2199435 21155843 := bstep (se 1 (by rfl) ⟨15866882, by rfl⟩ : syracuseStep 21155843 = 31733765) B31733765
theorem B14103895 : Blo 2199435 14103895 := bstep (se 1 (by rfl) ⟨10577921, by rfl⟩ : syracuseStep 14103895 = 21155843) B21155843
theorem B18805193 : Blo 2199435 18805193 := bstep (se 2 (by rfl) ⟨7051947, by rfl⟩ : syracuseStep 18805193 = 14103895) B14103895
theorem B12536795 : Blo 2199435 12536795 := bstep (se 1 (by rfl) ⟨9402596, by rfl⟩ : syracuseStep 12536795 = 18805193) B18805193
theorem B8357863 : Blo 2199435 8357863 := bstep (se 1 (by rfl) ⟨6268397, by rfl⟩ : syracuseStep 8357863 = 12536795) B12536795
theorem B11143817 : Blo 2199435 11143817 := bstep (se 2 (by rfl) ⟨4178931, by rfl⟩ : syracuseStep 11143817 = 8357863) B8357863
theorem B7429211 : Blo 2199435 7429211 := bstep (se 1 (by rfl) ⟨5571908, by rfl⟩ : syracuseStep 7429211 = 11143817) B11143817
theorem B4952807 : Blo 2199435 4952807 := bstep (se 1 (by rfl) ⟨3714605, by rfl⟩ : syracuseStep 4952807 = 7429211) B7429211
theorem B3301871 : Blo 2199435 3301871 := bstep (se 1 (by rfl) ⟨2476403, by rfl⟩ : syracuseStep 3301871 = 4952807) B4952807
theorem B2201247 : Blo 2199435 2201247 := bstep (se 1 (by rfl) ⟨1650935, by rfl⟩ : syracuseStep 2201247 = 3301871) B3301871
theorem B3301877 : Blo 2199435 3301877 := bbase (se 5 (by rfl) ⟨154775, by rfl⟩ : syracuseStep 3301877 = 309551) (by norm_num)
theorem B2201251 : Blo 2199435 2201251 := bstep (se 1 (by rfl) ⟨1650938, by rfl⟩ : syracuseStep 2201251 = 3301877) B3301877
theorem B6268421 : Blo 2199435 6268421 := bbase (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) (by norm_num)
theorem B4178947 : Blo 2199435 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B5571929 : Blo 2199435 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B3714619 : Blo 2199435 3714619 := bstep (se 1 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 3714619 = 5571929) B5571929
theorem B4952825 : Blo 2199435 4952825 := bstep (se 2 (by rfl) ⟨1857309, by rfl⟩ : syracuseStep 4952825 = 3714619) B3714619
theorem B3301883 : Blo 2199435 3301883 := bstep (se 1 (by rfl) ⟨2476412, by rfl⟩ : syracuseStep 3301883 = 4952825) B4952825
theorem B2201255 : Blo 2199435 2201255 := bstep (se 1 (by rfl) ⟨1650941, by rfl⟩ : syracuseStep 2201255 = 3301883) B3301883
theorem B2476417 : Blo 2199435 2476417 := bbase (se 2 (by rfl) ⟨928656, by rfl⟩ : syracuseStep 2476417 = 1857313) (by norm_num)
theorem B3301889 : Blo 2199435 3301889 := bstep (se 2 (by rfl) ⟨1238208, by rfl⟩ : syracuseStep 3301889 = 2476417) B2476417
theorem B2201259 : Blo 2199435 2201259 := bstep (se 1 (by rfl) ⟨1650944, by rfl⟩ : syracuseStep 2201259 = 3301889) B3301889
theorem B5571949 : Blo 2199435 5571949 := bbase (se 3 (by rfl) ⟨1044740, by rfl⟩ : syracuseStep 5571949 = 2089481) (by norm_num)
theorem B7429265 : Blo 2199435 7429265 := bstep (se 2 (by rfl) ⟨2785974, by rfl⟩ : syracuseStep 7429265 = 5571949) B5571949
theorem B4952843 : Blo 2199435 4952843 := bstep (se 1 (by rfl) ⟨3714632, by rfl⟩ : syracuseStep 4952843 = 7429265) B7429265
theorem B3301895 : Blo 2199435 3301895 := bstep (se 1 (by rfl) ⟨2476421, by rfl⟩ : syracuseStep 3301895 = 4952843) B4952843
theorem B2201263 : Blo 2199435 2201263 := bstep (se 1 (by rfl) ⟨1650947, by rfl⟩ : syracuseStep 2201263 = 3301895) B3301895
theorem B3301901 : Blo 2199435 3301901 := bbase (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) (by norm_num)
theorem B2201267 : Blo 2199435 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B4952861 : Blo 2199435 4952861 := bbase (se 3 (by rfl) ⟨928661, by rfl⟩ : syracuseStep 4952861 = 1857323) (by norm_num)
theorem B3301907 : Blo 2199435 3301907 := bstep (se 1 (by rfl) ⟨2476430, by rfl⟩ : syracuseStep 3301907 = 4952861) B4952861
theorem B2201271 : Blo 2199435 2201271 := bstep (se 1 (by rfl) ⟨1650953, by rfl⟩ : syracuseStep 2201271 = 3301907) B3301907
theorem B3714653 : Blo 2199435 3714653 := bbase (se 3 (by rfl) ⟨696497, by rfl⟩ : syracuseStep 3714653 = 1392995) (by norm_num)
theorem B2476435 : Blo 2199435 2476435 := bstep (se 1 (by rfl) ⟨1857326, by rfl⟩ : syracuseStep 2476435 = 3714653) B3714653
theorem B3301913 : Blo 2199435 3301913 := bstep (se 2 (by rfl) ⟨1238217, by rfl⟩ : syracuseStep 3301913 = 2476435) B2476435
theorem B2201275 : Blo 2199435 2201275 := bstep (se 1 (by rfl) ⟨1650956, by rfl⟩ : syracuseStep 2201275 = 3301913) B3301913
theorem B6693941 : Blo 2199435 6693941 := bbase (se 5 (by rfl) ⟨313778, by rfl⟩ : syracuseStep 6693941 = 627557) (by norm_num)
theorem B4462627 : Blo 2199435 4462627 := bstep (se 1 (by rfl) ⟨3346970, by rfl⟩ : syracuseStep 4462627 = 6693941) B6693941
theorem B5950169 : Blo 2199435 5950169 := bstep (se 2 (by rfl) ⟨2231313, by rfl⟩ : syracuseStep 5950169 = 4462627) B4462627
theorem B3966779 : Blo 2199435 3966779 := bstep (se 1 (by rfl) ⟨2975084, by rfl⟩ : syracuseStep 3966779 = 5950169) B5950169
theorem B2644519 : Blo 2199435 2644519 := bstep (se 1 (by rfl) ⟨1983389, by rfl⟩ : syracuseStep 2644519 = 3966779) B3966779
theorem B3526025 : Blo 2199435 3526025 := bstep (se 2 (by rfl) ⟨1322259, by rfl⟩ : syracuseStep 3526025 = 2644519) B2644519
theorem B9402733 : Blo 2199435 9402733 := bstep (se 3 (by rfl) ⟨1763012, by rfl⟩ : syracuseStep 9402733 = 3526025) B3526025
theorem B12536977 : Blo 2199435 12536977 := bstep (se 2 (by rfl) ⟨4701366, by rfl⟩ : syracuseStep 12536977 = 9402733) B9402733
theorem B16715969 : Blo 2199435 16715969 := bstep (se 2 (by rfl) ⟨6268488, by rfl⟩ : syracuseStep 16715969 = 12536977) B12536977
theorem B11143979 : Blo 2199435 11143979 := bstep (se 1 (by rfl) ⟨8357984, by rfl⟩ : syracuseStep 11143979 = 16715969) B16715969
theorem B7429319 : Blo 2199435 7429319 := bstep (se 1 (by rfl) ⟨5571989, by rfl⟩ : syracuseStep 7429319 = 11143979) B11143979
theorem B4952879 : Blo 2199435 4952879 := bstep (se 1 (by rfl) ⟨3714659, by rfl⟩ : syracuseStep 4952879 = 7429319) B7429319
theorem B3301919 : Blo 2199435 3301919 := bstep (se 1 (by rfl) ⟨2476439, by rfl⟩ : syracuseStep 3301919 = 4952879) B4952879
theorem B2201279 : Blo 2199435 2201279 := bstep (se 1 (by rfl) ⟨1650959, by rfl⟩ : syracuseStep 2201279 = 3301919) B3301919
theorem B3301925 : Blo 2199435 3301925 := bbase (se 4 (by rfl) ⟨309555, by rfl⟩ : syracuseStep 3301925 = 619111) (by norm_num)
theorem B2201283 : Blo 2199435 2201283 := bstep (se 1 (by rfl) ⟨1650962, by rfl⟩ : syracuseStep 2201283 = 3301925) B3301925
theorem B2786005 : Blo 2199435 2786005 := bbase (se 7 (by rfl) ⟨32648, by rfl⟩ : syracuseStep 2786005 = 65297) (by norm_num)
theorem B3714673 : Blo 2199435 3714673 := bstep (se 2 (by rfl) ⟨1393002, by rfl⟩ : syracuseStep 3714673 = 2786005) B2786005
theorem B4952897 : Blo 2199435 4952897 := bstep (se 2 (by rfl) ⟨1857336, by rfl⟩ : syracuseStep 4952897 = 3714673) B3714673
theorem B3301931 : Blo 2199435 3301931 := bstep (se 1 (by rfl) ⟨2476448, by rfl⟩ : syracuseStep 3301931 = 4952897) B4952897
theorem B2201287 : Blo 2199435 2201287 := bstep (se 1 (by rfl) ⟨1650965, by rfl⟩ : syracuseStep 2201287 = 3301931) B3301931
theorem B2476453 : Blo 2199435 2476453 := bbase (se 4 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 2476453 = 464335) (by norm_num)
theorem B3301937 : Blo 2199435 3301937 := bstep (se 2 (by rfl) ⟨1238226, by rfl⟩ : syracuseStep 3301937 = 2476453) B2476453
theorem B2201291 : Blo 2199435 2201291 := bstep (se 1 (by rfl) ⟨1650968, by rfl⟩ : syracuseStep 2201291 = 3301937) B3301937
theorem B5289077 : Blo 2199435 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B14104205 : Blo 2199435 14104205 := bstep (se 3 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 14104205 = 5289077) B5289077
theorem B9402803 : Blo 2199435 9402803 := bstep (se 1 (by rfl) ⟨7052102, by rfl⟩ : syracuseStep 9402803 = 14104205) B14104205
theorem B6268535 : Blo 2199435 6268535 := bstep (se 1 (by rfl) ⟨4701401, by rfl⟩ : syracuseStep 6268535 = 9402803) B9402803
theorem B4179023 : Blo 2199435 4179023 := bstep (se 1 (by rfl) ⟨3134267, by rfl⟩ : syracuseStep 4179023 = 6268535) B6268535
theorem B2786015 : Blo 2199435 2786015 := bstep (se 1 (by rfl) ⟨2089511, by rfl⟩ : syracuseStep 2786015 = 4179023) B4179023
theorem B7429373 : Blo 2199435 7429373 := bstep (se 3 (by rfl) ⟨1393007, by rfl⟩ : syracuseStep 7429373 = 2786015) B2786015
theorem B4952915 : Blo 2199435 4952915 := bstep (se 1 (by rfl) ⟨3714686, by rfl⟩ : syracuseStep 4952915 = 7429373) B7429373
theorem B3301943 : Blo 2199435 3301943 := bstep (se 1 (by rfl) ⟨2476457, by rfl⟩ : syracuseStep 3301943 = 4952915) B4952915
theorem B2201295 : Blo 2199435 2201295 := bstep (se 1 (by rfl) ⟨1650971, by rfl⟩ : syracuseStep 2201295 = 3301943) B3301943
theorem B3301949 : Blo 2199435 3301949 := bbase (se 3 (by rfl) ⟨619115, by rfl⟩ : syracuseStep 3301949 = 1238231) (by norm_num)
theorem B2201299 : Blo 2199435 2201299 := bstep (se 1 (by rfl) ⟨1650974, by rfl⟩ : syracuseStep 2201299 = 3301949) B3301949
theorem B4952933 : Blo 2199435 4952933 := bbase (se 4 (by rfl) ⟨464337, by rfl⟩ : syracuseStep 4952933 = 928675) (by norm_num)
theorem B3301955 : Blo 2199435 3301955 := bstep (se 1 (by rfl) ⟨2476466, by rfl⟩ : syracuseStep 3301955 = 4952933) B4952933
theorem B2201303 : Blo 2199435 2201303 := bstep (se 1 (by rfl) ⟨1650977, by rfl⟩ : syracuseStep 2201303 = 3301955) B3301955
theorem B5572061 : Blo 2199435 5572061 := bbase (se 3 (by rfl) ⟨1044761, by rfl⟩ : syracuseStep 5572061 = 2089523) (by norm_num)
theorem B3714707 : Blo 2199435 3714707 := bstep (se 1 (by rfl) ⟨2786030, by rfl⟩ : syracuseStep 3714707 = 5572061) B5572061
theorem B2476471 : Blo 2199435 2476471 := bstep (se 1 (by rfl) ⟨1857353, by rfl⟩ : syracuseStep 2476471 = 3714707) B3714707
theorem B3301961 : Blo 2199435 3301961 := bstep (se 2 (by rfl) ⟨1238235, by rfl⟩ : syracuseStep 3301961 = 2476471) B2476471
theorem B2201307 : Blo 2199435 2201307 := bstep (se 1 (by rfl) ⟨1650980, by rfl⟩ : syracuseStep 2201307 = 3301961) B3301961
theorem B4179053 : Blo 2199435 4179053 := bbase (se 3 (by rfl) ⟨783572, by rfl⟩ : syracuseStep 4179053 = 1567145) (by norm_num)
theorem B11144141 : Blo 2199435 11144141 := bstep (se 3 (by rfl) ⟨2089526, by rfl⟩ : syracuseStep 11144141 = 4179053) B4179053
theorem B7429427 : Blo 2199435 7429427 := bstep (se 1 (by rfl) ⟨5572070, by rfl⟩ : syracuseStep 7429427 = 11144141) B11144141
theorem B4952951 : Blo 2199435 4952951 := bstep (se 1 (by rfl) ⟨3714713, by rfl⟩ : syracuseStep 4952951 = 7429427) B7429427
theorem B3301967 : Blo 2199435 3301967 := bstep (se 1 (by rfl) ⟨2476475, by rfl⟩ : syracuseStep 3301967 = 4952951) B4952951
theorem B2201311 : Blo 2199435 2201311 := bstep (se 1 (by rfl) ⟨1650983, by rfl⟩ : syracuseStep 2201311 = 3301967) B3301967
theorem B3301973 : Blo 2199435 3301973 := bbase (se 8 (by rfl) ⟨19347, by rfl⟩ : syracuseStep 3301973 = 38695) (by norm_num)
theorem B2201315 : Blo 2199435 2201315 := bstep (se 1 (by rfl) ⟨1650986, by rfl⟩ : syracuseStep 2201315 = 3301973) B3301973
theorem B5950277 : Blo 2199435 5950277 := bbase (se 4 (by rfl) ⟨557838, by rfl⟩ : syracuseStep 5950277 = 1115677) (by norm_num)
theorem B3966851 : Blo 2199435 3966851 := bstep (se 1 (by rfl) ⟨2975138, by rfl⟩ : syracuseStep 3966851 = 5950277) B5950277
theorem B10578269 : Blo 2199435 10578269 := bstep (se 3 (by rfl) ⟨1983425, by rfl⟩ : syracuseStep 10578269 = 3966851) B3966851
theorem B7052179 : Blo 2199435 7052179 := bstep (se 1 (by rfl) ⟨5289134, by rfl⟩ : syracuseStep 7052179 = 10578269) B10578269
theorem B9402905 : Blo 2199435 9402905 := bstep (se 2 (by rfl) ⟨3526089, by rfl⟩ : syracuseStep 9402905 = 7052179) B7052179
theorem B6268603 : Blo 2199435 6268603 := bstep (se 1 (by rfl) ⟨4701452, by rfl⟩ : syracuseStep 6268603 = 9402905) B9402905
theorem B8358137 : Blo 2199435 8358137 := bstep (se 2 (by rfl) ⟨3134301, by rfl⟩ : syracuseStep 8358137 = 6268603) B6268603
theorem B5572091 : Blo 2199435 5572091 := bstep (se 1 (by rfl) ⟨4179068, by rfl⟩ : syracuseStep 5572091 = 8358137) B8358137
theorem B3714727 : Blo 2199435 3714727 := bstep (se 1 (by rfl) ⟨2786045, by rfl⟩ : syracuseStep 3714727 = 5572091) B5572091
theorem B4952969 : Blo 2199435 4952969 := bstep (se 2 (by rfl) ⟨1857363, by rfl⟩ : syracuseStep 4952969 = 3714727) B3714727
theorem B3301979 : Blo 2199435 3301979 := bstep (se 1 (by rfl) ⟨2476484, by rfl⟩ : syracuseStep 3301979 = 4952969) B4952969
theorem B2201319 : Blo 2199435 2201319 := bstep (se 1 (by rfl) ⟨1650989, by rfl⟩ : syracuseStep 2201319 = 3301979) B3301979
theorem B2476489 : Blo 2199435 2476489 := bbase (se 2 (by rfl) ⟨928683, by rfl⟩ : syracuseStep 2476489 = 1857367) (by norm_num)
theorem B3301985 : Blo 2199435 3301985 := bstep (se 2 (by rfl) ⟨1238244, by rfl⟩ : syracuseStep 3301985 = 2476489) B2476489
theorem B2201323 : Blo 2199435 2201323 := bstep (se 1 (by rfl) ⟨1650992, by rfl⟩ : syracuseStep 2201323 = 3301985) B3301985
theorem B18805877 : Blo 2199435 18805877 := bbase (se 5 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 18805877 = 1763051) (by norm_num)
theorem B12537251 : Blo 2199435 12537251 := bstep (se 1 (by rfl) ⟨9402938, by rfl⟩ : syracuseStep 12537251 = 18805877) B18805877
theorem B8358167 : Blo 2199435 8358167 := bstep (se 1 (by rfl) ⟨6268625, by rfl⟩ : syracuseStep 8358167 = 12537251) B12537251
theorem B5572111 : Blo 2199435 5572111 := bstep (se 1 (by rfl) ⟨4179083, by rfl⟩ : syracuseStep 5572111 = 8358167) B8358167
theorem B7429481 : Blo 2199435 7429481 := bstep (se 2 (by rfl) ⟨2786055, by rfl⟩ : syracuseStep 7429481 = 5572111) B5572111
theorem B4952987 : Blo 2199435 4952987 := bstep (se 1 (by rfl) ⟨3714740, by rfl⟩ : syracuseStep 4952987 = 7429481) B7429481
theorem B3301991 : Blo 2199435 3301991 := bstep (se 1 (by rfl) ⟨2476493, by rfl⟩ : syracuseStep 3301991 = 4952987) B4952987
theorem B2201327 : Blo 2199435 2201327 := bstep (se 1 (by rfl) ⟨1650995, by rfl⟩ : syracuseStep 2201327 = 3301991) B3301991
theorem B3301997 : Blo 2199435 3301997 := bbase (se 3 (by rfl) ⟨619124, by rfl⟩ : syracuseStep 3301997 = 1238249) (by norm_num)
theorem B2201331 : Blo 2199435 2201331 := bstep (se 1 (by rfl) ⟨1650998, by rfl⟩ : syracuseStep 2201331 = 3301997) B3301997
theorem B4953005 : Blo 2199435 4953005 := bbase (se 3 (by rfl) ⟨928688, by rfl⟩ : syracuseStep 4953005 = 1857377) (by norm_num)
theorem B3302003 : Blo 2199435 3302003 := bstep (se 1 (by rfl) ⟨2476502, by rfl⟩ : syracuseStep 3302003 = 4953005) B4953005
theorem B2201335 : Blo 2199435 2201335 := bstep (se 1 (by rfl) ⟨1651001, by rfl⟩ : syracuseStep 2201335 = 3302003) B3302003
theorem B6268661 : Blo 2199435 6268661 := bbase (se 5 (by rfl) ⟨293843, by rfl⟩ : syracuseStep 6268661 = 587687) (by norm_num)
theorem B4179107 : Blo 2199435 4179107 := bstep (se 1 (by rfl) ⟨3134330, by rfl⟩ : syracuseStep 4179107 = 6268661) B6268661
theorem B2786071 : Blo 2199435 2786071 := bstep (se 1 (by rfl) ⟨2089553, by rfl⟩ : syracuseStep 2786071 = 4179107) B4179107
theorem B3714761 : Blo 2199435 3714761 := bstep (se 2 (by rfl) ⟨1393035, by rfl⟩ : syracuseStep 3714761 = 2786071) B2786071
theorem B2476507 : Blo 2199435 2476507 := bstep (se 1 (by rfl) ⟨1857380, by rfl⟩ : syracuseStep 2476507 = 3714761) B3714761
theorem B3302009 : Blo 2199435 3302009 := bstep (se 2 (by rfl) ⟨1238253, by rfl⟩ : syracuseStep 3302009 = 2476507) B2476507
theorem B2201339 : Blo 2199435 2201339 := bstep (se 1 (by rfl) ⟨1651004, by rfl⟩ : syracuseStep 2201339 = 3302009) B3302009
theorem B5434501 : Blo 2199435 5434501 := bbase (se 4 (by rfl) ⟨509484, by rfl⟩ : syracuseStep 5434501 = 1018969) (by norm_num)
theorem B7246001 : Blo 2199435 7246001 := bstep (se 2 (by rfl) ⟨2717250, by rfl⟩ : syracuseStep 7246001 = 5434501) B5434501
theorem B19322669 : Blo 2199435 19322669 := bstep (se 3 (by rfl) ⟨3623000, by rfl⟩ : syracuseStep 19322669 = 7246001) B7246001
theorem B51527117 : Blo 2199435 51527117 := bstep (se 3 (by rfl) ⟨9661334, by rfl⟩ : syracuseStep 51527117 = 19322669) B19322669
theorem B34351411 : Blo 2199435 34351411 := bstep (se 1 (by rfl) ⟨25763558, by rfl⟩ : syracuseStep 34351411 = 51527117) B51527117
theorem B45801881 : Blo 2199435 45801881 := bstep (se 2 (by rfl) ⟨17175705, by rfl⟩ : syracuseStep 45801881 = 34351411) B34351411
theorem B30534587 : Blo 2199435 30534587 := bstep (se 1 (by rfl) ⟨22900940, by rfl⟩ : syracuseStep 30534587 = 45801881) B45801881
theorem B20356391 : Blo 2199435 20356391 := bstep (se 1 (by rfl) ⟨15267293, by rfl⟩ : syracuseStep 20356391 = 30534587) B30534587
theorem B54283709 : Blo 2199435 54283709 := bstep (se 3 (by rfl) ⟨10178195, by rfl⟩ : syracuseStep 54283709 = 20356391) B20356391
theorem B36189139 : Blo 2199435 36189139 := bstep (se 1 (by rfl) ⟨27141854, by rfl⟩ : syracuseStep 36189139 = 54283709) B54283709
theorem B48252185 : Blo 2199435 48252185 := bstep (se 2 (by rfl) ⟨18094569, by rfl⟩ : syracuseStep 48252185 = 36189139) B36189139
theorem B32168123 : Blo 2199435 32168123 := bstep (se 1 (by rfl) ⟨24126092, by rfl⟩ : syracuseStep 32168123 = 48252185) B48252185
theorem B21445415 : Blo 2199435 21445415 := bstep (se 1 (by rfl) ⟨16084061, by rfl⟩ : syracuseStep 21445415 = 32168123) B32168123
theorem B14296943 : Blo 2199435 14296943 := bstep (se 1 (by rfl) ⟨10722707, by rfl⟩ : syracuseStep 14296943 = 21445415) B21445415
theorem B38125181 : Blo 2199435 38125181 := bstep (se 3 (by rfl) ⟨7148471, by rfl⟩ : syracuseStep 38125181 = 14296943) B14296943
theorem B25416787 : Blo 2199435 25416787 := bstep (se 1 (by rfl) ⟨19062590, by rfl⟩ : syracuseStep 25416787 = 38125181) B38125181
theorem B33889049 : Blo 2199435 33889049 := bstep (se 2 (by rfl) ⟨12708393, by rfl⟩ : syracuseStep 33889049 = 25416787) B25416787
theorem B22592699 : Blo 2199435 22592699 := bstep (se 1 (by rfl) ⟨16944524, by rfl⟩ : syracuseStep 22592699 = 33889049) B33889049
theorem B15061799 : Blo 2199435 15061799 := bstep (se 1 (by rfl) ⟨11296349, by rfl⟩ : syracuseStep 15061799 = 22592699) B22592699
theorem B40164797 : Blo 2199435 40164797 := bstep (se 3 (by rfl) ⟨7530899, by rfl⟩ : syracuseStep 40164797 = 15061799) B15061799
theorem B26776531 : Blo 2199435 26776531 := bstep (se 1 (by rfl) ⟨20082398, by rfl⟩ : syracuseStep 26776531 = 40164797) B40164797
theorem B35702041 : Blo 2199435 35702041 := bstep (se 2 (by rfl) ⟨13388265, by rfl⟩ : syracuseStep 35702041 = 26776531) B26776531
theorem B47602721 : Blo 2199435 47602721 := bstep (se 2 (by rfl) ⟨17851020, by rfl⟩ : syracuseStep 47602721 = 35702041) B35702041
theorem B31735147 : Blo 2199435 31735147 := bstep (se 1 (by rfl) ⟨23801360, by rfl⟩ : syracuseStep 31735147 = 47602721) B47602721
theorem B42313529 : Blo 2199435 42313529 := bstep (se 2 (by rfl) ⟨15867573, by rfl⟩ : syracuseStep 42313529 = 31735147) B31735147
theorem B28209019 : Blo 2199435 28209019 := bstep (se 1 (by rfl) ⟨21156764, by rfl⟩ : syracuseStep 28209019 = 42313529) B42313529
theorem B37612025 : Blo 2199435 37612025 := bstep (se 2 (by rfl) ⟨14104509, by rfl⟩ : syracuseStep 37612025 = 28209019) B28209019
theorem B25074683 : Blo 2199435 25074683 := bstep (se 1 (by rfl) ⟨18806012, by rfl⟩ : syracuseStep 25074683 = 37612025) B37612025
theorem B16716455 : Blo 2199435 16716455 := bstep (se 1 (by rfl) ⟨12537341, by rfl⟩ : syracuseStep 16716455 = 25074683) B25074683
theorem B11144303 : Blo 2199435 11144303 := bstep (se 1 (by rfl) ⟨8358227, by rfl⟩ : syracuseStep 11144303 = 16716455) B16716455
theorem B7429535 : Blo 2199435 7429535 := bstep (se 1 (by rfl) ⟨5572151, by rfl⟩ : syracuseStep 7429535 = 11144303) B11144303
theorem B4953023 : Blo 2199435 4953023 := bstep (se 1 (by rfl) ⟨3714767, by rfl⟩ : syracuseStep 4953023 = 7429535) B7429535
theorem B3302015 : Blo 2199435 3302015 := bstep (se 1 (by rfl) ⟨2476511, by rfl⟩ : syracuseStep 3302015 = 4953023) B4953023
theorem B2201343 : Blo 2199435 2201343 := bstep (se 1 (by rfl) ⟨1651007, by rfl⟩ : syracuseStep 2201343 = 3302015) B3302015
theorem B3302021 : Blo 2199435 3302021 := bbase (se 4 (by rfl) ⟨309564, by rfl⟩ : syracuseStep 3302021 = 619129) (by norm_num)
theorem B2201347 : Blo 2199435 2201347 := bstep (se 1 (by rfl) ⟨1651010, by rfl⟩ : syracuseStep 2201347 = 3302021) B3302021
theorem B3714781 : Blo 2199435 3714781 := bbase (se 3 (by rfl) ⟨696521, by rfl⟩ : syracuseStep 3714781 = 1393043) (by norm_num)
theorem B4953041 : Blo 2199435 4953041 := bstep (se 2 (by rfl) ⟨1857390, by rfl⟩ : syracuseStep 4953041 = 3714781) B3714781
theorem B3302027 : Blo 2199435 3302027 := bstep (se 1 (by rfl) ⟨2476520, by rfl⟩ : syracuseStep 3302027 = 4953041) B4953041
theorem B2201351 : Blo 2199435 2201351 := bstep (se 1 (by rfl) ⟨1651013, by rfl⟩ : syracuseStep 2201351 = 3302027) B3302027
theorem B2476525 : Blo 2199435 2476525 := bbase (se 3 (by rfl) ⟨464348, by rfl⟩ : syracuseStep 2476525 = 928697) (by norm_num)
theorem B3302033 : Blo 2199435 3302033 := bstep (se 2 (by rfl) ⟨1238262, by rfl⟩ : syracuseStep 3302033 = 2476525) B2476525
theorem B2201355 : Blo 2199435 2201355 := bstep (se 1 (by rfl) ⟨1651016, by rfl⟩ : syracuseStep 2201355 = 3302033) B3302033
theorem B7429589 : Blo 2199435 7429589 := bbase (se 7 (by rfl) ⟨87065, by rfl⟩ : syracuseStep 7429589 = 174131) (by norm_num)
theorem B4953059 : Blo 2199435 4953059 := bstep (se 1 (by rfl) ⟨3714794, by rfl⟩ : syracuseStep 4953059 = 7429589) B7429589
theorem B3302039 : Blo 2199435 3302039 := bstep (se 1 (by rfl) ⟨2476529, by rfl⟩ : syracuseStep 3302039 = 4953059) B4953059
theorem B2201359 : Blo 2199435 2201359 := bstep (se 1 (by rfl) ⟨1651019, by rfl⟩ : syracuseStep 2201359 = 3302039) B3302039
theorem B3302045 : Blo 2199435 3302045 := bbase (se 3 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 3302045 = 1238267) (by norm_num)
theorem B2201363 : Blo 2199435 2201363 := bstep (se 1 (by rfl) ⟨1651022, by rfl⟩ : syracuseStep 2201363 = 3302045) B3302045
theorem B4953077 : Blo 2199435 4953077 := bbase (se 5 (by rfl) ⟨232175, by rfl⟩ : syracuseStep 4953077 = 464351) (by norm_num)
theorem B3302051 : Blo 2199435 3302051 := bstep (se 1 (by rfl) ⟨2476538, by rfl⟩ : syracuseStep 3302051 = 4953077) B4953077
theorem B2201367 : Blo 2199435 2201367 := bstep (se 1 (by rfl) ⟨1651025, by rfl⟩ : syracuseStep 2201367 = 3302051) B3302051
theorem B22901237 : Blo 2199435 22901237 := bbase (se 5 (by rfl) ⟨1073495, by rfl⟩ : syracuseStep 22901237 = 2146991) (by norm_num)
theorem B15267491 : Blo 2199435 15267491 := bstep (se 1 (by rfl) ⟨11450618, by rfl⟩ : syracuseStep 15267491 = 22901237) B22901237
theorem B10178327 : Blo 2199435 10178327 := bstep (se 1 (by rfl) ⟨7633745, by rfl⟩ : syracuseStep 10178327 = 15267491) B15267491
theorem B6785551 : Blo 2199435 6785551 := bstep (se 1 (by rfl) ⟨5089163, by rfl⟩ : syracuseStep 6785551 = 10178327) B10178327
theorem B36189605 : Blo 2199435 36189605 := bstep (se 4 (by rfl) ⟨3392775, by rfl⟩ : syracuseStep 36189605 = 6785551) B6785551
theorem B96505613 : Blo 2199435 96505613 := bstep (se 3 (by rfl) ⟨18094802, by rfl⟩ : syracuseStep 96505613 = 36189605) B36189605
theorem B64337075 : Blo 2199435 64337075 := bstep (se 1 (by rfl) ⟨48252806, by rfl⟩ : syracuseStep 64337075 = 96505613) B96505613
theorem B42891383 : Blo 2199435 42891383 := bstep (se 1 (by rfl) ⟨32168537, by rfl⟩ : syracuseStep 42891383 = 64337075) B64337075
theorem B28594255 : Blo 2199435 28594255 := bstep (se 1 (by rfl) ⟨21445691, by rfl⟩ : syracuseStep 28594255 = 42891383) B42891383
theorem B38125673 : Blo 2199435 38125673 := bstep (se 2 (by rfl) ⟨14297127, by rfl⟩ : syracuseStep 38125673 = 28594255) B28594255
theorem B25417115 : Blo 2199435 25417115 := bstep (se 1 (by rfl) ⟨19062836, by rfl⟩ : syracuseStep 25417115 = 38125673) B38125673
theorem B16944743 : Blo 2199435 16944743 := bstep (se 1 (by rfl) ⟨12708557, by rfl⟩ : syracuseStep 16944743 = 25417115) B25417115
theorem B11296495 : Blo 2199435 11296495 := bstep (se 1 (by rfl) ⟨8472371, by rfl⟩ : syracuseStep 11296495 = 16944743) B16944743
theorem B15061993 : Blo 2199435 15061993 := bstep (se 2 (by rfl) ⟨5648247, by rfl⟩ : syracuseStep 15061993 = 11296495) B11296495
theorem B80330629 : Blo 2199435 80330629 := bstep (se 4 (by rfl) ⟨7530996, by rfl⟩ : syracuseStep 80330629 = 15061993) B15061993
theorem B107107505 : Blo 2199435 107107505 := bstep (se 2 (by rfl) ⟨40165314, by rfl⟩ : syracuseStep 107107505 = 80330629) B80330629
theorem B71405003 : Blo 2199435 71405003 := bstep (se 1 (by rfl) ⟨53553752, by rfl⟩ : syracuseStep 71405003 = 107107505) B107107505
theorem B47603335 : Blo 2199435 47603335 := bstep (se 1 (by rfl) ⟨35702501, by rfl⟩ : syracuseStep 47603335 = 71405003) B71405003
theorem B63471113 : Blo 2199435 63471113 := bstep (se 2 (by rfl) ⟨23801667, by rfl⟩ : syracuseStep 63471113 = 47603335) B47603335
theorem B42314075 : Blo 2199435 42314075 := bstep (se 1 (by rfl) ⟨31735556, by rfl⟩ : syracuseStep 42314075 = 63471113) B63471113
theorem B28209383 : Blo 2199435 28209383 := bstep (se 1 (by rfl) ⟨21157037, by rfl⟩ : syracuseStep 28209383 = 42314075) B42314075
theorem B18806255 : Blo 2199435 18806255 := bstep (se 1 (by rfl) ⟨14104691, by rfl⟩ : syracuseStep 18806255 = 28209383) B28209383
theorem B12537503 : Blo 2199435 12537503 := bstep (se 1 (by rfl) ⟨9403127, by rfl⟩ : syracuseStep 12537503 = 18806255) B18806255
theorem B8358335 : Blo 2199435 8358335 := bstep (se 1 (by rfl) ⟨6268751, by rfl⟩ : syracuseStep 8358335 = 12537503) B12537503
theorem B5572223 : Blo 2199435 5572223 := bstep (se 1 (by rfl) ⟨4179167, by rfl⟩ : syracuseStep 5572223 = 8358335) B8358335
theorem B3714815 : Blo 2199435 3714815 := bstep (se 1 (by rfl) ⟨2786111, by rfl⟩ : syracuseStep 3714815 = 5572223) B5572223
theorem B2476543 : Blo 2199435 2476543 := bstep (se 1 (by rfl) ⟨1857407, by rfl⟩ : syracuseStep 2476543 = 3714815) B3714815
theorem B3302057 : Blo 2199435 3302057 := bstep (se 2 (by rfl) ⟨1238271, by rfl⟩ : syracuseStep 3302057 = 2476543) B2476543
theorem B2201371 : Blo 2199435 2201371 := bstep (se 1 (by rfl) ⟨1651028, by rfl⟩ : syracuseStep 2201371 = 3302057) B3302057
theorem B3134381 : Blo 2199435 3134381 := bbase (se 3 (by rfl) ⟨587696, by rfl⟩ : syracuseStep 3134381 = 1175393) (by norm_num)
theorem B8358349 : Blo 2199435 8358349 := bstep (se 3 (by rfl) ⟨1567190, by rfl⟩ : syracuseStep 8358349 = 3134381) B3134381
theorem B11144465 : Blo 2199435 11144465 := bstep (se 2 (by rfl) ⟨4179174, by rfl⟩ : syracuseStep 11144465 = 8358349) B8358349
theorem B7429643 : Blo 2199435 7429643 := bstep (se 1 (by rfl) ⟨5572232, by rfl⟩ : syracuseStep 7429643 = 11144465) B11144465
theorem B4953095 : Blo 2199435 4953095 := bstep (se 1 (by rfl) ⟨3714821, by rfl⟩ : syracuseStep 4953095 = 7429643) B7429643
theorem B3302063 : Blo 2199435 3302063 := bstep (se 1 (by rfl) ⟨2476547, by rfl⟩ : syracuseStep 3302063 = 4953095) B4953095
theorem B2201375 : Blo 2199435 2201375 := bstep (se 1 (by rfl) ⟨1651031, by rfl⟩ : syracuseStep 2201375 = 3302063) B3302063
theorem B3302069 : Blo 2199435 3302069 := bbase (se 5 (by rfl) ⟨154784, by rfl⟩ : syracuseStep 3302069 = 309569) (by norm_num)
theorem B2201379 : Blo 2199435 2201379 := bstep (se 1 (by rfl) ⟨1651034, by rfl⟩ : syracuseStep 2201379 = 3302069) B3302069
theorem B5572253 : Blo 2199435 5572253 := bbase (se 3 (by rfl) ⟨1044797, by rfl⟩ : syracuseStep 5572253 = 2089595) (by norm_num)
theorem B3714835 : Blo 2199435 3714835 := bstep (se 1 (by rfl) ⟨2786126, by rfl⟩ : syracuseStep 3714835 = 5572253) B5572253
theorem B4953113 : Blo 2199435 4953113 := bstep (se 2 (by rfl) ⟨1857417, by rfl⟩ : syracuseStep 4953113 = 3714835) B3714835
theorem B3302075 : Blo 2199435 3302075 := bstep (se 1 (by rfl) ⟨2476556, by rfl⟩ : syracuseStep 3302075 = 4953113) B4953113
theorem B2201383 : Blo 2199435 2201383 := bstep (se 1 (by rfl) ⟨1651037, by rfl⟩ : syracuseStep 2201383 = 3302075) B3302075
theorem B2476561 : Blo 2199435 2476561 := bbase (se 2 (by rfl) ⟨928710, by rfl⟩ : syracuseStep 2476561 = 1857421) (by norm_num)
theorem B3302081 : Blo 2199435 3302081 := bstep (se 2 (by rfl) ⟨1238280, by rfl⟩ : syracuseStep 3302081 = 2476561) B2476561
theorem B2201387 : Blo 2199435 2201387 := bstep (se 1 (by rfl) ⟨1651040, by rfl⟩ : syracuseStep 2201387 = 3302081) B3302081
theorem B4179205 : Blo 2199435 4179205 := bbase (se 4 (by rfl) ⟨391800, by rfl⟩ : syracuseStep 4179205 = 783601) (by norm_num)
theorem B5572273 : Blo 2199435 5572273 := bstep (se 2 (by rfl) ⟨2089602, by rfl⟩ : syracuseStep 5572273 = 4179205) B4179205
theorem B7429697 : Blo 2199435 7429697 := bstep (se 2 (by rfl) ⟨2786136, by rfl⟩ : syracuseStep 7429697 = 5572273) B5572273
theorem B4953131 : Blo 2199435 4953131 := bstep (se 1 (by rfl) ⟨3714848, by rfl⟩ : syracuseStep 4953131 = 7429697) B7429697
theorem B3302087 : Blo 2199435 3302087 := bstep (se 1 (by rfl) ⟨2476565, by rfl⟩ : syracuseStep 3302087 = 4953131) B4953131
theorem B2201391 : Blo 2199435 2201391 := bstep (se 1 (by rfl) ⟨1651043, by rfl⟩ : syracuseStep 2201391 = 3302087) B3302087
theorem B3302093 : Blo 2199435 3302093 := bbase (se 3 (by rfl) ⟨619142, by rfl⟩ : syracuseStep 3302093 = 1238285) (by norm_num)
theorem B2201395 : Blo 2199435 2201395 := bstep (se 1 (by rfl) ⟨1651046, by rfl⟩ : syracuseStep 2201395 = 3302093) B3302093
theorem B4953149 : Blo 2199435 4953149 := bbase (se 3 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 4953149 = 1857431) (by norm_num)
theorem B3302099 : Blo 2199435 3302099 := bstep (se 1 (by rfl) ⟨2476574, by rfl⟩ : syracuseStep 3302099 = 4953149) B4953149
theorem B2201399 : Blo 2199435 2201399 := bstep (se 1 (by rfl) ⟨1651049, by rfl⟩ : syracuseStep 2201399 = 3302099) B3302099
theorem B3714869 : Blo 2199435 3714869 := bbase (se 5 (by rfl) ⟨174134, by rfl⟩ : syracuseStep 3714869 = 348269) (by norm_num)
theorem B2476579 : Blo 2199435 2476579 := bstep (se 1 (by rfl) ⟨1857434, by rfl⟩ : syracuseStep 2476579 = 3714869) B3714869
theorem B3302105 : Blo 2199435 3302105 := bstep (se 2 (by rfl) ⟨1238289, by rfl⟩ : syracuseStep 3302105 = 2476579) B2476579
theorem B2201403 : Blo 2199435 2201403 := bstep (se 1 (by rfl) ⟨1651052, by rfl⟩ : syracuseStep 2201403 = 3302105) B3302105
theorem B6268853 : Blo 2199435 6268853 := bbase (se 5 (by rfl) ⟨293852, by rfl⟩ : syracuseStep 6268853 = 587705) (by norm_num)
theorem B16716941 : Blo 2199435 16716941 := bstep (se 3 (by rfl) ⟨3134426, by rfl⟩ : syracuseStep 16716941 = 6268853) B6268853
theorem B11144627 : Blo 2199435 11144627 := bstep (se 1 (by rfl) ⟨8358470, by rfl⟩ : syracuseStep 11144627 = 16716941) B16716941
theorem B7429751 : Blo 2199435 7429751 := bstep (se 1 (by rfl) ⟨5572313, by rfl⟩ : syracuseStep 7429751 = 11144627) B11144627
theorem B4953167 : Blo 2199435 4953167 := bstep (se 1 (by rfl) ⟨3714875, by rfl⟩ : syracuseStep 4953167 = 7429751) B7429751
theorem B3302111 : Blo 2199435 3302111 := bstep (se 1 (by rfl) ⟨2476583, by rfl⟩ : syracuseStep 3302111 = 4953167) B4953167
theorem B2201407 : Blo 2199435 2201407 := bstep (se 1 (by rfl) ⟨1651055, by rfl⟩ : syracuseStep 2201407 = 3302111) B3302111
theorem B3302117 : Blo 2199435 3302117 := bbase (se 4 (by rfl) ⟨309573, by rfl⟩ : syracuseStep 3302117 = 619147) (by norm_num)
theorem B2201411 : Blo 2199435 2201411 := bstep (se 1 (by rfl) ⟨1651058, by rfl⟩ : syracuseStep 2201411 = 3302117) B3302117
theorem B2350829 : Blo 2199435 2350829 := bbase (se 3 (by rfl) ⟨440780, by rfl⟩ : syracuseStep 2350829 = 881561) (by norm_num)
theorem B6268877 : Blo 2199435 6268877 := bstep (se 3 (by rfl) ⟨1175414, by rfl⟩ : syracuseStep 6268877 = 2350829) B2350829
theorem B4179251 : Blo 2199435 4179251 := bstep (se 1 (by rfl) ⟨3134438, by rfl⟩ : syracuseStep 4179251 = 6268877) B6268877
theorem B2786167 : Blo 2199435 2786167 := bstep (se 1 (by rfl) ⟨2089625, by rfl⟩ : syracuseStep 2786167 = 4179251) B4179251
theorem B3714889 : Blo 2199435 3714889 := bstep (se 2 (by rfl) ⟨1393083, by rfl⟩ : syracuseStep 3714889 = 2786167) B2786167
theorem B4953185 : Blo 2199435 4953185 := bstep (se 2 (by rfl) ⟨1857444, by rfl⟩ : syracuseStep 4953185 = 3714889) B3714889
theorem B3302123 : Blo 2199435 3302123 := bstep (se 1 (by rfl) ⟨2476592, by rfl⟩ : syracuseStep 3302123 = 4953185) B4953185
theorem B2201415 : Blo 2199435 2201415 := bstep (se 1 (by rfl) ⟨1651061, by rfl⟩ : syracuseStep 2201415 = 3302123) B3302123
theorem B2476597 : Blo 2199435 2476597 := bbase (se 5 (by rfl) ⟨116090, by rfl⟩ : syracuseStep 2476597 = 232181) (by norm_num)
theorem B3302129 : Blo 2199435 3302129 := bstep (se 2 (by rfl) ⟨1238298, by rfl⟩ : syracuseStep 3302129 = 2476597) B2476597
theorem B2201419 : Blo 2199435 2201419 := bstep (se 1 (by rfl) ⟨1651064, by rfl⟩ : syracuseStep 2201419 = 3302129) B3302129
theorem B2786177 : Blo 2199435 2786177 := bbase (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) (by norm_num)
theorem B7429805 : Blo 2199435 7429805 := bstep (se 3 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 7429805 = 2786177) B2786177
theorem B4953203 : Blo 2199435 4953203 := bstep (se 1 (by rfl) ⟨3714902, by rfl⟩ : syracuseStep 4953203 = 7429805) B7429805
theorem B3302135 : Blo 2199435 3302135 := bstep (se 1 (by rfl) ⟨2476601, by rfl⟩ : syracuseStep 3302135 = 4953203) B4953203
theorem B2201423 : Blo 2199435 2201423 := bstep (se 1 (by rfl) ⟨1651067, by rfl⟩ : syracuseStep 2201423 = 3302135) B3302135
theorem B3302141 : Blo 2199435 3302141 := bbase (se 3 (by rfl) ⟨619151, by rfl⟩ : syracuseStep 3302141 = 1238303) (by norm_num)
theorem B2201427 : Blo 2199435 2201427 := bstep (se 1 (by rfl) ⟨1651070, by rfl⟩ : syracuseStep 2201427 = 3302141) B3302141
theorem B4953221 : Blo 2199435 4953221 := bbase (se 4 (by rfl) ⟨464364, by rfl⟩ : syracuseStep 4953221 = 928729) (by norm_num)
theorem B3302147 : Blo 2199435 3302147 := bstep (se 1 (by rfl) ⟨2476610, by rfl⟩ : syracuseStep 3302147 = 4953221) B4953221
theorem B2201431 : Blo 2199435 2201431 := bstep (se 1 (by rfl) ⟨1651073, by rfl⟩ : syracuseStep 2201431 = 3302147) B3302147
theorem B4701701 : Blo 2199435 4701701 := bbase (se 4 (by rfl) ⟨440784, by rfl⟩ : syracuseStep 4701701 = 881569) (by norm_num)
theorem B3134467 : Blo 2199435 3134467 := bstep (se 1 (by rfl) ⟨2350850, by rfl⟩ : syracuseStep 3134467 = 4701701) B4701701
theorem B4179289 : Blo 2199435 4179289 := bstep (se 2 (by rfl) ⟨1567233, by rfl⟩ : syracuseStep 4179289 = 3134467) B3134467
theorem B5572385 : Blo 2199435 5572385 := bstep (se 2 (by rfl) ⟨2089644, by rfl⟩ : syracuseStep 5572385 = 4179289) B4179289
theorem B3714923 : Blo 2199435 3714923 := bstep (se 1 (by rfl) ⟨2786192, by rfl⟩ : syracuseStep 3714923 = 5572385) B5572385
theorem B2476615 : Blo 2199435 2476615 := bstep (se 1 (by rfl) ⟨1857461, by rfl⟩ : syracuseStep 2476615 = 3714923) B3714923
theorem B3302153 : Blo 2199435 3302153 := bstep (se 2 (by rfl) ⟨1238307, by rfl⟩ : syracuseStep 3302153 = 2476615) B2476615
theorem B2201435 : Blo 2199435 2201435 := bstep (se 1 (by rfl) ⟨1651076, by rfl⟩ : syracuseStep 2201435 = 3302153) B3302153
theorem C0 (j : ℕ) (h1 : 549858 ≤ j) (h2 : j ≤ 550358) : Blo 2199435 (4 * j + 3) := by
  interval_cases j
  · exact B2199435
  · exact B2199439
  · exact B2199443
  · exact B2199447
  · exact B2199451
  · exact B2199455
  · exact B2199459
  · exact B2199463
  · exact B2199467
  · exact B2199471
  · exact B2199475
  · exact B2199479
  · exact B2199483
  · exact B2199487
  · exact B2199491
  · exact B2199495
  · exact B2199499
  · exact B2199503
  · exact B2199507
  · exact B2199511
  · exact B2199515
  · exact B2199519
  · exact B2199523
  · exact B2199527
  · exact B2199531
  · exact B2199535
  · exact B2199539
  · exact B2199543
  · exact B2199547
  · exact B2199551
  · exact B2199555
  · exact B2199559
  · exact B2199563
  · exact B2199567
  · exact B2199571
  · exact B2199575
  · exact B2199579
  · exact B2199583
  · exact B2199587
  · exact B2199591
  · exact B2199595
  · exact B2199599
  · exact B2199603
  · exact B2199607
  · exact B2199611
  · exact B2199615
  · exact B2199619
  · exact B2199623
  · exact B2199627
  · exact B2199631
  · exact B2199635
  · exact B2199639
  · exact B2199643
  · exact B2199647
  · exact B2199651
  · exact B2199655
  · exact B2199659
  · exact B2199663
  · exact B2199667
  · exact B2199671
  · exact B2199675
  · exact B2199679
  · exact B2199683
  · exact B2199687
  · exact B2199691
  · exact B2199695
  · exact B2199699
  · exact B2199703
  · exact B2199707
  · exact B2199711
  · exact B2199715
  · exact B2199719
  · exact B2199723
  · exact B2199727
  · exact B2199731
  · exact B2199735
  · exact B2199739
  · exact B2199743
  · exact B2199747
  · exact B2199751
  · exact B2199755
  · exact B2199759
  · exact B2199763
  · exact B2199767
  · exact B2199771
  · exact B2199775
  · exact B2199779
  · exact B2199783
  · exact B2199787
  · exact B2199791
  · exact B2199795
  · exact B2199799
  · exact B2199803
  · exact B2199807
  · exact B2199811
  · exact B2199815
  · exact B2199819
  · exact B2199823
  · exact B2199827
  · exact B2199831
  · exact B2199835
  · exact B2199839
  · exact B2199843
  · exact B2199847
  · exact B2199851
  · exact B2199855
  · exact B2199859
  · exact B2199863
  · exact B2199867
  · exact B2199871
  · exact B2199875
  · exact B2199879
  · exact B2199883
  · exact B2199887
  · exact B2199891
  · exact B2199895
  · exact B2199899
  · exact B2199903
  · exact B2199907
  · exact B2199911
  · exact B2199915
  · exact B2199919
  · exact B2199923
  · exact B2199927
  · exact B2199931
  · exact B2199935
  · exact B2199939
  · exact B2199943
  · exact B2199947
  · exact B2199951
  · exact B2199955
  · exact B2199959
  · exact B2199963
  · exact B2199967
  · exact B2199971
  · exact B2199975
  · exact B2199979
  · exact B2199983
  · exact B2199987
  · exact B2199991
  · exact B2199995
  · exact B2199999
  · exact B2200003
  · exact B2200007
  · exact B2200011
  · exact B2200015
  · exact B2200019
  · exact B2200023
  · exact B2200027
  · exact B2200031
  · exact B2200035
  · exact B2200039
  · exact B2200043
  · exact B2200047
  · exact B2200051
  · exact B2200055
  · exact B2200059
  · exact B2200063
  · exact B2200067
  · exact B2200071
  · exact B2200075
  · exact B2200079
  · exact B2200083
  · exact B2200087
  · exact B2200091
  · exact B2200095
  · exact B2200099
  · exact B2200103
  · exact B2200107
  · exact B2200111
  · exact B2200115
  · exact B2200119
  · exact B2200123
  · exact B2200127
  · exact B2200131
  · exact B2200135
  · exact B2200139
  · exact B2200143
  · exact B2200147
  · exact B2200151
  · exact B2200155
  · exact B2200159
  · exact B2200163
  · exact B2200167
  · exact B2200171
  · exact B2200175
  · exact B2200179
  · exact B2200183
  · exact B2200187
  · exact B2200191
  · exact B2200195
  · exact B2200199
  · exact B2200203
  · exact B2200207
  · exact B2200211
  · exact B2200215
  · exact B2200219
  · exact B2200223
  · exact B2200227
  · exact B2200231
  · exact B2200235
  · exact B2200239
  · exact B2200243
  · exact B2200247
  · exact B2200251
  · exact B2200255
  · exact B2200259
  · exact B2200263
  · exact B2200267
  · exact B2200271
  · exact B2200275
  · exact B2200279
  · exact B2200283
  · exact B2200287
  · exact B2200291
  · exact B2200295
  · exact B2200299
  · exact B2200303
  · exact B2200307
  · exact B2200311
  · exact B2200315
  · exact B2200319
  · exact B2200323
  · exact B2200327
  · exact B2200331
  · exact B2200335
  · exact B2200339
  · exact B2200343
  · exact B2200347
  · exact B2200351
  · exact B2200355
  · exact B2200359
  · exact B2200363
  · exact B2200367
  · exact B2200371
  · exact B2200375
  · exact B2200379
  · exact B2200383
  · exact B2200387
  · exact B2200391
  · exact B2200395
  · exact B2200399
  · exact B2200403
  · exact B2200407
  · exact B2200411
  · exact B2200415
  · exact B2200419
  · exact B2200423
  · exact B2200427
  · exact B2200431
  · exact B2200435
  · exact B2200439
  · exact B2200443
  · exact B2200447
  · exact B2200451
  · exact B2200455
  · exact B2200459
  · exact B2200463
  · exact B2200467
  · exact B2200471
  · exact B2200475
  · exact B2200479
  · exact B2200483
  · exact B2200487
  · exact B2200491
  · exact B2200495
  · exact B2200499
  · exact B2200503
  · exact B2200507
  · exact B2200511
  · exact B2200515
  · exact B2200519
  · exact B2200523
  · exact B2200527
  · exact B2200531
  · exact B2200535
  · exact B2200539
  · exact B2200543
  · exact B2200547
  · exact B2200551
  · exact B2200555
  · exact B2200559
  · exact B2200563
  · exact B2200567
  · exact B2200571
  · exact B2200575
  · exact B2200579
  · exact B2200583
  · exact B2200587
  · exact B2200591
  · exact B2200595
  · exact B2200599
  · exact B2200603
  · exact B2200607
  · exact B2200611
  · exact B2200615
  · exact B2200619
  · exact B2200623
  · exact B2200627
  · exact B2200631
  · exact B2200635
  · exact B2200639
  · exact B2200643
  · exact B2200647
  · exact B2200651
  · exact B2200655
  · exact B2200659
  · exact B2200663
  · exact B2200667
  · exact B2200671
  · exact B2200675
  · exact B2200679
  · exact B2200683
  · exact B2200687
  · exact B2200691
  · exact B2200695
  · exact B2200699
  · exact B2200703
  · exact B2200707
  · exact B2200711
  · exact B2200715
  · exact B2200719
  · exact B2200723
  · exact B2200727
  · exact B2200731
  · exact B2200735
  · exact B2200739
  · exact B2200743
  · exact B2200747
  · exact B2200751
  · exact B2200755
  · exact B2200759
  · exact B2200763
  · exact B2200767
  · exact B2200771
  · exact B2200775
  · exact B2200779
  · exact B2200783
  · exact B2200787
  · exact B2200791
  · exact B2200795
  · exact B2200799
  · exact B2200803
  · exact B2200807
  · exact B2200811
  · exact B2200815
  · exact B2200819
  · exact B2200823
  · exact B2200827
  · exact B2200831
  · exact B2200835
  · exact B2200839
  · exact B2200843
  · exact B2200847
  · exact B2200851
  · exact B2200855
  · exact B2200859
  · exact B2200863
  · exact B2200867
  · exact B2200871
  · exact B2200875
  · exact B2200879
  · exact B2200883
  · exact B2200887
  · exact B2200891
  · exact B2200895
  · exact B2200899
  · exact B2200903
  · exact B2200907
  · exact B2200911
  · exact B2200915
  · exact B2200919
  · exact B2200923
  · exact B2200927
  · exact B2200931
  · exact B2200935
  · exact B2200939
  · exact B2200943
  · exact B2200947
  · exact B2200951
  · exact B2200955
  · exact B2200959
  · exact B2200963
  · exact B2200967
  · exact B2200971
  · exact B2200975
  · exact B2200979
  · exact B2200983
  · exact B2200987
  · exact B2200991
  · exact B2200995
  · exact B2200999
  · exact B2201003
  · exact B2201007
  · exact B2201011
  · exact B2201015
  · exact B2201019
  · exact B2201023
  · exact B2201027
  · exact B2201031
  · exact B2201035
  · exact B2201039
  · exact B2201043
  · exact B2201047
  · exact B2201051
  · exact B2201055
  · exact B2201059
  · exact B2201063
  · exact B2201067
  · exact B2201071
  · exact B2201075
  · exact B2201079
  · exact B2201083
  · exact B2201087
  · exact B2201091
  · exact B2201095
  · exact B2201099
  · exact B2201103
  · exact B2201107
  · exact B2201111
  · exact B2201115
  · exact B2201119
  · exact B2201123
  · exact B2201127
  · exact B2201131
  · exact B2201135
  · exact B2201139
  · exact B2201143
  · exact B2201147
  · exact B2201151
  · exact B2201155
  · exact B2201159
  · exact B2201163
  · exact B2201167
  · exact B2201171
  · exact B2201175
  · exact B2201179
  · exact B2201183
  · exact B2201187
  · exact B2201191
  · exact B2201195
  · exact B2201199
  · exact B2201203
  · exact B2201207
  · exact B2201211
  · exact B2201215
  · exact B2201219
  · exact B2201223
  · exact B2201227
  · exact B2201231
  · exact B2201235
  · exact B2201239
  · exact B2201243
  · exact B2201247
  · exact B2201251
  · exact B2201255
  · exact B2201259
  · exact B2201263
  · exact B2201267
  · exact B2201271
  · exact B2201275
  · exact B2201279
  · exact B2201283
  · exact B2201287
  · exact B2201291
  · exact B2201295
  · exact B2201299
  · exact B2201303
  · exact B2201307
  · exact B2201311
  · exact B2201315
  · exact B2201319
  · exact B2201323
  · exact B2201327
  · exact B2201331
  · exact B2201335
  · exact B2201339
  · exact B2201343
  · exact B2201347
  · exact B2201351
  · exact B2201355
  · exact B2201359
  · exact B2201363
  · exact B2201367
  · exact B2201371
  · exact B2201375
  · exact B2201379
  · exact B2201383
  · exact B2201387
  · exact B2201391
  · exact B2201395
  · exact B2201399
  · exact B2201403
  · exact B2201407
  · exact B2201411
  · exact B2201415
  · exact B2201419
  · exact B2201423
  · exact B2201427
  · exact B2201431
  · exact B2201435
theorem solution (m : ℕ) (hlo : 2199435 ≤ m) (hhi : m ≤ 2201435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 549858 ≤ j := by omega
    have hj2 : j ≤ 550358 := by omega
    have hb : Blo 2199435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
