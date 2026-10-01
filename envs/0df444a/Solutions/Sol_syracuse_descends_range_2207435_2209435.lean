-- Prove2me | solution 1 for syracuse_descends_range_2207435_2209435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:25.844754+00:00
-- url     : https://prove2.me/submissions/eef0ad4c-2fc6-45ce-afbe-5f133ce3e0ab

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

theorem B2483365 : Blo 2207435 2483365 := bbase (se 4 (by rfl) ⟨232815, by rfl⟩ : syracuseStep 2483365 = 465631) (by norm_num)
theorem B3311153 : Blo 2207435 3311153 := bstep (se 2 (by rfl) ⟨1241682, by rfl⟩ : syracuseStep 3311153 = 2483365) B2483365
theorem B2207435 : Blo 2207435 2207435 := bstep (se 1 (by rfl) ⟨1655576, by rfl⟩ : syracuseStep 2207435 = 3311153) B3311153
theorem B6048229 : Blo 2207435 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B8064305 : Blo 2207435 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B5376203 : Blo 2207435 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B3584135 : Blo 2207435 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B9557693 : Blo 2207435 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B6371795 : Blo 2207435 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B16991453 : Blo 2207435 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B11327635 : Blo 2207435 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B15103513 : Blo 2207435 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B20138017 : Blo 2207435 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B26850689 : Blo 2207435 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B17900459 : Blo 2207435 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B11933639 : Blo 2207435 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B7955759 : Blo 2207435 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B21215357 : Blo 2207435 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B14143571 : Blo 2207435 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B9429047 : Blo 2207435 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B6286031 : Blo 2207435 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B4190687 : Blo 2207435 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B2793791 : Blo 2207435 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B7450109 : Blo 2207435 7450109 := bstep (se 3 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 7450109 = 2793791) B2793791
theorem B4966739 : Blo 2207435 4966739 := bstep (se 1 (by rfl) ⟨3725054, by rfl⟩ : syracuseStep 4966739 = 7450109) B7450109
theorem B3311159 : Blo 2207435 3311159 := bstep (se 1 (by rfl) ⟨2483369, by rfl⟩ : syracuseStep 3311159 = 4966739) B4966739
theorem B2207439 : Blo 2207435 2207439 := bstep (se 1 (by rfl) ⟨1655579, by rfl⟩ : syracuseStep 2207439 = 3311159) B3311159
theorem B3311165 : Blo 2207435 3311165 := bbase (se 3 (by rfl) ⟨620843, by rfl⟩ : syracuseStep 3311165 = 1241687) (by norm_num)
theorem B2207443 : Blo 2207435 2207443 := bstep (se 1 (by rfl) ⟨1655582, by rfl⟩ : syracuseStep 2207443 = 3311165) B3311165
theorem B4966757 : Blo 2207435 4966757 := bbase (se 4 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 4966757 = 931267) (by norm_num)
theorem B3311171 : Blo 2207435 3311171 := bstep (se 1 (by rfl) ⟨2483378, by rfl⟩ : syracuseStep 3311171 = 4966757) B4966757
theorem B2207447 : Blo 2207435 2207447 := bstep (se 1 (by rfl) ⟨1655585, by rfl⟩ : syracuseStep 2207447 = 3311171) B3311171
theorem B5587613 : Blo 2207435 5587613 := bbase (se 3 (by rfl) ⟨1047677, by rfl⟩ : syracuseStep 5587613 = 2095355) (by norm_num)
theorem B3725075 : Blo 2207435 3725075 := bstep (se 1 (by rfl) ⟨2793806, by rfl⟩ : syracuseStep 3725075 = 5587613) B5587613
theorem B2483383 : Blo 2207435 2483383 := bstep (se 1 (by rfl) ⟨1862537, by rfl⟩ : syracuseStep 2483383 = 3725075) B3725075
theorem B3311177 : Blo 2207435 3311177 := bstep (se 2 (by rfl) ⟨1241691, by rfl⟩ : syracuseStep 3311177 = 2483383) B2483383
theorem B2207451 : Blo 2207435 2207451 := bstep (se 1 (by rfl) ⟨1655588, by rfl⟩ : syracuseStep 2207451 = 3311177) B3311177
theorem B4190717 : Blo 2207435 4190717 := bbase (se 3 (by rfl) ⟨785759, by rfl⟩ : syracuseStep 4190717 = 1571519) (by norm_num)
theorem B11175245 : Blo 2207435 11175245 := bstep (se 3 (by rfl) ⟨2095358, by rfl⟩ : syracuseStep 11175245 = 4190717) B4190717
theorem B7450163 : Blo 2207435 7450163 := bstep (se 1 (by rfl) ⟨5587622, by rfl⟩ : syracuseStep 7450163 = 11175245) B11175245
theorem B4966775 : Blo 2207435 4966775 := bstep (se 1 (by rfl) ⟨3725081, by rfl⟩ : syracuseStep 4966775 = 7450163) B7450163
theorem B3311183 : Blo 2207435 3311183 := bstep (se 1 (by rfl) ⟨2483387, by rfl⟩ : syracuseStep 3311183 = 4966775) B4966775
theorem B2207455 : Blo 2207435 2207455 := bstep (se 1 (by rfl) ⟨1655591, by rfl⟩ : syracuseStep 2207455 = 3311183) B3311183
theorem B3311189 : Blo 2207435 3311189 := bbase (se 8 (by rfl) ⟨19401, by rfl⟩ : syracuseStep 3311189 = 38803) (by norm_num)
theorem B2207459 : Blo 2207435 2207459 := bstep (se 1 (by rfl) ⟨1655594, by rfl⟩ : syracuseStep 2207459 = 3311189) B3311189
theorem B5966885 : Blo 2207435 5966885 := bbase (se 4 (by rfl) ⟨559395, by rfl⟩ : syracuseStep 5966885 = 1118791) (by norm_num)
theorem B3977923 : Blo 2207435 3977923 := bstep (se 1 (by rfl) ⟨2983442, by rfl⟩ : syracuseStep 3977923 = 5966885) B5966885
theorem B5303897 : Blo 2207435 5303897 := bstep (se 2 (by rfl) ⟨1988961, by rfl⟩ : syracuseStep 5303897 = 3977923) B3977923
theorem B3535931 : Blo 2207435 3535931 := bstep (se 1 (by rfl) ⟨2651948, by rfl⟩ : syracuseStep 3535931 = 5303897) B5303897
theorem B9429149 : Blo 2207435 9429149 := bstep (se 3 (by rfl) ⟨1767965, by rfl⟩ : syracuseStep 9429149 = 3535931) B3535931
theorem B6286099 : Blo 2207435 6286099 := bstep (se 1 (by rfl) ⟨4714574, by rfl⟩ : syracuseStep 6286099 = 9429149) B9429149
theorem B8381465 : Blo 2207435 8381465 := bstep (se 2 (by rfl) ⟨3143049, by rfl⟩ : syracuseStep 8381465 = 6286099) B6286099
theorem B5587643 : Blo 2207435 5587643 := bstep (se 1 (by rfl) ⟨4190732, by rfl⟩ : syracuseStep 5587643 = 8381465) B8381465
theorem B3725095 : Blo 2207435 3725095 := bstep (se 1 (by rfl) ⟨2793821, by rfl⟩ : syracuseStep 3725095 = 5587643) B5587643
theorem B4966793 : Blo 2207435 4966793 := bstep (se 2 (by rfl) ⟨1862547, by rfl⟩ : syracuseStep 4966793 = 3725095) B3725095
theorem B3311195 : Blo 2207435 3311195 := bstep (se 1 (by rfl) ⟨2483396, by rfl⟩ : syracuseStep 3311195 = 4966793) B4966793
theorem B2207463 : Blo 2207435 2207463 := bstep (se 1 (by rfl) ⟨1655597, by rfl⟩ : syracuseStep 2207463 = 3311195) B3311195
theorem B2483401 : Blo 2207435 2483401 := bbase (se 2 (by rfl) ⟨931275, by rfl⟩ : syracuseStep 2483401 = 1862551) (by norm_num)
theorem B3311201 : Blo 2207435 3311201 := bstep (se 2 (by rfl) ⟨1241700, by rfl⟩ : syracuseStep 3311201 = 2483401) B2483401
theorem B2207467 : Blo 2207435 2207467 := bstep (se 1 (by rfl) ⟨1655600, by rfl⟩ : syracuseStep 2207467 = 3311201) B3311201
theorem B3775933 : Blo 2207435 3775933 := bbase (se 3 (by rfl) ⟨707987, by rfl⟩ : syracuseStep 3775933 = 1415975) (by norm_num)
theorem B5034577 : Blo 2207435 5034577 := bstep (se 2 (by rfl) ⟨1887966, by rfl⟩ : syracuseStep 5034577 = 3775933) B3775933
theorem B6712769 : Blo 2207435 6712769 := bstep (se 2 (by rfl) ⟨2517288, by rfl⟩ : syracuseStep 6712769 = 5034577) B5034577
theorem B4475179 : Blo 2207435 4475179 := bstep (se 1 (by rfl) ⟨3356384, by rfl⟩ : syracuseStep 4475179 = 6712769) B6712769
theorem B23867621 : Blo 2207435 23867621 := bstep (se 4 (by rfl) ⟨2237589, by rfl⟩ : syracuseStep 23867621 = 4475179) B4475179
theorem B15911747 : Blo 2207435 15911747 := bstep (se 1 (by rfl) ⟨11933810, by rfl⟩ : syracuseStep 15911747 = 23867621) B23867621
theorem B10607831 : Blo 2207435 10607831 := bstep (se 1 (by rfl) ⟨7955873, by rfl⟩ : syracuseStep 10607831 = 15911747) B15911747
theorem B7071887 : Blo 2207435 7071887 := bstep (se 1 (by rfl) ⟨5303915, by rfl⟩ : syracuseStep 7071887 = 10607831) B10607831
theorem B18858365 : Blo 2207435 18858365 := bstep (se 3 (by rfl) ⟨3535943, by rfl⟩ : syracuseStep 18858365 = 7071887) B7071887
theorem B12572243 : Blo 2207435 12572243 := bstep (se 1 (by rfl) ⟨9429182, by rfl⟩ : syracuseStep 12572243 = 18858365) B18858365
theorem B8381495 : Blo 2207435 8381495 := bstep (se 1 (by rfl) ⟨6286121, by rfl⟩ : syracuseStep 8381495 = 12572243) B12572243
theorem B5587663 : Blo 2207435 5587663 := bstep (se 1 (by rfl) ⟨4190747, by rfl⟩ : syracuseStep 5587663 = 8381495) B8381495
theorem B7450217 : Blo 2207435 7450217 := bstep (se 2 (by rfl) ⟨2793831, by rfl⟩ : syracuseStep 7450217 = 5587663) B5587663
theorem B4966811 : Blo 2207435 4966811 := bstep (se 1 (by rfl) ⟨3725108, by rfl⟩ : syracuseStep 4966811 = 7450217) B7450217
theorem B3311207 : Blo 2207435 3311207 := bstep (se 1 (by rfl) ⟨2483405, by rfl⟩ : syracuseStep 3311207 = 4966811) B4966811
theorem B2207471 : Blo 2207435 2207471 := bstep (se 1 (by rfl) ⟨1655603, by rfl⟩ : syracuseStep 2207471 = 3311207) B3311207
theorem B3311213 : Blo 2207435 3311213 := bbase (se 3 (by rfl) ⟨620852, by rfl⟩ : syracuseStep 3311213 = 1241705) (by norm_num)
theorem B2207475 : Blo 2207435 2207475 := bstep (se 1 (by rfl) ⟨1655606, by rfl⟩ : syracuseStep 2207475 = 3311213) B3311213
theorem B4966829 : Blo 2207435 4966829 := bbase (se 3 (by rfl) ⟨931280, by rfl⟩ : syracuseStep 4966829 = 1862561) (by norm_num)
theorem B3311219 : Blo 2207435 3311219 := bstep (se 1 (by rfl) ⟨2483414, by rfl⟩ : syracuseStep 3311219 = 4966829) B4966829
theorem B2207479 : Blo 2207435 2207479 := bstep (se 1 (by rfl) ⟨1655609, by rfl⟩ : syracuseStep 2207479 = 3311219) B3311219
theorem B2357309 : Blo 2207435 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B6286157 : Blo 2207435 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B4190771 : Blo 2207435 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B2793847 : Blo 2207435 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B3725129 : Blo 2207435 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B2483419 : Blo 2207435 2483419 := bstep (se 1 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 2483419 = 3725129) B3725129
theorem B3311225 : Blo 2207435 3311225 := bstep (se 2 (by rfl) ⟨1241709, by rfl⟩ : syracuseStep 3311225 = 2483419) B2483419
theorem B2207483 : Blo 2207435 2207483 := bstep (se 1 (by rfl) ⟨1655612, by rfl⟩ : syracuseStep 2207483 = 3311225) B3311225
theorem B8495909 : Blo 2207435 8495909 := bbase (se 4 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 8495909 = 1592983) (by norm_num)
theorem B5663939 : Blo 2207435 5663939 := bstep (se 1 (by rfl) ⟨4247954, by rfl⟩ : syracuseStep 5663939 = 8495909) B8495909
theorem B15103837 : Blo 2207435 15103837 := bstep (se 3 (by rfl) ⟨2831969, by rfl⟩ : syracuseStep 15103837 = 5663939) B5663939
theorem B20138449 : Blo 2207435 20138449 := bstep (se 2 (by rfl) ⟨7551918, by rfl⟩ : syracuseStep 20138449 = 15103837) B15103837
theorem B26851265 : Blo 2207435 26851265 := bstep (se 2 (by rfl) ⟨10069224, by rfl⟩ : syracuseStep 26851265 = 20138449) B20138449
theorem B17900843 : Blo 2207435 17900843 := bstep (se 1 (by rfl) ⟨13425632, by rfl⟩ : syracuseStep 17900843 = 26851265) B26851265
theorem B47735581 : Blo 2207435 47735581 := bstep (se 3 (by rfl) ⟨8950421, by rfl⟩ : syracuseStep 47735581 = 17900843) B17900843
theorem B63647441 : Blo 2207435 63647441 := bstep (se 2 (by rfl) ⟨23867790, by rfl⟩ : syracuseStep 63647441 = 47735581) B47735581
theorem B42431627 : Blo 2207435 42431627 := bstep (se 1 (by rfl) ⟨31823720, by rfl⟩ : syracuseStep 42431627 = 63647441) B63647441
theorem B28287751 : Blo 2207435 28287751 := bstep (se 1 (by rfl) ⟨21215813, by rfl⟩ : syracuseStep 28287751 = 42431627) B42431627
theorem B37717001 : Blo 2207435 37717001 := bstep (se 2 (by rfl) ⟨14143875, by rfl⟩ : syracuseStep 37717001 = 28287751) B28287751
theorem B25144667 : Blo 2207435 25144667 := bstep (se 1 (by rfl) ⟨18858500, by rfl⟩ : syracuseStep 25144667 = 37717001) B37717001
theorem B16763111 : Blo 2207435 16763111 := bstep (se 1 (by rfl) ⟨12572333, by rfl⟩ : syracuseStep 16763111 = 25144667) B25144667
theorem B11175407 : Blo 2207435 11175407 := bstep (se 1 (by rfl) ⟨8381555, by rfl⟩ : syracuseStep 11175407 = 16763111) B16763111
theorem B7450271 : Blo 2207435 7450271 := bstep (se 1 (by rfl) ⟨5587703, by rfl⟩ : syracuseStep 7450271 = 11175407) B11175407
theorem B4966847 : Blo 2207435 4966847 := bstep (se 1 (by rfl) ⟨3725135, by rfl⟩ : syracuseStep 4966847 = 7450271) B7450271
theorem B3311231 : Blo 2207435 3311231 := bstep (se 1 (by rfl) ⟨2483423, by rfl⟩ : syracuseStep 3311231 = 4966847) B4966847
theorem B2207487 : Blo 2207435 2207487 := bstep (se 1 (by rfl) ⟨1655615, by rfl⟩ : syracuseStep 2207487 = 3311231) B3311231
theorem B3311237 : Blo 2207435 3311237 := bbase (se 4 (by rfl) ⟨310428, by rfl⟩ : syracuseStep 3311237 = 620857) (by norm_num)
theorem B2207491 : Blo 2207435 2207491 := bstep (se 1 (by rfl) ⟨1655618, by rfl⟩ : syracuseStep 2207491 = 3311237) B3311237
theorem B3725149 : Blo 2207435 3725149 := bbase (se 3 (by rfl) ⟨698465, by rfl⟩ : syracuseStep 3725149 = 1396931) (by norm_num)
theorem B4966865 : Blo 2207435 4966865 := bstep (se 2 (by rfl) ⟨1862574, by rfl⟩ : syracuseStep 4966865 = 3725149) B3725149
theorem B3311243 : Blo 2207435 3311243 := bstep (se 1 (by rfl) ⟨2483432, by rfl⟩ : syracuseStep 3311243 = 4966865) B4966865
theorem B2207495 : Blo 2207435 2207495 := bstep (se 1 (by rfl) ⟨1655621, by rfl⟩ : syracuseStep 2207495 = 3311243) B3311243
theorem B2483437 : Blo 2207435 2483437 := bbase (se 3 (by rfl) ⟨465644, by rfl⟩ : syracuseStep 2483437 = 931289) (by norm_num)
theorem B3311249 : Blo 2207435 3311249 := bstep (se 2 (by rfl) ⟨1241718, by rfl⟩ : syracuseStep 3311249 = 2483437) B2483437
theorem B2207499 : Blo 2207435 2207499 := bstep (se 1 (by rfl) ⟨1655624, by rfl⟩ : syracuseStep 2207499 = 3311249) B3311249
theorem B7450325 : Blo 2207435 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B4966883 : Blo 2207435 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B3311255 : Blo 2207435 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B2207503 : Blo 2207435 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B3311261 : Blo 2207435 3311261 := bbase (se 3 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 3311261 = 1241723) (by norm_num)
theorem B2207507 : Blo 2207435 2207507 := bstep (se 1 (by rfl) ⟨1655630, by rfl⟩ : syracuseStep 2207507 = 3311261) B3311261
theorem B4966901 : Blo 2207435 4966901 := bbase (se 5 (by rfl) ⟨232823, by rfl⟩ : syracuseStep 4966901 = 465647) (by norm_num)
theorem B3311267 : Blo 2207435 3311267 := bstep (se 1 (by rfl) ⟨2483450, by rfl⟩ : syracuseStep 3311267 = 4966901) B4966901
theorem B2207511 : Blo 2207435 2207511 := bstep (se 1 (by rfl) ⟨1655633, by rfl⟩ : syracuseStep 2207511 = 3311267) B3311267
theorem B7168517 : Blo 2207435 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B4779011 : Blo 2207435 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B12744029 : Blo 2207435 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B8496019 : Blo 2207435 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B11328025 : Blo 2207435 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B15104033 : Blo 2207435 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B10069355 : Blo 2207435 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B6712903 : Blo 2207435 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B8950537 : Blo 2207435 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B11934049 : Blo 2207435 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B15912065 : Blo 2207435 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B42432173 : Blo 2207435 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B28288115 : Blo 2207435 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B18858743 : Blo 2207435 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B12572495 : Blo 2207435 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B8381663 : Blo 2207435 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B5587775 : Blo 2207435 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B3725183 : Blo 2207435 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B2483455 : Blo 2207435 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B3311273 : Blo 2207435 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B2207515 : Blo 2207435 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B3536021 : Blo 2207435 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B2357347 : Blo 2207435 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B3143129 : Blo 2207435 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B8381677 : Blo 2207435 8381677 := bstep (se 3 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 8381677 = 3143129) B3143129
theorem B11175569 : Blo 2207435 11175569 := bstep (se 2 (by rfl) ⟨4190838, by rfl⟩ : syracuseStep 11175569 = 8381677) B8381677
theorem B7450379 : Blo 2207435 7450379 := bstep (se 1 (by rfl) ⟨5587784, by rfl⟩ : syracuseStep 7450379 = 11175569) B11175569
theorem B4966919 : Blo 2207435 4966919 := bstep (se 1 (by rfl) ⟨3725189, by rfl⟩ : syracuseStep 4966919 = 7450379) B7450379
theorem B3311279 : Blo 2207435 3311279 := bstep (se 1 (by rfl) ⟨2483459, by rfl⟩ : syracuseStep 3311279 = 4966919) B4966919
theorem B2207519 : Blo 2207435 2207519 := bstep (se 1 (by rfl) ⟨1655639, by rfl⟩ : syracuseStep 2207519 = 3311279) B3311279
theorem B3311285 : Blo 2207435 3311285 := bbase (se 5 (by rfl) ⟨155216, by rfl⟩ : syracuseStep 3311285 = 310433) (by norm_num)
theorem B2207523 : Blo 2207435 2207523 := bstep (se 1 (by rfl) ⟨1655642, by rfl⟩ : syracuseStep 2207523 = 3311285) B3311285
theorem B5587805 : Blo 2207435 5587805 := bbase (se 3 (by rfl) ⟨1047713, by rfl⟩ : syracuseStep 5587805 = 2095427) (by norm_num)
theorem B3725203 : Blo 2207435 3725203 := bstep (se 1 (by rfl) ⟨2793902, by rfl⟩ : syracuseStep 3725203 = 5587805) B5587805
theorem B4966937 : Blo 2207435 4966937 := bstep (se 2 (by rfl) ⟨1862601, by rfl⟩ : syracuseStep 4966937 = 3725203) B3725203
theorem B3311291 : Blo 2207435 3311291 := bstep (se 1 (by rfl) ⟨2483468, by rfl⟩ : syracuseStep 3311291 = 4966937) B4966937
theorem B2207527 : Blo 2207435 2207527 := bstep (se 1 (by rfl) ⟨1655645, by rfl⟩ : syracuseStep 2207527 = 3311291) B3311291
theorem B2483473 : Blo 2207435 2483473 := bbase (se 2 (by rfl) ⟨931302, by rfl⟩ : syracuseStep 2483473 = 1862605) (by norm_num)
theorem B3311297 : Blo 2207435 3311297 := bstep (se 2 (by rfl) ⟨1241736, by rfl⟩ : syracuseStep 3311297 = 2483473) B2483473
theorem B2207531 : Blo 2207435 2207531 := bstep (se 1 (by rfl) ⟨1655648, by rfl⟩ : syracuseStep 2207531 = 3311297) B3311297
theorem B4190869 : Blo 2207435 4190869 := bbase (se 6 (by rfl) ⟨98223, by rfl⟩ : syracuseStep 4190869 = 196447) (by norm_num)
theorem B5587825 : Blo 2207435 5587825 := bstep (se 2 (by rfl) ⟨2095434, by rfl⟩ : syracuseStep 5587825 = 4190869) B4190869
theorem B7450433 : Blo 2207435 7450433 := bstep (se 2 (by rfl) ⟨2793912, by rfl⟩ : syracuseStep 7450433 = 5587825) B5587825
theorem B4966955 : Blo 2207435 4966955 := bstep (se 1 (by rfl) ⟨3725216, by rfl⟩ : syracuseStep 4966955 = 7450433) B7450433
theorem B3311303 : Blo 2207435 3311303 := bstep (se 1 (by rfl) ⟨2483477, by rfl⟩ : syracuseStep 3311303 = 4966955) B4966955
theorem B2207535 : Blo 2207435 2207535 := bstep (se 1 (by rfl) ⟨1655651, by rfl⟩ : syracuseStep 2207535 = 3311303) B3311303
theorem B3311309 : Blo 2207435 3311309 := bbase (se 3 (by rfl) ⟨620870, by rfl⟩ : syracuseStep 3311309 = 1241741) (by norm_num)
theorem B2207539 : Blo 2207435 2207539 := bstep (se 1 (by rfl) ⟨1655654, by rfl⟩ : syracuseStep 2207539 = 3311309) B3311309
theorem B4966973 : Blo 2207435 4966973 := bbase (se 3 (by rfl) ⟨931307, by rfl⟩ : syracuseStep 4966973 = 1862615) (by norm_num)
theorem B3311315 : Blo 2207435 3311315 := bstep (se 1 (by rfl) ⟨2483486, by rfl⟩ : syracuseStep 3311315 = 4966973) B4966973
theorem B2207543 : Blo 2207435 2207543 := bstep (se 1 (by rfl) ⟨1655657, by rfl⟩ : syracuseStep 2207543 = 3311315) B3311315
theorem B3725237 : Blo 2207435 3725237 := bbase (se 5 (by rfl) ⟨174620, by rfl⟩ : syracuseStep 3725237 = 349241) (by norm_num)
theorem B2483491 : Blo 2207435 2483491 := bstep (se 1 (by rfl) ⟨1862618, by rfl⟩ : syracuseStep 2483491 = 3725237) B3725237
theorem B3311321 : Blo 2207435 3311321 := bstep (se 2 (by rfl) ⟨1241745, by rfl⟩ : syracuseStep 3311321 = 2483491) B2483491
theorem B2207547 : Blo 2207435 2207547 := bstep (se 1 (by rfl) ⟨1655660, by rfl⟩ : syracuseStep 2207547 = 3311321) B3311321
theorem B2357381 : Blo 2207435 2357381 := bbase (se 4 (by rfl) ⟨221004, by rfl⟩ : syracuseStep 2357381 = 442009) (by norm_num)
theorem B6286349 : Blo 2207435 6286349 := bstep (se 3 (by rfl) ⟨1178690, by rfl⟩ : syracuseStep 6286349 = 2357381) B2357381
theorem B16763597 : Blo 2207435 16763597 := bstep (se 3 (by rfl) ⟨3143174, by rfl⟩ : syracuseStep 16763597 = 6286349) B6286349
theorem B11175731 : Blo 2207435 11175731 := bstep (se 1 (by rfl) ⟨8381798, by rfl⟩ : syracuseStep 11175731 = 16763597) B16763597
theorem B7450487 : Blo 2207435 7450487 := bstep (se 1 (by rfl) ⟨5587865, by rfl⟩ : syracuseStep 7450487 = 11175731) B11175731
theorem B4966991 : Blo 2207435 4966991 := bstep (se 1 (by rfl) ⟨3725243, by rfl⟩ : syracuseStep 4966991 = 7450487) B7450487
theorem B3311327 : Blo 2207435 3311327 := bstep (se 1 (by rfl) ⟨2483495, by rfl⟩ : syracuseStep 3311327 = 4966991) B4966991
theorem B2207551 : Blo 2207435 2207551 := bstep (se 1 (by rfl) ⟨1655663, by rfl⟩ : syracuseStep 2207551 = 3311327) B3311327
theorem B3311333 : Blo 2207435 3311333 := bbase (se 4 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 3311333 = 620875) (by norm_num)
theorem B2207555 : Blo 2207435 2207555 := bstep (se 1 (by rfl) ⟨1655666, by rfl⟩ : syracuseStep 2207555 = 3311333) B3311333
theorem B6286373 : Blo 2207435 6286373 := bbase (se 4 (by rfl) ⟨589347, by rfl⟩ : syracuseStep 6286373 = 1178695) (by norm_num)
theorem B4190915 : Blo 2207435 4190915 := bstep (se 1 (by rfl) ⟨3143186, by rfl⟩ : syracuseStep 4190915 = 6286373) B6286373
theorem B2793943 : Blo 2207435 2793943 := bstep (se 1 (by rfl) ⟨2095457, by rfl⟩ : syracuseStep 2793943 = 4190915) B4190915
theorem B3725257 : Blo 2207435 3725257 := bstep (se 2 (by rfl) ⟨1396971, by rfl⟩ : syracuseStep 3725257 = 2793943) B2793943
theorem B4967009 : Blo 2207435 4967009 := bstep (se 2 (by rfl) ⟨1862628, by rfl⟩ : syracuseStep 4967009 = 3725257) B3725257
theorem B3311339 : Blo 2207435 3311339 := bstep (se 1 (by rfl) ⟨2483504, by rfl⟩ : syracuseStep 3311339 = 4967009) B4967009
theorem B2207559 : Blo 2207435 2207559 := bstep (se 1 (by rfl) ⟨1655669, by rfl⟩ : syracuseStep 2207559 = 3311339) B3311339
theorem B2483509 : Blo 2207435 2483509 := bbase (se 5 (by rfl) ⟨116414, by rfl⟩ : syracuseStep 2483509 = 232829) (by norm_num)
theorem B3311345 : Blo 2207435 3311345 := bstep (se 2 (by rfl) ⟨1241754, by rfl⟩ : syracuseStep 3311345 = 2483509) B2483509
theorem B2207563 : Blo 2207435 2207563 := bstep (se 1 (by rfl) ⟨1655672, by rfl⟩ : syracuseStep 2207563 = 3311345) B3311345
theorem B2793953 : Blo 2207435 2793953 := bbase (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) (by norm_num)
theorem B7450541 : Blo 2207435 7450541 := bstep (se 3 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 7450541 = 2793953) B2793953
theorem B4967027 : Blo 2207435 4967027 := bstep (se 1 (by rfl) ⟨3725270, by rfl⟩ : syracuseStep 4967027 = 7450541) B7450541
theorem B3311351 : Blo 2207435 3311351 := bstep (se 1 (by rfl) ⟨2483513, by rfl⟩ : syracuseStep 3311351 = 4967027) B4967027
theorem B2207567 : Blo 2207435 2207567 := bstep (se 1 (by rfl) ⟨1655675, by rfl⟩ : syracuseStep 2207567 = 3311351) B3311351
theorem B3311357 : Blo 2207435 3311357 := bbase (se 3 (by rfl) ⟨620879, by rfl⟩ : syracuseStep 3311357 = 1241759) (by norm_num)
theorem B2207571 : Blo 2207435 2207571 := bstep (se 1 (by rfl) ⟨1655678, by rfl⟩ : syracuseStep 2207571 = 3311357) B3311357
theorem B4967045 : Blo 2207435 4967045 := bbase (se 4 (by rfl) ⟨465660, by rfl⟩ : syracuseStep 4967045 = 931321) (by norm_num)
theorem B3311363 : Blo 2207435 3311363 := bstep (se 1 (by rfl) ⟨2483522, by rfl⟩ : syracuseStep 3311363 = 4967045) B4967045
theorem B2207575 : Blo 2207435 2207575 := bstep (se 1 (by rfl) ⟨1655681, by rfl⟩ : syracuseStep 2207575 = 3311363) B3311363
theorem B2832089 : Blo 2207435 2832089 := bbase (se 2 (by rfl) ⟨1062033, by rfl⟩ : syracuseStep 2832089 = 2124067) (by norm_num)
theorem B30208949 : Blo 2207435 30208949 := bstep (se 5 (by rfl) ⟨1416044, by rfl⟩ : syracuseStep 30208949 = 2832089) B2832089
theorem B20139299 : Blo 2207435 20139299 := bstep (se 1 (by rfl) ⟨15104474, by rfl⟩ : syracuseStep 20139299 = 30208949) B30208949
theorem B13426199 : Blo 2207435 13426199 := bstep (se 1 (by rfl) ⟨10069649, by rfl⟩ : syracuseStep 13426199 = 20139299) B20139299
theorem B8950799 : Blo 2207435 8950799 := bstep (se 1 (by rfl) ⟨6713099, by rfl⟩ : syracuseStep 8950799 = 13426199) B13426199
theorem B5967199 : Blo 2207435 5967199 := bstep (se 1 (by rfl) ⟨4475399, by rfl⟩ : syracuseStep 5967199 = 8950799) B8950799
theorem B7956265 : Blo 2207435 7956265 := bstep (se 2 (by rfl) ⟨2983599, by rfl⟩ : syracuseStep 7956265 = 5967199) B5967199
theorem B10608353 : Blo 2207435 10608353 := bstep (se 2 (by rfl) ⟨3978132, by rfl⟩ : syracuseStep 10608353 = 7956265) B7956265
theorem B7072235 : Blo 2207435 7072235 := bstep (se 1 (by rfl) ⟨5304176, by rfl⟩ : syracuseStep 7072235 = 10608353) B10608353
theorem B4714823 : Blo 2207435 4714823 := bstep (se 1 (by rfl) ⟨3536117, by rfl⟩ : syracuseStep 4714823 = 7072235) B7072235
theorem B3143215 : Blo 2207435 3143215 := bstep (se 1 (by rfl) ⟨2357411, by rfl⟩ : syracuseStep 3143215 = 4714823) B4714823
theorem B4190953 : Blo 2207435 4190953 := bstep (se 2 (by rfl) ⟨1571607, by rfl⟩ : syracuseStep 4190953 = 3143215) B3143215
theorem B5587937 : Blo 2207435 5587937 := bstep (se 2 (by rfl) ⟨2095476, by rfl⟩ : syracuseStep 5587937 = 4190953) B4190953
theorem B3725291 : Blo 2207435 3725291 := bstep (se 1 (by rfl) ⟨2793968, by rfl⟩ : syracuseStep 3725291 = 5587937) B5587937
theorem B2483527 : Blo 2207435 2483527 := bstep (se 1 (by rfl) ⟨1862645, by rfl⟩ : syracuseStep 2483527 = 3725291) B3725291
theorem B3311369 : Blo 2207435 3311369 := bstep (se 2 (by rfl) ⟨1241763, by rfl⟩ : syracuseStep 3311369 = 2483527) B2483527
theorem B2207579 : Blo 2207435 2207579 := bstep (se 1 (by rfl) ⟨1655684, by rfl⟩ : syracuseStep 2207579 = 3311369) B3311369
theorem B11175893 : Blo 2207435 11175893 := bbase (se 7 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 11175893 = 261935) (by norm_num)
theorem B7450595 : Blo 2207435 7450595 := bstep (se 1 (by rfl) ⟨5587946, by rfl⟩ : syracuseStep 7450595 = 11175893) B11175893
theorem B4967063 : Blo 2207435 4967063 := bstep (se 1 (by rfl) ⟨3725297, by rfl⟩ : syracuseStep 4967063 = 7450595) B7450595
theorem B3311375 : Blo 2207435 3311375 := bstep (se 1 (by rfl) ⟨2483531, by rfl⟩ : syracuseStep 3311375 = 4967063) B4967063
theorem B2207583 : Blo 2207435 2207583 := bstep (se 1 (by rfl) ⟨1655687, by rfl⟩ : syracuseStep 2207583 = 3311375) B3311375
theorem B3311381 : Blo 2207435 3311381 := bbase (se 6 (by rfl) ⟨77610, by rfl⟩ : syracuseStep 3311381 = 155221) (by norm_num)
theorem B2207587 : Blo 2207435 2207587 := bstep (se 1 (by rfl) ⟨1655690, by rfl⟩ : syracuseStep 2207587 = 3311381) B3311381
theorem B135940949 : Blo 2207435 135940949 := bbase (se 9 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 135940949 = 796529) (by norm_num)
theorem B90627299 : Blo 2207435 90627299 := bstep (se 1 (by rfl) ⟨67970474, by rfl⟩ : syracuseStep 90627299 = 135940949) B135940949
theorem B60418199 : Blo 2207435 60418199 := bstep (se 1 (by rfl) ⟨45313649, by rfl⟩ : syracuseStep 60418199 = 90627299) B90627299
theorem B40278799 : Blo 2207435 40278799 := bstep (se 1 (by rfl) ⟨30209099, by rfl⟩ : syracuseStep 40278799 = 60418199) B60418199
theorem B214820261 : Blo 2207435 214820261 := bstep (se 4 (by rfl) ⟨20139399, by rfl⟩ : syracuseStep 214820261 = 40278799) B40278799
theorem B143213507 : Blo 2207435 143213507 := bstep (se 1 (by rfl) ⟨107410130, by rfl⟩ : syracuseStep 143213507 = 214820261) B214820261
theorem B95475671 : Blo 2207435 95475671 := bstep (se 1 (by rfl) ⟨71606753, by rfl⟩ : syracuseStep 95475671 = 143213507) B143213507
theorem B63650447 : Blo 2207435 63650447 := bstep (se 1 (by rfl) ⟨47737835, by rfl⟩ : syracuseStep 63650447 = 95475671) B95475671
theorem B42433631 : Blo 2207435 42433631 := bstep (se 1 (by rfl) ⟨31825223, by rfl⟩ : syracuseStep 42433631 = 63650447) B63650447
theorem B28289087 : Blo 2207435 28289087 := bstep (se 1 (by rfl) ⟨21216815, by rfl⟩ : syracuseStep 28289087 = 42433631) B42433631
theorem B18859391 : Blo 2207435 18859391 := bstep (se 1 (by rfl) ⟨14144543, by rfl⟩ : syracuseStep 18859391 = 28289087) B28289087
theorem B12572927 : Blo 2207435 12572927 := bstep (se 1 (by rfl) ⟨9429695, by rfl⟩ : syracuseStep 12572927 = 18859391) B18859391
theorem B8381951 : Blo 2207435 8381951 := bstep (se 1 (by rfl) ⟨6286463, by rfl⟩ : syracuseStep 8381951 = 12572927) B12572927
theorem B5587967 : Blo 2207435 5587967 := bstep (se 1 (by rfl) ⟨4190975, by rfl⟩ : syracuseStep 5587967 = 8381951) B8381951
theorem B3725311 : Blo 2207435 3725311 := bstep (se 1 (by rfl) ⟨2793983, by rfl⟩ : syracuseStep 3725311 = 5587967) B5587967
theorem B4967081 : Blo 2207435 4967081 := bstep (se 2 (by rfl) ⟨1862655, by rfl⟩ : syracuseStep 4967081 = 3725311) B3725311
theorem B3311387 : Blo 2207435 3311387 := bstep (se 1 (by rfl) ⟨2483540, by rfl⟩ : syracuseStep 3311387 = 4967081) B4967081
theorem B2207591 : Blo 2207435 2207591 := bstep (se 1 (by rfl) ⟨1655693, by rfl⟩ : syracuseStep 2207591 = 3311387) B3311387
theorem B2483545 : Blo 2207435 2483545 := bbase (se 2 (by rfl) ⟨931329, by rfl⟩ : syracuseStep 2483545 = 1862659) (by norm_num)
theorem B3311393 : Blo 2207435 3311393 := bstep (se 2 (by rfl) ⟨1241772, by rfl⟩ : syracuseStep 3311393 = 2483545) B2483545
theorem B2207595 : Blo 2207435 2207595 := bstep (se 1 (by rfl) ⟨1655696, by rfl⟩ : syracuseStep 2207595 = 3311393) B3311393
theorem B3536149 : Blo 2207435 3536149 := bbase (se 6 (by rfl) ⟨82878, by rfl⟩ : syracuseStep 3536149 = 165757) (by norm_num)
theorem B4714865 : Blo 2207435 4714865 := bstep (se 2 (by rfl) ⟨1768074, by rfl⟩ : syracuseStep 4714865 = 3536149) B3536149
theorem B3143243 : Blo 2207435 3143243 := bstep (se 1 (by rfl) ⟨2357432, by rfl⟩ : syracuseStep 3143243 = 4714865) B4714865
theorem B8381981 : Blo 2207435 8381981 := bstep (se 3 (by rfl) ⟨1571621, by rfl⟩ : syracuseStep 8381981 = 3143243) B3143243
theorem B5587987 : Blo 2207435 5587987 := bstep (se 1 (by rfl) ⟨4190990, by rfl⟩ : syracuseStep 5587987 = 8381981) B8381981
theorem B7450649 : Blo 2207435 7450649 := bstep (se 2 (by rfl) ⟨2793993, by rfl⟩ : syracuseStep 7450649 = 5587987) B5587987
theorem B4967099 : Blo 2207435 4967099 := bstep (se 1 (by rfl) ⟨3725324, by rfl⟩ : syracuseStep 4967099 = 7450649) B7450649
theorem B3311399 : Blo 2207435 3311399 := bstep (se 1 (by rfl) ⟨2483549, by rfl⟩ : syracuseStep 3311399 = 4967099) B4967099
theorem B2207599 : Blo 2207435 2207599 := bstep (se 1 (by rfl) ⟨1655699, by rfl⟩ : syracuseStep 2207599 = 3311399) B3311399
theorem B3311405 : Blo 2207435 3311405 := bbase (se 3 (by rfl) ⟨620888, by rfl⟩ : syracuseStep 3311405 = 1241777) (by norm_num)
theorem B2207603 : Blo 2207435 2207603 := bstep (se 1 (by rfl) ⟨1655702, by rfl⟩ : syracuseStep 2207603 = 3311405) B3311405
theorem B4967117 : Blo 2207435 4967117 := bbase (se 3 (by rfl) ⟨931334, by rfl⟩ : syracuseStep 4967117 = 1862669) (by norm_num)
theorem B3311411 : Blo 2207435 3311411 := bstep (se 1 (by rfl) ⟨2483558, by rfl⟩ : syracuseStep 3311411 = 4967117) B4967117
theorem B2207607 : Blo 2207435 2207607 := bstep (se 1 (by rfl) ⟨1655705, by rfl⟩ : syracuseStep 2207607 = 3311411) B3311411
theorem B2794009 : Blo 2207435 2794009 := bbase (se 2 (by rfl) ⟨1047753, by rfl⟩ : syracuseStep 2794009 = 2095507) (by norm_num)
theorem B3725345 : Blo 2207435 3725345 := bstep (se 2 (by rfl) ⟨1397004, by rfl⟩ : syracuseStep 3725345 = 2794009) B2794009
theorem B2483563 : Blo 2207435 2483563 := bstep (se 1 (by rfl) ⟨1862672, by rfl⟩ : syracuseStep 2483563 = 3725345) B3725345
theorem B3311417 : Blo 2207435 3311417 := bstep (se 2 (by rfl) ⟨1241781, by rfl⟩ : syracuseStep 3311417 = 2483563) B2483563
theorem B2207611 : Blo 2207435 2207611 := bstep (se 1 (by rfl) ⟨1655708, by rfl⟩ : syracuseStep 2207611 = 3311417) B3311417
theorem B9429797 : Blo 2207435 9429797 := bbase (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) (by norm_num)
theorem B25146125 : Blo 2207435 25146125 := bstep (se 3 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 25146125 = 9429797) B9429797
theorem B16764083 : Blo 2207435 16764083 := bstep (se 1 (by rfl) ⟨12573062, by rfl⟩ : syracuseStep 16764083 = 25146125) B25146125
theorem B11176055 : Blo 2207435 11176055 := bstep (se 1 (by rfl) ⟨8382041, by rfl⟩ : syracuseStep 11176055 = 16764083) B16764083
theorem B7450703 : Blo 2207435 7450703 := bstep (se 1 (by rfl) ⟨5588027, by rfl⟩ : syracuseStep 7450703 = 11176055) B11176055
theorem B4967135 : Blo 2207435 4967135 := bstep (se 1 (by rfl) ⟨3725351, by rfl⟩ : syracuseStep 4967135 = 7450703) B7450703
theorem B3311423 : Blo 2207435 3311423 := bstep (se 1 (by rfl) ⟨2483567, by rfl⟩ : syracuseStep 3311423 = 4967135) B4967135
theorem B2207615 : Blo 2207435 2207615 := bstep (se 1 (by rfl) ⟨1655711, by rfl⟩ : syracuseStep 2207615 = 3311423) B3311423
theorem B3311429 : Blo 2207435 3311429 := bbase (se 4 (by rfl) ⟨310446, by rfl⟩ : syracuseStep 3311429 = 620893) (by norm_num)
theorem B2207619 : Blo 2207435 2207619 := bstep (se 1 (by rfl) ⟨1655714, by rfl⟩ : syracuseStep 2207619 = 3311429) B3311429
theorem B3725365 : Blo 2207435 3725365 := bbase (se 5 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 3725365 = 349253) (by norm_num)
theorem B4967153 : Blo 2207435 4967153 := bstep (se 2 (by rfl) ⟨1862682, by rfl⟩ : syracuseStep 4967153 = 3725365) B3725365
theorem B3311435 : Blo 2207435 3311435 := bstep (se 1 (by rfl) ⟨2483576, by rfl⟩ : syracuseStep 3311435 = 4967153) B4967153
theorem B2207623 : Blo 2207435 2207623 := bstep (se 1 (by rfl) ⟨1655717, by rfl⟩ : syracuseStep 2207623 = 3311435) B3311435
theorem B2483581 : Blo 2207435 2483581 := bbase (se 3 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 2483581 = 931343) (by norm_num)
theorem B3311441 : Blo 2207435 3311441 := bstep (se 2 (by rfl) ⟨1241790, by rfl⟩ : syracuseStep 3311441 = 2483581) B2483581
theorem B2207627 : Blo 2207435 2207627 := bstep (se 1 (by rfl) ⟨1655720, by rfl⟩ : syracuseStep 2207627 = 3311441) B3311441
theorem B7450757 : Blo 2207435 7450757 := bbase (se 4 (by rfl) ⟨698508, by rfl⟩ : syracuseStep 7450757 = 1397017) (by norm_num)
theorem B4967171 : Blo 2207435 4967171 := bstep (se 1 (by rfl) ⟨3725378, by rfl⟩ : syracuseStep 4967171 = 7450757) B7450757
theorem B3311447 : Blo 2207435 3311447 := bstep (se 1 (by rfl) ⟨2483585, by rfl⟩ : syracuseStep 3311447 = 4967171) B4967171
theorem B2207631 : Blo 2207435 2207631 := bstep (se 1 (by rfl) ⟨1655723, by rfl⟩ : syracuseStep 2207631 = 3311447) B3311447
theorem B3311453 : Blo 2207435 3311453 := bbase (se 3 (by rfl) ⟨620897, by rfl⟩ : syracuseStep 3311453 = 1241795) (by norm_num)
theorem B2207635 : Blo 2207435 2207635 := bstep (se 1 (by rfl) ⟨1655726, by rfl⟩ : syracuseStep 2207635 = 3311453) B3311453
theorem B4967189 : Blo 2207435 4967189 := bbase (se 6 (by rfl) ⟨116418, by rfl⟩ : syracuseStep 4967189 = 232837) (by norm_num)
theorem B3311459 : Blo 2207435 3311459 := bstep (se 1 (by rfl) ⟨2483594, by rfl⟩ : syracuseStep 3311459 = 4967189) B4967189
theorem B2207639 : Blo 2207435 2207639 := bstep (se 1 (by rfl) ⟨1655729, by rfl⟩ : syracuseStep 2207639 = 3311459) B3311459
theorem B8382149 : Blo 2207435 8382149 := bbase (se 4 (by rfl) ⟨785826, by rfl⟩ : syracuseStep 8382149 = 1571653) (by norm_num)
theorem B5588099 : Blo 2207435 5588099 := bstep (se 1 (by rfl) ⟨4191074, by rfl⟩ : syracuseStep 5588099 = 8382149) B8382149
theorem B3725399 : Blo 2207435 3725399 := bstep (se 1 (by rfl) ⟨2794049, by rfl⟩ : syracuseStep 3725399 = 5588099) B5588099
theorem B2483599 : Blo 2207435 2483599 := bstep (se 1 (by rfl) ⟨1862699, by rfl⟩ : syracuseStep 2483599 = 3725399) B3725399
theorem B3311465 : Blo 2207435 3311465 := bstep (se 2 (by rfl) ⟨1241799, by rfl⟩ : syracuseStep 3311465 = 2483599) B2483599
theorem B2207643 : Blo 2207435 2207643 := bstep (se 1 (by rfl) ⟨1655732, by rfl⟩ : syracuseStep 2207643 = 3311465) B3311465
theorem B10608677 : Blo 2207435 10608677 := bbase (se 4 (by rfl) ⟨994563, by rfl⟩ : syracuseStep 10608677 = 1989127) (by norm_num)
theorem B7072451 : Blo 2207435 7072451 := bstep (se 1 (by rfl) ⟨5304338, by rfl⟩ : syracuseStep 7072451 = 10608677) B10608677
theorem B4714967 : Blo 2207435 4714967 := bstep (se 1 (by rfl) ⟨3536225, by rfl⟩ : syracuseStep 4714967 = 7072451) B7072451
theorem B12573245 : Blo 2207435 12573245 := bstep (se 3 (by rfl) ⟨2357483, by rfl⟩ : syracuseStep 12573245 = 4714967) B4714967
theorem B8382163 : Blo 2207435 8382163 := bstep (se 1 (by rfl) ⟨6286622, by rfl⟩ : syracuseStep 8382163 = 12573245) B12573245
theorem B11176217 : Blo 2207435 11176217 := bstep (se 2 (by rfl) ⟨4191081, by rfl⟩ : syracuseStep 11176217 = 8382163) B8382163
theorem B7450811 : Blo 2207435 7450811 := bstep (se 1 (by rfl) ⟨5588108, by rfl⟩ : syracuseStep 7450811 = 11176217) B11176217
theorem B4967207 : Blo 2207435 4967207 := bstep (se 1 (by rfl) ⟨3725405, by rfl⟩ : syracuseStep 4967207 = 7450811) B7450811
theorem B3311471 : Blo 2207435 3311471 := bstep (se 1 (by rfl) ⟨2483603, by rfl⟩ : syracuseStep 3311471 = 4967207) B4967207
theorem B2207647 : Blo 2207435 2207647 := bstep (se 1 (by rfl) ⟨1655735, by rfl⟩ : syracuseStep 2207647 = 3311471) B3311471
theorem B3311477 : Blo 2207435 3311477 := bbase (se 5 (by rfl) ⟨155225, by rfl⟩ : syracuseStep 3311477 = 310451) (by norm_num)
theorem B2207651 : Blo 2207435 2207651 := bstep (se 1 (by rfl) ⟨1655738, by rfl⟩ : syracuseStep 2207651 = 3311477) B3311477
theorem B4779317 : Blo 2207435 4779317 := bbase (se 5 (by rfl) ⟨224030, by rfl⟩ : syracuseStep 4779317 = 448061) (by norm_num)
theorem B3186211 : Blo 2207435 3186211 := bstep (se 1 (by rfl) ⟨2389658, by rfl⟩ : syracuseStep 3186211 = 4779317) B4779317
theorem B4248281 : Blo 2207435 4248281 := bstep (se 2 (by rfl) ⟨1593105, by rfl⟩ : syracuseStep 4248281 = 3186211) B3186211
theorem B2832187 : Blo 2207435 2832187 := bstep (se 1 (by rfl) ⟨2124140, by rfl⟩ : syracuseStep 2832187 = 4248281) B4248281
theorem B3776249 : Blo 2207435 3776249 := bstep (se 2 (by rfl) ⟨1416093, by rfl⟩ : syracuseStep 3776249 = 2832187) B2832187
theorem B2517499 : Blo 2207435 2517499 := bstep (se 1 (by rfl) ⟨1888124, by rfl⟩ : syracuseStep 2517499 = 3776249) B3776249
theorem B13426661 : Blo 2207435 13426661 := bstep (se 4 (by rfl) ⟨1258749, by rfl⟩ : syracuseStep 13426661 = 2517499) B2517499
theorem B8951107 : Blo 2207435 8951107 := bstep (se 1 (by rfl) ⟨6713330, by rfl⟩ : syracuseStep 8951107 = 13426661) B13426661
theorem B11934809 : Blo 2207435 11934809 := bstep (se 2 (by rfl) ⟨4475553, by rfl⟩ : syracuseStep 11934809 = 8951107) B8951107
theorem B7956539 : Blo 2207435 7956539 := bstep (se 1 (by rfl) ⟨5967404, by rfl⟩ : syracuseStep 7956539 = 11934809) B11934809
theorem B5304359 : Blo 2207435 5304359 := bstep (se 1 (by rfl) ⟨3978269, by rfl⟩ : syracuseStep 5304359 = 7956539) B7956539
theorem B3536239 : Blo 2207435 3536239 := bstep (se 1 (by rfl) ⟨2652179, by rfl⟩ : syracuseStep 3536239 = 5304359) B5304359
theorem B4714985 : Blo 2207435 4714985 := bstep (se 2 (by rfl) ⟨1768119, by rfl⟩ : syracuseStep 4714985 = 3536239) B3536239
theorem B3143323 : Blo 2207435 3143323 := bstep (se 1 (by rfl) ⟨2357492, by rfl⟩ : syracuseStep 3143323 = 4714985) B4714985
theorem B4191097 : Blo 2207435 4191097 := bstep (se 2 (by rfl) ⟨1571661, by rfl⟩ : syracuseStep 4191097 = 3143323) B3143323
theorem B5588129 : Blo 2207435 5588129 := bstep (se 2 (by rfl) ⟨2095548, by rfl⟩ : syracuseStep 5588129 = 4191097) B4191097
theorem B3725419 : Blo 2207435 3725419 := bstep (se 1 (by rfl) ⟨2794064, by rfl⟩ : syracuseStep 3725419 = 5588129) B5588129
theorem B4967225 : Blo 2207435 4967225 := bstep (se 2 (by rfl) ⟨1862709, by rfl⟩ : syracuseStep 4967225 = 3725419) B3725419
theorem B3311483 : Blo 2207435 3311483 := bstep (se 1 (by rfl) ⟨2483612, by rfl⟩ : syracuseStep 3311483 = 4967225) B4967225
theorem B2207655 : Blo 2207435 2207655 := bstep (se 1 (by rfl) ⟨1655741, by rfl⟩ : syracuseStep 2207655 = 3311483) B3311483
theorem B2483617 : Blo 2207435 2483617 := bbase (se 2 (by rfl) ⟨931356, by rfl⟩ : syracuseStep 2483617 = 1862713) (by norm_num)
theorem B3311489 : Blo 2207435 3311489 := bstep (se 2 (by rfl) ⟨1241808, by rfl⟩ : syracuseStep 3311489 = 2483617) B2483617
theorem B2207659 : Blo 2207435 2207659 := bstep (se 1 (by rfl) ⟨1655744, by rfl⟩ : syracuseStep 2207659 = 3311489) B3311489
theorem B5588149 : Blo 2207435 5588149 := bbase (se 5 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 5588149 = 523889) (by norm_num)
theorem B7450865 : Blo 2207435 7450865 := bstep (se 2 (by rfl) ⟨2794074, by rfl⟩ : syracuseStep 7450865 = 5588149) B5588149
theorem B4967243 : Blo 2207435 4967243 := bstep (se 1 (by rfl) ⟨3725432, by rfl⟩ : syracuseStep 4967243 = 7450865) B7450865
theorem B3311495 : Blo 2207435 3311495 := bstep (se 1 (by rfl) ⟨2483621, by rfl⟩ : syracuseStep 3311495 = 4967243) B4967243
theorem B2207663 : Blo 2207435 2207663 := bstep (se 1 (by rfl) ⟨1655747, by rfl⟩ : syracuseStep 2207663 = 3311495) B3311495
theorem B3311501 : Blo 2207435 3311501 := bbase (se 3 (by rfl) ⟨620906, by rfl⟩ : syracuseStep 3311501 = 1241813) (by norm_num)
theorem B2207667 : Blo 2207435 2207667 := bstep (se 1 (by rfl) ⟨1655750, by rfl⟩ : syracuseStep 2207667 = 3311501) B3311501
theorem B4967261 : Blo 2207435 4967261 := bbase (se 3 (by rfl) ⟨931361, by rfl⟩ : syracuseStep 4967261 = 1862723) (by norm_num)
theorem B3311507 : Blo 2207435 3311507 := bstep (se 1 (by rfl) ⟨2483630, by rfl⟩ : syracuseStep 3311507 = 4967261) B4967261
theorem B2207671 : Blo 2207435 2207671 := bstep (se 1 (by rfl) ⟨1655753, by rfl⟩ : syracuseStep 2207671 = 3311507) B3311507
theorem B3725453 : Blo 2207435 3725453 := bbase (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) (by norm_num)
theorem B2483635 : Blo 2207435 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B3311513 : Blo 2207435 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B2207675 : Blo 2207435 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B4248325 : Blo 2207435 4248325 := bbase (se 4 (by rfl) ⟨398280, by rfl⟩ : syracuseStep 4248325 = 796561) (by norm_num)
theorem B5664433 : Blo 2207435 5664433 := bstep (se 2 (by rfl) ⟨2124162, by rfl⟩ : syracuseStep 5664433 = 4248325) B4248325
theorem B7552577 : Blo 2207435 7552577 := bstep (se 2 (by rfl) ⟨2832216, by rfl⟩ : syracuseStep 7552577 = 5664433) B5664433
theorem B5035051 : Blo 2207435 5035051 := bstep (se 1 (by rfl) ⟨3776288, by rfl⟩ : syracuseStep 5035051 = 7552577) B7552577
theorem B26853605 : Blo 2207435 26853605 := bstep (se 4 (by rfl) ⟨2517525, by rfl⟩ : syracuseStep 26853605 = 5035051) B5035051
theorem B17902403 : Blo 2207435 17902403 := bstep (se 1 (by rfl) ⟨13426802, by rfl⟩ : syracuseStep 17902403 = 26853605) B26853605
theorem B11934935 : Blo 2207435 11934935 := bstep (se 1 (by rfl) ⟨8951201, by rfl⟩ : syracuseStep 11934935 = 17902403) B17902403
theorem B7956623 : Blo 2207435 7956623 := bstep (se 1 (by rfl) ⟨5967467, by rfl⟩ : syracuseStep 7956623 = 11934935) B11934935
theorem B5304415 : Blo 2207435 5304415 := bstep (se 1 (by rfl) ⟨3978311, by rfl⟩ : syracuseStep 5304415 = 7956623) B7956623
theorem B7072553 : Blo 2207435 7072553 := bstep (se 2 (by rfl) ⟨2652207, by rfl⟩ : syracuseStep 7072553 = 5304415) B5304415
theorem B18860141 : Blo 2207435 18860141 := bstep (se 3 (by rfl) ⟨3536276, by rfl⟩ : syracuseStep 18860141 = 7072553) B7072553
theorem B12573427 : Blo 2207435 12573427 := bstep (se 1 (by rfl) ⟨9430070, by rfl⟩ : syracuseStep 12573427 = 18860141) B18860141
theorem B16764569 : Blo 2207435 16764569 := bstep (se 2 (by rfl) ⟨6286713, by rfl⟩ : syracuseStep 16764569 = 12573427) B12573427
theorem B11176379 : Blo 2207435 11176379 := bstep (se 1 (by rfl) ⟨8382284, by rfl⟩ : syracuseStep 11176379 = 16764569) B16764569
theorem B7450919 : Blo 2207435 7450919 := bstep (se 1 (by rfl) ⟨5588189, by rfl⟩ : syracuseStep 7450919 = 11176379) B11176379
theorem B4967279 : Blo 2207435 4967279 := bstep (se 1 (by rfl) ⟨3725459, by rfl⟩ : syracuseStep 4967279 = 7450919) B7450919
theorem B3311519 : Blo 2207435 3311519 := bstep (se 1 (by rfl) ⟨2483639, by rfl⟩ : syracuseStep 3311519 = 4967279) B4967279
theorem B2207679 : Blo 2207435 2207679 := bstep (se 1 (by rfl) ⟨1655759, by rfl⟩ : syracuseStep 2207679 = 3311519) B3311519
theorem B3311525 : Blo 2207435 3311525 := bbase (se 4 (by rfl) ⟨310455, by rfl⟩ : syracuseStep 3311525 = 620911) (by norm_num)
theorem B2207683 : Blo 2207435 2207683 := bstep (se 1 (by rfl) ⟨1655762, by rfl⟩ : syracuseStep 2207683 = 3311525) B3311525
theorem B2794105 : Blo 2207435 2794105 := bbase (se 2 (by rfl) ⟨1047789, by rfl⟩ : syracuseStep 2794105 = 2095579) (by norm_num)
theorem B3725473 : Blo 2207435 3725473 := bstep (se 2 (by rfl) ⟨1397052, by rfl⟩ : syracuseStep 3725473 = 2794105) B2794105
theorem B4967297 : Blo 2207435 4967297 := bstep (se 2 (by rfl) ⟨1862736, by rfl⟩ : syracuseStep 4967297 = 3725473) B3725473
theorem B3311531 : Blo 2207435 3311531 := bstep (se 1 (by rfl) ⟨2483648, by rfl⟩ : syracuseStep 3311531 = 4967297) B4967297
theorem B2207687 : Blo 2207435 2207687 := bstep (se 1 (by rfl) ⟨1655765, by rfl⟩ : syracuseStep 2207687 = 3311531) B3311531
theorem B2483653 : Blo 2207435 2483653 := bbase (se 4 (by rfl) ⟨232842, by rfl⟩ : syracuseStep 2483653 = 465685) (by norm_num)
theorem B3311537 : Blo 2207435 3311537 := bstep (se 2 (by rfl) ⟨1241826, by rfl⟩ : syracuseStep 3311537 = 2483653) B2483653
theorem B2207691 : Blo 2207435 2207691 := bstep (se 1 (by rfl) ⟨1655768, by rfl⟩ : syracuseStep 2207691 = 3311537) B3311537
theorem B4191173 : Blo 2207435 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B2794115 : Blo 2207435 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B7450973 : Blo 2207435 7450973 := bstep (se 3 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 7450973 = 2794115) B2794115
theorem B4967315 : Blo 2207435 4967315 := bstep (se 1 (by rfl) ⟨3725486, by rfl⟩ : syracuseStep 4967315 = 7450973) B7450973
theorem B3311543 : Blo 2207435 3311543 := bstep (se 1 (by rfl) ⟨2483657, by rfl⟩ : syracuseStep 3311543 = 4967315) B4967315
theorem B2207695 : Blo 2207435 2207695 := bstep (se 1 (by rfl) ⟨1655771, by rfl⟩ : syracuseStep 2207695 = 3311543) B3311543
theorem B3311549 : Blo 2207435 3311549 := bbase (se 3 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 3311549 = 1241831) (by norm_num)
theorem B2207699 : Blo 2207435 2207699 := bstep (se 1 (by rfl) ⟨1655774, by rfl⟩ : syracuseStep 2207699 = 3311549) B3311549
theorem B4967333 : Blo 2207435 4967333 := bbase (se 4 (by rfl) ⟨465687, by rfl⟩ : syracuseStep 4967333 = 931375) (by norm_num)
theorem B3311555 : Blo 2207435 3311555 := bstep (se 1 (by rfl) ⟨2483666, by rfl⟩ : syracuseStep 3311555 = 4967333) B4967333
theorem B2207703 : Blo 2207435 2207703 := bstep (se 1 (by rfl) ⟨1655777, by rfl⟩ : syracuseStep 2207703 = 3311555) B3311555
theorem B5588261 : Blo 2207435 5588261 := bbase (se 4 (by rfl) ⟨523899, by rfl⟩ : syracuseStep 5588261 = 1047799) (by norm_num)
theorem B3725507 : Blo 2207435 3725507 := bstep (se 1 (by rfl) ⟨2794130, by rfl⟩ : syracuseStep 3725507 = 5588261) B5588261
theorem B2483671 : Blo 2207435 2483671 := bstep (se 1 (by rfl) ⟨1862753, by rfl⟩ : syracuseStep 2483671 = 3725507) B3725507
theorem B3311561 : Blo 2207435 3311561 := bstep (se 2 (by rfl) ⟨1241835, by rfl⟩ : syracuseStep 3311561 = 2483671) B2483671
theorem B2207707 : Blo 2207435 2207707 := bstep (se 1 (by rfl) ⟨1655780, by rfl⟩ : syracuseStep 2207707 = 3311561) B3311561
theorem B6286805 : Blo 2207435 6286805 := bbase (se 7 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 6286805 = 147347) (by norm_num)
theorem B4191203 : Blo 2207435 4191203 := bstep (se 1 (by rfl) ⟨3143402, by rfl⟩ : syracuseStep 4191203 = 6286805) B6286805
theorem B11176541 : Blo 2207435 11176541 := bstep (se 3 (by rfl) ⟨2095601, by rfl⟩ : syracuseStep 11176541 = 4191203) B4191203
theorem B7451027 : Blo 2207435 7451027 := bstep (se 1 (by rfl) ⟨5588270, by rfl⟩ : syracuseStep 7451027 = 11176541) B11176541
theorem B4967351 : Blo 2207435 4967351 := bstep (se 1 (by rfl) ⟨3725513, by rfl⟩ : syracuseStep 4967351 = 7451027) B7451027
theorem B3311567 : Blo 2207435 3311567 := bstep (se 1 (by rfl) ⟨2483675, by rfl⟩ : syracuseStep 3311567 = 4967351) B4967351
theorem B2207711 : Blo 2207435 2207711 := bstep (se 1 (by rfl) ⟨1655783, by rfl⟩ : syracuseStep 2207711 = 3311567) B3311567
theorem B3311573 : Blo 2207435 3311573 := bbase (se 7 (by rfl) ⟨38807, by rfl⟩ : syracuseStep 3311573 = 77615) (by norm_num)
theorem B2207715 : Blo 2207435 2207715 := bstep (se 1 (by rfl) ⟨1655786, by rfl⟩ : syracuseStep 2207715 = 3311573) B3311573
theorem B8382437 : Blo 2207435 8382437 := bbase (se 4 (by rfl) ⟨785853, by rfl⟩ : syracuseStep 8382437 = 1571707) (by norm_num)
theorem B5588291 : Blo 2207435 5588291 := bstep (se 1 (by rfl) ⟨4191218, by rfl⟩ : syracuseStep 5588291 = 8382437) B8382437
theorem B3725527 : Blo 2207435 3725527 := bstep (se 1 (by rfl) ⟨2794145, by rfl⟩ : syracuseStep 3725527 = 5588291) B5588291
theorem B4967369 : Blo 2207435 4967369 := bstep (se 2 (by rfl) ⟨1862763, by rfl⟩ : syracuseStep 4967369 = 3725527) B3725527
theorem B3311579 : Blo 2207435 3311579 := bstep (se 1 (by rfl) ⟨2483684, by rfl⟩ : syracuseStep 3311579 = 4967369) B4967369
theorem B2207719 : Blo 2207435 2207719 := bstep (se 1 (by rfl) ⟨1655789, by rfl⟩ : syracuseStep 2207719 = 3311579) B3311579
theorem B2483689 : Blo 2207435 2483689 := bbase (se 2 (by rfl) ⟨931383, by rfl⟩ : syracuseStep 2483689 = 1862767) (by norm_num)
theorem B3311585 : Blo 2207435 3311585 := bstep (se 2 (by rfl) ⟨1241844, by rfl⟩ : syracuseStep 3311585 = 2483689) B2483689
theorem B2207723 : Blo 2207435 2207723 := bstep (se 1 (by rfl) ⟨1655792, by rfl⟩ : syracuseStep 2207723 = 3311585) B3311585
theorem B2357569 : Blo 2207435 2357569 := bbase (se 2 (by rfl) ⟨884088, by rfl⟩ : syracuseStep 2357569 = 1768177) (by norm_num)
theorem B12573701 : Blo 2207435 12573701 := bstep (se 4 (by rfl) ⟨1178784, by rfl⟩ : syracuseStep 12573701 = 2357569) B2357569
theorem B8382467 : Blo 2207435 8382467 := bstep (se 1 (by rfl) ⟨6286850, by rfl⟩ : syracuseStep 8382467 = 12573701) B12573701
theorem B5588311 : Blo 2207435 5588311 := bstep (se 1 (by rfl) ⟨4191233, by rfl⟩ : syracuseStep 5588311 = 8382467) B8382467
theorem B7451081 : Blo 2207435 7451081 := bstep (se 2 (by rfl) ⟨2794155, by rfl⟩ : syracuseStep 7451081 = 5588311) B5588311
theorem B4967387 : Blo 2207435 4967387 := bstep (se 1 (by rfl) ⟨3725540, by rfl⟩ : syracuseStep 4967387 = 7451081) B7451081
theorem B3311591 : Blo 2207435 3311591 := bstep (se 1 (by rfl) ⟨2483693, by rfl⟩ : syracuseStep 3311591 = 4967387) B4967387
theorem B2207727 : Blo 2207435 2207727 := bstep (se 1 (by rfl) ⟨1655795, by rfl⟩ : syracuseStep 2207727 = 3311591) B3311591
theorem B3311597 : Blo 2207435 3311597 := bbase (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) (by norm_num)
theorem B2207731 : Blo 2207435 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B4967405 : Blo 2207435 4967405 := bbase (se 3 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 4967405 = 1862777) (by norm_num)
theorem B3311603 : Blo 2207435 3311603 := bstep (se 1 (by rfl) ⟨2483702, by rfl⟩ : syracuseStep 3311603 = 4967405) B4967405
theorem B2207735 : Blo 2207435 2207735 := bstep (se 1 (by rfl) ⟨1655801, by rfl⟩ : syracuseStep 2207735 = 3311603) B3311603
theorem B4715165 : Blo 2207435 4715165 := bbase (se 3 (by rfl) ⟨884093, by rfl⟩ : syracuseStep 4715165 = 1768187) (by norm_num)
theorem B3143443 : Blo 2207435 3143443 := bstep (se 1 (by rfl) ⟨2357582, by rfl⟩ : syracuseStep 3143443 = 4715165) B4715165
theorem B4191257 : Blo 2207435 4191257 := bstep (se 2 (by rfl) ⟨1571721, by rfl⟩ : syracuseStep 4191257 = 3143443) B3143443
theorem B2794171 : Blo 2207435 2794171 := bstep (se 1 (by rfl) ⟨2095628, by rfl⟩ : syracuseStep 2794171 = 4191257) B4191257
theorem B3725561 : Blo 2207435 3725561 := bstep (se 2 (by rfl) ⟨1397085, by rfl⟩ : syracuseStep 3725561 = 2794171) B2794171
theorem B2483707 : Blo 2207435 2483707 := bstep (se 1 (by rfl) ⟨1862780, by rfl⟩ : syracuseStep 2483707 = 3725561) B3725561
theorem B3311609 : Blo 2207435 3311609 := bstep (se 2 (by rfl) ⟨1241853, by rfl⟩ : syracuseStep 3311609 = 2483707) B2483707
theorem B2207739 : Blo 2207435 2207739 := bstep (se 1 (by rfl) ⟨1655804, by rfl⟩ : syracuseStep 2207739 = 3311609) B3311609
theorem B13427189 : Blo 2207435 13427189 := bbase (se 5 (by rfl) ⟨629399, by rfl⟩ : syracuseStep 13427189 = 1258799) (by norm_num)
theorem B143223349 : Blo 2207435 143223349 := bstep (se 5 (by rfl) ⟨6713594, by rfl⟩ : syracuseStep 143223349 = 13427189) B13427189
theorem B190964465 : Blo 2207435 190964465 := bstep (se 2 (by rfl) ⟨71611674, by rfl⟩ : syracuseStep 190964465 = 143223349) B143223349
theorem B127309643 : Blo 2207435 127309643 := bstep (se 1 (by rfl) ⟨95482232, by rfl⟩ : syracuseStep 127309643 = 190964465) B190964465
theorem B84873095 : Blo 2207435 84873095 := bstep (se 1 (by rfl) ⟨63654821, by rfl⟩ : syracuseStep 84873095 = 127309643) B127309643
theorem B56582063 : Blo 2207435 56582063 := bstep (se 1 (by rfl) ⟨42436547, by rfl⟩ : syracuseStep 56582063 = 84873095) B84873095
theorem B37721375 : Blo 2207435 37721375 := bstep (se 1 (by rfl) ⟨28291031, by rfl⟩ : syracuseStep 37721375 = 56582063) B56582063
theorem B25147583 : Blo 2207435 25147583 := bstep (se 1 (by rfl) ⟨18860687, by rfl⟩ : syracuseStep 25147583 = 37721375) B37721375
theorem B16765055 : Blo 2207435 16765055 := bstep (se 1 (by rfl) ⟨12573791, by rfl⟩ : syracuseStep 16765055 = 25147583) B25147583
theorem B11176703 : Blo 2207435 11176703 := bstep (se 1 (by rfl) ⟨8382527, by rfl⟩ : syracuseStep 11176703 = 16765055) B16765055
theorem B7451135 : Blo 2207435 7451135 := bstep (se 1 (by rfl) ⟨5588351, by rfl⟩ : syracuseStep 7451135 = 11176703) B11176703
theorem B4967423 : Blo 2207435 4967423 := bstep (se 1 (by rfl) ⟨3725567, by rfl⟩ : syracuseStep 4967423 = 7451135) B7451135
theorem B3311615 : Blo 2207435 3311615 := bstep (se 1 (by rfl) ⟨2483711, by rfl⟩ : syracuseStep 3311615 = 4967423) B4967423
theorem B2207743 : Blo 2207435 2207743 := bstep (se 1 (by rfl) ⟨1655807, by rfl⟩ : syracuseStep 2207743 = 3311615) B3311615
theorem B3311621 : Blo 2207435 3311621 := bbase (se 4 (by rfl) ⟨310464, by rfl⟩ : syracuseStep 3311621 = 620929) (by norm_num)
theorem B2207747 : Blo 2207435 2207747 := bstep (se 1 (by rfl) ⟨1655810, by rfl⟩ : syracuseStep 2207747 = 3311621) B3311621
theorem B3725581 : Blo 2207435 3725581 := bbase (se 3 (by rfl) ⟨698546, by rfl⟩ : syracuseStep 3725581 = 1397093) (by norm_num)
theorem B4967441 : Blo 2207435 4967441 := bstep (se 2 (by rfl) ⟨1862790, by rfl⟩ : syracuseStep 4967441 = 3725581) B3725581
theorem B3311627 : Blo 2207435 3311627 := bstep (se 1 (by rfl) ⟨2483720, by rfl⟩ : syracuseStep 3311627 = 4967441) B4967441
theorem B2207751 : Blo 2207435 2207751 := bstep (se 1 (by rfl) ⟨1655813, by rfl⟩ : syracuseStep 2207751 = 3311627) B3311627
theorem B2483725 : Blo 2207435 2483725 := bbase (se 3 (by rfl) ⟨465698, by rfl⟩ : syracuseStep 2483725 = 931397) (by norm_num)
theorem B3311633 : Blo 2207435 3311633 := bstep (se 2 (by rfl) ⟨1241862, by rfl⟩ : syracuseStep 3311633 = 2483725) B2483725
theorem B2207755 : Blo 2207435 2207755 := bstep (se 1 (by rfl) ⟨1655816, by rfl⟩ : syracuseStep 2207755 = 3311633) B3311633
theorem B7451189 : Blo 2207435 7451189 := bbase (se 5 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 7451189 = 698549) (by norm_num)
theorem B4967459 : Blo 2207435 4967459 := bstep (se 1 (by rfl) ⟨3725594, by rfl⟩ : syracuseStep 4967459 = 7451189) B7451189
theorem B3311639 : Blo 2207435 3311639 := bstep (se 1 (by rfl) ⟨2483729, by rfl⟩ : syracuseStep 3311639 = 4967459) B4967459
theorem B2207759 : Blo 2207435 2207759 := bstep (se 1 (by rfl) ⟨1655819, by rfl⟩ : syracuseStep 2207759 = 3311639) B3311639
theorem B3311645 : Blo 2207435 3311645 := bbase (se 3 (by rfl) ⟨620933, by rfl⟩ : syracuseStep 3311645 = 1241867) (by norm_num)
theorem B2207763 : Blo 2207435 2207763 := bstep (se 1 (by rfl) ⟨1655822, by rfl⟩ : syracuseStep 2207763 = 3311645) B3311645
theorem B4967477 : Blo 2207435 4967477 := bbase (se 5 (by rfl) ⟨232850, by rfl⟩ : syracuseStep 4967477 = 465701) (by norm_num)
theorem B3311651 : Blo 2207435 3311651 := bstep (se 1 (by rfl) ⟨2483738, by rfl⟩ : syracuseStep 3311651 = 4967477) B4967477
theorem B2207767 : Blo 2207435 2207767 := bstep (se 1 (by rfl) ⟨1655825, by rfl⟩ : syracuseStep 2207767 = 3311651) B3311651
theorem B5304637 : Blo 2207435 5304637 := bbase (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) (by norm_num)
theorem B7072849 : Blo 2207435 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B9430465 : Blo 2207435 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B12573953 : Blo 2207435 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B8382635 : Blo 2207435 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B5588423 : Blo 2207435 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B3725615 : Blo 2207435 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B2483743 : Blo 2207435 2483743 := bstep (se 1 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 2483743 = 3725615) B3725615
theorem B3311657 : Blo 2207435 3311657 := bstep (se 2 (by rfl) ⟨1241871, by rfl⟩ : syracuseStep 3311657 = 2483743) B2483743
theorem B2207771 : Blo 2207435 2207771 := bstep (se 1 (by rfl) ⟨1655828, by rfl⟩ : syracuseStep 2207771 = 3311657) B3311657
theorem B3978485 : Blo 2207435 3978485 := bbase (se 5 (by rfl) ⟨186491, by rfl⟩ : syracuseStep 3978485 = 372983) (by norm_num)
theorem B2652323 : Blo 2207435 2652323 := bstep (se 1 (by rfl) ⟨1989242, by rfl⟩ : syracuseStep 2652323 = 3978485) B3978485
theorem B7072861 : Blo 2207435 7072861 := bstep (se 3 (by rfl) ⟨1326161, by rfl⟩ : syracuseStep 7072861 = 2652323) B2652323
theorem B9430481 : Blo 2207435 9430481 := bstep (se 2 (by rfl) ⟨3536430, by rfl⟩ : syracuseStep 9430481 = 7072861) B7072861
theorem B6286987 : Blo 2207435 6286987 := bstep (se 1 (by rfl) ⟨4715240, by rfl⟩ : syracuseStep 6286987 = 9430481) B9430481
theorem B8382649 : Blo 2207435 8382649 := bstep (se 2 (by rfl) ⟨3143493, by rfl⟩ : syracuseStep 8382649 = 6286987) B6286987
theorem B11176865 : Blo 2207435 11176865 := bstep (se 2 (by rfl) ⟨4191324, by rfl⟩ : syracuseStep 11176865 = 8382649) B8382649
theorem B7451243 : Blo 2207435 7451243 := bstep (se 1 (by rfl) ⟨5588432, by rfl⟩ : syracuseStep 7451243 = 11176865) B11176865
theorem B4967495 : Blo 2207435 4967495 := bstep (se 1 (by rfl) ⟨3725621, by rfl⟩ : syracuseStep 4967495 = 7451243) B7451243
theorem B3311663 : Blo 2207435 3311663 := bstep (se 1 (by rfl) ⟨2483747, by rfl⟩ : syracuseStep 3311663 = 4967495) B4967495
theorem B2207775 : Blo 2207435 2207775 := bstep (se 1 (by rfl) ⟨1655831, by rfl⟩ : syracuseStep 2207775 = 3311663) B3311663
theorem B3311669 : Blo 2207435 3311669 := bbase (se 5 (by rfl) ⟨155234, by rfl⟩ : syracuseStep 3311669 = 310469) (by norm_num)
theorem B2207779 : Blo 2207435 2207779 := bstep (se 1 (by rfl) ⟨1655834, by rfl⟩ : syracuseStep 2207779 = 3311669) B3311669
theorem B5588453 : Blo 2207435 5588453 := bbase (se 4 (by rfl) ⟨523917, by rfl⟩ : syracuseStep 5588453 = 1047835) (by norm_num)
theorem B3725635 : Blo 2207435 3725635 := bstep (se 1 (by rfl) ⟨2794226, by rfl⟩ : syracuseStep 3725635 = 5588453) B5588453
theorem B4967513 : Blo 2207435 4967513 := bstep (se 2 (by rfl) ⟨1862817, by rfl⟩ : syracuseStep 4967513 = 3725635) B3725635
theorem B3311675 : Blo 2207435 3311675 := bstep (se 1 (by rfl) ⟨2483756, by rfl⟩ : syracuseStep 3311675 = 4967513) B4967513
theorem B2207783 : Blo 2207435 2207783 := bstep (se 1 (by rfl) ⟨1655837, by rfl⟩ : syracuseStep 2207783 = 3311675) B3311675
theorem B2483761 : Blo 2207435 2483761 := bbase (se 2 (by rfl) ⟨931410, by rfl⟩ : syracuseStep 2483761 = 1862821) (by norm_num)
theorem B3311681 : Blo 2207435 3311681 := bstep (se 2 (by rfl) ⟨1241880, by rfl⟩ : syracuseStep 3311681 = 2483761) B2483761
theorem B2207787 : Blo 2207435 2207787 := bstep (se 1 (by rfl) ⟨1655840, by rfl⟩ : syracuseStep 2207787 = 3311681) B3311681
theorem B5304685 : Blo 2207435 5304685 := bbase (se 3 (by rfl) ⟨994628, by rfl⟩ : syracuseStep 5304685 = 1989257) (by norm_num)
theorem B7072913 : Blo 2207435 7072913 := bstep (se 2 (by rfl) ⟨2652342, by rfl⟩ : syracuseStep 7072913 = 5304685) B5304685
theorem B4715275 : Blo 2207435 4715275 := bstep (se 1 (by rfl) ⟨3536456, by rfl⟩ : syracuseStep 4715275 = 7072913) B7072913
theorem B6287033 : Blo 2207435 6287033 := bstep (se 2 (by rfl) ⟨2357637, by rfl⟩ : syracuseStep 6287033 = 4715275) B4715275
theorem B4191355 : Blo 2207435 4191355 := bstep (se 1 (by rfl) ⟨3143516, by rfl⟩ : syracuseStep 4191355 = 6287033) B6287033
theorem B5588473 : Blo 2207435 5588473 := bstep (se 2 (by rfl) ⟨2095677, by rfl⟩ : syracuseStep 5588473 = 4191355) B4191355
theorem B7451297 : Blo 2207435 7451297 := bstep (se 2 (by rfl) ⟨2794236, by rfl⟩ : syracuseStep 7451297 = 5588473) B5588473
theorem B4967531 : Blo 2207435 4967531 := bstep (se 1 (by rfl) ⟨3725648, by rfl⟩ : syracuseStep 4967531 = 7451297) B7451297
theorem B3311687 : Blo 2207435 3311687 := bstep (se 1 (by rfl) ⟨2483765, by rfl⟩ : syracuseStep 3311687 = 4967531) B4967531
theorem B2207791 : Blo 2207435 2207791 := bstep (se 1 (by rfl) ⟨1655843, by rfl⟩ : syracuseStep 2207791 = 3311687) B3311687
theorem B3311693 : Blo 2207435 3311693 := bbase (se 3 (by rfl) ⟨620942, by rfl⟩ : syracuseStep 3311693 = 1241885) (by norm_num)
theorem B2207795 : Blo 2207435 2207795 := bstep (se 1 (by rfl) ⟨1655846, by rfl⟩ : syracuseStep 2207795 = 3311693) B3311693
theorem B4967549 : Blo 2207435 4967549 := bbase (se 3 (by rfl) ⟨931415, by rfl⟩ : syracuseStep 4967549 = 1862831) (by norm_num)
theorem B3311699 : Blo 2207435 3311699 := bstep (se 1 (by rfl) ⟨2483774, by rfl⟩ : syracuseStep 3311699 = 4967549) B4967549
theorem B2207799 : Blo 2207435 2207799 := bstep (se 1 (by rfl) ⟨1655849, by rfl⟩ : syracuseStep 2207799 = 3311699) B3311699
theorem B3725669 : Blo 2207435 3725669 := bbase (se 4 (by rfl) ⟨349281, by rfl⟩ : syracuseStep 3725669 = 698563) (by norm_num)
theorem B2483779 : Blo 2207435 2483779 := bstep (se 1 (by rfl) ⟨1862834, by rfl⟩ : syracuseStep 2483779 = 3725669) B3725669
theorem B3311705 : Blo 2207435 3311705 := bstep (se 2 (by rfl) ⟨1241889, by rfl⟩ : syracuseStep 3311705 = 2483779) B2483779
theorem B2207803 : Blo 2207435 2207803 := bstep (se 1 (by rfl) ⟨1655852, by rfl⟩ : syracuseStep 2207803 = 3311705) B3311705
theorem B4715309 : Blo 2207435 4715309 := bbase (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) (by norm_num)
theorem B3143539 : Blo 2207435 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B16765541 : Blo 2207435 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B11177027 : Blo 2207435 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B7451351 : Blo 2207435 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B4967567 : Blo 2207435 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B3311711 : Blo 2207435 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B2207807 : Blo 2207435 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B3311717 : Blo 2207435 3311717 := bbase (se 4 (by rfl) ⟨310473, by rfl⟩ : syracuseStep 3311717 = 620947) (by norm_num)
theorem B2207811 : Blo 2207435 2207811 := bstep (se 1 (by rfl) ⟨1655858, by rfl⟩ : syracuseStep 2207811 = 3311717) B3311717
theorem B10070725 : Blo 2207435 10070725 := bbase (se 4 (by rfl) ⟨944130, by rfl⟩ : syracuseStep 10070725 = 1888261) (by norm_num)
theorem B13427633 : Blo 2207435 13427633 := bstep (se 2 (by rfl) ⟨5035362, by rfl⟩ : syracuseStep 13427633 = 10070725) B10070725
theorem B35807021 : Blo 2207435 35807021 := bstep (se 3 (by rfl) ⟨6713816, by rfl⟩ : syracuseStep 35807021 = 13427633) B13427633
theorem B23871347 : Blo 2207435 23871347 := bstep (se 1 (by rfl) ⟨17903510, by rfl⟩ : syracuseStep 23871347 = 35807021) B35807021
theorem B15914231 : Blo 2207435 15914231 := bstep (se 1 (by rfl) ⟨11935673, by rfl⟩ : syracuseStep 15914231 = 23871347) B23871347
theorem B10609487 : Blo 2207435 10609487 := bstep (se 1 (by rfl) ⟨7957115, by rfl⟩ : syracuseStep 10609487 = 15914231) B15914231
theorem B7072991 : Blo 2207435 7072991 := bstep (se 1 (by rfl) ⟨5304743, by rfl⟩ : syracuseStep 7072991 = 10609487) B10609487
theorem B4715327 : Blo 2207435 4715327 := bstep (se 1 (by rfl) ⟨3536495, by rfl⟩ : syracuseStep 4715327 = 7072991) B7072991
theorem B3143551 : Blo 2207435 3143551 := bstep (se 1 (by rfl) ⟨2357663, by rfl⟩ : syracuseStep 3143551 = 4715327) B4715327
theorem B4191401 : Blo 2207435 4191401 := bstep (se 2 (by rfl) ⟨1571775, by rfl⟩ : syracuseStep 4191401 = 3143551) B3143551
theorem B2794267 : Blo 2207435 2794267 := bstep (se 1 (by rfl) ⟨2095700, by rfl⟩ : syracuseStep 2794267 = 4191401) B4191401
theorem B3725689 : Blo 2207435 3725689 := bstep (se 2 (by rfl) ⟨1397133, by rfl⟩ : syracuseStep 3725689 = 2794267) B2794267
theorem B4967585 : Blo 2207435 4967585 := bstep (se 2 (by rfl) ⟨1862844, by rfl⟩ : syracuseStep 4967585 = 3725689) B3725689
theorem B3311723 : Blo 2207435 3311723 := bstep (se 1 (by rfl) ⟨2483792, by rfl⟩ : syracuseStep 3311723 = 4967585) B4967585
theorem B2207815 : Blo 2207435 2207815 := bstep (se 1 (by rfl) ⟨1655861, by rfl⟩ : syracuseStep 2207815 = 3311723) B3311723
theorem B2483797 : Blo 2207435 2483797 := bbase (se 8 (by rfl) ⟨14553, by rfl⟩ : syracuseStep 2483797 = 29107) (by norm_num)
theorem B3311729 : Blo 2207435 3311729 := bstep (se 2 (by rfl) ⟨1241898, by rfl⟩ : syracuseStep 3311729 = 2483797) B2483797
theorem B2207819 : Blo 2207435 2207819 := bstep (se 1 (by rfl) ⟨1655864, by rfl⟩ : syracuseStep 2207819 = 3311729) B3311729
theorem B2794277 : Blo 2207435 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B7451405 : Blo 2207435 7451405 := bstep (se 3 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 7451405 = 2794277) B2794277
theorem B4967603 : Blo 2207435 4967603 := bstep (se 1 (by rfl) ⟨3725702, by rfl⟩ : syracuseStep 4967603 = 7451405) B7451405
theorem B3311735 : Blo 2207435 3311735 := bstep (se 1 (by rfl) ⟨2483801, by rfl⟩ : syracuseStep 3311735 = 4967603) B4967603
theorem B2207823 : Blo 2207435 2207823 := bstep (se 1 (by rfl) ⟨1655867, by rfl⟩ : syracuseStep 2207823 = 3311735) B3311735
theorem B3311741 : Blo 2207435 3311741 := bbase (se 3 (by rfl) ⟨620951, by rfl⟩ : syracuseStep 3311741 = 1241903) (by norm_num)
theorem B2207827 : Blo 2207435 2207827 := bstep (se 1 (by rfl) ⟨1655870, by rfl⟩ : syracuseStep 2207827 = 3311741) B3311741
theorem B4967621 : Blo 2207435 4967621 := bbase (se 4 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 4967621 = 931429) (by norm_num)
theorem B3311747 : Blo 2207435 3311747 := bstep (se 1 (by rfl) ⟨2483810, by rfl⟩ : syracuseStep 3311747 = 4967621) B4967621
theorem B2207831 : Blo 2207435 2207831 := bstep (se 1 (by rfl) ⟨1655873, by rfl⟩ : syracuseStep 2207831 = 3311747) B3311747
theorem B3776557 : Blo 2207435 3776557 := bbase (se 3 (by rfl) ⟨708104, by rfl⟩ : syracuseStep 3776557 = 1416209) (by norm_num)
theorem B5035409 : Blo 2207435 5035409 := bstep (se 2 (by rfl) ⟨1888278, by rfl⟩ : syracuseStep 5035409 = 3776557) B3776557
theorem B3356939 : Blo 2207435 3356939 := bstep (se 1 (by rfl) ⟨2517704, by rfl⟩ : syracuseStep 3356939 = 5035409) B5035409
theorem B2237959 : Blo 2207435 2237959 := bstep (se 1 (by rfl) ⟨1678469, by rfl⟩ : syracuseStep 2237959 = 3356939) B3356939
theorem B11935781 : Blo 2207435 11935781 := bstep (se 4 (by rfl) ⟨1118979, by rfl⟩ : syracuseStep 11935781 = 2237959) B2237959
theorem B7957187 : Blo 2207435 7957187 := bstep (se 1 (by rfl) ⟨5967890, by rfl⟩ : syracuseStep 7957187 = 11935781) B11935781
theorem B5304791 : Blo 2207435 5304791 := bstep (se 1 (by rfl) ⟨3978593, by rfl⟩ : syracuseStep 5304791 = 7957187) B7957187
theorem B14146109 : Blo 2207435 14146109 := bstep (se 3 (by rfl) ⟨2652395, by rfl⟩ : syracuseStep 14146109 = 5304791) B5304791
theorem B9430739 : Blo 2207435 9430739 := bstep (se 1 (by rfl) ⟨7073054, by rfl⟩ : syracuseStep 9430739 = 14146109) B14146109
theorem B6287159 : Blo 2207435 6287159 := bstep (se 1 (by rfl) ⟨4715369, by rfl⟩ : syracuseStep 6287159 = 9430739) B9430739
theorem B4191439 : Blo 2207435 4191439 := bstep (se 1 (by rfl) ⟨3143579, by rfl⟩ : syracuseStep 4191439 = 6287159) B6287159
theorem B5588585 : Blo 2207435 5588585 := bstep (se 2 (by rfl) ⟨2095719, by rfl⟩ : syracuseStep 5588585 = 4191439) B4191439
theorem B3725723 : Blo 2207435 3725723 := bstep (se 1 (by rfl) ⟨2794292, by rfl⟩ : syracuseStep 3725723 = 5588585) B5588585
theorem B2483815 : Blo 2207435 2483815 := bstep (se 1 (by rfl) ⟨1862861, by rfl⟩ : syracuseStep 2483815 = 3725723) B3725723
theorem B3311753 : Blo 2207435 3311753 := bstep (se 2 (by rfl) ⟨1241907, by rfl⟩ : syracuseStep 3311753 = 2483815) B2483815
theorem B2207835 : Blo 2207435 2207835 := bstep (se 1 (by rfl) ⟨1655876, by rfl⟩ : syracuseStep 2207835 = 3311753) B3311753
theorem B11177189 : Blo 2207435 11177189 := bbase (se 4 (by rfl) ⟨1047861, by rfl⟩ : syracuseStep 11177189 = 2095723) (by norm_num)
theorem B7451459 : Blo 2207435 7451459 := bstep (se 1 (by rfl) ⟨5588594, by rfl⟩ : syracuseStep 7451459 = 11177189) B11177189
theorem B4967639 : Blo 2207435 4967639 := bstep (se 1 (by rfl) ⟨3725729, by rfl⟩ : syracuseStep 4967639 = 7451459) B7451459
theorem B3311759 : Blo 2207435 3311759 := bstep (se 1 (by rfl) ⟨2483819, by rfl⟩ : syracuseStep 3311759 = 4967639) B4967639
theorem B2207839 : Blo 2207435 2207839 := bstep (se 1 (by rfl) ⟨1655879, by rfl⟩ : syracuseStep 2207839 = 3311759) B3311759
theorem B3311765 : Blo 2207435 3311765 := bbase (se 6 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 3311765 = 155239) (by norm_num)
theorem B2207843 : Blo 2207435 2207843 := bstep (se 1 (by rfl) ⟨1655882, by rfl⟩ : syracuseStep 2207843 = 3311765) B3311765
theorem B9430789 : Blo 2207435 9430789 := bbase (se 4 (by rfl) ⟨884136, by rfl⟩ : syracuseStep 9430789 = 1768273) (by norm_num)
theorem B12574385 : Blo 2207435 12574385 := bstep (se 2 (by rfl) ⟨4715394, by rfl⟩ : syracuseStep 12574385 = 9430789) B9430789
theorem B8382923 : Blo 2207435 8382923 := bstep (se 1 (by rfl) ⟨6287192, by rfl⟩ : syracuseStep 8382923 = 12574385) B12574385
theorem B5588615 : Blo 2207435 5588615 := bstep (se 1 (by rfl) ⟨4191461, by rfl⟩ : syracuseStep 5588615 = 8382923) B8382923
theorem B3725743 : Blo 2207435 3725743 := bstep (se 1 (by rfl) ⟨2794307, by rfl⟩ : syracuseStep 3725743 = 5588615) B5588615
theorem B4967657 : Blo 2207435 4967657 := bstep (se 2 (by rfl) ⟨1862871, by rfl⟩ : syracuseStep 4967657 = 3725743) B3725743
theorem B3311771 : Blo 2207435 3311771 := bstep (se 1 (by rfl) ⟨2483828, by rfl⟩ : syracuseStep 3311771 = 4967657) B4967657
theorem B2207847 : Blo 2207435 2207847 := bstep (se 1 (by rfl) ⟨1655885, by rfl⟩ : syracuseStep 2207847 = 3311771) B3311771
theorem B2483833 : Blo 2207435 2483833 := bbase (se 2 (by rfl) ⟨931437, by rfl⟩ : syracuseStep 2483833 = 1862875) (by norm_num)
theorem B3311777 : Blo 2207435 3311777 := bstep (se 2 (by rfl) ⟨1241916, by rfl⟩ : syracuseStep 3311777 = 2483833) B2483833
theorem B2207851 : Blo 2207435 2207851 := bstep (se 1 (by rfl) ⟨1655888, by rfl⟩ : syracuseStep 2207851 = 3311777) B3311777
theorem B5820517 : Blo 2207435 5820517 := bbase (se 4 (by rfl) ⟨545673, by rfl⟩ : syracuseStep 5820517 = 1091347) (by norm_num)
theorem B31042757 : Blo 2207435 31042757 := bstep (se 4 (by rfl) ⟨2910258, by rfl⟩ : syracuseStep 31042757 = 5820517) B5820517
theorem B20695171 : Blo 2207435 20695171 := bstep (se 1 (by rfl) ⟨15521378, by rfl⟩ : syracuseStep 20695171 = 31042757) B31042757
theorem B27593561 : Blo 2207435 27593561 := bstep (se 2 (by rfl) ⟨10347585, by rfl⟩ : syracuseStep 27593561 = 20695171) B20695171
theorem B18395707 : Blo 2207435 18395707 := bstep (se 1 (by rfl) ⟨13796780, by rfl⟩ : syracuseStep 18395707 = 27593561) B27593561
theorem B24527609 : Blo 2207435 24527609 := bstep (se 2 (by rfl) ⟨9197853, by rfl⟩ : syracuseStep 24527609 = 18395707) B18395707
theorem B16351739 : Blo 2207435 16351739 := bstep (se 1 (by rfl) ⟨12263804, by rfl⟩ : syracuseStep 16351739 = 24527609) B24527609
theorem B10901159 : Blo 2207435 10901159 := bstep (se 1 (by rfl) ⟨8175869, by rfl⟩ : syracuseStep 10901159 = 16351739) B16351739
theorem B7267439 : Blo 2207435 7267439 := bstep (se 1 (by rfl) ⟨5450579, by rfl⟩ : syracuseStep 7267439 = 10901159) B10901159
theorem B19379837 : Blo 2207435 19379837 := bstep (se 3 (by rfl) ⟨3633719, by rfl⟩ : syracuseStep 19379837 = 7267439) B7267439
theorem B12919891 : Blo 2207435 12919891 := bstep (se 1 (by rfl) ⟨9689918, by rfl⟩ : syracuseStep 12919891 = 19379837) B19379837
theorem B17226521 : Blo 2207435 17226521 := bstep (se 2 (by rfl) ⟨6459945, by rfl⟩ : syracuseStep 17226521 = 12919891) B12919891
theorem B11484347 : Blo 2207435 11484347 := bstep (se 1 (by rfl) ⟨8613260, by rfl⟩ : syracuseStep 11484347 = 17226521) B17226521
theorem B30624925 : Blo 2207435 30624925 := bstep (se 3 (by rfl) ⟨5742173, by rfl⟩ : syracuseStep 30624925 = 11484347) B11484347
theorem B40833233 : Blo 2207435 40833233 := bstep (se 2 (by rfl) ⟨15312462, by rfl⟩ : syracuseStep 40833233 = 30624925) B30624925
theorem B27222155 : Blo 2207435 27222155 := bstep (se 1 (by rfl) ⟨20416616, by rfl⟩ : syracuseStep 27222155 = 40833233) B40833233
theorem B18148103 : Blo 2207435 18148103 := bstep (se 1 (by rfl) ⟨13611077, by rfl⟩ : syracuseStep 18148103 = 27222155) B27222155
theorem B12098735 : Blo 2207435 12098735 := bstep (se 1 (by rfl) ⟨9074051, by rfl⟩ : syracuseStep 12098735 = 18148103) B18148103
theorem B8065823 : Blo 2207435 8065823 := bstep (se 1 (by rfl) ⟨6049367, by rfl⟩ : syracuseStep 8065823 = 12098735) B12098735
theorem B21508861 : Blo 2207435 21508861 := bstep (se 3 (by rfl) ⟨4032911, by rfl⟩ : syracuseStep 21508861 = 8065823) B8065823
theorem B28678481 : Blo 2207435 28678481 := bstep (se 2 (by rfl) ⟨10754430, by rfl⟩ : syracuseStep 28678481 = 21508861) B21508861
theorem B19118987 : Blo 2207435 19118987 := bstep (se 1 (by rfl) ⟨14339240, by rfl⟩ : syracuseStep 19118987 = 28678481) B28678481
theorem B12745991 : Blo 2207435 12745991 := bstep (se 1 (by rfl) ⟨9559493, by rfl⟩ : syracuseStep 12745991 = 19118987) B19118987
theorem B8497327 : Blo 2207435 8497327 := bstep (se 1 (by rfl) ⟨6372995, by rfl⟩ : syracuseStep 8497327 = 12745991) B12745991
theorem B11329769 : Blo 2207435 11329769 := bstep (se 2 (by rfl) ⟨4248663, by rfl⟩ : syracuseStep 11329769 = 8497327) B8497327
theorem B7553179 : Blo 2207435 7553179 := bstep (se 1 (by rfl) ⟨5664884, by rfl⟩ : syracuseStep 7553179 = 11329769) B11329769
theorem B10070905 : Blo 2207435 10070905 := bstep (se 2 (by rfl) ⟨3776589, by rfl⟩ : syracuseStep 10070905 = 7553179) B7553179
theorem B13427873 : Blo 2207435 13427873 := bstep (se 2 (by rfl) ⟨5035452, by rfl⟩ : syracuseStep 13427873 = 10070905) B10070905
theorem B8951915 : Blo 2207435 8951915 := bstep (se 1 (by rfl) ⟨6713936, by rfl⟩ : syracuseStep 8951915 = 13427873) B13427873
theorem B23871773 : Blo 2207435 23871773 := bstep (se 3 (by rfl) ⟨4475957, by rfl⟩ : syracuseStep 23871773 = 8951915) B8951915
theorem B15914515 : Blo 2207435 15914515 := bstep (se 1 (by rfl) ⟨11935886, by rfl⟩ : syracuseStep 15914515 = 23871773) B23871773
theorem B21219353 : Blo 2207435 21219353 := bstep (se 2 (by rfl) ⟨7957257, by rfl⟩ : syracuseStep 21219353 = 15914515) B15914515
theorem B14146235 : Blo 2207435 14146235 := bstep (se 1 (by rfl) ⟨10609676, by rfl⟩ : syracuseStep 14146235 = 21219353) B21219353
theorem B9430823 : Blo 2207435 9430823 := bstep (se 1 (by rfl) ⟨7073117, by rfl⟩ : syracuseStep 9430823 = 14146235) B14146235
theorem B6287215 : Blo 2207435 6287215 := bstep (se 1 (by rfl) ⟨4715411, by rfl⟩ : syracuseStep 6287215 = 9430823) B9430823
theorem B8382953 : Blo 2207435 8382953 := bstep (se 2 (by rfl) ⟨3143607, by rfl⟩ : syracuseStep 8382953 = 6287215) B6287215
theorem B5588635 : Blo 2207435 5588635 := bstep (se 1 (by rfl) ⟨4191476, by rfl⟩ : syracuseStep 5588635 = 8382953) B8382953
theorem B7451513 : Blo 2207435 7451513 := bstep (se 2 (by rfl) ⟨2794317, by rfl⟩ : syracuseStep 7451513 = 5588635) B5588635
theorem B4967675 : Blo 2207435 4967675 := bstep (se 1 (by rfl) ⟨3725756, by rfl⟩ : syracuseStep 4967675 = 7451513) B7451513
theorem B3311783 : Blo 2207435 3311783 := bstep (se 1 (by rfl) ⟨2483837, by rfl⟩ : syracuseStep 3311783 = 4967675) B4967675
theorem B2207855 : Blo 2207435 2207855 := bstep (se 1 (by rfl) ⟨1655891, by rfl⟩ : syracuseStep 2207855 = 3311783) B3311783
theorem B3311789 : Blo 2207435 3311789 := bbase (se 3 (by rfl) ⟨620960, by rfl⟩ : syracuseStep 3311789 = 1241921) (by norm_num)
theorem B2207859 : Blo 2207435 2207859 := bstep (se 1 (by rfl) ⟨1655894, by rfl⟩ : syracuseStep 2207859 = 3311789) B3311789
theorem B4967693 : Blo 2207435 4967693 := bbase (se 3 (by rfl) ⟨931442, by rfl⟩ : syracuseStep 4967693 = 1862885) (by norm_num)
theorem B3311795 : Blo 2207435 3311795 := bstep (se 1 (by rfl) ⟨2483846, by rfl⟩ : syracuseStep 3311795 = 4967693) B4967693
theorem B2207863 : Blo 2207435 2207863 := bstep (se 1 (by rfl) ⟨1655897, by rfl⟩ : syracuseStep 2207863 = 3311795) B3311795
theorem B2794333 : Blo 2207435 2794333 := bbase (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) (by norm_num)
theorem B3725777 : Blo 2207435 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B2483851 : Blo 2207435 2483851 := bstep (se 1 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 2483851 = 3725777) B3725777
theorem B3311801 : Blo 2207435 3311801 := bstep (se 2 (by rfl) ⟨1241925, by rfl⟩ : syracuseStep 3311801 = 2483851) B2483851
theorem B2207867 : Blo 2207435 2207867 := bstep (se 1 (by rfl) ⟨1655900, by rfl⟩ : syracuseStep 2207867 = 3311801) B3311801
theorem B18861781 : Blo 2207435 18861781 := bbase (se 7 (by rfl) ⟨221036, by rfl⟩ : syracuseStep 18861781 = 442073) (by norm_num)
theorem B25149041 : Blo 2207435 25149041 := bstep (se 2 (by rfl) ⟨9430890, by rfl⟩ : syracuseStep 25149041 = 18861781) B18861781
theorem B16766027 : Blo 2207435 16766027 := bstep (se 1 (by rfl) ⟨12574520, by rfl⟩ : syracuseStep 16766027 = 25149041) B25149041
theorem B11177351 : Blo 2207435 11177351 := bstep (se 1 (by rfl) ⟨8383013, by rfl⟩ : syracuseStep 11177351 = 16766027) B16766027
theorem B7451567 : Blo 2207435 7451567 := bstep (se 1 (by rfl) ⟨5588675, by rfl⟩ : syracuseStep 7451567 = 11177351) B11177351
theorem B4967711 : Blo 2207435 4967711 := bstep (se 1 (by rfl) ⟨3725783, by rfl⟩ : syracuseStep 4967711 = 7451567) B7451567
theorem B3311807 : Blo 2207435 3311807 := bstep (se 1 (by rfl) ⟨2483855, by rfl⟩ : syracuseStep 3311807 = 4967711) B4967711
theorem B2207871 : Blo 2207435 2207871 := bstep (se 1 (by rfl) ⟨1655903, by rfl⟩ : syracuseStep 2207871 = 3311807) B3311807
theorem B3311813 : Blo 2207435 3311813 := bbase (se 4 (by rfl) ⟨310482, by rfl⟩ : syracuseStep 3311813 = 620965) (by norm_num)
theorem B2207875 : Blo 2207435 2207875 := bstep (se 1 (by rfl) ⟨1655906, by rfl⟩ : syracuseStep 2207875 = 3311813) B3311813
theorem B3725797 : Blo 2207435 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B4967729 : Blo 2207435 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B3311819 : Blo 2207435 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B2207879 : Blo 2207435 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B2483869 : Blo 2207435 2483869 := bbase (se 3 (by rfl) ⟨465725, by rfl⟩ : syracuseStep 2483869 = 931451) (by norm_num)
theorem B3311825 : Blo 2207435 3311825 := bstep (se 2 (by rfl) ⟨1241934, by rfl⟩ : syracuseStep 3311825 = 2483869) B2483869
theorem B2207883 : Blo 2207435 2207883 := bstep (se 1 (by rfl) ⟨1655912, by rfl⟩ : syracuseStep 2207883 = 3311825) B3311825
theorem B7451621 : Blo 2207435 7451621 := bbase (se 4 (by rfl) ⟨698589, by rfl⟩ : syracuseStep 7451621 = 1397179) (by norm_num)
theorem B4967747 : Blo 2207435 4967747 := bstep (se 1 (by rfl) ⟨3725810, by rfl⟩ : syracuseStep 4967747 = 7451621) B7451621
theorem B3311831 : Blo 2207435 3311831 := bstep (se 1 (by rfl) ⟨2483873, by rfl⟩ : syracuseStep 3311831 = 4967747) B4967747
theorem B2207887 : Blo 2207435 2207887 := bstep (se 1 (by rfl) ⟨1655915, by rfl⟩ : syracuseStep 2207887 = 3311831) B3311831
theorem B3311837 : Blo 2207435 3311837 := bbase (se 3 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 3311837 = 1241939) (by norm_num)
theorem B2207891 : Blo 2207435 2207891 := bstep (se 1 (by rfl) ⟨1655918, by rfl⟩ : syracuseStep 2207891 = 3311837) B3311837
theorem B4967765 : Blo 2207435 4967765 := bbase (se 11 (by rfl) ⟨3638, by rfl⟩ : syracuseStep 4967765 = 7277) (by norm_num)
theorem B3311843 : Blo 2207435 3311843 := bstep (se 1 (by rfl) ⟨2483882, by rfl⟩ : syracuseStep 3311843 = 4967765) B4967765
theorem B2207895 : Blo 2207435 2207895 := bstep (se 1 (by rfl) ⟨1655921, by rfl⟩ : syracuseStep 2207895 = 3311843) B3311843
theorem B2357753 : Blo 2207435 2357753 := bbase (se 2 (by rfl) ⟨884157, by rfl⟩ : syracuseStep 2357753 = 1768315) (by norm_num)
theorem B6287341 : Blo 2207435 6287341 := bstep (se 3 (by rfl) ⟨1178876, by rfl⟩ : syracuseStep 6287341 = 2357753) B2357753
theorem B8383121 : Blo 2207435 8383121 := bstep (se 2 (by rfl) ⟨3143670, by rfl⟩ : syracuseStep 8383121 = 6287341) B6287341
theorem B5588747 : Blo 2207435 5588747 := bstep (se 1 (by rfl) ⟨4191560, by rfl⟩ : syracuseStep 5588747 = 8383121) B8383121
theorem B3725831 : Blo 2207435 3725831 := bstep (se 1 (by rfl) ⟨2794373, by rfl⟩ : syracuseStep 3725831 = 5588747) B5588747
theorem B2483887 : Blo 2207435 2483887 := bstep (se 1 (by rfl) ⟨1862915, by rfl⟩ : syracuseStep 2483887 = 3725831) B3725831
theorem B3311849 : Blo 2207435 3311849 := bstep (se 2 (by rfl) ⟨1241943, by rfl⟩ : syracuseStep 3311849 = 2483887) B2483887
theorem B2207899 : Blo 2207435 2207899 := bstep (se 1 (by rfl) ⟨1655924, by rfl⟩ : syracuseStep 2207899 = 3311849) B3311849
theorem B6460085 : Blo 2207435 6460085 := bbase (se 5 (by rfl) ⟨302816, by rfl⟩ : syracuseStep 6460085 = 605633) (by norm_num)
theorem B17226893 : Blo 2207435 17226893 := bstep (se 3 (by rfl) ⟨3230042, by rfl⟩ : syracuseStep 17226893 = 6460085) B6460085
theorem B11484595 : Blo 2207435 11484595 := bstep (se 1 (by rfl) ⟨8613446, by rfl⟩ : syracuseStep 11484595 = 17226893) B17226893
theorem B61251173 : Blo 2207435 61251173 := bstep (se 4 (by rfl) ⟨5742297, by rfl⟩ : syracuseStep 61251173 = 11484595) B11484595
theorem B40834115 : Blo 2207435 40834115 := bstep (se 1 (by rfl) ⟨30625586, by rfl⟩ : syracuseStep 40834115 = 61251173) B61251173
theorem B27222743 : Blo 2207435 27222743 := bstep (se 1 (by rfl) ⟨20417057, by rfl⟩ : syracuseStep 27222743 = 40834115) B40834115
theorem B72593981 : Blo 2207435 72593981 := bstep (se 3 (by rfl) ⟨13611371, by rfl⟩ : syracuseStep 72593981 = 27222743) B27222743
theorem B48395987 : Blo 2207435 48395987 := bstep (se 1 (by rfl) ⟨36296990, by rfl⟩ : syracuseStep 48395987 = 72593981) B72593981
theorem B32263991 : Blo 2207435 32263991 := bstep (se 1 (by rfl) ⟨24197993, by rfl⟩ : syracuseStep 32263991 = 48395987) B48395987
theorem B21509327 : Blo 2207435 21509327 := bstep (se 1 (by rfl) ⟨16131995, by rfl⟩ : syracuseStep 21509327 = 32263991) B32263991
theorem B14339551 : Blo 2207435 14339551 := bstep (se 1 (by rfl) ⟨10754663, by rfl⟩ : syracuseStep 14339551 = 21509327) B21509327
theorem B19119401 : Blo 2207435 19119401 := bstep (se 2 (by rfl) ⟨7169775, by rfl⟩ : syracuseStep 19119401 = 14339551) B14339551
theorem B12746267 : Blo 2207435 12746267 := bstep (se 1 (by rfl) ⟨9559700, by rfl⟩ : syracuseStep 12746267 = 19119401) B19119401
theorem B8497511 : Blo 2207435 8497511 := bstep (se 1 (by rfl) ⟨6373133, by rfl⟩ : syracuseStep 8497511 = 12746267) B12746267
theorem B5665007 : Blo 2207435 5665007 := bstep (se 1 (by rfl) ⟨4248755, by rfl⟩ : syracuseStep 5665007 = 8497511) B8497511
theorem B3776671 : Blo 2207435 3776671 := bstep (se 1 (by rfl) ⟨2832503, by rfl⟩ : syracuseStep 3776671 = 5665007) B5665007
theorem B20142245 : Blo 2207435 20142245 := bstep (se 4 (by rfl) ⟨1888335, by rfl⟩ : syracuseStep 20142245 = 3776671) B3776671
theorem B13428163 : Blo 2207435 13428163 := bstep (se 1 (by rfl) ⟨10071122, by rfl⟩ : syracuseStep 13428163 = 20142245) B20142245
theorem B71616869 : Blo 2207435 71616869 := bstep (se 4 (by rfl) ⟨6714081, by rfl⟩ : syracuseStep 71616869 = 13428163) B13428163
theorem B47744579 : Blo 2207435 47744579 := bstep (se 1 (by rfl) ⟨35808434, by rfl⟩ : syracuseStep 47744579 = 71616869) B71616869
theorem B31829719 : Blo 2207435 31829719 := bstep (se 1 (by rfl) ⟨23872289, by rfl⟩ : syracuseStep 31829719 = 47744579) B47744579
theorem B42439625 : Blo 2207435 42439625 := bstep (se 2 (by rfl) ⟨15914859, by rfl⟩ : syracuseStep 42439625 = 31829719) B31829719
theorem B28293083 : Blo 2207435 28293083 := bstep (se 1 (by rfl) ⟨21219812, by rfl⟩ : syracuseStep 28293083 = 42439625) B42439625
theorem B18862055 : Blo 2207435 18862055 := bstep (se 1 (by rfl) ⟨14146541, by rfl⟩ : syracuseStep 18862055 = 28293083) B28293083
theorem B12574703 : Blo 2207435 12574703 := bstep (se 1 (by rfl) ⟨9431027, by rfl⟩ : syracuseStep 12574703 = 18862055) B18862055
theorem B8383135 : Blo 2207435 8383135 := bstep (se 1 (by rfl) ⟨6287351, by rfl⟩ : syracuseStep 8383135 = 12574703) B12574703
theorem B11177513 : Blo 2207435 11177513 := bstep (se 2 (by rfl) ⟨4191567, by rfl⟩ : syracuseStep 11177513 = 8383135) B8383135
theorem B7451675 : Blo 2207435 7451675 := bstep (se 1 (by rfl) ⟨5588756, by rfl⟩ : syracuseStep 7451675 = 11177513) B11177513
theorem B4967783 : Blo 2207435 4967783 := bstep (se 1 (by rfl) ⟨3725837, by rfl⟩ : syracuseStep 4967783 = 7451675) B7451675
theorem B3311855 : Blo 2207435 3311855 := bstep (se 1 (by rfl) ⟨2483891, by rfl⟩ : syracuseStep 3311855 = 4967783) B4967783
theorem B2207903 : Blo 2207435 2207903 := bstep (se 1 (by rfl) ⟨1655927, by rfl⟩ : syracuseStep 2207903 = 3311855) B3311855
theorem B3311861 : Blo 2207435 3311861 := bbase (se 5 (by rfl) ⟨155243, by rfl⟩ : syracuseStep 3311861 = 310487) (by norm_num)
theorem B2207907 : Blo 2207435 2207907 := bstep (se 1 (by rfl) ⟨1655930, by rfl⟩ : syracuseStep 2207907 = 3311861) B3311861
theorem B21219893 : Blo 2207435 21219893 := bbase (se 5 (by rfl) ⟨994682, by rfl⟩ : syracuseStep 21219893 = 1989365) (by norm_num)
theorem B14146595 : Blo 2207435 14146595 := bstep (se 1 (by rfl) ⟨10609946, by rfl⟩ : syracuseStep 14146595 = 21219893) B21219893
theorem B9431063 : Blo 2207435 9431063 := bstep (se 1 (by rfl) ⟨7073297, by rfl⟩ : syracuseStep 9431063 = 14146595) B14146595
theorem B6287375 : Blo 2207435 6287375 := bstep (se 1 (by rfl) ⟨4715531, by rfl⟩ : syracuseStep 6287375 = 9431063) B9431063
theorem B4191583 : Blo 2207435 4191583 := bstep (se 1 (by rfl) ⟨3143687, by rfl⟩ : syracuseStep 4191583 = 6287375) B6287375
theorem B5588777 : Blo 2207435 5588777 := bstep (se 2 (by rfl) ⟨2095791, by rfl⟩ : syracuseStep 5588777 = 4191583) B4191583
theorem B3725851 : Blo 2207435 3725851 := bstep (se 1 (by rfl) ⟨2794388, by rfl⟩ : syracuseStep 3725851 = 5588777) B5588777
theorem B4967801 : Blo 2207435 4967801 := bstep (se 2 (by rfl) ⟨1862925, by rfl⟩ : syracuseStep 4967801 = 3725851) B3725851
theorem B3311867 : Blo 2207435 3311867 := bstep (se 1 (by rfl) ⟨2483900, by rfl⟩ : syracuseStep 3311867 = 4967801) B4967801
theorem B2207911 : Blo 2207435 2207911 := bstep (se 1 (by rfl) ⟨1655933, by rfl⟩ : syracuseStep 2207911 = 3311867) B3311867
theorem B2483905 : Blo 2207435 2483905 := bbase (se 2 (by rfl) ⟨931464, by rfl⟩ : syracuseStep 2483905 = 1862929) (by norm_num)
theorem B3311873 : Blo 2207435 3311873 := bstep (se 2 (by rfl) ⟨1241952, by rfl⟩ : syracuseStep 3311873 = 2483905) B2483905
theorem B2207915 : Blo 2207435 2207915 := bstep (se 1 (by rfl) ⟨1655936, by rfl⟩ : syracuseStep 2207915 = 3311873) B3311873
theorem B5588797 : Blo 2207435 5588797 := bbase (se 3 (by rfl) ⟨1047899, by rfl⟩ : syracuseStep 5588797 = 2095799) (by norm_num)
theorem B7451729 : Blo 2207435 7451729 := bstep (se 2 (by rfl) ⟨2794398, by rfl⟩ : syracuseStep 7451729 = 5588797) B5588797
theorem B4967819 : Blo 2207435 4967819 := bstep (se 1 (by rfl) ⟨3725864, by rfl⟩ : syracuseStep 4967819 = 7451729) B7451729
theorem B3311879 : Blo 2207435 3311879 := bstep (se 1 (by rfl) ⟨2483909, by rfl⟩ : syracuseStep 3311879 = 4967819) B4967819
theorem B2207919 : Blo 2207435 2207919 := bstep (se 1 (by rfl) ⟨1655939, by rfl⟩ : syracuseStep 2207919 = 3311879) B3311879
theorem B3311885 : Blo 2207435 3311885 := bbase (se 3 (by rfl) ⟨620978, by rfl⟩ : syracuseStep 3311885 = 1241957) (by norm_num)
theorem B2207923 : Blo 2207435 2207923 := bstep (se 1 (by rfl) ⟨1655942, by rfl⟩ : syracuseStep 2207923 = 3311885) B3311885
theorem B4967837 : Blo 2207435 4967837 := bbase (se 3 (by rfl) ⟨931469, by rfl⟩ : syracuseStep 4967837 = 1862939) (by norm_num)
theorem B3311891 : Blo 2207435 3311891 := bstep (se 1 (by rfl) ⟨2483918, by rfl⟩ : syracuseStep 3311891 = 4967837) B4967837
theorem B2207927 : Blo 2207435 2207927 := bstep (se 1 (by rfl) ⟨1655945, by rfl⟩ : syracuseStep 2207927 = 3311891) B3311891
theorem B3725885 : Blo 2207435 3725885 := bbase (se 3 (by rfl) ⟨698603, by rfl⟩ : syracuseStep 3725885 = 1397207) (by norm_num)
theorem B2483923 : Blo 2207435 2483923 := bstep (se 1 (by rfl) ⟨1862942, by rfl⟩ : syracuseStep 2483923 = 3725885) B3725885
theorem B3311897 : Blo 2207435 3311897 := bstep (se 2 (by rfl) ⟨1241961, by rfl⟩ : syracuseStep 3311897 = 2483923) B2483923
theorem B2207931 : Blo 2207435 2207931 := bstep (se 1 (by rfl) ⟨1655948, by rfl⟩ : syracuseStep 2207931 = 3311897) B3311897
theorem B6714181 : Blo 2207435 6714181 := bbase (se 4 (by rfl) ⟨629454, by rfl⟩ : syracuseStep 6714181 = 1258909) (by norm_num)
theorem B8952241 : Blo 2207435 8952241 := bstep (se 2 (by rfl) ⟨3357090, by rfl⟩ : syracuseStep 8952241 = 6714181) B6714181
theorem B11936321 : Blo 2207435 11936321 := bstep (se 2 (by rfl) ⟨4476120, by rfl⟩ : syracuseStep 11936321 = 8952241) B8952241
theorem B7957547 : Blo 2207435 7957547 := bstep (se 1 (by rfl) ⟨5968160, by rfl⟩ : syracuseStep 7957547 = 11936321) B11936321
theorem B5305031 : Blo 2207435 5305031 := bstep (se 1 (by rfl) ⟨3978773, by rfl⟩ : syracuseStep 5305031 = 7957547) B7957547
theorem B3536687 : Blo 2207435 3536687 := bstep (se 1 (by rfl) ⟨2652515, by rfl⟩ : syracuseStep 3536687 = 5305031) B5305031
theorem B2357791 : Blo 2207435 2357791 := bstep (se 1 (by rfl) ⟨1768343, by rfl⟩ : syracuseStep 2357791 = 3536687) B3536687
theorem B12574885 : Blo 2207435 12574885 := bstep (se 4 (by rfl) ⟨1178895, by rfl⟩ : syracuseStep 12574885 = 2357791) B2357791
theorem B16766513 : Blo 2207435 16766513 := bstep (se 2 (by rfl) ⟨6287442, by rfl⟩ : syracuseStep 16766513 = 12574885) B12574885
theorem B11177675 : Blo 2207435 11177675 := bstep (se 1 (by rfl) ⟨8383256, by rfl⟩ : syracuseStep 11177675 = 16766513) B16766513
theorem B7451783 : Blo 2207435 7451783 := bstep (se 1 (by rfl) ⟨5588837, by rfl⟩ : syracuseStep 7451783 = 11177675) B11177675
theorem B4967855 : Blo 2207435 4967855 := bstep (se 1 (by rfl) ⟨3725891, by rfl⟩ : syracuseStep 4967855 = 7451783) B7451783
theorem B3311903 : Blo 2207435 3311903 := bstep (se 1 (by rfl) ⟨2483927, by rfl⟩ : syracuseStep 3311903 = 4967855) B4967855
theorem B2207935 : Blo 2207435 2207935 := bstep (se 1 (by rfl) ⟨1655951, by rfl⟩ : syracuseStep 2207935 = 3311903) B3311903
theorem B3311909 : Blo 2207435 3311909 := bbase (se 4 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 3311909 = 620983) (by norm_num)
theorem B2207939 : Blo 2207435 2207939 := bstep (se 1 (by rfl) ⟨1655954, by rfl⟩ : syracuseStep 2207939 = 3311909) B3311909
theorem B2794429 : Blo 2207435 2794429 := bbase (se 3 (by rfl) ⟨523955, by rfl⟩ : syracuseStep 2794429 = 1047911) (by norm_num)
theorem B3725905 : Blo 2207435 3725905 := bstep (se 2 (by rfl) ⟨1397214, by rfl⟩ : syracuseStep 3725905 = 2794429) B2794429
theorem B4967873 : Blo 2207435 4967873 := bstep (se 2 (by rfl) ⟨1862952, by rfl⟩ : syracuseStep 4967873 = 3725905) B3725905
theorem B3311915 : Blo 2207435 3311915 := bstep (se 1 (by rfl) ⟨2483936, by rfl⟩ : syracuseStep 3311915 = 4967873) B4967873
theorem B2207943 : Blo 2207435 2207943 := bstep (se 1 (by rfl) ⟨1655957, by rfl⟩ : syracuseStep 2207943 = 3311915) B3311915
theorem B2483941 : Blo 2207435 2483941 := bbase (se 4 (by rfl) ⟨232869, by rfl⟩ : syracuseStep 2483941 = 465739) (by norm_num)
theorem B3311921 : Blo 2207435 3311921 := bstep (se 2 (by rfl) ⟨1241970, by rfl⟩ : syracuseStep 3311921 = 2483941) B2483941
theorem B2207947 : Blo 2207435 2207947 := bstep (se 1 (by rfl) ⟨1655960, by rfl⟩ : syracuseStep 2207947 = 3311921) B3311921
theorem B2238077 : Blo 2207435 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B5968205 : Blo 2207435 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B3978803 : Blo 2207435 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B2652535 : Blo 2207435 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B3536713 : Blo 2207435 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B4715617 : Blo 2207435 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B6287489 : Blo 2207435 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B4191659 : Blo 2207435 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B2794439 : Blo 2207435 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B7451837 : Blo 2207435 7451837 := bstep (se 3 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 7451837 = 2794439) B2794439
theorem B4967891 : Blo 2207435 4967891 := bstep (se 1 (by rfl) ⟨3725918, by rfl⟩ : syracuseStep 4967891 = 7451837) B7451837
theorem B3311927 : Blo 2207435 3311927 := bstep (se 1 (by rfl) ⟨2483945, by rfl⟩ : syracuseStep 3311927 = 4967891) B4967891
theorem B2207951 : Blo 2207435 2207951 := bstep (se 1 (by rfl) ⟨1655963, by rfl⟩ : syracuseStep 2207951 = 3311927) B3311927
theorem B3311933 : Blo 2207435 3311933 := bbase (se 3 (by rfl) ⟨620987, by rfl⟩ : syracuseStep 3311933 = 1241975) (by norm_num)
theorem B2207955 : Blo 2207435 2207955 := bstep (se 1 (by rfl) ⟨1655966, by rfl⟩ : syracuseStep 2207955 = 3311933) B3311933
theorem B4967909 : Blo 2207435 4967909 := bbase (se 4 (by rfl) ⟨465741, by rfl⟩ : syracuseStep 4967909 = 931483) (by norm_num)
theorem B3311939 : Blo 2207435 3311939 := bstep (se 1 (by rfl) ⟨2483954, by rfl⟩ : syracuseStep 3311939 = 4967909) B4967909
theorem B2207959 : Blo 2207435 2207959 := bstep (se 1 (by rfl) ⟨1655969, by rfl⟩ : syracuseStep 2207959 = 3311939) B3311939
theorem B5588909 : Blo 2207435 5588909 := bbase (se 3 (by rfl) ⟨1047920, by rfl⟩ : syracuseStep 5588909 = 2095841) (by norm_num)
theorem B3725939 : Blo 2207435 3725939 := bstep (se 1 (by rfl) ⟨2794454, by rfl⟩ : syracuseStep 3725939 = 5588909) B5588909
theorem B2483959 : Blo 2207435 2483959 := bstep (se 1 (by rfl) ⟨1862969, by rfl⟩ : syracuseStep 2483959 = 3725939) B3725939
theorem B3311945 : Blo 2207435 3311945 := bstep (se 2 (by rfl) ⟨1241979, by rfl⟩ : syracuseStep 3311945 = 2483959) B2483959
theorem B2207963 : Blo 2207435 2207963 := bstep (se 1 (by rfl) ⟨1655972, by rfl⟩ : syracuseStep 2207963 = 3311945) B3311945
theorem B7073477 : Blo 2207435 7073477 := bbase (se 4 (by rfl) ⟨663138, by rfl⟩ : syracuseStep 7073477 = 1326277) (by norm_num)
theorem B4715651 : Blo 2207435 4715651 := bstep (se 1 (by rfl) ⟨3536738, by rfl⟩ : syracuseStep 4715651 = 7073477) B7073477
theorem B3143767 : Blo 2207435 3143767 := bstep (se 1 (by rfl) ⟨2357825, by rfl⟩ : syracuseStep 3143767 = 4715651) B4715651
theorem B4191689 : Blo 2207435 4191689 := bstep (se 2 (by rfl) ⟨1571883, by rfl⟩ : syracuseStep 4191689 = 3143767) B3143767
theorem B11177837 : Blo 2207435 11177837 := bstep (se 3 (by rfl) ⟨2095844, by rfl⟩ : syracuseStep 11177837 = 4191689) B4191689
theorem B7451891 : Blo 2207435 7451891 := bstep (se 1 (by rfl) ⟨5588918, by rfl⟩ : syracuseStep 7451891 = 11177837) B11177837
theorem B4967927 : Blo 2207435 4967927 := bstep (se 1 (by rfl) ⟨3725945, by rfl⟩ : syracuseStep 4967927 = 7451891) B7451891
theorem B3311951 : Blo 2207435 3311951 := bstep (se 1 (by rfl) ⟨2483963, by rfl⟩ : syracuseStep 3311951 = 4967927) B4967927
theorem B2207967 : Blo 2207435 2207967 := bstep (se 1 (by rfl) ⟨1655975, by rfl⟩ : syracuseStep 2207967 = 3311951) B3311951
theorem B3311957 : Blo 2207435 3311957 := bbase (se 10 (by rfl) ⟨4851, by rfl⟩ : syracuseStep 3311957 = 9703) (by norm_num)
theorem B2207971 : Blo 2207435 2207971 := bstep (se 1 (by rfl) ⟨1655978, by rfl⟩ : syracuseStep 2207971 = 3311957) B3311957
theorem B6287557 : Blo 2207435 6287557 := bbase (se 4 (by rfl) ⟨589458, by rfl⟩ : syracuseStep 6287557 = 1178917) (by norm_num)
theorem B8383409 : Blo 2207435 8383409 := bstep (se 2 (by rfl) ⟨3143778, by rfl⟩ : syracuseStep 8383409 = 6287557) B6287557
theorem B5588939 : Blo 2207435 5588939 := bstep (se 1 (by rfl) ⟨4191704, by rfl⟩ : syracuseStep 5588939 = 8383409) B8383409
theorem B3725959 : Blo 2207435 3725959 := bstep (se 1 (by rfl) ⟨2794469, by rfl⟩ : syracuseStep 3725959 = 5588939) B5588939
theorem B4967945 : Blo 2207435 4967945 := bstep (se 2 (by rfl) ⟨1862979, by rfl⟩ : syracuseStep 4967945 = 3725959) B3725959
theorem B3311963 : Blo 2207435 3311963 := bstep (se 1 (by rfl) ⟨2483972, by rfl⟩ : syracuseStep 3311963 = 4967945) B4967945
theorem B2207975 : Blo 2207435 2207975 := bstep (se 1 (by rfl) ⟨1655981, by rfl⟩ : syracuseStep 2207975 = 3311963) B3311963
theorem B2483977 : Blo 2207435 2483977 := bbase (se 2 (by rfl) ⟨931491, by rfl⟩ : syracuseStep 2483977 = 1862983) (by norm_num)
theorem B3311969 : Blo 2207435 3311969 := bstep (se 2 (by rfl) ⟨1241988, by rfl⟩ : syracuseStep 3311969 = 2483977) B2483977
theorem B2207979 : Blo 2207435 2207979 := bstep (se 1 (by rfl) ⟨1655984, by rfl⟩ : syracuseStep 2207979 = 3311969) B3311969
theorem B5104453 : Blo 2207435 5104453 := bbase (se 4 (by rfl) ⟨478542, by rfl⟩ : syracuseStep 5104453 = 957085) (by norm_num)
theorem B6805937 : Blo 2207435 6805937 := bstep (se 2 (by rfl) ⟨2552226, by rfl⟩ : syracuseStep 6805937 = 5104453) B5104453
theorem B4537291 : Blo 2207435 4537291 := bstep (se 1 (by rfl) ⟨3402968, by rfl⟩ : syracuseStep 4537291 = 6805937) B6805937
theorem B6049721 : Blo 2207435 6049721 := bstep (se 2 (by rfl) ⟨2268645, by rfl⟩ : syracuseStep 6049721 = 4537291) B4537291
theorem B4033147 : Blo 2207435 4033147 := bstep (se 1 (by rfl) ⟨3024860, by rfl⟩ : syracuseStep 4033147 = 6049721) B6049721
theorem B5377529 : Blo 2207435 5377529 := bstep (se 2 (by rfl) ⟨2016573, by rfl⟩ : syracuseStep 5377529 = 4033147) B4033147
theorem B14340077 : Blo 2207435 14340077 := bstep (se 3 (by rfl) ⟨2688764, by rfl⟩ : syracuseStep 14340077 = 5377529) B5377529
theorem B9560051 : Blo 2207435 9560051 := bstep (se 1 (by rfl) ⟨7170038, by rfl⟩ : syracuseStep 9560051 = 14340077) B14340077
theorem B6373367 : Blo 2207435 6373367 := bstep (se 1 (by rfl) ⟨4780025, by rfl⟩ : syracuseStep 6373367 = 9560051) B9560051
theorem B4248911 : Blo 2207435 4248911 := bstep (se 1 (by rfl) ⟨3186683, by rfl⟩ : syracuseStep 4248911 = 6373367) B6373367
theorem B2832607 : Blo 2207435 2832607 := bstep (se 1 (by rfl) ⟨2124455, by rfl⟩ : syracuseStep 2832607 = 4248911) B4248911
theorem B3776809 : Blo 2207435 3776809 := bstep (se 2 (by rfl) ⟨1416303, by rfl⟩ : syracuseStep 3776809 = 2832607) B2832607
theorem B5035745 : Blo 2207435 5035745 := bstep (se 2 (by rfl) ⟨1888404, by rfl⟩ : syracuseStep 5035745 = 3776809) B3776809
theorem B3357163 : Blo 2207435 3357163 := bstep (se 1 (by rfl) ⟨2517872, by rfl⟩ : syracuseStep 3357163 = 5035745) B5035745
theorem B4476217 : Blo 2207435 4476217 := bstep (se 2 (by rfl) ⟨1678581, by rfl⟩ : syracuseStep 4476217 = 3357163) B3357163
theorem B5968289 : Blo 2207435 5968289 := bstep (se 2 (by rfl) ⟨2238108, by rfl⟩ : syracuseStep 5968289 = 4476217) B4476217
theorem B15915437 : Blo 2207435 15915437 := bstep (se 3 (by rfl) ⟨2984144, by rfl⟩ : syracuseStep 15915437 = 5968289) B5968289
theorem B10610291 : Blo 2207435 10610291 := bstep (se 1 (by rfl) ⟨7957718, by rfl⟩ : syracuseStep 10610291 = 15915437) B15915437
theorem B28294109 : Blo 2207435 28294109 := bstep (se 3 (by rfl) ⟨5305145, by rfl⟩ : syracuseStep 28294109 = 10610291) B10610291
theorem B18862739 : Blo 2207435 18862739 := bstep (se 1 (by rfl) ⟨14147054, by rfl⟩ : syracuseStep 18862739 = 28294109) B28294109
theorem B12575159 : Blo 2207435 12575159 := bstep (se 1 (by rfl) ⟨9431369, by rfl⟩ : syracuseStep 12575159 = 18862739) B18862739
theorem B8383439 : Blo 2207435 8383439 := bstep (se 1 (by rfl) ⟨6287579, by rfl⟩ : syracuseStep 8383439 = 12575159) B12575159
theorem B5588959 : Blo 2207435 5588959 := bstep (se 1 (by rfl) ⟨4191719, by rfl⟩ : syracuseStep 5588959 = 8383439) B8383439
theorem B7451945 : Blo 2207435 7451945 := bstep (se 2 (by rfl) ⟨2794479, by rfl⟩ : syracuseStep 7451945 = 5588959) B5588959
theorem B4967963 : Blo 2207435 4967963 := bstep (se 1 (by rfl) ⟨3725972, by rfl⟩ : syracuseStep 4967963 = 7451945) B7451945
theorem B3311975 : Blo 2207435 3311975 := bstep (se 1 (by rfl) ⟨2483981, by rfl⟩ : syracuseStep 3311975 = 4967963) B4967963
theorem B2207983 : Blo 2207435 2207983 := bstep (se 1 (by rfl) ⟨1655987, by rfl⟩ : syracuseStep 2207983 = 3311975) B3311975
theorem B3311981 : Blo 2207435 3311981 := bbase (se 3 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 3311981 = 1241993) (by norm_num)
theorem B2207987 : Blo 2207435 2207987 := bstep (se 1 (by rfl) ⟨1655990, by rfl⟩ : syracuseStep 2207987 = 3311981) B3311981
theorem B4967981 : Blo 2207435 4967981 := bbase (se 3 (by rfl) ⟨931496, by rfl⟩ : syracuseStep 4967981 = 1862993) (by norm_num)
theorem B3311987 : Blo 2207435 3311987 := bstep (se 1 (by rfl) ⟨2483990, by rfl⟩ : syracuseStep 3311987 = 4967981) B4967981
theorem B2207991 : Blo 2207435 2207991 := bstep (se 1 (by rfl) ⟨1655993, by rfl⟩ : syracuseStep 2207991 = 3311987) B3311987
theorem B9560101 : Blo 2207435 9560101 := bbase (se 4 (by rfl) ⟨896259, by rfl⟩ : syracuseStep 9560101 = 1792519) (by norm_num)
theorem B12746801 : Blo 2207435 12746801 := bstep (se 2 (by rfl) ⟨4780050, by rfl⟩ : syracuseStep 12746801 = 9560101) B9560101
theorem B8497867 : Blo 2207435 8497867 := bstep (se 1 (by rfl) ⟨6373400, by rfl⟩ : syracuseStep 8497867 = 12746801) B12746801
theorem B11330489 : Blo 2207435 11330489 := bstep (se 2 (by rfl) ⟨4248933, by rfl⟩ : syracuseStep 11330489 = 8497867) B8497867
theorem B7553659 : Blo 2207435 7553659 := bstep (se 1 (by rfl) ⟨5665244, by rfl⟩ : syracuseStep 7553659 = 11330489) B11330489
theorem B10071545 : Blo 2207435 10071545 := bstep (se 2 (by rfl) ⟨3776829, by rfl⟩ : syracuseStep 10071545 = 7553659) B7553659
theorem B107429813 : Blo 2207435 107429813 := bstep (se 5 (by rfl) ⟨5035772, by rfl⟩ : syracuseStep 107429813 = 10071545) B10071545
theorem B71619875 : Blo 2207435 71619875 := bstep (se 1 (by rfl) ⟨53714906, by rfl⟩ : syracuseStep 71619875 = 107429813) B107429813
theorem B47746583 : Blo 2207435 47746583 := bstep (se 1 (by rfl) ⟨35809937, by rfl⟩ : syracuseStep 47746583 = 71619875) B71619875
theorem B31831055 : Blo 2207435 31831055 := bstep (se 1 (by rfl) ⟨23873291, by rfl⟩ : syracuseStep 31831055 = 47746583) B47746583
theorem B21220703 : Blo 2207435 21220703 := bstep (se 1 (by rfl) ⟨15915527, by rfl⟩ : syracuseStep 21220703 = 31831055) B31831055
theorem B14147135 : Blo 2207435 14147135 := bstep (se 1 (by rfl) ⟨10610351, by rfl⟩ : syracuseStep 14147135 = 21220703) B21220703
theorem B9431423 : Blo 2207435 9431423 := bstep (se 1 (by rfl) ⟨7073567, by rfl⟩ : syracuseStep 9431423 = 14147135) B14147135
theorem B6287615 : Blo 2207435 6287615 := bstep (se 1 (by rfl) ⟨4715711, by rfl⟩ : syracuseStep 6287615 = 9431423) B9431423
theorem B4191743 : Blo 2207435 4191743 := bstep (se 1 (by rfl) ⟨3143807, by rfl⟩ : syracuseStep 4191743 = 6287615) B6287615
theorem B2794495 : Blo 2207435 2794495 := bstep (se 1 (by rfl) ⟨2095871, by rfl⟩ : syracuseStep 2794495 = 4191743) B4191743
theorem B3725993 : Blo 2207435 3725993 := bstep (se 2 (by rfl) ⟨1397247, by rfl⟩ : syracuseStep 3725993 = 2794495) B2794495
theorem B2483995 : Blo 2207435 2483995 := bstep (se 1 (by rfl) ⟨1862996, by rfl⟩ : syracuseStep 2483995 = 3725993) B3725993
theorem B3311993 : Blo 2207435 3311993 := bstep (se 2 (by rfl) ⟨1241997, by rfl⟩ : syracuseStep 3311993 = 2483995) B2483995
theorem B2207995 : Blo 2207435 2207995 := bstep (se 1 (by rfl) ⟨1655996, by rfl⟩ : syracuseStep 2207995 = 3311993) B3311993
theorem B3536789 : Blo 2207435 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B37725749 : Blo 2207435 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B25150499 : Blo 2207435 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B16766999 : Blo 2207435 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B11177999 : Blo 2207435 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B7451999 : Blo 2207435 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B4967999 : Blo 2207435 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B3311999 : Blo 2207435 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2207999 : Blo 2207435 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B3312005 : Blo 2207435 3312005 := bbase (se 4 (by rfl) ⟨310500, by rfl⟩ : syracuseStep 3312005 = 621001) (by norm_num)
theorem B2208003 : Blo 2207435 2208003 := bstep (se 1 (by rfl) ⟨1656002, by rfl⟩ : syracuseStep 2208003 = 3312005) B3312005
theorem B3726013 : Blo 2207435 3726013 := bbase (se 3 (by rfl) ⟨698627, by rfl⟩ : syracuseStep 3726013 = 1397255) (by norm_num)
theorem B4968017 : Blo 2207435 4968017 := bstep (se 2 (by rfl) ⟨1863006, by rfl⟩ : syracuseStep 4968017 = 3726013) B3726013
theorem B3312011 : Blo 2207435 3312011 := bstep (se 1 (by rfl) ⟨2484008, by rfl⟩ : syracuseStep 3312011 = 4968017) B4968017
theorem B2208007 : Blo 2207435 2208007 := bstep (se 1 (by rfl) ⟨1656005, by rfl⟩ : syracuseStep 2208007 = 3312011) B3312011
theorem B2484013 : Blo 2207435 2484013 := bbase (se 3 (by rfl) ⟨465752, by rfl⟩ : syracuseStep 2484013 = 931505) (by norm_num)
theorem B3312017 : Blo 2207435 3312017 := bstep (se 2 (by rfl) ⟨1242006, by rfl⟩ : syracuseStep 3312017 = 2484013) B2484013
theorem B2208011 : Blo 2207435 2208011 := bstep (se 1 (by rfl) ⟨1656008, by rfl⟩ : syracuseStep 2208011 = 3312017) B3312017
theorem B7452053 : Blo 2207435 7452053 := bbase (se 6 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 7452053 = 349315) (by norm_num)
theorem B4968035 : Blo 2207435 4968035 := bstep (se 1 (by rfl) ⟨3726026, by rfl⟩ : syracuseStep 4968035 = 7452053) B7452053
theorem B3312023 : Blo 2207435 3312023 := bstep (se 1 (by rfl) ⟨2484017, by rfl⟩ : syracuseStep 3312023 = 4968035) B4968035
theorem B2208015 : Blo 2207435 2208015 := bstep (se 1 (by rfl) ⟨1656011, by rfl⟩ : syracuseStep 2208015 = 3312023) B3312023
theorem B3312029 : Blo 2207435 3312029 := bbase (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) (by norm_num)
theorem B2208019 : Blo 2207435 2208019 := bstep (se 1 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 2208019 = 3312029) B3312029
theorem B4968053 : Blo 2207435 4968053 := bbase (se 5 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 4968053 = 465755) (by norm_num)
theorem B3312035 : Blo 2207435 3312035 := bstep (se 1 (by rfl) ⟨2484026, by rfl⟩ : syracuseStep 3312035 = 4968053) B4968053
theorem B2208023 : Blo 2207435 2208023 := bstep (se 1 (by rfl) ⟨1656017, by rfl⟩ : syracuseStep 2208023 = 3312035) B3312035
theorem B7073669 : Blo 2207435 7073669 := bbase (se 4 (by rfl) ⟨663156, by rfl⟩ : syracuseStep 7073669 = 1326313) (by norm_num)
theorem B18863117 : Blo 2207435 18863117 := bstep (se 3 (by rfl) ⟨3536834, by rfl⟩ : syracuseStep 18863117 = 7073669) B7073669
theorem B12575411 : Blo 2207435 12575411 := bstep (se 1 (by rfl) ⟨9431558, by rfl⟩ : syracuseStep 12575411 = 18863117) B18863117
theorem B8383607 : Blo 2207435 8383607 := bstep (se 1 (by rfl) ⟨6287705, by rfl⟩ : syracuseStep 8383607 = 12575411) B12575411
theorem B5589071 : Blo 2207435 5589071 := bstep (se 1 (by rfl) ⟨4191803, by rfl⟩ : syracuseStep 5589071 = 8383607) B8383607
theorem B3726047 : Blo 2207435 3726047 := bstep (se 1 (by rfl) ⟨2794535, by rfl⟩ : syracuseStep 3726047 = 5589071) B5589071
theorem B2484031 : Blo 2207435 2484031 := bstep (se 1 (by rfl) ⟨1863023, by rfl⟩ : syracuseStep 2484031 = 3726047) B3726047
theorem B3312041 : Blo 2207435 3312041 := bstep (se 2 (by rfl) ⟨1242015, by rfl⟩ : syracuseStep 3312041 = 2484031) B2484031
theorem B2208027 : Blo 2207435 2208027 := bstep (se 1 (by rfl) ⟨1656020, by rfl⟩ : syracuseStep 2208027 = 3312041) B3312041
theorem B8383621 : Blo 2207435 8383621 := bbase (se 4 (by rfl) ⟨785964, by rfl⟩ : syracuseStep 8383621 = 1571929) (by norm_num)
theorem B11178161 : Blo 2207435 11178161 := bstep (se 2 (by rfl) ⟨4191810, by rfl⟩ : syracuseStep 11178161 = 8383621) B8383621
theorem B7452107 : Blo 2207435 7452107 := bstep (se 1 (by rfl) ⟨5589080, by rfl⟩ : syracuseStep 7452107 = 11178161) B11178161
theorem B4968071 : Blo 2207435 4968071 := bstep (se 1 (by rfl) ⟨3726053, by rfl⟩ : syracuseStep 4968071 = 7452107) B7452107
theorem B3312047 : Blo 2207435 3312047 := bstep (se 1 (by rfl) ⟨2484035, by rfl⟩ : syracuseStep 3312047 = 4968071) B4968071
theorem B2208031 : Blo 2207435 2208031 := bstep (se 1 (by rfl) ⟨1656023, by rfl⟩ : syracuseStep 2208031 = 3312047) B3312047
theorem B3312053 : Blo 2207435 3312053 := bbase (se 5 (by rfl) ⟨155252, by rfl⟩ : syracuseStep 3312053 = 310505) (by norm_num)
theorem B2208035 : Blo 2207435 2208035 := bstep (se 1 (by rfl) ⟨1656026, by rfl⟩ : syracuseStep 2208035 = 3312053) B3312053
theorem B5589101 : Blo 2207435 5589101 := bbase (se 3 (by rfl) ⟨1047956, by rfl⟩ : syracuseStep 5589101 = 2095913) (by norm_num)
theorem B3726067 : Blo 2207435 3726067 := bstep (se 1 (by rfl) ⟨2794550, by rfl⟩ : syracuseStep 3726067 = 5589101) B5589101
theorem B4968089 : Blo 2207435 4968089 := bstep (se 2 (by rfl) ⟨1863033, by rfl⟩ : syracuseStep 4968089 = 3726067) B3726067
theorem B3312059 : Blo 2207435 3312059 := bstep (se 1 (by rfl) ⟨2484044, by rfl⟩ : syracuseStep 3312059 = 4968089) B4968089
theorem B2208039 : Blo 2207435 2208039 := bstep (se 1 (by rfl) ⟨1656029, by rfl⟩ : syracuseStep 2208039 = 3312059) B3312059
theorem B2484049 : Blo 2207435 2484049 := bbase (se 2 (by rfl) ⟨931518, by rfl⟩ : syracuseStep 2484049 = 1863037) (by norm_num)
theorem B3312065 : Blo 2207435 3312065 := bstep (se 2 (by rfl) ⟨1242024, by rfl⟩ : syracuseStep 3312065 = 2484049) B2484049
theorem B2208043 : Blo 2207435 2208043 := bstep (se 1 (by rfl) ⟨1656032, by rfl⟩ : syracuseStep 2208043 = 3312065) B3312065
theorem B5305301 : Blo 2207435 5305301 := bbase (se 7 (by rfl) ⟨62171, by rfl⟩ : syracuseStep 5305301 = 124343) (by norm_num)
theorem B3536867 : Blo 2207435 3536867 := bstep (se 1 (by rfl) ⟨2652650, by rfl⟩ : syracuseStep 3536867 = 5305301) B5305301
theorem B2357911 : Blo 2207435 2357911 := bstep (se 1 (by rfl) ⟨1768433, by rfl⟩ : syracuseStep 2357911 = 3536867) B3536867
theorem B3143881 : Blo 2207435 3143881 := bstep (se 2 (by rfl) ⟨1178955, by rfl⟩ : syracuseStep 3143881 = 2357911) B2357911
theorem B4191841 : Blo 2207435 4191841 := bstep (se 2 (by rfl) ⟨1571940, by rfl⟩ : syracuseStep 4191841 = 3143881) B3143881
theorem B5589121 : Blo 2207435 5589121 := bstep (se 2 (by rfl) ⟨2095920, by rfl⟩ : syracuseStep 5589121 = 4191841) B4191841
theorem B7452161 : Blo 2207435 7452161 := bstep (se 2 (by rfl) ⟨2794560, by rfl⟩ : syracuseStep 7452161 = 5589121) B5589121
theorem B4968107 : Blo 2207435 4968107 := bstep (se 1 (by rfl) ⟨3726080, by rfl⟩ : syracuseStep 4968107 = 7452161) B7452161
theorem B3312071 : Blo 2207435 3312071 := bstep (se 1 (by rfl) ⟨2484053, by rfl⟩ : syracuseStep 3312071 = 4968107) B4968107
theorem B2208047 : Blo 2207435 2208047 := bstep (se 1 (by rfl) ⟨1656035, by rfl⟩ : syracuseStep 2208047 = 3312071) B3312071
theorem B3312077 : Blo 2207435 3312077 := bbase (se 3 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 3312077 = 1242029) (by norm_num)
theorem B2208051 : Blo 2207435 2208051 := bstep (se 1 (by rfl) ⟨1656038, by rfl⟩ : syracuseStep 2208051 = 3312077) B3312077
theorem B4968125 : Blo 2207435 4968125 := bbase (se 3 (by rfl) ⟨931523, by rfl⟩ : syracuseStep 4968125 = 1863047) (by norm_num)
theorem B3312083 : Blo 2207435 3312083 := bstep (se 1 (by rfl) ⟨2484062, by rfl⟩ : syracuseStep 3312083 = 4968125) B4968125
theorem B2208055 : Blo 2207435 2208055 := bstep (se 1 (by rfl) ⟨1656041, by rfl⟩ : syracuseStep 2208055 = 3312083) B3312083
theorem B3726101 : Blo 2207435 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B2484067 : Blo 2207435 2484067 := bstep (se 1 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 2484067 = 3726101) B3726101
theorem B3312089 : Blo 2207435 3312089 := bstep (se 2 (by rfl) ⟨1242033, by rfl⟩ : syracuseStep 3312089 = 2484067) B2484067
theorem B2208059 : Blo 2207435 2208059 := bstep (se 1 (by rfl) ⟨1656044, by rfl⟩ : syracuseStep 2208059 = 3312089) B3312089
theorem B4537453 : Blo 2207435 4537453 := bbase (se 3 (by rfl) ⟨850772, by rfl⟩ : syracuseStep 4537453 = 1701545) (by norm_num)
theorem B6049937 : Blo 2207435 6049937 := bstep (se 2 (by rfl) ⟨2268726, by rfl⟩ : syracuseStep 6049937 = 4537453) B4537453
theorem B16133165 : Blo 2207435 16133165 := bstep (se 3 (by rfl) ⟨3024968, by rfl⟩ : syracuseStep 16133165 = 6049937) B6049937
theorem B10755443 : Blo 2207435 10755443 := bstep (se 1 (by rfl) ⟨8066582, by rfl⟩ : syracuseStep 10755443 = 16133165) B16133165
theorem B7170295 : Blo 2207435 7170295 := bstep (se 1 (by rfl) ⟨5377721, by rfl⟩ : syracuseStep 7170295 = 10755443) B10755443
theorem B9560393 : Blo 2207435 9560393 := bstep (se 2 (by rfl) ⟨3585147, by rfl⟩ : syracuseStep 9560393 = 7170295) B7170295
theorem B6373595 : Blo 2207435 6373595 := bstep (se 1 (by rfl) ⟨4780196, by rfl⟩ : syracuseStep 6373595 = 9560393) B9560393
theorem B4249063 : Blo 2207435 4249063 := bstep (se 1 (by rfl) ⟨3186797, by rfl⟩ : syracuseStep 4249063 = 6373595) B6373595
theorem B22661669 : Blo 2207435 22661669 := bstep (se 4 (by rfl) ⟨2124531, by rfl⟩ : syracuseStep 22661669 = 4249063) B4249063
theorem B15107779 : Blo 2207435 15107779 := bstep (se 1 (by rfl) ⟨11330834, by rfl⟩ : syracuseStep 15107779 = 22661669) B22661669
theorem B80574821 : Blo 2207435 80574821 := bstep (se 4 (by rfl) ⟨7553889, by rfl⟩ : syracuseStep 80574821 = 15107779) B15107779
theorem B53716547 : Blo 2207435 53716547 := bstep (se 1 (by rfl) ⟨40287410, by rfl⟩ : syracuseStep 53716547 = 80574821) B80574821
theorem B35811031 : Blo 2207435 35811031 := bstep (se 1 (by rfl) ⟨26858273, by rfl⟩ : syracuseStep 35811031 = 53716547) B53716547
theorem B47748041 : Blo 2207435 47748041 := bstep (se 2 (by rfl) ⟨17905515, by rfl⟩ : syracuseStep 47748041 = 35811031) B35811031
theorem B31832027 : Blo 2207435 31832027 := bstep (se 1 (by rfl) ⟨23874020, by rfl⟩ : syracuseStep 31832027 = 47748041) B47748041
theorem B21221351 : Blo 2207435 21221351 := bstep (se 1 (by rfl) ⟨15916013, by rfl⟩ : syracuseStep 21221351 = 31832027) B31832027
theorem B14147567 : Blo 2207435 14147567 := bstep (se 1 (by rfl) ⟨10610675, by rfl⟩ : syracuseStep 14147567 = 21221351) B21221351
theorem B9431711 : Blo 2207435 9431711 := bstep (se 1 (by rfl) ⟨7073783, by rfl⟩ : syracuseStep 9431711 = 14147567) B14147567
theorem B6287807 : Blo 2207435 6287807 := bstep (se 1 (by rfl) ⟨4715855, by rfl⟩ : syracuseStep 6287807 = 9431711) B9431711
theorem B16767485 : Blo 2207435 16767485 := bstep (se 3 (by rfl) ⟨3143903, by rfl⟩ : syracuseStep 16767485 = 6287807) B6287807
theorem B11178323 : Blo 2207435 11178323 := bstep (se 1 (by rfl) ⟨8383742, by rfl⟩ : syracuseStep 11178323 = 16767485) B16767485
theorem B7452215 : Blo 2207435 7452215 := bstep (se 1 (by rfl) ⟨5589161, by rfl⟩ : syracuseStep 7452215 = 11178323) B11178323
theorem B4968143 : Blo 2207435 4968143 := bstep (se 1 (by rfl) ⟨3726107, by rfl⟩ : syracuseStep 4968143 = 7452215) B7452215
theorem B3312095 : Blo 2207435 3312095 := bstep (se 1 (by rfl) ⟨2484071, by rfl⟩ : syracuseStep 3312095 = 4968143) B4968143
theorem B2208063 : Blo 2207435 2208063 := bstep (se 1 (by rfl) ⟨1656047, by rfl⟩ : syracuseStep 2208063 = 3312095) B3312095
theorem B3312101 : Blo 2207435 3312101 := bbase (se 4 (by rfl) ⟨310509, by rfl⟩ : syracuseStep 3312101 = 621019) (by norm_num)
theorem B2208067 : Blo 2207435 2208067 := bstep (se 1 (by rfl) ⟨1656050, by rfl⟩ : syracuseStep 2208067 = 3312101) B3312101
theorem B4476397 : Blo 2207435 4476397 := bbase (se 3 (by rfl) ⟨839324, by rfl⟩ : syracuseStep 4476397 = 1678649) (by norm_num)
theorem B5968529 : Blo 2207435 5968529 := bstep (se 2 (by rfl) ⟨2238198, by rfl⟩ : syracuseStep 5968529 = 4476397) B4476397
theorem B3979019 : Blo 2207435 3979019 := bstep (se 1 (by rfl) ⟨2984264, by rfl⟩ : syracuseStep 3979019 = 5968529) B5968529
theorem B2652679 : Blo 2207435 2652679 := bstep (se 1 (by rfl) ⟨1989509, by rfl⟩ : syracuseStep 2652679 = 3979019) B3979019
theorem B14147621 : Blo 2207435 14147621 := bstep (se 4 (by rfl) ⟨1326339, by rfl⟩ : syracuseStep 14147621 = 2652679) B2652679
theorem B9431747 : Blo 2207435 9431747 := bstep (se 1 (by rfl) ⟨7073810, by rfl⟩ : syracuseStep 9431747 = 14147621) B14147621
theorem B6287831 : Blo 2207435 6287831 := bstep (se 1 (by rfl) ⟨4715873, by rfl⟩ : syracuseStep 6287831 = 9431747) B9431747
theorem B4191887 : Blo 2207435 4191887 := bstep (se 1 (by rfl) ⟨3143915, by rfl⟩ : syracuseStep 4191887 = 6287831) B6287831
theorem B2794591 : Blo 2207435 2794591 := bstep (se 1 (by rfl) ⟨2095943, by rfl⟩ : syracuseStep 2794591 = 4191887) B4191887
theorem B3726121 : Blo 2207435 3726121 := bstep (se 2 (by rfl) ⟨1397295, by rfl⟩ : syracuseStep 3726121 = 2794591) B2794591
theorem B4968161 : Blo 2207435 4968161 := bstep (se 2 (by rfl) ⟨1863060, by rfl⟩ : syracuseStep 4968161 = 3726121) B3726121
theorem B3312107 : Blo 2207435 3312107 := bstep (se 1 (by rfl) ⟨2484080, by rfl⟩ : syracuseStep 3312107 = 4968161) B4968161
theorem B2208071 : Blo 2207435 2208071 := bstep (se 1 (by rfl) ⟨1656053, by rfl⟩ : syracuseStep 2208071 = 3312107) B3312107
theorem B2484085 : Blo 2207435 2484085 := bbase (se 5 (by rfl) ⟨116441, by rfl⟩ : syracuseStep 2484085 = 232883) (by norm_num)
theorem B3312113 : Blo 2207435 3312113 := bstep (se 2 (by rfl) ⟨1242042, by rfl⟩ : syracuseStep 3312113 = 2484085) B2484085
theorem B2208075 : Blo 2207435 2208075 := bstep (se 1 (by rfl) ⟨1656056, by rfl⟩ : syracuseStep 2208075 = 3312113) B3312113
theorem B2794601 : Blo 2207435 2794601 := bbase (se 2 (by rfl) ⟨1047975, by rfl⟩ : syracuseStep 2794601 = 2095951) (by norm_num)
theorem B7452269 : Blo 2207435 7452269 := bstep (se 3 (by rfl) ⟨1397300, by rfl⟩ : syracuseStep 7452269 = 2794601) B2794601
theorem B4968179 : Blo 2207435 4968179 := bstep (se 1 (by rfl) ⟨3726134, by rfl⟩ : syracuseStep 4968179 = 7452269) B7452269
theorem B3312119 : Blo 2207435 3312119 := bstep (se 1 (by rfl) ⟨2484089, by rfl⟩ : syracuseStep 3312119 = 4968179) B4968179
theorem B2208079 : Blo 2207435 2208079 := bstep (se 1 (by rfl) ⟨1656059, by rfl⟩ : syracuseStep 2208079 = 3312119) B3312119
theorem B3312125 : Blo 2207435 3312125 := bbase (se 3 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 3312125 = 1242047) (by norm_num)
theorem B2208083 : Blo 2207435 2208083 := bstep (se 1 (by rfl) ⟨1656062, by rfl⟩ : syracuseStep 2208083 = 3312125) B3312125
theorem B4968197 : Blo 2207435 4968197 := bbase (se 4 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 4968197 = 931537) (by norm_num)
theorem B3312131 : Blo 2207435 3312131 := bstep (se 1 (by rfl) ⟨2484098, by rfl⟩ : syracuseStep 3312131 = 4968197) B4968197
theorem B2208087 : Blo 2207435 2208087 := bstep (se 1 (by rfl) ⟨1656065, by rfl⟩ : syracuseStep 2208087 = 3312131) B3312131
theorem B4191925 : Blo 2207435 4191925 := bbase (se 5 (by rfl) ⟨196496, by rfl⟩ : syracuseStep 4191925 = 392993) (by norm_num)
theorem B5589233 : Blo 2207435 5589233 := bstep (se 2 (by rfl) ⟨2095962, by rfl⟩ : syracuseStep 5589233 = 4191925) B4191925
theorem B3726155 : Blo 2207435 3726155 := bstep (se 1 (by rfl) ⟨2794616, by rfl⟩ : syracuseStep 3726155 = 5589233) B5589233
theorem B2484103 : Blo 2207435 2484103 := bstep (se 1 (by rfl) ⟨1863077, by rfl⟩ : syracuseStep 2484103 = 3726155) B3726155
theorem B3312137 : Blo 2207435 3312137 := bstep (se 2 (by rfl) ⟨1242051, by rfl⟩ : syracuseStep 3312137 = 2484103) B2484103
theorem B2208091 : Blo 2207435 2208091 := bstep (se 1 (by rfl) ⟨1656068, by rfl⟩ : syracuseStep 2208091 = 3312137) B3312137
theorem B11178485 : Blo 2207435 11178485 := bbase (se 5 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 11178485 = 1047983) (by norm_num)
theorem B7452323 : Blo 2207435 7452323 := bstep (se 1 (by rfl) ⟨5589242, by rfl⟩ : syracuseStep 7452323 = 11178485) B11178485
theorem B4968215 : Blo 2207435 4968215 := bstep (se 1 (by rfl) ⟨3726161, by rfl⟩ : syracuseStep 4968215 = 7452323) B7452323
theorem B3312143 : Blo 2207435 3312143 := bstep (se 1 (by rfl) ⟨2484107, by rfl⟩ : syracuseStep 3312143 = 4968215) B4968215
theorem B2208095 : Blo 2207435 2208095 := bstep (se 1 (by rfl) ⟨1656071, by rfl⟩ : syracuseStep 2208095 = 3312143) B3312143
theorem B3312149 : Blo 2207435 3312149 := bbase (se 6 (by rfl) ⟨77628, by rfl⟩ : syracuseStep 3312149 = 155257) (by norm_num)
theorem B2208099 : Blo 2207435 2208099 := bstep (se 1 (by rfl) ⟨1656074, by rfl⟩ : syracuseStep 2208099 = 3312149) B3312149
theorem B18863765 : Blo 2207435 18863765 := bbase (se 6 (by rfl) ⟨442119, by rfl⟩ : syracuseStep 18863765 = 884239) (by norm_num)
theorem B12575843 : Blo 2207435 12575843 := bstep (se 1 (by rfl) ⟨9431882, by rfl⟩ : syracuseStep 12575843 = 18863765) B18863765
theorem B8383895 : Blo 2207435 8383895 := bstep (se 1 (by rfl) ⟨6287921, by rfl⟩ : syracuseStep 8383895 = 12575843) B12575843
theorem B5589263 : Blo 2207435 5589263 := bstep (se 1 (by rfl) ⟨4191947, by rfl⟩ : syracuseStep 5589263 = 8383895) B8383895
theorem B3726175 : Blo 2207435 3726175 := bstep (se 1 (by rfl) ⟨2794631, by rfl⟩ : syracuseStep 3726175 = 5589263) B5589263
theorem B4968233 : Blo 2207435 4968233 := bstep (se 2 (by rfl) ⟨1863087, by rfl⟩ : syracuseStep 4968233 = 3726175) B3726175
theorem B3312155 : Blo 2207435 3312155 := bstep (se 1 (by rfl) ⟨2484116, by rfl⟩ : syracuseStep 3312155 = 4968233) B4968233
theorem B2208103 : Blo 2207435 2208103 := bstep (se 1 (by rfl) ⟨1656077, by rfl⟩ : syracuseStep 2208103 = 3312155) B3312155
theorem B2484121 : Blo 2207435 2484121 := bbase (se 2 (by rfl) ⟨931545, by rfl⟩ : syracuseStep 2484121 = 1863091) (by norm_num)
theorem B3312161 : Blo 2207435 3312161 := bstep (se 2 (by rfl) ⟨1242060, by rfl⟩ : syracuseStep 3312161 = 2484121) B2484121
theorem B2208107 : Blo 2207435 2208107 := bstep (se 1 (by rfl) ⟨1656080, by rfl⟩ : syracuseStep 2208107 = 3312161) B3312161
theorem B8383925 : Blo 2207435 8383925 := bbase (se 5 (by rfl) ⟨392996, by rfl⟩ : syracuseStep 8383925 = 785993) (by norm_num)
theorem B5589283 : Blo 2207435 5589283 := bstep (se 1 (by rfl) ⟨4191962, by rfl⟩ : syracuseStep 5589283 = 8383925) B8383925
theorem B7452377 : Blo 2207435 7452377 := bstep (se 2 (by rfl) ⟨2794641, by rfl⟩ : syracuseStep 7452377 = 5589283) B5589283
theorem B4968251 : Blo 2207435 4968251 := bstep (se 1 (by rfl) ⟨3726188, by rfl⟩ : syracuseStep 4968251 = 7452377) B7452377
theorem B3312167 : Blo 2207435 3312167 := bstep (se 1 (by rfl) ⟨2484125, by rfl⟩ : syracuseStep 3312167 = 4968251) B4968251
theorem B2208111 : Blo 2207435 2208111 := bstep (se 1 (by rfl) ⟨1656083, by rfl⟩ : syracuseStep 2208111 = 3312167) B3312167
theorem B3312173 : Blo 2207435 3312173 := bbase (se 3 (by rfl) ⟨621032, by rfl⟩ : syracuseStep 3312173 = 1242065) (by norm_num)
theorem B2208115 : Blo 2207435 2208115 := bstep (se 1 (by rfl) ⟨1656086, by rfl⟩ : syracuseStep 2208115 = 3312173) B3312173
theorem B4968269 : Blo 2207435 4968269 := bbase (se 3 (by rfl) ⟨931550, by rfl⟩ : syracuseStep 4968269 = 1863101) (by norm_num)
theorem B3312179 : Blo 2207435 3312179 := bstep (se 1 (by rfl) ⟨2484134, by rfl⟩ : syracuseStep 3312179 = 4968269) B4968269
theorem B2208119 : Blo 2207435 2208119 := bstep (se 1 (by rfl) ⟨1656089, by rfl⟩ : syracuseStep 2208119 = 3312179) B3312179
theorem B2794657 : Blo 2207435 2794657 := bbase (se 2 (by rfl) ⟨1047996, by rfl⟩ : syracuseStep 2794657 = 2095993) (by norm_num)
theorem B3726209 : Blo 2207435 3726209 := bstep (se 2 (by rfl) ⟨1397328, by rfl⟩ : syracuseStep 3726209 = 2794657) B2794657
theorem B2484139 : Blo 2207435 2484139 := bstep (se 1 (by rfl) ⟨1863104, by rfl⟩ : syracuseStep 2484139 = 3726209) B3726209
theorem B3312185 : Blo 2207435 3312185 := bstep (se 2 (by rfl) ⟨1242069, by rfl⟩ : syracuseStep 3312185 = 2484139) B2484139
theorem B2208123 : Blo 2207435 2208123 := bstep (se 1 (by rfl) ⟨1656092, by rfl⟩ : syracuseStep 2208123 = 3312185) B3312185
theorem B25151957 : Blo 2207435 25151957 := bbase (se 7 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 25151957 = 589499) (by norm_num)
theorem B16767971 : Blo 2207435 16767971 := bstep (se 1 (by rfl) ⟨12575978, by rfl⟩ : syracuseStep 16767971 = 25151957) B25151957
theorem B11178647 : Blo 2207435 11178647 := bstep (se 1 (by rfl) ⟨8383985, by rfl⟩ : syracuseStep 11178647 = 16767971) B16767971
theorem B7452431 : Blo 2207435 7452431 := bstep (se 1 (by rfl) ⟨5589323, by rfl⟩ : syracuseStep 7452431 = 11178647) B11178647
theorem B4968287 : Blo 2207435 4968287 := bstep (se 1 (by rfl) ⟨3726215, by rfl⟩ : syracuseStep 4968287 = 7452431) B7452431
theorem B3312191 : Blo 2207435 3312191 := bstep (se 1 (by rfl) ⟨2484143, by rfl⟩ : syracuseStep 3312191 = 4968287) B4968287
theorem B2208127 : Blo 2207435 2208127 := bstep (se 1 (by rfl) ⟨1656095, by rfl⟩ : syracuseStep 2208127 = 3312191) B3312191
theorem B3312197 : Blo 2207435 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B2208131 : Blo 2207435 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B3726229 : Blo 2207435 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B4968305 : Blo 2207435 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B3312203 : Blo 2207435 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B2208135 : Blo 2207435 2208135 := bstep (se 1 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 2208135 = 3312203) B3312203
theorem B2484157 : Blo 2207435 2484157 := bbase (se 3 (by rfl) ⟨465779, by rfl⟩ : syracuseStep 2484157 = 931559) (by norm_num)
theorem B3312209 : Blo 2207435 3312209 := bstep (se 2 (by rfl) ⟨1242078, by rfl⟩ : syracuseStep 3312209 = 2484157) B2484157
theorem B2208139 : Blo 2207435 2208139 := bstep (se 1 (by rfl) ⟨1656104, by rfl⟩ : syracuseStep 2208139 = 3312209) B3312209
theorem B7452485 : Blo 2207435 7452485 := bbase (se 4 (by rfl) ⟨698670, by rfl⟩ : syracuseStep 7452485 = 1397341) (by norm_num)
theorem B4968323 : Blo 2207435 4968323 := bstep (se 1 (by rfl) ⟨3726242, by rfl⟩ : syracuseStep 4968323 = 7452485) B7452485
theorem B3312215 : Blo 2207435 3312215 := bstep (se 1 (by rfl) ⟨2484161, by rfl⟩ : syracuseStep 3312215 = 4968323) B4968323
theorem B2208143 : Blo 2207435 2208143 := bstep (se 1 (by rfl) ⟨1656107, by rfl⟩ : syracuseStep 2208143 = 3312215) B3312215
theorem B3312221 : Blo 2207435 3312221 := bbase (se 3 (by rfl) ⟨621041, by rfl⟩ : syracuseStep 3312221 = 1242083) (by norm_num)
theorem B2208147 : Blo 2207435 2208147 := bstep (se 1 (by rfl) ⟨1656110, by rfl⟩ : syracuseStep 2208147 = 3312221) B3312221
theorem B4968341 : Blo 2207435 4968341 := bbase (se 6 (by rfl) ⟨116445, by rfl⟩ : syracuseStep 4968341 = 232891) (by norm_num)
theorem B3312227 : Blo 2207435 3312227 := bstep (se 1 (by rfl) ⟨2484170, by rfl⟩ : syracuseStep 3312227 = 4968341) B4968341
theorem B2208151 : Blo 2207435 2208151 := bstep (se 1 (by rfl) ⟨1656113, by rfl⟩ : syracuseStep 2208151 = 3312227) B3312227
theorem B4716053 : Blo 2207435 4716053 := bbase (se 6 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 4716053 = 221065) (by norm_num)
theorem B3144035 : Blo 2207435 3144035 := bstep (se 1 (by rfl) ⟨2358026, by rfl⟩ : syracuseStep 3144035 = 4716053) B4716053
theorem B8384093 : Blo 2207435 8384093 := bstep (se 3 (by rfl) ⟨1572017, by rfl⟩ : syracuseStep 8384093 = 3144035) B3144035
theorem B5589395 : Blo 2207435 5589395 := bstep (se 1 (by rfl) ⟨4192046, by rfl⟩ : syracuseStep 5589395 = 8384093) B8384093
theorem B3726263 : Blo 2207435 3726263 := bstep (se 1 (by rfl) ⟨2794697, by rfl⟩ : syracuseStep 3726263 = 5589395) B5589395
theorem B2484175 : Blo 2207435 2484175 := bstep (se 1 (by rfl) ⟨1863131, by rfl⟩ : syracuseStep 2484175 = 3726263) B3726263
theorem B3312233 : Blo 2207435 3312233 := bstep (se 2 (by rfl) ⟨1242087, by rfl⟩ : syracuseStep 3312233 = 2484175) B2484175
theorem B2208155 : Blo 2207435 2208155 := bstep (se 1 (by rfl) ⟨1656116, by rfl⟩ : syracuseStep 2208155 = 3312233) B3312233
theorem B2832833 : Blo 2207435 2832833 := bbase (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) (by norm_num)
theorem B7554221 : Blo 2207435 7554221 := bstep (se 3 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 7554221 = 2832833) B2832833
theorem B5036147 : Blo 2207435 5036147 := bstep (se 1 (by rfl) ⟨3777110, by rfl⟩ : syracuseStep 5036147 = 7554221) B7554221
theorem B3357431 : Blo 2207435 3357431 := bstep (se 1 (by rfl) ⟨2518073, by rfl⟩ : syracuseStep 3357431 = 5036147) B5036147
theorem B2238287 : Blo 2207435 2238287 := bstep (se 1 (by rfl) ⟨1678715, by rfl⟩ : syracuseStep 2238287 = 3357431) B3357431
theorem B5968765 : Blo 2207435 5968765 := bstep (se 3 (by rfl) ⟨1119143, by rfl⟩ : syracuseStep 5968765 = 2238287) B2238287
theorem B7958353 : Blo 2207435 7958353 := bstep (se 2 (by rfl) ⟨2984382, by rfl⟩ : syracuseStep 7958353 = 5968765) B5968765
theorem B10611137 : Blo 2207435 10611137 := bstep (se 2 (by rfl) ⟨3979176, by rfl⟩ : syracuseStep 10611137 = 7958353) B7958353
theorem B7074091 : Blo 2207435 7074091 := bstep (se 1 (by rfl) ⟨5305568, by rfl⟩ : syracuseStep 7074091 = 10611137) B10611137
theorem B9432121 : Blo 2207435 9432121 := bstep (se 2 (by rfl) ⟨3537045, by rfl⟩ : syracuseStep 9432121 = 7074091) B7074091
theorem B12576161 : Blo 2207435 12576161 := bstep (se 2 (by rfl) ⟨4716060, by rfl⟩ : syracuseStep 12576161 = 9432121) B9432121
theorem B8384107 : Blo 2207435 8384107 := bstep (se 1 (by rfl) ⟨6288080, by rfl⟩ : syracuseStep 8384107 = 12576161) B12576161
theorem B11178809 : Blo 2207435 11178809 := bstep (se 2 (by rfl) ⟨4192053, by rfl⟩ : syracuseStep 11178809 = 8384107) B8384107
theorem B7452539 : Blo 2207435 7452539 := bstep (se 1 (by rfl) ⟨5589404, by rfl⟩ : syracuseStep 7452539 = 11178809) B11178809
theorem B4968359 : Blo 2207435 4968359 := bstep (se 1 (by rfl) ⟨3726269, by rfl⟩ : syracuseStep 4968359 = 7452539) B7452539
theorem B3312239 : Blo 2207435 3312239 := bstep (se 1 (by rfl) ⟨2484179, by rfl⟩ : syracuseStep 3312239 = 4968359) B4968359
theorem B2208159 : Blo 2207435 2208159 := bstep (se 1 (by rfl) ⟨1656119, by rfl⟩ : syracuseStep 2208159 = 3312239) B3312239
theorem B3312245 : Blo 2207435 3312245 := bbase (se 5 (by rfl) ⟨155261, by rfl⟩ : syracuseStep 3312245 = 310523) (by norm_num)
theorem B2208163 : Blo 2207435 2208163 := bstep (se 1 (by rfl) ⟨1656122, by rfl⟩ : syracuseStep 2208163 = 3312245) B3312245
theorem B4192069 : Blo 2207435 4192069 := bbase (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) (by norm_num)
theorem B5589425 : Blo 2207435 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B3726283 : Blo 2207435 3726283 := bstep (se 1 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 3726283 = 5589425) B5589425
theorem B4968377 : Blo 2207435 4968377 := bstep (se 2 (by rfl) ⟨1863141, by rfl⟩ : syracuseStep 4968377 = 3726283) B3726283
theorem B3312251 : Blo 2207435 3312251 := bstep (se 1 (by rfl) ⟨2484188, by rfl⟩ : syracuseStep 3312251 = 4968377) B4968377
theorem B2208167 : Blo 2207435 2208167 := bstep (se 1 (by rfl) ⟨1656125, by rfl⟩ : syracuseStep 2208167 = 3312251) B3312251
theorem B2484193 : Blo 2207435 2484193 := bbase (se 2 (by rfl) ⟨931572, by rfl⟩ : syracuseStep 2484193 = 1863145) (by norm_num)
theorem B3312257 : Blo 2207435 3312257 := bstep (se 2 (by rfl) ⟨1242096, by rfl⟩ : syracuseStep 3312257 = 2484193) B2484193
theorem B2208171 : Blo 2207435 2208171 := bstep (se 1 (by rfl) ⟨1656128, by rfl⟩ : syracuseStep 2208171 = 3312257) B3312257
theorem B5589445 : Blo 2207435 5589445 := bbase (se 4 (by rfl) ⟨524010, by rfl⟩ : syracuseStep 5589445 = 1048021) (by norm_num)
theorem B7452593 : Blo 2207435 7452593 := bstep (se 2 (by rfl) ⟨2794722, by rfl⟩ : syracuseStep 7452593 = 5589445) B5589445
theorem B4968395 : Blo 2207435 4968395 := bstep (se 1 (by rfl) ⟨3726296, by rfl⟩ : syracuseStep 4968395 = 7452593) B7452593
theorem B3312263 : Blo 2207435 3312263 := bstep (se 1 (by rfl) ⟨2484197, by rfl⟩ : syracuseStep 3312263 = 4968395) B4968395
theorem B2208175 : Blo 2207435 2208175 := bstep (se 1 (by rfl) ⟨1656131, by rfl⟩ : syracuseStep 2208175 = 3312263) B3312263
theorem B3312269 : Blo 2207435 3312269 := bbase (se 3 (by rfl) ⟨621050, by rfl⟩ : syracuseStep 3312269 = 1242101) (by norm_num)
theorem B2208179 : Blo 2207435 2208179 := bstep (se 1 (by rfl) ⟨1656134, by rfl⟩ : syracuseStep 2208179 = 3312269) B3312269
theorem B4968413 : Blo 2207435 4968413 := bbase (se 3 (by rfl) ⟨931577, by rfl⟩ : syracuseStep 4968413 = 1863155) (by norm_num)
theorem B3312275 : Blo 2207435 3312275 := bstep (se 1 (by rfl) ⟨2484206, by rfl⟩ : syracuseStep 3312275 = 4968413) B4968413
theorem B2208183 : Blo 2207435 2208183 := bstep (se 1 (by rfl) ⟨1656137, by rfl⟩ : syracuseStep 2208183 = 3312275) B3312275
theorem B3726317 : Blo 2207435 3726317 := bbase (se 3 (by rfl) ⟨698684, by rfl⟩ : syracuseStep 3726317 = 1397369) (by norm_num)
theorem B2484211 : Blo 2207435 2484211 := bstep (se 1 (by rfl) ⟨1863158, by rfl⟩ : syracuseStep 2484211 = 3726317) B3726317
theorem B3312281 : Blo 2207435 3312281 := bstep (se 2 (by rfl) ⟨1242105, by rfl⟩ : syracuseStep 3312281 = 2484211) B2484211
theorem B2208187 : Blo 2207435 2208187 := bstep (se 1 (by rfl) ⟨1656140, by rfl⟩ : syracuseStep 2208187 = 3312281) B3312281
theorem B5305645 : Blo 2207435 5305645 := bbase (se 3 (by rfl) ⟨994808, by rfl⟩ : syracuseStep 5305645 = 1989617) (by norm_num)
theorem B28296773 : Blo 2207435 28296773 := bstep (se 4 (by rfl) ⟨2652822, by rfl⟩ : syracuseStep 28296773 = 5305645) B5305645
theorem B18864515 : Blo 2207435 18864515 := bstep (se 1 (by rfl) ⟨14148386, by rfl⟩ : syracuseStep 18864515 = 28296773) B28296773
theorem B12576343 : Blo 2207435 12576343 := bstep (se 1 (by rfl) ⟨9432257, by rfl⟩ : syracuseStep 12576343 = 18864515) B18864515
theorem B16768457 : Blo 2207435 16768457 := bstep (se 2 (by rfl) ⟨6288171, by rfl⟩ : syracuseStep 16768457 = 12576343) B12576343
theorem B11178971 : Blo 2207435 11178971 := bstep (se 1 (by rfl) ⟨8384228, by rfl⟩ : syracuseStep 11178971 = 16768457) B16768457
theorem B7452647 : Blo 2207435 7452647 := bstep (se 1 (by rfl) ⟨5589485, by rfl⟩ : syracuseStep 7452647 = 11178971) B11178971
theorem B4968431 : Blo 2207435 4968431 := bstep (se 1 (by rfl) ⟨3726323, by rfl⟩ : syracuseStep 4968431 = 7452647) B7452647
theorem B3312287 : Blo 2207435 3312287 := bstep (se 1 (by rfl) ⟨2484215, by rfl⟩ : syracuseStep 3312287 = 4968431) B4968431
theorem B2208191 : Blo 2207435 2208191 := bstep (se 1 (by rfl) ⟨1656143, by rfl⟩ : syracuseStep 2208191 = 3312287) B3312287
theorem B3312293 : Blo 2207435 3312293 := bbase (se 4 (by rfl) ⟨310527, by rfl⟩ : syracuseStep 3312293 = 621055) (by norm_num)
theorem B2208195 : Blo 2207435 2208195 := bstep (se 1 (by rfl) ⟨1656146, by rfl⟩ : syracuseStep 2208195 = 3312293) B3312293
theorem B2794753 : Blo 2207435 2794753 := bbase (se 2 (by rfl) ⟨1048032, by rfl⟩ : syracuseStep 2794753 = 2096065) (by norm_num)
theorem B3726337 : Blo 2207435 3726337 := bstep (se 2 (by rfl) ⟨1397376, by rfl⟩ : syracuseStep 3726337 = 2794753) B2794753
theorem B4968449 : Blo 2207435 4968449 := bstep (se 2 (by rfl) ⟨1863168, by rfl⟩ : syracuseStep 4968449 = 3726337) B3726337
theorem B3312299 : Blo 2207435 3312299 := bstep (se 1 (by rfl) ⟨2484224, by rfl⟩ : syracuseStep 3312299 = 4968449) B4968449
theorem B2208199 : Blo 2207435 2208199 := bstep (se 1 (by rfl) ⟨1656149, by rfl⟩ : syracuseStep 2208199 = 3312299) B3312299
theorem B2484229 : Blo 2207435 2484229 := bbase (se 4 (by rfl) ⟨232896, by rfl⟩ : syracuseStep 2484229 = 465793) (by norm_num)
theorem B3312305 : Blo 2207435 3312305 := bstep (se 2 (by rfl) ⟨1242114, by rfl⟩ : syracuseStep 3312305 = 2484229) B2484229
theorem B2208203 : Blo 2207435 2208203 := bstep (se 1 (by rfl) ⟨1656152, by rfl⟩ : syracuseStep 2208203 = 3312305) B3312305
theorem B3144109 : Blo 2207435 3144109 := bbase (se 3 (by rfl) ⟨589520, by rfl⟩ : syracuseStep 3144109 = 1179041) (by norm_num)
theorem B4192145 : Blo 2207435 4192145 := bstep (se 2 (by rfl) ⟨1572054, by rfl⟩ : syracuseStep 4192145 = 3144109) B3144109
theorem B2794763 : Blo 2207435 2794763 := bstep (se 1 (by rfl) ⟨2096072, by rfl⟩ : syracuseStep 2794763 = 4192145) B4192145
theorem B7452701 : Blo 2207435 7452701 := bstep (se 3 (by rfl) ⟨1397381, by rfl⟩ : syracuseStep 7452701 = 2794763) B2794763
theorem B4968467 : Blo 2207435 4968467 := bstep (se 1 (by rfl) ⟨3726350, by rfl⟩ : syracuseStep 4968467 = 7452701) B7452701
theorem B3312311 : Blo 2207435 3312311 := bstep (se 1 (by rfl) ⟨2484233, by rfl⟩ : syracuseStep 3312311 = 4968467) B4968467
theorem B2208207 : Blo 2207435 2208207 := bstep (se 1 (by rfl) ⟨1656155, by rfl⟩ : syracuseStep 2208207 = 3312311) B3312311
theorem B3312317 : Blo 2207435 3312317 := bbase (se 3 (by rfl) ⟨621059, by rfl⟩ : syracuseStep 3312317 = 1242119) (by norm_num)
theorem B2208211 : Blo 2207435 2208211 := bstep (se 1 (by rfl) ⟨1656158, by rfl⟩ : syracuseStep 2208211 = 3312317) B3312317
theorem B4968485 : Blo 2207435 4968485 := bbase (se 4 (by rfl) ⟨465795, by rfl⟩ : syracuseStep 4968485 = 931591) (by norm_num)
theorem B3312323 : Blo 2207435 3312323 := bstep (se 1 (by rfl) ⟨2484242, by rfl⟩ : syracuseStep 3312323 = 4968485) B4968485
theorem B2208215 : Blo 2207435 2208215 := bstep (se 1 (by rfl) ⟨1656161, by rfl⟩ : syracuseStep 2208215 = 3312323) B3312323
theorem B5589557 : Blo 2207435 5589557 := bbase (se 5 (by rfl) ⟨262010, by rfl⟩ : syracuseStep 5589557 = 524021) (by norm_num)
theorem B3726371 : Blo 2207435 3726371 := bstep (se 1 (by rfl) ⟨2794778, by rfl⟩ : syracuseStep 3726371 = 5589557) B5589557
theorem B2484247 : Blo 2207435 2484247 := bstep (se 1 (by rfl) ⟨1863185, by rfl⟩ : syracuseStep 2484247 = 3726371) B3726371
theorem B3312329 : Blo 2207435 3312329 := bstep (se 2 (by rfl) ⟨1242123, by rfl⟩ : syracuseStep 3312329 = 2484247) B2484247
theorem B2208219 : Blo 2207435 2208219 := bstep (se 1 (by rfl) ⟨1656164, by rfl⟩ : syracuseStep 2208219 = 3312329) B3312329
theorem B10611445 : Blo 2207435 10611445 := bbase (se 5 (by rfl) ⟨497411, by rfl⟩ : syracuseStep 10611445 = 994823) (by norm_num)
theorem B14148593 : Blo 2207435 14148593 := bstep (se 2 (by rfl) ⟨5305722, by rfl⟩ : syracuseStep 14148593 = 10611445) B10611445
theorem B9432395 : Blo 2207435 9432395 := bstep (se 1 (by rfl) ⟨7074296, by rfl⟩ : syracuseStep 9432395 = 14148593) B14148593
theorem B6288263 : Blo 2207435 6288263 := bstep (se 1 (by rfl) ⟨4716197, by rfl⟩ : syracuseStep 6288263 = 9432395) B9432395
theorem B4192175 : Blo 2207435 4192175 := bstep (se 1 (by rfl) ⟨3144131, by rfl⟩ : syracuseStep 4192175 = 6288263) B6288263
theorem B11179133 : Blo 2207435 11179133 := bstep (se 3 (by rfl) ⟨2096087, by rfl⟩ : syracuseStep 11179133 = 4192175) B4192175
theorem B7452755 : Blo 2207435 7452755 := bstep (se 1 (by rfl) ⟨5589566, by rfl⟩ : syracuseStep 7452755 = 11179133) B11179133
theorem B4968503 : Blo 2207435 4968503 := bstep (se 1 (by rfl) ⟨3726377, by rfl⟩ : syracuseStep 4968503 = 7452755) B7452755
theorem B3312335 : Blo 2207435 3312335 := bstep (se 1 (by rfl) ⟨2484251, by rfl⟩ : syracuseStep 3312335 = 4968503) B4968503
theorem B2208223 : Blo 2207435 2208223 := bstep (se 1 (by rfl) ⟨1656167, by rfl⟩ : syracuseStep 2208223 = 3312335) B3312335
theorem B3312341 : Blo 2207435 3312341 := bbase (se 7 (by rfl) ⟨38816, by rfl⟩ : syracuseStep 3312341 = 77633) (by norm_num)
theorem B2208227 : Blo 2207435 2208227 := bstep (se 1 (by rfl) ⟨1656170, by rfl⟩ : syracuseStep 2208227 = 3312341) B3312341
theorem B3357541 : Blo 2207435 3357541 := bbase (se 4 (by rfl) ⟨314769, by rfl⟩ : syracuseStep 3357541 = 629539) (by norm_num)
theorem B4476721 : Blo 2207435 4476721 := bstep (se 2 (by rfl) ⟨1678770, by rfl⟩ : syracuseStep 4476721 = 3357541) B3357541
theorem B5968961 : Blo 2207435 5968961 := bstep (se 2 (by rfl) ⟨2238360, by rfl⟩ : syracuseStep 5968961 = 4476721) B4476721
theorem B3979307 : Blo 2207435 3979307 := bstep (se 1 (by rfl) ⟨2984480, by rfl⟩ : syracuseStep 3979307 = 5968961) B5968961
theorem B10611485 : Blo 2207435 10611485 := bstep (se 3 (by rfl) ⟨1989653, by rfl⟩ : syracuseStep 10611485 = 3979307) B3979307
theorem B7074323 : Blo 2207435 7074323 := bstep (se 1 (by rfl) ⟨5305742, by rfl⟩ : syracuseStep 7074323 = 10611485) B10611485
theorem B4716215 : Blo 2207435 4716215 := bstep (se 1 (by rfl) ⟨3537161, by rfl⟩ : syracuseStep 4716215 = 7074323) B7074323
theorem B3144143 : Blo 2207435 3144143 := bstep (se 1 (by rfl) ⟨2358107, by rfl⟩ : syracuseStep 3144143 = 4716215) B4716215
theorem B8384381 : Blo 2207435 8384381 := bstep (se 3 (by rfl) ⟨1572071, by rfl⟩ : syracuseStep 8384381 = 3144143) B3144143
theorem B5589587 : Blo 2207435 5589587 := bstep (se 1 (by rfl) ⟨4192190, by rfl⟩ : syracuseStep 5589587 = 8384381) B8384381
theorem B3726391 : Blo 2207435 3726391 := bstep (se 1 (by rfl) ⟨2794793, by rfl⟩ : syracuseStep 3726391 = 5589587) B5589587
theorem B4968521 : Blo 2207435 4968521 := bstep (se 2 (by rfl) ⟨1863195, by rfl⟩ : syracuseStep 4968521 = 3726391) B3726391
theorem B3312347 : Blo 2207435 3312347 := bstep (se 1 (by rfl) ⟨2484260, by rfl⟩ : syracuseStep 3312347 = 4968521) B4968521
theorem B2208231 : Blo 2207435 2208231 := bstep (se 1 (by rfl) ⟨1656173, by rfl⟩ : syracuseStep 2208231 = 3312347) B3312347
theorem B2484265 : Blo 2207435 2484265 := bbase (se 2 (by rfl) ⟨931599, by rfl⟩ : syracuseStep 2484265 = 1863199) (by norm_num)
theorem B3312353 : Blo 2207435 3312353 := bstep (se 2 (by rfl) ⟨1242132, by rfl⟩ : syracuseStep 3312353 = 2484265) B2484265
theorem B2208235 : Blo 2207435 2208235 := bstep (se 1 (by rfl) ⟨1656176, by rfl⟩ : syracuseStep 2208235 = 3312353) B3312353
theorem B5968981 : Blo 2207435 5968981 := bbase (se 8 (by rfl) ⟨34974, by rfl⟩ : syracuseStep 5968981 = 69949) (by norm_num)
theorem B31834565 : Blo 2207435 31834565 := bstep (se 4 (by rfl) ⟨2984490, by rfl⟩ : syracuseStep 31834565 = 5968981) B5968981
theorem B21223043 : Blo 2207435 21223043 := bstep (se 1 (by rfl) ⟨15917282, by rfl⟩ : syracuseStep 21223043 = 31834565) B31834565
theorem B14148695 : Blo 2207435 14148695 := bstep (se 1 (by rfl) ⟨10611521, by rfl⟩ : syracuseStep 14148695 = 21223043) B21223043
theorem B9432463 : Blo 2207435 9432463 := bstep (se 1 (by rfl) ⟨7074347, by rfl⟩ : syracuseStep 9432463 = 14148695) B14148695
theorem B12576617 : Blo 2207435 12576617 := bstep (se 2 (by rfl) ⟨4716231, by rfl⟩ : syracuseStep 12576617 = 9432463) B9432463
theorem B8384411 : Blo 2207435 8384411 := bstep (se 1 (by rfl) ⟨6288308, by rfl⟩ : syracuseStep 8384411 = 12576617) B12576617
theorem B5589607 : Blo 2207435 5589607 := bstep (se 1 (by rfl) ⟨4192205, by rfl⟩ : syracuseStep 5589607 = 8384411) B8384411
theorem B7452809 : Blo 2207435 7452809 := bstep (se 2 (by rfl) ⟨2794803, by rfl⟩ : syracuseStep 7452809 = 5589607) B5589607
theorem B4968539 : Blo 2207435 4968539 := bstep (se 1 (by rfl) ⟨3726404, by rfl⟩ : syracuseStep 4968539 = 7452809) B7452809
theorem B3312359 : Blo 2207435 3312359 := bstep (se 1 (by rfl) ⟨2484269, by rfl⟩ : syracuseStep 3312359 = 4968539) B4968539
theorem B2208239 : Blo 2207435 2208239 := bstep (se 1 (by rfl) ⟨1656179, by rfl⟩ : syracuseStep 2208239 = 3312359) B3312359
theorem B3312365 : Blo 2207435 3312365 := bbase (se 3 (by rfl) ⟨621068, by rfl⟩ : syracuseStep 3312365 = 1242137) (by norm_num)
theorem B2208243 : Blo 2207435 2208243 := bstep (se 1 (by rfl) ⟨1656182, by rfl⟩ : syracuseStep 2208243 = 3312365) B3312365
theorem B4968557 : Blo 2207435 4968557 := bbase (se 3 (by rfl) ⟨931604, by rfl⟩ : syracuseStep 4968557 = 1863209) (by norm_num)
theorem B3312371 : Blo 2207435 3312371 := bstep (se 1 (by rfl) ⟨2484278, by rfl⟩ : syracuseStep 3312371 = 4968557) B4968557
theorem B2208247 : Blo 2207435 2208247 := bstep (se 1 (by rfl) ⟨1656185, by rfl⟩ : syracuseStep 2208247 = 3312371) B3312371
theorem B4192229 : Blo 2207435 4192229 := bbase (se 4 (by rfl) ⟨393021, by rfl⟩ : syracuseStep 4192229 = 786043) (by norm_num)
theorem B2794819 : Blo 2207435 2794819 := bstep (se 1 (by rfl) ⟨2096114, by rfl⟩ : syracuseStep 2794819 = 4192229) B4192229
theorem B3726425 : Blo 2207435 3726425 := bstep (se 2 (by rfl) ⟨1397409, by rfl⟩ : syracuseStep 3726425 = 2794819) B2794819
theorem B2484283 : Blo 2207435 2484283 := bstep (se 1 (by rfl) ⟨1863212, by rfl⟩ : syracuseStep 2484283 = 3726425) B3726425
theorem B3312377 : Blo 2207435 3312377 := bstep (se 2 (by rfl) ⟨1242141, by rfl⟩ : syracuseStep 3312377 = 2484283) B2484283
theorem B2208251 : Blo 2207435 2208251 := bstep (se 1 (by rfl) ⟨1656188, by rfl⟩ : syracuseStep 2208251 = 3312377) B3312377
theorem B3979349 : Blo 2207435 3979349 := bbase (se 8 (by rfl) ⟨23316, by rfl⟩ : syracuseStep 3979349 = 46633) (by norm_num)
theorem B42446389 : Blo 2207435 42446389 := bstep (se 5 (by rfl) ⟨1989674, by rfl⟩ : syracuseStep 42446389 = 3979349) B3979349
theorem B56595185 : Blo 2207435 56595185 := bstep (se 2 (by rfl) ⟨21223194, by rfl⟩ : syracuseStep 56595185 = 42446389) B42446389
theorem B37730123 : Blo 2207435 37730123 := bstep (se 1 (by rfl) ⟨28297592, by rfl⟩ : syracuseStep 37730123 = 56595185) B56595185
theorem B25153415 : Blo 2207435 25153415 := bstep (se 1 (by rfl) ⟨18865061, by rfl⟩ : syracuseStep 25153415 = 37730123) B37730123
theorem B16768943 : Blo 2207435 16768943 := bstep (se 1 (by rfl) ⟨12576707, by rfl⟩ : syracuseStep 16768943 = 25153415) B25153415
theorem B11179295 : Blo 2207435 11179295 := bstep (se 1 (by rfl) ⟨8384471, by rfl⟩ : syracuseStep 11179295 = 16768943) B16768943
theorem B7452863 : Blo 2207435 7452863 := bstep (se 1 (by rfl) ⟨5589647, by rfl⟩ : syracuseStep 7452863 = 11179295) B11179295
theorem B4968575 : Blo 2207435 4968575 := bstep (se 1 (by rfl) ⟨3726431, by rfl⟩ : syracuseStep 4968575 = 7452863) B7452863
theorem B3312383 : Blo 2207435 3312383 := bstep (se 1 (by rfl) ⟨2484287, by rfl⟩ : syracuseStep 3312383 = 4968575) B4968575
theorem B2208255 : Blo 2207435 2208255 := bstep (se 1 (by rfl) ⟨1656191, by rfl⟩ : syracuseStep 2208255 = 3312383) B3312383
theorem B3312389 : Blo 2207435 3312389 := bbase (se 4 (by rfl) ⟨310536, by rfl⟩ : syracuseStep 3312389 = 621073) (by norm_num)
theorem B2208259 : Blo 2207435 2208259 := bstep (se 1 (by rfl) ⟨1656194, by rfl⟩ : syracuseStep 2208259 = 3312389) B3312389
theorem B3726445 : Blo 2207435 3726445 := bbase (se 3 (by rfl) ⟨698708, by rfl⟩ : syracuseStep 3726445 = 1397417) (by norm_num)
theorem B4968593 : Blo 2207435 4968593 := bstep (se 2 (by rfl) ⟨1863222, by rfl⟩ : syracuseStep 4968593 = 3726445) B3726445
theorem B3312395 : Blo 2207435 3312395 := bstep (se 1 (by rfl) ⟨2484296, by rfl⟩ : syracuseStep 3312395 = 4968593) B4968593
theorem B2208263 : Blo 2207435 2208263 := bstep (se 1 (by rfl) ⟨1656197, by rfl⟩ : syracuseStep 2208263 = 3312395) B3312395
theorem B2484301 : Blo 2207435 2484301 := bbase (se 3 (by rfl) ⟨465806, by rfl⟩ : syracuseStep 2484301 = 931613) (by norm_num)
theorem B3312401 : Blo 2207435 3312401 := bstep (se 2 (by rfl) ⟨1242150, by rfl⟩ : syracuseStep 3312401 = 2484301) B2484301
theorem B2208267 : Blo 2207435 2208267 := bstep (se 1 (by rfl) ⟨1656200, by rfl⟩ : syracuseStep 2208267 = 3312401) B3312401
theorem B7452917 : Blo 2207435 7452917 := bbase (se 5 (by rfl) ⟨349355, by rfl⟩ : syracuseStep 7452917 = 698711) (by norm_num)
theorem B4968611 : Blo 2207435 4968611 := bstep (se 1 (by rfl) ⟨3726458, by rfl⟩ : syracuseStep 4968611 = 7452917) B7452917
theorem B3312407 : Blo 2207435 3312407 := bstep (se 1 (by rfl) ⟨2484305, by rfl⟩ : syracuseStep 3312407 = 4968611) B4968611
theorem B2208271 : Blo 2207435 2208271 := bstep (se 1 (by rfl) ⟨1656203, by rfl⟩ : syracuseStep 2208271 = 3312407) B3312407
theorem B3312413 : Blo 2207435 3312413 := bbase (se 3 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 3312413 = 1242155) (by norm_num)
theorem B2208275 : Blo 2207435 2208275 := bstep (se 1 (by rfl) ⟨1656206, by rfl⟩ : syracuseStep 2208275 = 3312413) B3312413
theorem B4968629 : Blo 2207435 4968629 := bbase (se 5 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 4968629 = 465809) (by norm_num)
theorem B3312419 : Blo 2207435 3312419 := bstep (se 1 (by rfl) ⟨2484314, by rfl⟩ : syracuseStep 3312419 = 4968629) B4968629
theorem B2208279 : Blo 2207435 2208279 := bstep (se 1 (by rfl) ⟨1656209, by rfl⟩ : syracuseStep 2208279 = 3312419) B3312419
theorem B3537245 : Blo 2207435 3537245 := bbase (se 3 (by rfl) ⟨663233, by rfl⟩ : syracuseStep 3537245 = 1326467) (by norm_num)
theorem B2358163 : Blo 2207435 2358163 := bstep (se 1 (by rfl) ⟨1768622, by rfl⟩ : syracuseStep 2358163 = 3537245) B3537245
theorem B12576869 : Blo 2207435 12576869 := bstep (se 4 (by rfl) ⟨1179081, by rfl⟩ : syracuseStep 12576869 = 2358163) B2358163
theorem B8384579 : Blo 2207435 8384579 := bstep (se 1 (by rfl) ⟨6288434, by rfl⟩ : syracuseStep 8384579 = 12576869) B12576869
theorem B5589719 : Blo 2207435 5589719 := bstep (se 1 (by rfl) ⟨4192289, by rfl⟩ : syracuseStep 5589719 = 8384579) B8384579
theorem B3726479 : Blo 2207435 3726479 := bstep (se 1 (by rfl) ⟨2794859, by rfl⟩ : syracuseStep 3726479 = 5589719) B5589719
theorem B2484319 : Blo 2207435 2484319 := bstep (se 1 (by rfl) ⟨1863239, by rfl⟩ : syracuseStep 2484319 = 3726479) B3726479
theorem B3312425 : Blo 2207435 3312425 := bstep (se 2 (by rfl) ⟨1242159, by rfl⟩ : syracuseStep 3312425 = 2484319) B2484319
theorem B2208283 : Blo 2207435 2208283 := bstep (se 1 (by rfl) ⟨1656212, by rfl⟩ : syracuseStep 2208283 = 3312425) B3312425
theorem B5305877 : Blo 2207435 5305877 := bbase (se 6 (by rfl) ⟨124356, by rfl⟩ : syracuseStep 5305877 = 248713) (by norm_num)
theorem B3537251 : Blo 2207435 3537251 := bstep (se 1 (by rfl) ⟨2652938, by rfl⟩ : syracuseStep 3537251 = 5305877) B5305877
theorem B2358167 : Blo 2207435 2358167 := bstep (se 1 (by rfl) ⟨1768625, by rfl⟩ : syracuseStep 2358167 = 3537251) B3537251
theorem B6288445 : Blo 2207435 6288445 := bstep (se 3 (by rfl) ⟨1179083, by rfl⟩ : syracuseStep 6288445 = 2358167) B2358167
theorem B8384593 : Blo 2207435 8384593 := bstep (se 2 (by rfl) ⟨3144222, by rfl⟩ : syracuseStep 8384593 = 6288445) B6288445
theorem B11179457 : Blo 2207435 11179457 := bstep (se 2 (by rfl) ⟨4192296, by rfl⟩ : syracuseStep 11179457 = 8384593) B8384593
theorem B7452971 : Blo 2207435 7452971 := bstep (se 1 (by rfl) ⟨5589728, by rfl⟩ : syracuseStep 7452971 = 11179457) B11179457
theorem B4968647 : Blo 2207435 4968647 := bstep (se 1 (by rfl) ⟨3726485, by rfl⟩ : syracuseStep 4968647 = 7452971) B7452971
theorem B3312431 : Blo 2207435 3312431 := bstep (se 1 (by rfl) ⟨2484323, by rfl⟩ : syracuseStep 3312431 = 4968647) B4968647
theorem B2208287 : Blo 2207435 2208287 := bstep (se 1 (by rfl) ⟨1656215, by rfl⟩ : syracuseStep 2208287 = 3312431) B3312431
theorem B3312437 : Blo 2207435 3312437 := bbase (se 5 (by rfl) ⟨155270, by rfl⟩ : syracuseStep 3312437 = 310541) (by norm_num)
theorem B2208291 : Blo 2207435 2208291 := bstep (se 1 (by rfl) ⟨1656218, by rfl⟩ : syracuseStep 2208291 = 3312437) B3312437
theorem B5589749 : Blo 2207435 5589749 := bbase (se 5 (by rfl) ⟨262019, by rfl⟩ : syracuseStep 5589749 = 524039) (by norm_num)
theorem B3726499 : Blo 2207435 3726499 := bstep (se 1 (by rfl) ⟨2794874, by rfl⟩ : syracuseStep 3726499 = 5589749) B5589749
theorem B4968665 : Blo 2207435 4968665 := bstep (se 2 (by rfl) ⟨1863249, by rfl⟩ : syracuseStep 4968665 = 3726499) B3726499
theorem B3312443 : Blo 2207435 3312443 := bstep (se 1 (by rfl) ⟨2484332, by rfl⟩ : syracuseStep 3312443 = 4968665) B4968665
theorem B2208295 : Blo 2207435 2208295 := bstep (se 1 (by rfl) ⟨1656221, by rfl⟩ : syracuseStep 2208295 = 3312443) B3312443
theorem B2484337 : Blo 2207435 2484337 := bbase (se 2 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 2484337 = 1863253) (by norm_num)
theorem B3312449 : Blo 2207435 3312449 := bstep (se 2 (by rfl) ⟨1242168, by rfl⟩ : syracuseStep 3312449 = 2484337) B2484337
theorem B2208299 : Blo 2207435 2208299 := bstep (se 1 (by rfl) ⟨1656224, by rfl⟩ : syracuseStep 2208299 = 3312449) B3312449
theorem B8953733 : Blo 2207435 8953733 := bbase (se 4 (by rfl) ⟨839412, by rfl⟩ : syracuseStep 8953733 = 1678825) (by norm_num)
theorem B5969155 : Blo 2207435 5969155 := bstep (se 1 (by rfl) ⟨4476866, by rfl⟩ : syracuseStep 5969155 = 8953733) B8953733
theorem B7958873 : Blo 2207435 7958873 := bstep (se 2 (by rfl) ⟨2984577, by rfl⟩ : syracuseStep 7958873 = 5969155) B5969155
theorem B5305915 : Blo 2207435 5305915 := bstep (se 1 (by rfl) ⟨3979436, by rfl⟩ : syracuseStep 5305915 = 7958873) B7958873
theorem B7074553 : Blo 2207435 7074553 := bstep (se 2 (by rfl) ⟨2652957, by rfl⟩ : syracuseStep 7074553 = 5305915) B5305915
theorem B9432737 : Blo 2207435 9432737 := bstep (se 2 (by rfl) ⟨3537276, by rfl⟩ : syracuseStep 9432737 = 7074553) B7074553
theorem B6288491 : Blo 2207435 6288491 := bstep (se 1 (by rfl) ⟨4716368, by rfl⟩ : syracuseStep 6288491 = 9432737) B9432737
theorem B4192327 : Blo 2207435 4192327 := bstep (se 1 (by rfl) ⟨3144245, by rfl⟩ : syracuseStep 4192327 = 6288491) B6288491
theorem B5589769 : Blo 2207435 5589769 := bstep (se 2 (by rfl) ⟨2096163, by rfl⟩ : syracuseStep 5589769 = 4192327) B4192327
theorem B7453025 : Blo 2207435 7453025 := bstep (se 2 (by rfl) ⟨2794884, by rfl⟩ : syracuseStep 7453025 = 5589769) B5589769
theorem B4968683 : Blo 2207435 4968683 := bstep (se 1 (by rfl) ⟨3726512, by rfl⟩ : syracuseStep 4968683 = 7453025) B7453025
theorem B3312455 : Blo 2207435 3312455 := bstep (se 1 (by rfl) ⟨2484341, by rfl⟩ : syracuseStep 3312455 = 4968683) B4968683
theorem B2208303 : Blo 2207435 2208303 := bstep (se 1 (by rfl) ⟨1656227, by rfl⟩ : syracuseStep 2208303 = 3312455) B3312455
theorem B3312461 : Blo 2207435 3312461 := bbase (se 3 (by rfl) ⟨621086, by rfl⟩ : syracuseStep 3312461 = 1242173) (by norm_num)
theorem B2208307 : Blo 2207435 2208307 := bstep (se 1 (by rfl) ⟨1656230, by rfl⟩ : syracuseStep 2208307 = 3312461) B3312461
theorem B4968701 : Blo 2207435 4968701 := bbase (se 3 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 4968701 = 1863263) (by norm_num)
theorem B3312467 : Blo 2207435 3312467 := bstep (se 1 (by rfl) ⟨2484350, by rfl⟩ : syracuseStep 3312467 = 4968701) B4968701
theorem B2208311 : Blo 2207435 2208311 := bstep (se 1 (by rfl) ⟨1656233, by rfl⟩ : syracuseStep 2208311 = 3312467) B3312467
theorem B3726533 : Blo 2207435 3726533 := bbase (se 4 (by rfl) ⟨349362, by rfl⟩ : syracuseStep 3726533 = 698725) (by norm_num)
theorem B2484355 : Blo 2207435 2484355 := bstep (se 1 (by rfl) ⟨1863266, by rfl⟩ : syracuseStep 2484355 = 3726533) B3726533
theorem B3312473 : Blo 2207435 3312473 := bstep (se 2 (by rfl) ⟨1242177, by rfl⟩ : syracuseStep 3312473 = 2484355) B2484355
theorem B2208315 : Blo 2207435 2208315 := bstep (se 1 (by rfl) ⟨1656236, by rfl⟩ : syracuseStep 2208315 = 3312473) B3312473
theorem B16769429 : Blo 2207435 16769429 := bbase (se 6 (by rfl) ⟨393033, by rfl⟩ : syracuseStep 16769429 = 786067) (by norm_num)
theorem B11179619 : Blo 2207435 11179619 := bstep (se 1 (by rfl) ⟨8384714, by rfl⟩ : syracuseStep 11179619 = 16769429) B16769429
theorem B7453079 : Blo 2207435 7453079 := bstep (se 1 (by rfl) ⟨5589809, by rfl⟩ : syracuseStep 7453079 = 11179619) B11179619
theorem B4968719 : Blo 2207435 4968719 := bstep (se 1 (by rfl) ⟨3726539, by rfl⟩ : syracuseStep 4968719 = 7453079) B7453079
theorem B3312479 : Blo 2207435 3312479 := bstep (se 1 (by rfl) ⟨2484359, by rfl⟩ : syracuseStep 3312479 = 4968719) B4968719
theorem B2208319 : Blo 2207435 2208319 := bstep (se 1 (by rfl) ⟨1656239, by rfl⟩ : syracuseStep 2208319 = 3312479) B3312479
theorem B3312485 : Blo 2207435 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2208323 : Blo 2207435 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B4192373 : Blo 2207435 4192373 := bbase (se 5 (by rfl) ⟨196517, by rfl⟩ : syracuseStep 4192373 = 393035) (by norm_num)
theorem B2794915 : Blo 2207435 2794915 := bstep (se 1 (by rfl) ⟨2096186, by rfl⟩ : syracuseStep 2794915 = 4192373) B4192373
theorem B3726553 : Blo 2207435 3726553 := bstep (se 2 (by rfl) ⟨1397457, by rfl⟩ : syracuseStep 3726553 = 2794915) B2794915
theorem B4968737 : Blo 2207435 4968737 := bstep (se 2 (by rfl) ⟨1863276, by rfl⟩ : syracuseStep 4968737 = 3726553) B3726553
theorem B3312491 : Blo 2207435 3312491 := bstep (se 1 (by rfl) ⟨2484368, by rfl⟩ : syracuseStep 3312491 = 4968737) B4968737
theorem B2208327 : Blo 2207435 2208327 := bstep (se 1 (by rfl) ⟨1656245, by rfl⟩ : syracuseStep 2208327 = 3312491) B3312491
theorem B2484373 : Blo 2207435 2484373 := bbase (se 6 (by rfl) ⟨58227, by rfl⟩ : syracuseStep 2484373 = 116455) (by norm_num)
theorem B3312497 : Blo 2207435 3312497 := bstep (se 2 (by rfl) ⟨1242186, by rfl⟩ : syracuseStep 3312497 = 2484373) B2484373
theorem B2208331 : Blo 2207435 2208331 := bstep (se 1 (by rfl) ⟨1656248, by rfl⟩ : syracuseStep 2208331 = 3312497) B3312497
theorem B2794925 : Blo 2207435 2794925 := bbase (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) (by norm_num)
theorem B7453133 : Blo 2207435 7453133 := bstep (se 3 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 7453133 = 2794925) B2794925
theorem B4968755 : Blo 2207435 4968755 := bstep (se 1 (by rfl) ⟨3726566, by rfl⟩ : syracuseStep 4968755 = 7453133) B7453133
theorem B3312503 : Blo 2207435 3312503 := bstep (se 1 (by rfl) ⟨2484377, by rfl⟩ : syracuseStep 3312503 = 4968755) B4968755
theorem B2208335 : Blo 2207435 2208335 := bstep (se 1 (by rfl) ⟨1656251, by rfl⟩ : syracuseStep 2208335 = 3312503) B3312503
theorem B3312509 : Blo 2207435 3312509 := bbase (se 3 (by rfl) ⟨621095, by rfl⟩ : syracuseStep 3312509 = 1242191) (by norm_num)
theorem B2208339 : Blo 2207435 2208339 := bstep (se 1 (by rfl) ⟨1656254, by rfl⟩ : syracuseStep 2208339 = 3312509) B3312509
theorem B4968773 : Blo 2207435 4968773 := bbase (se 4 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 4968773 = 931645) (by norm_num)
theorem B3312515 : Blo 2207435 3312515 := bstep (se 1 (by rfl) ⟨2484386, by rfl⟩ : syracuseStep 3312515 = 4968773) B4968773
theorem B2208343 : Blo 2207435 2208343 := bstep (se 1 (by rfl) ⟨1656257, by rfl⟩ : syracuseStep 2208343 = 3312515) B3312515
theorem B11938549 : Blo 2207435 11938549 := bbase (se 5 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 11938549 = 1119239) (by norm_num)
theorem B15918065 : Blo 2207435 15918065 := bstep (se 2 (by rfl) ⟨5969274, by rfl⟩ : syracuseStep 15918065 = 11938549) B11938549
theorem B10612043 : Blo 2207435 10612043 := bstep (se 1 (by rfl) ⟨7959032, by rfl⟩ : syracuseStep 10612043 = 15918065) B15918065
theorem B7074695 : Blo 2207435 7074695 := bstep (se 1 (by rfl) ⟨5306021, by rfl⟩ : syracuseStep 7074695 = 10612043) B10612043
theorem B4716463 : Blo 2207435 4716463 := bstep (se 1 (by rfl) ⟨3537347, by rfl⟩ : syracuseStep 4716463 = 7074695) B7074695
theorem B6288617 : Blo 2207435 6288617 := bstep (se 2 (by rfl) ⟨2358231, by rfl⟩ : syracuseStep 6288617 = 4716463) B4716463
theorem B4192411 : Blo 2207435 4192411 := bstep (se 1 (by rfl) ⟨3144308, by rfl⟩ : syracuseStep 4192411 = 6288617) B6288617
theorem B5589881 : Blo 2207435 5589881 := bstep (se 2 (by rfl) ⟨2096205, by rfl⟩ : syracuseStep 5589881 = 4192411) B4192411
theorem B3726587 : Blo 2207435 3726587 := bstep (se 1 (by rfl) ⟨2794940, by rfl⟩ : syracuseStep 3726587 = 5589881) B5589881
theorem B2484391 : Blo 2207435 2484391 := bstep (se 1 (by rfl) ⟨1863293, by rfl⟩ : syracuseStep 2484391 = 3726587) B3726587
theorem B3312521 : Blo 2207435 3312521 := bstep (se 2 (by rfl) ⟨1242195, by rfl⟩ : syracuseStep 3312521 = 2484391) B2484391
theorem B2208347 : Blo 2207435 2208347 := bstep (se 1 (by rfl) ⟨1656260, by rfl⟩ : syracuseStep 2208347 = 3312521) B3312521
theorem B11179781 : Blo 2207435 11179781 := bbase (se 4 (by rfl) ⟨1048104, by rfl⟩ : syracuseStep 11179781 = 2096209) (by norm_num)
theorem B7453187 : Blo 2207435 7453187 := bstep (se 1 (by rfl) ⟨5589890, by rfl⟩ : syracuseStep 7453187 = 11179781) B11179781
theorem B4968791 : Blo 2207435 4968791 := bstep (se 1 (by rfl) ⟨3726593, by rfl⟩ : syracuseStep 4968791 = 7453187) B7453187
theorem B3312527 : Blo 2207435 3312527 := bstep (se 1 (by rfl) ⟨2484395, by rfl⟩ : syracuseStep 3312527 = 4968791) B4968791
theorem B2208351 : Blo 2207435 2208351 := bstep (se 1 (by rfl) ⟨1656263, by rfl⟩ : syracuseStep 2208351 = 3312527) B3312527
theorem B3312533 : Blo 2207435 3312533 := bbase (se 6 (by rfl) ⟨77637, by rfl⟩ : syracuseStep 3312533 = 155275) (by norm_num)
theorem B2208355 : Blo 2207435 2208355 := bstep (se 1 (by rfl) ⟨1656266, by rfl⟩ : syracuseStep 2208355 = 3312533) B3312533
theorem B12577301 : Blo 2207435 12577301 := bbase (se 6 (by rfl) ⟨294780, by rfl⟩ : syracuseStep 12577301 = 589561) (by norm_num)
theorem B8384867 : Blo 2207435 8384867 := bstep (se 1 (by rfl) ⟨6288650, by rfl⟩ : syracuseStep 8384867 = 12577301) B12577301
theorem B5589911 : Blo 2207435 5589911 := bstep (se 1 (by rfl) ⟨4192433, by rfl⟩ : syracuseStep 5589911 = 8384867) B8384867
theorem B3726607 : Blo 2207435 3726607 := bstep (se 1 (by rfl) ⟨2794955, by rfl⟩ : syracuseStep 3726607 = 5589911) B5589911
theorem B4968809 : Blo 2207435 4968809 := bstep (se 2 (by rfl) ⟨1863303, by rfl⟩ : syracuseStep 4968809 = 3726607) B3726607
theorem B3312539 : Blo 2207435 3312539 := bstep (se 1 (by rfl) ⟨2484404, by rfl⟩ : syracuseStep 3312539 = 4968809) B4968809
theorem B2208359 : Blo 2207435 2208359 := bstep (se 1 (by rfl) ⟨1656269, by rfl⟩ : syracuseStep 2208359 = 3312539) B3312539
theorem B2484409 : Blo 2207435 2484409 := bbase (se 2 (by rfl) ⟨931653, by rfl⟩ : syracuseStep 2484409 = 1863307) (by norm_num)
theorem B3312545 : Blo 2207435 3312545 := bstep (se 2 (by rfl) ⟨1242204, by rfl⟩ : syracuseStep 3312545 = 2484409) B2484409
theorem B2208363 : Blo 2207435 2208363 := bstep (se 1 (by rfl) ⟨1656272, by rfl⟩ : syracuseStep 2208363 = 3312545) B3312545
theorem B5306069 : Blo 2207435 5306069 := bbase (se 7 (by rfl) ⟨62180, by rfl⟩ : syracuseStep 5306069 = 124361) (by norm_num)
theorem B3537379 : Blo 2207435 3537379 := bstep (se 1 (by rfl) ⟨2653034, by rfl⟩ : syracuseStep 3537379 = 5306069) B5306069
theorem B4716505 : Blo 2207435 4716505 := bstep (se 2 (by rfl) ⟨1768689, by rfl⟩ : syracuseStep 4716505 = 3537379) B3537379
theorem B6288673 : Blo 2207435 6288673 := bstep (se 2 (by rfl) ⟨2358252, by rfl⟩ : syracuseStep 6288673 = 4716505) B4716505
theorem B8384897 : Blo 2207435 8384897 := bstep (se 2 (by rfl) ⟨3144336, by rfl⟩ : syracuseStep 8384897 = 6288673) B6288673
theorem B5589931 : Blo 2207435 5589931 := bstep (se 1 (by rfl) ⟨4192448, by rfl⟩ : syracuseStep 5589931 = 8384897) B8384897
theorem B7453241 : Blo 2207435 7453241 := bstep (se 2 (by rfl) ⟨2794965, by rfl⟩ : syracuseStep 7453241 = 5589931) B5589931
theorem B4968827 : Blo 2207435 4968827 := bstep (se 1 (by rfl) ⟨3726620, by rfl⟩ : syracuseStep 4968827 = 7453241) B7453241
theorem B3312551 : Blo 2207435 3312551 := bstep (se 1 (by rfl) ⟨2484413, by rfl⟩ : syracuseStep 3312551 = 4968827) B4968827
theorem B2208367 : Blo 2207435 2208367 := bstep (se 1 (by rfl) ⟨1656275, by rfl⟩ : syracuseStep 2208367 = 3312551) B3312551
theorem B3312557 : Blo 2207435 3312557 := bbase (se 3 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 3312557 = 1242209) (by norm_num)
theorem B2208371 : Blo 2207435 2208371 := bstep (se 1 (by rfl) ⟨1656278, by rfl⟩ : syracuseStep 2208371 = 3312557) B3312557
theorem B4968845 : Blo 2207435 4968845 := bbase (se 3 (by rfl) ⟨931658, by rfl⟩ : syracuseStep 4968845 = 1863317) (by norm_num)
theorem B3312563 : Blo 2207435 3312563 := bstep (se 1 (by rfl) ⟨2484422, by rfl⟩ : syracuseStep 3312563 = 4968845) B4968845
theorem B2208375 : Blo 2207435 2208375 := bstep (se 1 (by rfl) ⟨1656281, by rfl⟩ : syracuseStep 2208375 = 3312563) B3312563
theorem B2794981 : Blo 2207435 2794981 := bbase (se 4 (by rfl) ⟨262029, by rfl⟩ : syracuseStep 2794981 = 524059) (by norm_num)
theorem B3726641 : Blo 2207435 3726641 := bstep (se 2 (by rfl) ⟨1397490, by rfl⟩ : syracuseStep 3726641 = 2794981) B2794981
theorem B2484427 : Blo 2207435 2484427 := bstep (se 1 (by rfl) ⟨1863320, by rfl⟩ : syracuseStep 2484427 = 3726641) B3726641
theorem B3312569 : Blo 2207435 3312569 := bstep (se 2 (by rfl) ⟨1242213, by rfl⟩ : syracuseStep 3312569 = 2484427) B2484427
theorem B2208379 : Blo 2207435 2208379 := bstep (se 1 (by rfl) ⟨1656284, by rfl⟩ : syracuseStep 2208379 = 3312569) B3312569
theorem B7269173 : Blo 2207435 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B77537845 : Blo 2207435 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B103383793 : Blo 2207435 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B551380229 : Blo 2207435 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B367586819 : Blo 2207435 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B245057879 : Blo 2207435 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B163371919 : Blo 2207435 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B217829225 : Blo 2207435 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B145219483 : Blo 2207435 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B193625977 : Blo 2207435 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B258167969 : Blo 2207435 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B172111979 : Blo 2207435 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B458965277 : Blo 2207435 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B305976851 : Blo 2207435 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B203984567 : Blo 2207435 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B135989711 : Blo 2207435 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B90659807 : Blo 2207435 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B60439871 : Blo 2207435 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B40293247 : Blo 2207435 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B53724329 : Blo 2207435 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B35816219 : Blo 2207435 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B23877479 : Blo 2207435 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B15918319 : Blo 2207435 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B21224425 : Blo 2207435 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B28299233 : Blo 2207435 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B18866155 : Blo 2207435 18866155 := bstep (se 1 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 18866155 = 28299233) B28299233
theorem B25154873 : Blo 2207435 25154873 := bstep (se 2 (by rfl) ⟨9433077, by rfl⟩ : syracuseStep 25154873 = 18866155) B18866155
theorem B16769915 : Blo 2207435 16769915 := bstep (se 1 (by rfl) ⟨12577436, by rfl⟩ : syracuseStep 16769915 = 25154873) B25154873
theorem B11179943 : Blo 2207435 11179943 := bstep (se 1 (by rfl) ⟨8384957, by rfl⟩ : syracuseStep 11179943 = 16769915) B16769915
theorem B7453295 : Blo 2207435 7453295 := bstep (se 1 (by rfl) ⟨5589971, by rfl⟩ : syracuseStep 7453295 = 11179943) B11179943
theorem B4968863 : Blo 2207435 4968863 := bstep (se 1 (by rfl) ⟨3726647, by rfl⟩ : syracuseStep 4968863 = 7453295) B7453295
theorem B3312575 : Blo 2207435 3312575 := bstep (se 1 (by rfl) ⟨2484431, by rfl⟩ : syracuseStep 3312575 = 4968863) B4968863
theorem B2208383 : Blo 2207435 2208383 := bstep (se 1 (by rfl) ⟨1656287, by rfl⟩ : syracuseStep 2208383 = 3312575) B3312575
theorem B3312581 : Blo 2207435 3312581 := bbase (se 4 (by rfl) ⟨310554, by rfl⟩ : syracuseStep 3312581 = 621109) (by norm_num)
theorem B2208387 : Blo 2207435 2208387 := bstep (se 1 (by rfl) ⟨1656290, by rfl⟩ : syracuseStep 2208387 = 3312581) B3312581
theorem B3726661 : Blo 2207435 3726661 := bbase (se 4 (by rfl) ⟨349374, by rfl⟩ : syracuseStep 3726661 = 698749) (by norm_num)
theorem B4968881 : Blo 2207435 4968881 := bstep (se 2 (by rfl) ⟨1863330, by rfl⟩ : syracuseStep 4968881 = 3726661) B3726661
theorem B3312587 : Blo 2207435 3312587 := bstep (se 1 (by rfl) ⟨2484440, by rfl⟩ : syracuseStep 3312587 = 4968881) B4968881
theorem B2208391 : Blo 2207435 2208391 := bstep (se 1 (by rfl) ⟨1656293, by rfl⟩ : syracuseStep 2208391 = 3312587) B3312587
theorem B2484445 : Blo 2207435 2484445 := bbase (se 3 (by rfl) ⟨465833, by rfl⟩ : syracuseStep 2484445 = 931667) (by norm_num)
theorem B3312593 : Blo 2207435 3312593 := bstep (se 2 (by rfl) ⟨1242222, by rfl⟩ : syracuseStep 3312593 = 2484445) B2484445
theorem B2208395 : Blo 2207435 2208395 := bstep (se 1 (by rfl) ⟨1656296, by rfl⟩ : syracuseStep 2208395 = 3312593) B3312593
theorem B7453349 : Blo 2207435 7453349 := bbase (se 4 (by rfl) ⟨698751, by rfl⟩ : syracuseStep 7453349 = 1397503) (by norm_num)
theorem B4968899 : Blo 2207435 4968899 := bstep (se 1 (by rfl) ⟨3726674, by rfl⟩ : syracuseStep 4968899 = 7453349) B7453349
theorem B3312599 : Blo 2207435 3312599 := bstep (se 1 (by rfl) ⟨2484449, by rfl⟩ : syracuseStep 3312599 = 4968899) B4968899
theorem B2208399 : Blo 2207435 2208399 := bstep (se 1 (by rfl) ⟨1656299, by rfl⟩ : syracuseStep 2208399 = 3312599) B3312599
theorem B3312605 : Blo 2207435 3312605 := bbase (se 3 (by rfl) ⟨621113, by rfl⟩ : syracuseStep 3312605 = 1242227) (by norm_num)
theorem B2208403 : Blo 2207435 2208403 := bstep (se 1 (by rfl) ⟨1656302, by rfl⟩ : syracuseStep 2208403 = 3312605) B3312605
theorem B4968917 : Blo 2207435 4968917 := bbase (se 7 (by rfl) ⟨58229, by rfl⟩ : syracuseStep 4968917 = 116459) (by norm_num)
theorem B3312611 : Blo 2207435 3312611 := bstep (se 1 (by rfl) ⟨2484458, by rfl⟩ : syracuseStep 3312611 = 4968917) B4968917
theorem B2208407 : Blo 2207435 2208407 := bstep (se 1 (by rfl) ⟨1656305, by rfl⟩ : syracuseStep 2208407 = 3312611) B3312611
theorem B67995733 : Blo 2207435 67995733 := bbase (se 8 (by rfl) ⟨398412, by rfl⟩ : syracuseStep 67995733 = 796825) (by norm_num)
theorem B90660977 : Blo 2207435 90660977 := bstep (se 2 (by rfl) ⟨33997866, by rfl⟩ : syracuseStep 90660977 = 67995733) B67995733
theorem B60440651 : Blo 2207435 60440651 := bstep (se 1 (by rfl) ⟨45330488, by rfl⟩ : syracuseStep 60440651 = 90660977) B90660977
theorem B40293767 : Blo 2207435 40293767 := bstep (se 1 (by rfl) ⟨30220325, by rfl⟩ : syracuseStep 40293767 = 60440651) B60440651
theorem B26862511 : Blo 2207435 26862511 := bstep (se 1 (by rfl) ⟨20146883, by rfl⟩ : syracuseStep 26862511 = 40293767) B40293767
theorem B35816681 : Blo 2207435 35816681 := bstep (se 2 (by rfl) ⟨13431255, by rfl⟩ : syracuseStep 35816681 = 26862511) B26862511
theorem B23877787 : Blo 2207435 23877787 := bstep (se 1 (by rfl) ⟨17908340, by rfl⟩ : syracuseStep 23877787 = 35816681) B35816681
theorem B31837049 : Blo 2207435 31837049 := bstep (se 2 (by rfl) ⟨11938893, by rfl⟩ : syracuseStep 31837049 = 23877787) B23877787
theorem B21224699 : Blo 2207435 21224699 := bstep (se 1 (by rfl) ⟨15918524, by rfl⟩ : syracuseStep 21224699 = 31837049) B31837049
theorem B14149799 : Blo 2207435 14149799 := bstep (se 1 (by rfl) ⟨10612349, by rfl⟩ : syracuseStep 14149799 = 21224699) B21224699
theorem B9433199 : Blo 2207435 9433199 := bstep (se 1 (by rfl) ⟨7074899, by rfl⟩ : syracuseStep 9433199 = 14149799) B14149799
theorem B6288799 : Blo 2207435 6288799 := bstep (se 1 (by rfl) ⟨4716599, by rfl⟩ : syracuseStep 6288799 = 9433199) B9433199
theorem B8385065 : Blo 2207435 8385065 := bstep (se 2 (by rfl) ⟨3144399, by rfl⟩ : syracuseStep 8385065 = 6288799) B6288799
theorem B5590043 : Blo 2207435 5590043 := bstep (se 1 (by rfl) ⟨4192532, by rfl⟩ : syracuseStep 5590043 = 8385065) B8385065
theorem B3726695 : Blo 2207435 3726695 := bstep (se 1 (by rfl) ⟨2795021, by rfl⟩ : syracuseStep 3726695 = 5590043) B5590043
theorem B2484463 : Blo 2207435 2484463 := bstep (se 1 (by rfl) ⟨1863347, by rfl⟩ : syracuseStep 2484463 = 3726695) B3726695
theorem B3312617 : Blo 2207435 3312617 := bstep (se 2 (by rfl) ⟨1242231, by rfl⟩ : syracuseStep 3312617 = 2484463) B2484463
theorem B2208411 : Blo 2207435 2208411 := bstep (se 1 (by rfl) ⟨1656308, by rfl⟩ : syracuseStep 2208411 = 3312617) B3312617
theorem B4249741 : Blo 2207435 4249741 := bbase (se 3 (by rfl) ⟨796826, by rfl⟩ : syracuseStep 4249741 = 1593653) (by norm_num)
theorem B5666321 : Blo 2207435 5666321 := bstep (se 2 (by rfl) ⟨2124870, by rfl⟩ : syracuseStep 5666321 = 4249741) B4249741
theorem B15110189 : Blo 2207435 15110189 := bstep (se 3 (by rfl) ⟨2833160, by rfl⟩ : syracuseStep 15110189 = 5666321) B5666321
theorem B10073459 : Blo 2207435 10073459 := bstep (se 1 (by rfl) ⟨7555094, by rfl⟩ : syracuseStep 10073459 = 15110189) B15110189
theorem B6715639 : Blo 2207435 6715639 := bstep (se 1 (by rfl) ⟨5036729, by rfl⟩ : syracuseStep 6715639 = 10073459) B10073459
theorem B35816741 : Blo 2207435 35816741 := bstep (se 4 (by rfl) ⟨3357819, by rfl⟩ : syracuseStep 35816741 = 6715639) B6715639
theorem B23877827 : Blo 2207435 23877827 := bstep (se 1 (by rfl) ⟨17908370, by rfl⟩ : syracuseStep 23877827 = 35816741) B35816741
theorem B15918551 : Blo 2207435 15918551 := bstep (se 1 (by rfl) ⟨11938913, by rfl⟩ : syracuseStep 15918551 = 23877827) B23877827
theorem B10612367 : Blo 2207435 10612367 := bstep (se 1 (by rfl) ⟨7959275, by rfl⟩ : syracuseStep 10612367 = 15918551) B15918551
theorem B7074911 : Blo 2207435 7074911 := bstep (se 1 (by rfl) ⟨5306183, by rfl⟩ : syracuseStep 7074911 = 10612367) B10612367
theorem B18866429 : Blo 2207435 18866429 := bstep (se 3 (by rfl) ⟨3537455, by rfl⟩ : syracuseStep 18866429 = 7074911) B7074911
theorem B12577619 : Blo 2207435 12577619 := bstep (se 1 (by rfl) ⟨9433214, by rfl⟩ : syracuseStep 12577619 = 18866429) B18866429
theorem B8385079 : Blo 2207435 8385079 := bstep (se 1 (by rfl) ⟨6288809, by rfl⟩ : syracuseStep 8385079 = 12577619) B12577619
theorem B11180105 : Blo 2207435 11180105 := bstep (se 2 (by rfl) ⟨4192539, by rfl⟩ : syracuseStep 11180105 = 8385079) B8385079
theorem B7453403 : Blo 2207435 7453403 := bstep (se 1 (by rfl) ⟨5590052, by rfl⟩ : syracuseStep 7453403 = 11180105) B11180105
theorem B4968935 : Blo 2207435 4968935 := bstep (se 1 (by rfl) ⟨3726701, by rfl⟩ : syracuseStep 4968935 = 7453403) B7453403
theorem B3312623 : Blo 2207435 3312623 := bstep (se 1 (by rfl) ⟨2484467, by rfl⟩ : syracuseStep 3312623 = 4968935) B4968935
theorem B2208415 : Blo 2207435 2208415 := bstep (se 1 (by rfl) ⟨1656311, by rfl⟩ : syracuseStep 2208415 = 3312623) B3312623
theorem B3312629 : Blo 2207435 3312629 := bbase (se 5 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 3312629 = 310559) (by norm_num)
theorem B2208419 : Blo 2207435 2208419 := bstep (se 1 (by rfl) ⟨1656314, by rfl⟩ : syracuseStep 2208419 = 3312629) B3312629
theorem B3537469 : Blo 2207435 3537469 := bbase (se 3 (by rfl) ⟨663275, by rfl⟩ : syracuseStep 3537469 = 1326551) (by norm_num)
theorem B4716625 : Blo 2207435 4716625 := bstep (se 2 (by rfl) ⟨1768734, by rfl⟩ : syracuseStep 4716625 = 3537469) B3537469
theorem B6288833 : Blo 2207435 6288833 := bstep (se 2 (by rfl) ⟨2358312, by rfl⟩ : syracuseStep 6288833 = 4716625) B4716625
theorem B4192555 : Blo 2207435 4192555 := bstep (se 1 (by rfl) ⟨3144416, by rfl⟩ : syracuseStep 4192555 = 6288833) B6288833
theorem B5590073 : Blo 2207435 5590073 := bstep (se 2 (by rfl) ⟨2096277, by rfl⟩ : syracuseStep 5590073 = 4192555) B4192555
theorem B3726715 : Blo 2207435 3726715 := bstep (se 1 (by rfl) ⟨2795036, by rfl⟩ : syracuseStep 3726715 = 5590073) B5590073
theorem B4968953 : Blo 2207435 4968953 := bstep (se 2 (by rfl) ⟨1863357, by rfl⟩ : syracuseStep 4968953 = 3726715) B3726715
theorem B3312635 : Blo 2207435 3312635 := bstep (se 1 (by rfl) ⟨2484476, by rfl⟩ : syracuseStep 3312635 = 4968953) B4968953
theorem B2208423 : Blo 2207435 2208423 := bstep (se 1 (by rfl) ⟨1656317, by rfl⟩ : syracuseStep 2208423 = 3312635) B3312635
theorem B2484481 : Blo 2207435 2484481 := bbase (se 2 (by rfl) ⟨931680, by rfl⟩ : syracuseStep 2484481 = 1863361) (by norm_num)
theorem B3312641 : Blo 2207435 3312641 := bstep (se 2 (by rfl) ⟨1242240, by rfl⟩ : syracuseStep 3312641 = 2484481) B2484481
theorem B2208427 : Blo 2207435 2208427 := bstep (se 1 (by rfl) ⟨1656320, by rfl⟩ : syracuseStep 2208427 = 3312641) B3312641
theorem B5590093 : Blo 2207435 5590093 := bbase (se 3 (by rfl) ⟨1048142, by rfl⟩ : syracuseStep 5590093 = 2096285) (by norm_num)
theorem B7453457 : Blo 2207435 7453457 := bstep (se 2 (by rfl) ⟨2795046, by rfl⟩ : syracuseStep 7453457 = 5590093) B5590093
theorem B4968971 : Blo 2207435 4968971 := bstep (se 1 (by rfl) ⟨3726728, by rfl⟩ : syracuseStep 4968971 = 7453457) B7453457
theorem B3312647 : Blo 2207435 3312647 := bstep (se 1 (by rfl) ⟨2484485, by rfl⟩ : syracuseStep 3312647 = 4968971) B4968971
theorem B2208431 : Blo 2207435 2208431 := bstep (se 1 (by rfl) ⟨1656323, by rfl⟩ : syracuseStep 2208431 = 3312647) B3312647
theorem B3312653 : Blo 2207435 3312653 := bbase (se 3 (by rfl) ⟨621122, by rfl⟩ : syracuseStep 3312653 = 1242245) (by norm_num)
theorem B2208435 : Blo 2207435 2208435 := bstep (se 1 (by rfl) ⟨1656326, by rfl⟩ : syracuseStep 2208435 = 3312653) B3312653
theorem B4968989 : Blo 2207435 4968989 := bbase (se 3 (by rfl) ⟨931685, by rfl⟩ : syracuseStep 4968989 = 1863371) (by norm_num)
theorem B3312659 : Blo 2207435 3312659 := bstep (se 1 (by rfl) ⟨2484494, by rfl⟩ : syracuseStep 3312659 = 4968989) B4968989
theorem B2208439 : Blo 2207435 2208439 := bstep (se 1 (by rfl) ⟨1656329, by rfl⟩ : syracuseStep 2208439 = 3312659) B3312659
theorem B3726749 : Blo 2207435 3726749 := bbase (se 3 (by rfl) ⟨698765, by rfl⟩ : syracuseStep 3726749 = 1397531) (by norm_num)
theorem B2484499 : Blo 2207435 2484499 := bstep (se 1 (by rfl) ⟨1863374, by rfl⟩ : syracuseStep 2484499 = 3726749) B3726749
theorem B3312665 : Blo 2207435 3312665 := bstep (se 2 (by rfl) ⟨1242249, by rfl⟩ : syracuseStep 3312665 = 2484499) B2484499
theorem B2208443 : Blo 2207435 2208443 := bstep (se 1 (by rfl) ⟨1656332, by rfl⟩ : syracuseStep 2208443 = 3312665) B3312665
theorem B10073605 : Blo 2207435 10073605 := bbase (se 4 (by rfl) ⟨944400, by rfl⟩ : syracuseStep 10073605 = 1888801) (by norm_num)
theorem B13431473 : Blo 2207435 13431473 := bstep (se 2 (by rfl) ⟨5036802, by rfl⟩ : syracuseStep 13431473 = 10073605) B10073605
theorem B8954315 : Blo 2207435 8954315 := bstep (se 1 (by rfl) ⟨6715736, by rfl⟩ : syracuseStep 8954315 = 13431473) B13431473
theorem B5969543 : Blo 2207435 5969543 := bstep (se 1 (by rfl) ⟨4477157, by rfl⟩ : syracuseStep 5969543 = 8954315) B8954315
theorem B15918781 : Blo 2207435 15918781 := bstep (se 3 (by rfl) ⟨2984771, by rfl⟩ : syracuseStep 15918781 = 5969543) B5969543
theorem B21225041 : Blo 2207435 21225041 := bstep (se 2 (by rfl) ⟨7959390, by rfl⟩ : syracuseStep 21225041 = 15918781) B15918781
theorem B14150027 : Blo 2207435 14150027 := bstep (se 1 (by rfl) ⟨10612520, by rfl⟩ : syracuseStep 14150027 = 21225041) B21225041
theorem B9433351 : Blo 2207435 9433351 := bstep (se 1 (by rfl) ⟨7075013, by rfl⟩ : syracuseStep 9433351 = 14150027) B14150027
theorem B12577801 : Blo 2207435 12577801 := bstep (se 2 (by rfl) ⟨4716675, by rfl⟩ : syracuseStep 12577801 = 9433351) B9433351
theorem B16770401 : Blo 2207435 16770401 := bstep (se 2 (by rfl) ⟨6288900, by rfl⟩ : syracuseStep 16770401 = 12577801) B12577801
theorem B11180267 : Blo 2207435 11180267 := bstep (se 1 (by rfl) ⟨8385200, by rfl⟩ : syracuseStep 11180267 = 16770401) B16770401
theorem B7453511 : Blo 2207435 7453511 := bstep (se 1 (by rfl) ⟨5590133, by rfl⟩ : syracuseStep 7453511 = 11180267) B11180267
theorem B4969007 : Blo 2207435 4969007 := bstep (se 1 (by rfl) ⟨3726755, by rfl⟩ : syracuseStep 4969007 = 7453511) B7453511
theorem B3312671 : Blo 2207435 3312671 := bstep (se 1 (by rfl) ⟨2484503, by rfl⟩ : syracuseStep 3312671 = 4969007) B4969007
theorem B2208447 : Blo 2207435 2208447 := bstep (se 1 (by rfl) ⟨1656335, by rfl⟩ : syracuseStep 2208447 = 3312671) B3312671
theorem B3312677 : Blo 2207435 3312677 := bbase (se 4 (by rfl) ⟨310563, by rfl⟩ : syracuseStep 3312677 = 621127) (by norm_num)
theorem B2208451 : Blo 2207435 2208451 := bstep (se 1 (by rfl) ⟨1656338, by rfl⟩ : syracuseStep 2208451 = 3312677) B3312677
theorem B2795077 : Blo 2207435 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B3726769 : Blo 2207435 3726769 := bstep (se 2 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 3726769 = 2795077) B2795077
theorem B4969025 : Blo 2207435 4969025 := bstep (se 2 (by rfl) ⟨1863384, by rfl⟩ : syracuseStep 4969025 = 3726769) B3726769
theorem B3312683 : Blo 2207435 3312683 := bstep (se 1 (by rfl) ⟨2484512, by rfl⟩ : syracuseStep 3312683 = 4969025) B4969025
theorem B2208455 : Blo 2207435 2208455 := bstep (se 1 (by rfl) ⟨1656341, by rfl⟩ : syracuseStep 2208455 = 3312683) B3312683
theorem B2484517 : Blo 2207435 2484517 := bbase (se 4 (by rfl) ⟨232923, by rfl⟩ : syracuseStep 2484517 = 465847) (by norm_num)
theorem B3312689 : Blo 2207435 3312689 := bstep (se 2 (by rfl) ⟨1242258, by rfl⟩ : syracuseStep 3312689 = 2484517) B2484517
theorem B2208459 : Blo 2207435 2208459 := bstep (se 1 (by rfl) ⟨1656344, by rfl⟩ : syracuseStep 2208459 = 3312689) B3312689
theorem B3537533 : Blo 2207435 3537533 := bbase (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) (by norm_num)
theorem B9433421 : Blo 2207435 9433421 := bstep (se 3 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 9433421 = 3537533) B3537533
theorem B6288947 : Blo 2207435 6288947 := bstep (se 1 (by rfl) ⟨4716710, by rfl⟩ : syracuseStep 6288947 = 9433421) B9433421
theorem B4192631 : Blo 2207435 4192631 := bstep (se 1 (by rfl) ⟨3144473, by rfl⟩ : syracuseStep 4192631 = 6288947) B6288947
theorem B2795087 : Blo 2207435 2795087 := bstep (se 1 (by rfl) ⟨2096315, by rfl⟩ : syracuseStep 2795087 = 4192631) B4192631
theorem B7453565 : Blo 2207435 7453565 := bstep (se 3 (by rfl) ⟨1397543, by rfl⟩ : syracuseStep 7453565 = 2795087) B2795087
theorem B4969043 : Blo 2207435 4969043 := bstep (se 1 (by rfl) ⟨3726782, by rfl⟩ : syracuseStep 4969043 = 7453565) B7453565
theorem B3312695 : Blo 2207435 3312695 := bstep (se 1 (by rfl) ⟨2484521, by rfl⟩ : syracuseStep 3312695 = 4969043) B4969043
theorem B2208463 : Blo 2207435 2208463 := bstep (se 1 (by rfl) ⟨1656347, by rfl⟩ : syracuseStep 2208463 = 3312695) B3312695
theorem B3312701 : Blo 2207435 3312701 := bbase (se 3 (by rfl) ⟨621131, by rfl⟩ : syracuseStep 3312701 = 1242263) (by norm_num)
theorem B2208467 : Blo 2207435 2208467 := bstep (se 1 (by rfl) ⟨1656350, by rfl⟩ : syracuseStep 2208467 = 3312701) B3312701
theorem B4969061 : Blo 2207435 4969061 := bbase (se 4 (by rfl) ⟨465849, by rfl⟩ : syracuseStep 4969061 = 931699) (by norm_num)
theorem B3312707 : Blo 2207435 3312707 := bstep (se 1 (by rfl) ⟨2484530, by rfl⟩ : syracuseStep 3312707 = 4969061) B4969061
theorem B2208471 : Blo 2207435 2208471 := bstep (se 1 (by rfl) ⟨1656353, by rfl⟩ : syracuseStep 2208471 = 3312707) B3312707
theorem B5590205 : Blo 2207435 5590205 := bbase (se 3 (by rfl) ⟨1048163, by rfl⟩ : syracuseStep 5590205 = 2096327) (by norm_num)
theorem B3726803 : Blo 2207435 3726803 := bstep (se 1 (by rfl) ⟨2795102, by rfl⟩ : syracuseStep 3726803 = 5590205) B5590205
theorem B2484535 : Blo 2207435 2484535 := bstep (se 1 (by rfl) ⟨1863401, by rfl⟩ : syracuseStep 2484535 = 3726803) B3726803
theorem B3312713 : Blo 2207435 3312713 := bstep (se 2 (by rfl) ⟨1242267, by rfl⟩ : syracuseStep 3312713 = 2484535) B2484535
theorem B2208475 : Blo 2207435 2208475 := bstep (se 1 (by rfl) ⟨1656356, by rfl⟩ : syracuseStep 2208475 = 3312713) B3312713
theorem B4192661 : Blo 2207435 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B11180429 : Blo 2207435 11180429 := bstep (se 3 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 11180429 = 4192661) B4192661
theorem B7453619 : Blo 2207435 7453619 := bstep (se 1 (by rfl) ⟨5590214, by rfl⟩ : syracuseStep 7453619 = 11180429) B11180429
theorem B4969079 : Blo 2207435 4969079 := bstep (se 1 (by rfl) ⟨3726809, by rfl⟩ : syracuseStep 4969079 = 7453619) B7453619
theorem B3312719 : Blo 2207435 3312719 := bstep (se 1 (by rfl) ⟨2484539, by rfl⟩ : syracuseStep 3312719 = 4969079) B4969079
theorem B2208479 : Blo 2207435 2208479 := bstep (se 1 (by rfl) ⟨1656359, by rfl⟩ : syracuseStep 2208479 = 3312719) B3312719
theorem B3312725 : Blo 2207435 3312725 := bbase (se 8 (by rfl) ⟨19410, by rfl⟩ : syracuseStep 3312725 = 38821) (by norm_num)
theorem B2208483 : Blo 2207435 2208483 := bstep (se 1 (by rfl) ⟨1656362, by rfl⟩ : syracuseStep 2208483 = 3312725) B3312725
theorem B5306357 : Blo 2207435 5306357 := bbase (se 5 (by rfl) ⟨248735, by rfl⟩ : syracuseStep 5306357 = 497471) (by norm_num)
theorem B14150285 : Blo 2207435 14150285 := bstep (se 3 (by rfl) ⟨2653178, by rfl⟩ : syracuseStep 14150285 = 5306357) B5306357
theorem B9433523 : Blo 2207435 9433523 := bstep (se 1 (by rfl) ⟨7075142, by rfl⟩ : syracuseStep 9433523 = 14150285) B14150285
theorem B6289015 : Blo 2207435 6289015 := bstep (se 1 (by rfl) ⟨4716761, by rfl⟩ : syracuseStep 6289015 = 9433523) B9433523
theorem B8385353 : Blo 2207435 8385353 := bstep (se 2 (by rfl) ⟨3144507, by rfl⟩ : syracuseStep 8385353 = 6289015) B6289015
theorem B5590235 : Blo 2207435 5590235 := bstep (se 1 (by rfl) ⟨4192676, by rfl⟩ : syracuseStep 5590235 = 8385353) B8385353
theorem B3726823 : Blo 2207435 3726823 := bstep (se 1 (by rfl) ⟨2795117, by rfl⟩ : syracuseStep 3726823 = 5590235) B5590235
theorem B4969097 : Blo 2207435 4969097 := bstep (se 2 (by rfl) ⟨1863411, by rfl⟩ : syracuseStep 4969097 = 3726823) B3726823
theorem B3312731 : Blo 2207435 3312731 := bstep (se 1 (by rfl) ⟨2484548, by rfl⟩ : syracuseStep 3312731 = 4969097) B4969097
theorem B2208487 : Blo 2207435 2208487 := bstep (se 1 (by rfl) ⟨1656365, by rfl⟩ : syracuseStep 2208487 = 3312731) B3312731
theorem B2484553 : Blo 2207435 2484553 := bbase (se 2 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 2484553 = 1863415) (by norm_num)
theorem B3312737 : Blo 2207435 3312737 := bstep (se 2 (by rfl) ⟨1242276, by rfl⟩ : syracuseStep 3312737 = 2484553) B2484553
theorem B2208491 : Blo 2207435 2208491 := bstep (se 1 (by rfl) ⟨1656368, by rfl⟩ : syracuseStep 2208491 = 3312737) B3312737
theorem B5378773 : Blo 2207435 5378773 := bbase (se 7 (by rfl) ⟨63032, by rfl⟩ : syracuseStep 5378773 = 126065) (by norm_num)
theorem B7171697 : Blo 2207435 7171697 := bstep (se 2 (by rfl) ⟨2689386, by rfl⟩ : syracuseStep 7171697 = 5378773) B5378773
theorem B4781131 : Blo 2207435 4781131 := bstep (se 1 (by rfl) ⟨3585848, by rfl⟩ : syracuseStep 4781131 = 7171697) B7171697
theorem B101997461 : Blo 2207435 101997461 := bstep (se 6 (by rfl) ⟨2390565, by rfl⟩ : syracuseStep 101997461 = 4781131) B4781131
theorem B67998307 : Blo 2207435 67998307 := bstep (se 1 (by rfl) ⟨50998730, by rfl⟩ : syracuseStep 67998307 = 101997461) B101997461
theorem B90664409 : Blo 2207435 90664409 := bstep (se 2 (by rfl) ⟨33999153, by rfl⟩ : syracuseStep 90664409 = 67998307) B67998307
theorem B60442939 : Blo 2207435 60442939 := bstep (se 1 (by rfl) ⟨45332204, by rfl⟩ : syracuseStep 60442939 = 90664409) B90664409
theorem B80590585 : Blo 2207435 80590585 := bstep (se 2 (by rfl) ⟨30221469, by rfl⟩ : syracuseStep 80590585 = 60442939) B60442939
theorem B107454113 : Blo 2207435 107454113 := bstep (se 2 (by rfl) ⟨40295292, by rfl⟩ : syracuseStep 107454113 = 80590585) B80590585
theorem B71636075 : Blo 2207435 71636075 := bstep (se 1 (by rfl) ⟨53727056, by rfl⟩ : syracuseStep 71636075 = 107454113) B107454113
theorem B47757383 : Blo 2207435 47757383 := bstep (se 1 (by rfl) ⟨35818037, by rfl⟩ : syracuseStep 47757383 = 71636075) B71636075
theorem B31838255 : Blo 2207435 31838255 := bstep (se 1 (by rfl) ⟨23878691, by rfl⟩ : syracuseStep 31838255 = 47757383) B47757383
theorem B21225503 : Blo 2207435 21225503 := bstep (se 1 (by rfl) ⟨15919127, by rfl⟩ : syracuseStep 21225503 = 31838255) B31838255
theorem B14150335 : Blo 2207435 14150335 := bstep (se 1 (by rfl) ⟨10612751, by rfl⟩ : syracuseStep 14150335 = 21225503) B21225503
theorem B18867113 : Blo 2207435 18867113 := bstep (se 2 (by rfl) ⟨7075167, by rfl⟩ : syracuseStep 18867113 = 14150335) B14150335
theorem B12578075 : Blo 2207435 12578075 := bstep (se 1 (by rfl) ⟨9433556, by rfl⟩ : syracuseStep 12578075 = 18867113) B18867113
theorem B8385383 : Blo 2207435 8385383 := bstep (se 1 (by rfl) ⟨6289037, by rfl⟩ : syracuseStep 8385383 = 12578075) B12578075
theorem B5590255 : Blo 2207435 5590255 := bstep (se 1 (by rfl) ⟨4192691, by rfl⟩ : syracuseStep 5590255 = 8385383) B8385383
theorem B7453673 : Blo 2207435 7453673 := bstep (se 2 (by rfl) ⟨2795127, by rfl⟩ : syracuseStep 7453673 = 5590255) B5590255
theorem B4969115 : Blo 2207435 4969115 := bstep (se 1 (by rfl) ⟨3726836, by rfl⟩ : syracuseStep 4969115 = 7453673) B7453673
theorem B3312743 : Blo 2207435 3312743 := bstep (se 1 (by rfl) ⟨2484557, by rfl⟩ : syracuseStep 3312743 = 4969115) B4969115
theorem B2208495 : Blo 2207435 2208495 := bstep (se 1 (by rfl) ⟨1656371, by rfl⟩ : syracuseStep 2208495 = 3312743) B3312743
theorem B3312749 : Blo 2207435 3312749 := bbase (se 3 (by rfl) ⟨621140, by rfl⟩ : syracuseStep 3312749 = 1242281) (by norm_num)
theorem B2208499 : Blo 2207435 2208499 := bstep (se 1 (by rfl) ⟨1656374, by rfl⟩ : syracuseStep 2208499 = 3312749) B3312749
theorem B4969133 : Blo 2207435 4969133 := bbase (se 3 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 4969133 = 1863425) (by norm_num)
theorem B3312755 : Blo 2207435 3312755 := bstep (se 1 (by rfl) ⟨2484566, by rfl⟩ : syracuseStep 3312755 = 4969133) B4969133
theorem B2208503 : Blo 2207435 2208503 := bstep (se 1 (by rfl) ⟨1656377, by rfl⟩ : syracuseStep 2208503 = 3312755) B3312755
theorem B4716805 : Blo 2207435 4716805 := bbase (se 4 (by rfl) ⟨442200, by rfl⟩ : syracuseStep 4716805 = 884401) (by norm_num)
theorem B6289073 : Blo 2207435 6289073 := bstep (se 2 (by rfl) ⟨2358402, by rfl⟩ : syracuseStep 6289073 = 4716805) B4716805
theorem B4192715 : Blo 2207435 4192715 := bstep (se 1 (by rfl) ⟨3144536, by rfl⟩ : syracuseStep 4192715 = 6289073) B6289073
theorem B2795143 : Blo 2207435 2795143 := bstep (se 1 (by rfl) ⟨2096357, by rfl⟩ : syracuseStep 2795143 = 4192715) B4192715
theorem B3726857 : Blo 2207435 3726857 := bstep (se 2 (by rfl) ⟨1397571, by rfl⟩ : syracuseStep 3726857 = 2795143) B2795143
theorem B2484571 : Blo 2207435 2484571 := bstep (se 1 (by rfl) ⟨1863428, by rfl⟩ : syracuseStep 2484571 = 3726857) B3726857
theorem B3312761 : Blo 2207435 3312761 := bstep (se 2 (by rfl) ⟨1242285, by rfl⟩ : syracuseStep 3312761 = 2484571) B2484571
theorem B2208507 : Blo 2207435 2208507 := bstep (se 1 (by rfl) ⟨1656380, by rfl⟩ : syracuseStep 2208507 = 3312761) B3312761
theorem B4307909 : Blo 2207435 4307909 := bbase (se 4 (by rfl) ⟨403866, by rfl⟩ : syracuseStep 4307909 = 807733) (by norm_num)
theorem B11487757 : Blo 2207435 11487757 := bstep (se 3 (by rfl) ⟨2153954, by rfl⟩ : syracuseStep 11487757 = 4307909) B4307909
theorem B15317009 : Blo 2207435 15317009 := bstep (se 2 (by rfl) ⟨5743878, by rfl⟩ : syracuseStep 15317009 = 11487757) B11487757
theorem B10211339 : Blo 2207435 10211339 := bstep (se 1 (by rfl) ⟨7658504, by rfl⟩ : syracuseStep 10211339 = 15317009) B15317009
theorem B6807559 : Blo 2207435 6807559 := bstep (se 1 (by rfl) ⟨5105669, by rfl⟩ : syracuseStep 6807559 = 10211339) B10211339
theorem B9076745 : Blo 2207435 9076745 := bstep (se 2 (by rfl) ⟨3403779, by rfl⟩ : syracuseStep 9076745 = 6807559) B6807559
theorem B24204653 : Blo 2207435 24204653 := bstep (se 3 (by rfl) ⟨4538372, by rfl⟩ : syracuseStep 24204653 = 9076745) B9076745
theorem B16136435 : Blo 2207435 16136435 := bstep (se 1 (by rfl) ⟨12102326, by rfl⟩ : syracuseStep 16136435 = 24204653) B24204653
theorem B10757623 : Blo 2207435 10757623 := bstep (se 1 (by rfl) ⟨8068217, by rfl⟩ : syracuseStep 10757623 = 16136435) B16136435
theorem B14343497 : Blo 2207435 14343497 := bstep (se 2 (by rfl) ⟨5378811, by rfl⟩ : syracuseStep 14343497 = 10757623) B10757623
theorem B9562331 : Blo 2207435 9562331 := bstep (se 1 (by rfl) ⟨7171748, by rfl⟩ : syracuseStep 9562331 = 14343497) B14343497
theorem B25499549 : Blo 2207435 25499549 := bstep (se 3 (by rfl) ⟨4781165, by rfl⟩ : syracuseStep 25499549 = 9562331) B9562331
theorem B67998797 : Blo 2207435 67998797 := bstep (se 3 (by rfl) ⟨12749774, by rfl⟩ : syracuseStep 67998797 = 25499549) B25499549
theorem B45332531 : Blo 2207435 45332531 := bstep (se 1 (by rfl) ⟨33999398, by rfl⟩ : syracuseStep 45332531 = 67998797) B67998797
theorem B30221687 : Blo 2207435 30221687 := bstep (se 1 (by rfl) ⟨22666265, by rfl⟩ : syracuseStep 30221687 = 45332531) B45332531
theorem B20147791 : Blo 2207435 20147791 := bstep (se 1 (by rfl) ⟨15110843, by rfl⟩ : syracuseStep 20147791 = 30221687) B30221687
theorem B26863721 : Blo 2207435 26863721 := bstep (se 2 (by rfl) ⟨10073895, by rfl⟩ : syracuseStep 26863721 = 20147791) B20147791
theorem B17909147 : Blo 2207435 17909147 := bstep (se 1 (by rfl) ⟨13431860, by rfl⟩ : syracuseStep 17909147 = 26863721) B26863721
theorem B47757725 : Blo 2207435 47757725 := bstep (se 3 (by rfl) ⟨8954573, by rfl⟩ : syracuseStep 47757725 = 17909147) B17909147
theorem B31838483 : Blo 2207435 31838483 := bstep (se 1 (by rfl) ⟨23878862, by rfl⟩ : syracuseStep 31838483 = 47757725) B47757725
theorem B21225655 : Blo 2207435 21225655 := bstep (se 1 (by rfl) ⟨15919241, by rfl⟩ : syracuseStep 21225655 = 31838483) B31838483
theorem B28300873 : Blo 2207435 28300873 := bstep (se 2 (by rfl) ⟨10612827, by rfl⟩ : syracuseStep 28300873 = 21225655) B21225655
theorem B37734497 : Blo 2207435 37734497 := bstep (se 2 (by rfl) ⟨14150436, by rfl⟩ : syracuseStep 37734497 = 28300873) B28300873
theorem B25156331 : Blo 2207435 25156331 := bstep (se 1 (by rfl) ⟨18867248, by rfl⟩ : syracuseStep 25156331 = 37734497) B37734497
theorem B16770887 : Blo 2207435 16770887 := bstep (se 1 (by rfl) ⟨12578165, by rfl⟩ : syracuseStep 16770887 = 25156331) B25156331
theorem B11180591 : Blo 2207435 11180591 := bstep (se 1 (by rfl) ⟨8385443, by rfl⟩ : syracuseStep 11180591 = 16770887) B16770887
theorem B7453727 : Blo 2207435 7453727 := bstep (se 1 (by rfl) ⟨5590295, by rfl⟩ : syracuseStep 7453727 = 11180591) B11180591
theorem B4969151 : Blo 2207435 4969151 := bstep (se 1 (by rfl) ⟨3726863, by rfl⟩ : syracuseStep 4969151 = 7453727) B7453727
theorem B3312767 : Blo 2207435 3312767 := bstep (se 1 (by rfl) ⟨2484575, by rfl⟩ : syracuseStep 3312767 = 4969151) B4969151
theorem B2208511 : Blo 2207435 2208511 := bstep (se 1 (by rfl) ⟨1656383, by rfl⟩ : syracuseStep 2208511 = 3312767) B3312767
theorem B3312773 : Blo 2207435 3312773 := bbase (se 4 (by rfl) ⟨310572, by rfl⟩ : syracuseStep 3312773 = 621145) (by norm_num)
theorem B2208515 : Blo 2207435 2208515 := bstep (se 1 (by rfl) ⟨1656386, by rfl⟩ : syracuseStep 2208515 = 3312773) B3312773
theorem B3726877 : Blo 2207435 3726877 := bbase (se 3 (by rfl) ⟨698789, by rfl⟩ : syracuseStep 3726877 = 1397579) (by norm_num)
theorem B4969169 : Blo 2207435 4969169 := bstep (se 2 (by rfl) ⟨1863438, by rfl⟩ : syracuseStep 4969169 = 3726877) B3726877
theorem B3312779 : Blo 2207435 3312779 := bstep (se 1 (by rfl) ⟨2484584, by rfl⟩ : syracuseStep 3312779 = 4969169) B4969169
theorem B2208519 : Blo 2207435 2208519 := bstep (se 1 (by rfl) ⟨1656389, by rfl⟩ : syracuseStep 2208519 = 3312779) B3312779
theorem B2484589 : Blo 2207435 2484589 := bbase (se 3 (by rfl) ⟨465860, by rfl⟩ : syracuseStep 2484589 = 931721) (by norm_num)
theorem B3312785 : Blo 2207435 3312785 := bstep (se 2 (by rfl) ⟨1242294, by rfl⟩ : syracuseStep 3312785 = 2484589) B2484589
theorem B2208523 : Blo 2207435 2208523 := bstep (se 1 (by rfl) ⟨1656392, by rfl⟩ : syracuseStep 2208523 = 3312785) B3312785
theorem B7453781 : Blo 2207435 7453781 := bbase (se 8 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 7453781 = 87349) (by norm_num)
theorem B4969187 : Blo 2207435 4969187 := bstep (se 1 (by rfl) ⟨3726890, by rfl⟩ : syracuseStep 4969187 = 7453781) B7453781
theorem B3312791 : Blo 2207435 3312791 := bstep (se 1 (by rfl) ⟨2484593, by rfl⟩ : syracuseStep 3312791 = 4969187) B4969187
theorem B2208527 : Blo 2207435 2208527 := bstep (se 1 (by rfl) ⟨1656395, by rfl⟩ : syracuseStep 2208527 = 3312791) B3312791
theorem B3312797 : Blo 2207435 3312797 := bbase (se 3 (by rfl) ⟨621149, by rfl⟩ : syracuseStep 3312797 = 1242299) (by norm_num)
theorem B2208531 : Blo 2207435 2208531 := bstep (se 1 (by rfl) ⟨1656398, by rfl⟩ : syracuseStep 2208531 = 3312797) B3312797
theorem B4969205 : Blo 2207435 4969205 := bbase (se 5 (by rfl) ⟨232931, by rfl⟩ : syracuseStep 4969205 = 465863) (by norm_num)
theorem B3312803 : Blo 2207435 3312803 := bstep (se 1 (by rfl) ⟨2484602, by rfl⟩ : syracuseStep 3312803 = 4969205) B4969205
theorem B2208535 : Blo 2207435 2208535 := bstep (se 1 (by rfl) ⟨1656401, by rfl⟩ : syracuseStep 2208535 = 3312803) B3312803
theorem B2653241 : Blo 2207435 2653241 := bbase (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) (by norm_num)
theorem B28301237 : Blo 2207435 28301237 := bstep (se 5 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 28301237 = 2653241) B2653241
theorem B18867491 : Blo 2207435 18867491 := bstep (se 1 (by rfl) ⟨14150618, by rfl⟩ : syracuseStep 18867491 = 28301237) B28301237
theorem B12578327 : Blo 2207435 12578327 := bstep (se 1 (by rfl) ⟨9433745, by rfl⟩ : syracuseStep 12578327 = 18867491) B18867491
theorem B8385551 : Blo 2207435 8385551 := bstep (se 1 (by rfl) ⟨6289163, by rfl⟩ : syracuseStep 8385551 = 12578327) B12578327
theorem B5590367 : Blo 2207435 5590367 := bstep (se 1 (by rfl) ⟨4192775, by rfl⟩ : syracuseStep 5590367 = 8385551) B8385551
theorem B3726911 : Blo 2207435 3726911 := bstep (se 1 (by rfl) ⟨2795183, by rfl⟩ : syracuseStep 3726911 = 5590367) B5590367
theorem B2484607 : Blo 2207435 2484607 := bstep (se 1 (by rfl) ⟨1863455, by rfl⟩ : syracuseStep 2484607 = 3726911) B3726911
theorem B3312809 : Blo 2207435 3312809 := bstep (se 2 (by rfl) ⟨1242303, by rfl⟩ : syracuseStep 3312809 = 2484607) B2484607
theorem B2208539 : Blo 2207435 2208539 := bstep (se 1 (by rfl) ⟨1656404, by rfl⟩ : syracuseStep 2208539 = 3312809) B3312809
theorem B3537661 : Blo 2207435 3537661 := bbase (se 3 (by rfl) ⟨663311, by rfl⟩ : syracuseStep 3537661 = 1326623) (by norm_num)
theorem B4716881 : Blo 2207435 4716881 := bstep (se 2 (by rfl) ⟨1768830, by rfl⟩ : syracuseStep 4716881 = 3537661) B3537661
theorem B3144587 : Blo 2207435 3144587 := bstep (se 1 (by rfl) ⟨2358440, by rfl⟩ : syracuseStep 3144587 = 4716881) B4716881
theorem B8385565 : Blo 2207435 8385565 := bstep (se 3 (by rfl) ⟨1572293, by rfl⟩ : syracuseStep 8385565 = 3144587) B3144587
theorem B11180753 : Blo 2207435 11180753 := bstep (se 2 (by rfl) ⟨4192782, by rfl⟩ : syracuseStep 11180753 = 8385565) B8385565
theorem B7453835 : Blo 2207435 7453835 := bstep (se 1 (by rfl) ⟨5590376, by rfl⟩ : syracuseStep 7453835 = 11180753) B11180753
theorem B4969223 : Blo 2207435 4969223 := bstep (se 1 (by rfl) ⟨3726917, by rfl⟩ : syracuseStep 4969223 = 7453835) B7453835
theorem B3312815 : Blo 2207435 3312815 := bstep (se 1 (by rfl) ⟨2484611, by rfl⟩ : syracuseStep 3312815 = 4969223) B4969223
theorem B2208543 : Blo 2207435 2208543 := bstep (se 1 (by rfl) ⟨1656407, by rfl⟩ : syracuseStep 2208543 = 3312815) B3312815
theorem B3312821 : Blo 2207435 3312821 := bbase (se 5 (by rfl) ⟨155288, by rfl⟩ : syracuseStep 3312821 = 310577) (by norm_num)
theorem B2208547 : Blo 2207435 2208547 := bstep (se 1 (by rfl) ⟨1656410, by rfl⟩ : syracuseStep 2208547 = 3312821) B3312821
theorem B5590397 : Blo 2207435 5590397 := bbase (se 3 (by rfl) ⟨1048199, by rfl⟩ : syracuseStep 5590397 = 2096399) (by norm_num)
theorem B3726931 : Blo 2207435 3726931 := bstep (se 1 (by rfl) ⟨2795198, by rfl⟩ : syracuseStep 3726931 = 5590397) B5590397
theorem B4969241 : Blo 2207435 4969241 := bstep (se 2 (by rfl) ⟨1863465, by rfl⟩ : syracuseStep 4969241 = 3726931) B3726931
theorem B3312827 : Blo 2207435 3312827 := bstep (se 1 (by rfl) ⟨2484620, by rfl⟩ : syracuseStep 3312827 = 4969241) B4969241
theorem B2208551 : Blo 2207435 2208551 := bstep (se 1 (by rfl) ⟨1656413, by rfl⟩ : syracuseStep 2208551 = 3312827) B3312827
theorem B2484625 : Blo 2207435 2484625 := bbase (se 2 (by rfl) ⟨931734, by rfl⟩ : syracuseStep 2484625 = 1863469) (by norm_num)
theorem B3312833 : Blo 2207435 3312833 := bstep (se 2 (by rfl) ⟨1242312, by rfl⟩ : syracuseStep 3312833 = 2484625) B2484625
theorem B2208555 : Blo 2207435 2208555 := bstep (se 1 (by rfl) ⟨1656416, by rfl⟩ : syracuseStep 2208555 = 3312833) B3312833
theorem B4192813 : Blo 2207435 4192813 := bbase (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) (by norm_num)
theorem B5590417 : Blo 2207435 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B7453889 : Blo 2207435 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B4969259 : Blo 2207435 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B3312839 : Blo 2207435 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B2208559 : Blo 2207435 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B3312845 : Blo 2207435 3312845 := bbase (se 3 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 3312845 = 1242317) (by norm_num)
theorem B2208563 : Blo 2207435 2208563 := bstep (se 1 (by rfl) ⟨1656422, by rfl⟩ : syracuseStep 2208563 = 3312845) B3312845
theorem B4969277 : Blo 2207435 4969277 := bbase (se 3 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 4969277 = 1863479) (by norm_num)
theorem B3312851 : Blo 2207435 3312851 := bstep (se 1 (by rfl) ⟨2484638, by rfl⟩ : syracuseStep 3312851 = 4969277) B4969277
theorem B2208567 : Blo 2207435 2208567 := bstep (se 1 (by rfl) ⟨1656425, by rfl⟩ : syracuseStep 2208567 = 3312851) B3312851
theorem B3726965 : Blo 2207435 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B2484643 : Blo 2207435 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B3312857 : Blo 2207435 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B2208571 : Blo 2207435 2208571 := bstep (se 1 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 2208571 = 3312857) B3312857
theorem B4716949 : Blo 2207435 4716949 := bbase (se 6 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 4716949 = 221107) (by norm_num)
theorem B6289265 : Blo 2207435 6289265 := bstep (se 2 (by rfl) ⟨2358474, by rfl⟩ : syracuseStep 6289265 = 4716949) B4716949
theorem B16771373 : Blo 2207435 16771373 := bstep (se 3 (by rfl) ⟨3144632, by rfl⟩ : syracuseStep 16771373 = 6289265) B6289265
theorem B11180915 : Blo 2207435 11180915 := bstep (se 1 (by rfl) ⟨8385686, by rfl⟩ : syracuseStep 11180915 = 16771373) B16771373
theorem B7453943 : Blo 2207435 7453943 := bstep (se 1 (by rfl) ⟨5590457, by rfl⟩ : syracuseStep 7453943 = 11180915) B11180915
theorem B4969295 : Blo 2207435 4969295 := bstep (se 1 (by rfl) ⟨3726971, by rfl⟩ : syracuseStep 4969295 = 7453943) B7453943
theorem B3312863 : Blo 2207435 3312863 := bstep (se 1 (by rfl) ⟨2484647, by rfl⟩ : syracuseStep 3312863 = 4969295) B4969295
theorem B2208575 : Blo 2207435 2208575 := bstep (se 1 (by rfl) ⟨1656431, by rfl⟩ : syracuseStep 2208575 = 3312863) B3312863
theorem B3312869 : Blo 2207435 3312869 := bbase (se 4 (by rfl) ⟨310581, by rfl⟩ : syracuseStep 3312869 = 621163) (by norm_num)
theorem B2208579 : Blo 2207435 2208579 := bstep (se 1 (by rfl) ⟨1656434, by rfl⟩ : syracuseStep 2208579 = 3312869) B3312869
theorem B8954869 : Blo 2207435 8954869 := bbase (se 5 (by rfl) ⟨419759, by rfl⟩ : syracuseStep 8954869 = 839519) (by norm_num)
theorem B11939825 : Blo 2207435 11939825 := bstep (se 2 (by rfl) ⟨4477434, by rfl⟩ : syracuseStep 11939825 = 8954869) B8954869
theorem B7959883 : Blo 2207435 7959883 := bstep (se 1 (by rfl) ⟨5969912, by rfl⟩ : syracuseStep 7959883 = 11939825) B11939825
theorem B10613177 : Blo 2207435 10613177 := bstep (se 2 (by rfl) ⟨3979941, by rfl⟩ : syracuseStep 10613177 = 7959883) B7959883
theorem B7075451 : Blo 2207435 7075451 := bstep (se 1 (by rfl) ⟨5306588, by rfl⟩ : syracuseStep 7075451 = 10613177) B10613177
theorem B4716967 : Blo 2207435 4716967 := bstep (se 1 (by rfl) ⟨3537725, by rfl⟩ : syracuseStep 4716967 = 7075451) B7075451
theorem B6289289 : Blo 2207435 6289289 := bstep (se 2 (by rfl) ⟨2358483, by rfl⟩ : syracuseStep 6289289 = 4716967) B4716967
theorem B4192859 : Blo 2207435 4192859 := bstep (se 1 (by rfl) ⟨3144644, by rfl⟩ : syracuseStep 4192859 = 6289289) B6289289
theorem B2795239 : Blo 2207435 2795239 := bstep (se 1 (by rfl) ⟨2096429, by rfl⟩ : syracuseStep 2795239 = 4192859) B4192859
theorem B3726985 : Blo 2207435 3726985 := bstep (se 2 (by rfl) ⟨1397619, by rfl⟩ : syracuseStep 3726985 = 2795239) B2795239
theorem B4969313 : Blo 2207435 4969313 := bstep (se 2 (by rfl) ⟨1863492, by rfl⟩ : syracuseStep 4969313 = 3726985) B3726985
theorem B3312875 : Blo 2207435 3312875 := bstep (se 1 (by rfl) ⟨2484656, by rfl⟩ : syracuseStep 3312875 = 4969313) B4969313
theorem B2208583 : Blo 2207435 2208583 := bstep (se 1 (by rfl) ⟨1656437, by rfl⟩ : syracuseStep 2208583 = 3312875) B3312875
theorem B2484661 : Blo 2207435 2484661 := bbase (se 5 (by rfl) ⟨116468, by rfl⟩ : syracuseStep 2484661 = 232937) (by norm_num)
theorem B3312881 : Blo 2207435 3312881 := bstep (se 2 (by rfl) ⟨1242330, by rfl⟩ : syracuseStep 3312881 = 2484661) B2484661
theorem B2208587 : Blo 2207435 2208587 := bstep (se 1 (by rfl) ⟨1656440, by rfl⟩ : syracuseStep 2208587 = 3312881) B3312881
theorem B2795249 : Blo 2207435 2795249 := bbase (se 2 (by rfl) ⟨1048218, by rfl⟩ : syracuseStep 2795249 = 2096437) (by norm_num)
theorem B7453997 : Blo 2207435 7453997 := bstep (se 3 (by rfl) ⟨1397624, by rfl⟩ : syracuseStep 7453997 = 2795249) B2795249
theorem B4969331 : Blo 2207435 4969331 := bstep (se 1 (by rfl) ⟨3726998, by rfl⟩ : syracuseStep 4969331 = 7453997) B7453997
theorem B3312887 : Blo 2207435 3312887 := bstep (se 1 (by rfl) ⟨2484665, by rfl⟩ : syracuseStep 3312887 = 4969331) B4969331
theorem B2208591 : Blo 2207435 2208591 := bstep (se 1 (by rfl) ⟨1656443, by rfl⟩ : syracuseStep 2208591 = 3312887) B3312887
theorem B3312893 : Blo 2207435 3312893 := bbase (se 3 (by rfl) ⟨621167, by rfl⟩ : syracuseStep 3312893 = 1242335) (by norm_num)
theorem B2208595 : Blo 2207435 2208595 := bstep (se 1 (by rfl) ⟨1656446, by rfl⟩ : syracuseStep 2208595 = 3312893) B3312893
theorem B4969349 : Blo 2207435 4969349 := bbase (se 4 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 4969349 = 931753) (by norm_num)
theorem B3312899 : Blo 2207435 3312899 := bstep (se 1 (by rfl) ⟨2484674, by rfl⟩ : syracuseStep 3312899 = 4969349) B4969349
theorem B2208599 : Blo 2207435 2208599 := bstep (se 1 (by rfl) ⟨1656449, by rfl⟩ : syracuseStep 2208599 = 3312899) B3312899
theorem B2358505 : Blo 2207435 2358505 := bbase (se 2 (by rfl) ⟨884439, by rfl⟩ : syracuseStep 2358505 = 1768879) (by norm_num)
theorem B3144673 : Blo 2207435 3144673 := bstep (se 2 (by rfl) ⟨1179252, by rfl⟩ : syracuseStep 3144673 = 2358505) B2358505
theorem B4192897 : Blo 2207435 4192897 := bstep (se 2 (by rfl) ⟨1572336, by rfl⟩ : syracuseStep 4192897 = 3144673) B3144673
theorem B5590529 : Blo 2207435 5590529 := bstep (se 2 (by rfl) ⟨2096448, by rfl⟩ : syracuseStep 5590529 = 4192897) B4192897
theorem B3727019 : Blo 2207435 3727019 := bstep (se 1 (by rfl) ⟨2795264, by rfl⟩ : syracuseStep 3727019 = 5590529) B5590529
theorem B2484679 : Blo 2207435 2484679 := bstep (se 1 (by rfl) ⟨1863509, by rfl⟩ : syracuseStep 2484679 = 3727019) B3727019
theorem B3312905 : Blo 2207435 3312905 := bstep (se 2 (by rfl) ⟨1242339, by rfl⟩ : syracuseStep 3312905 = 2484679) B2484679
theorem B2208603 : Blo 2207435 2208603 := bstep (se 1 (by rfl) ⟨1656452, by rfl⟩ : syracuseStep 2208603 = 3312905) B3312905
theorem B11181077 : Blo 2207435 11181077 := bbase (se 6 (by rfl) ⟨262056, by rfl⟩ : syracuseStep 11181077 = 524113) (by norm_num)
theorem B7454051 : Blo 2207435 7454051 := bstep (se 1 (by rfl) ⟨5590538, by rfl⟩ : syracuseStep 7454051 = 11181077) B11181077
theorem B4969367 : Blo 2207435 4969367 := bstep (se 1 (by rfl) ⟨3727025, by rfl⟩ : syracuseStep 4969367 = 7454051) B7454051
theorem B3312911 : Blo 2207435 3312911 := bstep (se 1 (by rfl) ⟨2484683, by rfl⟩ : syracuseStep 3312911 = 4969367) B4969367
theorem B2208607 : Blo 2207435 2208607 := bstep (se 1 (by rfl) ⟨1656455, by rfl⟩ : syracuseStep 2208607 = 3312911) B3312911
theorem B3312917 : Blo 2207435 3312917 := bbase (se 6 (by rfl) ⟨77646, by rfl⟩ : syracuseStep 3312917 = 155293) (by norm_num)
theorem B2208611 : Blo 2207435 2208611 := bstep (se 1 (by rfl) ⟨1656458, by rfl⟩ : syracuseStep 2208611 = 3312917) B3312917
theorem B22976597 : Blo 2207435 22976597 := bbase (se 8 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 22976597 = 269257) (by norm_num)
theorem B15317731 : Blo 2207435 15317731 := bstep (se 1 (by rfl) ⟨11488298, by rfl⟩ : syracuseStep 15317731 = 22976597) B22976597
theorem B81694565 : Blo 2207435 81694565 := bstep (se 4 (by rfl) ⟨7658865, by rfl⟩ : syracuseStep 81694565 = 15317731) B15317731
theorem B54463043 : Blo 2207435 54463043 := bstep (se 1 (by rfl) ⟨40847282, by rfl⟩ : syracuseStep 54463043 = 81694565) B81694565
theorem B36308695 : Blo 2207435 36308695 := bstep (se 1 (by rfl) ⟨27231521, by rfl⟩ : syracuseStep 36308695 = 54463043) B54463043
theorem B48411593 : Blo 2207435 48411593 := bstep (se 2 (by rfl) ⟨18154347, by rfl⟩ : syracuseStep 48411593 = 36308695) B36308695
theorem B32274395 : Blo 2207435 32274395 := bstep (se 1 (by rfl) ⟨24205796, by rfl⟩ : syracuseStep 32274395 = 48411593) B48411593
theorem B21516263 : Blo 2207435 21516263 := bstep (se 1 (by rfl) ⟨16137197, by rfl⟩ : syracuseStep 21516263 = 32274395) B32274395
theorem B14344175 : Blo 2207435 14344175 := bstep (se 1 (by rfl) ⟨10758131, by rfl⟩ : syracuseStep 14344175 = 21516263) B21516263
theorem B9562783 : Blo 2207435 9562783 := bstep (se 1 (by rfl) ⟨7172087, by rfl⟩ : syracuseStep 9562783 = 14344175) B14344175
theorem B12750377 : Blo 2207435 12750377 := bstep (se 2 (by rfl) ⟨4781391, by rfl⟩ : syracuseStep 12750377 = 9562783) B9562783
theorem B34001005 : Blo 2207435 34001005 := bstep (se 3 (by rfl) ⟨6375188, by rfl⟩ : syracuseStep 34001005 = 12750377) B12750377
theorem B45334673 : Blo 2207435 45334673 := bstep (se 2 (by rfl) ⟨17000502, by rfl⟩ : syracuseStep 45334673 = 34001005) B34001005
theorem B30223115 : Blo 2207435 30223115 := bstep (se 1 (by rfl) ⟨22667336, by rfl⟩ : syracuseStep 30223115 = 45334673) B45334673
theorem B20148743 : Blo 2207435 20148743 := bstep (se 1 (by rfl) ⟨15111557, by rfl⟩ : syracuseStep 20148743 = 30223115) B30223115
theorem B13432495 : Blo 2207435 13432495 := bstep (se 1 (by rfl) ⟨10074371, by rfl⟩ : syracuseStep 13432495 = 20148743) B20148743
theorem B17909993 : Blo 2207435 17909993 := bstep (se 2 (by rfl) ⟨6716247, by rfl⟩ : syracuseStep 17909993 = 13432495) B13432495
theorem B11939995 : Blo 2207435 11939995 := bstep (se 1 (by rfl) ⟨8954996, by rfl⟩ : syracuseStep 11939995 = 17909993) B17909993
theorem B15919993 : Blo 2207435 15919993 := bstep (se 2 (by rfl) ⟨5969997, by rfl⟩ : syracuseStep 15919993 = 11939995) B11939995
theorem B21226657 : Blo 2207435 21226657 := bstep (se 2 (by rfl) ⟨7959996, by rfl⟩ : syracuseStep 21226657 = 15919993) B15919993
theorem B28302209 : Blo 2207435 28302209 := bstep (se 2 (by rfl) ⟨10613328, by rfl⟩ : syracuseStep 28302209 = 21226657) B21226657
theorem B18868139 : Blo 2207435 18868139 := bstep (se 1 (by rfl) ⟨14151104, by rfl⟩ : syracuseStep 18868139 = 28302209) B28302209
theorem B12578759 : Blo 2207435 12578759 := bstep (se 1 (by rfl) ⟨9434069, by rfl⟩ : syracuseStep 12578759 = 18868139) B18868139
theorem B8385839 : Blo 2207435 8385839 := bstep (se 1 (by rfl) ⟨6289379, by rfl⟩ : syracuseStep 8385839 = 12578759) B12578759
theorem B5590559 : Blo 2207435 5590559 := bstep (se 1 (by rfl) ⟨4192919, by rfl⟩ : syracuseStep 5590559 = 8385839) B8385839
theorem B3727039 : Blo 2207435 3727039 := bstep (se 1 (by rfl) ⟨2795279, by rfl⟩ : syracuseStep 3727039 = 5590559) B5590559
theorem B4969385 : Blo 2207435 4969385 := bstep (se 2 (by rfl) ⟨1863519, by rfl⟩ : syracuseStep 4969385 = 3727039) B3727039
theorem B3312923 : Blo 2207435 3312923 := bstep (se 1 (by rfl) ⟨2484692, by rfl⟩ : syracuseStep 3312923 = 4969385) B4969385
theorem B2208615 : Blo 2207435 2208615 := bstep (se 1 (by rfl) ⟨1656461, by rfl⟩ : syracuseStep 2208615 = 3312923) B3312923
theorem B2484697 : Blo 2207435 2484697 := bbase (se 2 (by rfl) ⟨931761, by rfl⟩ : syracuseStep 2484697 = 1863523) (by norm_num)
theorem B3312929 : Blo 2207435 3312929 := bstep (se 2 (by rfl) ⟨1242348, by rfl⟩ : syracuseStep 3312929 = 2484697) B2484697
theorem B2208619 : Blo 2207435 2208619 := bstep (se 1 (by rfl) ⟨1656464, by rfl⟩ : syracuseStep 2208619 = 3312929) B3312929
theorem B3144701 : Blo 2207435 3144701 := bbase (se 3 (by rfl) ⟨589631, by rfl⟩ : syracuseStep 3144701 = 1179263) (by norm_num)
theorem B8385869 : Blo 2207435 8385869 := bstep (se 3 (by rfl) ⟨1572350, by rfl⟩ : syracuseStep 8385869 = 3144701) B3144701
theorem B5590579 : Blo 2207435 5590579 := bstep (se 1 (by rfl) ⟨4192934, by rfl⟩ : syracuseStep 5590579 = 8385869) B8385869
theorem B7454105 : Blo 2207435 7454105 := bstep (se 2 (by rfl) ⟨2795289, by rfl⟩ : syracuseStep 7454105 = 5590579) B5590579
theorem B4969403 : Blo 2207435 4969403 := bstep (se 1 (by rfl) ⟨3727052, by rfl⟩ : syracuseStep 4969403 = 7454105) B7454105
theorem B3312935 : Blo 2207435 3312935 := bstep (se 1 (by rfl) ⟨2484701, by rfl⟩ : syracuseStep 3312935 = 4969403) B4969403
theorem B2208623 : Blo 2207435 2208623 := bstep (se 1 (by rfl) ⟨1656467, by rfl⟩ : syracuseStep 2208623 = 3312935) B3312935
theorem B3312941 : Blo 2207435 3312941 := bbase (se 3 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 3312941 = 1242353) (by norm_num)
theorem B2208627 : Blo 2207435 2208627 := bstep (se 1 (by rfl) ⟨1656470, by rfl⟩ : syracuseStep 2208627 = 3312941) B3312941
theorem B4969421 : Blo 2207435 4969421 := bbase (se 3 (by rfl) ⟨931766, by rfl⟩ : syracuseStep 4969421 = 1863533) (by norm_num)
theorem B3312947 : Blo 2207435 3312947 := bstep (se 1 (by rfl) ⟨2484710, by rfl⟩ : syracuseStep 3312947 = 4969421) B4969421
theorem B2208631 : Blo 2207435 2208631 := bstep (se 1 (by rfl) ⟨1656473, by rfl⟩ : syracuseStep 2208631 = 3312947) B3312947
theorem B2795305 : Blo 2207435 2795305 := bbase (se 2 (by rfl) ⟨1048239, by rfl⟩ : syracuseStep 2795305 = 2096479) (by norm_num)
theorem B3727073 : Blo 2207435 3727073 := bstep (se 2 (by rfl) ⟨1397652, by rfl⟩ : syracuseStep 3727073 = 2795305) B2795305
theorem B2484715 : Blo 2207435 2484715 := bstep (se 1 (by rfl) ⟨1863536, by rfl⟩ : syracuseStep 2484715 = 3727073) B3727073
theorem B3312953 : Blo 2207435 3312953 := bstep (se 2 (by rfl) ⟨1242357, by rfl⟩ : syracuseStep 3312953 = 2484715) B2484715
theorem B2208635 : Blo 2207435 2208635 := bstep (se 1 (by rfl) ⟨1656476, by rfl⟩ : syracuseStep 2208635 = 3312953) B3312953
theorem B4250173 : Blo 2207435 4250173 := bbase (se 3 (by rfl) ⟨796907, by rfl⟩ : syracuseStep 4250173 = 1593815) (by norm_num)
theorem B5666897 : Blo 2207435 5666897 := bstep (se 2 (by rfl) ⟨2125086, by rfl⟩ : syracuseStep 5666897 = 4250173) B4250173
theorem B3777931 : Blo 2207435 3777931 := bstep (se 1 (by rfl) ⟨2833448, by rfl⟩ : syracuseStep 3777931 = 5666897) B5666897
theorem B5037241 : Blo 2207435 5037241 := bstep (se 2 (by rfl) ⟨1888965, by rfl⟩ : syracuseStep 5037241 = 3777931) B3777931
theorem B6716321 : Blo 2207435 6716321 := bstep (se 2 (by rfl) ⟨2518620, by rfl⟩ : syracuseStep 6716321 = 5037241) B5037241
theorem B4477547 : Blo 2207435 4477547 := bstep (se 1 (by rfl) ⟨3358160, by rfl⟩ : syracuseStep 4477547 = 6716321) B6716321
theorem B2985031 : Blo 2207435 2985031 := bstep (se 1 (by rfl) ⟨2238773, by rfl⟩ : syracuseStep 2985031 = 4477547) B4477547
theorem B15920165 : Blo 2207435 15920165 := bstep (se 4 (by rfl) ⟨1492515, by rfl⟩ : syracuseStep 15920165 = 2985031) B2985031
theorem B10613443 : Blo 2207435 10613443 := bstep (se 1 (by rfl) ⟨7960082, by rfl⟩ : syracuseStep 10613443 = 15920165) B15920165
theorem B14151257 : Blo 2207435 14151257 := bstep (se 2 (by rfl) ⟨5306721, by rfl⟩ : syracuseStep 14151257 = 10613443) B10613443
theorem B9434171 : Blo 2207435 9434171 := bstep (se 1 (by rfl) ⟨7075628, by rfl⟩ : syracuseStep 9434171 = 14151257) B14151257
theorem B25157789 : Blo 2207435 25157789 := bstep (se 3 (by rfl) ⟨4717085, by rfl⟩ : syracuseStep 25157789 = 9434171) B9434171
theorem B16771859 : Blo 2207435 16771859 := bstep (se 1 (by rfl) ⟨12578894, by rfl⟩ : syracuseStep 16771859 = 25157789) B25157789
theorem B11181239 : Blo 2207435 11181239 := bstep (se 1 (by rfl) ⟨8385929, by rfl⟩ : syracuseStep 11181239 = 16771859) B16771859
theorem B7454159 : Blo 2207435 7454159 := bstep (se 1 (by rfl) ⟨5590619, by rfl⟩ : syracuseStep 7454159 = 11181239) B11181239
theorem B4969439 : Blo 2207435 4969439 := bstep (se 1 (by rfl) ⟨3727079, by rfl⟩ : syracuseStep 4969439 = 7454159) B7454159
theorem B3312959 : Blo 2207435 3312959 := bstep (se 1 (by rfl) ⟨2484719, by rfl⟩ : syracuseStep 3312959 = 4969439) B4969439
theorem B2208639 : Blo 2207435 2208639 := bstep (se 1 (by rfl) ⟨1656479, by rfl⟩ : syracuseStep 2208639 = 3312959) B3312959
theorem B3312965 : Blo 2207435 3312965 := bbase (se 4 (by rfl) ⟨310590, by rfl⟩ : syracuseStep 3312965 = 621181) (by norm_num)
theorem B2208643 : Blo 2207435 2208643 := bstep (se 1 (by rfl) ⟨1656482, by rfl⟩ : syracuseStep 2208643 = 3312965) B3312965
theorem B3727093 : Blo 2207435 3727093 := bbase (se 5 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 3727093 = 349415) (by norm_num)
theorem B4969457 : Blo 2207435 4969457 := bstep (se 2 (by rfl) ⟨1863546, by rfl⟩ : syracuseStep 4969457 = 3727093) B3727093
theorem B3312971 : Blo 2207435 3312971 := bstep (se 1 (by rfl) ⟨2484728, by rfl⟩ : syracuseStep 3312971 = 4969457) B4969457
theorem B2208647 : Blo 2207435 2208647 := bstep (se 1 (by rfl) ⟨1656485, by rfl⟩ : syracuseStep 2208647 = 3312971) B3312971
theorem B2484733 : Blo 2207435 2484733 := bbase (se 3 (by rfl) ⟨465887, by rfl⟩ : syracuseStep 2484733 = 931775) (by norm_num)
theorem B3312977 : Blo 2207435 3312977 := bstep (se 2 (by rfl) ⟨1242366, by rfl⟩ : syracuseStep 3312977 = 2484733) B2484733
theorem B2208651 : Blo 2207435 2208651 := bstep (se 1 (by rfl) ⟨1656488, by rfl⟩ : syracuseStep 2208651 = 3312977) B3312977
theorem B7454213 : Blo 2207435 7454213 := bbase (se 4 (by rfl) ⟨698832, by rfl⟩ : syracuseStep 7454213 = 1397665) (by norm_num)
theorem B4969475 : Blo 2207435 4969475 := bstep (se 1 (by rfl) ⟨3727106, by rfl⟩ : syracuseStep 4969475 = 7454213) B7454213
theorem B3312983 : Blo 2207435 3312983 := bstep (se 1 (by rfl) ⟨2484737, by rfl⟩ : syracuseStep 3312983 = 4969475) B4969475
theorem B2208655 : Blo 2207435 2208655 := bstep (se 1 (by rfl) ⟨1656491, by rfl⟩ : syracuseStep 2208655 = 3312983) B3312983
theorem B3312989 : Blo 2207435 3312989 := bbase (se 3 (by rfl) ⟨621185, by rfl⟩ : syracuseStep 3312989 = 1242371) (by norm_num)
theorem B2208659 : Blo 2207435 2208659 := bstep (se 1 (by rfl) ⟨1656494, by rfl⟩ : syracuseStep 2208659 = 3312989) B3312989
theorem B4969493 : Blo 2207435 4969493 := bbase (se 6 (by rfl) ⟨116472, by rfl⟩ : syracuseStep 4969493 = 232945) (by norm_num)
theorem B3312995 : Blo 2207435 3312995 := bstep (se 1 (by rfl) ⟨2484746, by rfl⟩ : syracuseStep 3312995 = 4969493) B4969493
theorem B2208663 : Blo 2207435 2208663 := bstep (se 1 (by rfl) ⟨1656497, by rfl⟩ : syracuseStep 2208663 = 3312995) B3312995
theorem B8386037 : Blo 2207435 8386037 := bbase (se 5 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 8386037 = 786191) (by norm_num)
theorem B5590691 : Blo 2207435 5590691 := bstep (se 1 (by rfl) ⟨4193018, by rfl⟩ : syracuseStep 5590691 = 8386037) B8386037
theorem B3727127 : Blo 2207435 3727127 := bstep (se 1 (by rfl) ⟨2795345, by rfl⟩ : syracuseStep 3727127 = 5590691) B5590691
theorem B2484751 : Blo 2207435 2484751 := bstep (se 1 (by rfl) ⟨1863563, by rfl⟩ : syracuseStep 2484751 = 3727127) B3727127
theorem B3313001 : Blo 2207435 3313001 := bstep (se 2 (by rfl) ⟨1242375, by rfl⟩ : syracuseStep 3313001 = 2484751) B2484751
theorem B2208667 : Blo 2207435 2208667 := bstep (se 1 (by rfl) ⟨1656500, by rfl⟩ : syracuseStep 2208667 = 3313001) B3313001
theorem B2358577 : Blo 2207435 2358577 := bbase (se 2 (by rfl) ⟨884466, by rfl⟩ : syracuseStep 2358577 = 1768933) (by norm_num)
theorem B12579077 : Blo 2207435 12579077 := bstep (se 4 (by rfl) ⟨1179288, by rfl⟩ : syracuseStep 12579077 = 2358577) B2358577
theorem B8386051 : Blo 2207435 8386051 := bstep (se 1 (by rfl) ⟨6289538, by rfl⟩ : syracuseStep 8386051 = 12579077) B12579077
theorem B11181401 : Blo 2207435 11181401 := bstep (se 2 (by rfl) ⟨4193025, by rfl⟩ : syracuseStep 11181401 = 8386051) B8386051
theorem B7454267 : Blo 2207435 7454267 := bstep (se 1 (by rfl) ⟨5590700, by rfl⟩ : syracuseStep 7454267 = 11181401) B11181401
theorem B4969511 : Blo 2207435 4969511 := bstep (se 1 (by rfl) ⟨3727133, by rfl⟩ : syracuseStep 4969511 = 7454267) B7454267
theorem B3313007 : Blo 2207435 3313007 := bstep (se 1 (by rfl) ⟨2484755, by rfl⟩ : syracuseStep 3313007 = 4969511) B4969511
theorem B2208671 : Blo 2207435 2208671 := bstep (se 1 (by rfl) ⟨1656503, by rfl⟩ : syracuseStep 2208671 = 3313007) B3313007
theorem B3313013 : Blo 2207435 3313013 := bbase (se 5 (by rfl) ⟨155297, by rfl⟩ : syracuseStep 3313013 = 310595) (by norm_num)
theorem B2208675 : Blo 2207435 2208675 := bstep (se 1 (by rfl) ⟨1656506, by rfl⟩ : syracuseStep 2208675 = 3313013) B3313013
theorem B3144781 : Blo 2207435 3144781 := bbase (se 3 (by rfl) ⟨589646, by rfl⟩ : syracuseStep 3144781 = 1179293) (by norm_num)
theorem B4193041 : Blo 2207435 4193041 := bstep (se 2 (by rfl) ⟨1572390, by rfl⟩ : syracuseStep 4193041 = 3144781) B3144781
theorem B5590721 : Blo 2207435 5590721 := bstep (se 2 (by rfl) ⟨2096520, by rfl⟩ : syracuseStep 5590721 = 4193041) B4193041
theorem B3727147 : Blo 2207435 3727147 := bstep (se 1 (by rfl) ⟨2795360, by rfl⟩ : syracuseStep 3727147 = 5590721) B5590721
theorem B4969529 : Blo 2207435 4969529 := bstep (se 2 (by rfl) ⟨1863573, by rfl⟩ : syracuseStep 4969529 = 3727147) B3727147
theorem B3313019 : Blo 2207435 3313019 := bstep (se 1 (by rfl) ⟨2484764, by rfl⟩ : syracuseStep 3313019 = 4969529) B4969529
theorem B2208679 : Blo 2207435 2208679 := bstep (se 1 (by rfl) ⟨1656509, by rfl⟩ : syracuseStep 2208679 = 3313019) B3313019
theorem B2484769 : Blo 2207435 2484769 := bbase (se 2 (by rfl) ⟨931788, by rfl⟩ : syracuseStep 2484769 = 1863577) (by norm_num)
theorem B3313025 : Blo 2207435 3313025 := bstep (se 2 (by rfl) ⟨1242384, by rfl⟩ : syracuseStep 3313025 = 2484769) B2484769
theorem B2208683 : Blo 2207435 2208683 := bstep (se 1 (by rfl) ⟨1656512, by rfl⟩ : syracuseStep 2208683 = 3313025) B3313025
theorem B5590741 : Blo 2207435 5590741 := bbase (se 7 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 5590741 = 131033) (by norm_num)
theorem B7454321 : Blo 2207435 7454321 := bstep (se 2 (by rfl) ⟨2795370, by rfl⟩ : syracuseStep 7454321 = 5590741) B5590741
theorem B4969547 : Blo 2207435 4969547 := bstep (se 1 (by rfl) ⟨3727160, by rfl⟩ : syracuseStep 4969547 = 7454321) B7454321
theorem B3313031 : Blo 2207435 3313031 := bstep (se 1 (by rfl) ⟨2484773, by rfl⟩ : syracuseStep 3313031 = 4969547) B4969547
theorem B2208687 : Blo 2207435 2208687 := bstep (se 1 (by rfl) ⟨1656515, by rfl⟩ : syracuseStep 2208687 = 3313031) B3313031
theorem B3313037 : Blo 2207435 3313037 := bbase (se 3 (by rfl) ⟨621194, by rfl⟩ : syracuseStep 3313037 = 1242389) (by norm_num)
theorem B2208691 : Blo 2207435 2208691 := bstep (se 1 (by rfl) ⟨1656518, by rfl⟩ : syracuseStep 2208691 = 3313037) B3313037
theorem B4969565 : Blo 2207435 4969565 := bbase (se 3 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 4969565 = 1863587) (by norm_num)
theorem B3313043 : Blo 2207435 3313043 := bstep (se 1 (by rfl) ⟨2484782, by rfl⟩ : syracuseStep 3313043 = 4969565) B4969565
theorem B2208695 : Blo 2207435 2208695 := bstep (se 1 (by rfl) ⟨1656521, by rfl⟩ : syracuseStep 2208695 = 3313043) B3313043
theorem B3727181 : Blo 2207435 3727181 := bbase (se 3 (by rfl) ⟨698846, by rfl⟩ : syracuseStep 3727181 = 1397693) (by norm_num)
theorem B2484787 : Blo 2207435 2484787 := bstep (se 1 (by rfl) ⟨1863590, by rfl⟩ : syracuseStep 2484787 = 3727181) B3727181
theorem B3313049 : Blo 2207435 3313049 := bstep (se 2 (by rfl) ⟨1242393, by rfl⟩ : syracuseStep 3313049 = 2484787) B2484787
theorem B2208699 : Blo 2207435 2208699 := bstep (se 1 (by rfl) ⟨1656524, by rfl⟩ : syracuseStep 2208699 = 3313049) B3313049
theorem B10074773 : Blo 2207435 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B6716515 : Blo 2207435 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B8955353 : Blo 2207435 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B5970235 : Blo 2207435 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B7960313 : Blo 2207435 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B21227501 : Blo 2207435 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B14151667 : Blo 2207435 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B18868889 : Blo 2207435 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B12579259 : Blo 2207435 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B16772345 : Blo 2207435 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B11181563 : Blo 2207435 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B7454375 : Blo 2207435 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B4969583 : Blo 2207435 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B3313055 : Blo 2207435 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B2208703 : Blo 2207435 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B3313061 : Blo 2207435 3313061 := bbase (se 4 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 3313061 = 621199) (by norm_num)
theorem B2208707 : Blo 2207435 2208707 := bstep (se 1 (by rfl) ⟨1656530, by rfl⟩ : syracuseStep 2208707 = 3313061) B3313061
theorem B2795401 : Blo 2207435 2795401 := bbase (se 2 (by rfl) ⟨1048275, by rfl⟩ : syracuseStep 2795401 = 2096551) (by norm_num)
theorem B3727201 : Blo 2207435 3727201 := bstep (se 2 (by rfl) ⟨1397700, by rfl⟩ : syracuseStep 3727201 = 2795401) B2795401
theorem B4969601 : Blo 2207435 4969601 := bstep (se 2 (by rfl) ⟨1863600, by rfl⟩ : syracuseStep 4969601 = 3727201) B3727201
theorem B3313067 : Blo 2207435 3313067 := bstep (se 1 (by rfl) ⟨2484800, by rfl⟩ : syracuseStep 3313067 = 4969601) B4969601
theorem B2208711 : Blo 2207435 2208711 := bstep (se 1 (by rfl) ⟨1656533, by rfl⟩ : syracuseStep 2208711 = 3313067) B3313067
theorem B2484805 : Blo 2207435 2484805 := bbase (se 4 (by rfl) ⟨232950, by rfl⟩ : syracuseStep 2484805 = 465901) (by norm_num)
theorem B3313073 : Blo 2207435 3313073 := bstep (se 2 (by rfl) ⟨1242402, by rfl⟩ : syracuseStep 3313073 = 2484805) B2484805
theorem B2208715 : Blo 2207435 2208715 := bstep (se 1 (by rfl) ⟨1656536, by rfl⟩ : syracuseStep 2208715 = 3313073) B3313073
theorem B4193117 : Blo 2207435 4193117 := bbase (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) (by norm_num)
theorem B2795411 : Blo 2207435 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B7454429 : Blo 2207435 7454429 := bstep (se 3 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 7454429 = 2795411) B2795411
theorem B4969619 : Blo 2207435 4969619 := bstep (se 1 (by rfl) ⟨3727214, by rfl⟩ : syracuseStep 4969619 = 7454429) B7454429
theorem B3313079 : Blo 2207435 3313079 := bstep (se 1 (by rfl) ⟨2484809, by rfl⟩ : syracuseStep 3313079 = 4969619) B4969619
theorem B2208719 : Blo 2207435 2208719 := bstep (se 1 (by rfl) ⟨1656539, by rfl⟩ : syracuseStep 2208719 = 3313079) B3313079
theorem B3313085 : Blo 2207435 3313085 := bbase (se 3 (by rfl) ⟨621203, by rfl⟩ : syracuseStep 3313085 = 1242407) (by norm_num)
theorem B2208723 : Blo 2207435 2208723 := bstep (se 1 (by rfl) ⟨1656542, by rfl⟩ : syracuseStep 2208723 = 3313085) B3313085
theorem B4969637 : Blo 2207435 4969637 := bbase (se 4 (by rfl) ⟨465903, by rfl⟩ : syracuseStep 4969637 = 931807) (by norm_num)
theorem B3313091 : Blo 2207435 3313091 := bstep (se 1 (by rfl) ⟨2484818, by rfl⟩ : syracuseStep 3313091 = 4969637) B4969637
theorem B2208727 : Blo 2207435 2208727 := bstep (se 1 (by rfl) ⟨1656545, by rfl⟩ : syracuseStep 2208727 = 3313091) B3313091
theorem B5590853 : Blo 2207435 5590853 := bbase (se 4 (by rfl) ⟨524142, by rfl⟩ : syracuseStep 5590853 = 1048285) (by norm_num)
theorem B3727235 : Blo 2207435 3727235 := bstep (se 1 (by rfl) ⟨2795426, by rfl⟩ : syracuseStep 3727235 = 5590853) B5590853
theorem B2484823 : Blo 2207435 2484823 := bstep (se 1 (by rfl) ⟨1863617, by rfl⟩ : syracuseStep 2484823 = 3727235) B3727235
theorem B3313097 : Blo 2207435 3313097 := bstep (se 2 (by rfl) ⟨1242411, by rfl⟩ : syracuseStep 3313097 = 2484823) B2484823
theorem B2208731 : Blo 2207435 2208731 := bstep (se 1 (by rfl) ⟨1656548, by rfl⟩ : syracuseStep 2208731 = 3313097) B3313097
theorem B5037461 : Blo 2207435 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B3358307 : Blo 2207435 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B8955485 : Blo 2207435 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B5970323 : Blo 2207435 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B3980215 : Blo 2207435 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B5306953 : Blo 2207435 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B7075937 : Blo 2207435 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B4717291 : Blo 2207435 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B6289721 : Blo 2207435 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B4193147 : Blo 2207435 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B11181725 : Blo 2207435 11181725 := bstep (se 3 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 11181725 = 4193147) B4193147
theorem B7454483 : Blo 2207435 7454483 := bstep (se 1 (by rfl) ⟨5590862, by rfl⟩ : syracuseStep 7454483 = 11181725) B11181725
theorem B4969655 : Blo 2207435 4969655 := bstep (se 1 (by rfl) ⟨3727241, by rfl⟩ : syracuseStep 4969655 = 7454483) B7454483
theorem B3313103 : Blo 2207435 3313103 := bstep (se 1 (by rfl) ⟨2484827, by rfl⟩ : syracuseStep 3313103 = 4969655) B4969655
theorem B2208735 : Blo 2207435 2208735 := bstep (se 1 (by rfl) ⟨1656551, by rfl⟩ : syracuseStep 2208735 = 3313103) B3313103
theorem B3313109 : Blo 2207435 3313109 := bbase (se 7 (by rfl) ⟨38825, by rfl⟩ : syracuseStep 3313109 = 77651) (by norm_num)
theorem B2208739 : Blo 2207435 2208739 := bstep (se 1 (by rfl) ⟨1656554, by rfl⟩ : syracuseStep 2208739 = 3313109) B3313109
theorem B8386325 : Blo 2207435 8386325 := bbase (se 6 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 8386325 = 393109) (by norm_num)
theorem B5590883 : Blo 2207435 5590883 := bstep (se 1 (by rfl) ⟨4193162, by rfl⟩ : syracuseStep 5590883 = 8386325) B8386325
theorem B3727255 : Blo 2207435 3727255 := bstep (se 1 (by rfl) ⟨2795441, by rfl⟩ : syracuseStep 3727255 = 5590883) B5590883
theorem B4969673 : Blo 2207435 4969673 := bstep (se 2 (by rfl) ⟨1863627, by rfl⟩ : syracuseStep 4969673 = 3727255) B3727255
theorem B3313115 : Blo 2207435 3313115 := bstep (se 1 (by rfl) ⟨2484836, by rfl⟩ : syracuseStep 3313115 = 4969673) B4969673
theorem B2208743 : Blo 2207435 2208743 := bstep (se 1 (by rfl) ⟨1656557, by rfl⟩ : syracuseStep 2208743 = 3313115) B3313115
theorem B2484841 : Blo 2207435 2484841 := bbase (se 2 (by rfl) ⟨931815, by rfl⟩ : syracuseStep 2484841 = 1863631) (by norm_num)
theorem B3313121 : Blo 2207435 3313121 := bstep (se 2 (by rfl) ⟨1242420, by rfl⟩ : syracuseStep 3313121 = 2484841) B2484841
theorem B2208747 : Blo 2207435 2208747 := bstep (se 1 (by rfl) ⟨1656560, by rfl⟩ : syracuseStep 2208747 = 3313121) B3313121
theorem B4717325 : Blo 2207435 4717325 := bbase (se 3 (by rfl) ⟨884498, by rfl⟩ : syracuseStep 4717325 = 1768997) (by norm_num)
theorem B12579533 : Blo 2207435 12579533 := bstep (se 3 (by rfl) ⟨2358662, by rfl⟩ : syracuseStep 12579533 = 4717325) B4717325
theorem B8386355 : Blo 2207435 8386355 := bstep (se 1 (by rfl) ⟨6289766, by rfl⟩ : syracuseStep 8386355 = 12579533) B12579533
theorem B5590903 : Blo 2207435 5590903 := bstep (se 1 (by rfl) ⟨4193177, by rfl⟩ : syracuseStep 5590903 = 8386355) B8386355
theorem B7454537 : Blo 2207435 7454537 := bstep (se 2 (by rfl) ⟨2795451, by rfl⟩ : syracuseStep 7454537 = 5590903) B5590903
theorem B4969691 : Blo 2207435 4969691 := bstep (se 1 (by rfl) ⟨3727268, by rfl⟩ : syracuseStep 4969691 = 7454537) B7454537
theorem B3313127 : Blo 2207435 3313127 := bstep (se 1 (by rfl) ⟨2484845, by rfl⟩ : syracuseStep 3313127 = 4969691) B4969691
theorem B2208751 : Blo 2207435 2208751 := bstep (se 1 (by rfl) ⟨1656563, by rfl⟩ : syracuseStep 2208751 = 3313127) B3313127
theorem B3313133 : Blo 2207435 3313133 := bbase (se 3 (by rfl) ⟨621212, by rfl⟩ : syracuseStep 3313133 = 1242425) (by norm_num)
theorem B2208755 : Blo 2207435 2208755 := bstep (se 1 (by rfl) ⟨1656566, by rfl⟩ : syracuseStep 2208755 = 3313133) B3313133
theorem B4969709 : Blo 2207435 4969709 := bbase (se 3 (by rfl) ⟨931820, by rfl⟩ : syracuseStep 4969709 = 1863641) (by norm_num)
theorem B3313139 : Blo 2207435 3313139 := bstep (se 1 (by rfl) ⟨2484854, by rfl⟩ : syracuseStep 3313139 = 4969709) B4969709
theorem B2208759 : Blo 2207435 2208759 := bstep (se 1 (by rfl) ⟨1656569, by rfl⟩ : syracuseStep 2208759 = 3313139) B3313139
theorem B3144901 : Blo 2207435 3144901 := bbase (se 4 (by rfl) ⟨294834, by rfl⟩ : syracuseStep 3144901 = 589669) (by norm_num)
theorem B4193201 : Blo 2207435 4193201 := bstep (se 2 (by rfl) ⟨1572450, by rfl⟩ : syracuseStep 4193201 = 3144901) B3144901
theorem B2795467 : Blo 2207435 2795467 := bstep (se 1 (by rfl) ⟨2096600, by rfl⟩ : syracuseStep 2795467 = 4193201) B4193201
theorem B3727289 : Blo 2207435 3727289 := bstep (se 2 (by rfl) ⟨1397733, by rfl⟩ : syracuseStep 3727289 = 2795467) B2795467
theorem B2484859 : Blo 2207435 2484859 := bstep (se 1 (by rfl) ⟨1863644, by rfl⟩ : syracuseStep 2484859 = 3727289) B3727289
theorem B3313145 : Blo 2207435 3313145 := bstep (se 2 (by rfl) ⟨1242429, by rfl⟩ : syracuseStep 3313145 = 2484859) B2484859
theorem B2208763 : Blo 2207435 2208763 := bstep (se 1 (by rfl) ⟨1656572, by rfl⟩ : syracuseStep 2208763 = 3313145) B3313145
theorem B12751253 : Blo 2207435 12751253 := bbase (se 6 (by rfl) ⟨298857, by rfl⟩ : syracuseStep 12751253 = 597715) (by norm_num)
theorem B8500835 : Blo 2207435 8500835 := bstep (se 1 (by rfl) ⟨6375626, by rfl⟩ : syracuseStep 8500835 = 12751253) B12751253
theorem B22668893 : Blo 2207435 22668893 := bstep (se 3 (by rfl) ⟨4250417, by rfl⟩ : syracuseStep 22668893 = 8500835) B8500835
theorem B15112595 : Blo 2207435 15112595 := bstep (se 1 (by rfl) ⟨11334446, by rfl⟩ : syracuseStep 15112595 = 22668893) B22668893
theorem B40300253 : Blo 2207435 40300253 := bstep (se 3 (by rfl) ⟨7556297, by rfl⟩ : syracuseStep 40300253 = 15112595) B15112595
theorem B26866835 : Blo 2207435 26866835 := bstep (se 1 (by rfl) ⟨20150126, by rfl⟩ : syracuseStep 26866835 = 40300253) B40300253
theorem B17911223 : Blo 2207435 17911223 := bstep (se 1 (by rfl) ⟨13433417, by rfl⟩ : syracuseStep 17911223 = 26866835) B26866835
theorem B11940815 : Blo 2207435 11940815 := bstep (se 1 (by rfl) ⟨8955611, by rfl⟩ : syracuseStep 11940815 = 17911223) B17911223
theorem B31842173 : Blo 2207435 31842173 := bstep (se 3 (by rfl) ⟨5970407, by rfl⟩ : syracuseStep 31842173 = 11940815) B11940815
theorem B84912461 : Blo 2207435 84912461 := bstep (se 3 (by rfl) ⟨15921086, by rfl⟩ : syracuseStep 84912461 = 31842173) B31842173
theorem B56608307 : Blo 2207435 56608307 := bstep (se 1 (by rfl) ⟨42456230, by rfl⟩ : syracuseStep 56608307 = 84912461) B84912461
theorem B37738871 : Blo 2207435 37738871 := bstep (se 1 (by rfl) ⟨28304153, by rfl⟩ : syracuseStep 37738871 = 56608307) B56608307
theorem B25159247 : Blo 2207435 25159247 := bstep (se 1 (by rfl) ⟨18869435, by rfl⟩ : syracuseStep 25159247 = 37738871) B37738871
theorem B16772831 : Blo 2207435 16772831 := bstep (se 1 (by rfl) ⟨12579623, by rfl⟩ : syracuseStep 16772831 = 25159247) B25159247
theorem B11181887 : Blo 2207435 11181887 := bstep (se 1 (by rfl) ⟨8386415, by rfl⟩ : syracuseStep 11181887 = 16772831) B16772831
theorem B7454591 : Blo 2207435 7454591 := bstep (se 1 (by rfl) ⟨5590943, by rfl⟩ : syracuseStep 7454591 = 11181887) B11181887
theorem B4969727 : Blo 2207435 4969727 := bstep (se 1 (by rfl) ⟨3727295, by rfl⟩ : syracuseStep 4969727 = 7454591) B7454591
theorem B3313151 : Blo 2207435 3313151 := bstep (se 1 (by rfl) ⟨2484863, by rfl⟩ : syracuseStep 3313151 = 4969727) B4969727
theorem B2208767 : Blo 2207435 2208767 := bstep (se 1 (by rfl) ⟨1656575, by rfl⟩ : syracuseStep 2208767 = 3313151) B3313151
theorem B3313157 : Blo 2207435 3313157 := bbase (se 4 (by rfl) ⟨310608, by rfl⟩ : syracuseStep 3313157 = 621217) (by norm_num)
theorem B2208771 : Blo 2207435 2208771 := bstep (se 1 (by rfl) ⟨1656578, by rfl⟩ : syracuseStep 2208771 = 3313157) B3313157
theorem B3727309 : Blo 2207435 3727309 := bbase (se 3 (by rfl) ⟨698870, by rfl⟩ : syracuseStep 3727309 = 1397741) (by norm_num)
theorem B4969745 : Blo 2207435 4969745 := bstep (se 2 (by rfl) ⟨1863654, by rfl⟩ : syracuseStep 4969745 = 3727309) B3727309
theorem B3313163 : Blo 2207435 3313163 := bstep (se 1 (by rfl) ⟨2484872, by rfl⟩ : syracuseStep 3313163 = 4969745) B4969745
theorem B2208775 : Blo 2207435 2208775 := bstep (se 1 (by rfl) ⟨1656581, by rfl⟩ : syracuseStep 2208775 = 3313163) B3313163
theorem B2484877 : Blo 2207435 2484877 := bbase (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) (by norm_num)
theorem B3313169 : Blo 2207435 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B2208779 : Blo 2207435 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B7454645 : Blo 2207435 7454645 := bbase (se 5 (by rfl) ⟨349436, by rfl⟩ : syracuseStep 7454645 = 698873) (by norm_num)
theorem B4969763 : Blo 2207435 4969763 := bstep (se 1 (by rfl) ⟨3727322, by rfl⟩ : syracuseStep 4969763 = 7454645) B7454645
theorem B3313175 : Blo 2207435 3313175 := bstep (se 1 (by rfl) ⟨2484881, by rfl⟩ : syracuseStep 3313175 = 4969763) B4969763
theorem B2208783 : Blo 2207435 2208783 := bstep (se 1 (by rfl) ⟨1656587, by rfl⟩ : syracuseStep 2208783 = 3313175) B3313175
theorem B3313181 : Blo 2207435 3313181 := bbase (se 3 (by rfl) ⟨621221, by rfl⟩ : syracuseStep 3313181 = 1242443) (by norm_num)
theorem B2208787 : Blo 2207435 2208787 := bstep (se 1 (by rfl) ⟨1656590, by rfl⟩ : syracuseStep 2208787 = 3313181) B3313181
theorem B4969781 : Blo 2207435 4969781 := bbase (se 5 (by rfl) ⟨232958, by rfl⟩ : syracuseStep 4969781 = 465917) (by norm_num)
theorem B3313187 : Blo 2207435 3313187 := bstep (se 1 (by rfl) ⟨2484890, by rfl⟩ : syracuseStep 3313187 = 4969781) B4969781
theorem B2208791 : Blo 2207435 2208791 := bstep (se 1 (by rfl) ⟨1656593, by rfl⟩ : syracuseStep 2208791 = 3313187) B3313187
theorem B5970485 : Blo 2207435 5970485 := bbase (se 5 (by rfl) ⟨279866, by rfl⟩ : syracuseStep 5970485 = 559733) (by norm_num)
theorem B3980323 : Blo 2207435 3980323 := bstep (se 1 (by rfl) ⟨2985242, by rfl⟩ : syracuseStep 3980323 = 5970485) B5970485
theorem B21228389 : Blo 2207435 21228389 := bstep (se 4 (by rfl) ⟨1990161, by rfl⟩ : syracuseStep 21228389 = 3980323) B3980323
theorem B14152259 : Blo 2207435 14152259 := bstep (se 1 (by rfl) ⟨10614194, by rfl⟩ : syracuseStep 14152259 = 21228389) B21228389
theorem B9434839 : Blo 2207435 9434839 := bstep (se 1 (by rfl) ⟨7076129, by rfl⟩ : syracuseStep 9434839 = 14152259) B14152259
theorem B12579785 : Blo 2207435 12579785 := bstep (se 2 (by rfl) ⟨4717419, by rfl⟩ : syracuseStep 12579785 = 9434839) B9434839
theorem B8386523 : Blo 2207435 8386523 := bstep (se 1 (by rfl) ⟨6289892, by rfl⟩ : syracuseStep 8386523 = 12579785) B12579785
theorem B5591015 : Blo 2207435 5591015 := bstep (se 1 (by rfl) ⟨4193261, by rfl⟩ : syracuseStep 5591015 = 8386523) B8386523
theorem B3727343 : Blo 2207435 3727343 := bstep (se 1 (by rfl) ⟨2795507, by rfl⟩ : syracuseStep 3727343 = 5591015) B5591015
theorem B2484895 : Blo 2207435 2484895 := bstep (se 1 (by rfl) ⟨1863671, by rfl⟩ : syracuseStep 2484895 = 3727343) B3727343
theorem B3313193 : Blo 2207435 3313193 := bstep (se 2 (by rfl) ⟨1242447, by rfl⟩ : syracuseStep 3313193 = 2484895) B2484895
theorem B2208795 : Blo 2207435 2208795 := bstep (se 1 (by rfl) ⟨1656596, by rfl⟩ : syracuseStep 2208795 = 3313193) B3313193
theorem B12269045 : Blo 2207435 12269045 := bbase (se 5 (by rfl) ⟨575111, by rfl⟩ : syracuseStep 12269045 = 1150223) (by norm_num)
theorem B8179363 : Blo 2207435 8179363 := bstep (se 1 (by rfl) ⟨6134522, by rfl⟩ : syracuseStep 8179363 = 12269045) B12269045
theorem B43623269 : Blo 2207435 43623269 := bstep (se 4 (by rfl) ⟨4089681, by rfl⟩ : syracuseStep 43623269 = 8179363) B8179363
theorem B29082179 : Blo 2207435 29082179 := bstep (se 1 (by rfl) ⟨21811634, by rfl⟩ : syracuseStep 29082179 = 43623269) B43623269
theorem B19388119 : Blo 2207435 19388119 := bstep (se 1 (by rfl) ⟨14541089, by rfl⟩ : syracuseStep 19388119 = 29082179) B29082179
theorem B25850825 : Blo 2207435 25850825 := bstep (se 2 (by rfl) ⟨9694059, by rfl⟩ : syracuseStep 25850825 = 19388119) B19388119
theorem B17233883 : Blo 2207435 17233883 := bstep (se 1 (by rfl) ⟨12925412, by rfl⟩ : syracuseStep 17233883 = 25850825) B25850825
theorem B11489255 : Blo 2207435 11489255 := bstep (se 1 (by rfl) ⟨8616941, by rfl⟩ : syracuseStep 11489255 = 17233883) B17233883
theorem B7659503 : Blo 2207435 7659503 := bstep (se 1 (by rfl) ⟨5744627, by rfl⟩ : syracuseStep 7659503 = 11489255) B11489255
theorem B5106335 : Blo 2207435 5106335 := bstep (se 1 (by rfl) ⟨3829751, by rfl⟩ : syracuseStep 5106335 = 7659503) B7659503
theorem B13616893 : Blo 2207435 13616893 := bstep (se 3 (by rfl) ⟨2553167, by rfl⟩ : syracuseStep 13616893 = 5106335) B5106335
theorem B72623429 : Blo 2207435 72623429 := bstep (se 4 (by rfl) ⟨6808446, by rfl⟩ : syracuseStep 72623429 = 13616893) B13616893
theorem B48415619 : Blo 2207435 48415619 := bstep (se 1 (by rfl) ⟨36311714, by rfl⟩ : syracuseStep 48415619 = 72623429) B72623429
theorem B32277079 : Blo 2207435 32277079 := bstep (se 1 (by rfl) ⟨24207809, by rfl⟩ : syracuseStep 32277079 = 48415619) B48415619
theorem B43036105 : Blo 2207435 43036105 := bstep (se 2 (by rfl) ⟨16138539, by rfl⟩ : syracuseStep 43036105 = 32277079) B32277079
theorem B57381473 : Blo 2207435 57381473 := bstep (se 2 (by rfl) ⟨21518052, by rfl⟩ : syracuseStep 57381473 = 43036105) B43036105
theorem B153017261 : Blo 2207435 153017261 := bstep (se 3 (by rfl) ⟨28690736, by rfl⟩ : syracuseStep 153017261 = 57381473) B57381473
theorem B102011507 : Blo 2207435 102011507 := bstep (se 1 (by rfl) ⟨76508630, by rfl⟩ : syracuseStep 102011507 = 153017261) B153017261
theorem B68007671 : Blo 2207435 68007671 := bstep (se 1 (by rfl) ⟨51005753, by rfl⟩ : syracuseStep 68007671 = 102011507) B102011507
theorem B45338447 : Blo 2207435 45338447 := bstep (se 1 (by rfl) ⟨34003835, by rfl⟩ : syracuseStep 45338447 = 68007671) B68007671
theorem B30225631 : Blo 2207435 30225631 := bstep (se 1 (by rfl) ⟨22669223, by rfl⟩ : syracuseStep 30225631 = 45338447) B45338447
theorem B40300841 : Blo 2207435 40300841 := bstep (se 2 (by rfl) ⟨15112815, by rfl⟩ : syracuseStep 40300841 = 30225631) B30225631
theorem B26867227 : Blo 2207435 26867227 := bstep (se 1 (by rfl) ⟨20150420, by rfl⟩ : syracuseStep 26867227 = 40300841) B40300841
theorem B35822969 : Blo 2207435 35822969 := bstep (se 2 (by rfl) ⟨13433613, by rfl⟩ : syracuseStep 35822969 = 26867227) B26867227
theorem B23881979 : Blo 2207435 23881979 := bstep (se 1 (by rfl) ⟨17911484, by rfl⟩ : syracuseStep 23881979 = 35822969) B35822969
theorem B15921319 : Blo 2207435 15921319 := bstep (se 1 (by rfl) ⟨11940989, by rfl⟩ : syracuseStep 15921319 = 23881979) B23881979
theorem B21228425 : Blo 2207435 21228425 := bstep (se 2 (by rfl) ⟨7960659, by rfl⟩ : syracuseStep 21228425 = 15921319) B15921319
theorem B14152283 : Blo 2207435 14152283 := bstep (se 1 (by rfl) ⟨10614212, by rfl⟩ : syracuseStep 14152283 = 21228425) B21228425
theorem B9434855 : Blo 2207435 9434855 := bstep (se 1 (by rfl) ⟨7076141, by rfl⟩ : syracuseStep 9434855 = 14152283) B14152283
theorem B6289903 : Blo 2207435 6289903 := bstep (se 1 (by rfl) ⟨4717427, by rfl⟩ : syracuseStep 6289903 = 9434855) B9434855
theorem B8386537 : Blo 2207435 8386537 := bstep (se 2 (by rfl) ⟨3144951, by rfl⟩ : syracuseStep 8386537 = 6289903) B6289903
theorem B11182049 : Blo 2207435 11182049 := bstep (se 2 (by rfl) ⟨4193268, by rfl⟩ : syracuseStep 11182049 = 8386537) B8386537
theorem B7454699 : Blo 2207435 7454699 := bstep (se 1 (by rfl) ⟨5591024, by rfl⟩ : syracuseStep 7454699 = 11182049) B11182049
theorem B4969799 : Blo 2207435 4969799 := bstep (se 1 (by rfl) ⟨3727349, by rfl⟩ : syracuseStep 4969799 = 7454699) B7454699
theorem B3313199 : Blo 2207435 3313199 := bstep (se 1 (by rfl) ⟨2484899, by rfl⟩ : syracuseStep 3313199 = 4969799) B4969799
theorem B2208799 : Blo 2207435 2208799 := bstep (se 1 (by rfl) ⟨1656599, by rfl⟩ : syracuseStep 2208799 = 3313199) B3313199
theorem B3313205 : Blo 2207435 3313205 := bbase (se 5 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 3313205 = 310613) (by norm_num)
theorem B2208803 : Blo 2207435 2208803 := bstep (se 1 (by rfl) ⟨1656602, by rfl⟩ : syracuseStep 2208803 = 3313205) B3313205
theorem B5591045 : Blo 2207435 5591045 := bbase (se 4 (by rfl) ⟨524160, by rfl⟩ : syracuseStep 5591045 = 1048321) (by norm_num)
theorem B3727363 : Blo 2207435 3727363 := bstep (se 1 (by rfl) ⟨2795522, by rfl⟩ : syracuseStep 3727363 = 5591045) B5591045
theorem B4969817 : Blo 2207435 4969817 := bstep (se 2 (by rfl) ⟨1863681, by rfl⟩ : syracuseStep 4969817 = 3727363) B3727363
theorem B3313211 : Blo 2207435 3313211 := bstep (se 1 (by rfl) ⟨2484908, by rfl⟩ : syracuseStep 3313211 = 4969817) B4969817
theorem B2208807 : Blo 2207435 2208807 := bstep (se 1 (by rfl) ⟨1656605, by rfl⟩ : syracuseStep 2208807 = 3313211) B3313211
theorem B2484913 : Blo 2207435 2484913 := bbase (se 2 (by rfl) ⟨931842, by rfl⟩ : syracuseStep 2484913 = 1863685) (by norm_num)
theorem B3313217 : Blo 2207435 3313217 := bstep (se 2 (by rfl) ⟨1242456, by rfl⟩ : syracuseStep 3313217 = 2484913) B2484913
theorem B2208811 : Blo 2207435 2208811 := bstep (se 1 (by rfl) ⟨1656608, by rfl⟩ : syracuseStep 2208811 = 3313217) B3313217
theorem B2653573 : Blo 2207435 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B3538097 : Blo 2207435 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B2358731 : Blo 2207435 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B6289949 : Blo 2207435 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B4193299 : Blo 2207435 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B5591065 : Blo 2207435 5591065 := bstep (se 2 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 5591065 = 4193299) B4193299
theorem B7454753 : Blo 2207435 7454753 := bstep (se 2 (by rfl) ⟨2795532, by rfl⟩ : syracuseStep 7454753 = 5591065) B5591065
theorem B4969835 : Blo 2207435 4969835 := bstep (se 1 (by rfl) ⟨3727376, by rfl⟩ : syracuseStep 4969835 = 7454753) B7454753
theorem B3313223 : Blo 2207435 3313223 := bstep (se 1 (by rfl) ⟨2484917, by rfl⟩ : syracuseStep 3313223 = 4969835) B4969835
theorem B2208815 : Blo 2207435 2208815 := bstep (se 1 (by rfl) ⟨1656611, by rfl⟩ : syracuseStep 2208815 = 3313223) B3313223
theorem B3313229 : Blo 2207435 3313229 := bbase (se 3 (by rfl) ⟨621230, by rfl⟩ : syracuseStep 3313229 = 1242461) (by norm_num)
theorem B2208819 : Blo 2207435 2208819 := bstep (se 1 (by rfl) ⟨1656614, by rfl⟩ : syracuseStep 2208819 = 3313229) B3313229
theorem B4969853 : Blo 2207435 4969853 := bbase (se 3 (by rfl) ⟨931847, by rfl⟩ : syracuseStep 4969853 = 1863695) (by norm_num)
theorem B3313235 : Blo 2207435 3313235 := bstep (se 1 (by rfl) ⟨2484926, by rfl⟩ : syracuseStep 3313235 = 4969853) B4969853
theorem B2208823 : Blo 2207435 2208823 := bstep (se 1 (by rfl) ⟨1656617, by rfl⟩ : syracuseStep 2208823 = 3313235) B3313235
theorem B3727397 : Blo 2207435 3727397 := bbase (se 4 (by rfl) ⟨349443, by rfl⟩ : syracuseStep 3727397 = 698887) (by norm_num)
theorem B2484931 : Blo 2207435 2484931 := bstep (se 1 (by rfl) ⟨1863698, by rfl⟩ : syracuseStep 2484931 = 3727397) B3727397
theorem B3313241 : Blo 2207435 3313241 := bstep (se 2 (by rfl) ⟨1242465, by rfl⟩ : syracuseStep 3313241 = 2484931) B2484931
theorem B2208827 : Blo 2207435 2208827 := bstep (se 1 (by rfl) ⟨1656620, by rfl⟩ : syracuseStep 2208827 = 3313241) B3313241
theorem B3144997 : Blo 2207435 3144997 := bbase (se 4 (by rfl) ⟨294843, by rfl⟩ : syracuseStep 3144997 = 589687) (by norm_num)
theorem B16773317 : Blo 2207435 16773317 := bstep (se 4 (by rfl) ⟨1572498, by rfl⟩ : syracuseStep 16773317 = 3144997) B3144997
theorem B11182211 : Blo 2207435 11182211 := bstep (se 1 (by rfl) ⟨8386658, by rfl⟩ : syracuseStep 11182211 = 16773317) B16773317
theorem B7454807 : Blo 2207435 7454807 := bstep (se 1 (by rfl) ⟨5591105, by rfl⟩ : syracuseStep 7454807 = 11182211) B11182211
theorem B4969871 : Blo 2207435 4969871 := bstep (se 1 (by rfl) ⟨3727403, by rfl⟩ : syracuseStep 4969871 = 7454807) B7454807
theorem B3313247 : Blo 2207435 3313247 := bstep (se 1 (by rfl) ⟨2484935, by rfl⟩ : syracuseStep 3313247 = 4969871) B4969871
theorem B2208831 : Blo 2207435 2208831 := bstep (se 1 (by rfl) ⟨1656623, by rfl⟩ : syracuseStep 2208831 = 3313247) B3313247
theorem B3313253 : Blo 2207435 3313253 := bbase (se 4 (by rfl) ⟨310617, by rfl⟩ : syracuseStep 3313253 = 621235) (by norm_num)
theorem B2208835 : Blo 2207435 2208835 := bstep (se 1 (by rfl) ⟨1656626, by rfl⟩ : syracuseStep 2208835 = 3313253) B3313253
theorem B2358757 : Blo 2207435 2358757 := bbase (se 4 (by rfl) ⟨221133, by rfl⟩ : syracuseStep 2358757 = 442267) (by norm_num)
theorem B3145009 : Blo 2207435 3145009 := bstep (se 2 (by rfl) ⟨1179378, by rfl⟩ : syracuseStep 3145009 = 2358757) B2358757
theorem B4193345 : Blo 2207435 4193345 := bstep (se 2 (by rfl) ⟨1572504, by rfl⟩ : syracuseStep 4193345 = 3145009) B3145009
theorem B2795563 : Blo 2207435 2795563 := bstep (se 1 (by rfl) ⟨2096672, by rfl⟩ : syracuseStep 2795563 = 4193345) B4193345
theorem B3727417 : Blo 2207435 3727417 := bstep (se 2 (by rfl) ⟨1397781, by rfl⟩ : syracuseStep 3727417 = 2795563) B2795563
theorem B4969889 : Blo 2207435 4969889 := bstep (se 2 (by rfl) ⟨1863708, by rfl⟩ : syracuseStep 4969889 = 3727417) B3727417
theorem B3313259 : Blo 2207435 3313259 := bstep (se 1 (by rfl) ⟨2484944, by rfl⟩ : syracuseStep 3313259 = 4969889) B4969889
theorem B2208839 : Blo 2207435 2208839 := bstep (se 1 (by rfl) ⟨1656629, by rfl⟩ : syracuseStep 2208839 = 3313259) B3313259
theorem B2484949 : Blo 2207435 2484949 := bbase (se 7 (by rfl) ⟨29120, by rfl⟩ : syracuseStep 2484949 = 58241) (by norm_num)
theorem B3313265 : Blo 2207435 3313265 := bstep (se 2 (by rfl) ⟨1242474, by rfl⟩ : syracuseStep 3313265 = 2484949) B2484949
theorem B2208843 : Blo 2207435 2208843 := bstep (se 1 (by rfl) ⟨1656632, by rfl⟩ : syracuseStep 2208843 = 3313265) B3313265
theorem B2795573 : Blo 2207435 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B7454861 : Blo 2207435 7454861 := bstep (se 3 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 7454861 = 2795573) B2795573
theorem B4969907 : Blo 2207435 4969907 := bstep (se 1 (by rfl) ⟨3727430, by rfl⟩ : syracuseStep 4969907 = 7454861) B7454861
theorem B3313271 : Blo 2207435 3313271 := bstep (se 1 (by rfl) ⟨2484953, by rfl⟩ : syracuseStep 3313271 = 4969907) B4969907
theorem B2208847 : Blo 2207435 2208847 := bstep (se 1 (by rfl) ⟨1656635, by rfl⟩ : syracuseStep 2208847 = 3313271) B3313271
theorem B3313277 : Blo 2207435 3313277 := bbase (se 3 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 3313277 = 1242479) (by norm_num)
theorem B2208851 : Blo 2207435 2208851 := bstep (se 1 (by rfl) ⟨1656638, by rfl⟩ : syracuseStep 2208851 = 3313277) B3313277
theorem B4969925 : Blo 2207435 4969925 := bbase (se 4 (by rfl) ⟨465930, by rfl⟩ : syracuseStep 4969925 = 931861) (by norm_num)
theorem B3313283 : Blo 2207435 3313283 := bstep (se 1 (by rfl) ⟨2484962, by rfl⟩ : syracuseStep 3313283 = 4969925) B4969925
theorem B2208855 : Blo 2207435 2208855 := bstep (se 1 (by rfl) ⟨1656641, by rfl⟩ : syracuseStep 2208855 = 3313283) B3313283
theorem B4308589 : Blo 2207435 4308589 := bbase (se 3 (by rfl) ⟨807860, by rfl⟩ : syracuseStep 4308589 = 1615721) (by norm_num)
theorem B5744785 : Blo 2207435 5744785 := bstep (se 2 (by rfl) ⟨2154294, by rfl⟩ : syracuseStep 5744785 = 4308589) B4308589
theorem B7659713 : Blo 2207435 7659713 := bstep (se 2 (by rfl) ⟨2872392, by rfl⟩ : syracuseStep 7659713 = 5744785) B5744785
theorem B5106475 : Blo 2207435 5106475 := bstep (se 1 (by rfl) ⟨3829856, by rfl⟩ : syracuseStep 5106475 = 7659713) B7659713
theorem B6808633 : Blo 2207435 6808633 := bstep (se 2 (by rfl) ⟨2553237, by rfl⟩ : syracuseStep 6808633 = 5106475) B5106475
theorem B36312709 : Blo 2207435 36312709 := bstep (se 4 (by rfl) ⟨3404316, by rfl⟩ : syracuseStep 36312709 = 6808633) B6808633
theorem B48416945 : Blo 2207435 48416945 := bstep (se 2 (by rfl) ⟨18156354, by rfl⟩ : syracuseStep 48416945 = 36312709) B36312709
theorem B129111853 : Blo 2207435 129111853 := bstep (se 3 (by rfl) ⟨24208472, by rfl⟩ : syracuseStep 129111853 = 48416945) B48416945
theorem B172149137 : Blo 2207435 172149137 := bstep (se 2 (by rfl) ⟨64555926, by rfl⟩ : syracuseStep 172149137 = 129111853) B129111853
theorem B114766091 : Blo 2207435 114766091 := bstep (se 1 (by rfl) ⟨86074568, by rfl⟩ : syracuseStep 114766091 = 172149137) B172149137
theorem B76510727 : Blo 2207435 76510727 := bstep (se 1 (by rfl) ⟨57383045, by rfl⟩ : syracuseStep 76510727 = 114766091) B114766091
theorem B51007151 : Blo 2207435 51007151 := bstep (se 1 (by rfl) ⟨38255363, by rfl⟩ : syracuseStep 51007151 = 76510727) B76510727
theorem B34004767 : Blo 2207435 34004767 := bstep (se 1 (by rfl) ⟨25503575, by rfl⟩ : syracuseStep 34004767 = 51007151) B51007151
theorem B45339689 : Blo 2207435 45339689 := bstep (se 2 (by rfl) ⟨17002383, by rfl⟩ : syracuseStep 45339689 = 34004767) B34004767
theorem B30226459 : Blo 2207435 30226459 := bstep (se 1 (by rfl) ⟨22669844, by rfl⟩ : syracuseStep 30226459 = 45339689) B45339689
theorem B40301945 : Blo 2207435 40301945 := bstep (se 2 (by rfl) ⟨15113229, by rfl⟩ : syracuseStep 40301945 = 30226459) B30226459
theorem B26867963 : Blo 2207435 26867963 := bstep (se 1 (by rfl) ⟨20150972, by rfl⟩ : syracuseStep 26867963 = 40301945) B40301945
theorem B17911975 : Blo 2207435 17911975 := bstep (se 1 (by rfl) ⟨13433981, by rfl⟩ : syracuseStep 17911975 = 26867963) B26867963
theorem B23882633 : Blo 2207435 23882633 := bstep (se 2 (by rfl) ⟨8955987, by rfl⟩ : syracuseStep 23882633 = 17911975) B17911975
theorem B15921755 : Blo 2207435 15921755 := bstep (se 1 (by rfl) ⟨11941316, by rfl⟩ : syracuseStep 15921755 = 23882633) B23882633
theorem B10614503 : Blo 2207435 10614503 := bstep (se 1 (by rfl) ⟨7960877, by rfl⟩ : syracuseStep 10614503 = 15921755) B15921755
theorem B7076335 : Blo 2207435 7076335 := bstep (se 1 (by rfl) ⟨5307251, by rfl⟩ : syracuseStep 7076335 = 10614503) B10614503
theorem B9435113 : Blo 2207435 9435113 := bstep (se 2 (by rfl) ⟨3538167, by rfl⟩ : syracuseStep 9435113 = 7076335) B7076335
theorem B6290075 : Blo 2207435 6290075 := bstep (se 1 (by rfl) ⟨4717556, by rfl⟩ : syracuseStep 6290075 = 9435113) B9435113
theorem B4193383 : Blo 2207435 4193383 := bstep (se 1 (by rfl) ⟨3145037, by rfl⟩ : syracuseStep 4193383 = 6290075) B6290075
theorem B5591177 : Blo 2207435 5591177 := bstep (se 2 (by rfl) ⟨2096691, by rfl⟩ : syracuseStep 5591177 = 4193383) B4193383
theorem B3727451 : Blo 2207435 3727451 := bstep (se 1 (by rfl) ⟨2795588, by rfl⟩ : syracuseStep 3727451 = 5591177) B5591177
theorem B2484967 : Blo 2207435 2484967 := bstep (se 1 (by rfl) ⟨1863725, by rfl⟩ : syracuseStep 2484967 = 3727451) B3727451
theorem B3313289 : Blo 2207435 3313289 := bstep (se 2 (by rfl) ⟨1242483, by rfl⟩ : syracuseStep 3313289 = 2484967) B2484967
theorem B2208859 : Blo 2207435 2208859 := bstep (se 1 (by rfl) ⟨1656644, by rfl⟩ : syracuseStep 2208859 = 3313289) B3313289
theorem B11182373 : Blo 2207435 11182373 := bbase (se 4 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 11182373 = 2096695) (by norm_num)
theorem B7454915 : Blo 2207435 7454915 := bstep (se 1 (by rfl) ⟨5591186, by rfl⟩ : syracuseStep 7454915 = 11182373) B11182373
theorem B4969943 : Blo 2207435 4969943 := bstep (se 1 (by rfl) ⟨3727457, by rfl⟩ : syracuseStep 4969943 = 7454915) B7454915
theorem B3313295 : Blo 2207435 3313295 := bstep (se 1 (by rfl) ⟨2484971, by rfl⟩ : syracuseStep 3313295 = 4969943) B4969943
theorem B2208863 : Blo 2207435 2208863 := bstep (se 1 (by rfl) ⟨1656647, by rfl⟩ : syracuseStep 2208863 = 3313295) B3313295
theorem B3313301 : Blo 2207435 3313301 := bbase (se 6 (by rfl) ⟨77655, by rfl⟩ : syracuseStep 3313301 = 155311) (by norm_num)
theorem B2208867 : Blo 2207435 2208867 := bstep (se 1 (by rfl) ⟨1656650, by rfl⟩ : syracuseStep 2208867 = 3313301) B3313301
theorem B8501237 : Blo 2207435 8501237 := bbase (se 5 (by rfl) ⟨398495, by rfl⟩ : syracuseStep 8501237 = 796991) (by norm_num)
theorem B5667491 : Blo 2207435 5667491 := bstep (se 1 (by rfl) ⟨4250618, by rfl⟩ : syracuseStep 5667491 = 8501237) B8501237
theorem B15113309 : Blo 2207435 15113309 := bstep (se 3 (by rfl) ⟨2833745, by rfl⟩ : syracuseStep 15113309 = 5667491) B5667491
theorem B40302157 : Blo 2207435 40302157 := bstep (se 3 (by rfl) ⟨7556654, by rfl⟩ : syracuseStep 40302157 = 15113309) B15113309
theorem B53736209 : Blo 2207435 53736209 := bstep (se 2 (by rfl) ⟨20151078, by rfl⟩ : syracuseStep 53736209 = 40302157) B40302157
theorem B35824139 : Blo 2207435 35824139 := bstep (se 1 (by rfl) ⟨26868104, by rfl⟩ : syracuseStep 35824139 = 53736209) B53736209
theorem B23882759 : Blo 2207435 23882759 := bstep (se 1 (by rfl) ⟨17912069, by rfl⟩ : syracuseStep 23882759 = 35824139) B35824139
theorem B15921839 : Blo 2207435 15921839 := bstep (se 1 (by rfl) ⟨11941379, by rfl⟩ : syracuseStep 15921839 = 23882759) B23882759
theorem B10614559 : Blo 2207435 10614559 := bstep (se 1 (by rfl) ⟨7960919, by rfl⟩ : syracuseStep 10614559 = 15921839) B15921839
theorem B14152745 : Blo 2207435 14152745 := bstep (se 2 (by rfl) ⟨5307279, by rfl⟩ : syracuseStep 14152745 = 10614559) B10614559
theorem B9435163 : Blo 2207435 9435163 := bstep (se 1 (by rfl) ⟨7076372, by rfl⟩ : syracuseStep 9435163 = 14152745) B14152745
theorem B12580217 : Blo 2207435 12580217 := bstep (se 2 (by rfl) ⟨4717581, by rfl⟩ : syracuseStep 12580217 = 9435163) B9435163
theorem B8386811 : Blo 2207435 8386811 := bstep (se 1 (by rfl) ⟨6290108, by rfl⟩ : syracuseStep 8386811 = 12580217) B12580217
theorem B5591207 : Blo 2207435 5591207 := bstep (se 1 (by rfl) ⟨4193405, by rfl⟩ : syracuseStep 5591207 = 8386811) B8386811
theorem B3727471 : Blo 2207435 3727471 := bstep (se 1 (by rfl) ⟨2795603, by rfl⟩ : syracuseStep 3727471 = 5591207) B5591207
theorem B4969961 : Blo 2207435 4969961 := bstep (se 2 (by rfl) ⟨1863735, by rfl⟩ : syracuseStep 4969961 = 3727471) B3727471
theorem B3313307 : Blo 2207435 3313307 := bstep (se 1 (by rfl) ⟨2484980, by rfl⟩ : syracuseStep 3313307 = 4969961) B4969961
theorem B2208871 : Blo 2207435 2208871 := bstep (se 1 (by rfl) ⟨1656653, by rfl⟩ : syracuseStep 2208871 = 3313307) B3313307
theorem B2484985 : Blo 2207435 2484985 := bbase (se 2 (by rfl) ⟨931869, by rfl⟩ : syracuseStep 2484985 = 1863739) (by norm_num)
theorem B3313313 : Blo 2207435 3313313 := bstep (se 2 (by rfl) ⟨1242492, by rfl⟩ : syracuseStep 3313313 = 2484985) B2484985
theorem B2208875 : Blo 2207435 2208875 := bstep (se 1 (by rfl) ⟨1656656, by rfl⟩ : syracuseStep 2208875 = 3313313) B3313313
theorem B7960949 : Blo 2207435 7960949 := bbase (se 5 (by rfl) ⟨373169, by rfl⟩ : syracuseStep 7960949 = 746339) (by norm_num)
theorem B5307299 : Blo 2207435 5307299 := bstep (se 1 (by rfl) ⟨3980474, by rfl⟩ : syracuseStep 5307299 = 7960949) B7960949
theorem B3538199 : Blo 2207435 3538199 := bstep (se 1 (by rfl) ⟨2653649, by rfl⟩ : syracuseStep 3538199 = 5307299) B5307299
theorem B9435197 : Blo 2207435 9435197 := bstep (se 3 (by rfl) ⟨1769099, by rfl⟩ : syracuseStep 9435197 = 3538199) B3538199
theorem B6290131 : Blo 2207435 6290131 := bstep (se 1 (by rfl) ⟨4717598, by rfl⟩ : syracuseStep 6290131 = 9435197) B9435197
theorem B8386841 : Blo 2207435 8386841 := bstep (se 2 (by rfl) ⟨3145065, by rfl⟩ : syracuseStep 8386841 = 6290131) B6290131
theorem B5591227 : Blo 2207435 5591227 := bstep (se 1 (by rfl) ⟨4193420, by rfl⟩ : syracuseStep 5591227 = 8386841) B8386841
theorem B7454969 : Blo 2207435 7454969 := bstep (se 2 (by rfl) ⟨2795613, by rfl⟩ : syracuseStep 7454969 = 5591227) B5591227
theorem B4969979 : Blo 2207435 4969979 := bstep (se 1 (by rfl) ⟨3727484, by rfl⟩ : syracuseStep 4969979 = 7454969) B7454969
theorem B3313319 : Blo 2207435 3313319 := bstep (se 1 (by rfl) ⟨2484989, by rfl⟩ : syracuseStep 3313319 = 4969979) B4969979
theorem B2208879 : Blo 2207435 2208879 := bstep (se 1 (by rfl) ⟨1656659, by rfl⟩ : syracuseStep 2208879 = 3313319) B3313319
theorem B3313325 : Blo 2207435 3313325 := bbase (se 3 (by rfl) ⟨621248, by rfl⟩ : syracuseStep 3313325 = 1242497) (by norm_num)
theorem B2208883 : Blo 2207435 2208883 := bstep (se 1 (by rfl) ⟨1656662, by rfl⟩ : syracuseStep 2208883 = 3313325) B3313325
theorem B4969997 : Blo 2207435 4969997 := bbase (se 3 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 4969997 = 1863749) (by norm_num)
theorem B3313331 : Blo 2207435 3313331 := bstep (se 1 (by rfl) ⟨2484998, by rfl⟩ : syracuseStep 3313331 = 4969997) B4969997
theorem B2208887 : Blo 2207435 2208887 := bstep (se 1 (by rfl) ⟨1656665, by rfl⟩ : syracuseStep 2208887 = 3313331) B3313331
theorem B2795629 : Blo 2207435 2795629 := bbase (se 3 (by rfl) ⟨524180, by rfl⟩ : syracuseStep 2795629 = 1048361) (by norm_num)
theorem B3727505 : Blo 2207435 3727505 := bstep (se 2 (by rfl) ⟨1397814, by rfl⟩ : syracuseStep 3727505 = 2795629) B2795629
theorem B2485003 : Blo 2207435 2485003 := bstep (se 1 (by rfl) ⟨1863752, by rfl⟩ : syracuseStep 2485003 = 3727505) B3727505
theorem B3313337 : Blo 2207435 3313337 := bstep (se 2 (by rfl) ⟨1242501, by rfl⟩ : syracuseStep 3313337 = 2485003) B2485003
theorem B2208891 : Blo 2207435 2208891 := bstep (se 1 (by rfl) ⟨1656668, by rfl⟩ : syracuseStep 2208891 = 3313337) B3313337
theorem B2239033 : Blo 2207435 2239033 := bbase (se 2 (by rfl) ⟨839637, by rfl⟩ : syracuseStep 2239033 = 1679275) (by norm_num)
theorem B2985377 : Blo 2207435 2985377 := bstep (se 2 (by rfl) ⟨1119516, by rfl⟩ : syracuseStep 2985377 = 2239033) B2239033
theorem B7961005 : Blo 2207435 7961005 := bstep (se 3 (by rfl) ⟨1492688, by rfl⟩ : syracuseStep 7961005 = 2985377) B2985377
theorem B10614673 : Blo 2207435 10614673 := bstep (se 2 (by rfl) ⟨3980502, by rfl⟩ : syracuseStep 10614673 = 7961005) B7961005
theorem B14152897 : Blo 2207435 14152897 := bstep (se 2 (by rfl) ⟨5307336, by rfl⟩ : syracuseStep 14152897 = 10614673) B10614673
theorem B18870529 : Blo 2207435 18870529 := bstep (se 2 (by rfl) ⟨7076448, by rfl⟩ : syracuseStep 18870529 = 14152897) B14152897
theorem B25160705 : Blo 2207435 25160705 := bstep (se 2 (by rfl) ⟨9435264, by rfl⟩ : syracuseStep 25160705 = 18870529) B18870529
theorem B16773803 : Blo 2207435 16773803 := bstep (se 1 (by rfl) ⟨12580352, by rfl⟩ : syracuseStep 16773803 = 25160705) B25160705
theorem B11182535 : Blo 2207435 11182535 := bstep (se 1 (by rfl) ⟨8386901, by rfl⟩ : syracuseStep 11182535 = 16773803) B16773803
theorem B7455023 : Blo 2207435 7455023 := bstep (se 1 (by rfl) ⟨5591267, by rfl⟩ : syracuseStep 7455023 = 11182535) B11182535
theorem B4970015 : Blo 2207435 4970015 := bstep (se 1 (by rfl) ⟨3727511, by rfl⟩ : syracuseStep 4970015 = 7455023) B7455023
theorem B3313343 : Blo 2207435 3313343 := bstep (se 1 (by rfl) ⟨2485007, by rfl⟩ : syracuseStep 3313343 = 4970015) B4970015
theorem B2208895 : Blo 2207435 2208895 := bstep (se 1 (by rfl) ⟨1656671, by rfl⟩ : syracuseStep 2208895 = 3313343) B3313343
theorem B3313349 : Blo 2207435 3313349 := bbase (se 4 (by rfl) ⟨310626, by rfl⟩ : syracuseStep 3313349 = 621253) (by norm_num)
theorem B2208899 : Blo 2207435 2208899 := bstep (se 1 (by rfl) ⟨1656674, by rfl⟩ : syracuseStep 2208899 = 3313349) B3313349
theorem B3727525 : Blo 2207435 3727525 := bbase (se 4 (by rfl) ⟨349455, by rfl⟩ : syracuseStep 3727525 = 698911) (by norm_num)
theorem B4970033 : Blo 2207435 4970033 := bstep (se 2 (by rfl) ⟨1863762, by rfl⟩ : syracuseStep 4970033 = 3727525) B3727525
theorem B3313355 : Blo 2207435 3313355 := bstep (se 1 (by rfl) ⟨2485016, by rfl⟩ : syracuseStep 3313355 = 4970033) B4970033
theorem B2208903 : Blo 2207435 2208903 := bstep (se 1 (by rfl) ⟨1656677, by rfl⟩ : syracuseStep 2208903 = 3313355) B3313355
theorem B2485021 : Blo 2207435 2485021 := bbase (se 3 (by rfl) ⟨465941, by rfl⟩ : syracuseStep 2485021 = 931883) (by norm_num)
theorem B3313361 : Blo 2207435 3313361 := bstep (se 2 (by rfl) ⟨1242510, by rfl⟩ : syracuseStep 3313361 = 2485021) B2485021
theorem B2208907 : Blo 2207435 2208907 := bstep (se 1 (by rfl) ⟨1656680, by rfl⟩ : syracuseStep 2208907 = 3313361) B3313361
theorem B7455077 : Blo 2207435 7455077 := bbase (se 4 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 7455077 = 1397827) (by norm_num)
theorem B4970051 : Blo 2207435 4970051 := bstep (se 1 (by rfl) ⟨3727538, by rfl⟩ : syracuseStep 4970051 = 7455077) B7455077
theorem B3313367 : Blo 2207435 3313367 := bstep (se 1 (by rfl) ⟨2485025, by rfl⟩ : syracuseStep 3313367 = 4970051) B4970051
theorem B2208911 : Blo 2207435 2208911 := bstep (se 1 (by rfl) ⟨1656683, by rfl⟩ : syracuseStep 2208911 = 3313367) B3313367
theorem B3313373 : Blo 2207435 3313373 := bbase (se 3 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 3313373 = 1242515) (by norm_num)
theorem B2208915 : Blo 2207435 2208915 := bstep (se 1 (by rfl) ⟨1656686, by rfl⟩ : syracuseStep 2208915 = 3313373) B3313373
theorem B4970069 : Blo 2207435 4970069 := bbase (se 8 (by rfl) ⟨29121, by rfl⟩ : syracuseStep 4970069 = 58243) (by norm_num)
theorem B3313379 : Blo 2207435 3313379 := bstep (se 1 (by rfl) ⟨2485034, by rfl⟩ : syracuseStep 3313379 = 4970069) B4970069
theorem B2208919 : Blo 2207435 2208919 := bstep (se 1 (by rfl) ⟨1656689, by rfl⟩ : syracuseStep 2208919 = 3313379) B3313379
theorem B4717693 : Blo 2207435 4717693 := bbase (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) (by norm_num)
theorem B6290257 : Blo 2207435 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B8387009 : Blo 2207435 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B5591339 : Blo 2207435 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B3727559 : Blo 2207435 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B2485039 : Blo 2207435 2485039 := bstep (se 1 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 2485039 = 3727559) B3727559
theorem B3313385 : Blo 2207435 3313385 := bstep (se 2 (by rfl) ⟨1242519, by rfl⟩ : syracuseStep 3313385 = 2485039) B2485039
theorem B2208923 : Blo 2207435 2208923 := bstep (se 1 (by rfl) ⟨1656692, by rfl⟩ : syracuseStep 2208923 = 3313385) B3313385
theorem B8956261 : Blo 2207435 8956261 := bbase (se 4 (by rfl) ⟨839649, by rfl⟩ : syracuseStep 8956261 = 1679299) (by norm_num)
theorem B11941681 : Blo 2207435 11941681 := bstep (se 2 (by rfl) ⟨4478130, by rfl⟩ : syracuseStep 11941681 = 8956261) B8956261
theorem B15922241 : Blo 2207435 15922241 := bstep (se 2 (by rfl) ⟨5970840, by rfl⟩ : syracuseStep 15922241 = 11941681) B11941681
theorem B10614827 : Blo 2207435 10614827 := bstep (se 1 (by rfl) ⟨7961120, by rfl⟩ : syracuseStep 10614827 = 15922241) B15922241
theorem B28306205 : Blo 2207435 28306205 := bstep (se 3 (by rfl) ⟨5307413, by rfl⟩ : syracuseStep 28306205 = 10614827) B10614827
theorem B18870803 : Blo 2207435 18870803 := bstep (se 1 (by rfl) ⟨14153102, by rfl⟩ : syracuseStep 18870803 = 28306205) B28306205
theorem B12580535 : Blo 2207435 12580535 := bstep (se 1 (by rfl) ⟨9435401, by rfl⟩ : syracuseStep 12580535 = 18870803) B18870803
theorem B8387023 : Blo 2207435 8387023 := bstep (se 1 (by rfl) ⟨6290267, by rfl⟩ : syracuseStep 8387023 = 12580535) B12580535
theorem B11182697 : Blo 2207435 11182697 := bstep (se 2 (by rfl) ⟨4193511, by rfl⟩ : syracuseStep 11182697 = 8387023) B8387023
theorem B7455131 : Blo 2207435 7455131 := bstep (se 1 (by rfl) ⟨5591348, by rfl⟩ : syracuseStep 7455131 = 11182697) B11182697
theorem B4970087 : Blo 2207435 4970087 := bstep (se 1 (by rfl) ⟨3727565, by rfl⟩ : syracuseStep 4970087 = 7455131) B7455131
theorem B3313391 : Blo 2207435 3313391 := bstep (se 1 (by rfl) ⟨2485043, by rfl⟩ : syracuseStep 3313391 = 4970087) B4970087
theorem B2208927 : Blo 2207435 2208927 := bstep (se 1 (by rfl) ⟨1656695, by rfl⟩ : syracuseStep 2208927 = 3313391) B3313391
theorem B3313397 : Blo 2207435 3313397 := bbase (se 5 (by rfl) ⟨155315, by rfl⟩ : syracuseStep 3313397 = 310631) (by norm_num)
theorem B2208931 : Blo 2207435 2208931 := bstep (se 1 (by rfl) ⟨1656698, by rfl⟩ : syracuseStep 2208931 = 3313397) B3313397
theorem B2653717 : Blo 2207435 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B3538289 : Blo 2207435 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B9435437 : Blo 2207435 9435437 := bstep (se 3 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 9435437 = 3538289) B3538289
theorem B6290291 : Blo 2207435 6290291 := bstep (se 1 (by rfl) ⟨4717718, by rfl⟩ : syracuseStep 6290291 = 9435437) B9435437
theorem B4193527 : Blo 2207435 4193527 := bstep (se 1 (by rfl) ⟨3145145, by rfl⟩ : syracuseStep 4193527 = 6290291) B6290291
theorem B5591369 : Blo 2207435 5591369 := bstep (se 2 (by rfl) ⟨2096763, by rfl⟩ : syracuseStep 5591369 = 4193527) B4193527
theorem B3727579 : Blo 2207435 3727579 := bstep (se 1 (by rfl) ⟨2795684, by rfl⟩ : syracuseStep 3727579 = 5591369) B5591369
theorem B4970105 : Blo 2207435 4970105 := bstep (se 2 (by rfl) ⟨1863789, by rfl⟩ : syracuseStep 4970105 = 3727579) B3727579
theorem B3313403 : Blo 2207435 3313403 := bstep (se 1 (by rfl) ⟨2485052, by rfl⟩ : syracuseStep 3313403 = 4970105) B4970105
theorem B2208935 : Blo 2207435 2208935 := bstep (se 1 (by rfl) ⟨1656701, by rfl⟩ : syracuseStep 2208935 = 3313403) B3313403
theorem B2485057 : Blo 2207435 2485057 := bbase (se 2 (by rfl) ⟨931896, by rfl⟩ : syracuseStep 2485057 = 1863793) (by norm_num)
theorem B3313409 : Blo 2207435 3313409 := bstep (se 2 (by rfl) ⟨1242528, by rfl⟩ : syracuseStep 3313409 = 2485057) B2485057
theorem B2208939 : Blo 2207435 2208939 := bstep (se 1 (by rfl) ⟨1656704, by rfl⟩ : syracuseStep 2208939 = 3313409) B3313409
theorem B5591389 : Blo 2207435 5591389 := bbase (se 3 (by rfl) ⟨1048385, by rfl⟩ : syracuseStep 5591389 = 2096771) (by norm_num)
theorem B7455185 : Blo 2207435 7455185 := bstep (se 2 (by rfl) ⟨2795694, by rfl⟩ : syracuseStep 7455185 = 5591389) B5591389
theorem B4970123 : Blo 2207435 4970123 := bstep (se 1 (by rfl) ⟨3727592, by rfl⟩ : syracuseStep 4970123 = 7455185) B7455185
theorem B3313415 : Blo 2207435 3313415 := bstep (se 1 (by rfl) ⟨2485061, by rfl⟩ : syracuseStep 3313415 = 4970123) B4970123
theorem B2208943 : Blo 2207435 2208943 := bstep (se 1 (by rfl) ⟨1656707, by rfl⟩ : syracuseStep 2208943 = 3313415) B3313415
theorem B3313421 : Blo 2207435 3313421 := bbase (se 3 (by rfl) ⟨621266, by rfl⟩ : syracuseStep 3313421 = 1242533) (by norm_num)
theorem B2208947 : Blo 2207435 2208947 := bstep (se 1 (by rfl) ⟨1656710, by rfl⟩ : syracuseStep 2208947 = 3313421) B3313421
theorem B4970141 : Blo 2207435 4970141 := bbase (se 3 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 4970141 = 1863803) (by norm_num)
theorem B3313427 : Blo 2207435 3313427 := bstep (se 1 (by rfl) ⟨2485070, by rfl⟩ : syracuseStep 3313427 = 4970141) B4970141
theorem B2208951 : Blo 2207435 2208951 := bstep (se 1 (by rfl) ⟨1656713, by rfl⟩ : syracuseStep 2208951 = 3313427) B3313427
theorem B3727613 : Blo 2207435 3727613 := bbase (se 3 (by rfl) ⟨698927, by rfl⟩ : syracuseStep 3727613 = 1397855) (by norm_num)
theorem B2485075 : Blo 2207435 2485075 := bstep (se 1 (by rfl) ⟨1863806, by rfl⟩ : syracuseStep 2485075 = 3727613) B3727613
theorem B3313433 : Blo 2207435 3313433 := bstep (se 2 (by rfl) ⟨1242537, by rfl⟩ : syracuseStep 3313433 = 2485075) B2485075
theorem B2208955 : Blo 2207435 2208955 := bstep (se 1 (by rfl) ⟨1656716, by rfl⟩ : syracuseStep 2208955 = 3313433) B3313433
theorem B7961237 : Blo 2207435 7961237 := bbase (se 6 (by rfl) ⟨186591, by rfl⟩ : syracuseStep 7961237 = 373183) (by norm_num)
theorem B5307491 : Blo 2207435 5307491 := bstep (se 1 (by rfl) ⟨3980618, by rfl⟩ : syracuseStep 5307491 = 7961237) B7961237
theorem B3538327 : Blo 2207435 3538327 := bstep (se 1 (by rfl) ⟨2653745, by rfl⟩ : syracuseStep 3538327 = 5307491) B5307491
theorem B4717769 : Blo 2207435 4717769 := bstep (se 2 (by rfl) ⟨1769163, by rfl⟩ : syracuseStep 4717769 = 3538327) B3538327
theorem B12580717 : Blo 2207435 12580717 := bstep (se 3 (by rfl) ⟨2358884, by rfl⟩ : syracuseStep 12580717 = 4717769) B4717769
theorem B16774289 : Blo 2207435 16774289 := bstep (se 2 (by rfl) ⟨6290358, by rfl⟩ : syracuseStep 16774289 = 12580717) B12580717
theorem B11182859 : Blo 2207435 11182859 := bstep (se 1 (by rfl) ⟨8387144, by rfl⟩ : syracuseStep 11182859 = 16774289) B16774289
theorem B7455239 : Blo 2207435 7455239 := bstep (se 1 (by rfl) ⟨5591429, by rfl⟩ : syracuseStep 7455239 = 11182859) B11182859
theorem B4970159 : Blo 2207435 4970159 := bstep (se 1 (by rfl) ⟨3727619, by rfl⟩ : syracuseStep 4970159 = 7455239) B7455239
theorem B3313439 : Blo 2207435 3313439 := bstep (se 1 (by rfl) ⟨2485079, by rfl⟩ : syracuseStep 3313439 = 4970159) B4970159
theorem B2208959 : Blo 2207435 2208959 := bstep (se 1 (by rfl) ⟨1656719, by rfl⟩ : syracuseStep 2208959 = 3313439) B3313439
theorem B3313445 : Blo 2207435 3313445 := bbase (se 4 (by rfl) ⟨310635, by rfl⟩ : syracuseStep 3313445 = 621271) (by norm_num)
theorem B2208963 : Blo 2207435 2208963 := bstep (se 1 (by rfl) ⟨1656722, by rfl⟩ : syracuseStep 2208963 = 3313445) B3313445
theorem B2795725 : Blo 2207435 2795725 := bbase (se 3 (by rfl) ⟨524198, by rfl⟩ : syracuseStep 2795725 = 1048397) (by norm_num)
theorem B3727633 : Blo 2207435 3727633 := bstep (se 2 (by rfl) ⟨1397862, by rfl⟩ : syracuseStep 3727633 = 2795725) B2795725
theorem B4970177 : Blo 2207435 4970177 := bstep (se 2 (by rfl) ⟨1863816, by rfl⟩ : syracuseStep 4970177 = 3727633) B3727633
theorem B3313451 : Blo 2207435 3313451 := bstep (se 1 (by rfl) ⟨2485088, by rfl⟩ : syracuseStep 3313451 = 4970177) B4970177
theorem B2208967 : Blo 2207435 2208967 := bstep (se 1 (by rfl) ⟨1656725, by rfl⟩ : syracuseStep 2208967 = 3313451) B3313451
theorem B2485093 : Blo 2207435 2485093 := bbase (se 4 (by rfl) ⟨232977, by rfl⟩ : syracuseStep 2485093 = 465955) (by norm_num)
theorem B3313457 : Blo 2207435 3313457 := bstep (se 2 (by rfl) ⟨1242546, by rfl⟩ : syracuseStep 3313457 = 2485093) B2485093
theorem B2208971 : Blo 2207435 2208971 := bstep (se 1 (by rfl) ⟨1656728, by rfl⟩ : syracuseStep 2208971 = 3313457) B3313457
theorem B6290405 : Blo 2207435 6290405 := bbase (se 4 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 6290405 = 1179451) (by norm_num)
theorem B4193603 : Blo 2207435 4193603 := bstep (se 1 (by rfl) ⟨3145202, by rfl⟩ : syracuseStep 4193603 = 6290405) B6290405
theorem B2795735 : Blo 2207435 2795735 := bstep (se 1 (by rfl) ⟨2096801, by rfl⟩ : syracuseStep 2795735 = 4193603) B4193603
theorem B7455293 : Blo 2207435 7455293 := bstep (se 3 (by rfl) ⟨1397867, by rfl⟩ : syracuseStep 7455293 = 2795735) B2795735
theorem B4970195 : Blo 2207435 4970195 := bstep (se 1 (by rfl) ⟨3727646, by rfl⟩ : syracuseStep 4970195 = 7455293) B7455293
theorem B3313463 : Blo 2207435 3313463 := bstep (se 1 (by rfl) ⟨2485097, by rfl⟩ : syracuseStep 3313463 = 4970195) B4970195
theorem B2208975 : Blo 2207435 2208975 := bstep (se 1 (by rfl) ⟨1656731, by rfl⟩ : syracuseStep 2208975 = 3313463) B3313463
theorem B3313469 : Blo 2207435 3313469 := bbase (se 3 (by rfl) ⟨621275, by rfl⟩ : syracuseStep 3313469 = 1242551) (by norm_num)
theorem B2208979 : Blo 2207435 2208979 := bstep (se 1 (by rfl) ⟨1656734, by rfl⟩ : syracuseStep 2208979 = 3313469) B3313469
theorem B4970213 : Blo 2207435 4970213 := bbase (se 4 (by rfl) ⟨465957, by rfl⟩ : syracuseStep 4970213 = 931915) (by norm_num)
theorem B3313475 : Blo 2207435 3313475 := bstep (se 1 (by rfl) ⟨2485106, by rfl⟩ : syracuseStep 3313475 = 4970213) B4970213
theorem B2208983 : Blo 2207435 2208983 := bstep (se 1 (by rfl) ⟨1656737, by rfl⟩ : syracuseStep 2208983 = 3313475) B3313475
theorem B5591501 : Blo 2207435 5591501 := bbase (se 3 (by rfl) ⟨1048406, by rfl⟩ : syracuseStep 5591501 = 2096813) (by norm_num)
theorem B3727667 : Blo 2207435 3727667 := bstep (se 1 (by rfl) ⟨2795750, by rfl⟩ : syracuseStep 3727667 = 5591501) B5591501
theorem B2485111 : Blo 2207435 2485111 := bstep (se 1 (by rfl) ⟨1863833, by rfl⟩ : syracuseStep 2485111 = 3727667) B3727667
theorem B3313481 : Blo 2207435 3313481 := bstep (se 2 (by rfl) ⟨1242555, by rfl⟩ : syracuseStep 3313481 = 2485111) B2485111
theorem B2208987 : Blo 2207435 2208987 := bstep (se 1 (by rfl) ⟨1656740, by rfl⟩ : syracuseStep 2208987 = 3313481) B3313481
theorem B3980677 : Blo 2207435 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B5307569 : Blo 2207435 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B3538379 : Blo 2207435 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B2358919 : Blo 2207435 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3145225 : Blo 2207435 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B4193633 : Blo 2207435 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B11183021 : Blo 2207435 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B7455347 : Blo 2207435 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B4970231 : Blo 2207435 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B3313487 : Blo 2207435 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B2208991 : Blo 2207435 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B3313493 : Blo 2207435 3313493 := bbase (se 9 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 3313493 = 19415) (by norm_num)
theorem B2208995 : Blo 2207435 2208995 := bstep (se 1 (by rfl) ⟨1656746, by rfl⟩ : syracuseStep 2208995 = 3313493) B3313493
theorem B17913109 : Blo 2207435 17913109 := bbase (se 6 (by rfl) ⟨419838, by rfl⟩ : syracuseStep 17913109 = 839677) (by norm_num)
theorem B23884145 : Blo 2207435 23884145 := bstep (se 2 (by rfl) ⟨8956554, by rfl⟩ : syracuseStep 23884145 = 17913109) B17913109
theorem B15922763 : Blo 2207435 15922763 := bstep (se 1 (by rfl) ⟨11942072, by rfl⟩ : syracuseStep 15922763 = 23884145) B23884145
theorem B10615175 : Blo 2207435 10615175 := bstep (se 1 (by rfl) ⟨7961381, by rfl⟩ : syracuseStep 10615175 = 15922763) B15922763
theorem B7076783 : Blo 2207435 7076783 := bstep (se 1 (by rfl) ⟨5307587, by rfl⟩ : syracuseStep 7076783 = 10615175) B10615175
theorem B4717855 : Blo 2207435 4717855 := bstep (se 1 (by rfl) ⟨3538391, by rfl⟩ : syracuseStep 4717855 = 7076783) B7076783
theorem B6290473 : Blo 2207435 6290473 := bstep (se 2 (by rfl) ⟨2358927, by rfl⟩ : syracuseStep 6290473 = 4717855) B4717855
theorem B8387297 : Blo 2207435 8387297 := bstep (se 2 (by rfl) ⟨3145236, by rfl⟩ : syracuseStep 8387297 = 6290473) B6290473
theorem B5591531 : Blo 2207435 5591531 := bstep (se 1 (by rfl) ⟨4193648, by rfl⟩ : syracuseStep 5591531 = 8387297) B8387297
theorem B3727687 : Blo 2207435 3727687 := bstep (se 1 (by rfl) ⟨2795765, by rfl⟩ : syracuseStep 3727687 = 5591531) B5591531
theorem B4970249 : Blo 2207435 4970249 := bstep (se 2 (by rfl) ⟨1863843, by rfl⟩ : syracuseStep 4970249 = 3727687) B3727687
theorem B3313499 : Blo 2207435 3313499 := bstep (se 1 (by rfl) ⟨2485124, by rfl⟩ : syracuseStep 3313499 = 4970249) B4970249
theorem B2208999 : Blo 2207435 2208999 := bstep (se 1 (by rfl) ⟨1656749, by rfl⟩ : syracuseStep 2208999 = 3313499) B3313499
theorem B2485129 : Blo 2207435 2485129 := bbase (se 2 (by rfl) ⟨931923, by rfl⟩ : syracuseStep 2485129 = 1863847) (by norm_num)
theorem B3313505 : Blo 2207435 3313505 := bstep (se 2 (by rfl) ⟨1242564, by rfl⟩ : syracuseStep 3313505 = 2485129) B2485129
theorem B2209003 : Blo 2207435 2209003 := bstep (se 1 (by rfl) ⟨1656752, by rfl⟩ : syracuseStep 2209003 = 3313505) B3313505
theorem B12270197 : Blo 2207435 12270197 := bbase (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) (by norm_num)
theorem B32720525 : Blo 2207435 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B21813683 : Blo 2207435 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B58169821 : Blo 2207435 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B77559761 : Blo 2207435 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B51706507 : Blo 2207435 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B68942009 : Blo 2207435 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B45961339 : Blo 2207435 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B61281785 : Blo 2207435 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B163418093 : Blo 2207435 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B108945395 : Blo 2207435 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B72630263 : Blo 2207435 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B48420175 : Blo 2207435 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B64560233 : Blo 2207435 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B43040155 : Blo 2207435 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B57386873 : Blo 2207435 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B38257915 : Blo 2207435 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B51010553 : Blo 2207435 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B34007035 : Blo 2207435 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B45342713 : Blo 2207435 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B30228475 : Blo 2207435 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B40304633 : Blo 2207435 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B107479021 : Blo 2207435 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B143305361 : Blo 2207435 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B95536907 : Blo 2207435 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B63691271 : Blo 2207435 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B42460847 : Blo 2207435 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B28307231 : Blo 2207435 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B18871487 : Blo 2207435 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B12580991 : Blo 2207435 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B8387327 : Blo 2207435 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B5591551 : Blo 2207435 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B7455401 : Blo 2207435 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B4970267 : Blo 2207435 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B3313511 : Blo 2207435 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B2209007 : Blo 2207435 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B3313517 : Blo 2207435 3313517 := bbase (se 3 (by rfl) ⟨621284, by rfl⟩ : syracuseStep 3313517 = 1242569) (by norm_num)
theorem B2209011 : Blo 2207435 2209011 := bstep (se 1 (by rfl) ⟨1656758, by rfl⟩ : syracuseStep 2209011 = 3313517) B3313517
theorem B4970285 : Blo 2207435 4970285 := bbase (se 3 (by rfl) ⟨931928, by rfl⟩ : syracuseStep 4970285 = 1863857) (by norm_num)
theorem B3313523 : Blo 2207435 3313523 := bstep (se 1 (by rfl) ⟨2485142, by rfl⟩ : syracuseStep 3313523 = 4970285) B4970285
theorem B2209015 : Blo 2207435 2209015 := bstep (se 1 (by rfl) ⟨1656761, by rfl⟩ : syracuseStep 2209015 = 3313523) B3313523
theorem B9435797 : Blo 2207435 9435797 := bbase (se 6 (by rfl) ⟨221151, by rfl⟩ : syracuseStep 9435797 = 442303) (by norm_num)
theorem B6290531 : Blo 2207435 6290531 := bstep (se 1 (by rfl) ⟨4717898, by rfl⟩ : syracuseStep 6290531 = 9435797) B9435797
theorem B4193687 : Blo 2207435 4193687 := bstep (se 1 (by rfl) ⟨3145265, by rfl⟩ : syracuseStep 4193687 = 6290531) B6290531
theorem B2795791 : Blo 2207435 2795791 := bstep (se 1 (by rfl) ⟨2096843, by rfl⟩ : syracuseStep 2795791 = 4193687) B4193687
theorem B3727721 : Blo 2207435 3727721 := bstep (se 2 (by rfl) ⟨1397895, by rfl⟩ : syracuseStep 3727721 = 2795791) B2795791
theorem B2485147 : Blo 2207435 2485147 := bstep (se 1 (by rfl) ⟨1863860, by rfl⟩ : syracuseStep 2485147 = 3727721) B3727721
theorem B3313529 : Blo 2207435 3313529 := bstep (se 2 (by rfl) ⟨1242573, by rfl⟩ : syracuseStep 3313529 = 2485147) B2485147
theorem B2209019 : Blo 2207435 2209019 := bstep (se 1 (by rfl) ⟨1656764, by rfl⟩ : syracuseStep 2209019 = 3313529) B3313529
theorem B14153717 : Blo 2207435 14153717 := bbase (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) (by norm_num)
theorem B37743245 : Blo 2207435 37743245 := bstep (se 3 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 37743245 = 14153717) B14153717
theorem B25162163 : Blo 2207435 25162163 := bstep (se 1 (by rfl) ⟨18871622, by rfl⟩ : syracuseStep 25162163 = 37743245) B37743245
theorem B16774775 : Blo 2207435 16774775 := bstep (se 1 (by rfl) ⟨12581081, by rfl⟩ : syracuseStep 16774775 = 25162163) B25162163
theorem B11183183 : Blo 2207435 11183183 := bstep (se 1 (by rfl) ⟨8387387, by rfl⟩ : syracuseStep 11183183 = 16774775) B16774775
theorem B7455455 : Blo 2207435 7455455 := bstep (se 1 (by rfl) ⟨5591591, by rfl⟩ : syracuseStep 7455455 = 11183183) B11183183
theorem B4970303 : Blo 2207435 4970303 := bstep (se 1 (by rfl) ⟨3727727, by rfl⟩ : syracuseStep 4970303 = 7455455) B7455455
theorem B3313535 : Blo 2207435 3313535 := bstep (se 1 (by rfl) ⟨2485151, by rfl⟩ : syracuseStep 3313535 = 4970303) B4970303
theorem B2209023 : Blo 2207435 2209023 := bstep (se 1 (by rfl) ⟨1656767, by rfl⟩ : syracuseStep 2209023 = 3313535) B3313535
theorem B3313541 : Blo 2207435 3313541 := bbase (se 4 (by rfl) ⟨310644, by rfl⟩ : syracuseStep 3313541 = 621289) (by norm_num)
theorem B2209027 : Blo 2207435 2209027 := bstep (se 1 (by rfl) ⟨1656770, by rfl⟩ : syracuseStep 2209027 = 3313541) B3313541
theorem B3727741 : Blo 2207435 3727741 := bbase (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) (by norm_num)
theorem B4970321 : Blo 2207435 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B3313547 : Blo 2207435 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B2209031 : Blo 2207435 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B2485165 : Blo 2207435 2485165 := bbase (se 3 (by rfl) ⟨465968, by rfl⟩ : syracuseStep 2485165 = 931937) (by norm_num)
theorem B3313553 : Blo 2207435 3313553 := bstep (se 2 (by rfl) ⟨1242582, by rfl⟩ : syracuseStep 3313553 = 2485165) B2485165
theorem B2209035 : Blo 2207435 2209035 := bstep (se 1 (by rfl) ⟨1656776, by rfl⟩ : syracuseStep 2209035 = 3313553) B3313553
theorem B7455509 : Blo 2207435 7455509 := bbase (se 6 (by rfl) ⟨174738, by rfl⟩ : syracuseStep 7455509 = 349477) (by norm_num)
theorem B4970339 : Blo 2207435 4970339 := bstep (se 1 (by rfl) ⟨3727754, by rfl⟩ : syracuseStep 4970339 = 7455509) B7455509
theorem B3313559 : Blo 2207435 3313559 := bstep (se 1 (by rfl) ⟨2485169, by rfl⟩ : syracuseStep 3313559 = 4970339) B4970339
theorem B2209039 : Blo 2207435 2209039 := bstep (se 1 (by rfl) ⟨1656779, by rfl⟩ : syracuseStep 2209039 = 3313559) B3313559
theorem B3313565 : Blo 2207435 3313565 := bbase (se 3 (by rfl) ⟨621293, by rfl⟩ : syracuseStep 3313565 = 1242587) (by norm_num)
theorem B2209043 : Blo 2207435 2209043 := bstep (se 1 (by rfl) ⟨1656782, by rfl⟩ : syracuseStep 2209043 = 3313565) B3313565
theorem B4970357 : Blo 2207435 4970357 := bbase (se 5 (by rfl) ⟨232985, by rfl⟩ : syracuseStep 4970357 = 465971) (by norm_num)
theorem B3313571 : Blo 2207435 3313571 := bstep (se 1 (by rfl) ⟨2485178, by rfl⟩ : syracuseStep 3313571 = 4970357) B4970357
theorem B2209047 : Blo 2207435 2209047 := bstep (se 1 (by rfl) ⟨1656785, by rfl⟩ : syracuseStep 2209047 = 3313571) B3313571
theorem B5038181 : Blo 2207435 5038181 := bbase (se 4 (by rfl) ⟨472329, by rfl⟩ : syracuseStep 5038181 = 944659) (by norm_num)
theorem B3358787 : Blo 2207435 3358787 := bstep (se 1 (by rfl) ⟨2519090, by rfl⟩ : syracuseStep 3358787 = 5038181) B5038181
theorem B8956765 : Blo 2207435 8956765 := bstep (se 3 (by rfl) ⟨1679393, by rfl⟩ : syracuseStep 8956765 = 3358787) B3358787
theorem B11942353 : Blo 2207435 11942353 := bstep (se 2 (by rfl) ⟨4478382, by rfl⟩ : syracuseStep 11942353 = 8956765) B8956765
theorem B15923137 : Blo 2207435 15923137 := bstep (se 2 (by rfl) ⟨5971176, by rfl⟩ : syracuseStep 15923137 = 11942353) B11942353
theorem B21230849 : Blo 2207435 21230849 := bstep (se 2 (by rfl) ⟨7961568, by rfl⟩ : syracuseStep 21230849 = 15923137) B15923137
theorem B14153899 : Blo 2207435 14153899 := bstep (se 1 (by rfl) ⟨10615424, by rfl⟩ : syracuseStep 14153899 = 21230849) B21230849
theorem B18871865 : Blo 2207435 18871865 := bstep (se 2 (by rfl) ⟨7076949, by rfl⟩ : syracuseStep 18871865 = 14153899) B14153899
theorem B12581243 : Blo 2207435 12581243 := bstep (se 1 (by rfl) ⟨9435932, by rfl⟩ : syracuseStep 12581243 = 18871865) B18871865
theorem B8387495 : Blo 2207435 8387495 := bstep (se 1 (by rfl) ⟨6290621, by rfl⟩ : syracuseStep 8387495 = 12581243) B12581243
theorem B5591663 : Blo 2207435 5591663 := bstep (se 1 (by rfl) ⟨4193747, by rfl⟩ : syracuseStep 5591663 = 8387495) B8387495
theorem B3727775 : Blo 2207435 3727775 := bstep (se 1 (by rfl) ⟨2795831, by rfl⟩ : syracuseStep 3727775 = 5591663) B5591663
theorem B2485183 : Blo 2207435 2485183 := bstep (se 1 (by rfl) ⟨1863887, by rfl⟩ : syracuseStep 2485183 = 3727775) B3727775
theorem B3313577 : Blo 2207435 3313577 := bstep (se 2 (by rfl) ⟨1242591, by rfl⟩ : syracuseStep 3313577 = 2485183) B2485183
theorem B2209051 : Blo 2207435 2209051 := bstep (se 1 (by rfl) ⟨1656788, by rfl⟩ : syracuseStep 2209051 = 3313577) B3313577
theorem B8387509 : Blo 2207435 8387509 := bbase (se 5 (by rfl) ⟨393164, by rfl⟩ : syracuseStep 8387509 = 786329) (by norm_num)
theorem B11183345 : Blo 2207435 11183345 := bstep (se 2 (by rfl) ⟨4193754, by rfl⟩ : syracuseStep 11183345 = 8387509) B8387509
theorem B7455563 : Blo 2207435 7455563 := bstep (se 1 (by rfl) ⟨5591672, by rfl⟩ : syracuseStep 7455563 = 11183345) B11183345
theorem B4970375 : Blo 2207435 4970375 := bstep (se 1 (by rfl) ⟨3727781, by rfl⟩ : syracuseStep 4970375 = 7455563) B7455563
theorem B3313583 : Blo 2207435 3313583 := bstep (se 1 (by rfl) ⟨2485187, by rfl⟩ : syracuseStep 3313583 = 4970375) B4970375
theorem B2209055 : Blo 2207435 2209055 := bstep (se 1 (by rfl) ⟨1656791, by rfl⟩ : syracuseStep 2209055 = 3313583) B3313583
theorem B3313589 : Blo 2207435 3313589 := bbase (se 5 (by rfl) ⟨155324, by rfl⟩ : syracuseStep 3313589 = 310649) (by norm_num)
theorem B2209059 : Blo 2207435 2209059 := bstep (se 1 (by rfl) ⟨1656794, by rfl⟩ : syracuseStep 2209059 = 3313589) B3313589
theorem B5591693 : Blo 2207435 5591693 := bbase (se 3 (by rfl) ⟨1048442, by rfl⟩ : syracuseStep 5591693 = 2096885) (by norm_num)
theorem B3727795 : Blo 2207435 3727795 := bstep (se 1 (by rfl) ⟨2795846, by rfl⟩ : syracuseStep 3727795 = 5591693) B5591693
theorem B4970393 : Blo 2207435 4970393 := bstep (se 2 (by rfl) ⟨1863897, by rfl⟩ : syracuseStep 4970393 = 3727795) B3727795
theorem B3313595 : Blo 2207435 3313595 := bstep (se 1 (by rfl) ⟨2485196, by rfl⟩ : syracuseStep 3313595 = 4970393) B4970393
theorem B2209063 : Blo 2207435 2209063 := bstep (se 1 (by rfl) ⟨1656797, by rfl⟩ : syracuseStep 2209063 = 3313595) B3313595
theorem B2485201 : Blo 2207435 2485201 := bbase (se 2 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 2485201 = 1863901) (by norm_num)
theorem B3313601 : Blo 2207435 3313601 := bstep (se 2 (by rfl) ⟨1242600, by rfl⟩ : syracuseStep 3313601 = 2485201) B2485201
theorem B2209067 : Blo 2207435 2209067 := bstep (se 1 (by rfl) ⟨1656800, by rfl⟩ : syracuseStep 2209067 = 3313601) B3313601
theorem B3980821 : Blo 2207435 3980821 := bbase (se 6 (by rfl) ⟨93300, by rfl⟩ : syracuseStep 3980821 = 186601) (by norm_num)
theorem B5307761 : Blo 2207435 5307761 := bstep (se 2 (by rfl) ⟨1990410, by rfl⟩ : syracuseStep 5307761 = 3980821) B3980821
theorem B3538507 : Blo 2207435 3538507 := bstep (se 1 (by rfl) ⟨2653880, by rfl⟩ : syracuseStep 3538507 = 5307761) B5307761
theorem B4718009 : Blo 2207435 4718009 := bstep (se 2 (by rfl) ⟨1769253, by rfl⟩ : syracuseStep 4718009 = 3538507) B3538507
theorem B3145339 : Blo 2207435 3145339 := bstep (se 1 (by rfl) ⟨2359004, by rfl⟩ : syracuseStep 3145339 = 4718009) B4718009
theorem B4193785 : Blo 2207435 4193785 := bstep (se 2 (by rfl) ⟨1572669, by rfl⟩ : syracuseStep 4193785 = 3145339) B3145339
theorem B5591713 : Blo 2207435 5591713 := bstep (se 2 (by rfl) ⟨2096892, by rfl⟩ : syracuseStep 5591713 = 4193785) B4193785
theorem B7455617 : Blo 2207435 7455617 := bstep (se 2 (by rfl) ⟨2795856, by rfl⟩ : syracuseStep 7455617 = 5591713) B5591713
theorem B4970411 : Blo 2207435 4970411 := bstep (se 1 (by rfl) ⟨3727808, by rfl⟩ : syracuseStep 4970411 = 7455617) B7455617
theorem B3313607 : Blo 2207435 3313607 := bstep (se 1 (by rfl) ⟨2485205, by rfl⟩ : syracuseStep 3313607 = 4970411) B4970411
theorem B2209071 : Blo 2207435 2209071 := bstep (se 1 (by rfl) ⟨1656803, by rfl⟩ : syracuseStep 2209071 = 3313607) B3313607
theorem B3313613 : Blo 2207435 3313613 := bbase (se 3 (by rfl) ⟨621302, by rfl⟩ : syracuseStep 3313613 = 1242605) (by norm_num)
theorem B2209075 : Blo 2207435 2209075 := bstep (se 1 (by rfl) ⟨1656806, by rfl⟩ : syracuseStep 2209075 = 3313613) B3313613
theorem B4970429 : Blo 2207435 4970429 := bbase (se 3 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 4970429 = 1863911) (by norm_num)
theorem B3313619 : Blo 2207435 3313619 := bstep (se 1 (by rfl) ⟨2485214, by rfl⟩ : syracuseStep 3313619 = 4970429) B4970429
theorem B2209079 : Blo 2207435 2209079 := bstep (se 1 (by rfl) ⟨1656809, by rfl⟩ : syracuseStep 2209079 = 3313619) B3313619
theorem B3727829 : Blo 2207435 3727829 := bbase (se 7 (by rfl) ⟨43685, by rfl⟩ : syracuseStep 3727829 = 87371) (by norm_num)
theorem B2485219 : Blo 2207435 2485219 := bstep (se 1 (by rfl) ⟨1863914, by rfl⟩ : syracuseStep 2485219 = 3727829) B3727829
theorem B3313625 : Blo 2207435 3313625 := bstep (se 2 (by rfl) ⟨1242609, by rfl⟩ : syracuseStep 3313625 = 2485219) B2485219
theorem B2209083 : Blo 2207435 2209083 := bstep (se 1 (by rfl) ⟨1656812, by rfl⟩ : syracuseStep 2209083 = 3313625) B3313625
theorem B9436085 : Blo 2207435 9436085 := bbase (se 5 (by rfl) ⟨442316, by rfl⟩ : syracuseStep 9436085 = 884633) (by norm_num)
theorem B6290723 : Blo 2207435 6290723 := bstep (se 1 (by rfl) ⟨4718042, by rfl⟩ : syracuseStep 6290723 = 9436085) B9436085
theorem B16775261 : Blo 2207435 16775261 := bstep (se 3 (by rfl) ⟨3145361, by rfl⟩ : syracuseStep 16775261 = 6290723) B6290723
theorem B11183507 : Blo 2207435 11183507 := bstep (se 1 (by rfl) ⟨8387630, by rfl⟩ : syracuseStep 11183507 = 16775261) B16775261
theorem B7455671 : Blo 2207435 7455671 := bstep (se 1 (by rfl) ⟨5591753, by rfl⟩ : syracuseStep 7455671 = 11183507) B11183507
theorem B4970447 : Blo 2207435 4970447 := bstep (se 1 (by rfl) ⟨3727835, by rfl⟩ : syracuseStep 4970447 = 7455671) B7455671
theorem B3313631 : Blo 2207435 3313631 := bstep (se 1 (by rfl) ⟨2485223, by rfl⟩ : syracuseStep 3313631 = 4970447) B4970447
theorem B2209087 : Blo 2207435 2209087 := bstep (se 1 (by rfl) ⟨1656815, by rfl⟩ : syracuseStep 2209087 = 3313631) B3313631
theorem B3313637 : Blo 2207435 3313637 := bbase (se 4 (by rfl) ⟨310653, by rfl⟩ : syracuseStep 3313637 = 621307) (by norm_num)
theorem B2209091 : Blo 2207435 2209091 := bstep (se 1 (by rfl) ⟨1656818, by rfl⟩ : syracuseStep 2209091 = 3313637) B3313637
theorem B10615637 : Blo 2207435 10615637 := bbase (se 9 (by rfl) ⟨31100, by rfl⟩ : syracuseStep 10615637 = 62201) (by norm_num)
theorem B7077091 : Blo 2207435 7077091 := bstep (se 1 (by rfl) ⟨5307818, by rfl⟩ : syracuseStep 7077091 = 10615637) B10615637
theorem B9436121 : Blo 2207435 9436121 := bstep (se 2 (by rfl) ⟨3538545, by rfl⟩ : syracuseStep 9436121 = 7077091) B7077091
theorem B6290747 : Blo 2207435 6290747 := bstep (se 1 (by rfl) ⟨4718060, by rfl⟩ : syracuseStep 6290747 = 9436121) B9436121
theorem B4193831 : Blo 2207435 4193831 := bstep (se 1 (by rfl) ⟨3145373, by rfl⟩ : syracuseStep 4193831 = 6290747) B6290747
theorem B2795887 : Blo 2207435 2795887 := bstep (se 1 (by rfl) ⟨2096915, by rfl⟩ : syracuseStep 2795887 = 4193831) B4193831
theorem B3727849 : Blo 2207435 3727849 := bstep (se 2 (by rfl) ⟨1397943, by rfl⟩ : syracuseStep 3727849 = 2795887) B2795887
theorem B4970465 : Blo 2207435 4970465 := bstep (se 2 (by rfl) ⟨1863924, by rfl⟩ : syracuseStep 4970465 = 3727849) B3727849
theorem B3313643 : Blo 2207435 3313643 := bstep (se 1 (by rfl) ⟨2485232, by rfl⟩ : syracuseStep 3313643 = 4970465) B4970465
theorem B2209095 : Blo 2207435 2209095 := bstep (se 1 (by rfl) ⟨1656821, by rfl⟩ : syracuseStep 2209095 = 3313643) B3313643
theorem B2485237 : Blo 2207435 2485237 := bbase (se 5 (by rfl) ⟨116495, by rfl⟩ : syracuseStep 2485237 = 232991) (by norm_num)
theorem B3313649 : Blo 2207435 3313649 := bstep (se 2 (by rfl) ⟨1242618, by rfl⟩ : syracuseStep 3313649 = 2485237) B2485237
theorem B2209099 : Blo 2207435 2209099 := bstep (se 1 (by rfl) ⟨1656824, by rfl⟩ : syracuseStep 2209099 = 3313649) B3313649
theorem B2795897 : Blo 2207435 2795897 := bbase (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) (by norm_num)
theorem B7455725 : Blo 2207435 7455725 := bstep (se 3 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 7455725 = 2795897) B2795897
theorem B4970483 : Blo 2207435 4970483 := bstep (se 1 (by rfl) ⟨3727862, by rfl⟩ : syracuseStep 4970483 = 7455725) B7455725
theorem B3313655 : Blo 2207435 3313655 := bstep (se 1 (by rfl) ⟨2485241, by rfl⟩ : syracuseStep 3313655 = 4970483) B4970483
theorem B2209103 : Blo 2207435 2209103 := bstep (se 1 (by rfl) ⟨1656827, by rfl⟩ : syracuseStep 2209103 = 3313655) B3313655
theorem B3313661 : Blo 2207435 3313661 := bbase (se 3 (by rfl) ⟨621311, by rfl⟩ : syracuseStep 3313661 = 1242623) (by norm_num)
theorem B2209107 : Blo 2207435 2209107 := bstep (se 1 (by rfl) ⟨1656830, by rfl⟩ : syracuseStep 2209107 = 3313661) B3313661
theorem B4970501 : Blo 2207435 4970501 := bbase (se 4 (by rfl) ⟨465984, by rfl⟩ : syracuseStep 4970501 = 931969) (by norm_num)
theorem B3313667 : Blo 2207435 3313667 := bstep (se 1 (by rfl) ⟨2485250, by rfl⟩ : syracuseStep 3313667 = 4970501) B4970501
theorem B2209111 : Blo 2207435 2209111 := bstep (se 1 (by rfl) ⟨1656833, by rfl⟩ : syracuseStep 2209111 = 3313667) B3313667
theorem B4193869 : Blo 2207435 4193869 := bbase (se 3 (by rfl) ⟨786350, by rfl⟩ : syracuseStep 4193869 = 1572701) (by norm_num)
theorem B5591825 : Blo 2207435 5591825 := bstep (se 2 (by rfl) ⟨2096934, by rfl⟩ : syracuseStep 5591825 = 4193869) B4193869
theorem B3727883 : Blo 2207435 3727883 := bstep (se 1 (by rfl) ⟨2795912, by rfl⟩ : syracuseStep 3727883 = 5591825) B5591825
theorem B2485255 : Blo 2207435 2485255 := bstep (se 1 (by rfl) ⟨1863941, by rfl⟩ : syracuseStep 2485255 = 3727883) B3727883
theorem B3313673 : Blo 2207435 3313673 := bstep (se 2 (by rfl) ⟨1242627, by rfl⟩ : syracuseStep 3313673 = 2485255) B2485255
theorem B2209115 : Blo 2207435 2209115 := bstep (se 1 (by rfl) ⟨1656836, by rfl⟩ : syracuseStep 2209115 = 3313673) B3313673
theorem B11183669 : Blo 2207435 11183669 := bbase (se 5 (by rfl) ⟨524234, by rfl⟩ : syracuseStep 11183669 = 1048469) (by norm_num)
theorem B7455779 : Blo 2207435 7455779 := bstep (se 1 (by rfl) ⟨5591834, by rfl⟩ : syracuseStep 7455779 = 11183669) B11183669
theorem B4970519 : Blo 2207435 4970519 := bstep (se 1 (by rfl) ⟨3727889, by rfl⟩ : syracuseStep 4970519 = 7455779) B7455779
theorem B3313679 : Blo 2207435 3313679 := bstep (se 1 (by rfl) ⟨2485259, by rfl⟩ : syracuseStep 3313679 = 4970519) B4970519
theorem B2209119 : Blo 2207435 2209119 := bstep (se 1 (by rfl) ⟨1656839, by rfl⟩ : syracuseStep 2209119 = 3313679) B3313679
theorem B3313685 : Blo 2207435 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B2209123 : Blo 2207435 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B9079285 : Blo 2207435 9079285 := bbase (se 5 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 9079285 = 851183) (by norm_num)
theorem B12105713 : Blo 2207435 12105713 := bstep (se 2 (by rfl) ⟨4539642, by rfl⟩ : syracuseStep 12105713 = 9079285) B9079285
theorem B8070475 : Blo 2207435 8070475 := bstep (se 1 (by rfl) ⟨6052856, by rfl⟩ : syracuseStep 8070475 = 12105713) B12105713
theorem B10760633 : Blo 2207435 10760633 := bstep (se 2 (by rfl) ⟨4035237, by rfl⟩ : syracuseStep 10760633 = 8070475) B8070475
theorem B7173755 : Blo 2207435 7173755 := bstep (se 1 (by rfl) ⟨5380316, by rfl⟩ : syracuseStep 7173755 = 10760633) B10760633
theorem B4782503 : Blo 2207435 4782503 := bstep (se 1 (by rfl) ⟨3586877, by rfl⟩ : syracuseStep 4782503 = 7173755) B7173755
theorem B3188335 : Blo 2207435 3188335 := bstep (se 1 (by rfl) ⟨2391251, by rfl⟩ : syracuseStep 3188335 = 4782503) B4782503
theorem B4251113 : Blo 2207435 4251113 := bstep (se 2 (by rfl) ⟨1594167, by rfl⟩ : syracuseStep 4251113 = 3188335) B3188335
theorem B2834075 : Blo 2207435 2834075 := bstep (se 1 (by rfl) ⟨2125556, by rfl⟩ : syracuseStep 2834075 = 4251113) B4251113
theorem B7557533 : Blo 2207435 7557533 := bstep (se 3 (by rfl) ⟨1417037, by rfl⟩ : syracuseStep 7557533 = 2834075) B2834075
theorem B5038355 : Blo 2207435 5038355 := bstep (se 1 (by rfl) ⟨3778766, by rfl⟩ : syracuseStep 5038355 = 7557533) B7557533
theorem B3358903 : Blo 2207435 3358903 := bstep (se 1 (by rfl) ⟨2519177, by rfl⟩ : syracuseStep 3358903 = 5038355) B5038355
theorem B4478537 : Blo 2207435 4478537 := bstep (se 2 (by rfl) ⟨1679451, by rfl⟩ : syracuseStep 4478537 = 3358903) B3358903
theorem B2985691 : Blo 2207435 2985691 := bstep (se 1 (by rfl) ⟨2239268, by rfl⟩ : syracuseStep 2985691 = 4478537) B4478537
theorem B3980921 : Blo 2207435 3980921 := bstep (se 2 (by rfl) ⟨1492845, by rfl⟩ : syracuseStep 3980921 = 2985691) B2985691
theorem B10615789 : Blo 2207435 10615789 := bstep (se 3 (by rfl) ⟨1990460, by rfl⟩ : syracuseStep 10615789 = 3980921) B3980921
theorem B14154385 : Blo 2207435 14154385 := bstep (se 2 (by rfl) ⟨5307894, by rfl⟩ : syracuseStep 14154385 = 10615789) B10615789
theorem B18872513 : Blo 2207435 18872513 := bstep (se 2 (by rfl) ⟨7077192, by rfl⟩ : syracuseStep 18872513 = 14154385) B14154385
theorem B12581675 : Blo 2207435 12581675 := bstep (se 1 (by rfl) ⟨9436256, by rfl⟩ : syracuseStep 12581675 = 18872513) B18872513
theorem B8387783 : Blo 2207435 8387783 := bstep (se 1 (by rfl) ⟨6290837, by rfl⟩ : syracuseStep 8387783 = 12581675) B12581675
theorem B5591855 : Blo 2207435 5591855 := bstep (se 1 (by rfl) ⟨4193891, by rfl⟩ : syracuseStep 5591855 = 8387783) B8387783
theorem B3727903 : Blo 2207435 3727903 := bstep (se 1 (by rfl) ⟨2795927, by rfl⟩ : syracuseStep 3727903 = 5591855) B5591855
theorem B4970537 : Blo 2207435 4970537 := bstep (se 2 (by rfl) ⟨1863951, by rfl⟩ : syracuseStep 4970537 = 3727903) B3727903
theorem B3313691 : Blo 2207435 3313691 := bstep (se 1 (by rfl) ⟨2485268, by rfl⟩ : syracuseStep 3313691 = 4970537) B4970537
theorem B2209127 : Blo 2207435 2209127 := bstep (se 1 (by rfl) ⟨1656845, by rfl⟩ : syracuseStep 2209127 = 3313691) B3313691
theorem B2485273 : Blo 2207435 2485273 := bbase (se 2 (by rfl) ⟨931977, by rfl⟩ : syracuseStep 2485273 = 1863955) (by norm_num)
theorem B3313697 : Blo 2207435 3313697 := bstep (se 2 (by rfl) ⟨1242636, by rfl⟩ : syracuseStep 3313697 = 2485273) B2485273
theorem B2209131 : Blo 2207435 2209131 := bstep (se 1 (by rfl) ⟨1656848, by rfl⟩ : syracuseStep 2209131 = 3313697) B3313697
theorem B8387813 : Blo 2207435 8387813 := bbase (se 4 (by rfl) ⟨786357, by rfl⟩ : syracuseStep 8387813 = 1572715) (by norm_num)
theorem B5591875 : Blo 2207435 5591875 := bstep (se 1 (by rfl) ⟨4193906, by rfl⟩ : syracuseStep 5591875 = 8387813) B8387813
theorem B7455833 : Blo 2207435 7455833 := bstep (se 2 (by rfl) ⟨2795937, by rfl⟩ : syracuseStep 7455833 = 5591875) B5591875
theorem B4970555 : Blo 2207435 4970555 := bstep (se 1 (by rfl) ⟨3727916, by rfl⟩ : syracuseStep 4970555 = 7455833) B7455833
theorem B3313703 : Blo 2207435 3313703 := bstep (se 1 (by rfl) ⟨2485277, by rfl⟩ : syracuseStep 3313703 = 4970555) B4970555
theorem B2209135 : Blo 2207435 2209135 := bstep (se 1 (by rfl) ⟨1656851, by rfl⟩ : syracuseStep 2209135 = 3313703) B3313703
theorem B3313709 : Blo 2207435 3313709 := bbase (se 3 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 3313709 = 1242641) (by norm_num)
theorem B2209139 : Blo 2207435 2209139 := bstep (se 1 (by rfl) ⟨1656854, by rfl⟩ : syracuseStep 2209139 = 3313709) B3313709
theorem B4970573 : Blo 2207435 4970573 := bbase (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) (by norm_num)
theorem B3313715 : Blo 2207435 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B2209143 : Blo 2207435 2209143 := bstep (se 1 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 2209143 = 3313715) B3313715
theorem B2795953 : Blo 2207435 2795953 := bbase (se 2 (by rfl) ⟨1048482, by rfl⟩ : syracuseStep 2795953 = 2096965) (by norm_num)
theorem B3727937 : Blo 2207435 3727937 := bstep (se 2 (by rfl) ⟨1397976, by rfl⟩ : syracuseStep 3727937 = 2795953) B2795953
theorem B2485291 : Blo 2207435 2485291 := bstep (se 1 (by rfl) ⟨1863968, by rfl⟩ : syracuseStep 2485291 = 3727937) B3727937
theorem B3313721 : Blo 2207435 3313721 := bstep (se 2 (by rfl) ⟨1242645, by rfl⟩ : syracuseStep 3313721 = 2485291) B2485291
theorem B2209147 : Blo 2207435 2209147 := bstep (se 1 (by rfl) ⟨1656860, by rfl⟩ : syracuseStep 2209147 = 3313721) B3313721
theorem B7077269 : Blo 2207435 7077269 := bbase (se 6 (by rfl) ⟨165873, by rfl⟩ : syracuseStep 7077269 = 331747) (by norm_num)
theorem B4718179 : Blo 2207435 4718179 := bstep (se 1 (by rfl) ⟨3538634, by rfl⟩ : syracuseStep 4718179 = 7077269) B7077269
theorem B25163621 : Blo 2207435 25163621 := bstep (se 4 (by rfl) ⟨2359089, by rfl⟩ : syracuseStep 25163621 = 4718179) B4718179
theorem B16775747 : Blo 2207435 16775747 := bstep (se 1 (by rfl) ⟨12581810, by rfl⟩ : syracuseStep 16775747 = 25163621) B25163621
theorem B11183831 : Blo 2207435 11183831 := bstep (se 1 (by rfl) ⟨8387873, by rfl⟩ : syracuseStep 11183831 = 16775747) B16775747
theorem B7455887 : Blo 2207435 7455887 := bstep (se 1 (by rfl) ⟨5591915, by rfl⟩ : syracuseStep 7455887 = 11183831) B11183831
theorem B4970591 : Blo 2207435 4970591 := bstep (se 1 (by rfl) ⟨3727943, by rfl⟩ : syracuseStep 4970591 = 7455887) B7455887
theorem B3313727 : Blo 2207435 3313727 := bstep (se 1 (by rfl) ⟨2485295, by rfl⟩ : syracuseStep 3313727 = 4970591) B4970591
theorem B2209151 : Blo 2207435 2209151 := bstep (se 1 (by rfl) ⟨1656863, by rfl⟩ : syracuseStep 2209151 = 3313727) B3313727
theorem B3313733 : Blo 2207435 3313733 := bbase (se 4 (by rfl) ⟨310662, by rfl⟩ : syracuseStep 3313733 = 621325) (by norm_num)
theorem B2209155 : Blo 2207435 2209155 := bstep (se 1 (by rfl) ⟨1656866, by rfl⟩ : syracuseStep 2209155 = 3313733) B3313733
theorem B3727957 : Blo 2207435 3727957 := bbase (se 8 (by rfl) ⟨21843, by rfl⟩ : syracuseStep 3727957 = 43687) (by norm_num)
theorem B4970609 : Blo 2207435 4970609 := bstep (se 2 (by rfl) ⟨1863978, by rfl⟩ : syracuseStep 4970609 = 3727957) B3727957
theorem B3313739 : Blo 2207435 3313739 := bstep (se 1 (by rfl) ⟨2485304, by rfl⟩ : syracuseStep 3313739 = 4970609) B4970609
theorem B2209159 : Blo 2207435 2209159 := bstep (se 1 (by rfl) ⟨1656869, by rfl⟩ : syracuseStep 2209159 = 3313739) B3313739
theorem B2485309 : Blo 2207435 2485309 := bbase (se 3 (by rfl) ⟨465995, by rfl⟩ : syracuseStep 2485309 = 931991) (by norm_num)
theorem B3313745 : Blo 2207435 3313745 := bstep (se 2 (by rfl) ⟨1242654, by rfl⟩ : syracuseStep 3313745 = 2485309) B2485309
theorem B2209163 : Blo 2207435 2209163 := bstep (se 1 (by rfl) ⟨1656872, by rfl⟩ : syracuseStep 2209163 = 3313745) B3313745
theorem B7455941 : Blo 2207435 7455941 := bbase (se 4 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 7455941 = 1397989) (by norm_num)
theorem B4970627 : Blo 2207435 4970627 := bstep (se 1 (by rfl) ⟨3727970, by rfl⟩ : syracuseStep 4970627 = 7455941) B7455941
theorem B3313751 : Blo 2207435 3313751 := bstep (se 1 (by rfl) ⟨2485313, by rfl⟩ : syracuseStep 3313751 = 4970627) B4970627
theorem B2209167 : Blo 2207435 2209167 := bstep (se 1 (by rfl) ⟨1656875, by rfl⟩ : syracuseStep 2209167 = 3313751) B3313751
theorem B3313757 : Blo 2207435 3313757 := bbase (se 3 (by rfl) ⟨621329, by rfl⟩ : syracuseStep 3313757 = 1242659) (by norm_num)
theorem B2209171 : Blo 2207435 2209171 := bstep (se 1 (by rfl) ⟨1656878, by rfl⟩ : syracuseStep 2209171 = 3313757) B3313757
theorem B4970645 : Blo 2207435 4970645 := bbase (se 6 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 4970645 = 232999) (by norm_num)
theorem B3313763 : Blo 2207435 3313763 := bstep (se 1 (by rfl) ⟨2485322, by rfl⟩ : syracuseStep 3313763 = 4970645) B4970645
theorem B2209175 : Blo 2207435 2209175 := bstep (se 1 (by rfl) ⟨1656881, by rfl⟩ : syracuseStep 2209175 = 3313763) B3313763
theorem B3145493 : Blo 2207435 3145493 := bbase (se 6 (by rfl) ⟨73722, by rfl⟩ : syracuseStep 3145493 = 147445) (by norm_num)
theorem B8387981 : Blo 2207435 8387981 := bstep (se 3 (by rfl) ⟨1572746, by rfl⟩ : syracuseStep 8387981 = 3145493) B3145493
theorem B5591987 : Blo 2207435 5591987 := bstep (se 1 (by rfl) ⟨4193990, by rfl⟩ : syracuseStep 5591987 = 8387981) B8387981
theorem B3727991 : Blo 2207435 3727991 := bstep (se 1 (by rfl) ⟨2795993, by rfl⟩ : syracuseStep 3727991 = 5591987) B5591987
theorem B2485327 : Blo 2207435 2485327 := bstep (se 1 (by rfl) ⟨1863995, by rfl⟩ : syracuseStep 2485327 = 3727991) B3727991
theorem B3313769 : Blo 2207435 3313769 := bstep (se 2 (by rfl) ⟨1242663, by rfl⟩ : syracuseStep 3313769 = 2485327) B2485327
theorem B2209179 : Blo 2207435 2209179 := bstep (se 1 (by rfl) ⟨1656884, by rfl⟩ : syracuseStep 2209179 = 3313769) B3313769
theorem B3778861 : Blo 2207435 3778861 := bbase (se 3 (by rfl) ⟨708536, by rfl⟩ : syracuseStep 3778861 = 1417073) (by norm_num)
theorem B5038481 : Blo 2207435 5038481 := bstep (se 2 (by rfl) ⟨1889430, by rfl⟩ : syracuseStep 5038481 = 3778861) B3778861
theorem B13435949 : Blo 2207435 13435949 := bstep (se 3 (by rfl) ⟨2519240, by rfl⟩ : syracuseStep 13435949 = 5038481) B5038481
theorem B8957299 : Blo 2207435 8957299 := bstep (se 1 (by rfl) ⟨6717974, by rfl⟩ : syracuseStep 8957299 = 13435949) B13435949
theorem B11943065 : Blo 2207435 11943065 := bstep (se 2 (by rfl) ⟨4478649, by rfl⟩ : syracuseStep 11943065 = 8957299) B8957299
theorem B31848173 : Blo 2207435 31848173 := bstep (se 3 (by rfl) ⟨5971532, by rfl⟩ : syracuseStep 31848173 = 11943065) B11943065
theorem B21232115 : Blo 2207435 21232115 := bstep (se 1 (by rfl) ⟨15924086, by rfl⟩ : syracuseStep 21232115 = 31848173) B31848173
theorem B14154743 : Blo 2207435 14154743 := bstep (se 1 (by rfl) ⟨10616057, by rfl⟩ : syracuseStep 14154743 = 21232115) B21232115
theorem B9436495 : Blo 2207435 9436495 := bstep (se 1 (by rfl) ⟨7077371, by rfl⟩ : syracuseStep 9436495 = 14154743) B14154743
theorem B12581993 : Blo 2207435 12581993 := bstep (se 2 (by rfl) ⟨4718247, by rfl⟩ : syracuseStep 12581993 = 9436495) B9436495
theorem B8387995 : Blo 2207435 8387995 := bstep (se 1 (by rfl) ⟨6290996, by rfl⟩ : syracuseStep 8387995 = 12581993) B12581993
theorem B11183993 : Blo 2207435 11183993 := bstep (se 2 (by rfl) ⟨4193997, by rfl⟩ : syracuseStep 11183993 = 8387995) B8387995
theorem B7455995 : Blo 2207435 7455995 := bstep (se 1 (by rfl) ⟨5591996, by rfl⟩ : syracuseStep 7455995 = 11183993) B11183993
theorem B4970663 : Blo 2207435 4970663 := bstep (se 1 (by rfl) ⟨3727997, by rfl⟩ : syracuseStep 4970663 = 7455995) B7455995
theorem B3313775 : Blo 2207435 3313775 := bstep (se 1 (by rfl) ⟨2485331, by rfl⟩ : syracuseStep 3313775 = 4970663) B4970663
theorem B2209183 : Blo 2207435 2209183 := bstep (se 1 (by rfl) ⟨1656887, by rfl⟩ : syracuseStep 2209183 = 3313775) B3313775
theorem B3313781 : Blo 2207435 3313781 := bbase (se 5 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 3313781 = 310667) (by norm_num)
theorem B2209187 : Blo 2207435 2209187 := bstep (se 1 (by rfl) ⟨1656890, by rfl⟩ : syracuseStep 2209187 = 3313781) B3313781
theorem B4194013 : Blo 2207435 4194013 := bbase (se 3 (by rfl) ⟨786377, by rfl⟩ : syracuseStep 4194013 = 1572755) (by norm_num)
theorem B5592017 : Blo 2207435 5592017 := bstep (se 2 (by rfl) ⟨2097006, by rfl⟩ : syracuseStep 5592017 = 4194013) B4194013
theorem B3728011 : Blo 2207435 3728011 := bstep (se 1 (by rfl) ⟨2796008, by rfl⟩ : syracuseStep 3728011 = 5592017) B5592017
theorem B4970681 : Blo 2207435 4970681 := bstep (se 2 (by rfl) ⟨1864005, by rfl⟩ : syracuseStep 4970681 = 3728011) B3728011
theorem B3313787 : Blo 2207435 3313787 := bstep (se 1 (by rfl) ⟨2485340, by rfl⟩ : syracuseStep 3313787 = 4970681) B4970681
theorem B2209191 : Blo 2207435 2209191 := bstep (se 1 (by rfl) ⟨1656893, by rfl⟩ : syracuseStep 2209191 = 3313787) B3313787
theorem B2485345 : Blo 2207435 2485345 := bbase (se 2 (by rfl) ⟨932004, by rfl⟩ : syracuseStep 2485345 = 1864009) (by norm_num)
theorem B3313793 : Blo 2207435 3313793 := bstep (se 2 (by rfl) ⟨1242672, by rfl⟩ : syracuseStep 3313793 = 2485345) B2485345
theorem B2209195 : Blo 2207435 2209195 := bstep (se 1 (by rfl) ⟨1656896, by rfl⟩ : syracuseStep 2209195 = 3313793) B3313793
theorem B5592037 : Blo 2207435 5592037 := bbase (se 4 (by rfl) ⟨524253, by rfl⟩ : syracuseStep 5592037 = 1048507) (by norm_num)
theorem B7456049 : Blo 2207435 7456049 := bstep (se 2 (by rfl) ⟨2796018, by rfl⟩ : syracuseStep 7456049 = 5592037) B5592037
theorem B4970699 : Blo 2207435 4970699 := bstep (se 1 (by rfl) ⟨3728024, by rfl⟩ : syracuseStep 4970699 = 7456049) B7456049
theorem B3313799 : Blo 2207435 3313799 := bstep (se 1 (by rfl) ⟨2485349, by rfl⟩ : syracuseStep 3313799 = 4970699) B4970699
theorem B2209199 : Blo 2207435 2209199 := bstep (se 1 (by rfl) ⟨1656899, by rfl⟩ : syracuseStep 2209199 = 3313799) B3313799
theorem B3313805 : Blo 2207435 3313805 := bbase (se 3 (by rfl) ⟨621338, by rfl⟩ : syracuseStep 3313805 = 1242677) (by norm_num)
theorem B2209203 : Blo 2207435 2209203 := bstep (se 1 (by rfl) ⟨1656902, by rfl⟩ : syracuseStep 2209203 = 3313805) B3313805
theorem B4970717 : Blo 2207435 4970717 := bbase (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) (by norm_num)
theorem B3313811 : Blo 2207435 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B2209207 : Blo 2207435 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B3728045 : Blo 2207435 3728045 := bbase (se 3 (by rfl) ⟨699008, by rfl⟩ : syracuseStep 3728045 = 1398017) (by norm_num)
theorem B2485363 : Blo 2207435 2485363 := bstep (se 1 (by rfl) ⟨1864022, by rfl⟩ : syracuseStep 2485363 = 3728045) B3728045
theorem B3313817 : Blo 2207435 3313817 := bstep (se 2 (by rfl) ⟨1242681, by rfl⟩ : syracuseStep 3313817 = 2485363) B2485363
theorem B2209211 : Blo 2207435 2209211 := bstep (se 1 (by rfl) ⟨1656908, by rfl⟩ : syracuseStep 2209211 = 3313817) B3313817
theorem B2239357 : Blo 2207435 2239357 := bbase (se 3 (by rfl) ⟨419879, by rfl⟩ : syracuseStep 2239357 = 839759) (by norm_num)
theorem B47772949 : Blo 2207435 47772949 := bstep (se 6 (by rfl) ⟨1119678, by rfl⟩ : syracuseStep 47772949 = 2239357) B2239357
theorem B63697265 : Blo 2207435 63697265 := bstep (se 2 (by rfl) ⟨23886474, by rfl⟩ : syracuseStep 63697265 = 47772949) B47772949
theorem B42464843 : Blo 2207435 42464843 := bstep (se 1 (by rfl) ⟨31848632, by rfl⟩ : syracuseStep 42464843 = 63697265) B63697265
theorem B28309895 : Blo 2207435 28309895 := bstep (se 1 (by rfl) ⟨21232421, by rfl⟩ : syracuseStep 28309895 = 42464843) B42464843
theorem B18873263 : Blo 2207435 18873263 := bstep (se 1 (by rfl) ⟨14154947, by rfl⟩ : syracuseStep 18873263 = 28309895) B28309895
theorem B12582175 : Blo 2207435 12582175 := bstep (se 1 (by rfl) ⟨9436631, by rfl⟩ : syracuseStep 12582175 = 18873263) B18873263
theorem B16776233 : Blo 2207435 16776233 := bstep (se 2 (by rfl) ⟨6291087, by rfl⟩ : syracuseStep 16776233 = 12582175) B12582175
theorem B11184155 : Blo 2207435 11184155 := bstep (se 1 (by rfl) ⟨8388116, by rfl⟩ : syracuseStep 11184155 = 16776233) B16776233
theorem B7456103 : Blo 2207435 7456103 := bstep (se 1 (by rfl) ⟨5592077, by rfl⟩ : syracuseStep 7456103 = 11184155) B11184155
theorem B4970735 : Blo 2207435 4970735 := bstep (se 1 (by rfl) ⟨3728051, by rfl⟩ : syracuseStep 4970735 = 7456103) B7456103
theorem B3313823 : Blo 2207435 3313823 := bstep (se 1 (by rfl) ⟨2485367, by rfl⟩ : syracuseStep 3313823 = 4970735) B4970735
theorem B2209215 : Blo 2207435 2209215 := bstep (se 1 (by rfl) ⟨1656911, by rfl⟩ : syracuseStep 2209215 = 3313823) B3313823
theorem B3313829 : Blo 2207435 3313829 := bbase (se 4 (by rfl) ⟨310671, by rfl⟩ : syracuseStep 3313829 = 621343) (by norm_num)
theorem B2209219 : Blo 2207435 2209219 := bstep (se 1 (by rfl) ⟨1656914, by rfl⟩ : syracuseStep 2209219 = 3313829) B3313829
theorem B2796049 : Blo 2207435 2796049 := bbase (se 2 (by rfl) ⟨1048518, by rfl⟩ : syracuseStep 2796049 = 2097037) (by norm_num)
theorem B3728065 : Blo 2207435 3728065 := bstep (se 2 (by rfl) ⟨1398024, by rfl⟩ : syracuseStep 3728065 = 2796049) B2796049
theorem B4970753 : Blo 2207435 4970753 := bstep (se 2 (by rfl) ⟨1864032, by rfl⟩ : syracuseStep 4970753 = 3728065) B3728065
theorem B3313835 : Blo 2207435 3313835 := bstep (se 1 (by rfl) ⟨2485376, by rfl⟩ : syracuseStep 3313835 = 4970753) B4970753
theorem B2209223 : Blo 2207435 2209223 := bstep (se 1 (by rfl) ⟨1656917, by rfl⟩ : syracuseStep 2209223 = 3313835) B3313835
theorem B2485381 : Blo 2207435 2485381 := bbase (se 4 (by rfl) ⟨233004, by rfl⟩ : syracuseStep 2485381 = 466009) (by norm_num)
theorem B3313841 : Blo 2207435 3313841 := bstep (se 2 (by rfl) ⟨1242690, by rfl⟩ : syracuseStep 3313841 = 2485381) B2485381
theorem B2209227 : Blo 2207435 2209227 := bstep (se 1 (by rfl) ⟨1656920, by rfl⟩ : syracuseStep 2209227 = 3313841) B3313841
theorem B15924437 : Blo 2207435 15924437 := bbase (se 7 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 15924437 = 373229) (by norm_num)
theorem B10616291 : Blo 2207435 10616291 := bstep (se 1 (by rfl) ⟨7962218, by rfl⟩ : syracuseStep 10616291 = 15924437) B15924437
theorem B7077527 : Blo 2207435 7077527 := bstep (se 1 (by rfl) ⟨5308145, by rfl⟩ : syracuseStep 7077527 = 10616291) B10616291
theorem B4718351 : Blo 2207435 4718351 := bstep (se 1 (by rfl) ⟨3538763, by rfl⟩ : syracuseStep 4718351 = 7077527) B7077527
theorem B3145567 : Blo 2207435 3145567 := bstep (se 1 (by rfl) ⟨2359175, by rfl⟩ : syracuseStep 3145567 = 4718351) B4718351
theorem B4194089 : Blo 2207435 4194089 := bstep (se 2 (by rfl) ⟨1572783, by rfl⟩ : syracuseStep 4194089 = 3145567) B3145567
theorem B2796059 : Blo 2207435 2796059 := bstep (se 1 (by rfl) ⟨2097044, by rfl⟩ : syracuseStep 2796059 = 4194089) B4194089
theorem B7456157 : Blo 2207435 7456157 := bstep (se 3 (by rfl) ⟨1398029, by rfl⟩ : syracuseStep 7456157 = 2796059) B2796059
theorem B4970771 : Blo 2207435 4970771 := bstep (se 1 (by rfl) ⟨3728078, by rfl⟩ : syracuseStep 4970771 = 7456157) B7456157
theorem B3313847 : Blo 2207435 3313847 := bstep (se 1 (by rfl) ⟨2485385, by rfl⟩ : syracuseStep 3313847 = 4970771) B4970771
theorem B2209231 : Blo 2207435 2209231 := bstep (se 1 (by rfl) ⟨1656923, by rfl⟩ : syracuseStep 2209231 = 3313847) B3313847
theorem B3313853 : Blo 2207435 3313853 := bbase (se 3 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 3313853 = 1242695) (by norm_num)
theorem B2209235 : Blo 2207435 2209235 := bstep (se 1 (by rfl) ⟨1656926, by rfl⟩ : syracuseStep 2209235 = 3313853) B3313853
theorem B4970789 : Blo 2207435 4970789 := bbase (se 4 (by rfl) ⟨466011, by rfl⟩ : syracuseStep 4970789 = 932023) (by norm_num)
theorem B3313859 : Blo 2207435 3313859 := bstep (se 1 (by rfl) ⟨2485394, by rfl⟩ : syracuseStep 3313859 = 4970789) B4970789
theorem B2209239 : Blo 2207435 2209239 := bstep (se 1 (by rfl) ⟨1656929, by rfl⟩ : syracuseStep 2209239 = 3313859) B3313859
theorem B5592149 : Blo 2207435 5592149 := bbase (se 8 (by rfl) ⟨32766, by rfl⟩ : syracuseStep 5592149 = 65533) (by norm_num)
theorem B3728099 : Blo 2207435 3728099 := bstep (se 1 (by rfl) ⟨2796074, by rfl⟩ : syracuseStep 3728099 = 5592149) B5592149
theorem B2485399 : Blo 2207435 2485399 := bstep (se 1 (by rfl) ⟨1864049, by rfl⟩ : syracuseStep 2485399 = 3728099) B3728099
theorem B3313865 : Blo 2207435 3313865 := bstep (se 2 (by rfl) ⟨1242699, by rfl⟩ : syracuseStep 3313865 = 2485399) B2485399
theorem B2209243 : Blo 2207435 2209243 := bstep (se 1 (by rfl) ⟨1656932, by rfl⟩ : syracuseStep 2209243 = 3313865) B3313865
theorem B11943413 : Blo 2207435 11943413 := bbase (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) (by norm_num)
theorem B7962275 : Blo 2207435 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B5308183 : Blo 2207435 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B7077577 : Blo 2207435 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B9436769 : Blo 2207435 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B6291179 : Blo 2207435 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B4194119 : Blo 2207435 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B11184317 : Blo 2207435 11184317 := bstep (se 3 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 11184317 = 4194119) B4194119
theorem B7456211 : Blo 2207435 7456211 := bstep (se 1 (by rfl) ⟨5592158, by rfl⟩ : syracuseStep 7456211 = 11184317) B11184317
theorem B4970807 : Blo 2207435 4970807 := bstep (se 1 (by rfl) ⟨3728105, by rfl⟩ : syracuseStep 4970807 = 7456211) B7456211
theorem B3313871 : Blo 2207435 3313871 := bstep (se 1 (by rfl) ⟨2485403, by rfl⟩ : syracuseStep 3313871 = 4970807) B4970807
theorem B2209247 : Blo 2207435 2209247 := bstep (se 1 (by rfl) ⟨1656935, by rfl⟩ : syracuseStep 2209247 = 3313871) B3313871
theorem B3313877 : Blo 2207435 3313877 := bbase (se 7 (by rfl) ⟨38834, by rfl⟩ : syracuseStep 3313877 = 77669) (by norm_num)
theorem B2209251 : Blo 2207435 2209251 := bstep (se 1 (by rfl) ⟨1656938, by rfl⟩ : syracuseStep 2209251 = 3313877) B3313877
theorem B2359201 : Blo 2207435 2359201 := bbase (se 2 (by rfl) ⟨884700, by rfl⟩ : syracuseStep 2359201 = 1769401) (by norm_num)
theorem B3145601 : Blo 2207435 3145601 := bstep (se 2 (by rfl) ⟨1179600, by rfl⟩ : syracuseStep 3145601 = 2359201) B2359201
theorem B8388269 : Blo 2207435 8388269 := bstep (se 3 (by rfl) ⟨1572800, by rfl⟩ : syracuseStep 8388269 = 3145601) B3145601
theorem B5592179 : Blo 2207435 5592179 := bstep (se 1 (by rfl) ⟨4194134, by rfl⟩ : syracuseStep 5592179 = 8388269) B8388269
theorem B3728119 : Blo 2207435 3728119 := bstep (se 1 (by rfl) ⟨2796089, by rfl⟩ : syracuseStep 3728119 = 5592179) B5592179
theorem B4970825 : Blo 2207435 4970825 := bstep (se 2 (by rfl) ⟨1864059, by rfl⟩ : syracuseStep 4970825 = 3728119) B3728119
theorem B3313883 : Blo 2207435 3313883 := bstep (se 1 (by rfl) ⟨2485412, by rfl⟩ : syracuseStep 3313883 = 4970825) B4970825
theorem B2209255 : Blo 2207435 2209255 := bstep (se 1 (by rfl) ⟨1656941, by rfl⟩ : syracuseStep 2209255 = 3313883) B3313883
theorem B2485417 : Blo 2207435 2485417 := bbase (se 2 (by rfl) ⟨932031, by rfl⟩ : syracuseStep 2485417 = 1864063) (by norm_num)
theorem B3313889 : Blo 2207435 3313889 := bstep (se 2 (by rfl) ⟨1242708, by rfl⟩ : syracuseStep 3313889 = 2485417) B2485417
theorem B2209259 : Blo 2207435 2209259 := bstep (se 1 (by rfl) ⟨1656944, by rfl⟩ : syracuseStep 2209259 = 3313889) B3313889
theorem B9436837 : Blo 2207435 9436837 := bbase (se 4 (by rfl) ⟨884703, by rfl⟩ : syracuseStep 9436837 = 1769407) (by norm_num)
theorem B12582449 : Blo 2207435 12582449 := bstep (se 2 (by rfl) ⟨4718418, by rfl⟩ : syracuseStep 12582449 = 9436837) B9436837
theorem B8388299 : Blo 2207435 8388299 := bstep (se 1 (by rfl) ⟨6291224, by rfl⟩ : syracuseStep 8388299 = 12582449) B12582449
theorem B5592199 : Blo 2207435 5592199 := bstep (se 1 (by rfl) ⟨4194149, by rfl⟩ : syracuseStep 5592199 = 8388299) B8388299
theorem B7456265 : Blo 2207435 7456265 := bstep (se 2 (by rfl) ⟨2796099, by rfl⟩ : syracuseStep 7456265 = 5592199) B5592199
theorem B4970843 : Blo 2207435 4970843 := bstep (se 1 (by rfl) ⟨3728132, by rfl⟩ : syracuseStep 4970843 = 7456265) B7456265
theorem B3313895 : Blo 2207435 3313895 := bstep (se 1 (by rfl) ⟨2485421, by rfl⟩ : syracuseStep 3313895 = 4970843) B4970843
theorem B2209263 : Blo 2207435 2209263 := bstep (se 1 (by rfl) ⟨1656947, by rfl⟩ : syracuseStep 2209263 = 3313895) B3313895
theorem B3313901 : Blo 2207435 3313901 := bbase (se 3 (by rfl) ⟨621356, by rfl⟩ : syracuseStep 3313901 = 1242713) (by norm_num)
theorem B2209267 : Blo 2207435 2209267 := bstep (se 1 (by rfl) ⟨1656950, by rfl⟩ : syracuseStep 2209267 = 3313901) B3313901
theorem B4970861 : Blo 2207435 4970861 := bbase (se 3 (by rfl) ⟨932036, by rfl⟩ : syracuseStep 4970861 = 1864073) (by norm_num)
theorem B3313907 : Blo 2207435 3313907 := bstep (se 1 (by rfl) ⟨2485430, by rfl⟩ : syracuseStep 3313907 = 4970861) B4970861
theorem B2209271 : Blo 2207435 2209271 := bstep (se 1 (by rfl) ⟨1656953, by rfl⟩ : syracuseStep 2209271 = 3313907) B3313907
theorem B4194173 : Blo 2207435 4194173 := bbase (se 3 (by rfl) ⟨786407, by rfl⟩ : syracuseStep 4194173 = 1572815) (by norm_num)
theorem B2796115 : Blo 2207435 2796115 := bstep (se 1 (by rfl) ⟨2097086, by rfl⟩ : syracuseStep 2796115 = 4194173) B4194173
theorem B3728153 : Blo 2207435 3728153 := bstep (se 2 (by rfl) ⟨1398057, by rfl⟩ : syracuseStep 3728153 = 2796115) B2796115
theorem B2485435 : Blo 2207435 2485435 := bstep (se 1 (by rfl) ⟨1864076, by rfl⟩ : syracuseStep 2485435 = 3728153) B3728153
theorem B3313913 : Blo 2207435 3313913 := bstep (se 2 (by rfl) ⟨1242717, by rfl⟩ : syracuseStep 3313913 = 2485435) B2485435
theorem B2209275 : Blo 2207435 2209275 := bstep (se 1 (by rfl) ⟨1656956, by rfl⟩ : syracuseStep 2209275 = 3313913) B3313913
theorem B7962389 : Blo 2207435 7962389 := bbase (se 6 (by rfl) ⟨186618, by rfl⟩ : syracuseStep 7962389 = 373237) (by norm_num)
theorem B5308259 : Blo 2207435 5308259 := bstep (se 1 (by rfl) ⟨3981194, by rfl⟩ : syracuseStep 5308259 = 7962389) B7962389
theorem B56621429 : Blo 2207435 56621429 := bstep (se 5 (by rfl) ⟨2654129, by rfl⟩ : syracuseStep 56621429 = 5308259) B5308259
theorem B37747619 : Blo 2207435 37747619 := bstep (se 1 (by rfl) ⟨28310714, by rfl⟩ : syracuseStep 37747619 = 56621429) B56621429
theorem B25165079 : Blo 2207435 25165079 := bstep (se 1 (by rfl) ⟨18873809, by rfl⟩ : syracuseStep 25165079 = 37747619) B37747619
theorem B16776719 : Blo 2207435 16776719 := bstep (se 1 (by rfl) ⟨12582539, by rfl⟩ : syracuseStep 16776719 = 25165079) B25165079
theorem B11184479 : Blo 2207435 11184479 := bstep (se 1 (by rfl) ⟨8388359, by rfl⟩ : syracuseStep 11184479 = 16776719) B16776719
theorem B7456319 : Blo 2207435 7456319 := bstep (se 1 (by rfl) ⟨5592239, by rfl⟩ : syracuseStep 7456319 = 11184479) B11184479
theorem B4970879 : Blo 2207435 4970879 := bstep (se 1 (by rfl) ⟨3728159, by rfl⟩ : syracuseStep 4970879 = 7456319) B7456319
theorem B3313919 : Blo 2207435 3313919 := bstep (se 1 (by rfl) ⟨2485439, by rfl⟩ : syracuseStep 3313919 = 4970879) B4970879
theorem B2209279 : Blo 2207435 2209279 := bstep (se 1 (by rfl) ⟨1656959, by rfl⟩ : syracuseStep 2209279 = 3313919) B3313919
theorem B3313925 : Blo 2207435 3313925 := bbase (se 4 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 3313925 = 621361) (by norm_num)
theorem B2209283 : Blo 2207435 2209283 := bstep (se 1 (by rfl) ⟨1656962, by rfl⟩ : syracuseStep 2209283 = 3313925) B3313925
theorem B3728173 : Blo 2207435 3728173 := bbase (se 3 (by rfl) ⟨699032, by rfl⟩ : syracuseStep 3728173 = 1398065) (by norm_num)
theorem B4970897 : Blo 2207435 4970897 := bstep (se 2 (by rfl) ⟨1864086, by rfl⟩ : syracuseStep 4970897 = 3728173) B3728173
theorem B3313931 : Blo 2207435 3313931 := bstep (se 1 (by rfl) ⟨2485448, by rfl⟩ : syracuseStep 3313931 = 4970897) B4970897
theorem B2209287 : Blo 2207435 2209287 := bstep (se 1 (by rfl) ⟨1656965, by rfl⟩ : syracuseStep 2209287 = 3313931) B3313931
theorem B2485453 : Blo 2207435 2485453 := bbase (se 3 (by rfl) ⟨466022, by rfl⟩ : syracuseStep 2485453 = 932045) (by norm_num)
theorem B3313937 : Blo 2207435 3313937 := bstep (se 2 (by rfl) ⟨1242726, by rfl⟩ : syracuseStep 3313937 = 2485453) B2485453
theorem B2209291 : Blo 2207435 2209291 := bstep (se 1 (by rfl) ⟨1656968, by rfl⟩ : syracuseStep 2209291 = 3313937) B3313937
theorem B7456373 : Blo 2207435 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B4970915 : Blo 2207435 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B3313943 : Blo 2207435 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B2209295 : Blo 2207435 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B3313949 : Blo 2207435 3313949 := bbase (se 3 (by rfl) ⟨621365, by rfl⟩ : syracuseStep 3313949 = 1242731) (by norm_num)
theorem B2209299 : Blo 2207435 2209299 := bstep (se 1 (by rfl) ⟨1656974, by rfl⟩ : syracuseStep 2209299 = 3313949) B3313949
theorem B4970933 : Blo 2207435 4970933 := bbase (se 5 (by rfl) ⟨233012, by rfl⟩ : syracuseStep 4970933 = 466025) (by norm_num)
theorem B3313955 : Blo 2207435 3313955 := bstep (se 1 (by rfl) ⟨2485466, by rfl⟩ : syracuseStep 3313955 = 4970933) B4970933
theorem B2209303 : Blo 2207435 2209303 := bstep (se 1 (by rfl) ⟨1656977, by rfl⟩ : syracuseStep 2209303 = 3313955) B3313955
theorem B3538885 : Blo 2207435 3538885 := bbase (se 4 (by rfl) ⟨331770, by rfl⟩ : syracuseStep 3538885 = 663541) (by norm_num)
theorem B4718513 : Blo 2207435 4718513 := bstep (se 2 (by rfl) ⟨1769442, by rfl⟩ : syracuseStep 4718513 = 3538885) B3538885
theorem B12582701 : Blo 2207435 12582701 := bstep (se 3 (by rfl) ⟨2359256, by rfl⟩ : syracuseStep 12582701 = 4718513) B4718513
theorem B8388467 : Blo 2207435 8388467 := bstep (se 1 (by rfl) ⟨6291350, by rfl⟩ : syracuseStep 8388467 = 12582701) B12582701
theorem B5592311 : Blo 2207435 5592311 := bstep (se 1 (by rfl) ⟨4194233, by rfl⟩ : syracuseStep 5592311 = 8388467) B8388467
theorem B3728207 : Blo 2207435 3728207 := bstep (se 1 (by rfl) ⟨2796155, by rfl⟩ : syracuseStep 3728207 = 5592311) B5592311
theorem B2485471 : Blo 2207435 2485471 := bstep (se 1 (by rfl) ⟨1864103, by rfl⟩ : syracuseStep 2485471 = 3728207) B3728207
theorem B3313961 : Blo 2207435 3313961 := bstep (se 2 (by rfl) ⟨1242735, by rfl⟩ : syracuseStep 3313961 = 2485471) B2485471
theorem B2209307 : Blo 2207435 2209307 := bstep (se 1 (by rfl) ⟨1656980, by rfl⟩ : syracuseStep 2209307 = 3313961) B3313961
theorem B3981253 : Blo 2207435 3981253 := bbase (se 4 (by rfl) ⟨373242, by rfl⟩ : syracuseStep 3981253 = 746485) (by norm_num)
theorem B5308337 : Blo 2207435 5308337 := bstep (se 2 (by rfl) ⟨1990626, by rfl⟩ : syracuseStep 5308337 = 3981253) B3981253
theorem B3538891 : Blo 2207435 3538891 := bstep (se 1 (by rfl) ⟨2654168, by rfl⟩ : syracuseStep 3538891 = 5308337) B5308337
theorem B4718521 : Blo 2207435 4718521 := bstep (se 2 (by rfl) ⟨1769445, by rfl⟩ : syracuseStep 4718521 = 3538891) B3538891
theorem B6291361 : Blo 2207435 6291361 := bstep (se 2 (by rfl) ⟨2359260, by rfl⟩ : syracuseStep 6291361 = 4718521) B4718521
theorem B8388481 : Blo 2207435 8388481 := bstep (se 2 (by rfl) ⟨3145680, by rfl⟩ : syracuseStep 8388481 = 6291361) B6291361
theorem B11184641 : Blo 2207435 11184641 := bstep (se 2 (by rfl) ⟨4194240, by rfl⟩ : syracuseStep 11184641 = 8388481) B8388481
theorem B7456427 : Blo 2207435 7456427 := bstep (se 1 (by rfl) ⟨5592320, by rfl⟩ : syracuseStep 7456427 = 11184641) B11184641
theorem B4970951 : Blo 2207435 4970951 := bstep (se 1 (by rfl) ⟨3728213, by rfl⟩ : syracuseStep 4970951 = 7456427) B7456427
theorem B3313967 : Blo 2207435 3313967 := bstep (se 1 (by rfl) ⟨2485475, by rfl⟩ : syracuseStep 3313967 = 4970951) B4970951
theorem B2209311 : Blo 2207435 2209311 := bstep (se 1 (by rfl) ⟨1656983, by rfl⟩ : syracuseStep 2209311 = 3313967) B3313967
theorem B3313973 : Blo 2207435 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B2209315 : Blo 2207435 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B5592341 : Blo 2207435 5592341 := bbase (se 6 (by rfl) ⟨131070, by rfl⟩ : syracuseStep 5592341 = 262141) (by norm_num)
theorem B3728227 : Blo 2207435 3728227 := bstep (se 1 (by rfl) ⟨2796170, by rfl⟩ : syracuseStep 3728227 = 5592341) B5592341
theorem B4970969 : Blo 2207435 4970969 := bstep (se 2 (by rfl) ⟨1864113, by rfl⟩ : syracuseStep 4970969 = 3728227) B3728227
theorem B3313979 : Blo 2207435 3313979 := bstep (se 1 (by rfl) ⟨2485484, by rfl⟩ : syracuseStep 3313979 = 4970969) B4970969
theorem B2209319 : Blo 2207435 2209319 := bstep (se 1 (by rfl) ⟨1656989, by rfl⟩ : syracuseStep 2209319 = 3313979) B3313979
theorem B2485489 : Blo 2207435 2485489 := bbase (se 2 (by rfl) ⟨932058, by rfl⟩ : syracuseStep 2485489 = 1864117) (by norm_num)
theorem B3313985 : Blo 2207435 3313985 := bstep (se 2 (by rfl) ⟨1242744, by rfl⟩ : syracuseStep 3313985 = 2485489) B2485489
theorem B2209323 : Blo 2207435 2209323 := bstep (se 1 (by rfl) ⟨1656992, by rfl⟩ : syracuseStep 2209323 = 3313985) B3313985
theorem B10761605 : Blo 2207435 10761605 := bbase (se 4 (by rfl) ⟨1008900, by rfl⟩ : syracuseStep 10761605 = 2017801) (by norm_num)
theorem B7174403 : Blo 2207435 7174403 := bstep (se 1 (by rfl) ⟨5380802, by rfl⟩ : syracuseStep 7174403 = 10761605) B10761605
theorem B4782935 : Blo 2207435 4782935 := bstep (se 1 (by rfl) ⟨3587201, by rfl⟩ : syracuseStep 4782935 = 7174403) B7174403
theorem B12754493 : Blo 2207435 12754493 := bstep (se 3 (by rfl) ⟨2391467, by rfl⟩ : syracuseStep 12754493 = 4782935) B4782935
theorem B8502995 : Blo 2207435 8502995 := bstep (se 1 (by rfl) ⟨6377246, by rfl⟩ : syracuseStep 8502995 = 12754493) B12754493
theorem B5668663 : Blo 2207435 5668663 := bstep (se 1 (by rfl) ⟨4251497, by rfl⟩ : syracuseStep 5668663 = 8502995) B8502995
theorem B7558217 : Blo 2207435 7558217 := bstep (se 2 (by rfl) ⟨2834331, by rfl⟩ : syracuseStep 7558217 = 5668663) B5668663
theorem B5038811 : Blo 2207435 5038811 := bstep (se 1 (by rfl) ⟨3779108, by rfl⟩ : syracuseStep 5038811 = 7558217) B7558217
theorem B3359207 : Blo 2207435 3359207 := bstep (se 1 (by rfl) ⟨2519405, by rfl⟩ : syracuseStep 3359207 = 5038811) B5038811
theorem B2239471 : Blo 2207435 2239471 := bstep (se 1 (by rfl) ⟨1679603, by rfl⟩ : syracuseStep 2239471 = 3359207) B3359207
theorem B11943845 : Blo 2207435 11943845 := bstep (se 4 (by rfl) ⟨1119735, by rfl⟩ : syracuseStep 11943845 = 2239471) B2239471
theorem B7962563 : Blo 2207435 7962563 := bstep (se 1 (by rfl) ⟨5971922, by rfl⟩ : syracuseStep 7962563 = 11943845) B11943845
theorem B21233501 : Blo 2207435 21233501 := bstep (se 3 (by rfl) ⟨3981281, by rfl⟩ : syracuseStep 21233501 = 7962563) B7962563
theorem B14155667 : Blo 2207435 14155667 := bstep (se 1 (by rfl) ⟨10616750, by rfl⟩ : syracuseStep 14155667 = 21233501) B21233501
theorem B9437111 : Blo 2207435 9437111 := bstep (se 1 (by rfl) ⟨7077833, by rfl⟩ : syracuseStep 9437111 = 14155667) B14155667
theorem B6291407 : Blo 2207435 6291407 := bstep (se 1 (by rfl) ⟨4718555, by rfl⟩ : syracuseStep 6291407 = 9437111) B9437111
theorem B4194271 : Blo 2207435 4194271 := bstep (se 1 (by rfl) ⟨3145703, by rfl⟩ : syracuseStep 4194271 = 6291407) B6291407
theorem B5592361 : Blo 2207435 5592361 := bstep (se 2 (by rfl) ⟨2097135, by rfl⟩ : syracuseStep 5592361 = 4194271) B4194271
theorem B7456481 : Blo 2207435 7456481 := bstep (se 2 (by rfl) ⟨2796180, by rfl⟩ : syracuseStep 7456481 = 5592361) B5592361
theorem B4970987 : Blo 2207435 4970987 := bstep (se 1 (by rfl) ⟨3728240, by rfl⟩ : syracuseStep 4970987 = 7456481) B7456481
theorem B3313991 : Blo 2207435 3313991 := bstep (se 1 (by rfl) ⟨2485493, by rfl⟩ : syracuseStep 3313991 = 4970987) B4970987
theorem B2209327 : Blo 2207435 2209327 := bstep (se 1 (by rfl) ⟨1656995, by rfl⟩ : syracuseStep 2209327 = 3313991) B3313991
theorem B3313997 : Blo 2207435 3313997 := bbase (se 3 (by rfl) ⟨621374, by rfl⟩ : syracuseStep 3313997 = 1242749) (by norm_num)
theorem B2209331 : Blo 2207435 2209331 := bstep (se 1 (by rfl) ⟨1656998, by rfl⟩ : syracuseStep 2209331 = 3313997) B3313997
theorem B4971005 : Blo 2207435 4971005 := bbase (se 3 (by rfl) ⟨932063, by rfl⟩ : syracuseStep 4971005 = 1864127) (by norm_num)
theorem B3314003 : Blo 2207435 3314003 := bstep (se 1 (by rfl) ⟨2485502, by rfl⟩ : syracuseStep 3314003 = 4971005) B4971005
theorem B2209335 : Blo 2207435 2209335 := bstep (se 1 (by rfl) ⟨1657001, by rfl⟩ : syracuseStep 2209335 = 3314003) B3314003
theorem B3728261 : Blo 2207435 3728261 := bbase (se 4 (by rfl) ⟨349524, by rfl⟩ : syracuseStep 3728261 = 699049) (by norm_num)
theorem B2485507 : Blo 2207435 2485507 := bstep (se 1 (by rfl) ⟨1864130, by rfl⟩ : syracuseStep 2485507 = 3728261) B3728261
theorem B3314009 : Blo 2207435 3314009 := bstep (se 2 (by rfl) ⟨1242753, by rfl⟩ : syracuseStep 3314009 = 2485507) B2485507
theorem B2209339 : Blo 2207435 2209339 := bstep (se 1 (by rfl) ⟨1657004, by rfl⟩ : syracuseStep 2209339 = 3314009) B3314009
theorem B16777205 : Blo 2207435 16777205 := bbase (se 5 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 16777205 = 1572863) (by norm_num)
theorem B11184803 : Blo 2207435 11184803 := bstep (se 1 (by rfl) ⟨8388602, by rfl⟩ : syracuseStep 11184803 = 16777205) B16777205
theorem B7456535 : Blo 2207435 7456535 := bstep (se 1 (by rfl) ⟨5592401, by rfl⟩ : syracuseStep 7456535 = 11184803) B11184803
theorem B4971023 : Blo 2207435 4971023 := bstep (se 1 (by rfl) ⟨3728267, by rfl⟩ : syracuseStep 4971023 = 7456535) B7456535
theorem B3314015 : Blo 2207435 3314015 := bstep (se 1 (by rfl) ⟨2485511, by rfl⟩ : syracuseStep 3314015 = 4971023) B4971023
theorem B2209343 : Blo 2207435 2209343 := bstep (se 1 (by rfl) ⟨1657007, by rfl⟩ : syracuseStep 2209343 = 3314015) B3314015
theorem B3314021 : Blo 2207435 3314021 := bbase (se 4 (by rfl) ⟨310689, by rfl⟩ : syracuseStep 3314021 = 621379) (by norm_num)
theorem B2209347 : Blo 2207435 2209347 := bstep (se 1 (by rfl) ⟨1657010, by rfl⟩ : syracuseStep 2209347 = 3314021) B3314021
theorem B4194317 : Blo 2207435 4194317 := bbase (se 3 (by rfl) ⟨786434, by rfl⟩ : syracuseStep 4194317 = 1572869) (by norm_num)
theorem B2796211 : Blo 2207435 2796211 := bstep (se 1 (by rfl) ⟨2097158, by rfl⟩ : syracuseStep 2796211 = 4194317) B4194317
theorem B3728281 : Blo 2207435 3728281 := bstep (se 2 (by rfl) ⟨1398105, by rfl⟩ : syracuseStep 3728281 = 2796211) B2796211
theorem B4971041 : Blo 2207435 4971041 := bstep (se 2 (by rfl) ⟨1864140, by rfl⟩ : syracuseStep 4971041 = 3728281) B3728281
theorem B3314027 : Blo 2207435 3314027 := bstep (se 1 (by rfl) ⟨2485520, by rfl⟩ : syracuseStep 3314027 = 4971041) B4971041
theorem B2209351 : Blo 2207435 2209351 := bstep (se 1 (by rfl) ⟨1657013, by rfl⟩ : syracuseStep 2209351 = 3314027) B3314027
theorem B2485525 : Blo 2207435 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B3314033 : Blo 2207435 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B2209355 : Blo 2207435 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B2796221 : Blo 2207435 2796221 := bbase (se 3 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 2796221 = 1048583) (by norm_num)
theorem B7456589 : Blo 2207435 7456589 := bstep (se 3 (by rfl) ⟨1398110, by rfl⟩ : syracuseStep 7456589 = 2796221) B2796221
theorem B4971059 : Blo 2207435 4971059 := bstep (se 1 (by rfl) ⟨3728294, by rfl⟩ : syracuseStep 4971059 = 7456589) B7456589
theorem B3314039 : Blo 2207435 3314039 := bstep (se 1 (by rfl) ⟨2485529, by rfl⟩ : syracuseStep 3314039 = 4971059) B4971059
theorem B2209359 : Blo 2207435 2209359 := bstep (se 1 (by rfl) ⟨1657019, by rfl⟩ : syracuseStep 2209359 = 3314039) B3314039
theorem B3314045 : Blo 2207435 3314045 := bbase (se 3 (by rfl) ⟨621383, by rfl⟩ : syracuseStep 3314045 = 1242767) (by norm_num)
theorem B2209363 : Blo 2207435 2209363 := bstep (se 1 (by rfl) ⟨1657022, by rfl⟩ : syracuseStep 2209363 = 3314045) B3314045
theorem B4971077 : Blo 2207435 4971077 := bbase (se 4 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 4971077 = 932077) (by norm_num)
theorem B3314051 : Blo 2207435 3314051 := bstep (se 1 (by rfl) ⟨2485538, by rfl⟩ : syracuseStep 3314051 = 4971077) B4971077
theorem B2209367 : Blo 2207435 2209367 := bstep (se 1 (by rfl) ⟨1657025, by rfl⟩ : syracuseStep 2209367 = 3314051) B3314051
theorem B2359325 : Blo 2207435 2359325 := bbase (se 3 (by rfl) ⟨442373, by rfl⟩ : syracuseStep 2359325 = 884747) (by norm_num)
theorem B6291533 : Blo 2207435 6291533 := bstep (se 3 (by rfl) ⟨1179662, by rfl⟩ : syracuseStep 6291533 = 2359325) B2359325
theorem B4194355 : Blo 2207435 4194355 := bstep (se 1 (by rfl) ⟨3145766, by rfl⟩ : syracuseStep 4194355 = 6291533) B6291533
theorem B5592473 : Blo 2207435 5592473 := bstep (se 2 (by rfl) ⟨2097177, by rfl⟩ : syracuseStep 5592473 = 4194355) B4194355
theorem B3728315 : Blo 2207435 3728315 := bstep (se 1 (by rfl) ⟨2796236, by rfl⟩ : syracuseStep 3728315 = 5592473) B5592473
theorem B2485543 : Blo 2207435 2485543 := bstep (se 1 (by rfl) ⟨1864157, by rfl⟩ : syracuseStep 2485543 = 3728315) B3728315
theorem B3314057 : Blo 2207435 3314057 := bstep (se 2 (by rfl) ⟨1242771, by rfl⟩ : syracuseStep 3314057 = 2485543) B2485543
theorem B2209371 : Blo 2207435 2209371 := bstep (se 1 (by rfl) ⟨1657028, by rfl⟩ : syracuseStep 2209371 = 3314057) B3314057
theorem B11184965 : Blo 2207435 11184965 := bbase (se 4 (by rfl) ⟨1048590, by rfl⟩ : syracuseStep 11184965 = 2097181) (by norm_num)
theorem B7456643 : Blo 2207435 7456643 := bstep (se 1 (by rfl) ⟨5592482, by rfl⟩ : syracuseStep 7456643 = 11184965) B11184965
theorem B4971095 : Blo 2207435 4971095 := bstep (se 1 (by rfl) ⟨3728321, by rfl⟩ : syracuseStep 4971095 = 7456643) B7456643
theorem B3314063 : Blo 2207435 3314063 := bstep (se 1 (by rfl) ⟨2485547, by rfl⟩ : syracuseStep 3314063 = 4971095) B4971095
theorem B2209375 : Blo 2207435 2209375 := bstep (se 1 (by rfl) ⟨1657031, by rfl⟩ : syracuseStep 2209375 = 3314063) B3314063
theorem B3314069 : Blo 2207435 3314069 := bbase (se 6 (by rfl) ⟨77673, by rfl⟩ : syracuseStep 3314069 = 155347) (by norm_num)
theorem B2209379 : Blo 2207435 2209379 := bstep (se 1 (by rfl) ⟨1657034, by rfl⟩ : syracuseStep 2209379 = 3314069) B3314069
theorem B6053557 : Blo 2207435 6053557 := bbase (se 5 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 6053557 = 567521) (by norm_num)
theorem B8071409 : Blo 2207435 8071409 := bstep (se 2 (by rfl) ⟨3026778, by rfl⟩ : syracuseStep 8071409 = 6053557) B6053557
theorem B5380939 : Blo 2207435 5380939 := bstep (se 1 (by rfl) ⟨4035704, by rfl⟩ : syracuseStep 5380939 = 8071409) B8071409
theorem B7174585 : Blo 2207435 7174585 := bstep (se 2 (by rfl) ⟨2690469, by rfl⟩ : syracuseStep 7174585 = 5380939) B5380939
theorem B9566113 : Blo 2207435 9566113 := bstep (se 2 (by rfl) ⟨3587292, by rfl⟩ : syracuseStep 9566113 = 7174585) B7174585
theorem B12754817 : Blo 2207435 12754817 := bstep (se 2 (by rfl) ⟨4783056, by rfl⟩ : syracuseStep 12754817 = 9566113) B9566113
theorem B8503211 : Blo 2207435 8503211 := bstep (se 1 (by rfl) ⟨6377408, by rfl⟩ : syracuseStep 8503211 = 12754817) B12754817
theorem B5668807 : Blo 2207435 5668807 := bstep (se 1 (by rfl) ⟨4251605, by rfl⟩ : syracuseStep 5668807 = 8503211) B8503211
theorem B7558409 : Blo 2207435 7558409 := bstep (se 2 (by rfl) ⟨2834403, by rfl⟩ : syracuseStep 7558409 = 5668807) B5668807
theorem B5038939 : Blo 2207435 5038939 := bstep (se 1 (by rfl) ⟨3779204, by rfl⟩ : syracuseStep 5038939 = 7558409) B7558409
theorem B6718585 : Blo 2207435 6718585 := bstep (se 2 (by rfl) ⟨2519469, by rfl⟩ : syracuseStep 6718585 = 5038939) B5038939
theorem B8958113 : Blo 2207435 8958113 := bstep (se 2 (by rfl) ⟨3359292, by rfl⟩ : syracuseStep 8958113 = 6718585) B6718585
theorem B5972075 : Blo 2207435 5972075 := bstep (se 1 (by rfl) ⟨4479056, by rfl⟩ : syracuseStep 5972075 = 8958113) B8958113
theorem B3981383 : Blo 2207435 3981383 := bstep (se 1 (by rfl) ⟨2986037, by rfl⟩ : syracuseStep 3981383 = 5972075) B5972075
theorem B2654255 : Blo 2207435 2654255 := bstep (se 1 (by rfl) ⟨1990691, by rfl⟩ : syracuseStep 2654255 = 3981383) B3981383
theorem B7078013 : Blo 2207435 7078013 := bstep (se 3 (by rfl) ⟨1327127, by rfl⟩ : syracuseStep 7078013 = 2654255) B2654255
theorem B4718675 : Blo 2207435 4718675 := bstep (se 1 (by rfl) ⟨3539006, by rfl⟩ : syracuseStep 4718675 = 7078013) B7078013
theorem B12583133 : Blo 2207435 12583133 := bstep (se 3 (by rfl) ⟨2359337, by rfl⟩ : syracuseStep 12583133 = 4718675) B4718675
theorem B8388755 : Blo 2207435 8388755 := bstep (se 1 (by rfl) ⟨6291566, by rfl⟩ : syracuseStep 8388755 = 12583133) B12583133
theorem B5592503 : Blo 2207435 5592503 := bstep (se 1 (by rfl) ⟨4194377, by rfl⟩ : syracuseStep 5592503 = 8388755) B8388755
theorem B3728335 : Blo 2207435 3728335 := bstep (se 1 (by rfl) ⟨2796251, by rfl⟩ : syracuseStep 3728335 = 5592503) B5592503
theorem B4971113 : Blo 2207435 4971113 := bstep (se 2 (by rfl) ⟨1864167, by rfl⟩ : syracuseStep 4971113 = 3728335) B3728335
theorem B3314075 : Blo 2207435 3314075 := bstep (se 1 (by rfl) ⟨2485556, by rfl⟩ : syracuseStep 3314075 = 4971113) B4971113
theorem B2209383 : Blo 2207435 2209383 := bstep (se 1 (by rfl) ⟨1657037, by rfl⟩ : syracuseStep 2209383 = 3314075) B3314075
theorem B2485561 : Blo 2207435 2485561 := bbase (se 2 (by rfl) ⟨932085, by rfl⟩ : syracuseStep 2485561 = 1864171) (by norm_num)
theorem B3314081 : Blo 2207435 3314081 := bstep (se 2 (by rfl) ⟨1242780, by rfl⟩ : syracuseStep 3314081 = 2485561) B2485561
theorem B2209387 : Blo 2207435 2209387 := bstep (se 1 (by rfl) ⟨1657040, by rfl⟩ : syracuseStep 2209387 = 3314081) B3314081
theorem B6291589 : Blo 2207435 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B8388785 : Blo 2207435 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B5592523 : Blo 2207435 5592523 := bstep (se 1 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 5592523 = 8388785) B8388785
theorem B7456697 : Blo 2207435 7456697 := bstep (se 2 (by rfl) ⟨2796261, by rfl⟩ : syracuseStep 7456697 = 5592523) B5592523
theorem B4971131 : Blo 2207435 4971131 := bstep (se 1 (by rfl) ⟨3728348, by rfl⟩ : syracuseStep 4971131 = 7456697) B7456697
theorem B3314087 : Blo 2207435 3314087 := bstep (se 1 (by rfl) ⟨2485565, by rfl⟩ : syracuseStep 3314087 = 4971131) B4971131
theorem B2209391 : Blo 2207435 2209391 := bstep (se 1 (by rfl) ⟨1657043, by rfl⟩ : syracuseStep 2209391 = 3314087) B3314087
theorem B3314093 : Blo 2207435 3314093 := bbase (se 3 (by rfl) ⟨621392, by rfl⟩ : syracuseStep 3314093 = 1242785) (by norm_num)
theorem B2209395 : Blo 2207435 2209395 := bstep (se 1 (by rfl) ⟨1657046, by rfl⟩ : syracuseStep 2209395 = 3314093) B3314093
theorem B4971149 : Blo 2207435 4971149 := bbase (se 3 (by rfl) ⟨932090, by rfl⟩ : syracuseStep 4971149 = 1864181) (by norm_num)
theorem B3314099 : Blo 2207435 3314099 := bstep (se 1 (by rfl) ⟨2485574, by rfl⟩ : syracuseStep 3314099 = 4971149) B4971149
theorem B2209399 : Blo 2207435 2209399 := bstep (se 1 (by rfl) ⟨1657049, by rfl⟩ : syracuseStep 2209399 = 3314099) B3314099
theorem B2796277 : Blo 2207435 2796277 := bbase (se 5 (by rfl) ⟨131075, by rfl⟩ : syracuseStep 2796277 = 262151) (by norm_num)
theorem B3728369 : Blo 2207435 3728369 := bstep (se 2 (by rfl) ⟨1398138, by rfl⟩ : syracuseStep 3728369 = 2796277) B2796277
theorem B2485579 : Blo 2207435 2485579 := bstep (se 1 (by rfl) ⟨1864184, by rfl⟩ : syracuseStep 2485579 = 3728369) B3728369
theorem B3314105 : Blo 2207435 3314105 := bstep (se 2 (by rfl) ⟨1242789, by rfl⟩ : syracuseStep 3314105 = 2485579) B2485579
theorem B2209403 : Blo 2207435 2209403 := bstep (se 1 (by rfl) ⟨1657052, by rfl⟩ : syracuseStep 2209403 = 3314105) B3314105
theorem B2986069 : Blo 2207435 2986069 := bbase (se 8 (by rfl) ⟨17496, by rfl⟩ : syracuseStep 2986069 = 34993) (by norm_num)
theorem B3981425 : Blo 2207435 3981425 := bstep (se 2 (by rfl) ⟨1493034, by rfl⟩ : syracuseStep 3981425 = 2986069) B2986069
theorem B42468533 : Blo 2207435 42468533 := bstep (se 5 (by rfl) ⟨1990712, by rfl⟩ : syracuseStep 42468533 = 3981425) B3981425
theorem B28312355 : Blo 2207435 28312355 := bstep (se 1 (by rfl) ⟨21234266, by rfl⟩ : syracuseStep 28312355 = 42468533) B42468533
theorem B18874903 : Blo 2207435 18874903 := bstep (se 1 (by rfl) ⟨14156177, by rfl⟩ : syracuseStep 18874903 = 28312355) B28312355
theorem B25166537 : Blo 2207435 25166537 := bstep (se 2 (by rfl) ⟨9437451, by rfl⟩ : syracuseStep 25166537 = 18874903) B18874903
theorem B16777691 : Blo 2207435 16777691 := bstep (se 1 (by rfl) ⟨12583268, by rfl⟩ : syracuseStep 16777691 = 25166537) B25166537
theorem B11185127 : Blo 2207435 11185127 := bstep (se 1 (by rfl) ⟨8388845, by rfl⟩ : syracuseStep 11185127 = 16777691) B16777691
theorem B7456751 : Blo 2207435 7456751 := bstep (se 1 (by rfl) ⟨5592563, by rfl⟩ : syracuseStep 7456751 = 11185127) B11185127
theorem B4971167 : Blo 2207435 4971167 := bstep (se 1 (by rfl) ⟨3728375, by rfl⟩ : syracuseStep 4971167 = 7456751) B7456751
theorem B3314111 : Blo 2207435 3314111 := bstep (se 1 (by rfl) ⟨2485583, by rfl⟩ : syracuseStep 3314111 = 4971167) B4971167
theorem B2209407 : Blo 2207435 2209407 := bstep (se 1 (by rfl) ⟨1657055, by rfl⟩ : syracuseStep 2209407 = 3314111) B3314111
theorem B3314117 : Blo 2207435 3314117 := bbase (se 4 (by rfl) ⟨310698, by rfl⟩ : syracuseStep 3314117 = 621397) (by norm_num)
theorem B2209411 : Blo 2207435 2209411 := bstep (se 1 (by rfl) ⟨1657058, by rfl⟩ : syracuseStep 2209411 = 3314117) B3314117
theorem B3728389 : Blo 2207435 3728389 := bbase (se 4 (by rfl) ⟨349536, by rfl⟩ : syracuseStep 3728389 = 699073) (by norm_num)
theorem B4971185 : Blo 2207435 4971185 := bstep (se 2 (by rfl) ⟨1864194, by rfl⟩ : syracuseStep 4971185 = 3728389) B3728389
theorem B3314123 : Blo 2207435 3314123 := bstep (se 1 (by rfl) ⟨2485592, by rfl⟩ : syracuseStep 3314123 = 4971185) B4971185
theorem B2209415 : Blo 2207435 2209415 := bstep (se 1 (by rfl) ⟨1657061, by rfl⟩ : syracuseStep 2209415 = 3314123) B3314123
theorem B2485597 : Blo 2207435 2485597 := bbase (se 3 (by rfl) ⟨466049, by rfl⟩ : syracuseStep 2485597 = 932099) (by norm_num)
theorem B3314129 : Blo 2207435 3314129 := bstep (se 2 (by rfl) ⟨1242798, by rfl⟩ : syracuseStep 3314129 = 2485597) B2485597
theorem B2209419 : Blo 2207435 2209419 := bstep (se 1 (by rfl) ⟨1657064, by rfl⟩ : syracuseStep 2209419 = 3314129) B3314129
theorem B7456805 : Blo 2207435 7456805 := bbase (se 4 (by rfl) ⟨699075, by rfl⟩ : syracuseStep 7456805 = 1398151) (by norm_num)
theorem B4971203 : Blo 2207435 4971203 := bstep (se 1 (by rfl) ⟨3728402, by rfl⟩ : syracuseStep 4971203 = 7456805) B7456805
theorem B3314135 : Blo 2207435 3314135 := bstep (se 1 (by rfl) ⟨2485601, by rfl⟩ : syracuseStep 3314135 = 4971203) B4971203
theorem B2209423 : Blo 2207435 2209423 := bstep (se 1 (by rfl) ⟨1657067, by rfl⟩ : syracuseStep 2209423 = 3314135) B3314135
theorem B3314141 : Blo 2207435 3314141 := bbase (se 3 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 3314141 = 1242803) (by norm_num)
theorem B2209427 : Blo 2207435 2209427 := bstep (se 1 (by rfl) ⟨1657070, by rfl⟩ : syracuseStep 2209427 = 3314141) B3314141
theorem B4971221 : Blo 2207435 4971221 := bbase (se 7 (by rfl) ⟨58256, by rfl⟩ : syracuseStep 4971221 = 116513) (by norm_num)
theorem B3314147 : Blo 2207435 3314147 := bstep (se 1 (by rfl) ⟨2485610, by rfl⟩ : syracuseStep 3314147 = 4971221) B4971221
theorem B2209431 : Blo 2207435 2209431 := bstep (se 1 (by rfl) ⟨1657073, by rfl⟩ : syracuseStep 2209431 = 3314147) B3314147
theorem B9437573 : Blo 2207435 9437573 := bbase (se 4 (by rfl) ⟨884772, by rfl⟩ : syracuseStep 9437573 = 1769545) (by norm_num)
theorem B6291715 : Blo 2207435 6291715 := bstep (se 1 (by rfl) ⟨4718786, by rfl⟩ : syracuseStep 6291715 = 9437573) B9437573
theorem B8388953 : Blo 2207435 8388953 := bstep (se 2 (by rfl) ⟨3145857, by rfl⟩ : syracuseStep 8388953 = 6291715) B6291715
theorem B5592635 : Blo 2207435 5592635 := bstep (se 1 (by rfl) ⟨4194476, by rfl⟩ : syracuseStep 5592635 = 8388953) B8388953
theorem B3728423 : Blo 2207435 3728423 := bstep (se 1 (by rfl) ⟨2796317, by rfl⟩ : syracuseStep 3728423 = 5592635) B5592635
theorem B2485615 : Blo 2207435 2485615 := bstep (se 1 (by rfl) ⟨1864211, by rfl⟩ : syracuseStep 2485615 = 3728423) B3728423
theorem B3314153 : Blo 2207435 3314153 := bstep (se 2 (by rfl) ⟨1242807, by rfl⟩ : syracuseStep 3314153 = 2485615) B2485615
theorem B2209435 : Blo 2207435 2209435 := bstep (se 1 (by rfl) ⟨1657076, by rfl⟩ : syracuseStep 2209435 = 3314153) B3314153
theorem C0 (j : ℕ) (h1 : 551858 ≤ j) (h2 : j ≤ 552358) : Blo 2207435 (4 * j + 3) := by
  interval_cases j
  · exact B2207435
  · exact B2207439
  · exact B2207443
  · exact B2207447
  · exact B2207451
  · exact B2207455
  · exact B2207459
  · exact B2207463
  · exact B2207467
  · exact B2207471
  · exact B2207475
  · exact B2207479
  · exact B2207483
  · exact B2207487
  · exact B2207491
  · exact B2207495
  · exact B2207499
  · exact B2207503
  · exact B2207507
  · exact B2207511
  · exact B2207515
  · exact B2207519
  · exact B2207523
  · exact B2207527
  · exact B2207531
  · exact B2207535
  · exact B2207539
  · exact B2207543
  · exact B2207547
  · exact B2207551
  · exact B2207555
  · exact B2207559
  · exact B2207563
  · exact B2207567
  · exact B2207571
  · exact B2207575
  · exact B2207579
  · exact B2207583
  · exact B2207587
  · exact B2207591
  · exact B2207595
  · exact B2207599
  · exact B2207603
  · exact B2207607
  · exact B2207611
  · exact B2207615
  · exact B2207619
  · exact B2207623
  · exact B2207627
  · exact B2207631
  · exact B2207635
  · exact B2207639
  · exact B2207643
  · exact B2207647
  · exact B2207651
  · exact B2207655
  · exact B2207659
  · exact B2207663
  · exact B2207667
  · exact B2207671
  · exact B2207675
  · exact B2207679
  · exact B2207683
  · exact B2207687
  · exact B2207691
  · exact B2207695
  · exact B2207699
  · exact B2207703
  · exact B2207707
  · exact B2207711
  · exact B2207715
  · exact B2207719
  · exact B2207723
  · exact B2207727
  · exact B2207731
  · exact B2207735
  · exact B2207739
  · exact B2207743
  · exact B2207747
  · exact B2207751
  · exact B2207755
  · exact B2207759
  · exact B2207763
  · exact B2207767
  · exact B2207771
  · exact B2207775
  · exact B2207779
  · exact B2207783
  · exact B2207787
  · exact B2207791
  · exact B2207795
  · exact B2207799
  · exact B2207803
  · exact B2207807
  · exact B2207811
  · exact B2207815
  · exact B2207819
  · exact B2207823
  · exact B2207827
  · exact B2207831
  · exact B2207835
  · exact B2207839
  · exact B2207843
  · exact B2207847
  · exact B2207851
  · exact B2207855
  · exact B2207859
  · exact B2207863
  · exact B2207867
  · exact B2207871
  · exact B2207875
  · exact B2207879
  · exact B2207883
  · exact B2207887
  · exact B2207891
  · exact B2207895
  · exact B2207899
  · exact B2207903
  · exact B2207907
  · exact B2207911
  · exact B2207915
  · exact B2207919
  · exact B2207923
  · exact B2207927
  · exact B2207931
  · exact B2207935
  · exact B2207939
  · exact B2207943
  · exact B2207947
  · exact B2207951
  · exact B2207955
  · exact B2207959
  · exact B2207963
  · exact B2207967
  · exact B2207971
  · exact B2207975
  · exact B2207979
  · exact B2207983
  · exact B2207987
  · exact B2207991
  · exact B2207995
  · exact B2207999
  · exact B2208003
  · exact B2208007
  · exact B2208011
  · exact B2208015
  · exact B2208019
  · exact B2208023
  · exact B2208027
  · exact B2208031
  · exact B2208035
  · exact B2208039
  · exact B2208043
  · exact B2208047
  · exact B2208051
  · exact B2208055
  · exact B2208059
  · exact B2208063
  · exact B2208067
  · exact B2208071
  · exact B2208075
  · exact B2208079
  · exact B2208083
  · exact B2208087
  · exact B2208091
  · exact B2208095
  · exact B2208099
  · exact B2208103
  · exact B2208107
  · exact B2208111
  · exact B2208115
  · exact B2208119
  · exact B2208123
  · exact B2208127
  · exact B2208131
  · exact B2208135
  · exact B2208139
  · exact B2208143
  · exact B2208147
  · exact B2208151
  · exact B2208155
  · exact B2208159
  · exact B2208163
  · exact B2208167
  · exact B2208171
  · exact B2208175
  · exact B2208179
  · exact B2208183
  · exact B2208187
  · exact B2208191
  · exact B2208195
  · exact B2208199
  · exact B2208203
  · exact B2208207
  · exact B2208211
  · exact B2208215
  · exact B2208219
  · exact B2208223
  · exact B2208227
  · exact B2208231
  · exact B2208235
  · exact B2208239
  · exact B2208243
  · exact B2208247
  · exact B2208251
  · exact B2208255
  · exact B2208259
  · exact B2208263
  · exact B2208267
  · exact B2208271
  · exact B2208275
  · exact B2208279
  · exact B2208283
  · exact B2208287
  · exact B2208291
  · exact B2208295
  · exact B2208299
  · exact B2208303
  · exact B2208307
  · exact B2208311
  · exact B2208315
  · exact B2208319
  · exact B2208323
  · exact B2208327
  · exact B2208331
  · exact B2208335
  · exact B2208339
  · exact B2208343
  · exact B2208347
  · exact B2208351
  · exact B2208355
  · exact B2208359
  · exact B2208363
  · exact B2208367
  · exact B2208371
  · exact B2208375
  · exact B2208379
  · exact B2208383
  · exact B2208387
  · exact B2208391
  · exact B2208395
  · exact B2208399
  · exact B2208403
  · exact B2208407
  · exact B2208411
  · exact B2208415
  · exact B2208419
  · exact B2208423
  · exact B2208427
  · exact B2208431
  · exact B2208435
  · exact B2208439
  · exact B2208443
  · exact B2208447
  · exact B2208451
  · exact B2208455
  · exact B2208459
  · exact B2208463
  · exact B2208467
  · exact B2208471
  · exact B2208475
  · exact B2208479
  · exact B2208483
  · exact B2208487
  · exact B2208491
  · exact B2208495
  · exact B2208499
  · exact B2208503
  · exact B2208507
  · exact B2208511
  · exact B2208515
  · exact B2208519
  · exact B2208523
  · exact B2208527
  · exact B2208531
  · exact B2208535
  · exact B2208539
  · exact B2208543
  · exact B2208547
  · exact B2208551
  · exact B2208555
  · exact B2208559
  · exact B2208563
  · exact B2208567
  · exact B2208571
  · exact B2208575
  · exact B2208579
  · exact B2208583
  · exact B2208587
  · exact B2208591
  · exact B2208595
  · exact B2208599
  · exact B2208603
  · exact B2208607
  · exact B2208611
  · exact B2208615
  · exact B2208619
  · exact B2208623
  · exact B2208627
  · exact B2208631
  · exact B2208635
  · exact B2208639
  · exact B2208643
  · exact B2208647
  · exact B2208651
  · exact B2208655
  · exact B2208659
  · exact B2208663
  · exact B2208667
  · exact B2208671
  · exact B2208675
  · exact B2208679
  · exact B2208683
  · exact B2208687
  · exact B2208691
  · exact B2208695
  · exact B2208699
  · exact B2208703
  · exact B2208707
  · exact B2208711
  · exact B2208715
  · exact B2208719
  · exact B2208723
  · exact B2208727
  · exact B2208731
  · exact B2208735
  · exact B2208739
  · exact B2208743
  · exact B2208747
  · exact B2208751
  · exact B2208755
  · exact B2208759
  · exact B2208763
  · exact B2208767
  · exact B2208771
  · exact B2208775
  · exact B2208779
  · exact B2208783
  · exact B2208787
  · exact B2208791
  · exact B2208795
  · exact B2208799
  · exact B2208803
  · exact B2208807
  · exact B2208811
  · exact B2208815
  · exact B2208819
  · exact B2208823
  · exact B2208827
  · exact B2208831
  · exact B2208835
  · exact B2208839
  · exact B2208843
  · exact B2208847
  · exact B2208851
  · exact B2208855
  · exact B2208859
  · exact B2208863
  · exact B2208867
  · exact B2208871
  · exact B2208875
  · exact B2208879
  · exact B2208883
  · exact B2208887
  · exact B2208891
  · exact B2208895
  · exact B2208899
  · exact B2208903
  · exact B2208907
  · exact B2208911
  · exact B2208915
  · exact B2208919
  · exact B2208923
  · exact B2208927
  · exact B2208931
  · exact B2208935
  · exact B2208939
  · exact B2208943
  · exact B2208947
  · exact B2208951
  · exact B2208955
  · exact B2208959
  · exact B2208963
  · exact B2208967
  · exact B2208971
  · exact B2208975
  · exact B2208979
  · exact B2208983
  · exact B2208987
  · exact B2208991
  · exact B2208995
  · exact B2208999
  · exact B2209003
  · exact B2209007
  · exact B2209011
  · exact B2209015
  · exact B2209019
  · exact B2209023
  · exact B2209027
  · exact B2209031
  · exact B2209035
  · exact B2209039
  · exact B2209043
  · exact B2209047
  · exact B2209051
  · exact B2209055
  · exact B2209059
  · exact B2209063
  · exact B2209067
  · exact B2209071
  · exact B2209075
  · exact B2209079
  · exact B2209083
  · exact B2209087
  · exact B2209091
  · exact B2209095
  · exact B2209099
  · exact B2209103
  · exact B2209107
  · exact B2209111
  · exact B2209115
  · exact B2209119
  · exact B2209123
  · exact B2209127
  · exact B2209131
  · exact B2209135
  · exact B2209139
  · exact B2209143
  · exact B2209147
  · exact B2209151
  · exact B2209155
  · exact B2209159
  · exact B2209163
  · exact B2209167
  · exact B2209171
  · exact B2209175
  · exact B2209179
  · exact B2209183
  · exact B2209187
  · exact B2209191
  · exact B2209195
  · exact B2209199
  · exact B2209203
  · exact B2209207
  · exact B2209211
  · exact B2209215
  · exact B2209219
  · exact B2209223
  · exact B2209227
  · exact B2209231
  · exact B2209235
  · exact B2209239
  · exact B2209243
  · exact B2209247
  · exact B2209251
  · exact B2209255
  · exact B2209259
  · exact B2209263
  · exact B2209267
  · exact B2209271
  · exact B2209275
  · exact B2209279
  · exact B2209283
  · exact B2209287
  · exact B2209291
  · exact B2209295
  · exact B2209299
  · exact B2209303
  · exact B2209307
  · exact B2209311
  · exact B2209315
  · exact B2209319
  · exact B2209323
  · exact B2209327
  · exact B2209331
  · exact B2209335
  · exact B2209339
  · exact B2209343
  · exact B2209347
  · exact B2209351
  · exact B2209355
  · exact B2209359
  · exact B2209363
  · exact B2209367
  · exact B2209371
  · exact B2209375
  · exact B2209379
  · exact B2209383
  · exact B2209387
  · exact B2209391
  · exact B2209395
  · exact B2209399
  · exact B2209403
  · exact B2209407
  · exact B2209411
  · exact B2209415
  · exact B2209419
  · exact B2209423
  · exact B2209427
  · exact B2209431
  · exact B2209435
theorem solution (m : ℕ) (hlo : 2207435 ≤ m) (hhi : m ≤ 2209435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 551858 ≤ j := by omega
    have hj2 : j ≤ 552358 := by omega
    have hb : Blo 2207435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
