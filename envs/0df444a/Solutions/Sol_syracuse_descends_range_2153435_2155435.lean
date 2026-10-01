-- Prove2me | solution 1 for syracuse_descends_range_2153435_2155435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:30.270706+00:00
-- url     : https://prove2.me/submissions/9d3a772a-fec2-4c5a-a2e6-f2e21b67159c

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

theorem B5450885 : Blo 2153435 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B3633923 : Blo 2153435 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B2422615 : Blo 2153435 2422615 := bstep (se 1 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 2422615 = 3633923) B3633923
theorem B3230153 : Blo 2153435 3230153 := bstep (se 2 (by rfl) ⟨1211307, by rfl⟩ : syracuseStep 3230153 = 2422615) B2422615
theorem B2153435 : Blo 2153435 2153435 := bstep (se 1 (by rfl) ⟨1615076, by rfl⟩ : syracuseStep 2153435 = 3230153) B3230153
theorem B5174093 : Blo 2153435 5174093 := bbase (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) (by norm_num)
theorem B3449395 : Blo 2153435 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B4599193 : Blo 2153435 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B6132257 : Blo 2153435 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B4088171 : Blo 2153435 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B10901789 : Blo 2153435 10901789 := bstep (se 3 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 10901789 = 4088171) B4088171
theorem B7267859 : Blo 2153435 7267859 := bstep (se 1 (by rfl) ⟨5450894, by rfl⟩ : syracuseStep 7267859 = 10901789) B10901789
theorem B4845239 : Blo 2153435 4845239 := bstep (se 1 (by rfl) ⟨3633929, by rfl⟩ : syracuseStep 4845239 = 7267859) B7267859
theorem B3230159 : Blo 2153435 3230159 := bstep (se 1 (by rfl) ⟨2422619, by rfl⟩ : syracuseStep 3230159 = 4845239) B4845239
theorem B2153439 : Blo 2153435 2153439 := bstep (se 1 (by rfl) ⟨1615079, by rfl⟩ : syracuseStep 2153439 = 3230159) B3230159
theorem B3230165 : Blo 2153435 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B2153443 : Blo 2153435 2153443 := bstep (se 1 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 2153443 = 3230165) B3230165
theorem B8176373 : Blo 2153435 8176373 := bbase (se 5 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 8176373 = 766535) (by norm_num)
theorem B5450915 : Blo 2153435 5450915 := bstep (se 1 (by rfl) ⟨4088186, by rfl⟩ : syracuseStep 5450915 = 8176373) B8176373
theorem B3633943 : Blo 2153435 3633943 := bstep (se 1 (by rfl) ⟨2725457, by rfl⟩ : syracuseStep 3633943 = 5450915) B5450915
theorem B4845257 : Blo 2153435 4845257 := bstep (se 2 (by rfl) ⟨1816971, by rfl⟩ : syracuseStep 4845257 = 3633943) B3633943
theorem B3230171 : Blo 2153435 3230171 := bstep (se 1 (by rfl) ⟨2422628, by rfl⟩ : syracuseStep 3230171 = 4845257) B4845257
theorem B2153447 : Blo 2153435 2153447 := bstep (se 1 (by rfl) ⟨1615085, by rfl⟩ : syracuseStep 2153447 = 3230171) B3230171
theorem B2422633 : Blo 2153435 2422633 := bbase (se 2 (by rfl) ⟨908487, by rfl⟩ : syracuseStep 2422633 = 1816975) (by norm_num)
theorem B3230177 : Blo 2153435 3230177 := bstep (se 2 (by rfl) ⟨1211316, by rfl⟩ : syracuseStep 3230177 = 2422633) B2422633
theorem B2153451 : Blo 2153435 2153451 := bstep (se 1 (by rfl) ⟨1615088, by rfl⟩ : syracuseStep 2153451 = 3230177) B3230177
theorem B2182837 : Blo 2153435 2182837 := bbase (se 5 (by rfl) ⟨102320, by rfl⟩ : syracuseStep 2182837 = 204641) (by norm_num)
theorem B2910449 : Blo 2153435 2910449 := bstep (se 2 (by rfl) ⟨1091418, by rfl⟩ : syracuseStep 2910449 = 2182837) B2182837
theorem B7761197 : Blo 2153435 7761197 := bstep (se 3 (by rfl) ⟨1455224, by rfl⟩ : syracuseStep 7761197 = 2910449) B2910449
theorem B5174131 : Blo 2153435 5174131 := bstep (se 1 (by rfl) ⟨3880598, by rfl⟩ : syracuseStep 5174131 = 7761197) B7761197
theorem B6898841 : Blo 2153435 6898841 := bstep (se 2 (by rfl) ⟨2587065, by rfl⟩ : syracuseStep 6898841 = 5174131) B5174131
theorem B4599227 : Blo 2153435 4599227 := bstep (se 1 (by rfl) ⟨3449420, by rfl⟩ : syracuseStep 4599227 = 6898841) B6898841
theorem B12264605 : Blo 2153435 12264605 := bstep (se 3 (by rfl) ⟨2299613, by rfl⟩ : syracuseStep 12264605 = 4599227) B4599227
theorem B8176403 : Blo 2153435 8176403 := bstep (se 1 (by rfl) ⟨6132302, by rfl⟩ : syracuseStep 8176403 = 12264605) B12264605
theorem B5450935 : Blo 2153435 5450935 := bstep (se 1 (by rfl) ⟨4088201, by rfl⟩ : syracuseStep 5450935 = 8176403) B8176403
theorem B7267913 : Blo 2153435 7267913 := bstep (se 2 (by rfl) ⟨2725467, by rfl⟩ : syracuseStep 7267913 = 5450935) B5450935
theorem B4845275 : Blo 2153435 4845275 := bstep (se 1 (by rfl) ⟨3633956, by rfl⟩ : syracuseStep 4845275 = 7267913) B7267913
theorem B3230183 : Blo 2153435 3230183 := bstep (se 1 (by rfl) ⟨2422637, by rfl⟩ : syracuseStep 3230183 = 4845275) B4845275
theorem B2153455 : Blo 2153435 2153455 := bstep (se 1 (by rfl) ⟨1615091, by rfl⟩ : syracuseStep 2153455 = 3230183) B3230183
theorem B3230189 : Blo 2153435 3230189 := bbase (se 3 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 3230189 = 1211321) (by norm_num)
theorem B2153459 : Blo 2153435 2153459 := bstep (se 1 (by rfl) ⟨1615094, by rfl⟩ : syracuseStep 2153459 = 3230189) B3230189
theorem B4845293 : Blo 2153435 4845293 := bbase (se 3 (by rfl) ⟨908492, by rfl⟩ : syracuseStep 4845293 = 1816985) (by norm_num)
theorem B3230195 : Blo 2153435 3230195 := bstep (se 1 (by rfl) ⟨2422646, by rfl⟩ : syracuseStep 3230195 = 4845293) B4845293
theorem B2153463 : Blo 2153435 2153463 := bstep (se 1 (by rfl) ⟨1615097, by rfl⟩ : syracuseStep 2153463 = 3230195) B3230195
theorem B2587081 : Blo 2153435 2587081 := bbase (se 2 (by rfl) ⟨970155, by rfl⟩ : syracuseStep 2587081 = 1940311) (by norm_num)
theorem B3449441 : Blo 2153435 3449441 := bstep (se 2 (by rfl) ⟨1293540, by rfl⟩ : syracuseStep 3449441 = 2587081) B2587081
theorem B2299627 : Blo 2153435 2299627 := bstep (se 1 (by rfl) ⟨1724720, by rfl⟩ : syracuseStep 2299627 = 3449441) B3449441
theorem B3066169 : Blo 2153435 3066169 := bstep (se 2 (by rfl) ⟨1149813, by rfl⟩ : syracuseStep 3066169 = 2299627) B2299627
theorem B4088225 : Blo 2153435 4088225 := bstep (se 2 (by rfl) ⟨1533084, by rfl⟩ : syracuseStep 4088225 = 3066169) B3066169
theorem B2725483 : Blo 2153435 2725483 := bstep (se 1 (by rfl) ⟨2044112, by rfl⟩ : syracuseStep 2725483 = 4088225) B4088225
theorem B3633977 : Blo 2153435 3633977 := bstep (se 2 (by rfl) ⟨1362741, by rfl⟩ : syracuseStep 3633977 = 2725483) B2725483
theorem B2422651 : Blo 2153435 2422651 := bstep (se 1 (by rfl) ⟨1816988, by rfl⟩ : syracuseStep 2422651 = 3633977) B3633977
theorem B3230201 : Blo 2153435 3230201 := bstep (se 2 (by rfl) ⟨1211325, by rfl⟩ : syracuseStep 3230201 = 2422651) B2422651
theorem B2153467 : Blo 2153435 2153467 := bstep (se 1 (by rfl) ⟨1615100, by rfl⟩ : syracuseStep 2153467 = 3230201) B3230201
theorem B3031229 : Blo 2153435 3031229 := bbase (se 3 (by rfl) ⟨568355, by rfl⟩ : syracuseStep 3031229 = 1136711) (by norm_num)
theorem B8083277 : Blo 2153435 8083277 := bstep (se 3 (by rfl) ⟨1515614, by rfl⟩ : syracuseStep 8083277 = 3031229) B3031229
theorem B5388851 : Blo 2153435 5388851 := bstep (se 1 (by rfl) ⟨4041638, by rfl⟩ : syracuseStep 5388851 = 8083277) B8083277
theorem B3592567 : Blo 2153435 3592567 := bstep (se 1 (by rfl) ⟨2694425, by rfl⟩ : syracuseStep 3592567 = 5388851) B5388851
theorem B4790089 : Blo 2153435 4790089 := bstep (se 2 (by rfl) ⟨1796283, by rfl⟩ : syracuseStep 4790089 = 3592567) B3592567
theorem B25547141 : Blo 2153435 25547141 := bstep (se 4 (by rfl) ⟨2395044, by rfl⟩ : syracuseStep 25547141 = 4790089) B4790089
theorem B17031427 : Blo 2153435 17031427 := bstep (se 1 (by rfl) ⟨12773570, by rfl⟩ : syracuseStep 17031427 = 25547141) B25547141
theorem B363337109 : Blo 2153435 363337109 := bstep (se 6 (by rfl) ⟨8515713, by rfl⟩ : syracuseStep 363337109 = 17031427) B17031427
theorem B242224739 : Blo 2153435 242224739 := bstep (se 1 (by rfl) ⟨181668554, by rfl⟩ : syracuseStep 242224739 = 363337109) B363337109
theorem B161483159 : Blo 2153435 161483159 := bstep (se 1 (by rfl) ⟨121112369, by rfl⟩ : syracuseStep 161483159 = 242224739) B242224739
theorem B430621757 : Blo 2153435 430621757 := bstep (se 3 (by rfl) ⟨80741579, by rfl⟩ : syracuseStep 430621757 = 161483159) B161483159
theorem B287081171 : Blo 2153435 287081171 := bstep (se 1 (by rfl) ⟨215310878, by rfl⟩ : syracuseStep 287081171 = 430621757) B430621757
theorem B191387447 : Blo 2153435 191387447 := bstep (se 1 (by rfl) ⟨143540585, by rfl⟩ : syracuseStep 191387447 = 287081171) B287081171
theorem B127591631 : Blo 2153435 127591631 := bstep (se 1 (by rfl) ⟨95693723, by rfl⟩ : syracuseStep 127591631 = 191387447) B191387447
theorem B85061087 : Blo 2153435 85061087 := bstep (se 1 (by rfl) ⟨63795815, by rfl⟩ : syracuseStep 85061087 = 127591631) B127591631
theorem B56707391 : Blo 2153435 56707391 := bstep (se 1 (by rfl) ⟨42530543, by rfl⟩ : syracuseStep 56707391 = 85061087) B85061087
theorem B37804927 : Blo 2153435 37804927 := bstep (se 1 (by rfl) ⟨28353695, by rfl⟩ : syracuseStep 37804927 = 56707391) B56707391
theorem B50406569 : Blo 2153435 50406569 := bstep (se 2 (by rfl) ⟨18902463, by rfl⟩ : syracuseStep 50406569 = 37804927) B37804927
theorem B33604379 : Blo 2153435 33604379 := bstep (se 1 (by rfl) ⟨25203284, by rfl⟩ : syracuseStep 33604379 = 50406569) B50406569
theorem B22402919 : Blo 2153435 22402919 := bstep (se 1 (by rfl) ⟨16802189, by rfl⟩ : syracuseStep 22402919 = 33604379) B33604379
theorem B14935279 : Blo 2153435 14935279 := bstep (se 1 (by rfl) ⟨11201459, by rfl⟩ : syracuseStep 14935279 = 22402919) B22402919
theorem B19913705 : Blo 2153435 19913705 := bstep (se 2 (by rfl) ⟨7467639, by rfl⟩ : syracuseStep 19913705 = 14935279) B14935279
theorem B13275803 : Blo 2153435 13275803 := bstep (se 1 (by rfl) ⟨9956852, by rfl⟩ : syracuseStep 13275803 = 19913705) B19913705
theorem B8850535 : Blo 2153435 8850535 := bstep (se 1 (by rfl) ⟨6637901, by rfl⟩ : syracuseStep 8850535 = 13275803) B13275803
theorem B47202853 : Blo 2153435 47202853 := bstep (se 4 (by rfl) ⟨4425267, by rfl⟩ : syracuseStep 47202853 = 8850535) B8850535
theorem B62937137 : Blo 2153435 62937137 := bstep (se 2 (by rfl) ⟨23601426, by rfl⟩ : syracuseStep 62937137 = 47202853) B47202853
theorem B41958091 : Blo 2153435 41958091 := bstep (se 1 (by rfl) ⟨31468568, by rfl⟩ : syracuseStep 41958091 = 62937137) B62937137
theorem B55944121 : Blo 2153435 55944121 := bstep (se 2 (by rfl) ⟨20979045, by rfl⟩ : syracuseStep 55944121 = 41958091) B41958091
theorem B74592161 : Blo 2153435 74592161 := bstep (se 2 (by rfl) ⟨27972060, by rfl⟩ : syracuseStep 74592161 = 55944121) B55944121
theorem B49728107 : Blo 2153435 49728107 := bstep (se 1 (by rfl) ⟨37296080, by rfl⟩ : syracuseStep 49728107 = 74592161) B74592161
theorem B132608285 : Blo 2153435 132608285 := bstep (se 3 (by rfl) ⟨24864053, by rfl⟩ : syracuseStep 132608285 = 49728107) B49728107
theorem B88405523 : Blo 2153435 88405523 := bstep (se 1 (by rfl) ⟨66304142, by rfl⟩ : syracuseStep 88405523 = 132608285) B132608285
theorem B58937015 : Blo 2153435 58937015 := bstep (se 1 (by rfl) ⟨44202761, by rfl⟩ : syracuseStep 58937015 = 88405523) B88405523
theorem B157165373 : Blo 2153435 157165373 := bstep (se 3 (by rfl) ⟨29468507, by rfl⟩ : syracuseStep 157165373 = 58937015) B58937015
theorem B104776915 : Blo 2153435 104776915 := bstep (se 1 (by rfl) ⟨78582686, by rfl⟩ : syracuseStep 104776915 = 157165373) B157165373
theorem B139702553 : Blo 2153435 139702553 := bstep (se 2 (by rfl) ⟨52388457, by rfl⟩ : syracuseStep 139702553 = 104776915) B104776915
theorem B93135035 : Blo 2153435 93135035 := bstep (se 1 (by rfl) ⟨69851276, by rfl⟩ : syracuseStep 93135035 = 139702553) B139702553
theorem B62090023 : Blo 2153435 62090023 := bstep (se 1 (by rfl) ⟨46567517, by rfl⟩ : syracuseStep 62090023 = 93135035) B93135035
theorem B82786697 : Blo 2153435 82786697 := bstep (se 2 (by rfl) ⟨31045011, by rfl⟩ : syracuseStep 82786697 = 62090023) B62090023
theorem B55191131 : Blo 2153435 55191131 := bstep (se 1 (by rfl) ⟨41393348, by rfl⟩ : syracuseStep 55191131 = 82786697) B82786697
theorem B36794087 : Blo 2153435 36794087 := bstep (se 1 (by rfl) ⟨27595565, by rfl⟩ : syracuseStep 36794087 = 55191131) B55191131
theorem B24529391 : Blo 2153435 24529391 := bstep (se 1 (by rfl) ⟨18397043, by rfl⟩ : syracuseStep 24529391 = 36794087) B36794087
theorem B16352927 : Blo 2153435 16352927 := bstep (se 1 (by rfl) ⟨12264695, by rfl⟩ : syracuseStep 16352927 = 24529391) B24529391
theorem B10901951 : Blo 2153435 10901951 := bstep (se 1 (by rfl) ⟨8176463, by rfl⟩ : syracuseStep 10901951 = 16352927) B16352927
theorem B7267967 : Blo 2153435 7267967 := bstep (se 1 (by rfl) ⟨5450975, by rfl⟩ : syracuseStep 7267967 = 10901951) B10901951
theorem B4845311 : Blo 2153435 4845311 := bstep (se 1 (by rfl) ⟨3633983, by rfl⟩ : syracuseStep 4845311 = 7267967) B7267967
theorem B3230207 : Blo 2153435 3230207 := bstep (se 1 (by rfl) ⟨2422655, by rfl⟩ : syracuseStep 3230207 = 4845311) B4845311
theorem B2153471 : Blo 2153435 2153471 := bstep (se 1 (by rfl) ⟨1615103, by rfl⟩ : syracuseStep 2153471 = 3230207) B3230207
theorem B3230213 : Blo 2153435 3230213 := bbase (se 4 (by rfl) ⟨302832, by rfl⟩ : syracuseStep 3230213 = 605665) (by norm_num)
theorem B2153475 : Blo 2153435 2153475 := bstep (se 1 (by rfl) ⟨1615106, by rfl⟩ : syracuseStep 2153475 = 3230213) B3230213
theorem B3633997 : Blo 2153435 3633997 := bbase (se 3 (by rfl) ⟨681374, by rfl⟩ : syracuseStep 3633997 = 1362749) (by norm_num)
theorem B4845329 : Blo 2153435 4845329 := bstep (se 2 (by rfl) ⟨1816998, by rfl⟩ : syracuseStep 4845329 = 3633997) B3633997
theorem B3230219 : Blo 2153435 3230219 := bstep (se 1 (by rfl) ⟨2422664, by rfl⟩ : syracuseStep 3230219 = 4845329) B4845329
theorem B2153479 : Blo 2153435 2153479 := bstep (se 1 (by rfl) ⟨1615109, by rfl⟩ : syracuseStep 2153479 = 3230219) B3230219
theorem B2422669 : Blo 2153435 2422669 := bbase (se 3 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 2422669 = 908501) (by norm_num)
theorem B3230225 : Blo 2153435 3230225 := bstep (se 2 (by rfl) ⟨1211334, by rfl⟩ : syracuseStep 3230225 = 2422669) B2422669
theorem B2153483 : Blo 2153435 2153483 := bstep (se 1 (by rfl) ⟨1615112, by rfl⟩ : syracuseStep 2153483 = 3230225) B3230225
theorem B7268021 : Blo 2153435 7268021 := bbase (se 5 (by rfl) ⟨340688, by rfl⟩ : syracuseStep 7268021 = 681377) (by norm_num)
theorem B4845347 : Blo 2153435 4845347 := bstep (se 1 (by rfl) ⟨3634010, by rfl⟩ : syracuseStep 4845347 = 7268021) B7268021
theorem B3230231 : Blo 2153435 3230231 := bstep (se 1 (by rfl) ⟨2422673, by rfl⟩ : syracuseStep 3230231 = 4845347) B4845347
theorem B2153487 : Blo 2153435 2153487 := bstep (se 1 (by rfl) ⟨1615115, by rfl⟩ : syracuseStep 2153487 = 3230231) B3230231
theorem B3230237 : Blo 2153435 3230237 := bbase (se 3 (by rfl) ⟨605669, by rfl⟩ : syracuseStep 3230237 = 1211339) (by norm_num)
theorem B2153491 : Blo 2153435 2153491 := bstep (se 1 (by rfl) ⟨1615118, by rfl⟩ : syracuseStep 2153491 = 3230237) B3230237
theorem B4845365 : Blo 2153435 4845365 := bbase (se 5 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 4845365 = 454253) (by norm_num)
theorem B3230243 : Blo 2153435 3230243 := bstep (se 1 (by rfl) ⟨2422682, by rfl⟩ : syracuseStep 3230243 = 4845365) B4845365
theorem B2153495 : Blo 2153435 2153495 := bstep (se 1 (by rfl) ⟨1615121, by rfl⟩ : syracuseStep 2153495 = 3230243) B3230243
theorem B5174237 : Blo 2153435 5174237 := bbase (se 3 (by rfl) ⟨970169, by rfl⟩ : syracuseStep 5174237 = 1940339) (by norm_num)
theorem B13797965 : Blo 2153435 13797965 := bstep (se 3 (by rfl) ⟨2587118, by rfl⟩ : syracuseStep 13797965 = 5174237) B5174237
theorem B9198643 : Blo 2153435 9198643 := bstep (se 1 (by rfl) ⟨6898982, by rfl⟩ : syracuseStep 9198643 = 13797965) B13797965
theorem B12264857 : Blo 2153435 12264857 := bstep (se 2 (by rfl) ⟨4599321, by rfl⟩ : syracuseStep 12264857 = 9198643) B9198643
theorem B8176571 : Blo 2153435 8176571 := bstep (se 1 (by rfl) ⟨6132428, by rfl⟩ : syracuseStep 8176571 = 12264857) B12264857
theorem B5451047 : Blo 2153435 5451047 := bstep (se 1 (by rfl) ⟨4088285, by rfl⟩ : syracuseStep 5451047 = 8176571) B8176571
theorem B3634031 : Blo 2153435 3634031 := bstep (se 1 (by rfl) ⟨2725523, by rfl⟩ : syracuseStep 3634031 = 5451047) B5451047
theorem B2422687 : Blo 2153435 2422687 := bstep (se 1 (by rfl) ⟨1817015, by rfl⟩ : syracuseStep 2422687 = 3634031) B3634031
theorem B3230249 : Blo 2153435 3230249 := bstep (se 2 (by rfl) ⟨1211343, by rfl⟩ : syracuseStep 3230249 = 2422687) B2422687
theorem B2153499 : Blo 2153435 2153499 := bstep (se 1 (by rfl) ⟨1615124, by rfl⟩ : syracuseStep 2153499 = 3230249) B3230249
theorem B3880685 : Blo 2153435 3880685 := bbase (se 3 (by rfl) ⟨727628, by rfl⟩ : syracuseStep 3880685 = 1455257) (by norm_num)
theorem B2587123 : Blo 2153435 2587123 := bstep (se 1 (by rfl) ⟨1940342, by rfl⟩ : syracuseStep 2587123 = 3880685) B3880685
theorem B13797989 : Blo 2153435 13797989 := bstep (se 4 (by rfl) ⟨1293561, by rfl⟩ : syracuseStep 13797989 = 2587123) B2587123
theorem B9198659 : Blo 2153435 9198659 := bstep (se 1 (by rfl) ⟨6898994, by rfl⟩ : syracuseStep 9198659 = 13797989) B13797989
theorem B6132439 : Blo 2153435 6132439 := bstep (se 1 (by rfl) ⟨4599329, by rfl⟩ : syracuseStep 6132439 = 9198659) B9198659
theorem B8176585 : Blo 2153435 8176585 := bstep (se 2 (by rfl) ⟨3066219, by rfl⟩ : syracuseStep 8176585 = 6132439) B6132439
theorem B10902113 : Blo 2153435 10902113 := bstep (se 2 (by rfl) ⟨4088292, by rfl⟩ : syracuseStep 10902113 = 8176585) B8176585
theorem B7268075 : Blo 2153435 7268075 := bstep (se 1 (by rfl) ⟨5451056, by rfl⟩ : syracuseStep 7268075 = 10902113) B10902113
theorem B4845383 : Blo 2153435 4845383 := bstep (se 1 (by rfl) ⟨3634037, by rfl⟩ : syracuseStep 4845383 = 7268075) B7268075
theorem B3230255 : Blo 2153435 3230255 := bstep (se 1 (by rfl) ⟨2422691, by rfl⟩ : syracuseStep 3230255 = 4845383) B4845383
theorem B2153503 : Blo 2153435 2153503 := bstep (se 1 (by rfl) ⟨1615127, by rfl⟩ : syracuseStep 2153503 = 3230255) B3230255
theorem B3230261 : Blo 2153435 3230261 := bbase (se 5 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 3230261 = 302837) (by norm_num)
theorem B2153507 : Blo 2153435 2153507 := bstep (se 1 (by rfl) ⟨1615130, by rfl⟩ : syracuseStep 2153507 = 3230261) B3230261
theorem B5451077 : Blo 2153435 5451077 := bbase (se 4 (by rfl) ⟨511038, by rfl⟩ : syracuseStep 5451077 = 1022077) (by norm_num)
theorem B3634051 : Blo 2153435 3634051 := bstep (se 1 (by rfl) ⟨2725538, by rfl⟩ : syracuseStep 3634051 = 5451077) B5451077
theorem B4845401 : Blo 2153435 4845401 := bstep (se 2 (by rfl) ⟨1817025, by rfl⟩ : syracuseStep 4845401 = 3634051) B3634051
theorem B3230267 : Blo 2153435 3230267 := bstep (se 1 (by rfl) ⟨2422700, by rfl⟩ : syracuseStep 3230267 = 4845401) B4845401
theorem B2153511 : Blo 2153435 2153511 := bstep (se 1 (by rfl) ⟨1615133, by rfl⟩ : syracuseStep 2153511 = 3230267) B3230267
theorem B2422705 : Blo 2153435 2422705 := bbase (se 2 (by rfl) ⟨908514, by rfl⟩ : syracuseStep 2422705 = 1817029) (by norm_num)
theorem B3230273 : Blo 2153435 3230273 := bstep (se 2 (by rfl) ⟨1211352, by rfl⟩ : syracuseStep 3230273 = 2422705) B2422705
theorem B2153515 : Blo 2153435 2153515 := bstep (se 1 (by rfl) ⟨1615136, by rfl⟩ : syracuseStep 2153515 = 3230273) B3230273
theorem B6132485 : Blo 2153435 6132485 := bbase (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) (by norm_num)
theorem B4088323 : Blo 2153435 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B5451097 : Blo 2153435 5451097 := bstep (se 2 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 5451097 = 4088323) B4088323
theorem B7268129 : Blo 2153435 7268129 := bstep (se 2 (by rfl) ⟨2725548, by rfl⟩ : syracuseStep 7268129 = 5451097) B5451097
theorem B4845419 : Blo 2153435 4845419 := bstep (se 1 (by rfl) ⟨3634064, by rfl⟩ : syracuseStep 4845419 = 7268129) B7268129
theorem B3230279 : Blo 2153435 3230279 := bstep (se 1 (by rfl) ⟨2422709, by rfl⟩ : syracuseStep 3230279 = 4845419) B4845419
theorem B2153519 : Blo 2153435 2153519 := bstep (se 1 (by rfl) ⟨1615139, by rfl⟩ : syracuseStep 2153519 = 3230279) B3230279
theorem B3230285 : Blo 2153435 3230285 := bbase (se 3 (by rfl) ⟨605678, by rfl⟩ : syracuseStep 3230285 = 1211357) (by norm_num)
theorem B2153523 : Blo 2153435 2153523 := bstep (se 1 (by rfl) ⟨1615142, by rfl⟩ : syracuseStep 2153523 = 3230285) B3230285
theorem B4845437 : Blo 2153435 4845437 := bbase (se 3 (by rfl) ⟨908519, by rfl⟩ : syracuseStep 4845437 = 1817039) (by norm_num)
theorem B3230291 : Blo 2153435 3230291 := bstep (se 1 (by rfl) ⟨2422718, by rfl⟩ : syracuseStep 3230291 = 4845437) B4845437
theorem B2153527 : Blo 2153435 2153527 := bstep (se 1 (by rfl) ⟨1615145, by rfl⟩ : syracuseStep 2153527 = 3230291) B3230291
theorem B3634085 : Blo 2153435 3634085 := bbase (se 4 (by rfl) ⟨340695, by rfl⟩ : syracuseStep 3634085 = 681391) (by norm_num)
theorem B2422723 : Blo 2153435 2422723 := bstep (se 1 (by rfl) ⟨1817042, by rfl⟩ : syracuseStep 2422723 = 3634085) B3634085
theorem B3230297 : Blo 2153435 3230297 := bstep (se 2 (by rfl) ⟨1211361, by rfl⟩ : syracuseStep 3230297 = 2422723) B2422723
theorem B2153531 : Blo 2153435 2153531 := bstep (se 1 (by rfl) ⟨1615148, by rfl⟩ : syracuseStep 2153531 = 3230297) B3230297
theorem B3449549 : Blo 2153435 3449549 := bbase (se 3 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 3449549 = 1293581) (by norm_num)
theorem B2299699 : Blo 2153435 2299699 := bstep (se 1 (by rfl) ⟨1724774, by rfl⟩ : syracuseStep 2299699 = 3449549) B3449549
theorem B3066265 : Blo 2153435 3066265 := bstep (se 2 (by rfl) ⟨1149849, by rfl⟩ : syracuseStep 3066265 = 2299699) B2299699
theorem B16353413 : Blo 2153435 16353413 := bstep (se 4 (by rfl) ⟨1533132, by rfl⟩ : syracuseStep 16353413 = 3066265) B3066265
theorem B10902275 : Blo 2153435 10902275 := bstep (se 1 (by rfl) ⟨8176706, by rfl⟩ : syracuseStep 10902275 = 16353413) B16353413
theorem B7268183 : Blo 2153435 7268183 := bstep (se 1 (by rfl) ⟨5451137, by rfl⟩ : syracuseStep 7268183 = 10902275) B10902275
theorem B4845455 : Blo 2153435 4845455 := bstep (se 1 (by rfl) ⟨3634091, by rfl⟩ : syracuseStep 4845455 = 7268183) B7268183
theorem B3230303 : Blo 2153435 3230303 := bstep (se 1 (by rfl) ⟨2422727, by rfl⟩ : syracuseStep 3230303 = 4845455) B4845455
theorem B2153535 : Blo 2153435 2153535 := bstep (se 1 (by rfl) ⟨1615151, by rfl⟩ : syracuseStep 2153535 = 3230303) B3230303
theorem B3230309 : Blo 2153435 3230309 := bbase (se 4 (by rfl) ⟨302841, by rfl⟩ : syracuseStep 3230309 = 605683) (by norm_num)
theorem B2153539 : Blo 2153435 2153539 := bstep (se 1 (by rfl) ⟨1615154, by rfl⟩ : syracuseStep 2153539 = 3230309) B3230309
theorem B3066277 : Blo 2153435 3066277 := bbase (se 4 (by rfl) ⟨287463, by rfl⟩ : syracuseStep 3066277 = 574927) (by norm_num)
theorem B4088369 : Blo 2153435 4088369 := bstep (se 2 (by rfl) ⟨1533138, by rfl⟩ : syracuseStep 4088369 = 3066277) B3066277
theorem B2725579 : Blo 2153435 2725579 := bstep (se 1 (by rfl) ⟨2044184, by rfl⟩ : syracuseStep 2725579 = 4088369) B4088369
theorem B3634105 : Blo 2153435 3634105 := bstep (se 2 (by rfl) ⟨1362789, by rfl⟩ : syracuseStep 3634105 = 2725579) B2725579
theorem B4845473 : Blo 2153435 4845473 := bstep (se 2 (by rfl) ⟨1817052, by rfl⟩ : syracuseStep 4845473 = 3634105) B3634105
theorem B3230315 : Blo 2153435 3230315 := bstep (se 1 (by rfl) ⟨2422736, by rfl⟩ : syracuseStep 3230315 = 4845473) B4845473
theorem B2153543 : Blo 2153435 2153543 := bstep (se 1 (by rfl) ⟨1615157, by rfl⟩ : syracuseStep 2153543 = 3230315) B3230315
theorem B2422741 : Blo 2153435 2422741 := bbase (se 7 (by rfl) ⟨28391, by rfl⟩ : syracuseStep 2422741 = 56783) (by norm_num)
theorem B3230321 : Blo 2153435 3230321 := bstep (se 2 (by rfl) ⟨1211370, by rfl⟩ : syracuseStep 3230321 = 2422741) B2422741
theorem B2153547 : Blo 2153435 2153547 := bstep (se 1 (by rfl) ⟨1615160, by rfl⟩ : syracuseStep 2153547 = 3230321) B3230321
theorem B2725589 : Blo 2153435 2725589 := bbase (se 7 (by rfl) ⟨31940, by rfl⟩ : syracuseStep 2725589 = 63881) (by norm_num)
theorem B7268237 : Blo 2153435 7268237 := bstep (se 3 (by rfl) ⟨1362794, by rfl⟩ : syracuseStep 7268237 = 2725589) B2725589
theorem B4845491 : Blo 2153435 4845491 := bstep (se 1 (by rfl) ⟨3634118, by rfl⟩ : syracuseStep 4845491 = 7268237) B7268237
theorem B3230327 : Blo 2153435 3230327 := bstep (se 1 (by rfl) ⟨2422745, by rfl⟩ : syracuseStep 3230327 = 4845491) B4845491
theorem B2153551 : Blo 2153435 2153551 := bstep (se 1 (by rfl) ⟨1615163, by rfl⟩ : syracuseStep 2153551 = 3230327) B3230327
theorem B3230333 : Blo 2153435 3230333 := bbase (se 3 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 3230333 = 1211375) (by norm_num)
theorem B2153555 : Blo 2153435 2153555 := bstep (se 1 (by rfl) ⟨1615166, by rfl⟩ : syracuseStep 2153555 = 3230333) B3230333
theorem B4845509 : Blo 2153435 4845509 := bbase (se 4 (by rfl) ⟨454266, by rfl⟩ : syracuseStep 4845509 = 908533) (by norm_num)
theorem B3230339 : Blo 2153435 3230339 := bstep (se 1 (by rfl) ⟨2422754, by rfl⟩ : syracuseStep 3230339 = 4845509) B4845509
theorem B2153559 : Blo 2153435 2153559 := bstep (se 1 (by rfl) ⟨1615169, by rfl⟩ : syracuseStep 2153559 = 3230339) B3230339
theorem B9198917 : Blo 2153435 9198917 := bbase (se 4 (by rfl) ⟨862398, by rfl⟩ : syracuseStep 9198917 = 1724797) (by norm_num)
theorem B6132611 : Blo 2153435 6132611 := bstep (se 1 (by rfl) ⟨4599458, by rfl⟩ : syracuseStep 6132611 = 9198917) B9198917
theorem B4088407 : Blo 2153435 4088407 := bstep (se 1 (by rfl) ⟨3066305, by rfl⟩ : syracuseStep 4088407 = 6132611) B6132611
theorem B5451209 : Blo 2153435 5451209 := bstep (se 2 (by rfl) ⟨2044203, by rfl⟩ : syracuseStep 5451209 = 4088407) B4088407
theorem B3634139 : Blo 2153435 3634139 := bstep (se 1 (by rfl) ⟨2725604, by rfl⟩ : syracuseStep 3634139 = 5451209) B5451209
theorem B2422759 : Blo 2153435 2422759 := bstep (se 1 (by rfl) ⟨1817069, by rfl⟩ : syracuseStep 2422759 = 3634139) B3634139
theorem B3230345 : Blo 2153435 3230345 := bstep (se 2 (by rfl) ⟨1211379, by rfl⟩ : syracuseStep 3230345 = 2422759) B2422759
theorem B2153563 : Blo 2153435 2153563 := bstep (se 1 (by rfl) ⟨1615172, by rfl⟩ : syracuseStep 2153563 = 3230345) B3230345
theorem B10902437 : Blo 2153435 10902437 := bbase (se 4 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 10902437 = 2044207) (by norm_num)
theorem B7268291 : Blo 2153435 7268291 := bstep (se 1 (by rfl) ⟨5451218, by rfl⟩ : syracuseStep 7268291 = 10902437) B10902437
theorem B4845527 : Blo 2153435 4845527 := bstep (se 1 (by rfl) ⟨3634145, by rfl⟩ : syracuseStep 4845527 = 7268291) B7268291
theorem B3230351 : Blo 2153435 3230351 := bstep (se 1 (by rfl) ⟨2422763, by rfl⟩ : syracuseStep 3230351 = 4845527) B4845527
theorem B2153567 : Blo 2153435 2153567 := bstep (se 1 (by rfl) ⟨1615175, by rfl⟩ : syracuseStep 2153567 = 3230351) B3230351
theorem B3230357 : Blo 2153435 3230357 := bbase (se 6 (by rfl) ⟨75711, by rfl⟩ : syracuseStep 3230357 = 151423) (by norm_num)
theorem B2153571 : Blo 2153435 2153571 := bstep (se 1 (by rfl) ⟨1615178, by rfl⟩ : syracuseStep 2153571 = 3230357) B3230357
theorem B4365917 : Blo 2153435 4365917 := bbase (se 3 (by rfl) ⟨818609, by rfl⟩ : syracuseStep 4365917 = 1637219) (by norm_num)
theorem B2910611 : Blo 2153435 2910611 := bstep (se 1 (by rfl) ⟨2182958, by rfl⟩ : syracuseStep 2910611 = 4365917) B4365917
theorem B7761629 : Blo 2153435 7761629 := bstep (se 3 (by rfl) ⟨1455305, by rfl⟩ : syracuseStep 7761629 = 2910611) B2910611
theorem B20697677 : Blo 2153435 20697677 := bstep (se 3 (by rfl) ⟨3880814, by rfl⟩ : syracuseStep 20697677 = 7761629) B7761629
theorem B13798451 : Blo 2153435 13798451 := bstep (se 1 (by rfl) ⟨10348838, by rfl⟩ : syracuseStep 13798451 = 20697677) B20697677
theorem B9198967 : Blo 2153435 9198967 := bstep (se 1 (by rfl) ⟨6899225, by rfl⟩ : syracuseStep 9198967 = 13798451) B13798451
theorem B12265289 : Blo 2153435 12265289 := bstep (se 2 (by rfl) ⟨4599483, by rfl⟩ : syracuseStep 12265289 = 9198967) B9198967
theorem B8176859 : Blo 2153435 8176859 := bstep (se 1 (by rfl) ⟨6132644, by rfl⟩ : syracuseStep 8176859 = 12265289) B12265289
theorem B5451239 : Blo 2153435 5451239 := bstep (se 1 (by rfl) ⟨4088429, by rfl⟩ : syracuseStep 5451239 = 8176859) B8176859
theorem B3634159 : Blo 2153435 3634159 := bstep (se 1 (by rfl) ⟨2725619, by rfl⟩ : syracuseStep 3634159 = 5451239) B5451239
theorem B4845545 : Blo 2153435 4845545 := bstep (se 2 (by rfl) ⟨1817079, by rfl⟩ : syracuseStep 4845545 = 3634159) B3634159
theorem B3230363 : Blo 2153435 3230363 := bstep (se 1 (by rfl) ⟨2422772, by rfl⟩ : syracuseStep 3230363 = 4845545) B4845545
theorem B2153575 : Blo 2153435 2153575 := bstep (se 1 (by rfl) ⟨1615181, by rfl⟩ : syracuseStep 2153575 = 3230363) B3230363
theorem B2422777 : Blo 2153435 2422777 := bbase (se 2 (by rfl) ⟨908541, by rfl⟩ : syracuseStep 2422777 = 1817083) (by norm_num)
theorem B3230369 : Blo 2153435 3230369 := bstep (se 2 (by rfl) ⟨1211388, by rfl⟩ : syracuseStep 3230369 = 2422777) B2422777
theorem B2153579 : Blo 2153435 2153579 := bstep (se 1 (by rfl) ⟨1615184, by rfl⟩ : syracuseStep 2153579 = 3230369) B3230369
theorem B3880829 : Blo 2153435 3880829 := bbase (se 3 (by rfl) ⟨727655, by rfl⟩ : syracuseStep 3880829 = 1455311) (by norm_num)
theorem B10348877 : Blo 2153435 10348877 := bstep (se 3 (by rfl) ⟨1940414, by rfl⟩ : syracuseStep 10348877 = 3880829) B3880829
theorem B6899251 : Blo 2153435 6899251 := bstep (se 1 (by rfl) ⟨5174438, by rfl⟩ : syracuseStep 6899251 = 10348877) B10348877
theorem B9199001 : Blo 2153435 9199001 := bstep (se 2 (by rfl) ⟨3449625, by rfl⟩ : syracuseStep 9199001 = 6899251) B6899251
theorem B6132667 : Blo 2153435 6132667 := bstep (se 1 (by rfl) ⟨4599500, by rfl⟩ : syracuseStep 6132667 = 9199001) B9199001
theorem B8176889 : Blo 2153435 8176889 := bstep (se 2 (by rfl) ⟨3066333, by rfl⟩ : syracuseStep 8176889 = 6132667) B6132667
theorem B5451259 : Blo 2153435 5451259 := bstep (se 1 (by rfl) ⟨4088444, by rfl⟩ : syracuseStep 5451259 = 8176889) B8176889
theorem B7268345 : Blo 2153435 7268345 := bstep (se 2 (by rfl) ⟨2725629, by rfl⟩ : syracuseStep 7268345 = 5451259) B5451259
theorem B4845563 : Blo 2153435 4845563 := bstep (se 1 (by rfl) ⟨3634172, by rfl⟩ : syracuseStep 4845563 = 7268345) B7268345
theorem B3230375 : Blo 2153435 3230375 := bstep (se 1 (by rfl) ⟨2422781, by rfl⟩ : syracuseStep 3230375 = 4845563) B4845563
theorem B2153583 : Blo 2153435 2153583 := bstep (se 1 (by rfl) ⟨1615187, by rfl⟩ : syracuseStep 2153583 = 3230375) B3230375
theorem B3230381 : Blo 2153435 3230381 := bbase (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) (by norm_num)
theorem B2153587 : Blo 2153435 2153587 := bstep (se 1 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 2153587 = 3230381) B3230381
theorem B4845581 : Blo 2153435 4845581 := bbase (se 3 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 4845581 = 1817093) (by norm_num)
theorem B3230387 : Blo 2153435 3230387 := bstep (se 1 (by rfl) ⟨2422790, by rfl⟩ : syracuseStep 3230387 = 4845581) B4845581
theorem B2153591 : Blo 2153435 2153591 := bstep (se 1 (by rfl) ⟨1615193, by rfl⟩ : syracuseStep 2153591 = 3230387) B3230387
theorem B2725645 : Blo 2153435 2725645 := bbase (se 3 (by rfl) ⟨511058, by rfl⟩ : syracuseStep 2725645 = 1022117) (by norm_num)
theorem B3634193 : Blo 2153435 3634193 := bstep (se 2 (by rfl) ⟨1362822, by rfl⟩ : syracuseStep 3634193 = 2725645) B2725645
theorem B2422795 : Blo 2153435 2422795 := bstep (se 1 (by rfl) ⟨1817096, by rfl⟩ : syracuseStep 2422795 = 3634193) B3634193
theorem B3230393 : Blo 2153435 3230393 := bstep (se 2 (by rfl) ⟨1211397, by rfl⟩ : syracuseStep 3230393 = 2422795) B2422795
theorem B2153595 : Blo 2153435 2153595 := bstep (se 1 (by rfl) ⟨1615196, by rfl⟩ : syracuseStep 2153595 = 3230393) B3230393
theorem B4365965 : Blo 2153435 4365965 := bbase (se 3 (by rfl) ⟨818618, by rfl⟩ : syracuseStep 4365965 = 1637237) (by norm_num)
theorem B2910643 : Blo 2153435 2910643 := bstep (se 1 (by rfl) ⟨2182982, by rfl⟩ : syracuseStep 2910643 = 4365965) B4365965
theorem B15523429 : Blo 2153435 15523429 := bstep (se 4 (by rfl) ⟨1455321, by rfl⟩ : syracuseStep 15523429 = 2910643) B2910643
theorem B20697905 : Blo 2153435 20697905 := bstep (se 2 (by rfl) ⟨7761714, by rfl⟩ : syracuseStep 20697905 = 15523429) B15523429
theorem B13798603 : Blo 2153435 13798603 := bstep (se 1 (by rfl) ⟨10348952, by rfl⟩ : syracuseStep 13798603 = 20697905) B20697905
theorem B18398137 : Blo 2153435 18398137 := bstep (se 2 (by rfl) ⟨6899301, by rfl⟩ : syracuseStep 18398137 = 13798603) B13798603
theorem B24530849 : Blo 2153435 24530849 := bstep (se 2 (by rfl) ⟨9199068, by rfl⟩ : syracuseStep 24530849 = 18398137) B18398137
theorem B16353899 : Blo 2153435 16353899 := bstep (se 1 (by rfl) ⟨12265424, by rfl⟩ : syracuseStep 16353899 = 24530849) B24530849
theorem B10902599 : Blo 2153435 10902599 := bstep (se 1 (by rfl) ⟨8176949, by rfl⟩ : syracuseStep 10902599 = 16353899) B16353899
theorem B7268399 : Blo 2153435 7268399 := bstep (se 1 (by rfl) ⟨5451299, by rfl⟩ : syracuseStep 7268399 = 10902599) B10902599
theorem B4845599 : Blo 2153435 4845599 := bstep (se 1 (by rfl) ⟨3634199, by rfl⟩ : syracuseStep 4845599 = 7268399) B7268399
theorem B3230399 : Blo 2153435 3230399 := bstep (se 1 (by rfl) ⟨2422799, by rfl⟩ : syracuseStep 3230399 = 4845599) B4845599
theorem B2153599 : Blo 2153435 2153599 := bstep (se 1 (by rfl) ⟨1615199, by rfl⟩ : syracuseStep 2153599 = 3230399) B3230399
theorem B3230405 : Blo 2153435 3230405 := bbase (se 4 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 3230405 = 605701) (by norm_num)
theorem B2153603 : Blo 2153435 2153603 := bstep (se 1 (by rfl) ⟨1615202, by rfl⟩ : syracuseStep 2153603 = 3230405) B3230405
theorem B3634213 : Blo 2153435 3634213 := bbase (se 4 (by rfl) ⟨340707, by rfl⟩ : syracuseStep 3634213 = 681415) (by norm_num)
theorem B4845617 : Blo 2153435 4845617 := bstep (se 2 (by rfl) ⟨1817106, by rfl⟩ : syracuseStep 4845617 = 3634213) B3634213
theorem B3230411 : Blo 2153435 3230411 := bstep (se 1 (by rfl) ⟨2422808, by rfl⟩ : syracuseStep 3230411 = 4845617) B4845617
theorem B2153607 : Blo 2153435 2153607 := bstep (se 1 (by rfl) ⟨1615205, by rfl⟩ : syracuseStep 2153607 = 3230411) B3230411
theorem B2422813 : Blo 2153435 2422813 := bbase (se 3 (by rfl) ⟨454277, by rfl⟩ : syracuseStep 2422813 = 908555) (by norm_num)
theorem B3230417 : Blo 2153435 3230417 := bstep (se 2 (by rfl) ⟨1211406, by rfl⟩ : syracuseStep 3230417 = 2422813) B2422813
theorem B2153611 : Blo 2153435 2153611 := bstep (se 1 (by rfl) ⟨1615208, by rfl⟩ : syracuseStep 2153611 = 3230417) B3230417
theorem B7268453 : Blo 2153435 7268453 := bbase (se 4 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 7268453 = 1362835) (by norm_num)
theorem B4845635 : Blo 2153435 4845635 := bstep (se 1 (by rfl) ⟨3634226, by rfl⟩ : syracuseStep 4845635 = 7268453) B7268453
theorem B3230423 : Blo 2153435 3230423 := bstep (se 1 (by rfl) ⟨2422817, by rfl⟩ : syracuseStep 3230423 = 4845635) B4845635
theorem B2153615 : Blo 2153435 2153615 := bstep (se 1 (by rfl) ⟨1615211, by rfl⟩ : syracuseStep 2153615 = 3230423) B3230423
theorem B3230429 : Blo 2153435 3230429 := bbase (se 3 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 3230429 = 1211411) (by norm_num)
theorem B2153619 : Blo 2153435 2153619 := bstep (se 1 (by rfl) ⟨1615214, by rfl⟩ : syracuseStep 2153619 = 3230429) B3230429
theorem B4845653 : Blo 2153435 4845653 := bbase (se 8 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 4845653 = 56785) (by norm_num)
theorem B3230435 : Blo 2153435 3230435 := bstep (se 1 (by rfl) ⟨2422826, by rfl⟩ : syracuseStep 3230435 = 4845653) B4845653
theorem B2153623 : Blo 2153435 2153623 := bstep (se 1 (by rfl) ⟨1615217, by rfl⟩ : syracuseStep 2153623 = 3230435) B3230435
theorem B3880909 : Blo 2153435 3880909 := bbase (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) (by norm_num)
theorem B5174545 : Blo 2153435 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B6899393 : Blo 2153435 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B4599595 : Blo 2153435 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B6132793 : Blo 2153435 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B8177057 : Blo 2153435 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B5451371 : Blo 2153435 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B3634247 : Blo 2153435 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B2422831 : Blo 2153435 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B3230441 : Blo 2153435 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B2153627 : Blo 2153435 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B3592837 : Blo 2153435 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B4790449 : Blo 2153435 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B6387265 : Blo 2153435 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B8516353 : Blo 2153435 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B11355137 : Blo 2153435 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B7570091 : Blo 2153435 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B20186909 : Blo 2153435 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B13457939 : Blo 2153435 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B143551349 : Blo 2153435 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B95700899 : Blo 2153435 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B255202397 : Blo 2153435 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B170134931 : Blo 2153435 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B113423287 : Blo 2153435 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B151231049 : Blo 2153435 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B100820699 : Blo 2153435 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B67213799 : Blo 2153435 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B44809199 : Blo 2153435 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B29872799 : Blo 2153435 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B19915199 : Blo 2153435 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B13276799 : Blo 2153435 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B8851199 : Blo 2153435 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B94412789 : Blo 2153435 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B62941859 : Blo 2153435 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B41961239 : Blo 2153435 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B27974159 : Blo 2153435 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B18649439 : Blo 2153435 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B12432959 : Blo 2153435 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B8288639 : Blo 2153435 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B5525759 : Blo 2153435 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B3683839 : Blo 2153435 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B4911785 : Blo 2153435 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B3274523 : Blo 2153435 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B2183015 : Blo 2153435 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B5821373 : Blo 2153435 5821373 := bstep (se 3 (by rfl) ⟨1091507, by rfl⟩ : syracuseStep 5821373 = 2183015) B2183015
theorem B3880915 : Blo 2153435 3880915 := bstep (se 1 (by rfl) ⟨2910686, by rfl⟩ : syracuseStep 3880915 = 5821373) B5821373
theorem B20698213 : Blo 2153435 20698213 := bstep (se 4 (by rfl) ⟨1940457, by rfl⟩ : syracuseStep 20698213 = 3880915) B3880915
theorem B27597617 : Blo 2153435 27597617 := bstep (se 2 (by rfl) ⟨10349106, by rfl⟩ : syracuseStep 27597617 = 20698213) B20698213
theorem B18398411 : Blo 2153435 18398411 := bstep (se 1 (by rfl) ⟨13798808, by rfl⟩ : syracuseStep 18398411 = 27597617) B27597617
theorem B12265607 : Blo 2153435 12265607 := bstep (se 1 (by rfl) ⟨9199205, by rfl⟩ : syracuseStep 12265607 = 18398411) B18398411
theorem B8177071 : Blo 2153435 8177071 := bstep (se 1 (by rfl) ⟨6132803, by rfl⟩ : syracuseStep 8177071 = 12265607) B12265607
theorem B10902761 : Blo 2153435 10902761 := bstep (se 2 (by rfl) ⟨4088535, by rfl⟩ : syracuseStep 10902761 = 8177071) B8177071
theorem B7268507 : Blo 2153435 7268507 := bstep (se 1 (by rfl) ⟨5451380, by rfl⟩ : syracuseStep 7268507 = 10902761) B10902761
theorem B4845671 : Blo 2153435 4845671 := bstep (se 1 (by rfl) ⟨3634253, by rfl⟩ : syracuseStep 4845671 = 7268507) B7268507
theorem B3230447 : Blo 2153435 3230447 := bstep (se 1 (by rfl) ⟨2422835, by rfl⟩ : syracuseStep 3230447 = 4845671) B4845671
theorem B2153631 : Blo 2153435 2153631 := bstep (se 1 (by rfl) ⟨1615223, by rfl⟩ : syracuseStep 2153631 = 3230447) B3230447
theorem B3230453 : Blo 2153435 3230453 := bbase (se 5 (by rfl) ⟨151427, by rfl⟩ : syracuseStep 3230453 = 302855) (by norm_num)
theorem B2153635 : Blo 2153435 2153635 := bstep (se 1 (by rfl) ⟨1615226, by rfl⟩ : syracuseStep 2153635 = 3230453) B3230453
theorem B4200877 : Blo 2153435 4200877 := bbase (se 3 (by rfl) ⟨787664, by rfl⟩ : syracuseStep 4200877 = 1575329) (by norm_num)
theorem B5601169 : Blo 2153435 5601169 := bstep (se 2 (by rfl) ⟨2100438, by rfl⟩ : syracuseStep 5601169 = 4200877) B4200877
theorem B29872901 : Blo 2153435 29872901 := bstep (se 4 (by rfl) ⟨2800584, by rfl⟩ : syracuseStep 29872901 = 5601169) B5601169
theorem B19915267 : Blo 2153435 19915267 := bstep (se 1 (by rfl) ⟨14936450, by rfl⟩ : syracuseStep 19915267 = 29872901) B29872901
theorem B26553689 : Blo 2153435 26553689 := bstep (se 2 (by rfl) ⟨9957633, by rfl⟩ : syracuseStep 26553689 = 19915267) B19915267
theorem B17702459 : Blo 2153435 17702459 := bstep (se 1 (by rfl) ⟨13276844, by rfl⟩ : syracuseStep 17702459 = 26553689) B26553689
theorem B11801639 : Blo 2153435 11801639 := bstep (se 1 (by rfl) ⟨8851229, by rfl⟩ : syracuseStep 11801639 = 17702459) B17702459
theorem B31471037 : Blo 2153435 31471037 := bstep (se 3 (by rfl) ⟨5900819, by rfl⟩ : syracuseStep 31471037 = 11801639) B11801639
theorem B20980691 : Blo 2153435 20980691 := bstep (se 1 (by rfl) ⟨15735518, by rfl⟩ : syracuseStep 20980691 = 31471037) B31471037
theorem B13987127 : Blo 2153435 13987127 := bstep (se 1 (by rfl) ⟨10490345, by rfl⟩ : syracuseStep 13987127 = 20980691) B20980691
theorem B37299005 : Blo 2153435 37299005 := bstep (se 3 (by rfl) ⟨6993563, by rfl⟩ : syracuseStep 37299005 = 13987127) B13987127
theorem B24866003 : Blo 2153435 24866003 := bstep (se 1 (by rfl) ⟨18649502, by rfl⟩ : syracuseStep 24866003 = 37299005) B37299005
theorem B16577335 : Blo 2153435 16577335 := bstep (se 1 (by rfl) ⟨12433001, by rfl⟩ : syracuseStep 16577335 = 24866003) B24866003
theorem B22103113 : Blo 2153435 22103113 := bstep (se 2 (by rfl) ⟨8288667, by rfl⟩ : syracuseStep 22103113 = 16577335) B16577335
theorem B29470817 : Blo 2153435 29470817 := bstep (se 2 (by rfl) ⟨11051556, by rfl⟩ : syracuseStep 29470817 = 22103113) B22103113
theorem B19647211 : Blo 2153435 19647211 := bstep (se 1 (by rfl) ⟨14735408, by rfl⟩ : syracuseStep 19647211 = 29470817) B29470817
theorem B26196281 : Blo 2153435 26196281 := bstep (se 2 (by rfl) ⟨9823605, by rfl⟩ : syracuseStep 26196281 = 19647211) B19647211
theorem B17464187 : Blo 2153435 17464187 := bstep (se 1 (by rfl) ⟨13098140, by rfl⟩ : syracuseStep 17464187 = 26196281) B26196281
theorem B11642791 : Blo 2153435 11642791 := bstep (se 1 (by rfl) ⟨8732093, by rfl⟩ : syracuseStep 11642791 = 17464187) B17464187
theorem B15523721 : Blo 2153435 15523721 := bstep (se 2 (by rfl) ⟨5821395, by rfl⟩ : syracuseStep 15523721 = 11642791) B11642791
theorem B10349147 : Blo 2153435 10349147 := bstep (se 1 (by rfl) ⟨7761860, by rfl⟩ : syracuseStep 10349147 = 15523721) B15523721
theorem B6899431 : Blo 2153435 6899431 := bstep (se 1 (by rfl) ⟨5174573, by rfl⟩ : syracuseStep 6899431 = 10349147) B10349147
theorem B9199241 : Blo 2153435 9199241 := bstep (se 2 (by rfl) ⟨3449715, by rfl⟩ : syracuseStep 9199241 = 6899431) B6899431
theorem B6132827 : Blo 2153435 6132827 := bstep (se 1 (by rfl) ⟨4599620, by rfl⟩ : syracuseStep 6132827 = 9199241) B9199241
theorem B4088551 : Blo 2153435 4088551 := bstep (se 1 (by rfl) ⟨3066413, by rfl⟩ : syracuseStep 4088551 = 6132827) B6132827
theorem B5451401 : Blo 2153435 5451401 := bstep (se 2 (by rfl) ⟨2044275, by rfl⟩ : syracuseStep 5451401 = 4088551) B4088551
theorem B3634267 : Blo 2153435 3634267 := bstep (se 1 (by rfl) ⟨2725700, by rfl⟩ : syracuseStep 3634267 = 5451401) B5451401
theorem B4845689 : Blo 2153435 4845689 := bstep (se 2 (by rfl) ⟨1817133, by rfl⟩ : syracuseStep 4845689 = 3634267) B3634267
theorem B3230459 : Blo 2153435 3230459 := bstep (se 1 (by rfl) ⟨2422844, by rfl⟩ : syracuseStep 3230459 = 4845689) B4845689
theorem B2153639 : Blo 2153435 2153639 := bstep (se 1 (by rfl) ⟨1615229, by rfl⟩ : syracuseStep 2153639 = 3230459) B3230459
theorem B2422849 : Blo 2153435 2422849 := bbase (se 2 (by rfl) ⟨908568, by rfl⟩ : syracuseStep 2422849 = 1817137) (by norm_num)
theorem B3230465 : Blo 2153435 3230465 := bstep (se 2 (by rfl) ⟨1211424, by rfl⟩ : syracuseStep 3230465 = 2422849) B2422849
theorem B2153643 : Blo 2153435 2153643 := bstep (se 1 (by rfl) ⟨1615232, by rfl⟩ : syracuseStep 2153643 = 3230465) B3230465
theorem B5451421 : Blo 2153435 5451421 := bbase (se 3 (by rfl) ⟨1022141, by rfl⟩ : syracuseStep 5451421 = 2044283) (by norm_num)
theorem B7268561 : Blo 2153435 7268561 := bstep (se 2 (by rfl) ⟨2725710, by rfl⟩ : syracuseStep 7268561 = 5451421) B5451421
theorem B4845707 : Blo 2153435 4845707 := bstep (se 1 (by rfl) ⟨3634280, by rfl⟩ : syracuseStep 4845707 = 7268561) B7268561
theorem B3230471 : Blo 2153435 3230471 := bstep (se 1 (by rfl) ⟨2422853, by rfl⟩ : syracuseStep 3230471 = 4845707) B4845707
theorem B2153647 : Blo 2153435 2153647 := bstep (se 1 (by rfl) ⟨1615235, by rfl⟩ : syracuseStep 2153647 = 3230471) B3230471
theorem B3230477 : Blo 2153435 3230477 := bbase (se 3 (by rfl) ⟨605714, by rfl⟩ : syracuseStep 3230477 = 1211429) (by norm_num)
theorem B2153651 : Blo 2153435 2153651 := bstep (se 1 (by rfl) ⟨1615238, by rfl⟩ : syracuseStep 2153651 = 3230477) B3230477
theorem B4845725 : Blo 2153435 4845725 := bbase (se 3 (by rfl) ⟨908573, by rfl⟩ : syracuseStep 4845725 = 1817147) (by norm_num)
theorem B3230483 : Blo 2153435 3230483 := bstep (se 1 (by rfl) ⟨2422862, by rfl⟩ : syracuseStep 3230483 = 4845725) B4845725
theorem B2153655 : Blo 2153435 2153655 := bstep (se 1 (by rfl) ⟨1615241, by rfl⟩ : syracuseStep 2153655 = 3230483) B3230483
theorem B3634301 : Blo 2153435 3634301 := bbase (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) (by norm_num)
theorem B2422867 : Blo 2153435 2422867 := bstep (se 1 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 2422867 = 3634301) B3634301
theorem B3230489 : Blo 2153435 3230489 := bstep (se 2 (by rfl) ⟨1211433, by rfl⟩ : syracuseStep 3230489 = 2422867) B2422867
theorem B2153659 : Blo 2153435 2153659 := bstep (se 1 (by rfl) ⟨1615244, by rfl⟩ : syracuseStep 2153659 = 3230489) B3230489
theorem B3880973 : Blo 2153435 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B10349261 : Blo 2153435 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B6899507 : Blo 2153435 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B4599671 : Blo 2153435 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B12265789 : Blo 2153435 12265789 := bstep (se 3 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 12265789 = 4599671) B4599671
theorem B16354385 : Blo 2153435 16354385 := bstep (se 2 (by rfl) ⟨6132894, by rfl⟩ : syracuseStep 16354385 = 12265789) B12265789
theorem B10902923 : Blo 2153435 10902923 := bstep (se 1 (by rfl) ⟨8177192, by rfl⟩ : syracuseStep 10902923 = 16354385) B16354385
theorem B7268615 : Blo 2153435 7268615 := bstep (se 1 (by rfl) ⟨5451461, by rfl⟩ : syracuseStep 7268615 = 10902923) B10902923
theorem B4845743 : Blo 2153435 4845743 := bstep (se 1 (by rfl) ⟨3634307, by rfl⟩ : syracuseStep 4845743 = 7268615) B7268615
theorem B3230495 : Blo 2153435 3230495 := bstep (se 1 (by rfl) ⟨2422871, by rfl⟩ : syracuseStep 3230495 = 4845743) B4845743
theorem B2153663 : Blo 2153435 2153663 := bstep (se 1 (by rfl) ⟨1615247, by rfl⟩ : syracuseStep 2153663 = 3230495) B3230495
theorem B3230501 : Blo 2153435 3230501 := bbase (se 4 (by rfl) ⟨302859, by rfl⟩ : syracuseStep 3230501 = 605719) (by norm_num)
theorem B2153667 : Blo 2153435 2153667 := bstep (se 1 (by rfl) ⟨1615250, by rfl⟩ : syracuseStep 2153667 = 3230501) B3230501
theorem B2725741 : Blo 2153435 2725741 := bbase (se 3 (by rfl) ⟨511076, by rfl⟩ : syracuseStep 2725741 = 1022153) (by norm_num)
theorem B3634321 : Blo 2153435 3634321 := bstep (se 2 (by rfl) ⟨1362870, by rfl⟩ : syracuseStep 3634321 = 2725741) B2725741
theorem B4845761 : Blo 2153435 4845761 := bstep (se 2 (by rfl) ⟨1817160, by rfl⟩ : syracuseStep 4845761 = 3634321) B3634321
theorem B3230507 : Blo 2153435 3230507 := bstep (se 1 (by rfl) ⟨2422880, by rfl⟩ : syracuseStep 3230507 = 4845761) B4845761
theorem B2153671 : Blo 2153435 2153671 := bstep (se 1 (by rfl) ⟨1615253, by rfl⟩ : syracuseStep 2153671 = 3230507) B3230507
theorem B2422885 : Blo 2153435 2422885 := bbase (se 4 (by rfl) ⟨227145, by rfl⟩ : syracuseStep 2422885 = 454291) (by norm_num)
theorem B3230513 : Blo 2153435 3230513 := bstep (se 2 (by rfl) ⟨1211442, by rfl⟩ : syracuseStep 3230513 = 2422885) B2422885
theorem B2153675 : Blo 2153435 2153675 := bstep (se 1 (by rfl) ⟨1615256, by rfl⟩ : syracuseStep 2153675 = 3230513) B3230513
theorem B2299853 : Blo 2153435 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B6132941 : Blo 2153435 6132941 := bstep (se 3 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 6132941 = 2299853) B2299853
theorem B4088627 : Blo 2153435 4088627 := bstep (se 1 (by rfl) ⟨3066470, by rfl⟩ : syracuseStep 4088627 = 6132941) B6132941
theorem B2725751 : Blo 2153435 2725751 := bstep (se 1 (by rfl) ⟨2044313, by rfl⟩ : syracuseStep 2725751 = 4088627) B4088627
theorem B7268669 : Blo 2153435 7268669 := bstep (se 3 (by rfl) ⟨1362875, by rfl⟩ : syracuseStep 7268669 = 2725751) B2725751
theorem B4845779 : Blo 2153435 4845779 := bstep (se 1 (by rfl) ⟨3634334, by rfl⟩ : syracuseStep 4845779 = 7268669) B7268669
theorem B3230519 : Blo 2153435 3230519 := bstep (se 1 (by rfl) ⟨2422889, by rfl⟩ : syracuseStep 3230519 = 4845779) B4845779
theorem B2153679 : Blo 2153435 2153679 := bstep (se 1 (by rfl) ⟨1615259, by rfl⟩ : syracuseStep 2153679 = 3230519) B3230519
theorem B3230525 : Blo 2153435 3230525 := bbase (se 3 (by rfl) ⟨605723, by rfl⟩ : syracuseStep 3230525 = 1211447) (by norm_num)
theorem B2153683 : Blo 2153435 2153683 := bstep (se 1 (by rfl) ⟨1615262, by rfl⟩ : syracuseStep 2153683 = 3230525) B3230525
theorem B4845797 : Blo 2153435 4845797 := bbase (se 4 (by rfl) ⟨454293, by rfl⟩ : syracuseStep 4845797 = 908587) (by norm_num)
theorem B3230531 : Blo 2153435 3230531 := bstep (se 1 (by rfl) ⟨2422898, by rfl⟩ : syracuseStep 3230531 = 4845797) B4845797
theorem B2153687 : Blo 2153435 2153687 := bstep (se 1 (by rfl) ⟨1615265, by rfl⟩ : syracuseStep 2153687 = 3230531) B3230531
theorem B5451533 : Blo 2153435 5451533 := bbase (se 3 (by rfl) ⟨1022162, by rfl⟩ : syracuseStep 5451533 = 2044325) (by norm_num)
theorem B3634355 : Blo 2153435 3634355 := bstep (se 1 (by rfl) ⟨2725766, by rfl⟩ : syracuseStep 3634355 = 5451533) B5451533
theorem B2422903 : Blo 2153435 2422903 := bstep (se 1 (by rfl) ⟨1817177, by rfl⟩ : syracuseStep 2422903 = 3634355) B3634355
theorem B3230537 : Blo 2153435 3230537 := bstep (se 2 (by rfl) ⟨1211451, by rfl⟩ : syracuseStep 3230537 = 2422903) B2422903
theorem B2153691 : Blo 2153435 2153691 := bstep (se 1 (by rfl) ⟨1615268, by rfl⟩ : syracuseStep 2153691 = 3230537) B3230537
theorem B3066493 : Blo 2153435 3066493 := bbase (se 3 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 3066493 = 1149935) (by norm_num)
theorem B4088657 : Blo 2153435 4088657 := bstep (se 2 (by rfl) ⟨1533246, by rfl⟩ : syracuseStep 4088657 = 3066493) B3066493
theorem B10903085 : Blo 2153435 10903085 := bstep (se 3 (by rfl) ⟨2044328, by rfl⟩ : syracuseStep 10903085 = 4088657) B4088657
theorem B7268723 : Blo 2153435 7268723 := bstep (se 1 (by rfl) ⟨5451542, by rfl⟩ : syracuseStep 7268723 = 10903085) B10903085
theorem B4845815 : Blo 2153435 4845815 := bstep (se 1 (by rfl) ⟨3634361, by rfl⟩ : syracuseStep 4845815 = 7268723) B7268723
theorem B3230543 : Blo 2153435 3230543 := bstep (se 1 (by rfl) ⟨2422907, by rfl⟩ : syracuseStep 3230543 = 4845815) B4845815
theorem B2153695 : Blo 2153435 2153695 := bstep (se 1 (by rfl) ⟨1615271, by rfl⟩ : syracuseStep 2153695 = 3230543) B3230543
theorem B3230549 : Blo 2153435 3230549 := bbase (se 9 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 3230549 = 18929) (by norm_num)
theorem B2153699 : Blo 2153435 2153699 := bstep (se 1 (by rfl) ⟨1615274, by rfl⟩ : syracuseStep 2153699 = 3230549) B3230549
theorem B4599757 : Blo 2153435 4599757 := bbase (se 3 (by rfl) ⟨862454, by rfl⟩ : syracuseStep 4599757 = 1724909) (by norm_num)
theorem B6133009 : Blo 2153435 6133009 := bstep (se 2 (by rfl) ⟨2299878, by rfl⟩ : syracuseStep 6133009 = 4599757) B4599757
theorem B8177345 : Blo 2153435 8177345 := bstep (se 2 (by rfl) ⟨3066504, by rfl⟩ : syracuseStep 8177345 = 6133009) B6133009
theorem B5451563 : Blo 2153435 5451563 := bstep (se 1 (by rfl) ⟨4088672, by rfl⟩ : syracuseStep 5451563 = 8177345) B8177345
theorem B3634375 : Blo 2153435 3634375 := bstep (se 1 (by rfl) ⟨2725781, by rfl⟩ : syracuseStep 3634375 = 5451563) B5451563
theorem B4845833 : Blo 2153435 4845833 := bstep (se 2 (by rfl) ⟨1817187, by rfl⟩ : syracuseStep 4845833 = 3634375) B3634375
theorem B3230555 : Blo 2153435 3230555 := bstep (se 1 (by rfl) ⟨2422916, by rfl⟩ : syracuseStep 3230555 = 4845833) B4845833
theorem B2153703 : Blo 2153435 2153703 := bstep (se 1 (by rfl) ⟨1615277, by rfl⟩ : syracuseStep 2153703 = 3230555) B3230555
theorem B2422921 : Blo 2153435 2422921 := bbase (se 2 (by rfl) ⟨908595, by rfl⟩ : syracuseStep 2422921 = 1817191) (by norm_num)
theorem B3230561 : Blo 2153435 3230561 := bstep (se 2 (by rfl) ⟨1211460, by rfl⟩ : syracuseStep 3230561 = 2422921) B2422921
theorem B2153707 : Blo 2153435 2153707 := bstep (se 1 (by rfl) ⟨1615280, by rfl⟩ : syracuseStep 2153707 = 3230561) B3230561
theorem B5821589 : Blo 2153435 5821589 := bbase (se 6 (by rfl) ⟨136443, by rfl⟩ : syracuseStep 5821589 = 272887) (by norm_num)
theorem B15524237 : Blo 2153435 15524237 := bstep (se 3 (by rfl) ⟨2910794, by rfl⟩ : syracuseStep 15524237 = 5821589) B5821589
theorem B41397965 : Blo 2153435 41397965 := bstep (se 3 (by rfl) ⟨7762118, by rfl⟩ : syracuseStep 41397965 = 15524237) B15524237
theorem B27598643 : Blo 2153435 27598643 := bstep (se 1 (by rfl) ⟨20698982, by rfl⟩ : syracuseStep 27598643 = 41397965) B41397965
theorem B18399095 : Blo 2153435 18399095 := bstep (se 1 (by rfl) ⟨13799321, by rfl⟩ : syracuseStep 18399095 = 27598643) B27598643
theorem B12266063 : Blo 2153435 12266063 := bstep (se 1 (by rfl) ⟨9199547, by rfl⟩ : syracuseStep 12266063 = 18399095) B18399095
theorem B8177375 : Blo 2153435 8177375 := bstep (se 1 (by rfl) ⟨6133031, by rfl⟩ : syracuseStep 8177375 = 12266063) B12266063
theorem B5451583 : Blo 2153435 5451583 := bstep (se 1 (by rfl) ⟨4088687, by rfl⟩ : syracuseStep 5451583 = 8177375) B8177375
theorem B7268777 : Blo 2153435 7268777 := bstep (se 2 (by rfl) ⟨2725791, by rfl⟩ : syracuseStep 7268777 = 5451583) B5451583
theorem B4845851 : Blo 2153435 4845851 := bstep (se 1 (by rfl) ⟨3634388, by rfl⟩ : syracuseStep 4845851 = 7268777) B7268777
theorem B3230567 : Blo 2153435 3230567 := bstep (se 1 (by rfl) ⟨2422925, by rfl⟩ : syracuseStep 3230567 = 4845851) B4845851
theorem B2153711 : Blo 2153435 2153711 := bstep (se 1 (by rfl) ⟨1615283, by rfl⟩ : syracuseStep 2153711 = 3230567) B3230567
theorem B3230573 : Blo 2153435 3230573 := bbase (se 3 (by rfl) ⟨605732, by rfl⟩ : syracuseStep 3230573 = 1211465) (by norm_num)
theorem B2153715 : Blo 2153435 2153715 := bstep (se 1 (by rfl) ⟨1615286, by rfl⟩ : syracuseStep 2153715 = 3230573) B3230573
theorem B4845869 : Blo 2153435 4845869 := bbase (se 3 (by rfl) ⟨908600, by rfl⟩ : syracuseStep 4845869 = 1817201) (by norm_num)
theorem B3230579 : Blo 2153435 3230579 := bstep (se 1 (by rfl) ⟨2422934, by rfl⟩ : syracuseStep 3230579 = 4845869) B4845869
theorem B2153719 : Blo 2153435 2153719 := bstep (se 1 (by rfl) ⟨1615289, by rfl⟩ : syracuseStep 2153719 = 3230579) B3230579
theorem B6899701 : Blo 2153435 6899701 := bbase (se 5 (by rfl) ⟨323423, by rfl⟩ : syracuseStep 6899701 = 646847) (by norm_num)
theorem B9199601 : Blo 2153435 9199601 := bstep (se 2 (by rfl) ⟨3449850, by rfl⟩ : syracuseStep 9199601 = 6899701) B6899701
theorem B6133067 : Blo 2153435 6133067 := bstep (se 1 (by rfl) ⟨4599800, by rfl⟩ : syracuseStep 6133067 = 9199601) B9199601
theorem B4088711 : Blo 2153435 4088711 := bstep (se 1 (by rfl) ⟨3066533, by rfl⟩ : syracuseStep 4088711 = 6133067) B6133067
theorem B2725807 : Blo 2153435 2725807 := bstep (se 1 (by rfl) ⟨2044355, by rfl⟩ : syracuseStep 2725807 = 4088711) B4088711
theorem B3634409 : Blo 2153435 3634409 := bstep (se 2 (by rfl) ⟨1362903, by rfl⟩ : syracuseStep 3634409 = 2725807) B2725807
theorem B2422939 : Blo 2153435 2422939 := bstep (se 1 (by rfl) ⟨1817204, by rfl⟩ : syracuseStep 2422939 = 3634409) B3634409
theorem B3230585 : Blo 2153435 3230585 := bstep (se 2 (by rfl) ⟨1211469, by rfl⟩ : syracuseStep 3230585 = 2422939) B2422939
theorem B2153723 : Blo 2153435 2153723 := bstep (se 1 (by rfl) ⟨1615292, by rfl⟩ : syracuseStep 2153723 = 3230585) B3230585
theorem B2243089 : Blo 2153435 2243089 := bbase (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) (by norm_num)
theorem B2990785 : Blo 2153435 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B3987713 : Blo 2153435 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B2658475 : Blo 2153435 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B3544633 : Blo 2153435 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B18904709 : Blo 2153435 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B50412557 : Blo 2153435 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B33608371 : Blo 2153435 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B44811161 : Blo 2153435 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B29874107 : Blo 2153435 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B79664285 : Blo 2153435 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B53109523 : Blo 2153435 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B283250789 : Blo 2153435 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B188833859 : Blo 2153435 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B125889239 : Blo 2153435 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B335704637 : Blo 2153435 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B223803091 : Blo 2153435 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B1193616485 : Blo 2153435 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B795744323 : Blo 2153435 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B530496215 : Blo 2153435 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B353664143 : Blo 2153435 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B235776095 : Blo 2153435 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B157184063 : Blo 2153435 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B104789375 : Blo 2153435 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B69859583 : Blo 2153435 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B46573055 : Blo 2153435 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B31048703 : Blo 2153435 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B20699135 : Blo 2153435 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B13799423 : Blo 2153435 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B36798461 : Blo 2153435 36798461 := bstep (se 3 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 36798461 = 13799423) B13799423
theorem B24532307 : Blo 2153435 24532307 := bstep (se 1 (by rfl) ⟨18399230, by rfl⟩ : syracuseStep 24532307 = 36798461) B36798461
theorem B16354871 : Blo 2153435 16354871 := bstep (se 1 (by rfl) ⟨12266153, by rfl⟩ : syracuseStep 16354871 = 24532307) B24532307
theorem B10903247 : Blo 2153435 10903247 := bstep (se 1 (by rfl) ⟨8177435, by rfl⟩ : syracuseStep 10903247 = 16354871) B16354871
theorem B7268831 : Blo 2153435 7268831 := bstep (se 1 (by rfl) ⟨5451623, by rfl⟩ : syracuseStep 7268831 = 10903247) B10903247
theorem B4845887 : Blo 2153435 4845887 := bstep (se 1 (by rfl) ⟨3634415, by rfl⟩ : syracuseStep 4845887 = 7268831) B7268831
theorem B3230591 : Blo 2153435 3230591 := bstep (se 1 (by rfl) ⟨2422943, by rfl⟩ : syracuseStep 3230591 = 4845887) B4845887
theorem B2153727 : Blo 2153435 2153727 := bstep (se 1 (by rfl) ⟨1615295, by rfl⟩ : syracuseStep 2153727 = 3230591) B3230591
theorem B3230597 : Blo 2153435 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B2153731 : Blo 2153435 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B3634429 : Blo 2153435 3634429 := bbase (se 3 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 3634429 = 1362911) (by norm_num)
theorem B4845905 : Blo 2153435 4845905 := bstep (se 2 (by rfl) ⟨1817214, by rfl⟩ : syracuseStep 4845905 = 3634429) B3634429
theorem B3230603 : Blo 2153435 3230603 := bstep (se 1 (by rfl) ⟨2422952, by rfl⟩ : syracuseStep 3230603 = 4845905) B4845905
theorem B2153735 : Blo 2153435 2153735 := bstep (se 1 (by rfl) ⟨1615301, by rfl⟩ : syracuseStep 2153735 = 3230603) B3230603
theorem B2422957 : Blo 2153435 2422957 := bbase (se 3 (by rfl) ⟨454304, by rfl⟩ : syracuseStep 2422957 = 908609) (by norm_num)
theorem B3230609 : Blo 2153435 3230609 := bstep (se 2 (by rfl) ⟨1211478, by rfl⟩ : syracuseStep 3230609 = 2422957) B2422957
theorem B2153739 : Blo 2153435 2153739 := bstep (se 1 (by rfl) ⟨1615304, by rfl⟩ : syracuseStep 2153739 = 3230609) B3230609
theorem B7268885 : Blo 2153435 7268885 := bbase (se 6 (by rfl) ⟨170364, by rfl⟩ : syracuseStep 7268885 = 340729) (by norm_num)
theorem B4845923 : Blo 2153435 4845923 := bstep (se 1 (by rfl) ⟨3634442, by rfl⟩ : syracuseStep 4845923 = 7268885) B7268885
theorem B3230615 : Blo 2153435 3230615 := bstep (se 1 (by rfl) ⟨2422961, by rfl⟩ : syracuseStep 3230615 = 4845923) B4845923
theorem B2153743 : Blo 2153435 2153743 := bstep (se 1 (by rfl) ⟨1615307, by rfl⟩ : syracuseStep 2153743 = 3230615) B3230615
theorem B3230621 : Blo 2153435 3230621 := bbase (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) (by norm_num)
theorem B2153747 : Blo 2153435 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B4845941 : Blo 2153435 4845941 := bbase (se 5 (by rfl) ⟨227153, by rfl⟩ : syracuseStep 4845941 = 454307) (by norm_num)
theorem B3230627 : Blo 2153435 3230627 := bstep (se 1 (by rfl) ⟨2422970, by rfl⟩ : syracuseStep 3230627 = 4845941) B4845941
theorem B2153751 : Blo 2153435 2153751 := bstep (se 1 (by rfl) ⟨1615313, by rfl⟩ : syracuseStep 2153751 = 3230627) B3230627
theorem B13799605 : Blo 2153435 13799605 := bbase (se 5 (by rfl) ⟨646856, by rfl⟩ : syracuseStep 13799605 = 1293713) (by norm_num)
theorem B18399473 : Blo 2153435 18399473 := bstep (se 2 (by rfl) ⟨6899802, by rfl⟩ : syracuseStep 18399473 = 13799605) B13799605
theorem B12266315 : Blo 2153435 12266315 := bstep (se 1 (by rfl) ⟨9199736, by rfl⟩ : syracuseStep 12266315 = 18399473) B18399473
theorem B8177543 : Blo 2153435 8177543 := bstep (se 1 (by rfl) ⟨6133157, by rfl⟩ : syracuseStep 8177543 = 12266315) B12266315
theorem B5451695 : Blo 2153435 5451695 := bstep (se 1 (by rfl) ⟨4088771, by rfl⟩ : syracuseStep 5451695 = 8177543) B8177543
theorem B3634463 : Blo 2153435 3634463 := bstep (se 1 (by rfl) ⟨2725847, by rfl⟩ : syracuseStep 3634463 = 5451695) B5451695
theorem B2422975 : Blo 2153435 2422975 := bstep (se 1 (by rfl) ⟨1817231, by rfl⟩ : syracuseStep 2422975 = 3634463) B3634463
theorem B3230633 : Blo 2153435 3230633 := bstep (se 2 (by rfl) ⟨1211487, by rfl⟩ : syracuseStep 3230633 = 2422975) B2422975
theorem B2153755 : Blo 2153435 2153755 := bstep (se 1 (by rfl) ⟨1615316, by rfl⟩ : syracuseStep 2153755 = 3230633) B3230633
theorem B8177557 : Blo 2153435 8177557 := bbase (se 6 (by rfl) ⟨191661, by rfl⟩ : syracuseStep 8177557 = 383323) (by norm_num)
theorem B10903409 : Blo 2153435 10903409 := bstep (se 2 (by rfl) ⟨4088778, by rfl⟩ : syracuseStep 10903409 = 8177557) B8177557
theorem B7268939 : Blo 2153435 7268939 := bstep (se 1 (by rfl) ⟨5451704, by rfl⟩ : syracuseStep 7268939 = 10903409) B10903409
theorem B4845959 : Blo 2153435 4845959 := bstep (se 1 (by rfl) ⟨3634469, by rfl⟩ : syracuseStep 4845959 = 7268939) B7268939
theorem B3230639 : Blo 2153435 3230639 := bstep (se 1 (by rfl) ⟨2422979, by rfl⟩ : syracuseStep 3230639 = 4845959) B4845959
theorem B2153759 : Blo 2153435 2153759 := bstep (se 1 (by rfl) ⟨1615319, by rfl⟩ : syracuseStep 2153759 = 3230639) B3230639
theorem B3230645 : Blo 2153435 3230645 := bbase (se 5 (by rfl) ⟨151436, by rfl⟩ : syracuseStep 3230645 = 302873) (by norm_num)
theorem B2153763 : Blo 2153435 2153763 := bstep (se 1 (by rfl) ⟨1615322, by rfl⟩ : syracuseStep 2153763 = 3230645) B3230645
theorem B5451725 : Blo 2153435 5451725 := bbase (se 3 (by rfl) ⟨1022198, by rfl⟩ : syracuseStep 5451725 = 2044397) (by norm_num)
theorem B3634483 : Blo 2153435 3634483 := bstep (se 1 (by rfl) ⟨2725862, by rfl⟩ : syracuseStep 3634483 = 5451725) B5451725
theorem B4845977 : Blo 2153435 4845977 := bstep (se 2 (by rfl) ⟨1817241, by rfl⟩ : syracuseStep 4845977 = 3634483) B3634483
theorem B3230651 : Blo 2153435 3230651 := bstep (se 1 (by rfl) ⟨2422988, by rfl⟩ : syracuseStep 3230651 = 4845977) B4845977
theorem B2153767 : Blo 2153435 2153767 := bstep (se 1 (by rfl) ⟨1615325, by rfl⟩ : syracuseStep 2153767 = 3230651) B3230651
theorem B2422993 : Blo 2153435 2422993 := bbase (se 2 (by rfl) ⟨908622, by rfl⟩ : syracuseStep 2422993 = 1817245) (by norm_num)
theorem B3230657 : Blo 2153435 3230657 := bstep (se 2 (by rfl) ⟨1211496, by rfl⟩ : syracuseStep 3230657 = 2422993) B2422993
theorem B2153771 : Blo 2153435 2153771 := bstep (se 1 (by rfl) ⟨1615328, by rfl⟩ : syracuseStep 2153771 = 3230657) B3230657
theorem B3684085 : Blo 2153435 3684085 := bbase (se 5 (by rfl) ⟨172691, by rfl⟩ : syracuseStep 3684085 = 345383) (by norm_num)
theorem B19648453 : Blo 2153435 19648453 := bstep (se 4 (by rfl) ⟨1842042, by rfl⟩ : syracuseStep 19648453 = 3684085) B3684085
theorem B26197937 : Blo 2153435 26197937 := bstep (se 2 (by rfl) ⟨9824226, by rfl⟩ : syracuseStep 26197937 = 19648453) B19648453
theorem B17465291 : Blo 2153435 17465291 := bstep (se 1 (by rfl) ⟨13098968, by rfl⟩ : syracuseStep 17465291 = 26197937) B26197937
theorem B11643527 : Blo 2153435 11643527 := bstep (se 1 (by rfl) ⟨8732645, by rfl⟩ : syracuseStep 11643527 = 17465291) B17465291
theorem B7762351 : Blo 2153435 7762351 := bstep (se 1 (by rfl) ⟨5821763, by rfl⟩ : syracuseStep 7762351 = 11643527) B11643527
theorem B10349801 : Blo 2153435 10349801 := bstep (se 2 (by rfl) ⟨3881175, by rfl⟩ : syracuseStep 10349801 = 7762351) B7762351
theorem B6899867 : Blo 2153435 6899867 := bstep (se 1 (by rfl) ⟨5174900, by rfl⟩ : syracuseStep 6899867 = 10349801) B10349801
theorem B4599911 : Blo 2153435 4599911 := bstep (se 1 (by rfl) ⟨3449933, by rfl⟩ : syracuseStep 4599911 = 6899867) B6899867
theorem B3066607 : Blo 2153435 3066607 := bstep (se 1 (by rfl) ⟨2299955, by rfl⟩ : syracuseStep 3066607 = 4599911) B4599911
theorem B4088809 : Blo 2153435 4088809 := bstep (se 2 (by rfl) ⟨1533303, by rfl⟩ : syracuseStep 4088809 = 3066607) B3066607
theorem B5451745 : Blo 2153435 5451745 := bstep (se 2 (by rfl) ⟨2044404, by rfl⟩ : syracuseStep 5451745 = 4088809) B4088809
theorem B7268993 : Blo 2153435 7268993 := bstep (se 2 (by rfl) ⟨2725872, by rfl⟩ : syracuseStep 7268993 = 5451745) B5451745
theorem B4845995 : Blo 2153435 4845995 := bstep (se 1 (by rfl) ⟨3634496, by rfl⟩ : syracuseStep 4845995 = 7268993) B7268993
theorem B3230663 : Blo 2153435 3230663 := bstep (se 1 (by rfl) ⟨2422997, by rfl⟩ : syracuseStep 3230663 = 4845995) B4845995
theorem B2153775 : Blo 2153435 2153775 := bstep (se 1 (by rfl) ⟨1615331, by rfl⟩ : syracuseStep 2153775 = 3230663) B3230663
theorem B3230669 : Blo 2153435 3230669 := bbase (se 3 (by rfl) ⟨605750, by rfl⟩ : syracuseStep 3230669 = 1211501) (by norm_num)
theorem B2153779 : Blo 2153435 2153779 := bstep (se 1 (by rfl) ⟨1615334, by rfl⟩ : syracuseStep 2153779 = 3230669) B3230669
theorem B4846013 : Blo 2153435 4846013 := bbase (se 3 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 4846013 = 1817255) (by norm_num)
theorem B3230675 : Blo 2153435 3230675 := bstep (se 1 (by rfl) ⟨2423006, by rfl⟩ : syracuseStep 3230675 = 4846013) B4846013
theorem B2153783 : Blo 2153435 2153783 := bstep (se 1 (by rfl) ⟨1615337, by rfl⟩ : syracuseStep 2153783 = 3230675) B3230675
theorem B3634517 : Blo 2153435 3634517 := bbase (se 13 (by rfl) ⟨665, by rfl⟩ : syracuseStep 3634517 = 1331) (by norm_num)
theorem B2423011 : Blo 2153435 2423011 := bstep (se 1 (by rfl) ⟨1817258, by rfl⟩ : syracuseStep 2423011 = 3634517) B3634517
theorem B3230681 : Blo 2153435 3230681 := bstep (se 2 (by rfl) ⟨1211505, by rfl⟩ : syracuseStep 3230681 = 2423011) B2423011
theorem B2153787 : Blo 2153435 2153787 := bstep (se 1 (by rfl) ⟨1615340, by rfl⟩ : syracuseStep 2153787 = 3230681) B3230681
theorem B2587469 : Blo 2153435 2587469 := bbase (se 3 (by rfl) ⟨485150, by rfl⟩ : syracuseStep 2587469 = 970301) (by norm_num)
theorem B6899917 : Blo 2153435 6899917 := bstep (se 3 (by rfl) ⟨1293734, by rfl⟩ : syracuseStep 6899917 = 2587469) B2587469
theorem B9199889 : Blo 2153435 9199889 := bstep (se 2 (by rfl) ⟨3449958, by rfl⟩ : syracuseStep 9199889 = 6899917) B6899917
theorem B6133259 : Blo 2153435 6133259 := bstep (se 1 (by rfl) ⟨4599944, by rfl⟩ : syracuseStep 6133259 = 9199889) B9199889
theorem B16355357 : Blo 2153435 16355357 := bstep (se 3 (by rfl) ⟨3066629, by rfl⟩ : syracuseStep 16355357 = 6133259) B6133259
theorem B10903571 : Blo 2153435 10903571 := bstep (se 1 (by rfl) ⟨8177678, by rfl⟩ : syracuseStep 10903571 = 16355357) B16355357
theorem B7269047 : Blo 2153435 7269047 := bstep (se 1 (by rfl) ⟨5451785, by rfl⟩ : syracuseStep 7269047 = 10903571) B10903571
theorem B4846031 : Blo 2153435 4846031 := bstep (se 1 (by rfl) ⟨3634523, by rfl⟩ : syracuseStep 4846031 = 7269047) B7269047
theorem B3230687 : Blo 2153435 3230687 := bstep (se 1 (by rfl) ⟨2423015, by rfl⟩ : syracuseStep 3230687 = 4846031) B4846031
theorem B2153791 : Blo 2153435 2153791 := bstep (se 1 (by rfl) ⟨1615343, by rfl⟩ : syracuseStep 2153791 = 3230687) B3230687
theorem B3230693 : Blo 2153435 3230693 := bbase (se 4 (by rfl) ⟨302877, by rfl⟩ : syracuseStep 3230693 = 605755) (by norm_num)
theorem B2153795 : Blo 2153435 2153795 := bstep (se 1 (by rfl) ⟨1615346, by rfl⟩ : syracuseStep 2153795 = 3230693) B3230693
theorem B9199925 : Blo 2153435 9199925 := bbase (se 5 (by rfl) ⟨431246, by rfl⟩ : syracuseStep 9199925 = 862493) (by norm_num)
theorem B6133283 : Blo 2153435 6133283 := bstep (se 1 (by rfl) ⟨4599962, by rfl⟩ : syracuseStep 6133283 = 9199925) B9199925
theorem B4088855 : Blo 2153435 4088855 := bstep (se 1 (by rfl) ⟨3066641, by rfl⟩ : syracuseStep 4088855 = 6133283) B6133283
theorem B2725903 : Blo 2153435 2725903 := bstep (se 1 (by rfl) ⟨2044427, by rfl⟩ : syracuseStep 2725903 = 4088855) B4088855
theorem B3634537 : Blo 2153435 3634537 := bstep (se 2 (by rfl) ⟨1362951, by rfl⟩ : syracuseStep 3634537 = 2725903) B2725903
theorem B4846049 : Blo 2153435 4846049 := bstep (se 2 (by rfl) ⟨1817268, by rfl⟩ : syracuseStep 4846049 = 3634537) B3634537
theorem B3230699 : Blo 2153435 3230699 := bstep (se 1 (by rfl) ⟨2423024, by rfl⟩ : syracuseStep 3230699 = 4846049) B4846049
theorem B2153799 : Blo 2153435 2153799 := bstep (se 1 (by rfl) ⟨1615349, by rfl⟩ : syracuseStep 2153799 = 3230699) B3230699
theorem B2423029 : Blo 2153435 2423029 := bbase (se 5 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 2423029 = 227159) (by norm_num)
theorem B3230705 : Blo 2153435 3230705 := bstep (se 2 (by rfl) ⟨1211514, by rfl⟩ : syracuseStep 3230705 = 2423029) B2423029
theorem B2153803 : Blo 2153435 2153803 := bstep (se 1 (by rfl) ⟨1615352, by rfl⟩ : syracuseStep 2153803 = 3230705) B3230705
theorem B2725913 : Blo 2153435 2725913 := bbase (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) (by norm_num)
theorem B7269101 : Blo 2153435 7269101 := bstep (se 3 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 7269101 = 2725913) B2725913
theorem B4846067 : Blo 2153435 4846067 := bstep (se 1 (by rfl) ⟨3634550, by rfl⟩ : syracuseStep 4846067 = 7269101) B7269101
theorem B3230711 : Blo 2153435 3230711 := bstep (se 1 (by rfl) ⟨2423033, by rfl⟩ : syracuseStep 3230711 = 4846067) B4846067
theorem B2153807 : Blo 2153435 2153807 := bstep (se 1 (by rfl) ⟨1615355, by rfl⟩ : syracuseStep 2153807 = 3230711) B3230711
theorem B3230717 : Blo 2153435 3230717 := bbase (se 3 (by rfl) ⟨605759, by rfl⟩ : syracuseStep 3230717 = 1211519) (by norm_num)
theorem B2153811 : Blo 2153435 2153811 := bstep (se 1 (by rfl) ⟨1615358, by rfl⟩ : syracuseStep 2153811 = 3230717) B3230717
theorem B4846085 : Blo 2153435 4846085 := bbase (se 4 (by rfl) ⟨454320, by rfl⟩ : syracuseStep 4846085 = 908641) (by norm_num)
theorem B3230723 : Blo 2153435 3230723 := bstep (se 1 (by rfl) ⟨2423042, by rfl⟩ : syracuseStep 3230723 = 4846085) B4846085
theorem B2153815 : Blo 2153435 2153815 := bstep (se 1 (by rfl) ⟨1615361, by rfl⟩ : syracuseStep 2153815 = 3230723) B3230723
theorem B4088893 : Blo 2153435 4088893 := bbase (se 3 (by rfl) ⟨766667, by rfl⟩ : syracuseStep 4088893 = 1533335) (by norm_num)
theorem B5451857 : Blo 2153435 5451857 := bstep (se 2 (by rfl) ⟨2044446, by rfl⟩ : syracuseStep 5451857 = 4088893) B4088893
theorem B3634571 : Blo 2153435 3634571 := bstep (se 1 (by rfl) ⟨2725928, by rfl⟩ : syracuseStep 3634571 = 5451857) B5451857
theorem B2423047 : Blo 2153435 2423047 := bstep (se 1 (by rfl) ⟨1817285, by rfl⟩ : syracuseStep 2423047 = 3634571) B3634571
theorem B3230729 : Blo 2153435 3230729 := bstep (se 2 (by rfl) ⟨1211523, by rfl⟩ : syracuseStep 3230729 = 2423047) B2423047
theorem B2153819 : Blo 2153435 2153819 := bstep (se 1 (by rfl) ⟨1615364, by rfl⟩ : syracuseStep 2153819 = 3230729) B3230729
theorem B10903733 : Blo 2153435 10903733 := bbase (se 5 (by rfl) ⟨511112, by rfl⟩ : syracuseStep 10903733 = 1022225) (by norm_num)
theorem B7269155 : Blo 2153435 7269155 := bstep (se 1 (by rfl) ⟨5451866, by rfl⟩ : syracuseStep 7269155 = 10903733) B10903733
theorem B4846103 : Blo 2153435 4846103 := bstep (se 1 (by rfl) ⟨3634577, by rfl⟩ : syracuseStep 4846103 = 7269155) B7269155
theorem B3230735 : Blo 2153435 3230735 := bstep (se 1 (by rfl) ⟨2423051, by rfl⟩ : syracuseStep 3230735 = 4846103) B4846103
theorem B2153823 : Blo 2153435 2153823 := bstep (se 1 (by rfl) ⟨1615367, by rfl⟩ : syracuseStep 2153823 = 3230735) B3230735
theorem B3230741 : Blo 2153435 3230741 := bbase (se 6 (by rfl) ⟨75720, by rfl⟩ : syracuseStep 3230741 = 151441) (by norm_num)
theorem B2153827 : Blo 2153435 2153827 := bstep (se 1 (by rfl) ⟨1615370, by rfl⟩ : syracuseStep 2153827 = 3230741) B3230741
theorem B251790677 : Blo 2153435 251790677 := bbase (se 12 (by rfl) ⟨92208, by rfl⟩ : syracuseStep 251790677 = 184417) (by norm_num)
theorem B167860451 : Blo 2153435 167860451 := bstep (se 1 (by rfl) ⟨125895338, by rfl⟩ : syracuseStep 167860451 = 251790677) B251790677
theorem B447627869 : Blo 2153435 447627869 := bstep (se 3 (by rfl) ⟨83930225, by rfl⟩ : syracuseStep 447627869 = 167860451) B167860451
theorem B298418579 : Blo 2153435 298418579 := bstep (se 1 (by rfl) ⟨223813934, by rfl⟩ : syracuseStep 298418579 = 447627869) B447627869
theorem B198945719 : Blo 2153435 198945719 := bstep (se 1 (by rfl) ⟨149209289, by rfl⟩ : syracuseStep 198945719 = 298418579) B298418579
theorem B132630479 : Blo 2153435 132630479 := bstep (se 1 (by rfl) ⟨99472859, by rfl⟩ : syracuseStep 132630479 = 198945719) B198945719
theorem B88420319 : Blo 2153435 88420319 := bstep (se 1 (by rfl) ⟨66315239, by rfl⟩ : syracuseStep 88420319 = 132630479) B132630479
theorem B58946879 : Blo 2153435 58946879 := bstep (se 1 (by rfl) ⟨44210159, by rfl⟩ : syracuseStep 58946879 = 88420319) B88420319
theorem B39297919 : Blo 2153435 39297919 := bstep (se 1 (by rfl) ⟨29473439, by rfl⟩ : syracuseStep 39297919 = 58946879) B58946879
theorem B52397225 : Blo 2153435 52397225 := bstep (se 2 (by rfl) ⟨19648959, by rfl⟩ : syracuseStep 52397225 = 39297919) B39297919
theorem B34931483 : Blo 2153435 34931483 := bstep (se 1 (by rfl) ⟨26198612, by rfl⟩ : syracuseStep 34931483 = 52397225) B52397225
theorem B23287655 : Blo 2153435 23287655 := bstep (se 1 (by rfl) ⟨17465741, by rfl⟩ : syracuseStep 23287655 = 34931483) B34931483
theorem B15525103 : Blo 2153435 15525103 := bstep (se 1 (by rfl) ⟨11643827, by rfl⟩ : syracuseStep 15525103 = 23287655) B23287655
theorem B20700137 : Blo 2153435 20700137 := bstep (se 2 (by rfl) ⟨7762551, by rfl⟩ : syracuseStep 20700137 = 15525103) B15525103
theorem B13800091 : Blo 2153435 13800091 := bstep (se 1 (by rfl) ⟨10350068, by rfl⟩ : syracuseStep 13800091 = 20700137) B20700137
theorem B18400121 : Blo 2153435 18400121 := bstep (se 2 (by rfl) ⟨6900045, by rfl⟩ : syracuseStep 18400121 = 13800091) B13800091
theorem B12266747 : Blo 2153435 12266747 := bstep (se 1 (by rfl) ⟨9200060, by rfl⟩ : syracuseStep 12266747 = 18400121) B18400121
theorem B8177831 : Blo 2153435 8177831 := bstep (se 1 (by rfl) ⟨6133373, by rfl⟩ : syracuseStep 8177831 = 12266747) B12266747
theorem B5451887 : Blo 2153435 5451887 := bstep (se 1 (by rfl) ⟨4088915, by rfl⟩ : syracuseStep 5451887 = 8177831) B8177831
theorem B3634591 : Blo 2153435 3634591 := bstep (se 1 (by rfl) ⟨2725943, by rfl⟩ : syracuseStep 3634591 = 5451887) B5451887
theorem B4846121 : Blo 2153435 4846121 := bstep (se 2 (by rfl) ⟨1817295, by rfl⟩ : syracuseStep 4846121 = 3634591) B3634591
theorem B3230747 : Blo 2153435 3230747 := bstep (se 1 (by rfl) ⟨2423060, by rfl⟩ : syracuseStep 3230747 = 4846121) B4846121
theorem B2153831 : Blo 2153435 2153831 := bstep (se 1 (by rfl) ⟨1615373, by rfl⟩ : syracuseStep 2153831 = 3230747) B3230747
theorem B2423065 : Blo 2153435 2423065 := bbase (se 2 (by rfl) ⟨908649, by rfl⟩ : syracuseStep 2423065 = 1817299) (by norm_num)
theorem B3230753 : Blo 2153435 3230753 := bstep (se 2 (by rfl) ⟨1211532, by rfl⟩ : syracuseStep 3230753 = 2423065) B2423065
theorem B2153835 : Blo 2153435 2153835 := bstep (se 1 (by rfl) ⟨1615376, by rfl⟩ : syracuseStep 2153835 = 3230753) B3230753
theorem B8177861 : Blo 2153435 8177861 := bbase (se 4 (by rfl) ⟨766674, by rfl⟩ : syracuseStep 8177861 = 1533349) (by norm_num)
theorem B5451907 : Blo 2153435 5451907 := bstep (se 1 (by rfl) ⟨4088930, by rfl⟩ : syracuseStep 5451907 = 8177861) B8177861
theorem B7269209 : Blo 2153435 7269209 := bstep (se 2 (by rfl) ⟨2725953, by rfl⟩ : syracuseStep 7269209 = 5451907) B5451907
theorem B4846139 : Blo 2153435 4846139 := bstep (se 1 (by rfl) ⟨3634604, by rfl⟩ : syracuseStep 4846139 = 7269209) B7269209
theorem B3230759 : Blo 2153435 3230759 := bstep (se 1 (by rfl) ⟨2423069, by rfl⟩ : syracuseStep 3230759 = 4846139) B4846139
theorem B2153839 : Blo 2153435 2153839 := bstep (se 1 (by rfl) ⟨1615379, by rfl⟩ : syracuseStep 2153839 = 3230759) B3230759
theorem B3230765 : Blo 2153435 3230765 := bbase (se 3 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 3230765 = 1211537) (by norm_num)
theorem B2153843 : Blo 2153435 2153843 := bstep (se 1 (by rfl) ⟨1615382, by rfl⟩ : syracuseStep 2153843 = 3230765) B3230765
theorem B4846157 : Blo 2153435 4846157 := bbase (se 3 (by rfl) ⟨908654, by rfl⟩ : syracuseStep 4846157 = 1817309) (by norm_num)
theorem B3230771 : Blo 2153435 3230771 := bstep (se 1 (by rfl) ⟨2423078, by rfl⟩ : syracuseStep 3230771 = 4846157) B4846157
theorem B2153847 : Blo 2153435 2153847 := bstep (se 1 (by rfl) ⟨1615385, by rfl⟩ : syracuseStep 2153847 = 3230771) B3230771
theorem B2725969 : Blo 2153435 2725969 := bbase (se 2 (by rfl) ⟨1022238, by rfl⟩ : syracuseStep 2725969 = 2044477) (by norm_num)
theorem B3634625 : Blo 2153435 3634625 := bstep (se 2 (by rfl) ⟨1362984, by rfl⟩ : syracuseStep 3634625 = 2725969) B2725969
theorem B2423083 : Blo 2153435 2423083 := bstep (se 1 (by rfl) ⟨1817312, by rfl⟩ : syracuseStep 2423083 = 3634625) B3634625
theorem B3230777 : Blo 2153435 3230777 := bstep (se 2 (by rfl) ⟨1211541, by rfl⟩ : syracuseStep 3230777 = 2423083) B2423083
theorem B2153851 : Blo 2153435 2153851 := bstep (se 1 (by rfl) ⟨1615388, by rfl⟩ : syracuseStep 2153851 = 3230777) B3230777
theorem B3450061 : Blo 2153435 3450061 := bbase (se 3 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 3450061 = 1293773) (by norm_num)
theorem B4600081 : Blo 2153435 4600081 := bstep (se 2 (by rfl) ⟨1725030, by rfl⟩ : syracuseStep 4600081 = 3450061) B3450061
theorem B24533765 : Blo 2153435 24533765 := bstep (se 4 (by rfl) ⟨2300040, by rfl⟩ : syracuseStep 24533765 = 4600081) B4600081
theorem B16355843 : Blo 2153435 16355843 := bstep (se 1 (by rfl) ⟨12266882, by rfl⟩ : syracuseStep 16355843 = 24533765) B24533765
theorem B10903895 : Blo 2153435 10903895 := bstep (se 1 (by rfl) ⟨8177921, by rfl⟩ : syracuseStep 10903895 = 16355843) B16355843
theorem B7269263 : Blo 2153435 7269263 := bstep (se 1 (by rfl) ⟨5451947, by rfl⟩ : syracuseStep 7269263 = 10903895) B10903895
theorem B4846175 : Blo 2153435 4846175 := bstep (se 1 (by rfl) ⟨3634631, by rfl⟩ : syracuseStep 4846175 = 7269263) B7269263
theorem B3230783 : Blo 2153435 3230783 := bstep (se 1 (by rfl) ⟨2423087, by rfl⟩ : syracuseStep 3230783 = 4846175) B4846175
theorem B2153855 : Blo 2153435 2153855 := bstep (se 1 (by rfl) ⟨1615391, by rfl⟩ : syracuseStep 2153855 = 3230783) B3230783
theorem B3230789 : Blo 2153435 3230789 := bbase (se 4 (by rfl) ⟨302886, by rfl⟩ : syracuseStep 3230789 = 605773) (by norm_num)
theorem B2153859 : Blo 2153435 2153859 := bstep (se 1 (by rfl) ⟨1615394, by rfl⟩ : syracuseStep 2153859 = 3230789) B3230789
theorem B3634645 : Blo 2153435 3634645 := bbase (se 7 (by rfl) ⟨42593, by rfl⟩ : syracuseStep 3634645 = 85187) (by norm_num)
theorem B4846193 : Blo 2153435 4846193 := bstep (se 2 (by rfl) ⟨1817322, by rfl⟩ : syracuseStep 4846193 = 3634645) B3634645
theorem B3230795 : Blo 2153435 3230795 := bstep (se 1 (by rfl) ⟨2423096, by rfl⟩ : syracuseStep 3230795 = 4846193) B4846193
theorem B2153863 : Blo 2153435 2153863 := bstep (se 1 (by rfl) ⟨1615397, by rfl⟩ : syracuseStep 2153863 = 3230795) B3230795
theorem B2423101 : Blo 2153435 2423101 := bbase (se 3 (by rfl) ⟨454331, by rfl⟩ : syracuseStep 2423101 = 908663) (by norm_num)
theorem B3230801 : Blo 2153435 3230801 := bstep (se 2 (by rfl) ⟨1211550, by rfl⟩ : syracuseStep 3230801 = 2423101) B2423101
theorem B2153867 : Blo 2153435 2153867 := bstep (se 1 (by rfl) ⟨1615400, by rfl⟩ : syracuseStep 2153867 = 3230801) B3230801
theorem B7269317 : Blo 2153435 7269317 := bbase (se 4 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 7269317 = 1362997) (by norm_num)
theorem B4846211 : Blo 2153435 4846211 := bstep (se 1 (by rfl) ⟨3634658, by rfl⟩ : syracuseStep 4846211 = 7269317) B7269317
theorem B3230807 : Blo 2153435 3230807 := bstep (se 1 (by rfl) ⟨2423105, by rfl⟩ : syracuseStep 3230807 = 4846211) B4846211
theorem B2153871 : Blo 2153435 2153871 := bstep (se 1 (by rfl) ⟨1615403, by rfl⟩ : syracuseStep 2153871 = 3230807) B3230807
theorem B3230813 : Blo 2153435 3230813 := bbase (se 3 (by rfl) ⟨605777, by rfl⟩ : syracuseStep 3230813 = 1211555) (by norm_num)
theorem B2153875 : Blo 2153435 2153875 := bstep (se 1 (by rfl) ⟨1615406, by rfl⟩ : syracuseStep 2153875 = 3230813) B3230813
theorem B4846229 : Blo 2153435 4846229 := bbase (se 6 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 4846229 = 227167) (by norm_num)
theorem B3230819 : Blo 2153435 3230819 := bstep (se 1 (by rfl) ⟨2423114, by rfl⟩ : syracuseStep 3230819 = 4846229) B4846229
theorem B2153879 : Blo 2153435 2153879 := bstep (se 1 (by rfl) ⟨1615409, by rfl⟩ : syracuseStep 2153879 = 3230819) B3230819
theorem B9325813 : Blo 2153435 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B12434417 : Blo 2153435 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B8289611 : Blo 2153435 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B5526407 : Blo 2153435 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B14737085 : Blo 2153435 14737085 := bstep (se 3 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 14737085 = 5526407) B5526407
theorem B9824723 : Blo 2153435 9824723 := bstep (se 1 (by rfl) ⟨7368542, by rfl⟩ : syracuseStep 9824723 = 14737085) B14737085
theorem B6549815 : Blo 2153435 6549815 := bstep (se 1 (by rfl) ⟨4912361, by rfl⟩ : syracuseStep 6549815 = 9824723) B9824723
theorem B4366543 : Blo 2153435 4366543 := bstep (se 1 (by rfl) ⟨3274907, by rfl⟩ : syracuseStep 4366543 = 6549815) B6549815
theorem B5822057 : Blo 2153435 5822057 := bstep (se 2 (by rfl) ⟨2183271, by rfl⟩ : syracuseStep 5822057 = 4366543) B4366543
theorem B3881371 : Blo 2153435 3881371 := bstep (se 1 (by rfl) ⟨2911028, by rfl⟩ : syracuseStep 3881371 = 5822057) B5822057
theorem B5175161 : Blo 2153435 5175161 := bstep (se 2 (by rfl) ⟨1940685, by rfl⟩ : syracuseStep 5175161 = 3881371) B3881371
theorem B3450107 : Blo 2153435 3450107 := bstep (se 1 (by rfl) ⟨2587580, by rfl⟩ : syracuseStep 3450107 = 5175161) B5175161
theorem B2300071 : Blo 2153435 2300071 := bstep (se 1 (by rfl) ⟨1725053, by rfl⟩ : syracuseStep 2300071 = 3450107) B3450107
theorem B3066761 : Blo 2153435 3066761 := bstep (se 2 (by rfl) ⟨1150035, by rfl⟩ : syracuseStep 3066761 = 2300071) B2300071
theorem B8178029 : Blo 2153435 8178029 := bstep (se 3 (by rfl) ⟨1533380, by rfl⟩ : syracuseStep 8178029 = 3066761) B3066761
theorem B5452019 : Blo 2153435 5452019 := bstep (se 1 (by rfl) ⟨4089014, by rfl⟩ : syracuseStep 5452019 = 8178029) B8178029
theorem B3634679 : Blo 2153435 3634679 := bstep (se 1 (by rfl) ⟨2726009, by rfl⟩ : syracuseStep 3634679 = 5452019) B5452019
theorem B2423119 : Blo 2153435 2423119 := bstep (se 1 (by rfl) ⟨1817339, by rfl⟩ : syracuseStep 2423119 = 3634679) B3634679
theorem B3230825 : Blo 2153435 3230825 := bstep (se 2 (by rfl) ⟨1211559, by rfl⟩ : syracuseStep 3230825 = 2423119) B2423119
theorem B2153883 : Blo 2153435 2153883 := bstep (se 1 (by rfl) ⟨1615412, by rfl⟩ : syracuseStep 2153883 = 3230825) B3230825
theorem B4366549 : Blo 2153435 4366549 := bbase (se 7 (by rfl) ⟨51170, by rfl⟩ : syracuseStep 4366549 = 102341) (by norm_num)
theorem B5822065 : Blo 2153435 5822065 := bstep (se 2 (by rfl) ⟨2183274, by rfl⟩ : syracuseStep 5822065 = 4366549) B4366549
theorem B7762753 : Blo 2153435 7762753 := bstep (se 2 (by rfl) ⟨2911032, by rfl⟩ : syracuseStep 7762753 = 5822065) B5822065
theorem B10350337 : Blo 2153435 10350337 := bstep (se 2 (by rfl) ⟨3881376, by rfl⟩ : syracuseStep 10350337 = 7762753) B7762753
theorem B13800449 : Blo 2153435 13800449 := bstep (se 2 (by rfl) ⟨5175168, by rfl⟩ : syracuseStep 13800449 = 10350337) B10350337
theorem B9200299 : Blo 2153435 9200299 := bstep (se 1 (by rfl) ⟨6900224, by rfl⟩ : syracuseStep 9200299 = 13800449) B13800449
theorem B12267065 : Blo 2153435 12267065 := bstep (se 2 (by rfl) ⟨4600149, by rfl⟩ : syracuseStep 12267065 = 9200299) B9200299
theorem B8178043 : Blo 2153435 8178043 := bstep (se 1 (by rfl) ⟨6133532, by rfl⟩ : syracuseStep 8178043 = 12267065) B12267065
theorem B10904057 : Blo 2153435 10904057 := bstep (se 2 (by rfl) ⟨4089021, by rfl⟩ : syracuseStep 10904057 = 8178043) B8178043
theorem B7269371 : Blo 2153435 7269371 := bstep (se 1 (by rfl) ⟨5452028, by rfl⟩ : syracuseStep 7269371 = 10904057) B10904057
theorem B4846247 : Blo 2153435 4846247 := bstep (se 1 (by rfl) ⟨3634685, by rfl⟩ : syracuseStep 4846247 = 7269371) B7269371
theorem B3230831 : Blo 2153435 3230831 := bstep (se 1 (by rfl) ⟨2423123, by rfl⟩ : syracuseStep 3230831 = 4846247) B4846247
theorem B2153887 : Blo 2153435 2153887 := bstep (se 1 (by rfl) ⟨1615415, by rfl⟩ : syracuseStep 2153887 = 3230831) B3230831
theorem B3230837 : Blo 2153435 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B2153891 : Blo 2153435 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B4089037 : Blo 2153435 4089037 := bbase (se 3 (by rfl) ⟨766694, by rfl⟩ : syracuseStep 4089037 = 1533389) (by norm_num)
theorem B5452049 : Blo 2153435 5452049 := bstep (se 2 (by rfl) ⟨2044518, by rfl⟩ : syracuseStep 5452049 = 4089037) B4089037
theorem B3634699 : Blo 2153435 3634699 := bstep (se 1 (by rfl) ⟨2726024, by rfl⟩ : syracuseStep 3634699 = 5452049) B5452049
theorem B4846265 : Blo 2153435 4846265 := bstep (se 2 (by rfl) ⟨1817349, by rfl⟩ : syracuseStep 4846265 = 3634699) B3634699
theorem B3230843 : Blo 2153435 3230843 := bstep (se 1 (by rfl) ⟨2423132, by rfl⟩ : syracuseStep 3230843 = 4846265) B4846265
theorem B2153895 : Blo 2153435 2153895 := bstep (se 1 (by rfl) ⟨1615421, by rfl⟩ : syracuseStep 2153895 = 3230843) B3230843
theorem B2423137 : Blo 2153435 2423137 := bbase (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) (by norm_num)
theorem B3230849 : Blo 2153435 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B2153899 : Blo 2153435 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B5452069 : Blo 2153435 5452069 := bbase (se 4 (by rfl) ⟨511131, by rfl⟩ : syracuseStep 5452069 = 1022263) (by norm_num)
theorem B7269425 : Blo 2153435 7269425 := bstep (se 2 (by rfl) ⟨2726034, by rfl⟩ : syracuseStep 7269425 = 5452069) B5452069
theorem B4846283 : Blo 2153435 4846283 := bstep (se 1 (by rfl) ⟨3634712, by rfl⟩ : syracuseStep 4846283 = 7269425) B7269425
theorem B3230855 : Blo 2153435 3230855 := bstep (se 1 (by rfl) ⟨2423141, by rfl⟩ : syracuseStep 3230855 = 4846283) B4846283
theorem B2153903 : Blo 2153435 2153903 := bstep (se 1 (by rfl) ⟨1615427, by rfl⟩ : syracuseStep 2153903 = 3230855) B3230855
theorem B3230861 : Blo 2153435 3230861 := bbase (se 3 (by rfl) ⟨605786, by rfl⟩ : syracuseStep 3230861 = 1211573) (by norm_num)
theorem B2153907 : Blo 2153435 2153907 := bstep (se 1 (by rfl) ⟨1615430, by rfl⟩ : syracuseStep 2153907 = 3230861) B3230861
theorem B4846301 : Blo 2153435 4846301 := bbase (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) (by norm_num)
theorem B3230867 : Blo 2153435 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B2153911 : Blo 2153435 2153911 := bstep (se 1 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 2153911 = 3230867) B3230867
theorem B3634733 : Blo 2153435 3634733 := bbase (se 3 (by rfl) ⟨681512, by rfl⟩ : syracuseStep 3634733 = 1363025) (by norm_num)
theorem B2423155 : Blo 2153435 2423155 := bstep (se 1 (by rfl) ⟨1817366, by rfl⟩ : syracuseStep 2423155 = 3634733) B3634733
theorem B3230873 : Blo 2153435 3230873 := bstep (se 2 (by rfl) ⟨1211577, by rfl⟩ : syracuseStep 3230873 = 2423155) B2423155
theorem B2153915 : Blo 2153435 2153915 := bstep (se 1 (by rfl) ⟨1615436, by rfl⟩ : syracuseStep 2153915 = 3230873) B3230873
theorem B4201421 : Blo 2153435 4201421 := bbase (se 3 (by rfl) ⟨787766, by rfl⟩ : syracuseStep 4201421 = 1575533) (by norm_num)
theorem B44815157 : Blo 2153435 44815157 := bstep (se 5 (by rfl) ⟨2100710, by rfl⟩ : syracuseStep 44815157 = 4201421) B4201421
theorem B29876771 : Blo 2153435 29876771 := bstep (se 1 (by rfl) ⟨22407578, by rfl⟩ : syracuseStep 29876771 = 44815157) B44815157
theorem B19917847 : Blo 2153435 19917847 := bstep (se 1 (by rfl) ⟨14938385, by rfl⟩ : syracuseStep 19917847 = 29876771) B29876771
theorem B106228517 : Blo 2153435 106228517 := bstep (se 4 (by rfl) ⟨9958923, by rfl⟩ : syracuseStep 106228517 = 19917847) B19917847
theorem B283276045 : Blo 2153435 283276045 := bstep (se 3 (by rfl) ⟨53114258, by rfl⟩ : syracuseStep 283276045 = 106228517) B106228517
theorem B377701393 : Blo 2153435 377701393 := bstep (se 2 (by rfl) ⟨141638022, by rfl⟩ : syracuseStep 377701393 = 283276045) B283276045
theorem B503601857 : Blo 2153435 503601857 := bstep (se 2 (by rfl) ⟨188850696, by rfl⟩ : syracuseStep 503601857 = 377701393) B377701393
theorem B335734571 : Blo 2153435 335734571 := bstep (se 1 (by rfl) ⟨251800928, by rfl⟩ : syracuseStep 335734571 = 503601857) B503601857
theorem B223823047 : Blo 2153435 223823047 := bstep (se 1 (by rfl) ⟨167867285, by rfl⟩ : syracuseStep 223823047 = 335734571) B335734571
theorem B298430729 : Blo 2153435 298430729 := bstep (se 2 (by rfl) ⟨111911523, by rfl⟩ : syracuseStep 298430729 = 223823047) B223823047
theorem B198953819 : Blo 2153435 198953819 := bstep (se 1 (by rfl) ⟨149215364, by rfl⟩ : syracuseStep 198953819 = 298430729) B298430729
theorem B132635879 : Blo 2153435 132635879 := bstep (se 1 (by rfl) ⟨99476909, by rfl⟩ : syracuseStep 132635879 = 198953819) B198953819
theorem B88423919 : Blo 2153435 88423919 := bstep (se 1 (by rfl) ⟨66317939, by rfl⟩ : syracuseStep 88423919 = 132635879) B132635879
theorem B58949279 : Blo 2153435 58949279 := bstep (se 1 (by rfl) ⟨44211959, by rfl⟩ : syracuseStep 58949279 = 88423919) B88423919
theorem B39299519 : Blo 2153435 39299519 := bstep (se 1 (by rfl) ⟨29474639, by rfl⟩ : syracuseStep 39299519 = 58949279) B58949279
theorem B104798717 : Blo 2153435 104798717 := bstep (se 3 (by rfl) ⟨19649759, by rfl⟩ : syracuseStep 104798717 = 39299519) B39299519
theorem B69865811 : Blo 2153435 69865811 := bstep (se 1 (by rfl) ⟨52399358, by rfl⟩ : syracuseStep 69865811 = 104798717) B104798717
theorem B46577207 : Blo 2153435 46577207 := bstep (se 1 (by rfl) ⟨34932905, by rfl⟩ : syracuseStep 46577207 = 69865811) B69865811
theorem B31051471 : Blo 2153435 31051471 := bstep (se 1 (by rfl) ⟨23288603, by rfl⟩ : syracuseStep 31051471 = 46577207) B46577207
theorem B41401961 : Blo 2153435 41401961 := bstep (se 2 (by rfl) ⟨15525735, by rfl⟩ : syracuseStep 41401961 = 31051471) B31051471
theorem B27601307 : Blo 2153435 27601307 := bstep (se 1 (by rfl) ⟨20700980, by rfl⟩ : syracuseStep 27601307 = 41401961) B41401961
theorem B18400871 : Blo 2153435 18400871 := bstep (se 1 (by rfl) ⟨13800653, by rfl⟩ : syracuseStep 18400871 = 27601307) B27601307
theorem B12267247 : Blo 2153435 12267247 := bstep (se 1 (by rfl) ⟨9200435, by rfl⟩ : syracuseStep 12267247 = 18400871) B18400871
theorem B16356329 : Blo 2153435 16356329 := bstep (se 2 (by rfl) ⟨6133623, by rfl⟩ : syracuseStep 16356329 = 12267247) B12267247
theorem B10904219 : Blo 2153435 10904219 := bstep (se 1 (by rfl) ⟨8178164, by rfl⟩ : syracuseStep 10904219 = 16356329) B16356329
theorem B7269479 : Blo 2153435 7269479 := bstep (se 1 (by rfl) ⟨5452109, by rfl⟩ : syracuseStep 7269479 = 10904219) B10904219
theorem B4846319 : Blo 2153435 4846319 := bstep (se 1 (by rfl) ⟨3634739, by rfl⟩ : syracuseStep 4846319 = 7269479) B7269479
theorem B3230879 : Blo 2153435 3230879 := bstep (se 1 (by rfl) ⟨2423159, by rfl⟩ : syracuseStep 3230879 = 4846319) B4846319
theorem B2153919 : Blo 2153435 2153919 := bstep (se 1 (by rfl) ⟨1615439, by rfl⟩ : syracuseStep 2153919 = 3230879) B3230879
theorem B3230885 : Blo 2153435 3230885 := bbase (se 4 (by rfl) ⟨302895, by rfl⟩ : syracuseStep 3230885 = 605791) (by norm_num)
theorem B2153923 : Blo 2153435 2153923 := bstep (se 1 (by rfl) ⟨1615442, by rfl⟩ : syracuseStep 2153923 = 3230885) B3230885
theorem B2726065 : Blo 2153435 2726065 := bbase (se 2 (by rfl) ⟨1022274, by rfl⟩ : syracuseStep 2726065 = 2044549) (by norm_num)
theorem B3634753 : Blo 2153435 3634753 := bstep (se 2 (by rfl) ⟨1363032, by rfl⟩ : syracuseStep 3634753 = 2726065) B2726065
theorem B4846337 : Blo 2153435 4846337 := bstep (se 2 (by rfl) ⟨1817376, by rfl⟩ : syracuseStep 4846337 = 3634753) B3634753
theorem B3230891 : Blo 2153435 3230891 := bstep (se 1 (by rfl) ⟨2423168, by rfl⟩ : syracuseStep 3230891 = 4846337) B4846337
theorem B2153927 : Blo 2153435 2153927 := bstep (se 1 (by rfl) ⟨1615445, by rfl⟩ : syracuseStep 2153927 = 3230891) B3230891
theorem B2423173 : Blo 2153435 2423173 := bbase (se 4 (by rfl) ⟨227172, by rfl⟩ : syracuseStep 2423173 = 454345) (by norm_num)
theorem B3230897 : Blo 2153435 3230897 := bstep (se 2 (by rfl) ⟨1211586, by rfl⟩ : syracuseStep 3230897 = 2423173) B2423173
theorem B2153931 : Blo 2153435 2153931 := bstep (se 1 (by rfl) ⟨1615448, by rfl⟩ : syracuseStep 2153931 = 3230897) B3230897
theorem B4600253 : Blo 2153435 4600253 := bbase (se 3 (by rfl) ⟨862547, by rfl⟩ : syracuseStep 4600253 = 1725095) (by norm_num)
theorem B3066835 : Blo 2153435 3066835 := bstep (se 1 (by rfl) ⟨2300126, by rfl⟩ : syracuseStep 3066835 = 4600253) B4600253
theorem B4089113 : Blo 2153435 4089113 := bstep (se 2 (by rfl) ⟨1533417, by rfl⟩ : syracuseStep 4089113 = 3066835) B3066835
theorem B2726075 : Blo 2153435 2726075 := bstep (se 1 (by rfl) ⟨2044556, by rfl⟩ : syracuseStep 2726075 = 4089113) B4089113
theorem B7269533 : Blo 2153435 7269533 := bstep (se 3 (by rfl) ⟨1363037, by rfl⟩ : syracuseStep 7269533 = 2726075) B2726075
theorem B4846355 : Blo 2153435 4846355 := bstep (se 1 (by rfl) ⟨3634766, by rfl⟩ : syracuseStep 4846355 = 7269533) B7269533
theorem B3230903 : Blo 2153435 3230903 := bstep (se 1 (by rfl) ⟨2423177, by rfl⟩ : syracuseStep 3230903 = 4846355) B4846355
theorem B2153935 : Blo 2153435 2153935 := bstep (se 1 (by rfl) ⟨1615451, by rfl⟩ : syracuseStep 2153935 = 3230903) B3230903
theorem B3230909 : Blo 2153435 3230909 := bbase (se 3 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 3230909 = 1211591) (by norm_num)
theorem B2153939 : Blo 2153435 2153939 := bstep (se 1 (by rfl) ⟨1615454, by rfl⟩ : syracuseStep 2153939 = 3230909) B3230909
theorem B4846373 : Blo 2153435 4846373 := bbase (se 4 (by rfl) ⟨454347, by rfl⟩ : syracuseStep 4846373 = 908695) (by norm_num)
theorem B3230915 : Blo 2153435 3230915 := bstep (se 1 (by rfl) ⟨2423186, by rfl⟩ : syracuseStep 3230915 = 4846373) B4846373
theorem B2153943 : Blo 2153435 2153943 := bstep (se 1 (by rfl) ⟨1615457, by rfl⟩ : syracuseStep 2153943 = 3230915) B3230915
theorem B5452181 : Blo 2153435 5452181 := bbase (se 6 (by rfl) ⟨127785, by rfl⟩ : syracuseStep 5452181 = 255571) (by norm_num)
theorem B3634787 : Blo 2153435 3634787 := bstep (se 1 (by rfl) ⟨2726090, by rfl⟩ : syracuseStep 3634787 = 5452181) B5452181
theorem B2423191 : Blo 2153435 2423191 := bstep (se 1 (by rfl) ⟨1817393, by rfl⟩ : syracuseStep 2423191 = 3634787) B3634787
theorem B3230921 : Blo 2153435 3230921 := bstep (se 2 (by rfl) ⟨1211595, by rfl⟩ : syracuseStep 3230921 = 2423191) B2423191
theorem B2153947 : Blo 2153435 2153947 := bstep (se 1 (by rfl) ⟨1615460, by rfl⟩ : syracuseStep 2153947 = 3230921) B3230921
theorem B3108701 : Blo 2153435 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B8289869 : Blo 2153435 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B22106317 : Blo 2153435 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B29475089 : Blo 2153435 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B19650059 : Blo 2153435 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13100039 : Blo 2153435 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B8733359 : Blo 2153435 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B5822239 : Blo 2153435 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B7762985 : Blo 2153435 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B5175323 : Blo 2153435 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B3450215 : Blo 2153435 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B9200573 : Blo 2153435 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B6133715 : Blo 2153435 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B4089143 : Blo 2153435 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B10904381 : Blo 2153435 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B7269587 : Blo 2153435 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B4846391 : Blo 2153435 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B3230927 : Blo 2153435 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B2153951 : Blo 2153435 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B3230933 : Blo 2153435 3230933 := bbase (se 7 (by rfl) ⟨37862, by rfl⟩ : syracuseStep 3230933 = 75725) (by norm_num)
theorem B2153955 : Blo 2153435 2153955 := bstep (se 1 (by rfl) ⟨1615466, by rfl⟩ : syracuseStep 2153955 = 3230933) B3230933
theorem B3066869 : Blo 2153435 3066869 := bbase (se 5 (by rfl) ⟨143759, by rfl⟩ : syracuseStep 3066869 = 287519) (by norm_num)
theorem B8178317 : Blo 2153435 8178317 := bstep (se 3 (by rfl) ⟨1533434, by rfl⟩ : syracuseStep 8178317 = 3066869) B3066869
theorem B5452211 : Blo 2153435 5452211 := bstep (se 1 (by rfl) ⟨4089158, by rfl⟩ : syracuseStep 5452211 = 8178317) B8178317
theorem B3634807 : Blo 2153435 3634807 := bstep (se 1 (by rfl) ⟨2726105, by rfl⟩ : syracuseStep 3634807 = 5452211) B5452211
theorem B4846409 : Blo 2153435 4846409 := bstep (se 2 (by rfl) ⟨1817403, by rfl⟩ : syracuseStep 4846409 = 3634807) B3634807
theorem B3230939 : Blo 2153435 3230939 := bstep (se 1 (by rfl) ⟨2423204, by rfl⟩ : syracuseStep 3230939 = 4846409) B4846409
theorem B2153959 : Blo 2153435 2153959 := bstep (se 1 (by rfl) ⟨1615469, by rfl⟩ : syracuseStep 2153959 = 3230939) B3230939
theorem B2423209 : Blo 2153435 2423209 := bbase (se 2 (by rfl) ⟨908703, by rfl⟩ : syracuseStep 2423209 = 1817407) (by norm_num)
theorem B3230945 : Blo 2153435 3230945 := bstep (se 2 (by rfl) ⟨1211604, by rfl⟩ : syracuseStep 3230945 = 2423209) B2423209
theorem B2153963 : Blo 2153435 2153963 := bstep (se 1 (by rfl) ⟨1615472, by rfl⟩ : syracuseStep 2153963 = 3230945) B3230945
theorem B2911141 : Blo 2153435 2911141 := bbase (se 4 (by rfl) ⟨272919, by rfl⟩ : syracuseStep 2911141 = 545839) (by norm_num)
theorem B3881521 : Blo 2153435 3881521 := bstep (se 2 (by rfl) ⟨1455570, by rfl⟩ : syracuseStep 3881521 = 2911141) B2911141
theorem B5175361 : Blo 2153435 5175361 := bstep (se 2 (by rfl) ⟨1940760, by rfl⟩ : syracuseStep 5175361 = 3881521) B3881521
theorem B6900481 : Blo 2153435 6900481 := bstep (se 2 (by rfl) ⟨2587680, by rfl⟩ : syracuseStep 6900481 = 5175361) B5175361
theorem B9200641 : Blo 2153435 9200641 := bstep (se 2 (by rfl) ⟨3450240, by rfl⟩ : syracuseStep 9200641 = 6900481) B6900481
theorem B12267521 : Blo 2153435 12267521 := bstep (se 2 (by rfl) ⟨4600320, by rfl⟩ : syracuseStep 12267521 = 9200641) B9200641
theorem B8178347 : Blo 2153435 8178347 := bstep (se 1 (by rfl) ⟨6133760, by rfl⟩ : syracuseStep 8178347 = 12267521) B12267521
theorem B5452231 : Blo 2153435 5452231 := bstep (se 1 (by rfl) ⟨4089173, by rfl⟩ : syracuseStep 5452231 = 8178347) B8178347
theorem B7269641 : Blo 2153435 7269641 := bstep (se 2 (by rfl) ⟨2726115, by rfl⟩ : syracuseStep 7269641 = 5452231) B5452231
theorem B4846427 : Blo 2153435 4846427 := bstep (se 1 (by rfl) ⟨3634820, by rfl⟩ : syracuseStep 4846427 = 7269641) B7269641
theorem B3230951 : Blo 2153435 3230951 := bstep (se 1 (by rfl) ⟨2423213, by rfl⟩ : syracuseStep 3230951 = 4846427) B4846427
theorem B2153967 : Blo 2153435 2153967 := bstep (se 1 (by rfl) ⟨1615475, by rfl⟩ : syracuseStep 2153967 = 3230951) B3230951
theorem B3230957 : Blo 2153435 3230957 := bbase (se 3 (by rfl) ⟨605804, by rfl⟩ : syracuseStep 3230957 = 1211609) (by norm_num)
theorem B2153971 : Blo 2153435 2153971 := bstep (se 1 (by rfl) ⟨1615478, by rfl⟩ : syracuseStep 2153971 = 3230957) B3230957
theorem B4846445 : Blo 2153435 4846445 := bbase (se 3 (by rfl) ⟨908708, by rfl⟩ : syracuseStep 4846445 = 1817417) (by norm_num)
theorem B3230963 : Blo 2153435 3230963 := bstep (se 1 (by rfl) ⟨2423222, by rfl⟩ : syracuseStep 3230963 = 4846445) B4846445
theorem B2153975 : Blo 2153435 2153975 := bstep (se 1 (by rfl) ⟨1615481, by rfl⟩ : syracuseStep 2153975 = 3230963) B3230963
theorem B4089197 : Blo 2153435 4089197 := bbase (se 3 (by rfl) ⟨766724, by rfl⟩ : syracuseStep 4089197 = 1533449) (by norm_num)
theorem B2726131 : Blo 2153435 2726131 := bstep (se 1 (by rfl) ⟨2044598, by rfl⟩ : syracuseStep 2726131 = 4089197) B4089197
theorem B3634841 : Blo 2153435 3634841 := bstep (se 2 (by rfl) ⟨1363065, by rfl⟩ : syracuseStep 3634841 = 2726131) B2726131
theorem B2423227 : Blo 2153435 2423227 := bstep (se 1 (by rfl) ⟨1817420, by rfl⟩ : syracuseStep 2423227 = 3634841) B3634841
theorem B3230969 : Blo 2153435 3230969 := bstep (se 2 (by rfl) ⟨1211613, by rfl⟩ : syracuseStep 3230969 = 2423227) B2423227
theorem B2153979 : Blo 2153435 2153979 := bstep (se 1 (by rfl) ⟨1615484, by rfl⟩ : syracuseStep 2153979 = 3230969) B3230969
theorem B31476053 : Blo 2153435 31476053 := bbase (se 10 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 31476053 = 92215) (by norm_num)
theorem B20984035 : Blo 2153435 20984035 := bstep (se 1 (by rfl) ⟨15738026, by rfl⟩ : syracuseStep 20984035 = 31476053) B31476053
theorem B27978713 : Blo 2153435 27978713 := bstep (se 2 (by rfl) ⟨10492017, by rfl⟩ : syracuseStep 27978713 = 20984035) B20984035
theorem B18652475 : Blo 2153435 18652475 := bstep (se 1 (by rfl) ⟨13989356, by rfl⟩ : syracuseStep 18652475 = 27978713) B27978713
theorem B49739933 : Blo 2153435 49739933 := bstep (se 3 (by rfl) ⟨9326237, by rfl⟩ : syracuseStep 49739933 = 18652475) B18652475
theorem B33159955 : Blo 2153435 33159955 := bstep (se 1 (by rfl) ⟨24869966, by rfl⟩ : syracuseStep 33159955 = 49739933) B49739933
theorem B44213273 : Blo 2153435 44213273 := bstep (se 2 (by rfl) ⟨16579977, by rfl⟩ : syracuseStep 44213273 = 33159955) B33159955
theorem B29475515 : Blo 2153435 29475515 := bstep (se 1 (by rfl) ⟨22106636, by rfl⟩ : syracuseStep 29475515 = 44213273) B44213273
theorem B78601373 : Blo 2153435 78601373 := bstep (se 3 (by rfl) ⟨14737757, by rfl⟩ : syracuseStep 78601373 = 29475515) B29475515
theorem B52400915 : Blo 2153435 52400915 := bstep (se 1 (by rfl) ⟨39300686, by rfl⟩ : syracuseStep 52400915 = 78601373) B78601373
theorem B34933943 : Blo 2153435 34933943 := bstep (se 1 (by rfl) ⟨26200457, by rfl⟩ : syracuseStep 34933943 = 52400915) B52400915
theorem B23289295 : Blo 2153435 23289295 := bstep (se 1 (by rfl) ⟨17466971, by rfl⟩ : syracuseStep 23289295 = 34933943) B34933943
theorem B31052393 : Blo 2153435 31052393 := bstep (se 2 (by rfl) ⟨11644647, by rfl⟩ : syracuseStep 31052393 = 23289295) B23289295
theorem B20701595 : Blo 2153435 20701595 := bstep (se 1 (by rfl) ⟨15526196, by rfl⟩ : syracuseStep 20701595 = 31052393) B31052393
theorem B55204253 : Blo 2153435 55204253 := bstep (se 3 (by rfl) ⟨10350797, by rfl⟩ : syracuseStep 55204253 = 20701595) B20701595
theorem B36802835 : Blo 2153435 36802835 := bstep (se 1 (by rfl) ⟨27602126, by rfl⟩ : syracuseStep 36802835 = 55204253) B55204253
theorem B24535223 : Blo 2153435 24535223 := bstep (se 1 (by rfl) ⟨18401417, by rfl⟩ : syracuseStep 24535223 = 36802835) B36802835
theorem B16356815 : Blo 2153435 16356815 := bstep (se 1 (by rfl) ⟨12267611, by rfl⟩ : syracuseStep 16356815 = 24535223) B24535223
theorem B10904543 : Blo 2153435 10904543 := bstep (se 1 (by rfl) ⟨8178407, by rfl⟩ : syracuseStep 10904543 = 16356815) B16356815
theorem B7269695 : Blo 2153435 7269695 := bstep (se 1 (by rfl) ⟨5452271, by rfl⟩ : syracuseStep 7269695 = 10904543) B10904543
theorem B4846463 : Blo 2153435 4846463 := bstep (se 1 (by rfl) ⟨3634847, by rfl⟩ : syracuseStep 4846463 = 7269695) B7269695
theorem B3230975 : Blo 2153435 3230975 := bstep (se 1 (by rfl) ⟨2423231, by rfl⟩ : syracuseStep 3230975 = 4846463) B4846463
theorem B2153983 : Blo 2153435 2153983 := bstep (se 1 (by rfl) ⟨1615487, by rfl⟩ : syracuseStep 2153983 = 3230975) B3230975
theorem B3230981 : Blo 2153435 3230981 := bbase (se 4 (by rfl) ⟨302904, by rfl⟩ : syracuseStep 3230981 = 605809) (by norm_num)
theorem B2153987 : Blo 2153435 2153987 := bstep (se 1 (by rfl) ⟨1615490, by rfl⟩ : syracuseStep 2153987 = 3230981) B3230981
theorem B3634861 : Blo 2153435 3634861 := bbase (se 3 (by rfl) ⟨681536, by rfl⟩ : syracuseStep 3634861 = 1363073) (by norm_num)
theorem B4846481 : Blo 2153435 4846481 := bstep (se 2 (by rfl) ⟨1817430, by rfl⟩ : syracuseStep 4846481 = 3634861) B3634861
theorem B3230987 : Blo 2153435 3230987 := bstep (se 1 (by rfl) ⟨2423240, by rfl⟩ : syracuseStep 3230987 = 4846481) B4846481
theorem B2153991 : Blo 2153435 2153991 := bstep (se 1 (by rfl) ⟨1615493, by rfl⟩ : syracuseStep 2153991 = 3230987) B3230987
theorem B2423245 : Blo 2153435 2423245 := bbase (se 3 (by rfl) ⟨454358, by rfl⟩ : syracuseStep 2423245 = 908717) (by norm_num)
theorem B3230993 : Blo 2153435 3230993 := bstep (se 2 (by rfl) ⟨1211622, by rfl⟩ : syracuseStep 3230993 = 2423245) B2423245
theorem B2153995 : Blo 2153435 2153995 := bstep (se 1 (by rfl) ⟨1615496, by rfl⟩ : syracuseStep 2153995 = 3230993) B3230993
theorem B7269749 : Blo 2153435 7269749 := bbase (se 5 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 7269749 = 681539) (by norm_num)
theorem B4846499 : Blo 2153435 4846499 := bstep (se 1 (by rfl) ⟨3634874, by rfl⟩ : syracuseStep 4846499 = 7269749) B7269749
theorem B3230999 : Blo 2153435 3230999 := bstep (se 1 (by rfl) ⟨2423249, by rfl⟩ : syracuseStep 3230999 = 4846499) B4846499
theorem B2153999 : Blo 2153435 2153999 := bstep (se 1 (by rfl) ⟨1615499, by rfl⟩ : syracuseStep 2153999 = 3230999) B3230999
theorem B3231005 : Blo 2153435 3231005 := bbase (se 3 (by rfl) ⟨605813, by rfl⟩ : syracuseStep 3231005 = 1211627) (by norm_num)
theorem B2154003 : Blo 2153435 2154003 := bstep (se 1 (by rfl) ⟨1615502, by rfl⟩ : syracuseStep 2154003 = 3231005) B3231005
theorem B4846517 : Blo 2153435 4846517 := bbase (se 5 (by rfl) ⟨227180, by rfl⟩ : syracuseStep 4846517 = 454361) (by norm_num)
theorem B3231011 : Blo 2153435 3231011 := bstep (se 1 (by rfl) ⟨2423258, by rfl⟩ : syracuseStep 3231011 = 4846517) B4846517
theorem B2154007 : Blo 2153435 2154007 := bstep (se 1 (by rfl) ⟨1615505, by rfl⟩ : syracuseStep 2154007 = 3231011) B3231011
theorem B3275101 : Blo 2153435 3275101 := bbase (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) (by norm_num)
theorem B4366801 : Blo 2153435 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B23289605 : Blo 2153435 23289605 := bstep (se 4 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 23289605 = 4366801) B4366801
theorem B15526403 : Blo 2153435 15526403 := bstep (se 1 (by rfl) ⟨11644802, by rfl⟩ : syracuseStep 15526403 = 23289605) B23289605
theorem B10350935 : Blo 2153435 10350935 := bstep (se 1 (by rfl) ⟨7763201, by rfl⟩ : syracuseStep 10350935 = 15526403) B15526403
theorem B6900623 : Blo 2153435 6900623 := bstep (se 1 (by rfl) ⟨5175467, by rfl⟩ : syracuseStep 6900623 = 10350935) B10350935
theorem B4600415 : Blo 2153435 4600415 := bstep (se 1 (by rfl) ⟨3450311, by rfl⟩ : syracuseStep 4600415 = 6900623) B6900623
theorem B12267773 : Blo 2153435 12267773 := bstep (se 3 (by rfl) ⟨2300207, by rfl⟩ : syracuseStep 12267773 = 4600415) B4600415
theorem B8178515 : Blo 2153435 8178515 := bstep (se 1 (by rfl) ⟨6133886, by rfl⟩ : syracuseStep 8178515 = 12267773) B12267773
theorem B5452343 : Blo 2153435 5452343 := bstep (se 1 (by rfl) ⟨4089257, by rfl⟩ : syracuseStep 5452343 = 8178515) B8178515
theorem B3634895 : Blo 2153435 3634895 := bstep (se 1 (by rfl) ⟨2726171, by rfl⟩ : syracuseStep 3634895 = 5452343) B5452343
theorem B2423263 : Blo 2153435 2423263 := bstep (se 1 (by rfl) ⟨1817447, by rfl⟩ : syracuseStep 2423263 = 3634895) B3634895
theorem B3231017 : Blo 2153435 3231017 := bstep (se 2 (by rfl) ⟨1211631, by rfl⟩ : syracuseStep 3231017 = 2423263) B2423263
theorem B2154011 : Blo 2153435 2154011 := bstep (se 1 (by rfl) ⟨1615508, by rfl⟩ : syracuseStep 2154011 = 3231017) B3231017
theorem B26200853 : Blo 2153435 26200853 := bbase (se 6 (by rfl) ⟨614082, by rfl⟩ : syracuseStep 26200853 = 1228165) (by norm_num)
theorem B17467235 : Blo 2153435 17467235 := bstep (se 1 (by rfl) ⟨13100426, by rfl⟩ : syracuseStep 17467235 = 26200853) B26200853
theorem B11644823 : Blo 2153435 11644823 := bstep (se 1 (by rfl) ⟨8733617, by rfl⟩ : syracuseStep 11644823 = 17467235) B17467235
theorem B7763215 : Blo 2153435 7763215 := bstep (se 1 (by rfl) ⟨5822411, by rfl⟩ : syracuseStep 7763215 = 11644823) B11644823
theorem B10350953 : Blo 2153435 10350953 := bstep (se 2 (by rfl) ⟨3881607, by rfl⟩ : syracuseStep 10350953 = 7763215) B7763215
theorem B6900635 : Blo 2153435 6900635 := bstep (se 1 (by rfl) ⟨5175476, by rfl⟩ : syracuseStep 6900635 = 10350953) B10350953
theorem B4600423 : Blo 2153435 4600423 := bstep (se 1 (by rfl) ⟨3450317, by rfl⟩ : syracuseStep 4600423 = 6900635) B6900635
theorem B6133897 : Blo 2153435 6133897 := bstep (se 2 (by rfl) ⟨2300211, by rfl⟩ : syracuseStep 6133897 = 4600423) B4600423
theorem B8178529 : Blo 2153435 8178529 := bstep (se 2 (by rfl) ⟨3066948, by rfl⟩ : syracuseStep 8178529 = 6133897) B6133897
theorem B10904705 : Blo 2153435 10904705 := bstep (se 2 (by rfl) ⟨4089264, by rfl⟩ : syracuseStep 10904705 = 8178529) B8178529
theorem B7269803 : Blo 2153435 7269803 := bstep (se 1 (by rfl) ⟨5452352, by rfl⟩ : syracuseStep 7269803 = 10904705) B10904705
theorem B4846535 : Blo 2153435 4846535 := bstep (se 1 (by rfl) ⟨3634901, by rfl⟩ : syracuseStep 4846535 = 7269803) B7269803
theorem B3231023 : Blo 2153435 3231023 := bstep (se 1 (by rfl) ⟨2423267, by rfl⟩ : syracuseStep 3231023 = 4846535) B4846535
theorem B2154015 : Blo 2153435 2154015 := bstep (se 1 (by rfl) ⟨1615511, by rfl⟩ : syracuseStep 2154015 = 3231023) B3231023
theorem B3231029 : Blo 2153435 3231029 := bbase (se 5 (by rfl) ⟨151454, by rfl⟩ : syracuseStep 3231029 = 302909) (by norm_num)
theorem B2154019 : Blo 2153435 2154019 := bstep (se 1 (by rfl) ⟨1615514, by rfl⟩ : syracuseStep 2154019 = 3231029) B3231029
theorem B5452373 : Blo 2153435 5452373 := bbase (se 8 (by rfl) ⟨31947, by rfl⟩ : syracuseStep 5452373 = 63895) (by norm_num)
theorem B3634915 : Blo 2153435 3634915 := bstep (se 1 (by rfl) ⟨2726186, by rfl⟩ : syracuseStep 3634915 = 5452373) B5452373
theorem B4846553 : Blo 2153435 4846553 := bstep (se 2 (by rfl) ⟨1817457, by rfl⟩ : syracuseStep 4846553 = 3634915) B3634915
theorem B3231035 : Blo 2153435 3231035 := bstep (se 1 (by rfl) ⟨2423276, by rfl⟩ : syracuseStep 3231035 = 4846553) B4846553
theorem B2154023 : Blo 2153435 2154023 := bstep (se 1 (by rfl) ⟨1615517, by rfl⟩ : syracuseStep 2154023 = 3231035) B3231035
theorem B2423281 : Blo 2153435 2423281 := bbase (se 2 (by rfl) ⟨908730, by rfl⟩ : syracuseStep 2423281 = 1817461) (by norm_num)
theorem B3231041 : Blo 2153435 3231041 := bstep (se 2 (by rfl) ⟨1211640, by rfl⟩ : syracuseStep 3231041 = 2423281) B2423281
theorem B2154027 : Blo 2153435 2154027 := bstep (se 1 (by rfl) ⟨1615520, by rfl⟩ : syracuseStep 2154027 = 3231041) B3231041
theorem B2331613 : Blo 2153435 2331613 := bbase (se 3 (by rfl) ⟨437177, by rfl⟩ : syracuseStep 2331613 = 874355) (by norm_num)
theorem B3108817 : Blo 2153435 3108817 := bstep (se 2 (by rfl) ⟨1165806, by rfl⟩ : syracuseStep 3108817 = 2331613) B2331613
theorem B4145089 : Blo 2153435 4145089 := bstep (se 2 (by rfl) ⟨1554408, by rfl⟩ : syracuseStep 4145089 = 3108817) B3108817
theorem B5526785 : Blo 2153435 5526785 := bstep (se 2 (by rfl) ⟨2072544, by rfl⟩ : syracuseStep 5526785 = 4145089) B4145089
theorem B3684523 : Blo 2153435 3684523 := bstep (se 1 (by rfl) ⟨2763392, by rfl⟩ : syracuseStep 3684523 = 5526785) B5526785
theorem B4912697 : Blo 2153435 4912697 := bstep (se 2 (by rfl) ⟨1842261, by rfl⟩ : syracuseStep 4912697 = 3684523) B3684523
theorem B13100525 : Blo 2153435 13100525 := bstep (se 3 (by rfl) ⟨2456348, by rfl⟩ : syracuseStep 13100525 = 4912697) B4912697
theorem B8733683 : Blo 2153435 8733683 := bstep (se 1 (by rfl) ⟨6550262, by rfl⟩ : syracuseStep 8733683 = 13100525) B13100525
theorem B5822455 : Blo 2153435 5822455 := bstep (se 1 (by rfl) ⟨4366841, by rfl⟩ : syracuseStep 5822455 = 8733683) B8733683
theorem B7763273 : Blo 2153435 7763273 := bstep (se 2 (by rfl) ⟨2911227, by rfl⟩ : syracuseStep 7763273 = 5822455) B5822455
theorem B5175515 : Blo 2153435 5175515 := bstep (se 1 (by rfl) ⟨3881636, by rfl⟩ : syracuseStep 5175515 = 7763273) B7763273
theorem B13801373 : Blo 2153435 13801373 := bstep (se 3 (by rfl) ⟨2587757, by rfl⟩ : syracuseStep 13801373 = 5175515) B5175515
theorem B9200915 : Blo 2153435 9200915 := bstep (se 1 (by rfl) ⟨6900686, by rfl⟩ : syracuseStep 9200915 = 13801373) B13801373
theorem B6133943 : Blo 2153435 6133943 := bstep (se 1 (by rfl) ⟨4600457, by rfl⟩ : syracuseStep 6133943 = 9200915) B9200915
theorem B4089295 : Blo 2153435 4089295 := bstep (se 1 (by rfl) ⟨3066971, by rfl⟩ : syracuseStep 4089295 = 6133943) B6133943
theorem B5452393 : Blo 2153435 5452393 := bstep (se 2 (by rfl) ⟨2044647, by rfl⟩ : syracuseStep 5452393 = 4089295) B4089295
theorem B7269857 : Blo 2153435 7269857 := bstep (se 2 (by rfl) ⟨2726196, by rfl⟩ : syracuseStep 7269857 = 5452393) B5452393
theorem B4846571 : Blo 2153435 4846571 := bstep (se 1 (by rfl) ⟨3634928, by rfl⟩ : syracuseStep 4846571 = 7269857) B7269857
theorem B3231047 : Blo 2153435 3231047 := bstep (se 1 (by rfl) ⟨2423285, by rfl⟩ : syracuseStep 3231047 = 4846571) B4846571
theorem B2154031 : Blo 2153435 2154031 := bstep (se 1 (by rfl) ⟨1615523, by rfl⟩ : syracuseStep 2154031 = 3231047) B3231047
theorem B3231053 : Blo 2153435 3231053 := bbase (se 3 (by rfl) ⟨605822, by rfl⟩ : syracuseStep 3231053 = 1211645) (by norm_num)
theorem B2154035 : Blo 2153435 2154035 := bstep (se 1 (by rfl) ⟨1615526, by rfl⟩ : syracuseStep 2154035 = 3231053) B3231053
theorem B4846589 : Blo 2153435 4846589 := bbase (se 3 (by rfl) ⟨908735, by rfl⟩ : syracuseStep 4846589 = 1817471) (by norm_num)
theorem B3231059 : Blo 2153435 3231059 := bstep (se 1 (by rfl) ⟨2423294, by rfl⟩ : syracuseStep 3231059 = 4846589) B4846589
theorem B2154039 : Blo 2153435 2154039 := bstep (se 1 (by rfl) ⟨1615529, by rfl⟩ : syracuseStep 2154039 = 3231059) B3231059
theorem B3634949 : Blo 2153435 3634949 := bbase (se 4 (by rfl) ⟨340776, by rfl⟩ : syracuseStep 3634949 = 681553) (by norm_num)
theorem B2423299 : Blo 2153435 2423299 := bstep (se 1 (by rfl) ⟨1817474, by rfl⟩ : syracuseStep 2423299 = 3634949) B3634949
theorem B3231065 : Blo 2153435 3231065 := bstep (se 2 (by rfl) ⟨1211649, by rfl⟩ : syracuseStep 3231065 = 2423299) B2423299
theorem B2154043 : Blo 2153435 2154043 := bstep (se 1 (by rfl) ⟨1615532, by rfl⟩ : syracuseStep 2154043 = 3231065) B3231065
theorem B16357301 : Blo 2153435 16357301 := bbase (se 5 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 16357301 = 1533497) (by norm_num)
theorem B10904867 : Blo 2153435 10904867 := bstep (se 1 (by rfl) ⟨8178650, by rfl⟩ : syracuseStep 10904867 = 16357301) B16357301
theorem B7269911 : Blo 2153435 7269911 := bstep (se 1 (by rfl) ⟨5452433, by rfl⟩ : syracuseStep 7269911 = 10904867) B10904867
theorem B4846607 : Blo 2153435 4846607 := bstep (se 1 (by rfl) ⟨3634955, by rfl⟩ : syracuseStep 4846607 = 7269911) B7269911
theorem B3231071 : Blo 2153435 3231071 := bstep (se 1 (by rfl) ⟨2423303, by rfl⟩ : syracuseStep 3231071 = 4846607) B4846607
theorem B2154047 : Blo 2153435 2154047 := bstep (se 1 (by rfl) ⟨1615535, by rfl⟩ : syracuseStep 2154047 = 3231071) B3231071
theorem B3231077 : Blo 2153435 3231077 := bbase (se 4 (by rfl) ⟨302913, by rfl⟩ : syracuseStep 3231077 = 605827) (by norm_num)
theorem B2154051 : Blo 2153435 2154051 := bstep (se 1 (by rfl) ⟨1615538, by rfl⟩ : syracuseStep 2154051 = 3231077) B3231077
theorem B4089341 : Blo 2153435 4089341 := bbase (se 3 (by rfl) ⟨766751, by rfl⟩ : syracuseStep 4089341 = 1533503) (by norm_num)
theorem B2726227 : Blo 2153435 2726227 := bstep (se 1 (by rfl) ⟨2044670, by rfl⟩ : syracuseStep 2726227 = 4089341) B4089341
theorem B3634969 : Blo 2153435 3634969 := bstep (se 2 (by rfl) ⟨1363113, by rfl⟩ : syracuseStep 3634969 = 2726227) B2726227
theorem B4846625 : Blo 2153435 4846625 := bstep (se 2 (by rfl) ⟨1817484, by rfl⟩ : syracuseStep 4846625 = 3634969) B3634969
theorem B3231083 : Blo 2153435 3231083 := bstep (se 1 (by rfl) ⟨2423312, by rfl⟩ : syracuseStep 3231083 = 4846625) B4846625
theorem B2154055 : Blo 2153435 2154055 := bstep (se 1 (by rfl) ⟨1615541, by rfl⟩ : syracuseStep 2154055 = 3231083) B3231083
theorem B2423317 : Blo 2153435 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B3231089 : Blo 2153435 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B2154059 : Blo 2153435 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B2726237 : Blo 2153435 2726237 := bbase (se 3 (by rfl) ⟨511169, by rfl⟩ : syracuseStep 2726237 = 1022339) (by norm_num)
theorem B7269965 : Blo 2153435 7269965 := bstep (se 3 (by rfl) ⟨1363118, by rfl⟩ : syracuseStep 7269965 = 2726237) B2726237
theorem B4846643 : Blo 2153435 4846643 := bstep (se 1 (by rfl) ⟨3634982, by rfl⟩ : syracuseStep 4846643 = 7269965) B7269965
theorem B3231095 : Blo 2153435 3231095 := bstep (se 1 (by rfl) ⟨2423321, by rfl⟩ : syracuseStep 3231095 = 4846643) B4846643
theorem B2154063 : Blo 2153435 2154063 := bstep (se 1 (by rfl) ⟨1615547, by rfl⟩ : syracuseStep 2154063 = 3231095) B3231095
theorem B3231101 : Blo 2153435 3231101 := bbase (se 3 (by rfl) ⟨605831, by rfl⟩ : syracuseStep 3231101 = 1211663) (by norm_num)
theorem B2154067 : Blo 2153435 2154067 := bstep (se 1 (by rfl) ⟨1615550, by rfl⟩ : syracuseStep 2154067 = 3231101) B3231101
theorem B4846661 : Blo 2153435 4846661 := bbase (se 4 (by rfl) ⟨454374, by rfl⟩ : syracuseStep 4846661 = 908749) (by norm_num)
theorem B3231107 : Blo 2153435 3231107 := bstep (se 1 (by rfl) ⟨2423330, by rfl⟩ : syracuseStep 3231107 = 4846661) B4846661
theorem B2154071 : Blo 2153435 2154071 := bstep (se 1 (by rfl) ⟨1615553, by rfl⟩ : syracuseStep 2154071 = 3231107) B3231107
theorem B6134069 : Blo 2153435 6134069 := bbase (se 5 (by rfl) ⟨287534, by rfl⟩ : syracuseStep 6134069 = 575069) (by norm_num)
theorem B4089379 : Blo 2153435 4089379 := bstep (se 1 (by rfl) ⟨3067034, by rfl⟩ : syracuseStep 4089379 = 6134069) B6134069
theorem B5452505 : Blo 2153435 5452505 := bstep (se 2 (by rfl) ⟨2044689, by rfl⟩ : syracuseStep 5452505 = 4089379) B4089379
theorem B3635003 : Blo 2153435 3635003 := bstep (se 1 (by rfl) ⟨2726252, by rfl⟩ : syracuseStep 3635003 = 5452505) B5452505
theorem B2423335 : Blo 2153435 2423335 := bstep (se 1 (by rfl) ⟨1817501, by rfl⟩ : syracuseStep 2423335 = 3635003) B3635003
theorem B3231113 : Blo 2153435 3231113 := bstep (se 2 (by rfl) ⟨1211667, by rfl⟩ : syracuseStep 3231113 = 2423335) B2423335
theorem B2154075 : Blo 2153435 2154075 := bstep (se 1 (by rfl) ⟨1615556, by rfl⟩ : syracuseStep 2154075 = 3231113) B3231113
theorem B10905029 : Blo 2153435 10905029 := bbase (se 4 (by rfl) ⟨1022346, by rfl⟩ : syracuseStep 10905029 = 2044693) (by norm_num)
theorem B7270019 : Blo 2153435 7270019 := bstep (se 1 (by rfl) ⟨5452514, by rfl⟩ : syracuseStep 7270019 = 10905029) B10905029
theorem B4846679 : Blo 2153435 4846679 := bstep (se 1 (by rfl) ⟨3635009, by rfl⟩ : syracuseStep 4846679 = 7270019) B7270019
theorem B3231119 : Blo 2153435 3231119 := bstep (se 1 (by rfl) ⟨2423339, by rfl⟩ : syracuseStep 3231119 = 4846679) B4846679
theorem B2154079 : Blo 2153435 2154079 := bstep (se 1 (by rfl) ⟨1615559, by rfl⟩ : syracuseStep 2154079 = 3231119) B3231119
theorem B3231125 : Blo 2153435 3231125 := bbase (se 6 (by rfl) ⟨75729, by rfl⟩ : syracuseStep 3231125 = 151459) (by norm_num)
theorem B2154083 : Blo 2153435 2154083 := bstep (se 1 (by rfl) ⟨1615562, by rfl⟩ : syracuseStep 2154083 = 3231125) B3231125
theorem B2587825 : Blo 2153435 2587825 := bbase (se 2 (by rfl) ⟨970434, by rfl⟩ : syracuseStep 2587825 = 1940869) (by norm_num)
theorem B3450433 : Blo 2153435 3450433 := bstep (se 2 (by rfl) ⟨1293912, by rfl⟩ : syracuseStep 3450433 = 2587825) B2587825
theorem B4600577 : Blo 2153435 4600577 := bstep (se 2 (by rfl) ⟨1725216, by rfl⟩ : syracuseStep 4600577 = 3450433) B3450433
theorem B12268205 : Blo 2153435 12268205 := bstep (se 3 (by rfl) ⟨2300288, by rfl⟩ : syracuseStep 12268205 = 4600577) B4600577
theorem B8178803 : Blo 2153435 8178803 := bstep (se 1 (by rfl) ⟨6134102, by rfl⟩ : syracuseStep 8178803 = 12268205) B12268205
theorem B5452535 : Blo 2153435 5452535 := bstep (se 1 (by rfl) ⟨4089401, by rfl⟩ : syracuseStep 5452535 = 8178803) B8178803
theorem B3635023 : Blo 2153435 3635023 := bstep (se 1 (by rfl) ⟨2726267, by rfl⟩ : syracuseStep 3635023 = 5452535) B5452535
theorem B4846697 : Blo 2153435 4846697 := bstep (se 2 (by rfl) ⟨1817511, by rfl⟩ : syracuseStep 4846697 = 3635023) B3635023
theorem B3231131 : Blo 2153435 3231131 := bstep (se 1 (by rfl) ⟨2423348, by rfl⟩ : syracuseStep 3231131 = 4846697) B4846697
theorem B2154087 : Blo 2153435 2154087 := bstep (se 1 (by rfl) ⟨1615565, by rfl⟩ : syracuseStep 2154087 = 3231131) B3231131
theorem B2423353 : Blo 2153435 2423353 := bbase (se 2 (by rfl) ⟨908757, by rfl⟩ : syracuseStep 2423353 = 1817515) (by norm_num)
theorem B3231137 : Blo 2153435 3231137 := bstep (se 2 (by rfl) ⟨1211676, by rfl⟩ : syracuseStep 3231137 = 2423353) B2423353
theorem B2154091 : Blo 2153435 2154091 := bstep (se 1 (by rfl) ⟨1615568, by rfl⟩ : syracuseStep 2154091 = 3231137) B3231137
theorem B2300297 : Blo 2153435 2300297 := bbase (se 2 (by rfl) ⟨862611, by rfl⟩ : syracuseStep 2300297 = 1725223) (by norm_num)
theorem B6134125 : Blo 2153435 6134125 := bstep (se 3 (by rfl) ⟨1150148, by rfl⟩ : syracuseStep 6134125 = 2300297) B2300297
theorem B8178833 : Blo 2153435 8178833 := bstep (se 2 (by rfl) ⟨3067062, by rfl⟩ : syracuseStep 8178833 = 6134125) B6134125
theorem B5452555 : Blo 2153435 5452555 := bstep (se 1 (by rfl) ⟨4089416, by rfl⟩ : syracuseStep 5452555 = 8178833) B8178833
theorem B7270073 : Blo 2153435 7270073 := bstep (se 2 (by rfl) ⟨2726277, by rfl⟩ : syracuseStep 7270073 = 5452555) B5452555
theorem B4846715 : Blo 2153435 4846715 := bstep (se 1 (by rfl) ⟨3635036, by rfl⟩ : syracuseStep 4846715 = 7270073) B7270073
theorem B3231143 : Blo 2153435 3231143 := bstep (se 1 (by rfl) ⟨2423357, by rfl⟩ : syracuseStep 3231143 = 4846715) B4846715
theorem B2154095 : Blo 2153435 2154095 := bstep (se 1 (by rfl) ⟨1615571, by rfl⟩ : syracuseStep 2154095 = 3231143) B3231143
theorem B3231149 : Blo 2153435 3231149 := bbase (se 3 (by rfl) ⟨605840, by rfl⟩ : syracuseStep 3231149 = 1211681) (by norm_num)
theorem B2154099 : Blo 2153435 2154099 := bstep (se 1 (by rfl) ⟨1615574, by rfl⟩ : syracuseStep 2154099 = 3231149) B3231149
theorem B4846733 : Blo 2153435 4846733 := bbase (se 3 (by rfl) ⟨908762, by rfl⟩ : syracuseStep 4846733 = 1817525) (by norm_num)
theorem B3231155 : Blo 2153435 3231155 := bstep (se 1 (by rfl) ⟨2423366, by rfl⟩ : syracuseStep 3231155 = 4846733) B4846733
theorem B2154103 : Blo 2153435 2154103 := bstep (se 1 (by rfl) ⟨1615577, by rfl⟩ : syracuseStep 2154103 = 3231155) B3231155
theorem B2726293 : Blo 2153435 2726293 := bbase (se 6 (by rfl) ⟨63897, by rfl⟩ : syracuseStep 2726293 = 127795) (by norm_num)
theorem B3635057 : Blo 2153435 3635057 := bstep (se 2 (by rfl) ⟨1363146, by rfl⟩ : syracuseStep 3635057 = 2726293) B2726293
theorem B2423371 : Blo 2153435 2423371 := bstep (se 1 (by rfl) ⟨1817528, by rfl⟩ : syracuseStep 2423371 = 3635057) B3635057
theorem B3231161 : Blo 2153435 3231161 := bstep (se 2 (by rfl) ⟨1211685, by rfl⟩ : syracuseStep 3231161 = 2423371) B2423371
theorem B2154107 : Blo 2153435 2154107 := bstep (se 1 (by rfl) ⟨1615580, by rfl⟩ : syracuseStep 2154107 = 3231161) B3231161
theorem B24871445 : Blo 2153435 24871445 := bbase (se 6 (by rfl) ⟨582924, by rfl⟩ : syracuseStep 24871445 = 1165849) (by norm_num)
theorem B16580963 : Blo 2153435 16580963 := bstep (se 1 (by rfl) ⟨12435722, by rfl⟩ : syracuseStep 16580963 = 24871445) B24871445
theorem B44215901 : Blo 2153435 44215901 := bstep (se 3 (by rfl) ⟨8290481, by rfl⟩ : syracuseStep 44215901 = 16580963) B16580963
theorem B29477267 : Blo 2153435 29477267 := bstep (se 1 (by rfl) ⟨22107950, by rfl⟩ : syracuseStep 29477267 = 44215901) B44215901
theorem B19651511 : Blo 2153435 19651511 := bstep (se 1 (by rfl) ⟨14738633, by rfl⟩ : syracuseStep 19651511 = 29477267) B29477267
theorem B52404029 : Blo 2153435 52404029 := bstep (se 3 (by rfl) ⟨9825755, by rfl⟩ : syracuseStep 52404029 = 19651511) B19651511
theorem B34936019 : Blo 2153435 34936019 := bstep (se 1 (by rfl) ⟨26202014, by rfl⟩ : syracuseStep 34936019 = 52404029) B52404029
theorem B23290679 : Blo 2153435 23290679 := bstep (se 1 (by rfl) ⟨17468009, by rfl⟩ : syracuseStep 23290679 = 34936019) B34936019
theorem B62108477 : Blo 2153435 62108477 := bstep (se 3 (by rfl) ⟨11645339, by rfl⟩ : syracuseStep 62108477 = 23290679) B23290679
theorem B41405651 : Blo 2153435 41405651 := bstep (se 1 (by rfl) ⟨31054238, by rfl⟩ : syracuseStep 41405651 = 62108477) B62108477
theorem B27603767 : Blo 2153435 27603767 := bstep (se 1 (by rfl) ⟨20702825, by rfl⟩ : syracuseStep 27603767 = 41405651) B41405651
theorem B18402511 : Blo 2153435 18402511 := bstep (se 1 (by rfl) ⟨13801883, by rfl⟩ : syracuseStep 18402511 = 27603767) B27603767
theorem B24536681 : Blo 2153435 24536681 := bstep (se 2 (by rfl) ⟨9201255, by rfl⟩ : syracuseStep 24536681 = 18402511) B18402511
theorem B16357787 : Blo 2153435 16357787 := bstep (se 1 (by rfl) ⟨12268340, by rfl⟩ : syracuseStep 16357787 = 24536681) B24536681
theorem B10905191 : Blo 2153435 10905191 := bstep (se 1 (by rfl) ⟨8178893, by rfl⟩ : syracuseStep 10905191 = 16357787) B16357787
theorem B7270127 : Blo 2153435 7270127 := bstep (se 1 (by rfl) ⟨5452595, by rfl⟩ : syracuseStep 7270127 = 10905191) B10905191
theorem B4846751 : Blo 2153435 4846751 := bstep (se 1 (by rfl) ⟨3635063, by rfl⟩ : syracuseStep 4846751 = 7270127) B7270127
theorem B3231167 : Blo 2153435 3231167 := bstep (se 1 (by rfl) ⟨2423375, by rfl⟩ : syracuseStep 3231167 = 4846751) B4846751
theorem B2154111 : Blo 2153435 2154111 := bstep (se 1 (by rfl) ⟨1615583, by rfl⟩ : syracuseStep 2154111 = 3231167) B3231167
theorem B3231173 : Blo 2153435 3231173 := bbase (se 4 (by rfl) ⟨302922, by rfl⟩ : syracuseStep 3231173 = 605845) (by norm_num)
theorem B2154115 : Blo 2153435 2154115 := bstep (se 1 (by rfl) ⟨1615586, by rfl⟩ : syracuseStep 2154115 = 3231173) B3231173
theorem B3635077 : Blo 2153435 3635077 := bbase (se 4 (by rfl) ⟨340788, by rfl⟩ : syracuseStep 3635077 = 681577) (by norm_num)
theorem B4846769 : Blo 2153435 4846769 := bstep (se 2 (by rfl) ⟨1817538, by rfl⟩ : syracuseStep 4846769 = 3635077) B3635077
theorem B3231179 : Blo 2153435 3231179 := bstep (se 1 (by rfl) ⟨2423384, by rfl⟩ : syracuseStep 3231179 = 4846769) B4846769
theorem B2154119 : Blo 2153435 2154119 := bstep (se 1 (by rfl) ⟨1615589, by rfl⟩ : syracuseStep 2154119 = 3231179) B3231179
theorem B2423389 : Blo 2153435 2423389 := bbase (se 3 (by rfl) ⟨454385, by rfl⟩ : syracuseStep 2423389 = 908771) (by norm_num)
theorem B3231185 : Blo 2153435 3231185 := bstep (se 2 (by rfl) ⟨1211694, by rfl⟩ : syracuseStep 3231185 = 2423389) B2423389
theorem B2154123 : Blo 2153435 2154123 := bstep (se 1 (by rfl) ⟨1615592, by rfl⟩ : syracuseStep 2154123 = 3231185) B3231185
theorem B7270181 : Blo 2153435 7270181 := bbase (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) (by norm_num)
theorem B4846787 : Blo 2153435 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B3231191 : Blo 2153435 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B2154127 : Blo 2153435 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B3231197 : Blo 2153435 3231197 := bbase (se 3 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 3231197 = 1211699) (by norm_num)
theorem B2154131 : Blo 2153435 2154131 := bstep (se 1 (by rfl) ⟨1615598, by rfl⟩ : syracuseStep 2154131 = 3231197) B3231197
theorem B4846805 : Blo 2153435 4846805 := bbase (se 7 (by rfl) ⟨56798, by rfl⟩ : syracuseStep 4846805 = 113597) (by norm_num)
theorem B3231203 : Blo 2153435 3231203 := bstep (se 1 (by rfl) ⟨2423402, by rfl⟩ : syracuseStep 3231203 = 4846805) B4846805
theorem B2154135 : Blo 2153435 2154135 := bstep (se 1 (by rfl) ⟨1615601, by rfl⟩ : syracuseStep 2154135 = 3231203) B3231203
theorem B9326917 : Blo 2153435 9326917 := bbase (se 4 (by rfl) ⟨874398, by rfl⟩ : syracuseStep 9326917 = 1748797) (by norm_num)
theorem B49743557 : Blo 2153435 49743557 := bstep (se 4 (by rfl) ⟨4663458, by rfl⟩ : syracuseStep 49743557 = 9326917) B9326917
theorem B33162371 : Blo 2153435 33162371 := bstep (se 1 (by rfl) ⟨24871778, by rfl⟩ : syracuseStep 33162371 = 49743557) B49743557
theorem B22108247 : Blo 2153435 22108247 := bstep (se 1 (by rfl) ⟨16581185, by rfl⟩ : syracuseStep 22108247 = 33162371) B33162371
theorem B14738831 : Blo 2153435 14738831 := bstep (se 1 (by rfl) ⟨11054123, by rfl⟩ : syracuseStep 14738831 = 22108247) B22108247
theorem B9825887 : Blo 2153435 9825887 := bstep (se 1 (by rfl) ⟨7369415, by rfl⟩ : syracuseStep 9825887 = 14738831) B14738831
theorem B26202365 : Blo 2153435 26202365 := bstep (se 3 (by rfl) ⟨4912943, by rfl⟩ : syracuseStep 26202365 = 9825887) B9825887
theorem B17468243 : Blo 2153435 17468243 := bstep (se 1 (by rfl) ⟨13101182, by rfl⟩ : syracuseStep 17468243 = 26202365) B26202365
theorem B11645495 : Blo 2153435 11645495 := bstep (se 1 (by rfl) ⟨8734121, by rfl⟩ : syracuseStep 11645495 = 17468243) B17468243
theorem B7763663 : Blo 2153435 7763663 := bstep (se 1 (by rfl) ⟨5822747, by rfl⟩ : syracuseStep 7763663 = 11645495) B11645495
theorem B5175775 : Blo 2153435 5175775 := bstep (se 1 (by rfl) ⟨3881831, by rfl⟩ : syracuseStep 5175775 = 7763663) B7763663
theorem B6901033 : Blo 2153435 6901033 := bstep (se 2 (by rfl) ⟨2587887, by rfl⟩ : syracuseStep 6901033 = 5175775) B5175775
theorem B9201377 : Blo 2153435 9201377 := bstep (se 2 (by rfl) ⟨3450516, by rfl⟩ : syracuseStep 9201377 = 6901033) B6901033
theorem B6134251 : Blo 2153435 6134251 := bstep (se 1 (by rfl) ⟨4600688, by rfl⟩ : syracuseStep 6134251 = 9201377) B9201377
theorem B8179001 : Blo 2153435 8179001 := bstep (se 2 (by rfl) ⟨3067125, by rfl⟩ : syracuseStep 8179001 = 6134251) B6134251
theorem B5452667 : Blo 2153435 5452667 := bstep (se 1 (by rfl) ⟨4089500, by rfl⟩ : syracuseStep 5452667 = 8179001) B8179001
theorem B3635111 : Blo 2153435 3635111 := bstep (se 1 (by rfl) ⟨2726333, by rfl⟩ : syracuseStep 3635111 = 5452667) B5452667
theorem B2423407 : Blo 2153435 2423407 := bstep (se 1 (by rfl) ⟨1817555, by rfl⟩ : syracuseStep 2423407 = 3635111) B3635111
theorem B3231209 : Blo 2153435 3231209 := bstep (se 2 (by rfl) ⟨1211703, by rfl⟩ : syracuseStep 3231209 = 2423407) B2423407
theorem B2154139 : Blo 2153435 2154139 := bstep (se 1 (by rfl) ⟨1615604, by rfl⟩ : syracuseStep 2154139 = 3231209) B3231209
theorem B9326933 : Blo 2153435 9326933 := bbase (se 10 (by rfl) ⟨13662, by rfl⟩ : syracuseStep 9326933 = 27325) (by norm_num)
theorem B6217955 : Blo 2153435 6217955 := bstep (se 1 (by rfl) ⟨4663466, by rfl⟩ : syracuseStep 6217955 = 9326933) B9326933
theorem B4145303 : Blo 2153435 4145303 := bstep (se 1 (by rfl) ⟨3108977, by rfl⟩ : syracuseStep 4145303 = 6217955) B6217955
theorem B11054141 : Blo 2153435 11054141 := bstep (se 3 (by rfl) ⟨2072651, by rfl⟩ : syracuseStep 11054141 = 4145303) B4145303
theorem B7369427 : Blo 2153435 7369427 := bstep (se 1 (by rfl) ⟨5527070, by rfl⟩ : syracuseStep 7369427 = 11054141) B11054141
theorem B19651805 : Blo 2153435 19651805 := bstep (se 3 (by rfl) ⟨3684713, by rfl⟩ : syracuseStep 19651805 = 7369427) B7369427
theorem B13101203 : Blo 2153435 13101203 := bstep (se 1 (by rfl) ⟨9825902, by rfl⟩ : syracuseStep 13101203 = 19651805) B19651805
theorem B34936541 : Blo 2153435 34936541 := bstep (se 3 (by rfl) ⟨6550601, by rfl⟩ : syracuseStep 34936541 = 13101203) B13101203
theorem B23291027 : Blo 2153435 23291027 := bstep (se 1 (by rfl) ⟨17468270, by rfl⟩ : syracuseStep 23291027 = 34936541) B34936541
theorem B15527351 : Blo 2153435 15527351 := bstep (se 1 (by rfl) ⟨11645513, by rfl⟩ : syracuseStep 15527351 = 23291027) B23291027
theorem B10351567 : Blo 2153435 10351567 := bstep (se 1 (by rfl) ⟨7763675, by rfl⟩ : syracuseStep 10351567 = 15527351) B15527351
theorem B13802089 : Blo 2153435 13802089 := bstep (se 2 (by rfl) ⟨5175783, by rfl⟩ : syracuseStep 13802089 = 10351567) B10351567
theorem B18402785 : Blo 2153435 18402785 := bstep (se 2 (by rfl) ⟨6901044, by rfl⟩ : syracuseStep 18402785 = 13802089) B13802089
theorem B12268523 : Blo 2153435 12268523 := bstep (se 1 (by rfl) ⟨9201392, by rfl⟩ : syracuseStep 12268523 = 18402785) B18402785
theorem B8179015 : Blo 2153435 8179015 := bstep (se 1 (by rfl) ⟨6134261, by rfl⟩ : syracuseStep 8179015 = 12268523) B12268523
theorem B10905353 : Blo 2153435 10905353 := bstep (se 2 (by rfl) ⟨4089507, by rfl⟩ : syracuseStep 10905353 = 8179015) B8179015
theorem B7270235 : Blo 2153435 7270235 := bstep (se 1 (by rfl) ⟨5452676, by rfl⟩ : syracuseStep 7270235 = 10905353) B10905353
theorem B4846823 : Blo 2153435 4846823 := bstep (se 1 (by rfl) ⟨3635117, by rfl⟩ : syracuseStep 4846823 = 7270235) B7270235
theorem B3231215 : Blo 2153435 3231215 := bstep (se 1 (by rfl) ⟨2423411, by rfl⟩ : syracuseStep 3231215 = 4846823) B4846823
theorem B2154143 : Blo 2153435 2154143 := bstep (se 1 (by rfl) ⟨1615607, by rfl⟩ : syracuseStep 2154143 = 3231215) B3231215
theorem B3231221 : Blo 2153435 3231221 := bbase (se 5 (by rfl) ⟨151463, by rfl⟩ : syracuseStep 3231221 = 302927) (by norm_num)
theorem B2154147 : Blo 2153435 2154147 := bstep (se 1 (by rfl) ⟨1615610, by rfl⟩ : syracuseStep 2154147 = 3231221) B3231221
theorem B2300357 : Blo 2153435 2300357 := bbase (se 4 (by rfl) ⟨215658, by rfl⟩ : syracuseStep 2300357 = 431317) (by norm_num)
theorem B6134285 : Blo 2153435 6134285 := bstep (se 3 (by rfl) ⟨1150178, by rfl⟩ : syracuseStep 6134285 = 2300357) B2300357
theorem B4089523 : Blo 2153435 4089523 := bstep (se 1 (by rfl) ⟨3067142, by rfl⟩ : syracuseStep 4089523 = 6134285) B6134285
theorem B5452697 : Blo 2153435 5452697 := bstep (se 2 (by rfl) ⟨2044761, by rfl⟩ : syracuseStep 5452697 = 4089523) B4089523
theorem B3635131 : Blo 2153435 3635131 := bstep (se 1 (by rfl) ⟨2726348, by rfl⟩ : syracuseStep 3635131 = 5452697) B5452697
theorem B4846841 : Blo 2153435 4846841 := bstep (se 2 (by rfl) ⟨1817565, by rfl⟩ : syracuseStep 4846841 = 3635131) B3635131
theorem B3231227 : Blo 2153435 3231227 := bstep (se 1 (by rfl) ⟨2423420, by rfl⟩ : syracuseStep 3231227 = 4846841) B4846841
theorem B2154151 : Blo 2153435 2154151 := bstep (se 1 (by rfl) ⟨1615613, by rfl⟩ : syracuseStep 2154151 = 3231227) B3231227
theorem B2423425 : Blo 2153435 2423425 := bbase (se 2 (by rfl) ⟨908784, by rfl⟩ : syracuseStep 2423425 = 1817569) (by norm_num)
theorem B3231233 : Blo 2153435 3231233 := bstep (se 2 (by rfl) ⟨1211712, by rfl⟩ : syracuseStep 3231233 = 2423425) B2423425
theorem B2154155 : Blo 2153435 2154155 := bstep (se 1 (by rfl) ⟨1615616, by rfl⟩ : syracuseStep 2154155 = 3231233) B3231233
theorem B5452717 : Blo 2153435 5452717 := bbase (se 3 (by rfl) ⟨1022384, by rfl⟩ : syracuseStep 5452717 = 2044769) (by norm_num)
theorem B7270289 : Blo 2153435 7270289 := bstep (se 2 (by rfl) ⟨2726358, by rfl⟩ : syracuseStep 7270289 = 5452717) B5452717
theorem B4846859 : Blo 2153435 4846859 := bstep (se 1 (by rfl) ⟨3635144, by rfl⟩ : syracuseStep 4846859 = 7270289) B7270289
theorem B3231239 : Blo 2153435 3231239 := bstep (se 1 (by rfl) ⟨2423429, by rfl⟩ : syracuseStep 3231239 = 4846859) B4846859
theorem B2154159 : Blo 2153435 2154159 := bstep (se 1 (by rfl) ⟨1615619, by rfl⟩ : syracuseStep 2154159 = 3231239) B3231239
theorem B3231245 : Blo 2153435 3231245 := bbase (se 3 (by rfl) ⟨605858, by rfl⟩ : syracuseStep 3231245 = 1211717) (by norm_num)
theorem B2154163 : Blo 2153435 2154163 := bstep (se 1 (by rfl) ⟨1615622, by rfl⟩ : syracuseStep 2154163 = 3231245) B3231245
theorem B4846877 : Blo 2153435 4846877 := bbase (se 3 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 4846877 = 1817579) (by norm_num)
theorem B3231251 : Blo 2153435 3231251 := bstep (se 1 (by rfl) ⟨2423438, by rfl⟩ : syracuseStep 3231251 = 4846877) B4846877
theorem B2154167 : Blo 2153435 2154167 := bstep (se 1 (by rfl) ⟨1615625, by rfl⟩ : syracuseStep 2154167 = 3231251) B3231251
theorem B3635165 : Blo 2153435 3635165 := bbase (se 3 (by rfl) ⟨681593, by rfl⟩ : syracuseStep 3635165 = 1363187) (by norm_num)
theorem B2423443 : Blo 2153435 2423443 := bstep (se 1 (by rfl) ⟨1817582, by rfl⟩ : syracuseStep 2423443 = 3635165) B3635165
theorem B3231257 : Blo 2153435 3231257 := bstep (se 2 (by rfl) ⟨1211721, by rfl⟩ : syracuseStep 3231257 = 2423443) B2423443
theorem B2154171 : Blo 2153435 2154171 := bstep (se 1 (by rfl) ⟨1615628, by rfl⟩ : syracuseStep 2154171 = 3231257) B3231257
theorem B4145365 : Blo 2153435 4145365 := bbase (se 7 (by rfl) ⟨48578, by rfl⟩ : syracuseStep 4145365 = 97157) (by norm_num)
theorem B5527153 : Blo 2153435 5527153 := bstep (se 2 (by rfl) ⟨2072682, by rfl⟩ : syracuseStep 5527153 = 4145365) B4145365
theorem B7369537 : Blo 2153435 7369537 := bstep (se 2 (by rfl) ⟨2763576, by rfl⟩ : syracuseStep 7369537 = 5527153) B5527153
theorem B9826049 : Blo 2153435 9826049 := bstep (se 2 (by rfl) ⟨3684768, by rfl⟩ : syracuseStep 9826049 = 7369537) B7369537
theorem B26202797 : Blo 2153435 26202797 := bstep (se 3 (by rfl) ⟨4913024, by rfl⟩ : syracuseStep 26202797 = 9826049) B9826049
theorem B17468531 : Blo 2153435 17468531 := bstep (se 1 (by rfl) ⟨13101398, by rfl⟩ : syracuseStep 17468531 = 26202797) B26202797
theorem B11645687 : Blo 2153435 11645687 := bstep (se 1 (by rfl) ⟨8734265, by rfl⟩ : syracuseStep 11645687 = 17468531) B17468531
theorem B7763791 : Blo 2153435 7763791 := bstep (se 1 (by rfl) ⟨5822843, by rfl⟩ : syracuseStep 7763791 = 11645687) B11645687
theorem B10351721 : Blo 2153435 10351721 := bstep (se 2 (by rfl) ⟨3881895, by rfl⟩ : syracuseStep 10351721 = 7763791) B7763791
theorem B6901147 : Blo 2153435 6901147 := bstep (se 1 (by rfl) ⟨5175860, by rfl⟩ : syracuseStep 6901147 = 10351721) B10351721
theorem B9201529 : Blo 2153435 9201529 := bstep (se 2 (by rfl) ⟨3450573, by rfl⟩ : syracuseStep 9201529 = 6901147) B6901147
theorem B12268705 : Blo 2153435 12268705 := bstep (se 2 (by rfl) ⟨4600764, by rfl⟩ : syracuseStep 12268705 = 9201529) B9201529
theorem B16358273 : Blo 2153435 16358273 := bstep (se 2 (by rfl) ⟨6134352, by rfl⟩ : syracuseStep 16358273 = 12268705) B12268705
theorem B10905515 : Blo 2153435 10905515 := bstep (se 1 (by rfl) ⟨8179136, by rfl⟩ : syracuseStep 10905515 = 16358273) B16358273
theorem B7270343 : Blo 2153435 7270343 := bstep (se 1 (by rfl) ⟨5452757, by rfl⟩ : syracuseStep 7270343 = 10905515) B10905515
theorem B4846895 : Blo 2153435 4846895 := bstep (se 1 (by rfl) ⟨3635171, by rfl⟩ : syracuseStep 4846895 = 7270343) B7270343
theorem B3231263 : Blo 2153435 3231263 := bstep (se 1 (by rfl) ⟨2423447, by rfl⟩ : syracuseStep 3231263 = 4846895) B4846895
theorem B2154175 : Blo 2153435 2154175 := bstep (se 1 (by rfl) ⟨1615631, by rfl⟩ : syracuseStep 2154175 = 3231263) B3231263
theorem B3231269 : Blo 2153435 3231269 := bbase (se 4 (by rfl) ⟨302931, by rfl⟩ : syracuseStep 3231269 = 605863) (by norm_num)
theorem B2154179 : Blo 2153435 2154179 := bstep (se 1 (by rfl) ⟨1615634, by rfl⟩ : syracuseStep 2154179 = 3231269) B3231269
theorem B2726389 : Blo 2153435 2726389 := bbase (se 5 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 2726389 = 255599) (by norm_num)
theorem B3635185 : Blo 2153435 3635185 := bstep (se 2 (by rfl) ⟨1363194, by rfl⟩ : syracuseStep 3635185 = 2726389) B2726389
theorem B4846913 : Blo 2153435 4846913 := bstep (se 2 (by rfl) ⟨1817592, by rfl⟩ : syracuseStep 4846913 = 3635185) B3635185
theorem B3231275 : Blo 2153435 3231275 := bstep (se 1 (by rfl) ⟨2423456, by rfl⟩ : syracuseStep 3231275 = 4846913) B4846913
theorem B2154183 : Blo 2153435 2154183 := bstep (se 1 (by rfl) ⟨1615637, by rfl⟩ : syracuseStep 2154183 = 3231275) B3231275
theorem B2423461 : Blo 2153435 2423461 := bbase (se 4 (by rfl) ⟨227199, by rfl⟩ : syracuseStep 2423461 = 454399) (by norm_num)
theorem B3231281 : Blo 2153435 3231281 := bstep (se 2 (by rfl) ⟨1211730, by rfl⟩ : syracuseStep 3231281 = 2423461) B2423461
theorem B2154187 : Blo 2153435 2154187 := bstep (se 1 (by rfl) ⟨1615640, by rfl⟩ : syracuseStep 2154187 = 3231281) B3231281
theorem B78608981 : Blo 2153435 78608981 := bbase (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) (by norm_num)
theorem B52405987 : Blo 2153435 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B69874649 : Blo 2153435 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B46583099 : Blo 2153435 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B31055399 : Blo 2153435 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B20703599 : Blo 2153435 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B13802399 : Blo 2153435 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B9201599 : Blo 2153435 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B6134399 : Blo 2153435 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B4089599 : Blo 2153435 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B2726399 : Blo 2153435 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B7270397 : Blo 2153435 7270397 := bstep (se 3 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 7270397 = 2726399) B2726399
theorem B4846931 : Blo 2153435 4846931 := bstep (se 1 (by rfl) ⟨3635198, by rfl⟩ : syracuseStep 4846931 = 7270397) B7270397
theorem B3231287 : Blo 2153435 3231287 := bstep (se 1 (by rfl) ⟨2423465, by rfl⟩ : syracuseStep 3231287 = 4846931) B4846931
theorem B2154191 : Blo 2153435 2154191 := bstep (se 1 (by rfl) ⟨1615643, by rfl⟩ : syracuseStep 2154191 = 3231287) B3231287
theorem B3231293 : Blo 2153435 3231293 := bbase (se 3 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 3231293 = 1211735) (by norm_num)
theorem B2154195 : Blo 2153435 2154195 := bstep (se 1 (by rfl) ⟨1615646, by rfl⟩ : syracuseStep 2154195 = 3231293) B3231293
theorem B4846949 : Blo 2153435 4846949 := bbase (se 4 (by rfl) ⟨454401, by rfl⟩ : syracuseStep 4846949 = 908803) (by norm_num)
theorem B3231299 : Blo 2153435 3231299 := bstep (se 1 (by rfl) ⟨2423474, by rfl⟩ : syracuseStep 3231299 = 4846949) B4846949
theorem B2154199 : Blo 2153435 2154199 := bstep (se 1 (by rfl) ⟨1615649, by rfl⟩ : syracuseStep 2154199 = 3231299) B3231299
theorem B5452829 : Blo 2153435 5452829 := bbase (se 3 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 5452829 = 2044811) (by norm_num)
theorem B3635219 : Blo 2153435 3635219 := bstep (se 1 (by rfl) ⟨2726414, by rfl⟩ : syracuseStep 3635219 = 5452829) B5452829
theorem B2423479 : Blo 2153435 2423479 := bstep (se 1 (by rfl) ⟨1817609, by rfl⟩ : syracuseStep 2423479 = 3635219) B3635219
theorem B3231305 : Blo 2153435 3231305 := bstep (se 2 (by rfl) ⟨1211739, by rfl⟩ : syracuseStep 3231305 = 2423479) B2423479
theorem B2154203 : Blo 2153435 2154203 := bstep (se 1 (by rfl) ⟨1615652, by rfl⟩ : syracuseStep 2154203 = 3231305) B3231305
theorem B4089629 : Blo 2153435 4089629 := bbase (se 3 (by rfl) ⟨766805, by rfl⟩ : syracuseStep 4089629 = 1533611) (by norm_num)
theorem B10905677 : Blo 2153435 10905677 := bstep (se 3 (by rfl) ⟨2044814, by rfl⟩ : syracuseStep 10905677 = 4089629) B4089629
theorem B7270451 : Blo 2153435 7270451 := bstep (se 1 (by rfl) ⟨5452838, by rfl⟩ : syracuseStep 7270451 = 10905677) B10905677
theorem B4846967 : Blo 2153435 4846967 := bstep (se 1 (by rfl) ⟨3635225, by rfl⟩ : syracuseStep 4846967 = 7270451) B7270451
theorem B3231311 : Blo 2153435 3231311 := bstep (se 1 (by rfl) ⟨2423483, by rfl⟩ : syracuseStep 3231311 = 4846967) B4846967
theorem B2154207 : Blo 2153435 2154207 := bstep (se 1 (by rfl) ⟨1615655, by rfl⟩ : syracuseStep 2154207 = 3231311) B3231311
theorem B3231317 : Blo 2153435 3231317 := bbase (se 8 (by rfl) ⟨18933, by rfl⟩ : syracuseStep 3231317 = 37867) (by norm_num)
theorem B2154211 : Blo 2153435 2154211 := bstep (se 1 (by rfl) ⟨1615658, by rfl⟩ : syracuseStep 2154211 = 3231317) B3231317
theorem B9201701 : Blo 2153435 9201701 := bbase (se 4 (by rfl) ⟨862659, by rfl⟩ : syracuseStep 9201701 = 1725319) (by norm_num)
theorem B6134467 : Blo 2153435 6134467 := bstep (se 1 (by rfl) ⟨4600850, by rfl⟩ : syracuseStep 6134467 = 9201701) B9201701
theorem B8179289 : Blo 2153435 8179289 := bstep (se 2 (by rfl) ⟨3067233, by rfl⟩ : syracuseStep 8179289 = 6134467) B6134467
theorem B5452859 : Blo 2153435 5452859 := bstep (se 1 (by rfl) ⟨4089644, by rfl⟩ : syracuseStep 5452859 = 8179289) B8179289
theorem B3635239 : Blo 2153435 3635239 := bstep (se 1 (by rfl) ⟨2726429, by rfl⟩ : syracuseStep 3635239 = 5452859) B5452859
theorem B4846985 : Blo 2153435 4846985 := bstep (se 2 (by rfl) ⟨1817619, by rfl⟩ : syracuseStep 4846985 = 3635239) B3635239
theorem B3231323 : Blo 2153435 3231323 := bstep (se 1 (by rfl) ⟨2423492, by rfl⟩ : syracuseStep 3231323 = 4846985) B4846985
theorem B2154215 : Blo 2153435 2154215 := bstep (se 1 (by rfl) ⟨1615661, by rfl⟩ : syracuseStep 2154215 = 3231323) B3231323
theorem B2423497 : Blo 2153435 2423497 := bbase (se 2 (by rfl) ⟨908811, by rfl⟩ : syracuseStep 2423497 = 1817623) (by norm_num)
theorem B3231329 : Blo 2153435 3231329 := bstep (se 2 (by rfl) ⟨1211748, by rfl⟩ : syracuseStep 3231329 = 2423497) B2423497
theorem B2154219 : Blo 2153435 2154219 := bstep (se 1 (by rfl) ⟨1615664, by rfl⟩ : syracuseStep 2154219 = 3231329) B3231329
theorem B6901301 : Blo 2153435 6901301 := bbase (se 5 (by rfl) ⟨323498, by rfl⟩ : syracuseStep 6901301 = 646997) (by norm_num)
theorem B18403469 : Blo 2153435 18403469 := bstep (se 3 (by rfl) ⟨3450650, by rfl⟩ : syracuseStep 18403469 = 6901301) B6901301
theorem B12268979 : Blo 2153435 12268979 := bstep (se 1 (by rfl) ⟨9201734, by rfl⟩ : syracuseStep 12268979 = 18403469) B18403469
theorem B8179319 : Blo 2153435 8179319 := bstep (se 1 (by rfl) ⟨6134489, by rfl⟩ : syracuseStep 8179319 = 12268979) B12268979
theorem B5452879 : Blo 2153435 5452879 := bstep (se 1 (by rfl) ⟨4089659, by rfl⟩ : syracuseStep 5452879 = 8179319) B8179319
theorem B7270505 : Blo 2153435 7270505 := bstep (se 2 (by rfl) ⟨2726439, by rfl⟩ : syracuseStep 7270505 = 5452879) B5452879
theorem B4847003 : Blo 2153435 4847003 := bstep (se 1 (by rfl) ⟨3635252, by rfl⟩ : syracuseStep 4847003 = 7270505) B7270505
theorem B3231335 : Blo 2153435 3231335 := bstep (se 1 (by rfl) ⟨2423501, by rfl⟩ : syracuseStep 3231335 = 4847003) B4847003
theorem B2154223 : Blo 2153435 2154223 := bstep (se 1 (by rfl) ⟨1615667, by rfl⟩ : syracuseStep 2154223 = 3231335) B3231335
theorem B3231341 : Blo 2153435 3231341 := bbase (se 3 (by rfl) ⟨605876, by rfl⟩ : syracuseStep 3231341 = 1211753) (by norm_num)
theorem B2154227 : Blo 2153435 2154227 := bstep (se 1 (by rfl) ⟨1615670, by rfl⟩ : syracuseStep 2154227 = 3231341) B3231341
theorem B4847021 : Blo 2153435 4847021 := bbase (se 3 (by rfl) ⟨908816, by rfl⟩ : syracuseStep 4847021 = 1817633) (by norm_num)
theorem B3231347 : Blo 2153435 3231347 := bstep (se 1 (by rfl) ⟨2423510, by rfl⟩ : syracuseStep 3231347 = 4847021) B4847021
theorem B2154231 : Blo 2153435 2154231 := bstep (se 1 (by rfl) ⟨1615673, by rfl⟩ : syracuseStep 2154231 = 3231347) B3231347
theorem B6550885 : Blo 2153435 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B8734513 : Blo 2153435 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B11646017 : Blo 2153435 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B7764011 : Blo 2153435 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B5176007 : Blo 2153435 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B3450671 : Blo 2153435 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B2300447 : Blo 2153435 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B6134525 : Blo 2153435 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B4089683 : Blo 2153435 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B2726455 : Blo 2153435 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B3635273 : Blo 2153435 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B2423515 : Blo 2153435 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B3231353 : Blo 2153435 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B2154235 : Blo 2153435 2154235 := bstep (se 1 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 2154235 = 3231353) B3231353
theorem B27982037 : Blo 2153435 27982037 := bbase (se 7 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 27982037 = 655829) (by norm_num)
theorem B74618765 : Blo 2153435 74618765 := bstep (se 3 (by rfl) ⟨13991018, by rfl⟩ : syracuseStep 74618765 = 27982037) B27982037
theorem B49745843 : Blo 2153435 49745843 := bstep (se 1 (by rfl) ⟨37309382, by rfl⟩ : syracuseStep 49745843 = 74618765) B74618765
theorem B33163895 : Blo 2153435 33163895 := bstep (se 1 (by rfl) ⟨24872921, by rfl⟩ : syracuseStep 33163895 = 49745843) B49745843
theorem B22109263 : Blo 2153435 22109263 := bstep (se 1 (by rfl) ⟨16581947, by rfl⟩ : syracuseStep 22109263 = 33163895) B33163895
theorem B117916069 : Blo 2153435 117916069 := bstep (se 4 (by rfl) ⟨11054631, by rfl⟩ : syracuseStep 117916069 = 22109263) B22109263
theorem B157221425 : Blo 2153435 157221425 := bstep (se 2 (by rfl) ⟨58958034, by rfl⟩ : syracuseStep 157221425 = 117916069) B117916069
theorem B104814283 : Blo 2153435 104814283 := bstep (se 1 (by rfl) ⟨78610712, by rfl⟩ : syracuseStep 104814283 = 157221425) B157221425
theorem B139752377 : Blo 2153435 139752377 := bstep (se 2 (by rfl) ⟨52407141, by rfl⟩ : syracuseStep 139752377 = 104814283) B104814283
theorem B93168251 : Blo 2153435 93168251 := bstep (se 1 (by rfl) ⟨69876188, by rfl⟩ : syracuseStep 93168251 = 139752377) B139752377
theorem B62112167 : Blo 2153435 62112167 := bstep (se 1 (by rfl) ⟨46584125, by rfl⟩ : syracuseStep 62112167 = 93168251) B93168251
theorem B41408111 : Blo 2153435 41408111 := bstep (se 1 (by rfl) ⟨31056083, by rfl⟩ : syracuseStep 41408111 = 62112167) B62112167
theorem B27605407 : Blo 2153435 27605407 := bstep (se 1 (by rfl) ⟨20704055, by rfl⟩ : syracuseStep 27605407 = 41408111) B41408111
theorem B36807209 : Blo 2153435 36807209 := bstep (se 2 (by rfl) ⟨13802703, by rfl⟩ : syracuseStep 36807209 = 27605407) B27605407
theorem B24538139 : Blo 2153435 24538139 := bstep (se 1 (by rfl) ⟨18403604, by rfl⟩ : syracuseStep 24538139 = 36807209) B36807209
theorem B16358759 : Blo 2153435 16358759 := bstep (se 1 (by rfl) ⟨12269069, by rfl⟩ : syracuseStep 16358759 = 24538139) B24538139
theorem B10905839 : Blo 2153435 10905839 := bstep (se 1 (by rfl) ⟨8179379, by rfl⟩ : syracuseStep 10905839 = 16358759) B16358759
theorem B7270559 : Blo 2153435 7270559 := bstep (se 1 (by rfl) ⟨5452919, by rfl⟩ : syracuseStep 7270559 = 10905839) B10905839
theorem B4847039 : Blo 2153435 4847039 := bstep (se 1 (by rfl) ⟨3635279, by rfl⟩ : syracuseStep 4847039 = 7270559) B7270559
theorem B3231359 : Blo 2153435 3231359 := bstep (se 1 (by rfl) ⟨2423519, by rfl⟩ : syracuseStep 3231359 = 4847039) B4847039
theorem B2154239 : Blo 2153435 2154239 := bstep (se 1 (by rfl) ⟨1615679, by rfl⟩ : syracuseStep 2154239 = 3231359) B3231359
theorem B3231365 : Blo 2153435 3231365 := bbase (se 4 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 3231365 = 605881) (by norm_num)
theorem B2154243 : Blo 2153435 2154243 := bstep (se 1 (by rfl) ⟨1615682, by rfl⟩ : syracuseStep 2154243 = 3231365) B3231365
theorem B3635293 : Blo 2153435 3635293 := bbase (se 3 (by rfl) ⟨681617, by rfl⟩ : syracuseStep 3635293 = 1363235) (by norm_num)
theorem B4847057 : Blo 2153435 4847057 := bstep (se 2 (by rfl) ⟨1817646, by rfl⟩ : syracuseStep 4847057 = 3635293) B3635293
theorem B3231371 : Blo 2153435 3231371 := bstep (se 1 (by rfl) ⟨2423528, by rfl⟩ : syracuseStep 3231371 = 4847057) B4847057
theorem B2154247 : Blo 2153435 2154247 := bstep (se 1 (by rfl) ⟨1615685, by rfl⟩ : syracuseStep 2154247 = 3231371) B3231371
theorem B2423533 : Blo 2153435 2423533 := bbase (se 3 (by rfl) ⟨454412, by rfl⟩ : syracuseStep 2423533 = 908825) (by norm_num)
theorem B3231377 : Blo 2153435 3231377 := bstep (se 2 (by rfl) ⟨1211766, by rfl⟩ : syracuseStep 3231377 = 2423533) B2423533
theorem B2154251 : Blo 2153435 2154251 := bstep (se 1 (by rfl) ⟨1615688, by rfl⟩ : syracuseStep 2154251 = 3231377) B3231377
theorem B7270613 : Blo 2153435 7270613 := bbase (se 7 (by rfl) ⟨85202, by rfl⟩ : syracuseStep 7270613 = 170405) (by norm_num)
theorem B4847075 : Blo 2153435 4847075 := bstep (se 1 (by rfl) ⟨3635306, by rfl⟩ : syracuseStep 4847075 = 7270613) B7270613
theorem B3231383 : Blo 2153435 3231383 := bstep (se 1 (by rfl) ⟨2423537, by rfl⟩ : syracuseStep 3231383 = 4847075) B4847075
theorem B2154255 : Blo 2153435 2154255 := bstep (se 1 (by rfl) ⟨1615691, by rfl⟩ : syracuseStep 2154255 = 3231383) B3231383
theorem B3231389 : Blo 2153435 3231389 := bbase (se 3 (by rfl) ⟨605885, by rfl⟩ : syracuseStep 3231389 = 1211771) (by norm_num)
theorem B2154259 : Blo 2153435 2154259 := bstep (se 1 (by rfl) ⟨1615694, by rfl⟩ : syracuseStep 2154259 = 3231389) B3231389
theorem B4847093 : Blo 2153435 4847093 := bbase (se 5 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 4847093 = 454415) (by norm_num)
theorem B3231395 : Blo 2153435 3231395 := bstep (se 1 (by rfl) ⟨2423546, by rfl⟩ : syracuseStep 3231395 = 4847093) B4847093
theorem B2154263 : Blo 2153435 2154263 := bstep (se 1 (by rfl) ⟨1615697, by rfl⟩ : syracuseStep 2154263 = 3231395) B3231395
theorem B22109557 : Blo 2153435 22109557 := bbase (se 5 (by rfl) ⟨1036385, by rfl⟩ : syracuseStep 22109557 = 2072771) (by norm_num)
theorem B29479409 : Blo 2153435 29479409 := bstep (se 2 (by rfl) ⟨11054778, by rfl⟩ : syracuseStep 29479409 = 22109557) B22109557
theorem B19652939 : Blo 2153435 19652939 := bstep (se 1 (by rfl) ⟨14739704, by rfl⟩ : syracuseStep 19652939 = 29479409) B29479409
theorem B13101959 : Blo 2153435 13101959 := bstep (se 1 (by rfl) ⟨9826469, by rfl⟩ : syracuseStep 13101959 = 19652939) B19652939
theorem B8734639 : Blo 2153435 8734639 := bstep (se 1 (by rfl) ⟨6550979, by rfl⟩ : syracuseStep 8734639 = 13101959) B13101959
theorem B11646185 : Blo 2153435 11646185 := bstep (se 2 (by rfl) ⟨4367319, by rfl⟩ : syracuseStep 11646185 = 8734639) B8734639
theorem B31056493 : Blo 2153435 31056493 := bstep (se 3 (by rfl) ⟨5823092, by rfl⟩ : syracuseStep 31056493 = 11646185) B11646185
theorem B41408657 : Blo 2153435 41408657 := bstep (se 2 (by rfl) ⟨15528246, by rfl⟩ : syracuseStep 41408657 = 31056493) B31056493
theorem B27605771 : Blo 2153435 27605771 := bstep (se 1 (by rfl) ⟨20704328, by rfl⟩ : syracuseStep 27605771 = 41408657) B41408657
theorem B18403847 : Blo 2153435 18403847 := bstep (se 1 (by rfl) ⟨13802885, by rfl⟩ : syracuseStep 18403847 = 27605771) B27605771
theorem B12269231 : Blo 2153435 12269231 := bstep (se 1 (by rfl) ⟨9201923, by rfl⟩ : syracuseStep 12269231 = 18403847) B18403847
theorem B8179487 : Blo 2153435 8179487 := bstep (se 1 (by rfl) ⟨6134615, by rfl⟩ : syracuseStep 8179487 = 12269231) B12269231
theorem B5452991 : Blo 2153435 5452991 := bstep (se 1 (by rfl) ⟨4089743, by rfl⟩ : syracuseStep 5452991 = 8179487) B8179487
theorem B3635327 : Blo 2153435 3635327 := bstep (se 1 (by rfl) ⟨2726495, by rfl⟩ : syracuseStep 3635327 = 5452991) B5452991
theorem B2423551 : Blo 2153435 2423551 := bstep (se 1 (by rfl) ⟨1817663, by rfl⟩ : syracuseStep 2423551 = 3635327) B3635327
theorem B3231401 : Blo 2153435 3231401 := bstep (se 2 (by rfl) ⟨1211775, by rfl⟩ : syracuseStep 3231401 = 2423551) B2423551
theorem B2154267 : Blo 2153435 2154267 := bstep (se 1 (by rfl) ⟨1615700, by rfl⟩ : syracuseStep 2154267 = 3231401) B3231401
theorem B2300485 : Blo 2153435 2300485 := bbase (se 4 (by rfl) ⟨215670, by rfl⟩ : syracuseStep 2300485 = 431341) (by norm_num)
theorem B3067313 : Blo 2153435 3067313 := bstep (se 2 (by rfl) ⟨1150242, by rfl⟩ : syracuseStep 3067313 = 2300485) B2300485
theorem B8179501 : Blo 2153435 8179501 := bstep (se 3 (by rfl) ⟨1533656, by rfl⟩ : syracuseStep 8179501 = 3067313) B3067313
theorem B10906001 : Blo 2153435 10906001 := bstep (se 2 (by rfl) ⟨4089750, by rfl⟩ : syracuseStep 10906001 = 8179501) B8179501
theorem B7270667 : Blo 2153435 7270667 := bstep (se 1 (by rfl) ⟨5453000, by rfl⟩ : syracuseStep 7270667 = 10906001) B10906001
theorem B4847111 : Blo 2153435 4847111 := bstep (se 1 (by rfl) ⟨3635333, by rfl⟩ : syracuseStep 4847111 = 7270667) B7270667
theorem B3231407 : Blo 2153435 3231407 := bstep (se 1 (by rfl) ⟨2423555, by rfl⟩ : syracuseStep 3231407 = 4847111) B4847111
theorem B2154271 : Blo 2153435 2154271 := bstep (se 1 (by rfl) ⟨1615703, by rfl⟩ : syracuseStep 2154271 = 3231407) B3231407
theorem B3231413 : Blo 2153435 3231413 := bbase (se 5 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 3231413 = 302945) (by norm_num)
theorem B2154275 : Blo 2153435 2154275 := bstep (se 1 (by rfl) ⟨1615706, by rfl⟩ : syracuseStep 2154275 = 3231413) B3231413
theorem B5453021 : Blo 2153435 5453021 := bbase (se 3 (by rfl) ⟨1022441, by rfl⟩ : syracuseStep 5453021 = 2044883) (by norm_num)
theorem B3635347 : Blo 2153435 3635347 := bstep (se 1 (by rfl) ⟨2726510, by rfl⟩ : syracuseStep 3635347 = 5453021) B5453021
theorem B4847129 : Blo 2153435 4847129 := bstep (se 2 (by rfl) ⟨1817673, by rfl⟩ : syracuseStep 4847129 = 3635347) B3635347
theorem B3231419 : Blo 2153435 3231419 := bstep (se 1 (by rfl) ⟨2423564, by rfl⟩ : syracuseStep 3231419 = 4847129) B4847129
theorem B2154279 : Blo 2153435 2154279 := bstep (se 1 (by rfl) ⟨1615709, by rfl⟩ : syracuseStep 2154279 = 3231419) B3231419
theorem B2423569 : Blo 2153435 2423569 := bbase (se 2 (by rfl) ⟨908838, by rfl⟩ : syracuseStep 2423569 = 1817677) (by norm_num)
theorem B3231425 : Blo 2153435 3231425 := bstep (se 2 (by rfl) ⟨1211784, by rfl⟩ : syracuseStep 3231425 = 2423569) B2423569
theorem B2154283 : Blo 2153435 2154283 := bstep (se 1 (by rfl) ⟨1615712, by rfl⟩ : syracuseStep 2154283 = 3231425) B3231425
theorem B4089781 : Blo 2153435 4089781 := bbase (se 5 (by rfl) ⟨191708, by rfl⟩ : syracuseStep 4089781 = 383417) (by norm_num)
theorem B5453041 : Blo 2153435 5453041 := bstep (se 2 (by rfl) ⟨2044890, by rfl⟩ : syracuseStep 5453041 = 4089781) B4089781
theorem B7270721 : Blo 2153435 7270721 := bstep (se 2 (by rfl) ⟨2726520, by rfl⟩ : syracuseStep 7270721 = 5453041) B5453041
theorem B4847147 : Blo 2153435 4847147 := bstep (se 1 (by rfl) ⟨3635360, by rfl⟩ : syracuseStep 4847147 = 7270721) B7270721
theorem B3231431 : Blo 2153435 3231431 := bstep (se 1 (by rfl) ⟨2423573, by rfl⟩ : syracuseStep 3231431 = 4847147) B4847147
theorem B2154287 : Blo 2153435 2154287 := bstep (se 1 (by rfl) ⟨1615715, by rfl⟩ : syracuseStep 2154287 = 3231431) B3231431
theorem B3231437 : Blo 2153435 3231437 := bbase (se 3 (by rfl) ⟨605894, by rfl⟩ : syracuseStep 3231437 = 1211789) (by norm_num)
theorem B2154291 : Blo 2153435 2154291 := bstep (se 1 (by rfl) ⟨1615718, by rfl⟩ : syracuseStep 2154291 = 3231437) B3231437
theorem B4847165 : Blo 2153435 4847165 := bbase (se 3 (by rfl) ⟨908843, by rfl⟩ : syracuseStep 4847165 = 1817687) (by norm_num)
theorem B3231443 : Blo 2153435 3231443 := bstep (se 1 (by rfl) ⟨2423582, by rfl⟩ : syracuseStep 3231443 = 4847165) B4847165
theorem B2154295 : Blo 2153435 2154295 := bstep (se 1 (by rfl) ⟨1615721, by rfl⟩ : syracuseStep 2154295 = 3231443) B3231443
theorem B3635381 : Blo 2153435 3635381 := bbase (se 5 (by rfl) ⟨170408, by rfl⟩ : syracuseStep 3635381 = 340817) (by norm_num)
theorem B2423587 : Blo 2153435 2423587 := bstep (se 1 (by rfl) ⟨1817690, by rfl⟩ : syracuseStep 2423587 = 3635381) B3635381
theorem B3231449 : Blo 2153435 3231449 := bstep (se 2 (by rfl) ⟨1211793, by rfl⟩ : syracuseStep 3231449 = 2423587) B2423587
theorem B2154299 : Blo 2153435 2154299 := bstep (se 1 (by rfl) ⟨1615724, by rfl⟩ : syracuseStep 2154299 = 3231449) B3231449
theorem B3684989 : Blo 2153435 3684989 := bbase (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) (by norm_num)
theorem B2456659 : Blo 2153435 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B13102181 : Blo 2153435 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B8734787 : Blo 2153435 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B5823191 : Blo 2153435 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B3882127 : Blo 2153435 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B5176169 : Blo 2153435 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B3450779 : Blo 2153435 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B2300519 : Blo 2153435 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B6134717 : Blo 2153435 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B16359245 : Blo 2153435 16359245 := bstep (se 3 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 16359245 = 6134717) B6134717
theorem B10906163 : Blo 2153435 10906163 := bstep (se 1 (by rfl) ⟨8179622, by rfl⟩ : syracuseStep 10906163 = 16359245) B16359245
theorem B7270775 : Blo 2153435 7270775 := bstep (se 1 (by rfl) ⟨5453081, by rfl⟩ : syracuseStep 7270775 = 10906163) B10906163
theorem B4847183 : Blo 2153435 4847183 := bstep (se 1 (by rfl) ⟨3635387, by rfl⟩ : syracuseStep 4847183 = 7270775) B7270775
theorem B3231455 : Blo 2153435 3231455 := bstep (se 1 (by rfl) ⟨2423591, by rfl⟩ : syracuseStep 3231455 = 4847183) B4847183
theorem B2154303 : Blo 2153435 2154303 := bstep (se 1 (by rfl) ⟨1615727, by rfl⟩ : syracuseStep 2154303 = 3231455) B3231455
theorem B3231461 : Blo 2153435 3231461 := bbase (se 4 (by rfl) ⟨302949, by rfl⟩ : syracuseStep 3231461 = 605899) (by norm_num)
theorem B2154307 : Blo 2153435 2154307 := bstep (se 1 (by rfl) ⟨1615730, by rfl⟩ : syracuseStep 2154307 = 3231461) B3231461
theorem B6134741 : Blo 2153435 6134741 := bbase (se 7 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 6134741 = 143783) (by norm_num)
theorem B4089827 : Blo 2153435 4089827 := bstep (se 1 (by rfl) ⟨3067370, by rfl⟩ : syracuseStep 4089827 = 6134741) B6134741
theorem B2726551 : Blo 2153435 2726551 := bstep (se 1 (by rfl) ⟨2044913, by rfl⟩ : syracuseStep 2726551 = 4089827) B4089827
theorem B3635401 : Blo 2153435 3635401 := bstep (se 2 (by rfl) ⟨1363275, by rfl⟩ : syracuseStep 3635401 = 2726551) B2726551
theorem B4847201 : Blo 2153435 4847201 := bstep (se 2 (by rfl) ⟨1817700, by rfl⟩ : syracuseStep 4847201 = 3635401) B3635401
theorem B3231467 : Blo 2153435 3231467 := bstep (se 1 (by rfl) ⟨2423600, by rfl⟩ : syracuseStep 3231467 = 4847201) B4847201
theorem B2154311 : Blo 2153435 2154311 := bstep (se 1 (by rfl) ⟨1615733, by rfl⟩ : syracuseStep 2154311 = 3231467) B3231467
theorem B2423605 : Blo 2153435 2423605 := bbase (se 5 (by rfl) ⟨113606, by rfl⟩ : syracuseStep 2423605 = 227213) (by norm_num)
theorem B3231473 : Blo 2153435 3231473 := bstep (se 2 (by rfl) ⟨1211802, by rfl⟩ : syracuseStep 3231473 = 2423605) B2423605
theorem B2154315 : Blo 2153435 2154315 := bstep (se 1 (by rfl) ⟨1615736, by rfl⟩ : syracuseStep 2154315 = 3231473) B3231473
theorem B2726561 : Blo 2153435 2726561 := bbase (se 2 (by rfl) ⟨1022460, by rfl⟩ : syracuseStep 2726561 = 2044921) (by norm_num)
theorem B7270829 : Blo 2153435 7270829 := bstep (se 3 (by rfl) ⟨1363280, by rfl⟩ : syracuseStep 7270829 = 2726561) B2726561
theorem B4847219 : Blo 2153435 4847219 := bstep (se 1 (by rfl) ⟨3635414, by rfl⟩ : syracuseStep 4847219 = 7270829) B7270829
theorem B3231479 : Blo 2153435 3231479 := bstep (se 1 (by rfl) ⟨2423609, by rfl⟩ : syracuseStep 3231479 = 4847219) B4847219
theorem B2154319 : Blo 2153435 2154319 := bstep (se 1 (by rfl) ⟨1615739, by rfl⟩ : syracuseStep 2154319 = 3231479) B3231479
theorem B3231485 : Blo 2153435 3231485 := bbase (se 3 (by rfl) ⟨605903, by rfl⟩ : syracuseStep 3231485 = 1211807) (by norm_num)
theorem B2154323 : Blo 2153435 2154323 := bstep (se 1 (by rfl) ⟨1615742, by rfl⟩ : syracuseStep 2154323 = 3231485) B3231485
theorem B4847237 : Blo 2153435 4847237 := bbase (se 4 (by rfl) ⟨454428, by rfl⟩ : syracuseStep 4847237 = 908857) (by norm_num)
theorem B3231491 : Blo 2153435 3231491 := bstep (se 1 (by rfl) ⟨2423618, by rfl⟩ : syracuseStep 3231491 = 4847237) B4847237
theorem B2154327 : Blo 2153435 2154327 := bstep (se 1 (by rfl) ⟨1615745, by rfl⟩ : syracuseStep 2154327 = 3231491) B3231491
theorem B5176237 : Blo 2153435 5176237 := bbase (se 3 (by rfl) ⟨970544, by rfl⟩ : syracuseStep 5176237 = 1941089) (by norm_num)
theorem B6901649 : Blo 2153435 6901649 := bstep (se 2 (by rfl) ⟨2588118, by rfl⟩ : syracuseStep 6901649 = 5176237) B5176237
theorem B4601099 : Blo 2153435 4601099 := bstep (se 1 (by rfl) ⟨3450824, by rfl⟩ : syracuseStep 4601099 = 6901649) B6901649
theorem B3067399 : Blo 2153435 3067399 := bstep (se 1 (by rfl) ⟨2300549, by rfl⟩ : syracuseStep 3067399 = 4601099) B4601099
theorem B4089865 : Blo 2153435 4089865 := bstep (se 2 (by rfl) ⟨1533699, by rfl⟩ : syracuseStep 4089865 = 3067399) B3067399
theorem B5453153 : Blo 2153435 5453153 := bstep (se 2 (by rfl) ⟨2044932, by rfl⟩ : syracuseStep 5453153 = 4089865) B4089865
theorem B3635435 : Blo 2153435 3635435 := bstep (se 1 (by rfl) ⟨2726576, by rfl⟩ : syracuseStep 3635435 = 5453153) B5453153
theorem B2423623 : Blo 2153435 2423623 := bstep (se 1 (by rfl) ⟨1817717, by rfl⟩ : syracuseStep 2423623 = 3635435) B3635435
theorem B3231497 : Blo 2153435 3231497 := bstep (se 2 (by rfl) ⟨1211811, by rfl⟩ : syracuseStep 3231497 = 2423623) B2423623
theorem B2154331 : Blo 2153435 2154331 := bstep (se 1 (by rfl) ⟨1615748, by rfl⟩ : syracuseStep 2154331 = 3231497) B3231497
theorem B10906325 : Blo 2153435 10906325 := bbase (se 7 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 10906325 = 255617) (by norm_num)
theorem B7270883 : Blo 2153435 7270883 := bstep (se 1 (by rfl) ⟨5453162, by rfl⟩ : syracuseStep 7270883 = 10906325) B10906325
theorem B4847255 : Blo 2153435 4847255 := bstep (se 1 (by rfl) ⟨3635441, by rfl⟩ : syracuseStep 4847255 = 7270883) B7270883
theorem B3231503 : Blo 2153435 3231503 := bstep (se 1 (by rfl) ⟨2423627, by rfl⟩ : syracuseStep 3231503 = 4847255) B4847255
theorem B2154335 : Blo 2153435 2154335 := bstep (se 1 (by rfl) ⟨1615751, by rfl⟩ : syracuseStep 2154335 = 3231503) B3231503
theorem B3231509 : Blo 2153435 3231509 := bbase (se 6 (by rfl) ⟨75738, by rfl⟩ : syracuseStep 3231509 = 151477) (by norm_num)
theorem B2154339 : Blo 2153435 2154339 := bstep (se 1 (by rfl) ⟨1615754, by rfl⟩ : syracuseStep 2154339 = 3231509) B3231509
theorem B3275605 : Blo 2153435 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B17469893 : Blo 2153435 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B11646595 : Blo 2153435 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B62115173 : Blo 2153435 62115173 := bstep (se 4 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 62115173 = 11646595) B11646595
theorem B41410115 : Blo 2153435 41410115 := bstep (se 1 (by rfl) ⟨31057586, by rfl⟩ : syracuseStep 41410115 = 62115173) B62115173
theorem B27606743 : Blo 2153435 27606743 := bstep (se 1 (by rfl) ⟨20705057, by rfl⟩ : syracuseStep 27606743 = 41410115) B41410115
theorem B18404495 : Blo 2153435 18404495 := bstep (se 1 (by rfl) ⟨13803371, by rfl⟩ : syracuseStep 18404495 = 27606743) B27606743
theorem B12269663 : Blo 2153435 12269663 := bstep (se 1 (by rfl) ⟨9202247, by rfl⟩ : syracuseStep 12269663 = 18404495) B18404495
theorem B8179775 : Blo 2153435 8179775 := bstep (se 1 (by rfl) ⟨6134831, by rfl⟩ : syracuseStep 8179775 = 12269663) B12269663
theorem B5453183 : Blo 2153435 5453183 := bstep (se 1 (by rfl) ⟨4089887, by rfl⟩ : syracuseStep 5453183 = 8179775) B8179775
theorem B3635455 : Blo 2153435 3635455 := bstep (se 1 (by rfl) ⟨2726591, by rfl⟩ : syracuseStep 3635455 = 5453183) B5453183
theorem B4847273 : Blo 2153435 4847273 := bstep (se 2 (by rfl) ⟨1817727, by rfl⟩ : syracuseStep 4847273 = 3635455) B3635455
theorem B3231515 : Blo 2153435 3231515 := bstep (se 1 (by rfl) ⟨2423636, by rfl⟩ : syracuseStep 3231515 = 4847273) B4847273
theorem B2154343 : Blo 2153435 2154343 := bstep (se 1 (by rfl) ⟨1615757, by rfl⟩ : syracuseStep 2154343 = 3231515) B3231515
theorem B2423641 : Blo 2153435 2423641 := bbase (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) (by norm_num)
theorem B3231521 : Blo 2153435 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B2154347 : Blo 2153435 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B4601141 : Blo 2153435 4601141 := bbase (se 5 (by rfl) ⟨215678, by rfl⟩ : syracuseStep 4601141 = 431357) (by norm_num)
theorem B3067427 : Blo 2153435 3067427 := bstep (se 1 (by rfl) ⟨2300570, by rfl⟩ : syracuseStep 3067427 = 4601141) B4601141
theorem B8179805 : Blo 2153435 8179805 := bstep (se 3 (by rfl) ⟨1533713, by rfl⟩ : syracuseStep 8179805 = 3067427) B3067427
theorem B5453203 : Blo 2153435 5453203 := bstep (se 1 (by rfl) ⟨4089902, by rfl⟩ : syracuseStep 5453203 = 8179805) B8179805
theorem B7270937 : Blo 2153435 7270937 := bstep (se 2 (by rfl) ⟨2726601, by rfl⟩ : syracuseStep 7270937 = 5453203) B5453203
theorem B4847291 : Blo 2153435 4847291 := bstep (se 1 (by rfl) ⟨3635468, by rfl⟩ : syracuseStep 4847291 = 7270937) B7270937
theorem B3231527 : Blo 2153435 3231527 := bstep (se 1 (by rfl) ⟨2423645, by rfl⟩ : syracuseStep 3231527 = 4847291) B4847291
theorem B2154351 : Blo 2153435 2154351 := bstep (se 1 (by rfl) ⟨1615763, by rfl⟩ : syracuseStep 2154351 = 3231527) B3231527
theorem B3231533 : Blo 2153435 3231533 := bbase (se 3 (by rfl) ⟨605912, by rfl⟩ : syracuseStep 3231533 = 1211825) (by norm_num)
theorem B2154355 : Blo 2153435 2154355 := bstep (se 1 (by rfl) ⟨1615766, by rfl⟩ : syracuseStep 2154355 = 3231533) B3231533
theorem B4847309 : Blo 2153435 4847309 := bbase (se 3 (by rfl) ⟨908870, by rfl⟩ : syracuseStep 4847309 = 1817741) (by norm_num)
theorem B3231539 : Blo 2153435 3231539 := bstep (se 1 (by rfl) ⟨2423654, by rfl⟩ : syracuseStep 3231539 = 4847309) B4847309
theorem B2154359 : Blo 2153435 2154359 := bstep (se 1 (by rfl) ⟨1615769, by rfl⟩ : syracuseStep 2154359 = 3231539) B3231539
theorem B2726617 : Blo 2153435 2726617 := bbase (se 2 (by rfl) ⟨1022481, by rfl⟩ : syracuseStep 2726617 = 2044963) (by norm_num)
theorem B3635489 : Blo 2153435 3635489 := bstep (se 2 (by rfl) ⟨1363308, by rfl⟩ : syracuseStep 3635489 = 2726617) B2726617
theorem B2423659 : Blo 2153435 2423659 := bstep (se 1 (by rfl) ⟨1817744, by rfl⟩ : syracuseStep 2423659 = 3635489) B3635489
theorem B3231545 : Blo 2153435 3231545 := bstep (se 2 (by rfl) ⟨1211829, by rfl⟩ : syracuseStep 3231545 = 2423659) B2423659
theorem B2154363 : Blo 2153435 2154363 := bstep (se 1 (by rfl) ⟨1615772, by rfl⟩ : syracuseStep 2154363 = 3231545) B3231545
theorem B2588161 : Blo 2153435 2588161 := bbase (se 2 (by rfl) ⟨970560, by rfl⟩ : syracuseStep 2588161 = 1941121) (by norm_num)
theorem B3450881 : Blo 2153435 3450881 := bstep (se 2 (by rfl) ⟨1294080, by rfl⟩ : syracuseStep 3450881 = 2588161) B2588161
theorem B9202349 : Blo 2153435 9202349 := bstep (se 3 (by rfl) ⟨1725440, by rfl⟩ : syracuseStep 9202349 = 3450881) B3450881
theorem B24539597 : Blo 2153435 24539597 := bstep (se 3 (by rfl) ⟨4601174, by rfl⟩ : syracuseStep 24539597 = 9202349) B9202349
theorem B16359731 : Blo 2153435 16359731 := bstep (se 1 (by rfl) ⟨12269798, by rfl⟩ : syracuseStep 16359731 = 24539597) B24539597
theorem B10906487 : Blo 2153435 10906487 := bstep (se 1 (by rfl) ⟨8179865, by rfl⟩ : syracuseStep 10906487 = 16359731) B16359731
theorem B7270991 : Blo 2153435 7270991 := bstep (se 1 (by rfl) ⟨5453243, by rfl⟩ : syracuseStep 7270991 = 10906487) B10906487
theorem B4847327 : Blo 2153435 4847327 := bstep (se 1 (by rfl) ⟨3635495, by rfl⟩ : syracuseStep 4847327 = 7270991) B7270991
theorem B3231551 : Blo 2153435 3231551 := bstep (se 1 (by rfl) ⟨2423663, by rfl⟩ : syracuseStep 3231551 = 4847327) B4847327
theorem B2154367 : Blo 2153435 2154367 := bstep (se 1 (by rfl) ⟨1615775, by rfl⟩ : syracuseStep 2154367 = 3231551) B3231551
theorem B3231557 : Blo 2153435 3231557 := bbase (se 4 (by rfl) ⟨302958, by rfl⟩ : syracuseStep 3231557 = 605917) (by norm_num)
theorem B2154371 : Blo 2153435 2154371 := bstep (se 1 (by rfl) ⟨1615778, by rfl⟩ : syracuseStep 2154371 = 3231557) B3231557
theorem B3635509 : Blo 2153435 3635509 := bbase (se 5 (by rfl) ⟨170414, by rfl⟩ : syracuseStep 3635509 = 340829) (by norm_num)
theorem B4847345 : Blo 2153435 4847345 := bstep (se 2 (by rfl) ⟨1817754, by rfl⟩ : syracuseStep 4847345 = 3635509) B3635509
theorem B3231563 : Blo 2153435 3231563 := bstep (se 1 (by rfl) ⟨2423672, by rfl⟩ : syracuseStep 3231563 = 4847345) B4847345
theorem B2154375 : Blo 2153435 2154375 := bstep (se 1 (by rfl) ⟨1615781, by rfl⟩ : syracuseStep 2154375 = 3231563) B3231563
theorem B2423677 : Blo 2153435 2423677 := bbase (se 3 (by rfl) ⟨454439, by rfl⟩ : syracuseStep 2423677 = 908879) (by norm_num)
theorem B3231569 : Blo 2153435 3231569 := bstep (se 2 (by rfl) ⟨1211838, by rfl⟩ : syracuseStep 3231569 = 2423677) B2423677
theorem B2154379 : Blo 2153435 2154379 := bstep (se 1 (by rfl) ⟨1615784, by rfl⟩ : syracuseStep 2154379 = 3231569) B3231569
theorem B7271045 : Blo 2153435 7271045 := bbase (se 4 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 7271045 = 1363321) (by norm_num)
theorem B4847363 : Blo 2153435 4847363 := bstep (se 1 (by rfl) ⟨3635522, by rfl⟩ : syracuseStep 4847363 = 7271045) B7271045
theorem B3231575 : Blo 2153435 3231575 := bstep (se 1 (by rfl) ⟨2423681, by rfl⟩ : syracuseStep 3231575 = 4847363) B4847363
theorem B2154383 : Blo 2153435 2154383 := bstep (se 1 (by rfl) ⟨1615787, by rfl⟩ : syracuseStep 2154383 = 3231575) B3231575
theorem B3231581 : Blo 2153435 3231581 := bbase (se 3 (by rfl) ⟨605921, by rfl⟩ : syracuseStep 3231581 = 1211843) (by norm_num)
theorem B2154387 : Blo 2153435 2154387 := bstep (se 1 (by rfl) ⟨1615790, by rfl⟩ : syracuseStep 2154387 = 3231581) B3231581
theorem B4847381 : Blo 2153435 4847381 := bbase (se 6 (by rfl) ⟨113610, by rfl⟩ : syracuseStep 4847381 = 227221) (by norm_num)
theorem B3231587 : Blo 2153435 3231587 := bstep (se 1 (by rfl) ⟨2423690, by rfl⟩ : syracuseStep 3231587 = 4847381) B4847381
theorem B2154391 : Blo 2153435 2154391 := bstep (se 1 (by rfl) ⟨1615793, by rfl⟩ : syracuseStep 2154391 = 3231587) B3231587
theorem B8179973 : Blo 2153435 8179973 := bbase (se 4 (by rfl) ⟨766872, by rfl⟩ : syracuseStep 8179973 = 1533745) (by norm_num)
theorem B5453315 : Blo 2153435 5453315 := bstep (se 1 (by rfl) ⟨4089986, by rfl⟩ : syracuseStep 5453315 = 8179973) B8179973
theorem B3635543 : Blo 2153435 3635543 := bstep (se 1 (by rfl) ⟨2726657, by rfl⟩ : syracuseStep 3635543 = 5453315) B5453315
theorem B2423695 : Blo 2153435 2423695 := bstep (se 1 (by rfl) ⟨1817771, by rfl⟩ : syracuseStep 2423695 = 3635543) B3635543
theorem B3231593 : Blo 2153435 3231593 := bstep (se 2 (by rfl) ⟨1211847, by rfl⟩ : syracuseStep 3231593 = 2423695) B2423695
theorem B2154395 : Blo 2153435 2154395 := bstep (se 1 (by rfl) ⟨1615796, by rfl⟩ : syracuseStep 2154395 = 3231593) B3231593
theorem B6551381 : Blo 2153435 6551381 := bbase (se 9 (by rfl) ⟨19193, by rfl⟩ : syracuseStep 6551381 = 38387) (by norm_num)
theorem B17470349 : Blo 2153435 17470349 := bstep (se 3 (by rfl) ⟨3275690, by rfl⟩ : syracuseStep 17470349 = 6551381) B6551381
theorem B11646899 : Blo 2153435 11646899 := bstep (se 1 (by rfl) ⟨8735174, by rfl⟩ : syracuseStep 11646899 = 17470349) B17470349
theorem B7764599 : Blo 2153435 7764599 := bstep (se 1 (by rfl) ⟨5823449, by rfl⟩ : syracuseStep 7764599 = 11646899) B11646899
theorem B5176399 : Blo 2153435 5176399 := bstep (se 1 (by rfl) ⟨3882299, by rfl⟩ : syracuseStep 5176399 = 7764599) B7764599
theorem B6901865 : Blo 2153435 6901865 := bstep (se 2 (by rfl) ⟨2588199, by rfl⟩ : syracuseStep 6901865 = 5176399) B5176399
theorem B4601243 : Blo 2153435 4601243 := bstep (se 1 (by rfl) ⟨3450932, by rfl⟩ : syracuseStep 4601243 = 6901865) B6901865
theorem B12269981 : Blo 2153435 12269981 := bstep (se 3 (by rfl) ⟨2300621, by rfl⟩ : syracuseStep 12269981 = 4601243) B4601243
theorem B8179987 : Blo 2153435 8179987 := bstep (se 1 (by rfl) ⟨6134990, by rfl⟩ : syracuseStep 8179987 = 12269981) B12269981
theorem B10906649 : Blo 2153435 10906649 := bstep (se 2 (by rfl) ⟨4089993, by rfl⟩ : syracuseStep 10906649 = 8179987) B8179987
theorem B7271099 : Blo 2153435 7271099 := bstep (se 1 (by rfl) ⟨5453324, by rfl⟩ : syracuseStep 7271099 = 10906649) B10906649
theorem B4847399 : Blo 2153435 4847399 := bstep (se 1 (by rfl) ⟨3635549, by rfl⟩ : syracuseStep 4847399 = 7271099) B7271099
theorem B3231599 : Blo 2153435 3231599 := bstep (se 1 (by rfl) ⟨2423699, by rfl⟩ : syracuseStep 3231599 = 4847399) B4847399
theorem B2154399 : Blo 2153435 2154399 := bstep (se 1 (by rfl) ⟨1615799, by rfl⟩ : syracuseStep 2154399 = 3231599) B3231599
theorem B3231605 : Blo 2153435 3231605 := bbase (se 5 (by rfl) ⟨151481, by rfl⟩ : syracuseStep 3231605 = 302963) (by norm_num)
theorem B2154403 : Blo 2153435 2154403 := bstep (se 1 (by rfl) ⟨1615802, by rfl⟩ : syracuseStep 2154403 = 3231605) B3231605
theorem B4601261 : Blo 2153435 4601261 := bbase (se 3 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 4601261 = 1725473) (by norm_num)
theorem B3067507 : Blo 2153435 3067507 := bstep (se 1 (by rfl) ⟨2300630, by rfl⟩ : syracuseStep 3067507 = 4601261) B4601261
theorem B4090009 : Blo 2153435 4090009 := bstep (se 2 (by rfl) ⟨1533753, by rfl⟩ : syracuseStep 4090009 = 3067507) B3067507
theorem B5453345 : Blo 2153435 5453345 := bstep (se 2 (by rfl) ⟨2045004, by rfl⟩ : syracuseStep 5453345 = 4090009) B4090009
theorem B3635563 : Blo 2153435 3635563 := bstep (se 1 (by rfl) ⟨2726672, by rfl⟩ : syracuseStep 3635563 = 5453345) B5453345
theorem B4847417 : Blo 2153435 4847417 := bstep (se 2 (by rfl) ⟨1817781, by rfl⟩ : syracuseStep 4847417 = 3635563) B3635563
theorem B3231611 : Blo 2153435 3231611 := bstep (se 1 (by rfl) ⟨2423708, by rfl⟩ : syracuseStep 3231611 = 4847417) B4847417
theorem B2154407 : Blo 2153435 2154407 := bstep (se 1 (by rfl) ⟨1615805, by rfl⟩ : syracuseStep 2154407 = 3231611) B3231611
theorem B2423713 : Blo 2153435 2423713 := bbase (se 2 (by rfl) ⟨908892, by rfl⟩ : syracuseStep 2423713 = 1817785) (by norm_num)
theorem B3231617 : Blo 2153435 3231617 := bstep (se 2 (by rfl) ⟨1211856, by rfl⟩ : syracuseStep 3231617 = 2423713) B2423713
theorem B2154411 : Blo 2153435 2154411 := bstep (se 1 (by rfl) ⟨1615808, by rfl⟩ : syracuseStep 2154411 = 3231617) B3231617
theorem B5453365 : Blo 2153435 5453365 := bbase (se 5 (by rfl) ⟨255626, by rfl⟩ : syracuseStep 5453365 = 511253) (by norm_num)
theorem B7271153 : Blo 2153435 7271153 := bstep (se 2 (by rfl) ⟨2726682, by rfl⟩ : syracuseStep 7271153 = 5453365) B5453365
theorem B4847435 : Blo 2153435 4847435 := bstep (se 1 (by rfl) ⟨3635576, by rfl⟩ : syracuseStep 4847435 = 7271153) B7271153
theorem B3231623 : Blo 2153435 3231623 := bstep (se 1 (by rfl) ⟨2423717, by rfl⟩ : syracuseStep 3231623 = 4847435) B4847435
theorem B2154415 : Blo 2153435 2154415 := bstep (se 1 (by rfl) ⟨1615811, by rfl⟩ : syracuseStep 2154415 = 3231623) B3231623
theorem B3231629 : Blo 2153435 3231629 := bbase (se 3 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 3231629 = 1211861) (by norm_num)
theorem B2154419 : Blo 2153435 2154419 := bstep (se 1 (by rfl) ⟨1615814, by rfl⟩ : syracuseStep 2154419 = 3231629) B3231629
theorem B4847453 : Blo 2153435 4847453 := bbase (se 3 (by rfl) ⟨908897, by rfl⟩ : syracuseStep 4847453 = 1817795) (by norm_num)
theorem B3231635 : Blo 2153435 3231635 := bstep (se 1 (by rfl) ⟨2423726, by rfl⟩ : syracuseStep 3231635 = 4847453) B4847453
theorem B2154423 : Blo 2153435 2154423 := bstep (se 1 (by rfl) ⟨1615817, by rfl⟩ : syracuseStep 2154423 = 3231635) B3231635
theorem B3635597 : Blo 2153435 3635597 := bbase (se 3 (by rfl) ⟨681674, by rfl⟩ : syracuseStep 3635597 = 1363349) (by norm_num)
theorem B2423731 : Blo 2153435 2423731 := bstep (se 1 (by rfl) ⟨1817798, by rfl⟩ : syracuseStep 2423731 = 3635597) B3635597
theorem B3231641 : Blo 2153435 3231641 := bstep (se 2 (by rfl) ⟨1211865, by rfl⟩ : syracuseStep 3231641 = 2423731) B2423731
theorem B2154427 : Blo 2153435 2154427 := bstep (se 1 (by rfl) ⟨1615820, by rfl⟩ : syracuseStep 2154427 = 3231641) B3231641
theorem B2332045 : Blo 2153435 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B3109393 : Blo 2153435 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B16583429 : Blo 2153435 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B11055619 : Blo 2153435 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B14740825 : Blo 2153435 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B19654433 : Blo 2153435 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B13102955 : Blo 2153435 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B8735303 : Blo 2153435 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B23294141 : Blo 2153435 23294141 := bstep (se 3 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 23294141 = 8735303) B8735303
theorem B15529427 : Blo 2153435 15529427 := bstep (se 1 (by rfl) ⟨11647070, by rfl⟩ : syracuseStep 15529427 = 23294141) B23294141
theorem B10352951 : Blo 2153435 10352951 := bstep (se 1 (by rfl) ⟨7764713, by rfl⟩ : syracuseStep 10352951 = 15529427) B15529427
theorem B6901967 : Blo 2153435 6901967 := bstep (se 1 (by rfl) ⟨5176475, by rfl⟩ : syracuseStep 6901967 = 10352951) B10352951
theorem B18405245 : Blo 2153435 18405245 := bstep (se 3 (by rfl) ⟨3450983, by rfl⟩ : syracuseStep 18405245 = 6901967) B6901967
theorem B12270163 : Blo 2153435 12270163 := bstep (se 1 (by rfl) ⟨9202622, by rfl⟩ : syracuseStep 12270163 = 18405245) B18405245
theorem B16360217 : Blo 2153435 16360217 := bstep (se 2 (by rfl) ⟨6135081, by rfl⟩ : syracuseStep 16360217 = 12270163) B12270163
theorem B10906811 : Blo 2153435 10906811 := bstep (se 1 (by rfl) ⟨8180108, by rfl⟩ : syracuseStep 10906811 = 16360217) B16360217
theorem B7271207 : Blo 2153435 7271207 := bstep (se 1 (by rfl) ⟨5453405, by rfl⟩ : syracuseStep 7271207 = 10906811) B10906811
theorem B4847471 : Blo 2153435 4847471 := bstep (se 1 (by rfl) ⟨3635603, by rfl⟩ : syracuseStep 4847471 = 7271207) B7271207
theorem B3231647 : Blo 2153435 3231647 := bstep (se 1 (by rfl) ⟨2423735, by rfl⟩ : syracuseStep 3231647 = 4847471) B4847471
theorem B2154431 : Blo 2153435 2154431 := bstep (se 1 (by rfl) ⟨1615823, by rfl⟩ : syracuseStep 2154431 = 3231647) B3231647
theorem B3231653 : Blo 2153435 3231653 := bbase (se 4 (by rfl) ⟨302967, by rfl⟩ : syracuseStep 3231653 = 605935) (by norm_num)
theorem B2154435 : Blo 2153435 2154435 := bstep (se 1 (by rfl) ⟨1615826, by rfl⟩ : syracuseStep 2154435 = 3231653) B3231653
theorem B2726713 : Blo 2153435 2726713 := bbase (se 2 (by rfl) ⟨1022517, by rfl⟩ : syracuseStep 2726713 = 2045035) (by norm_num)
theorem B3635617 : Blo 2153435 3635617 := bstep (se 2 (by rfl) ⟨1363356, by rfl⟩ : syracuseStep 3635617 = 2726713) B2726713
theorem B4847489 : Blo 2153435 4847489 := bstep (se 2 (by rfl) ⟨1817808, by rfl⟩ : syracuseStep 4847489 = 3635617) B3635617
theorem B3231659 : Blo 2153435 3231659 := bstep (se 1 (by rfl) ⟨2423744, by rfl⟩ : syracuseStep 3231659 = 4847489) B4847489
theorem B2154439 : Blo 2153435 2154439 := bstep (se 1 (by rfl) ⟨1615829, by rfl⟩ : syracuseStep 2154439 = 3231659) B3231659
theorem B2423749 : Blo 2153435 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B3231665 : Blo 2153435 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B2154443 : Blo 2153435 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B4090085 : Blo 2153435 4090085 := bbase (se 4 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 4090085 = 766891) (by norm_num)
theorem B2726723 : Blo 2153435 2726723 := bstep (se 1 (by rfl) ⟨2045042, by rfl⟩ : syracuseStep 2726723 = 4090085) B4090085
theorem B7271261 : Blo 2153435 7271261 := bstep (se 3 (by rfl) ⟨1363361, by rfl⟩ : syracuseStep 7271261 = 2726723) B2726723
theorem B4847507 : Blo 2153435 4847507 := bstep (se 1 (by rfl) ⟨3635630, by rfl⟩ : syracuseStep 4847507 = 7271261) B7271261
theorem B3231671 : Blo 2153435 3231671 := bstep (se 1 (by rfl) ⟨2423753, by rfl⟩ : syracuseStep 3231671 = 4847507) B4847507
theorem B2154447 : Blo 2153435 2154447 := bstep (se 1 (by rfl) ⟨1615835, by rfl⟩ : syracuseStep 2154447 = 3231671) B3231671
theorem B3231677 : Blo 2153435 3231677 := bbase (se 3 (by rfl) ⟨605939, by rfl⟩ : syracuseStep 3231677 = 1211879) (by norm_num)
theorem B2154451 : Blo 2153435 2154451 := bstep (se 1 (by rfl) ⟨1615838, by rfl⟩ : syracuseStep 2154451 = 3231677) B3231677
theorem B4847525 : Blo 2153435 4847525 := bbase (se 4 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 4847525 = 908911) (by norm_num)
theorem B3231683 : Blo 2153435 3231683 := bstep (se 1 (by rfl) ⟨2423762, by rfl⟩ : syracuseStep 3231683 = 4847525) B4847525
theorem B2154455 : Blo 2153435 2154455 := bstep (se 1 (by rfl) ⟨1615841, by rfl⟩ : syracuseStep 2154455 = 3231683) B3231683
theorem B5453477 : Blo 2153435 5453477 := bbase (se 4 (by rfl) ⟨511263, by rfl⟩ : syracuseStep 5453477 = 1022527) (by norm_num)
theorem B3635651 : Blo 2153435 3635651 := bstep (se 1 (by rfl) ⟨2726738, by rfl⟩ : syracuseStep 3635651 = 5453477) B5453477
theorem B2423767 : Blo 2153435 2423767 := bstep (se 1 (by rfl) ⟨1817825, by rfl⟩ : syracuseStep 2423767 = 3635651) B3635651
theorem B3231689 : Blo 2153435 3231689 := bstep (se 2 (by rfl) ⟨1211883, by rfl⟩ : syracuseStep 3231689 = 2423767) B2423767
theorem B2154459 : Blo 2153435 2154459 := bstep (se 1 (by rfl) ⟨1615844, by rfl⟩ : syracuseStep 2154459 = 3231689) B3231689
theorem B6135173 : Blo 2153435 6135173 := bbase (se 4 (by rfl) ⟨575172, by rfl⟩ : syracuseStep 6135173 = 1150345) (by norm_num)
theorem B4090115 : Blo 2153435 4090115 := bstep (se 1 (by rfl) ⟨3067586, by rfl⟩ : syracuseStep 4090115 = 6135173) B6135173
theorem B10906973 : Blo 2153435 10906973 := bstep (se 3 (by rfl) ⟨2045057, by rfl⟩ : syracuseStep 10906973 = 4090115) B4090115
theorem B7271315 : Blo 2153435 7271315 := bstep (se 1 (by rfl) ⟨5453486, by rfl⟩ : syracuseStep 7271315 = 10906973) B10906973
theorem B4847543 : Blo 2153435 4847543 := bstep (se 1 (by rfl) ⟨3635657, by rfl⟩ : syracuseStep 4847543 = 7271315) B7271315
theorem B3231695 : Blo 2153435 3231695 := bstep (se 1 (by rfl) ⟨2423771, by rfl⟩ : syracuseStep 3231695 = 4847543) B4847543
theorem B2154463 : Blo 2153435 2154463 := bstep (se 1 (by rfl) ⟨1615847, by rfl⟩ : syracuseStep 2154463 = 3231695) B3231695
theorem B3231701 : Blo 2153435 3231701 := bbase (se 7 (by rfl) ⟨37871, by rfl⟩ : syracuseStep 3231701 = 75743) (by norm_num)
theorem B2154467 : Blo 2153435 2154467 := bstep (se 1 (by rfl) ⟨1615850, by rfl⟩ : syracuseStep 2154467 = 3231701) B3231701
theorem B8180261 : Blo 2153435 8180261 := bbase (se 4 (by rfl) ⟨766899, by rfl⟩ : syracuseStep 8180261 = 1533799) (by norm_num)
theorem B5453507 : Blo 2153435 5453507 := bstep (se 1 (by rfl) ⟨4090130, by rfl⟩ : syracuseStep 5453507 = 8180261) B8180261
theorem B3635671 : Blo 2153435 3635671 := bstep (se 1 (by rfl) ⟨2726753, by rfl⟩ : syracuseStep 3635671 = 5453507) B5453507
theorem B4847561 : Blo 2153435 4847561 := bstep (se 2 (by rfl) ⟨1817835, by rfl⟩ : syracuseStep 4847561 = 3635671) B3635671
theorem B3231707 : Blo 2153435 3231707 := bstep (se 1 (by rfl) ⟨2423780, by rfl⟩ : syracuseStep 3231707 = 4847561) B4847561
theorem B2154471 : Blo 2153435 2154471 := bstep (se 1 (by rfl) ⟨1615853, by rfl⟩ : syracuseStep 2154471 = 3231707) B3231707
theorem B2423785 : Blo 2153435 2423785 := bbase (se 2 (by rfl) ⟨908919, by rfl⟩ : syracuseStep 2423785 = 1817839) (by norm_num)
theorem B3231713 : Blo 2153435 3231713 := bstep (se 2 (by rfl) ⟨1211892, by rfl⟩ : syracuseStep 3231713 = 2423785) B2423785
theorem B2154475 : Blo 2153435 2154475 := bstep (se 1 (by rfl) ⟨1615856, by rfl⟩ : syracuseStep 2154475 = 3231713) B3231713
theorem B3451061 : Blo 2153435 3451061 := bbase (se 5 (by rfl) ⟨161768, by rfl⟩ : syracuseStep 3451061 = 323537) (by norm_num)
theorem B2300707 : Blo 2153435 2300707 := bstep (se 1 (by rfl) ⟨1725530, by rfl⟩ : syracuseStep 2300707 = 3451061) B3451061
theorem B12270437 : Blo 2153435 12270437 := bstep (se 4 (by rfl) ⟨1150353, by rfl⟩ : syracuseStep 12270437 = 2300707) B2300707
theorem B8180291 : Blo 2153435 8180291 := bstep (se 1 (by rfl) ⟨6135218, by rfl⟩ : syracuseStep 8180291 = 12270437) B12270437
theorem B5453527 : Blo 2153435 5453527 := bstep (se 1 (by rfl) ⟨4090145, by rfl⟩ : syracuseStep 5453527 = 8180291) B8180291
theorem B7271369 : Blo 2153435 7271369 := bstep (se 2 (by rfl) ⟨2726763, by rfl⟩ : syracuseStep 7271369 = 5453527) B5453527
theorem B4847579 : Blo 2153435 4847579 := bstep (se 1 (by rfl) ⟨3635684, by rfl⟩ : syracuseStep 4847579 = 7271369) B7271369
theorem B3231719 : Blo 2153435 3231719 := bstep (se 1 (by rfl) ⟨2423789, by rfl⟩ : syracuseStep 3231719 = 4847579) B4847579
theorem B2154479 : Blo 2153435 2154479 := bstep (se 1 (by rfl) ⟨1615859, by rfl⟩ : syracuseStep 2154479 = 3231719) B3231719
theorem B3231725 : Blo 2153435 3231725 := bbase (se 3 (by rfl) ⟨605948, by rfl⟩ : syracuseStep 3231725 = 1211897) (by norm_num)
theorem B2154483 : Blo 2153435 2154483 := bstep (se 1 (by rfl) ⟨1615862, by rfl⟩ : syracuseStep 2154483 = 3231725) B3231725
theorem B4847597 : Blo 2153435 4847597 := bbase (se 3 (by rfl) ⟨908924, by rfl⟩ : syracuseStep 4847597 = 1817849) (by norm_num)
theorem B3231731 : Blo 2153435 3231731 := bstep (se 1 (by rfl) ⟨2423798, by rfl⟩ : syracuseStep 3231731 = 4847597) B4847597
theorem B2154487 : Blo 2153435 2154487 := bstep (se 1 (by rfl) ⟨1615865, by rfl⟩ : syracuseStep 2154487 = 3231731) B3231731
theorem B5823701 : Blo 2153435 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B3882467 : Blo 2153435 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B2588311 : Blo 2153435 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B3451081 : Blo 2153435 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B4601441 : Blo 2153435 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B3067627 : Blo 2153435 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B4090169 : Blo 2153435 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B2726779 : Blo 2153435 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B3635705 : Blo 2153435 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B2423803 : Blo 2153435 2423803 := bstep (se 1 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 2423803 = 3635705) B3635705
theorem B3231737 : Blo 2153435 3231737 := bstep (se 2 (by rfl) ⟨1211901, by rfl⟩ : syracuseStep 3231737 = 2423803) B2423803
theorem B2154491 : Blo 2153435 2154491 := bstep (se 1 (by rfl) ⟨1615868, by rfl⟩ : syracuseStep 2154491 = 3231737) B3231737
theorem B5527973 : Blo 2153435 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B3685315 : Blo 2153435 3685315 := bstep (se 1 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 3685315 = 5527973) B5527973
theorem B78620053 : Blo 2153435 78620053 := bstep (se 6 (by rfl) ⟨1842657, by rfl⟩ : syracuseStep 78620053 = 3685315) B3685315
theorem B104826737 : Blo 2153435 104826737 := bstep (se 2 (by rfl) ⟨39310026, by rfl⟩ : syracuseStep 104826737 = 78620053) B78620053
theorem B279537965 : Blo 2153435 279537965 := bstep (se 3 (by rfl) ⟨52413368, by rfl⟩ : syracuseStep 279537965 = 104826737) B104826737
theorem B186358643 : Blo 2153435 186358643 := bstep (se 1 (by rfl) ⟨139768982, by rfl⟩ : syracuseStep 186358643 = 279537965) B279537965
theorem B124239095 : Blo 2153435 124239095 := bstep (se 1 (by rfl) ⟨93179321, by rfl⟩ : syracuseStep 124239095 = 186358643) B186358643
theorem B82826063 : Blo 2153435 82826063 := bstep (se 1 (by rfl) ⟨62119547, by rfl⟩ : syracuseStep 82826063 = 124239095) B124239095
theorem B55217375 : Blo 2153435 55217375 := bstep (se 1 (by rfl) ⟨41413031, by rfl⟩ : syracuseStep 55217375 = 82826063) B82826063
theorem B36811583 : Blo 2153435 36811583 := bstep (se 1 (by rfl) ⟨27608687, by rfl⟩ : syracuseStep 36811583 = 55217375) B55217375
theorem B24541055 : Blo 2153435 24541055 := bstep (se 1 (by rfl) ⟨18405791, by rfl⟩ : syracuseStep 24541055 = 36811583) B36811583
theorem B16360703 : Blo 2153435 16360703 := bstep (se 1 (by rfl) ⟨12270527, by rfl⟩ : syracuseStep 16360703 = 24541055) B24541055
theorem B10907135 : Blo 2153435 10907135 := bstep (se 1 (by rfl) ⟨8180351, by rfl⟩ : syracuseStep 10907135 = 16360703) B16360703
theorem B7271423 : Blo 2153435 7271423 := bstep (se 1 (by rfl) ⟨5453567, by rfl⟩ : syracuseStep 7271423 = 10907135) B10907135
theorem B4847615 : Blo 2153435 4847615 := bstep (se 1 (by rfl) ⟨3635711, by rfl⟩ : syracuseStep 4847615 = 7271423) B7271423
theorem B3231743 : Blo 2153435 3231743 := bstep (se 1 (by rfl) ⟨2423807, by rfl⟩ : syracuseStep 3231743 = 4847615) B4847615
theorem B2154495 : Blo 2153435 2154495 := bstep (se 1 (by rfl) ⟨1615871, by rfl⟩ : syracuseStep 2154495 = 3231743) B3231743
theorem B3231749 : Blo 2153435 3231749 := bbase (se 4 (by rfl) ⟨302976, by rfl⟩ : syracuseStep 3231749 = 605953) (by norm_num)
theorem B2154499 : Blo 2153435 2154499 := bstep (se 1 (by rfl) ⟨1615874, by rfl⟩ : syracuseStep 2154499 = 3231749) B3231749
theorem B3635725 : Blo 2153435 3635725 := bbase (se 3 (by rfl) ⟨681698, by rfl⟩ : syracuseStep 3635725 = 1363397) (by norm_num)
theorem B4847633 : Blo 2153435 4847633 := bstep (se 2 (by rfl) ⟨1817862, by rfl⟩ : syracuseStep 4847633 = 3635725) B3635725
theorem B3231755 : Blo 2153435 3231755 := bstep (se 1 (by rfl) ⟨2423816, by rfl⟩ : syracuseStep 3231755 = 4847633) B4847633
theorem B2154503 : Blo 2153435 2154503 := bstep (se 1 (by rfl) ⟨1615877, by rfl⟩ : syracuseStep 2154503 = 3231755) B3231755
theorem B2423821 : Blo 2153435 2423821 := bbase (se 3 (by rfl) ⟨454466, by rfl⟩ : syracuseStep 2423821 = 908933) (by norm_num)
theorem B3231761 : Blo 2153435 3231761 := bstep (se 2 (by rfl) ⟨1211910, by rfl⟩ : syracuseStep 3231761 = 2423821) B2423821
theorem B2154507 : Blo 2153435 2154507 := bstep (se 1 (by rfl) ⟨1615880, by rfl⟩ : syracuseStep 2154507 = 3231761) B3231761
theorem B7271477 : Blo 2153435 7271477 := bbase (se 5 (by rfl) ⟨340850, by rfl⟩ : syracuseStep 7271477 = 681701) (by norm_num)
theorem B4847651 : Blo 2153435 4847651 := bstep (se 1 (by rfl) ⟨3635738, by rfl⟩ : syracuseStep 4847651 = 7271477) B7271477
theorem B3231767 : Blo 2153435 3231767 := bstep (se 1 (by rfl) ⟨2423825, by rfl⟩ : syracuseStep 3231767 = 4847651) B4847651
theorem B2154511 : Blo 2153435 2154511 := bstep (se 1 (by rfl) ⟨1615883, by rfl⟩ : syracuseStep 2154511 = 3231767) B3231767
theorem B3231773 : Blo 2153435 3231773 := bbase (se 3 (by rfl) ⟨605957, by rfl⟩ : syracuseStep 3231773 = 1211915) (by norm_num)
theorem B2154515 : Blo 2153435 2154515 := bstep (se 1 (by rfl) ⟨1615886, by rfl⟩ : syracuseStep 2154515 = 3231773) B3231773
theorem B4847669 : Blo 2153435 4847669 := bbase (se 5 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 4847669 = 454469) (by norm_num)
theorem B3231779 : Blo 2153435 3231779 := bstep (se 1 (by rfl) ⟨2423834, by rfl⟩ : syracuseStep 3231779 = 4847669) B4847669
theorem B2154519 : Blo 2153435 2154519 := bstep (se 1 (by rfl) ⟨1615889, by rfl⟩ : syracuseStep 2154519 = 3231779) B3231779
theorem B19923445 : Blo 2153435 19923445 := bbase (se 5 (by rfl) ⟨933911, by rfl⟩ : syracuseStep 19923445 = 1867823) (by norm_num)
theorem B26564593 : Blo 2153435 26564593 := bstep (se 2 (by rfl) ⟨9961722, by rfl⟩ : syracuseStep 26564593 = 19923445) B19923445
theorem B35419457 : Blo 2153435 35419457 := bstep (se 2 (by rfl) ⟨13282296, by rfl⟩ : syracuseStep 35419457 = 26564593) B26564593
theorem B23612971 : Blo 2153435 23612971 := bstep (se 1 (by rfl) ⟨17709728, by rfl⟩ : syracuseStep 23612971 = 35419457) B35419457
theorem B31483961 : Blo 2153435 31483961 := bstep (se 2 (by rfl) ⟨11806485, by rfl⟩ : syracuseStep 31483961 = 23612971) B23612971
theorem B20989307 : Blo 2153435 20989307 := bstep (se 1 (by rfl) ⟨15741980, by rfl⟩ : syracuseStep 20989307 = 31483961) B31483961
theorem B13992871 : Blo 2153435 13992871 := bstep (se 1 (by rfl) ⟨10494653, by rfl⟩ : syracuseStep 13992871 = 20989307) B20989307
theorem B18657161 : Blo 2153435 18657161 := bstep (se 2 (by rfl) ⟨6996435, by rfl⟩ : syracuseStep 18657161 = 13992871) B13992871
theorem B12438107 : Blo 2153435 12438107 := bstep (se 1 (by rfl) ⟨9328580, by rfl⟩ : syracuseStep 12438107 = 18657161) B18657161
theorem B8292071 : Blo 2153435 8292071 := bstep (se 1 (by rfl) ⟨6219053, by rfl⟩ : syracuseStep 8292071 = 12438107) B12438107
theorem B22112189 : Blo 2153435 22112189 := bstep (se 3 (by rfl) ⟨4146035, by rfl⟩ : syracuseStep 22112189 = 8292071) B8292071
theorem B14741459 : Blo 2153435 14741459 := bstep (se 1 (by rfl) ⟨11056094, by rfl⟩ : syracuseStep 14741459 = 22112189) B22112189
theorem B9827639 : Blo 2153435 9827639 := bstep (se 1 (by rfl) ⟨7370729, by rfl⟩ : syracuseStep 9827639 = 14741459) B14741459
theorem B6551759 : Blo 2153435 6551759 := bstep (se 1 (by rfl) ⟨4913819, by rfl⟩ : syracuseStep 6551759 = 9827639) B9827639
theorem B4367839 : Blo 2153435 4367839 := bstep (se 1 (by rfl) ⟨3275879, by rfl⟩ : syracuseStep 4367839 = 6551759) B6551759
theorem B5823785 : Blo 2153435 5823785 := bstep (se 2 (by rfl) ⟨2183919, by rfl⟩ : syracuseStep 5823785 = 4367839) B4367839
theorem B15530093 : Blo 2153435 15530093 := bstep (se 3 (by rfl) ⟨2911892, by rfl⟩ : syracuseStep 15530093 = 5823785) B5823785
theorem B10353395 : Blo 2153435 10353395 := bstep (se 1 (by rfl) ⟨7765046, by rfl⟩ : syracuseStep 10353395 = 15530093) B15530093
theorem B6902263 : Blo 2153435 6902263 := bstep (se 1 (by rfl) ⟨5176697, by rfl⟩ : syracuseStep 6902263 = 10353395) B10353395
theorem B9203017 : Blo 2153435 9203017 := bstep (se 2 (by rfl) ⟨3451131, by rfl⟩ : syracuseStep 9203017 = 6902263) B6902263
theorem B12270689 : Blo 2153435 12270689 := bstep (se 2 (by rfl) ⟨4601508, by rfl⟩ : syracuseStep 12270689 = 9203017) B9203017
theorem B8180459 : Blo 2153435 8180459 := bstep (se 1 (by rfl) ⟨6135344, by rfl⟩ : syracuseStep 8180459 = 12270689) B12270689
theorem B5453639 : Blo 2153435 5453639 := bstep (se 1 (by rfl) ⟨4090229, by rfl⟩ : syracuseStep 5453639 = 8180459) B8180459
theorem B3635759 : Blo 2153435 3635759 := bstep (se 1 (by rfl) ⟨2726819, by rfl⟩ : syracuseStep 3635759 = 5453639) B5453639
theorem B2423839 : Blo 2153435 2423839 := bstep (se 1 (by rfl) ⟨1817879, by rfl⟩ : syracuseStep 2423839 = 3635759) B3635759
theorem B3231785 : Blo 2153435 3231785 := bstep (se 2 (by rfl) ⟨1211919, by rfl⟩ : syracuseStep 3231785 = 2423839) B2423839
theorem B2154523 : Blo 2153435 2154523 := bstep (se 1 (by rfl) ⟨1615892, by rfl⟩ : syracuseStep 2154523 = 3231785) B3231785
theorem B10353413 : Blo 2153435 10353413 := bbase (se 4 (by rfl) ⟨970632, by rfl⟩ : syracuseStep 10353413 = 1941265) (by norm_num)
theorem B6902275 : Blo 2153435 6902275 := bstep (se 1 (by rfl) ⟨5176706, by rfl⟩ : syracuseStep 6902275 = 10353413) B10353413
theorem B9203033 : Blo 2153435 9203033 := bstep (se 2 (by rfl) ⟨3451137, by rfl⟩ : syracuseStep 9203033 = 6902275) B6902275
theorem B6135355 : Blo 2153435 6135355 := bstep (se 1 (by rfl) ⟨4601516, by rfl⟩ : syracuseStep 6135355 = 9203033) B9203033
theorem B8180473 : Blo 2153435 8180473 := bstep (se 2 (by rfl) ⟨3067677, by rfl⟩ : syracuseStep 8180473 = 6135355) B6135355
theorem B10907297 : Blo 2153435 10907297 := bstep (se 2 (by rfl) ⟨4090236, by rfl⟩ : syracuseStep 10907297 = 8180473) B8180473
theorem B7271531 : Blo 2153435 7271531 := bstep (se 1 (by rfl) ⟨5453648, by rfl⟩ : syracuseStep 7271531 = 10907297) B10907297
theorem B4847687 : Blo 2153435 4847687 := bstep (se 1 (by rfl) ⟨3635765, by rfl⟩ : syracuseStep 4847687 = 7271531) B7271531
theorem B3231791 : Blo 2153435 3231791 := bstep (se 1 (by rfl) ⟨2423843, by rfl⟩ : syracuseStep 3231791 = 4847687) B4847687
theorem B2154527 : Blo 2153435 2154527 := bstep (se 1 (by rfl) ⟨1615895, by rfl⟩ : syracuseStep 2154527 = 3231791) B3231791
theorem B3231797 : Blo 2153435 3231797 := bbase (se 5 (by rfl) ⟨151490, by rfl⟩ : syracuseStep 3231797 = 302981) (by norm_num)
theorem B2154531 : Blo 2153435 2154531 := bstep (se 1 (by rfl) ⟨1615898, by rfl⟩ : syracuseStep 2154531 = 3231797) B3231797
theorem B5453669 : Blo 2153435 5453669 := bbase (se 4 (by rfl) ⟨511281, by rfl⟩ : syracuseStep 5453669 = 1022563) (by norm_num)
theorem B3635779 : Blo 2153435 3635779 := bstep (se 1 (by rfl) ⟨2726834, by rfl⟩ : syracuseStep 3635779 = 5453669) B5453669
theorem B4847705 : Blo 2153435 4847705 := bstep (se 2 (by rfl) ⟨1817889, by rfl⟩ : syracuseStep 4847705 = 3635779) B3635779
theorem B3231803 : Blo 2153435 3231803 := bstep (se 1 (by rfl) ⟨2423852, by rfl⟩ : syracuseStep 3231803 = 4847705) B4847705
theorem B2154535 : Blo 2153435 2154535 := bstep (se 1 (by rfl) ⟨1615901, by rfl⟩ : syracuseStep 2154535 = 3231803) B3231803
theorem B2423857 : Blo 2153435 2423857 := bbase (se 2 (by rfl) ⟨908946, by rfl⟩ : syracuseStep 2423857 = 1817893) (by norm_num)
theorem B3231809 : Blo 2153435 3231809 := bstep (se 2 (by rfl) ⟨1211928, by rfl⟩ : syracuseStep 3231809 = 2423857) B2423857
theorem B2154539 : Blo 2153435 2154539 := bstep (se 1 (by rfl) ⟨1615904, by rfl⟩ : syracuseStep 2154539 = 3231809) B3231809
theorem B2764049 : Blo 2153435 2764049 := bbase (se 2 (by rfl) ⟨1036518, by rfl⟩ : syracuseStep 2764049 = 2073037) (by norm_num)
theorem B29483189 : Blo 2153435 29483189 := bstep (se 5 (by rfl) ⟨1382024, by rfl⟩ : syracuseStep 29483189 = 2764049) B2764049
theorem B19655459 : Blo 2153435 19655459 := bstep (se 1 (by rfl) ⟨14741594, by rfl⟩ : syracuseStep 19655459 = 29483189) B29483189
theorem B13103639 : Blo 2153435 13103639 := bstep (se 1 (by rfl) ⟨9827729, by rfl⟩ : syracuseStep 13103639 = 19655459) B19655459
theorem B8735759 : Blo 2153435 8735759 := bstep (se 1 (by rfl) ⟨6551819, by rfl⟩ : syracuseStep 8735759 = 13103639) B13103639
theorem B5823839 : Blo 2153435 5823839 := bstep (se 1 (by rfl) ⟨4367879, by rfl⟩ : syracuseStep 5823839 = 8735759) B8735759
theorem B15530237 : Blo 2153435 15530237 := bstep (se 3 (by rfl) ⟨2911919, by rfl⟩ : syracuseStep 15530237 = 5823839) B5823839
theorem B10353491 : Blo 2153435 10353491 := bstep (se 1 (by rfl) ⟨7765118, by rfl⟩ : syracuseStep 10353491 = 15530237) B15530237
theorem B6902327 : Blo 2153435 6902327 := bstep (se 1 (by rfl) ⟨5176745, by rfl⟩ : syracuseStep 6902327 = 10353491) B10353491
theorem B4601551 : Blo 2153435 4601551 := bstep (se 1 (by rfl) ⟨3451163, by rfl⟩ : syracuseStep 4601551 = 6902327) B6902327
theorem B6135401 : Blo 2153435 6135401 := bstep (se 2 (by rfl) ⟨2300775, by rfl⟩ : syracuseStep 6135401 = 4601551) B4601551
theorem B4090267 : Blo 2153435 4090267 := bstep (se 1 (by rfl) ⟨3067700, by rfl⟩ : syracuseStep 4090267 = 6135401) B6135401
theorem B5453689 : Blo 2153435 5453689 := bstep (se 2 (by rfl) ⟨2045133, by rfl⟩ : syracuseStep 5453689 = 4090267) B4090267
theorem B7271585 : Blo 2153435 7271585 := bstep (se 2 (by rfl) ⟨2726844, by rfl⟩ : syracuseStep 7271585 = 5453689) B5453689
theorem B4847723 : Blo 2153435 4847723 := bstep (se 1 (by rfl) ⟨3635792, by rfl⟩ : syracuseStep 4847723 = 7271585) B7271585
theorem B3231815 : Blo 2153435 3231815 := bstep (se 1 (by rfl) ⟨2423861, by rfl⟩ : syracuseStep 3231815 = 4847723) B4847723
theorem B2154543 : Blo 2153435 2154543 := bstep (se 1 (by rfl) ⟨1615907, by rfl⟩ : syracuseStep 2154543 = 3231815) B3231815
theorem B3231821 : Blo 2153435 3231821 := bbase (se 3 (by rfl) ⟨605966, by rfl⟩ : syracuseStep 3231821 = 1211933) (by norm_num)
theorem B2154547 : Blo 2153435 2154547 := bstep (se 1 (by rfl) ⟨1615910, by rfl⟩ : syracuseStep 2154547 = 3231821) B3231821
theorem B4847741 : Blo 2153435 4847741 := bbase (se 3 (by rfl) ⟨908951, by rfl⟩ : syracuseStep 4847741 = 1817903) (by norm_num)
theorem B3231827 : Blo 2153435 3231827 := bstep (se 1 (by rfl) ⟨2423870, by rfl⟩ : syracuseStep 3231827 = 4847741) B4847741
theorem B2154551 : Blo 2153435 2154551 := bstep (se 1 (by rfl) ⟨1615913, by rfl⟩ : syracuseStep 2154551 = 3231827) B3231827
theorem B3635813 : Blo 2153435 3635813 := bbase (se 4 (by rfl) ⟨340857, by rfl⟩ : syracuseStep 3635813 = 681715) (by norm_num)
theorem B2423875 : Blo 2153435 2423875 := bstep (se 1 (by rfl) ⟨1817906, by rfl⟩ : syracuseStep 2423875 = 3635813) B3635813
theorem B3231833 : Blo 2153435 3231833 := bstep (se 2 (by rfl) ⟨1211937, by rfl⟩ : syracuseStep 3231833 = 2423875) B2423875
theorem B2154555 : Blo 2153435 2154555 := bstep (se 1 (by rfl) ⟨1615916, by rfl⟩ : syracuseStep 2154555 = 3231833) B3231833
theorem B3451189 : Blo 2153435 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B4601585 : Blo 2153435 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B3067723 : Blo 2153435 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B16361189 : Blo 2153435 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B10907459 : Blo 2153435 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B7271639 : Blo 2153435 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B4847759 : Blo 2153435 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B3231839 : Blo 2153435 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B2154559 : Blo 2153435 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B3231845 : Blo 2153435 3231845 := bbase (se 4 (by rfl) ⟨302985, by rfl⟩ : syracuseStep 3231845 = 605971) (by norm_num)
theorem B2154563 : Blo 2153435 2154563 := bstep (se 1 (by rfl) ⟨1615922, by rfl⟩ : syracuseStep 2154563 = 3231845) B3231845
theorem B6902405 : Blo 2153435 6902405 := bbase (se 4 (by rfl) ⟨647100, by rfl⟩ : syracuseStep 6902405 = 1294201) (by norm_num)
theorem B4601603 : Blo 2153435 4601603 := bstep (se 1 (by rfl) ⟨3451202, by rfl⟩ : syracuseStep 4601603 = 6902405) B6902405
theorem B3067735 : Blo 2153435 3067735 := bstep (se 1 (by rfl) ⟨2300801, by rfl⟩ : syracuseStep 3067735 = 4601603) B4601603
theorem B4090313 : Blo 2153435 4090313 := bstep (se 2 (by rfl) ⟨1533867, by rfl⟩ : syracuseStep 4090313 = 3067735) B3067735
theorem B2726875 : Blo 2153435 2726875 := bstep (se 1 (by rfl) ⟨2045156, by rfl⟩ : syracuseStep 2726875 = 4090313) B4090313
theorem B3635833 : Blo 2153435 3635833 := bstep (se 2 (by rfl) ⟨1363437, by rfl⟩ : syracuseStep 3635833 = 2726875) B2726875
theorem B4847777 : Blo 2153435 4847777 := bstep (se 2 (by rfl) ⟨1817916, by rfl⟩ : syracuseStep 4847777 = 3635833) B3635833
theorem B3231851 : Blo 2153435 3231851 := bstep (se 1 (by rfl) ⟨2423888, by rfl⟩ : syracuseStep 3231851 = 4847777) B4847777
theorem B2154567 : Blo 2153435 2154567 := bstep (se 1 (by rfl) ⟨1615925, by rfl⟩ : syracuseStep 2154567 = 3231851) B3231851
theorem B2423893 : Blo 2153435 2423893 := bbase (se 8 (by rfl) ⟨14202, by rfl⟩ : syracuseStep 2423893 = 28405) (by norm_num)
theorem B3231857 : Blo 2153435 3231857 := bstep (se 2 (by rfl) ⟨1211946, by rfl⟩ : syracuseStep 3231857 = 2423893) B2423893
theorem B2154571 : Blo 2153435 2154571 := bstep (se 1 (by rfl) ⟨1615928, by rfl⟩ : syracuseStep 2154571 = 3231857) B3231857
theorem B2726885 : Blo 2153435 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B7271693 : Blo 2153435 7271693 := bstep (se 3 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 7271693 = 2726885) B2726885
theorem B4847795 : Blo 2153435 4847795 := bstep (se 1 (by rfl) ⟨3635846, by rfl⟩ : syracuseStep 4847795 = 7271693) B7271693
theorem B3231863 : Blo 2153435 3231863 := bstep (se 1 (by rfl) ⟨2423897, by rfl⟩ : syracuseStep 3231863 = 4847795) B4847795
theorem B2154575 : Blo 2153435 2154575 := bstep (se 1 (by rfl) ⟨1615931, by rfl⟩ : syracuseStep 2154575 = 3231863) B3231863
theorem B3231869 : Blo 2153435 3231869 := bbase (se 3 (by rfl) ⟨605975, by rfl⟩ : syracuseStep 3231869 = 1211951) (by norm_num)
theorem B2154579 : Blo 2153435 2154579 := bstep (se 1 (by rfl) ⟨1615934, by rfl⟩ : syracuseStep 2154579 = 3231869) B3231869
theorem B4847813 : Blo 2153435 4847813 := bbase (se 4 (by rfl) ⟨454482, by rfl⟩ : syracuseStep 4847813 = 908965) (by norm_num)
theorem B3231875 : Blo 2153435 3231875 := bstep (se 1 (by rfl) ⟨2423906, by rfl⟩ : syracuseStep 3231875 = 4847813) B4847813
theorem B2154583 : Blo 2153435 2154583 := bstep (se 1 (by rfl) ⟨1615937, by rfl⟩ : syracuseStep 2154583 = 3231875) B3231875
theorem B4913965 : Blo 2153435 4913965 := bbase (se 3 (by rfl) ⟨921368, by rfl⟩ : syracuseStep 4913965 = 1842737) (by norm_num)
theorem B26207813 : Blo 2153435 26207813 := bstep (se 4 (by rfl) ⟨2456982, by rfl⟩ : syracuseStep 26207813 = 4913965) B4913965
theorem B17471875 : Blo 2153435 17471875 := bstep (se 1 (by rfl) ⟨13103906, by rfl⟩ : syracuseStep 17471875 = 26207813) B26207813
theorem B23295833 : Blo 2153435 23295833 := bstep (se 2 (by rfl) ⟨8735937, by rfl⟩ : syracuseStep 23295833 = 17471875) B17471875
theorem B15530555 : Blo 2153435 15530555 := bstep (se 1 (by rfl) ⟨11647916, by rfl⟩ : syracuseStep 15530555 = 23295833) B23295833
theorem B10353703 : Blo 2153435 10353703 := bstep (se 1 (by rfl) ⟨7765277, by rfl⟩ : syracuseStep 10353703 = 15530555) B15530555
theorem B13804937 : Blo 2153435 13804937 := bstep (se 2 (by rfl) ⟨5176851, by rfl⟩ : syracuseStep 13804937 = 10353703) B10353703
theorem B9203291 : Blo 2153435 9203291 := bstep (se 1 (by rfl) ⟨6902468, by rfl⟩ : syracuseStep 9203291 = 13804937) B13804937
theorem B6135527 : Blo 2153435 6135527 := bstep (se 1 (by rfl) ⟨4601645, by rfl⟩ : syracuseStep 6135527 = 9203291) B9203291
theorem B4090351 : Blo 2153435 4090351 := bstep (se 1 (by rfl) ⟨3067763, by rfl⟩ : syracuseStep 4090351 = 6135527) B6135527
theorem B5453801 : Blo 2153435 5453801 := bstep (se 2 (by rfl) ⟨2045175, by rfl⟩ : syracuseStep 5453801 = 4090351) B4090351
theorem B3635867 : Blo 2153435 3635867 := bstep (se 1 (by rfl) ⟨2726900, by rfl⟩ : syracuseStep 3635867 = 5453801) B5453801
theorem B2423911 : Blo 2153435 2423911 := bstep (se 1 (by rfl) ⟨1817933, by rfl⟩ : syracuseStep 2423911 = 3635867) B3635867
theorem B3231881 : Blo 2153435 3231881 := bstep (se 2 (by rfl) ⟨1211955, by rfl⟩ : syracuseStep 3231881 = 2423911) B2423911
theorem B2154587 : Blo 2153435 2154587 := bstep (se 1 (by rfl) ⟨1615940, by rfl⟩ : syracuseStep 2154587 = 3231881) B3231881
theorem B10907621 : Blo 2153435 10907621 := bbase (se 4 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 10907621 = 2045179) (by norm_num)
theorem B7271747 : Blo 2153435 7271747 := bstep (se 1 (by rfl) ⟨5453810, by rfl⟩ : syracuseStep 7271747 = 10907621) B10907621
theorem B4847831 : Blo 2153435 4847831 := bstep (se 1 (by rfl) ⟨3635873, by rfl⟩ : syracuseStep 4847831 = 7271747) B7271747
theorem B3231887 : Blo 2153435 3231887 := bstep (se 1 (by rfl) ⟨2423915, by rfl⟩ : syracuseStep 3231887 = 4847831) B4847831
theorem B2154591 : Blo 2153435 2154591 := bstep (se 1 (by rfl) ⟨1615943, by rfl⟩ : syracuseStep 2154591 = 3231887) B3231887
theorem B3231893 : Blo 2153435 3231893 := bbase (se 6 (by rfl) ⟨75747, by rfl⟩ : syracuseStep 3231893 = 151495) (by norm_num)
theorem B2154595 : Blo 2153435 2154595 := bstep (se 1 (by rfl) ⟨1615946, by rfl⟩ : syracuseStep 2154595 = 3231893) B3231893
theorem B3451253 : Blo 2153435 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B9203341 : Blo 2153435 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B12271121 : Blo 2153435 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B8180747 : Blo 2153435 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B5453831 : Blo 2153435 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B3635887 : Blo 2153435 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B4847849 : Blo 2153435 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B3231899 : Blo 2153435 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B2154599 : Blo 2153435 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B2423929 : Blo 2153435 2423929 := bbase (se 2 (by rfl) ⟨908973, by rfl⟩ : syracuseStep 2423929 = 1817947) (by norm_num)
theorem B3231905 : Blo 2153435 3231905 := bstep (se 2 (by rfl) ⟨1211964, by rfl⟩ : syracuseStep 3231905 = 2423929) B2423929
theorem B2154603 : Blo 2153435 2154603 := bstep (se 1 (by rfl) ⟨1615952, by rfl⟩ : syracuseStep 2154603 = 3231905) B3231905
theorem B2457005 : Blo 2153435 2457005 := bbase (se 3 (by rfl) ⟨460688, by rfl⟩ : syracuseStep 2457005 = 921377) (by norm_num)
theorem B6552013 : Blo 2153435 6552013 := bstep (se 3 (by rfl) ⟨1228502, by rfl⟩ : syracuseStep 6552013 = 2457005) B2457005
theorem B8736017 : Blo 2153435 8736017 := bstep (se 2 (by rfl) ⟨3276006, by rfl⟩ : syracuseStep 8736017 = 6552013) B6552013
theorem B23296045 : Blo 2153435 23296045 := bstep (se 3 (by rfl) ⟨4368008, by rfl⟩ : syracuseStep 23296045 = 8736017) B8736017
theorem B31061393 : Blo 2153435 31061393 := bstep (se 2 (by rfl) ⟨11648022, by rfl⟩ : syracuseStep 31061393 = 23296045) B23296045
theorem B20707595 : Blo 2153435 20707595 := bstep (se 1 (by rfl) ⟨15530696, by rfl⟩ : syracuseStep 20707595 = 31061393) B31061393
theorem B13805063 : Blo 2153435 13805063 := bstep (se 1 (by rfl) ⟨10353797, by rfl⟩ : syracuseStep 13805063 = 20707595) B20707595
theorem B9203375 : Blo 2153435 9203375 := bstep (se 1 (by rfl) ⟨6902531, by rfl⟩ : syracuseStep 9203375 = 13805063) B13805063
theorem B6135583 : Blo 2153435 6135583 := bstep (se 1 (by rfl) ⟨4601687, by rfl⟩ : syracuseStep 6135583 = 9203375) B9203375
theorem B8180777 : Blo 2153435 8180777 := bstep (se 2 (by rfl) ⟨3067791, by rfl⟩ : syracuseStep 8180777 = 6135583) B6135583
theorem B5453851 : Blo 2153435 5453851 := bstep (se 1 (by rfl) ⟨4090388, by rfl⟩ : syracuseStep 5453851 = 8180777) B8180777
theorem B7271801 : Blo 2153435 7271801 := bstep (se 2 (by rfl) ⟨2726925, by rfl⟩ : syracuseStep 7271801 = 5453851) B5453851
theorem B4847867 : Blo 2153435 4847867 := bstep (se 1 (by rfl) ⟨3635900, by rfl⟩ : syracuseStep 4847867 = 7271801) B7271801
theorem B3231911 : Blo 2153435 3231911 := bstep (se 1 (by rfl) ⟨2423933, by rfl⟩ : syracuseStep 3231911 = 4847867) B4847867
theorem B2154607 : Blo 2153435 2154607 := bstep (se 1 (by rfl) ⟨1615955, by rfl⟩ : syracuseStep 2154607 = 3231911) B3231911
theorem B3231917 : Blo 2153435 3231917 := bbase (se 3 (by rfl) ⟨605984, by rfl⟩ : syracuseStep 3231917 = 1211969) (by norm_num)
theorem B2154611 : Blo 2153435 2154611 := bstep (se 1 (by rfl) ⟨1615958, by rfl⟩ : syracuseStep 2154611 = 3231917) B3231917
theorem B4847885 : Blo 2153435 4847885 := bbase (se 3 (by rfl) ⟨908978, by rfl⟩ : syracuseStep 4847885 = 1817957) (by norm_num)
theorem B3231923 : Blo 2153435 3231923 := bstep (se 1 (by rfl) ⟨2423942, by rfl⟩ : syracuseStep 3231923 = 4847885) B4847885
theorem B2154615 : Blo 2153435 2154615 := bstep (se 1 (by rfl) ⟨1615961, by rfl⟩ : syracuseStep 2154615 = 3231923) B3231923
theorem B2726941 : Blo 2153435 2726941 := bbase (se 3 (by rfl) ⟨511301, by rfl⟩ : syracuseStep 2726941 = 1022603) (by norm_num)
theorem B3635921 : Blo 2153435 3635921 := bstep (se 2 (by rfl) ⟨1363470, by rfl⟩ : syracuseStep 3635921 = 2726941) B2726941
theorem B2423947 : Blo 2153435 2423947 := bstep (se 1 (by rfl) ⟨1817960, by rfl⟩ : syracuseStep 2423947 = 3635921) B3635921
theorem B3231929 : Blo 2153435 3231929 := bstep (se 2 (by rfl) ⟨1211973, by rfl⟩ : syracuseStep 3231929 = 2423947) B2423947
theorem B2154619 : Blo 2153435 2154619 := bstep (se 1 (by rfl) ⟨1615964, by rfl⟩ : syracuseStep 2154619 = 3231929) B3231929
theorem B4549277 : Blo 2153435 4549277 := bbase (se 3 (by rfl) ⟨852989, by rfl⟩ : syracuseStep 4549277 = 1705979) (by norm_num)
theorem B12131405 : Blo 2153435 12131405 := bstep (se 3 (by rfl) ⟨2274638, by rfl⟩ : syracuseStep 12131405 = 4549277) B4549277
theorem B8087603 : Blo 2153435 8087603 := bstep (se 1 (by rfl) ⟨6065702, by rfl⟩ : syracuseStep 8087603 = 12131405) B12131405
theorem B21566941 : Blo 2153435 21566941 := bstep (se 3 (by rfl) ⟨4043801, by rfl⟩ : syracuseStep 21566941 = 8087603) B8087603
theorem B460094741 : Blo 2153435 460094741 := bstep (se 6 (by rfl) ⟨10783470, by rfl⟩ : syracuseStep 460094741 = 21566941) B21566941
theorem B306729827 : Blo 2153435 306729827 := bstep (se 1 (by rfl) ⟨230047370, by rfl⟩ : syracuseStep 306729827 = 460094741) B460094741
theorem B204486551 : Blo 2153435 204486551 := bstep (se 1 (by rfl) ⟨153364913, by rfl⟩ : syracuseStep 204486551 = 306729827) B306729827
theorem B136324367 : Blo 2153435 136324367 := bstep (se 1 (by rfl) ⟨102243275, by rfl⟩ : syracuseStep 136324367 = 204486551) B204486551
theorem B90882911 : Blo 2153435 90882911 := bstep (se 1 (by rfl) ⟨68162183, by rfl⟩ : syracuseStep 90882911 = 136324367) B136324367
theorem B60588607 : Blo 2153435 60588607 := bstep (se 1 (by rfl) ⟨45441455, by rfl⟩ : syracuseStep 60588607 = 90882911) B90882911
theorem B80784809 : Blo 2153435 80784809 := bstep (se 2 (by rfl) ⟨30294303, by rfl⟩ : syracuseStep 80784809 = 60588607) B60588607
theorem B53856539 : Blo 2153435 53856539 := bstep (se 1 (by rfl) ⟨40392404, by rfl⟩ : syracuseStep 53856539 = 80784809) B80784809
theorem B35904359 : Blo 2153435 35904359 := bstep (se 1 (by rfl) ⟨26928269, by rfl⟩ : syracuseStep 35904359 = 53856539) B53856539
theorem B23936239 : Blo 2153435 23936239 := bstep (se 1 (by rfl) ⟨17952179, by rfl⟩ : syracuseStep 23936239 = 35904359) B35904359
theorem B127659941 : Blo 2153435 127659941 := bstep (se 4 (by rfl) ⟨11968119, by rfl⟩ : syracuseStep 127659941 = 23936239) B23936239
theorem B85106627 : Blo 2153435 85106627 := bstep (se 1 (by rfl) ⟨63829970, by rfl⟩ : syracuseStep 85106627 = 127659941) B127659941
theorem B56737751 : Blo 2153435 56737751 := bstep (se 1 (by rfl) ⟨42553313, by rfl⟩ : syracuseStep 56737751 = 85106627) B85106627
theorem B151300669 : Blo 2153435 151300669 := bstep (se 3 (by rfl) ⟨28368875, by rfl⟩ : syracuseStep 151300669 = 56737751) B56737751
theorem B201734225 : Blo 2153435 201734225 := bstep (se 2 (by rfl) ⟨75650334, by rfl⟩ : syracuseStep 201734225 = 151300669) B151300669
theorem B134489483 : Blo 2153435 134489483 := bstep (se 1 (by rfl) ⟨100867112, by rfl⟩ : syracuseStep 134489483 = 201734225) B201734225
theorem B89659655 : Blo 2153435 89659655 := bstep (se 1 (by rfl) ⟨67244741, by rfl⟩ : syracuseStep 89659655 = 134489483) B134489483
theorem B59773103 : Blo 2153435 59773103 := bstep (se 1 (by rfl) ⟨44829827, by rfl⟩ : syracuseStep 59773103 = 89659655) B89659655
theorem B39848735 : Blo 2153435 39848735 := bstep (se 1 (by rfl) ⟨29886551, by rfl⟩ : syracuseStep 39848735 = 59773103) B59773103
theorem B26565823 : Blo 2153435 26565823 := bstep (se 1 (by rfl) ⟨19924367, by rfl⟩ : syracuseStep 26565823 = 39848735) B39848735
theorem B35421097 : Blo 2153435 35421097 := bstep (se 2 (by rfl) ⟨13282911, by rfl⟩ : syracuseStep 35421097 = 26565823) B26565823
theorem B47228129 : Blo 2153435 47228129 := bstep (se 2 (by rfl) ⟨17710548, by rfl⟩ : syracuseStep 47228129 = 35421097) B35421097
theorem B31485419 : Blo 2153435 31485419 := bstep (se 1 (by rfl) ⟨23614064, by rfl⟩ : syracuseStep 31485419 = 47228129) B47228129
theorem B20990279 : Blo 2153435 20990279 := bstep (se 1 (by rfl) ⟨15742709, by rfl⟩ : syracuseStep 20990279 = 31485419) B31485419
theorem B55974077 : Blo 2153435 55974077 := bstep (se 3 (by rfl) ⟨10495139, by rfl⟩ : syracuseStep 55974077 = 20990279) B20990279
theorem B37316051 : Blo 2153435 37316051 := bstep (se 1 (by rfl) ⟨27987038, by rfl⟩ : syracuseStep 37316051 = 55974077) B55974077
theorem B24877367 : Blo 2153435 24877367 := bstep (se 1 (by rfl) ⟨18658025, by rfl⟩ : syracuseStep 24877367 = 37316051) B37316051
theorem B16584911 : Blo 2153435 16584911 := bstep (se 1 (by rfl) ⟨12438683, by rfl⟩ : syracuseStep 16584911 = 24877367) B24877367
theorem B11056607 : Blo 2153435 11056607 := bstep (se 1 (by rfl) ⟨8292455, by rfl⟩ : syracuseStep 11056607 = 16584911) B16584911
theorem B7371071 : Blo 2153435 7371071 := bstep (se 1 (by rfl) ⟨5528303, by rfl⟩ : syracuseStep 7371071 = 11056607) B11056607
theorem B4914047 : Blo 2153435 4914047 := bstep (se 1 (by rfl) ⟨3685535, by rfl⟩ : syracuseStep 4914047 = 7371071) B7371071
theorem B13104125 : Blo 2153435 13104125 := bstep (se 3 (by rfl) ⟨2457023, by rfl⟩ : syracuseStep 13104125 = 4914047) B4914047
theorem B8736083 : Blo 2153435 8736083 := bstep (se 1 (by rfl) ⟨6552062, by rfl⟩ : syracuseStep 8736083 = 13104125) B13104125
theorem B5824055 : Blo 2153435 5824055 := bstep (se 1 (by rfl) ⟨4368041, by rfl⟩ : syracuseStep 5824055 = 8736083) B8736083
theorem B3882703 : Blo 2153435 3882703 := bstep (se 1 (by rfl) ⟨2912027, by rfl⟩ : syracuseStep 3882703 = 5824055) B5824055
theorem B5176937 : Blo 2153435 5176937 := bstep (se 2 (by rfl) ⟨1941351, by rfl⟩ : syracuseStep 5176937 = 3882703) B3882703
theorem B3451291 : Blo 2153435 3451291 := bstep (se 1 (by rfl) ⟨2588468, by rfl⟩ : syracuseStep 3451291 = 5176937) B5176937
theorem B18406885 : Blo 2153435 18406885 := bstep (se 4 (by rfl) ⟨1725645, by rfl⟩ : syracuseStep 18406885 = 3451291) B3451291
theorem B24542513 : Blo 2153435 24542513 := bstep (se 2 (by rfl) ⟨9203442, by rfl⟩ : syracuseStep 24542513 = 18406885) B18406885
theorem B16361675 : Blo 2153435 16361675 := bstep (se 1 (by rfl) ⟨12271256, by rfl⟩ : syracuseStep 16361675 = 24542513) B24542513
theorem B10907783 : Blo 2153435 10907783 := bstep (se 1 (by rfl) ⟨8180837, by rfl⟩ : syracuseStep 10907783 = 16361675) B16361675
theorem B7271855 : Blo 2153435 7271855 := bstep (se 1 (by rfl) ⟨5453891, by rfl⟩ : syracuseStep 7271855 = 10907783) B10907783
theorem B4847903 : Blo 2153435 4847903 := bstep (se 1 (by rfl) ⟨3635927, by rfl⟩ : syracuseStep 4847903 = 7271855) B7271855
theorem B3231935 : Blo 2153435 3231935 := bstep (se 1 (by rfl) ⟨2423951, by rfl⟩ : syracuseStep 3231935 = 4847903) B4847903
theorem B2154623 : Blo 2153435 2154623 := bstep (se 1 (by rfl) ⟨1615967, by rfl⟩ : syracuseStep 2154623 = 3231935) B3231935
theorem B3231941 : Blo 2153435 3231941 := bbase (se 4 (by rfl) ⟨302994, by rfl⟩ : syracuseStep 3231941 = 605989) (by norm_num)
theorem B2154627 : Blo 2153435 2154627 := bstep (se 1 (by rfl) ⟨1615970, by rfl⟩ : syracuseStep 2154627 = 3231941) B3231941
theorem B3635941 : Blo 2153435 3635941 := bbase (se 4 (by rfl) ⟨340869, by rfl⟩ : syracuseStep 3635941 = 681739) (by norm_num)
theorem B4847921 : Blo 2153435 4847921 := bstep (se 2 (by rfl) ⟨1817970, by rfl⟩ : syracuseStep 4847921 = 3635941) B3635941
theorem B3231947 : Blo 2153435 3231947 := bstep (se 1 (by rfl) ⟨2423960, by rfl⟩ : syracuseStep 3231947 = 4847921) B4847921
theorem B2154631 : Blo 2153435 2154631 := bstep (se 1 (by rfl) ⟨1615973, by rfl⟩ : syracuseStep 2154631 = 3231947) B3231947
theorem B2423965 : Blo 2153435 2423965 := bbase (se 3 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 2423965 = 908987) (by norm_num)
theorem B3231953 : Blo 2153435 3231953 := bstep (se 2 (by rfl) ⟨1211982, by rfl⟩ : syracuseStep 3231953 = 2423965) B2423965
theorem B2154635 : Blo 2153435 2154635 := bstep (se 1 (by rfl) ⟨1615976, by rfl⟩ : syracuseStep 2154635 = 3231953) B3231953
theorem B7271909 : Blo 2153435 7271909 := bbase (se 4 (by rfl) ⟨681741, by rfl⟩ : syracuseStep 7271909 = 1363483) (by norm_num)
theorem B4847939 : Blo 2153435 4847939 := bstep (se 1 (by rfl) ⟨3635954, by rfl⟩ : syracuseStep 4847939 = 7271909) B7271909
theorem B3231959 : Blo 2153435 3231959 := bstep (se 1 (by rfl) ⟨2423969, by rfl⟩ : syracuseStep 3231959 = 4847939) B4847939
theorem B2154639 : Blo 2153435 2154639 := bstep (se 1 (by rfl) ⟨1615979, by rfl⟩ : syracuseStep 2154639 = 3231959) B3231959
theorem B3231965 : Blo 2153435 3231965 := bbase (se 3 (by rfl) ⟨605993, by rfl⟩ : syracuseStep 3231965 = 1211987) (by norm_num)
theorem B2154643 : Blo 2153435 2154643 := bstep (se 1 (by rfl) ⟨1615982, by rfl⟩ : syracuseStep 2154643 = 3231965) B3231965
theorem B4847957 : Blo 2153435 4847957 := bbase (se 10 (by rfl) ⟨7101, by rfl⟩ : syracuseStep 4847957 = 14203) (by norm_num)
theorem B3231971 : Blo 2153435 3231971 := bstep (se 1 (by rfl) ⟨2423978, by rfl⟩ : syracuseStep 3231971 = 4847957) B4847957
theorem B2154647 : Blo 2153435 2154647 := bstep (se 1 (by rfl) ⟨1615985, by rfl⟩ : syracuseStep 2154647 = 3231971) B3231971
theorem B5824133 : Blo 2153435 5824133 := bbase (se 4 (by rfl) ⟨546012, by rfl⟩ : syracuseStep 5824133 = 1092025) (by norm_num)
theorem B3882755 : Blo 2153435 3882755 := bstep (se 1 (by rfl) ⟨2912066, by rfl⟩ : syracuseStep 3882755 = 5824133) B5824133
theorem B2588503 : Blo 2153435 2588503 := bstep (se 1 (by rfl) ⟨1941377, by rfl⟩ : syracuseStep 2588503 = 3882755) B3882755
theorem B3451337 : Blo 2153435 3451337 := bstep (se 2 (by rfl) ⟨1294251, by rfl⟩ : syracuseStep 3451337 = 2588503) B2588503
theorem B2300891 : Blo 2153435 2300891 := bstep (se 1 (by rfl) ⟨1725668, by rfl⟩ : syracuseStep 2300891 = 3451337) B3451337
theorem B6135709 : Blo 2153435 6135709 := bstep (se 3 (by rfl) ⟨1150445, by rfl⟩ : syracuseStep 6135709 = 2300891) B2300891
theorem B8180945 : Blo 2153435 8180945 := bstep (se 2 (by rfl) ⟨3067854, by rfl⟩ : syracuseStep 8180945 = 6135709) B6135709
theorem B5453963 : Blo 2153435 5453963 := bstep (se 1 (by rfl) ⟨4090472, by rfl⟩ : syracuseStep 5453963 = 8180945) B8180945
theorem B3635975 : Blo 2153435 3635975 := bstep (se 1 (by rfl) ⟨2726981, by rfl⟩ : syracuseStep 3635975 = 5453963) B5453963
theorem B2423983 : Blo 2153435 2423983 := bstep (se 1 (by rfl) ⟨1817987, by rfl⟩ : syracuseStep 2423983 = 3635975) B3635975
theorem B3231977 : Blo 2153435 3231977 := bstep (se 2 (by rfl) ⟨1211991, by rfl⟩ : syracuseStep 3231977 = 2423983) B2423983
theorem B2154651 : Blo 2153435 2154651 := bstep (se 1 (by rfl) ⟨1615988, by rfl⟩ : syracuseStep 2154651 = 3231977) B3231977
theorem B23936597 : Blo 2153435 23936597 := bbase (se 8 (by rfl) ⟨140253, by rfl⟩ : syracuseStep 23936597 = 280507) (by norm_num)
theorem B15957731 : Blo 2153435 15957731 := bstep (se 1 (by rfl) ⟨11968298, by rfl⟩ : syracuseStep 15957731 = 23936597) B23936597
theorem B10638487 : Blo 2153435 10638487 := bstep (se 1 (by rfl) ⟨7978865, by rfl⟩ : syracuseStep 10638487 = 15957731) B15957731
theorem B14184649 : Blo 2153435 14184649 := bstep (se 2 (by rfl) ⟨5319243, by rfl⟩ : syracuseStep 14184649 = 10638487) B10638487
theorem B18912865 : Blo 2153435 18912865 := bstep (se 2 (by rfl) ⟨7092324, by rfl⟩ : syracuseStep 18912865 = 14184649) B14184649
theorem B25217153 : Blo 2153435 25217153 := bstep (se 2 (by rfl) ⟨9456432, by rfl⟩ : syracuseStep 25217153 = 18912865) B18912865
theorem B16811435 : Blo 2153435 16811435 := bstep (se 1 (by rfl) ⟨12608576, by rfl⟩ : syracuseStep 16811435 = 25217153) B25217153
theorem B44830493 : Blo 2153435 44830493 := bstep (se 3 (by rfl) ⟨8405717, by rfl⟩ : syracuseStep 44830493 = 16811435) B16811435
theorem B29886995 : Blo 2153435 29886995 := bstep (se 1 (by rfl) ⟨22415246, by rfl⟩ : syracuseStep 29886995 = 44830493) B44830493
theorem B79698653 : Blo 2153435 79698653 := bstep (se 3 (by rfl) ⟨14943497, by rfl⟩ : syracuseStep 79698653 = 29886995) B29886995
theorem B53132435 : Blo 2153435 53132435 := bstep (se 1 (by rfl) ⟨39849326, by rfl⟩ : syracuseStep 53132435 = 79698653) B79698653
theorem B35421623 : Blo 2153435 35421623 := bstep (se 1 (by rfl) ⟨26566217, by rfl⟩ : syracuseStep 35421623 = 53132435) B53132435
theorem B23614415 : Blo 2153435 23614415 := bstep (se 1 (by rfl) ⟨17710811, by rfl⟩ : syracuseStep 23614415 = 35421623) B35421623
theorem B15742943 : Blo 2153435 15742943 := bstep (se 1 (by rfl) ⟨11807207, by rfl⟩ : syracuseStep 15742943 = 23614415) B23614415
theorem B10495295 : Blo 2153435 10495295 := bstep (se 1 (by rfl) ⟨7871471, by rfl⟩ : syracuseStep 10495295 = 15742943) B15742943
theorem B6996863 : Blo 2153435 6996863 := bstep (se 1 (by rfl) ⟨5247647, by rfl⟩ : syracuseStep 6996863 = 10495295) B10495295
theorem B4664575 : Blo 2153435 4664575 := bstep (se 1 (by rfl) ⟨3498431, by rfl⟩ : syracuseStep 4664575 = 6996863) B6996863
theorem B6219433 : Blo 2153435 6219433 := bstep (se 2 (by rfl) ⟨2332287, by rfl⟩ : syracuseStep 6219433 = 4664575) B4664575
theorem B8292577 : Blo 2153435 8292577 := bstep (se 2 (by rfl) ⟨3109716, by rfl⟩ : syracuseStep 8292577 = 6219433) B6219433
theorem B11056769 : Blo 2153435 11056769 := bstep (se 2 (by rfl) ⟨4146288, by rfl⟩ : syracuseStep 11056769 = 8292577) B8292577
theorem B7371179 : Blo 2153435 7371179 := bstep (se 1 (by rfl) ⟨5528384, by rfl⟩ : syracuseStep 7371179 = 11056769) B11056769
theorem B4914119 : Blo 2153435 4914119 := bstep (se 1 (by rfl) ⟨3685589, by rfl⟩ : syracuseStep 4914119 = 7371179) B7371179
theorem B13104317 : Blo 2153435 13104317 := bstep (se 3 (by rfl) ⟨2457059, by rfl⟩ : syracuseStep 13104317 = 4914119) B4914119
theorem B8736211 : Blo 2153435 8736211 := bstep (se 1 (by rfl) ⟨6552158, by rfl⟩ : syracuseStep 8736211 = 13104317) B13104317
theorem B11648281 : Blo 2153435 11648281 := bstep (se 2 (by rfl) ⟨4368105, by rfl⟩ : syracuseStep 11648281 = 8736211) B8736211
theorem B15531041 : Blo 2153435 15531041 := bstep (se 2 (by rfl) ⟨5824140, by rfl⟩ : syracuseStep 15531041 = 11648281) B11648281
theorem B41416109 : Blo 2153435 41416109 := bstep (se 3 (by rfl) ⟨7765520, by rfl⟩ : syracuseStep 41416109 = 15531041) B15531041
theorem B27610739 : Blo 2153435 27610739 := bstep (se 1 (by rfl) ⟨20708054, by rfl⟩ : syracuseStep 27610739 = 41416109) B41416109
theorem B18407159 : Blo 2153435 18407159 := bstep (se 1 (by rfl) ⟨13805369, by rfl⟩ : syracuseStep 18407159 = 27610739) B27610739
theorem B12271439 : Blo 2153435 12271439 := bstep (se 1 (by rfl) ⟨9203579, by rfl⟩ : syracuseStep 12271439 = 18407159) B18407159
theorem B8180959 : Blo 2153435 8180959 := bstep (se 1 (by rfl) ⟨6135719, by rfl⟩ : syracuseStep 8180959 = 12271439) B12271439
theorem B10907945 : Blo 2153435 10907945 := bstep (se 2 (by rfl) ⟨4090479, by rfl⟩ : syracuseStep 10907945 = 8180959) B8180959
theorem B7271963 : Blo 2153435 7271963 := bstep (se 1 (by rfl) ⟨5453972, by rfl⟩ : syracuseStep 7271963 = 10907945) B10907945
theorem B4847975 : Blo 2153435 4847975 := bstep (se 1 (by rfl) ⟨3635981, by rfl⟩ : syracuseStep 4847975 = 7271963) B7271963
theorem B3231983 : Blo 2153435 3231983 := bstep (se 1 (by rfl) ⟨2423987, by rfl⟩ : syracuseStep 3231983 = 4847975) B4847975
theorem B2154655 : Blo 2153435 2154655 := bstep (se 1 (by rfl) ⟨1615991, by rfl⟩ : syracuseStep 2154655 = 3231983) B3231983
theorem B3231989 : Blo 2153435 3231989 := bbase (se 5 (by rfl) ⟨151499, by rfl⟩ : syracuseStep 3231989 = 302999) (by norm_num)
theorem B2154659 : Blo 2153435 2154659 := bstep (se 1 (by rfl) ⟨1615994, by rfl⟩ : syracuseStep 2154659 = 3231989) B3231989
theorem B3594557 : Blo 2153435 3594557 := bbase (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) (by norm_num)
theorem B9585485 : Blo 2153435 9585485 := bstep (se 3 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 9585485 = 3594557) B3594557
theorem B6390323 : Blo 2153435 6390323 := bstep (se 1 (by rfl) ⟨4792742, by rfl⟩ : syracuseStep 6390323 = 9585485) B9585485
theorem B4260215 : Blo 2153435 4260215 := bstep (se 1 (by rfl) ⟨3195161, by rfl⟩ : syracuseStep 4260215 = 6390323) B6390323
theorem B2840143 : Blo 2153435 2840143 := bstep (se 1 (by rfl) ⟨2130107, by rfl⟩ : syracuseStep 2840143 = 4260215) B4260215
theorem B3786857 : Blo 2153435 3786857 := bstep (se 2 (by rfl) ⟨1420071, by rfl⟩ : syracuseStep 3786857 = 2840143) B2840143
theorem B161572565 : Blo 2153435 161572565 := bstep (se 7 (by rfl) ⟨1893428, by rfl⟩ : syracuseStep 161572565 = 3786857) B3786857
theorem B107715043 : Blo 2153435 107715043 := bstep (se 1 (by rfl) ⟨80786282, by rfl⟩ : syracuseStep 107715043 = 161572565) B161572565
theorem B143620057 : Blo 2153435 143620057 := bstep (se 2 (by rfl) ⟨53857521, by rfl⟩ : syracuseStep 143620057 = 107715043) B107715043
theorem B191493409 : Blo 2153435 191493409 := bstep (se 2 (by rfl) ⟨71810028, by rfl⟩ : syracuseStep 191493409 = 143620057) B143620057
theorem B255324545 : Blo 2153435 255324545 := bstep (se 2 (by rfl) ⟨95746704, by rfl⟩ : syracuseStep 255324545 = 191493409) B191493409
theorem B170216363 : Blo 2153435 170216363 := bstep (se 1 (by rfl) ⟨127662272, by rfl⟩ : syracuseStep 170216363 = 255324545) B255324545
theorem B453910301 : Blo 2153435 453910301 := bstep (se 3 (by rfl) ⟨85108181, by rfl⟩ : syracuseStep 453910301 = 170216363) B170216363
theorem B302606867 : Blo 2153435 302606867 := bstep (se 1 (by rfl) ⟨226955150, by rfl⟩ : syracuseStep 302606867 = 453910301) B453910301
theorem B201737911 : Blo 2153435 201737911 := bstep (se 1 (by rfl) ⟨151303433, by rfl⟩ : syracuseStep 201737911 = 302606867) B302606867
theorem B268983881 : Blo 2153435 268983881 := bstep (se 2 (by rfl) ⟨100868955, by rfl⟩ : syracuseStep 268983881 = 201737911) B201737911
theorem B179322587 : Blo 2153435 179322587 := bstep (se 1 (by rfl) ⟨134491940, by rfl⟩ : syracuseStep 179322587 = 268983881) B268983881
theorem B119548391 : Blo 2153435 119548391 := bstep (se 1 (by rfl) ⟨89661293, by rfl⟩ : syracuseStep 119548391 = 179322587) B179322587
theorem B1275182837 : Blo 2153435 1275182837 := bstep (se 5 (by rfl) ⟨59774195, by rfl⟩ : syracuseStep 1275182837 = 119548391) B119548391
theorem B850121891 : Blo 2153435 850121891 := bstep (se 1 (by rfl) ⟨637591418, by rfl⟩ : syracuseStep 850121891 = 1275182837) B1275182837
theorem B566747927 : Blo 2153435 566747927 := bstep (se 1 (by rfl) ⟨425060945, by rfl⟩ : syracuseStep 566747927 = 850121891) B850121891
theorem B377831951 : Blo 2153435 377831951 := bstep (se 1 (by rfl) ⟨283373963, by rfl⟩ : syracuseStep 377831951 = 566747927) B566747927
theorem B251887967 : Blo 2153435 251887967 := bstep (se 1 (by rfl) ⟨188915975, by rfl⟩ : syracuseStep 251887967 = 377831951) B377831951
theorem B167925311 : Blo 2153435 167925311 := bstep (se 1 (by rfl) ⟨125943983, by rfl⟩ : syracuseStep 167925311 = 251887967) B251887967
theorem B111950207 : Blo 2153435 111950207 := bstep (se 1 (by rfl) ⟨83962655, by rfl⟩ : syracuseStep 111950207 = 167925311) B167925311
theorem B74633471 : Blo 2153435 74633471 := bstep (se 1 (by rfl) ⟨55975103, by rfl⟩ : syracuseStep 74633471 = 111950207) B111950207
theorem B49755647 : Blo 2153435 49755647 := bstep (se 1 (by rfl) ⟨37316735, by rfl⟩ : syracuseStep 49755647 = 74633471) B74633471
theorem B33170431 : Blo 2153435 33170431 := bstep (se 1 (by rfl) ⟨24877823, by rfl⟩ : syracuseStep 33170431 = 49755647) B49755647
theorem B44227241 : Blo 2153435 44227241 := bstep (se 2 (by rfl) ⟨16585215, by rfl⟩ : syracuseStep 44227241 = 33170431) B33170431
theorem B29484827 : Blo 2153435 29484827 := bstep (se 1 (by rfl) ⟨22113620, by rfl⟩ : syracuseStep 29484827 = 44227241) B44227241
theorem B19656551 : Blo 2153435 19656551 := bstep (se 1 (by rfl) ⟨14742413, by rfl⟩ : syracuseStep 19656551 = 29484827) B29484827
theorem B52417469 : Blo 2153435 52417469 := bstep (se 3 (by rfl) ⟨9828275, by rfl⟩ : syracuseStep 52417469 = 19656551) B19656551
theorem B34944979 : Blo 2153435 34944979 := bstep (se 1 (by rfl) ⟨26208734, by rfl⟩ : syracuseStep 34944979 = 52417469) B52417469
theorem B46593305 : Blo 2153435 46593305 := bstep (se 2 (by rfl) ⟨17472489, by rfl⟩ : syracuseStep 46593305 = 34944979) B34944979
theorem B31062203 : Blo 2153435 31062203 := bstep (se 1 (by rfl) ⟨23296652, by rfl⟩ : syracuseStep 31062203 = 46593305) B46593305
theorem B20708135 : Blo 2153435 20708135 := bstep (se 1 (by rfl) ⟨15531101, by rfl⟩ : syracuseStep 20708135 = 31062203) B31062203
theorem B13805423 : Blo 2153435 13805423 := bstep (se 1 (by rfl) ⟨10354067, by rfl⟩ : syracuseStep 13805423 = 20708135) B20708135
theorem B9203615 : Blo 2153435 9203615 := bstep (se 1 (by rfl) ⟨6902711, by rfl⟩ : syracuseStep 9203615 = 13805423) B13805423
theorem B6135743 : Blo 2153435 6135743 := bstep (se 1 (by rfl) ⟨4601807, by rfl⟩ : syracuseStep 6135743 = 9203615) B9203615
theorem B4090495 : Blo 2153435 4090495 := bstep (se 1 (by rfl) ⟨3067871, by rfl⟩ : syracuseStep 4090495 = 6135743) B6135743
theorem B5453993 : Blo 2153435 5453993 := bstep (se 2 (by rfl) ⟨2045247, by rfl⟩ : syracuseStep 5453993 = 4090495) B4090495
theorem B3635995 : Blo 2153435 3635995 := bstep (se 1 (by rfl) ⟨2726996, by rfl⟩ : syracuseStep 3635995 = 5453993) B5453993
theorem B4847993 : Blo 2153435 4847993 := bstep (se 2 (by rfl) ⟨1817997, by rfl⟩ : syracuseStep 4847993 = 3635995) B3635995
theorem B3231995 : Blo 2153435 3231995 := bstep (se 1 (by rfl) ⟨2423996, by rfl⟩ : syracuseStep 3231995 = 4847993) B4847993
theorem B2154663 : Blo 2153435 2154663 := bstep (se 1 (by rfl) ⟨1615997, by rfl⟩ : syracuseStep 2154663 = 3231995) B3231995
theorem B2424001 : Blo 2153435 2424001 := bbase (se 2 (by rfl) ⟨909000, by rfl⟩ : syracuseStep 2424001 = 1818001) (by norm_num)
theorem B3232001 : Blo 2153435 3232001 := bstep (se 2 (by rfl) ⟨1212000, by rfl⟩ : syracuseStep 3232001 = 2424001) B2424001
theorem B2154667 : Blo 2153435 2154667 := bstep (se 1 (by rfl) ⟨1616000, by rfl⟩ : syracuseStep 2154667 = 3232001) B3232001
theorem B5454013 : Blo 2153435 5454013 := bbase (se 3 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 5454013 = 2045255) (by norm_num)
theorem B7272017 : Blo 2153435 7272017 := bstep (se 2 (by rfl) ⟨2727006, by rfl⟩ : syracuseStep 7272017 = 5454013) B5454013
theorem B4848011 : Blo 2153435 4848011 := bstep (se 1 (by rfl) ⟨3636008, by rfl⟩ : syracuseStep 4848011 = 7272017) B7272017
theorem B3232007 : Blo 2153435 3232007 := bstep (se 1 (by rfl) ⟨2424005, by rfl⟩ : syracuseStep 3232007 = 4848011) B4848011
theorem B2154671 : Blo 2153435 2154671 := bstep (se 1 (by rfl) ⟨1616003, by rfl⟩ : syracuseStep 2154671 = 3232007) B3232007
theorem B3232013 : Blo 2153435 3232013 := bbase (se 3 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 3232013 = 1212005) (by norm_num)
theorem B2154675 : Blo 2153435 2154675 := bstep (se 1 (by rfl) ⟨1616006, by rfl⟩ : syracuseStep 2154675 = 3232013) B3232013
theorem B4848029 : Blo 2153435 4848029 := bbase (se 3 (by rfl) ⟨909005, by rfl⟩ : syracuseStep 4848029 = 1818011) (by norm_num)
theorem B3232019 : Blo 2153435 3232019 := bstep (se 1 (by rfl) ⟨2424014, by rfl⟩ : syracuseStep 3232019 = 4848029) B4848029
theorem B2154679 : Blo 2153435 2154679 := bstep (se 1 (by rfl) ⟨1616009, by rfl⟩ : syracuseStep 2154679 = 3232019) B3232019
theorem B3636029 : Blo 2153435 3636029 := bbase (se 3 (by rfl) ⟨681755, by rfl⟩ : syracuseStep 3636029 = 1363511) (by norm_num)
theorem B2424019 : Blo 2153435 2424019 := bstep (se 1 (by rfl) ⟨1818014, by rfl⟩ : syracuseStep 2424019 = 3636029) B3636029
theorem B3232025 : Blo 2153435 3232025 := bstep (se 2 (by rfl) ⟨1212009, by rfl⟩ : syracuseStep 3232025 = 2424019) B2424019
theorem B2154683 : Blo 2153435 2154683 := bstep (se 1 (by rfl) ⟨1616012, by rfl⟩ : syracuseStep 2154683 = 3232025) B3232025
theorem B2300929 : Blo 2153435 2300929 := bbase (se 2 (by rfl) ⟨862848, by rfl⟩ : syracuseStep 2300929 = 1725697) (by norm_num)
theorem B12271621 : Blo 2153435 12271621 := bstep (se 4 (by rfl) ⟨1150464, by rfl⟩ : syracuseStep 12271621 = 2300929) B2300929
theorem B16362161 : Blo 2153435 16362161 := bstep (se 2 (by rfl) ⟨6135810, by rfl⟩ : syracuseStep 16362161 = 12271621) B12271621
theorem B10908107 : Blo 2153435 10908107 := bstep (se 1 (by rfl) ⟨8181080, by rfl⟩ : syracuseStep 10908107 = 16362161) B16362161
theorem B7272071 : Blo 2153435 7272071 := bstep (se 1 (by rfl) ⟨5454053, by rfl⟩ : syracuseStep 7272071 = 10908107) B10908107
theorem B4848047 : Blo 2153435 4848047 := bstep (se 1 (by rfl) ⟨3636035, by rfl⟩ : syracuseStep 4848047 = 7272071) B7272071
theorem B3232031 : Blo 2153435 3232031 := bstep (se 1 (by rfl) ⟨2424023, by rfl⟩ : syracuseStep 3232031 = 4848047) B4848047
theorem B2154687 : Blo 2153435 2154687 := bstep (se 1 (by rfl) ⟨1616015, by rfl⟩ : syracuseStep 2154687 = 3232031) B3232031
theorem B3232037 : Blo 2153435 3232037 := bbase (se 4 (by rfl) ⟨303003, by rfl⟩ : syracuseStep 3232037 = 606007) (by norm_num)
theorem B2154691 : Blo 2153435 2154691 := bstep (se 1 (by rfl) ⟨1616018, by rfl⟩ : syracuseStep 2154691 = 3232037) B3232037
theorem B2727037 : Blo 2153435 2727037 := bbase (se 3 (by rfl) ⟨511319, by rfl⟩ : syracuseStep 2727037 = 1022639) (by norm_num)
theorem B3636049 : Blo 2153435 3636049 := bstep (se 2 (by rfl) ⟨1363518, by rfl⟩ : syracuseStep 3636049 = 2727037) B2727037
theorem B4848065 : Blo 2153435 4848065 := bstep (se 2 (by rfl) ⟨1818024, by rfl⟩ : syracuseStep 4848065 = 3636049) B3636049
theorem B3232043 : Blo 2153435 3232043 := bstep (se 1 (by rfl) ⟨2424032, by rfl⟩ : syracuseStep 3232043 = 4848065) B4848065
theorem B2154695 : Blo 2153435 2154695 := bstep (se 1 (by rfl) ⟨1616021, by rfl⟩ : syracuseStep 2154695 = 3232043) B3232043
theorem B2424037 : Blo 2153435 2424037 := bbase (se 4 (by rfl) ⟨227253, by rfl⟩ : syracuseStep 2424037 = 454507) (by norm_num)
theorem B3232049 : Blo 2153435 3232049 := bstep (se 2 (by rfl) ⟨1212018, by rfl⟩ : syracuseStep 3232049 = 2424037) B2424037
theorem B2154699 : Blo 2153435 2154699 := bstep (se 1 (by rfl) ⟨1616024, by rfl⟩ : syracuseStep 2154699 = 3232049) B3232049
theorem B4601893 : Blo 2153435 4601893 := bbase (se 4 (by rfl) ⟨431427, by rfl⟩ : syracuseStep 4601893 = 862855) (by norm_num)
theorem B6135857 : Blo 2153435 6135857 := bstep (se 2 (by rfl) ⟨2300946, by rfl⟩ : syracuseStep 6135857 = 4601893) B4601893
theorem B4090571 : Blo 2153435 4090571 := bstep (se 1 (by rfl) ⟨3067928, by rfl⟩ : syracuseStep 4090571 = 6135857) B6135857
theorem B2727047 : Blo 2153435 2727047 := bstep (se 1 (by rfl) ⟨2045285, by rfl⟩ : syracuseStep 2727047 = 4090571) B4090571
theorem B7272125 : Blo 2153435 7272125 := bstep (se 3 (by rfl) ⟨1363523, by rfl⟩ : syracuseStep 7272125 = 2727047) B2727047
theorem B4848083 : Blo 2153435 4848083 := bstep (se 1 (by rfl) ⟨3636062, by rfl⟩ : syracuseStep 4848083 = 7272125) B7272125
theorem B3232055 : Blo 2153435 3232055 := bstep (se 1 (by rfl) ⟨2424041, by rfl⟩ : syracuseStep 3232055 = 4848083) B4848083
theorem B2154703 : Blo 2153435 2154703 := bstep (se 1 (by rfl) ⟨1616027, by rfl⟩ : syracuseStep 2154703 = 3232055) B3232055
theorem B3232061 : Blo 2153435 3232061 := bbase (se 3 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 3232061 = 1212023) (by norm_num)
theorem B2154707 : Blo 2153435 2154707 := bstep (se 1 (by rfl) ⟨1616030, by rfl⟩ : syracuseStep 2154707 = 3232061) B3232061
theorem B4848101 : Blo 2153435 4848101 := bbase (se 4 (by rfl) ⟨454509, by rfl⟩ : syracuseStep 4848101 = 909019) (by norm_num)
theorem B3232067 : Blo 2153435 3232067 := bstep (se 1 (by rfl) ⟨2424050, by rfl⟩ : syracuseStep 3232067 = 4848101) B4848101
theorem B2154711 : Blo 2153435 2154711 := bstep (se 1 (by rfl) ⟨1616033, by rfl⟩ : syracuseStep 2154711 = 3232067) B3232067
theorem B5454125 : Blo 2153435 5454125 := bbase (se 3 (by rfl) ⟨1022648, by rfl⟩ : syracuseStep 5454125 = 2045297) (by norm_num)
theorem B3636083 : Blo 2153435 3636083 := bstep (se 1 (by rfl) ⟨2727062, by rfl⟩ : syracuseStep 3636083 = 5454125) B5454125
theorem B2424055 : Blo 2153435 2424055 := bstep (se 1 (by rfl) ⟨1818041, by rfl⟩ : syracuseStep 2424055 = 3636083) B3636083
theorem B3232073 : Blo 2153435 3232073 := bstep (se 2 (by rfl) ⟨1212027, by rfl⟩ : syracuseStep 3232073 = 2424055) B2424055
theorem B2154715 : Blo 2153435 2154715 := bstep (se 1 (by rfl) ⟨1616036, by rfl⟩ : syracuseStep 2154715 = 3232073) B3232073
theorem B9828533 : Blo 2153435 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B6552355 : Blo 2153435 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B8736473 : Blo 2153435 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B5824315 : Blo 2153435 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B7765753 : Blo 2153435 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B10354337 : Blo 2153435 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B6902891 : Blo 2153435 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B4601927 : Blo 2153435 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B3067951 : Blo 2153435 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B4090601 : Blo 2153435 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B10908269 : Blo 2153435 10908269 := bstep (se 3 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 10908269 = 4090601) B4090601
theorem B7272179 : Blo 2153435 7272179 := bstep (se 1 (by rfl) ⟨5454134, by rfl⟩ : syracuseStep 7272179 = 10908269) B10908269
theorem B4848119 : Blo 2153435 4848119 := bstep (se 1 (by rfl) ⟨3636089, by rfl⟩ : syracuseStep 4848119 = 7272179) B7272179
theorem B3232079 : Blo 2153435 3232079 := bstep (se 1 (by rfl) ⟨2424059, by rfl⟩ : syracuseStep 3232079 = 4848119) B4848119
theorem B2154719 : Blo 2153435 2154719 := bstep (se 1 (by rfl) ⟨1616039, by rfl⟩ : syracuseStep 2154719 = 3232079) B3232079
theorem B3232085 : Blo 2153435 3232085 := bbase (se 10 (by rfl) ⟨4734, by rfl⟩ : syracuseStep 3232085 = 9469) (by norm_num)
theorem B2154723 : Blo 2153435 2154723 := bstep (se 1 (by rfl) ⟨1616042, by rfl⟩ : syracuseStep 2154723 = 3232085) B3232085
theorem B6135925 : Blo 2153435 6135925 := bbase (se 5 (by rfl) ⟨287621, by rfl⟩ : syracuseStep 6135925 = 575243) (by norm_num)
theorem B8181233 : Blo 2153435 8181233 := bstep (se 2 (by rfl) ⟨3067962, by rfl⟩ : syracuseStep 8181233 = 6135925) B6135925
theorem B5454155 : Blo 2153435 5454155 := bstep (se 1 (by rfl) ⟨4090616, by rfl⟩ : syracuseStep 5454155 = 8181233) B8181233
theorem B3636103 : Blo 2153435 3636103 := bstep (se 1 (by rfl) ⟨2727077, by rfl⟩ : syracuseStep 3636103 = 5454155) B5454155
theorem B4848137 : Blo 2153435 4848137 := bstep (se 2 (by rfl) ⟨1818051, by rfl⟩ : syracuseStep 4848137 = 3636103) B3636103
theorem B3232091 : Blo 2153435 3232091 := bstep (se 1 (by rfl) ⟨2424068, by rfl⟩ : syracuseStep 3232091 = 4848137) B4848137
theorem B2154727 : Blo 2153435 2154727 := bstep (se 1 (by rfl) ⟨1616045, by rfl⟩ : syracuseStep 2154727 = 3232091) B3232091
theorem B2424073 : Blo 2153435 2424073 := bbase (se 2 (by rfl) ⟨909027, by rfl⟩ : syracuseStep 2424073 = 1818055) (by norm_num)
theorem B3232097 : Blo 2153435 3232097 := bstep (se 2 (by rfl) ⟨1212036, by rfl⟩ : syracuseStep 3232097 = 2424073) B2424073
theorem B2154731 : Blo 2153435 2154731 := bstep (se 1 (by rfl) ⟨1616048, by rfl⟩ : syracuseStep 2154731 = 3232097) B3232097
theorem B4368269 : Blo 2153435 4368269 := bbase (se 3 (by rfl) ⟨819050, by rfl⟩ : syracuseStep 4368269 = 1638101) (by norm_num)
theorem B2912179 : Blo 2153435 2912179 := bstep (se 1 (by rfl) ⟨2184134, by rfl⟩ : syracuseStep 2912179 = 4368269) B4368269
theorem B3882905 : Blo 2153435 3882905 := bstep (se 2 (by rfl) ⟨1456089, by rfl⟩ : syracuseStep 3882905 = 2912179) B2912179
theorem B2588603 : Blo 2153435 2588603 := bstep (se 1 (by rfl) ⟨1941452, by rfl⟩ : syracuseStep 2588603 = 3882905) B3882905
theorem B27611765 : Blo 2153435 27611765 := bstep (se 5 (by rfl) ⟨1294301, by rfl⟩ : syracuseStep 27611765 = 2588603) B2588603
theorem B18407843 : Blo 2153435 18407843 := bstep (se 1 (by rfl) ⟨13805882, by rfl⟩ : syracuseStep 18407843 = 27611765) B27611765
theorem B12271895 : Blo 2153435 12271895 := bstep (se 1 (by rfl) ⟨9203921, by rfl⟩ : syracuseStep 12271895 = 18407843) B18407843
theorem B8181263 : Blo 2153435 8181263 := bstep (se 1 (by rfl) ⟨6135947, by rfl⟩ : syracuseStep 8181263 = 12271895) B12271895
theorem B5454175 : Blo 2153435 5454175 := bstep (se 1 (by rfl) ⟨4090631, by rfl⟩ : syracuseStep 5454175 = 8181263) B8181263
theorem B7272233 : Blo 2153435 7272233 := bstep (se 2 (by rfl) ⟨2727087, by rfl⟩ : syracuseStep 7272233 = 5454175) B5454175
theorem B4848155 : Blo 2153435 4848155 := bstep (se 1 (by rfl) ⟨3636116, by rfl⟩ : syracuseStep 4848155 = 7272233) B7272233
theorem B3232103 : Blo 2153435 3232103 := bstep (se 1 (by rfl) ⟨2424077, by rfl⟩ : syracuseStep 3232103 = 4848155) B4848155
theorem B2154735 : Blo 2153435 2154735 := bstep (se 1 (by rfl) ⟨1616051, by rfl⟩ : syracuseStep 2154735 = 3232103) B3232103
theorem B3232109 : Blo 2153435 3232109 := bbase (se 3 (by rfl) ⟨606020, by rfl⟩ : syracuseStep 3232109 = 1212041) (by norm_num)
theorem B2154739 : Blo 2153435 2154739 := bstep (se 1 (by rfl) ⟨1616054, by rfl⟩ : syracuseStep 2154739 = 3232109) B3232109
theorem B4848173 : Blo 2153435 4848173 := bbase (se 3 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 4848173 = 1818065) (by norm_num)
theorem B3232115 : Blo 2153435 3232115 := bstep (se 1 (by rfl) ⟨2424086, by rfl⟩ : syracuseStep 3232115 = 4848173) B4848173
theorem B2154743 : Blo 2153435 2154743 := bstep (se 1 (by rfl) ⟨1616057, by rfl⟩ : syracuseStep 2154743 = 3232115) B3232115
theorem B9828661 : Blo 2153435 9828661 := bbase (se 5 (by rfl) ⟨460718, by rfl⟩ : syracuseStep 9828661 = 921437) (by norm_num)
theorem B13104881 : Blo 2153435 13104881 := bstep (se 2 (by rfl) ⟨4914330, by rfl⟩ : syracuseStep 13104881 = 9828661) B9828661
theorem B8736587 : Blo 2153435 8736587 := bstep (se 1 (by rfl) ⟨6552440, by rfl⟩ : syracuseStep 8736587 = 13104881) B13104881
theorem B5824391 : Blo 2153435 5824391 := bstep (se 1 (by rfl) ⟨4368293, by rfl⟩ : syracuseStep 5824391 = 8736587) B8736587
theorem B15531709 : Blo 2153435 15531709 := bstep (se 3 (by rfl) ⟨2912195, by rfl⟩ : syracuseStep 15531709 = 5824391) B5824391
theorem B20708945 : Blo 2153435 20708945 := bstep (se 2 (by rfl) ⟨7765854, by rfl⟩ : syracuseStep 20708945 = 15531709) B15531709
theorem B13805963 : Blo 2153435 13805963 := bstep (se 1 (by rfl) ⟨10354472, by rfl⟩ : syracuseStep 13805963 = 20708945) B20708945
theorem B9203975 : Blo 2153435 9203975 := bstep (se 1 (by rfl) ⟨6902981, by rfl⟩ : syracuseStep 9203975 = 13805963) B13805963
theorem B6135983 : Blo 2153435 6135983 := bstep (se 1 (by rfl) ⟨4601987, by rfl⟩ : syracuseStep 6135983 = 9203975) B9203975
theorem B4090655 : Blo 2153435 4090655 := bstep (se 1 (by rfl) ⟨3067991, by rfl⟩ : syracuseStep 4090655 = 6135983) B6135983
theorem B2727103 : Blo 2153435 2727103 := bstep (se 1 (by rfl) ⟨2045327, by rfl⟩ : syracuseStep 2727103 = 4090655) B4090655
theorem B3636137 : Blo 2153435 3636137 := bstep (se 2 (by rfl) ⟨1363551, by rfl⟩ : syracuseStep 3636137 = 2727103) B2727103
theorem B2424091 : Blo 2153435 2424091 := bstep (se 1 (by rfl) ⟨1818068, by rfl⟩ : syracuseStep 2424091 = 3636137) B3636137
theorem B3232121 : Blo 2153435 3232121 := bstep (se 2 (by rfl) ⟨1212045, by rfl⟩ : syracuseStep 3232121 = 2424091) B2424091
theorem B2154747 : Blo 2153435 2154747 := bstep (se 1 (by rfl) ⟨1616060, by rfl⟩ : syracuseStep 2154747 = 3232121) B3232121
theorem B36815957 : Blo 2153435 36815957 := bbase (se 8 (by rfl) ⟨215718, by rfl⟩ : syracuseStep 36815957 = 431437) (by norm_num)
theorem B24543971 : Blo 2153435 24543971 := bstep (se 1 (by rfl) ⟨18407978, by rfl⟩ : syracuseStep 24543971 = 36815957) B36815957
theorem B16362647 : Blo 2153435 16362647 := bstep (se 1 (by rfl) ⟨12271985, by rfl⟩ : syracuseStep 16362647 = 24543971) B24543971
theorem B10908431 : Blo 2153435 10908431 := bstep (se 1 (by rfl) ⟨8181323, by rfl⟩ : syracuseStep 10908431 = 16362647) B16362647
theorem B7272287 : Blo 2153435 7272287 := bstep (se 1 (by rfl) ⟨5454215, by rfl⟩ : syracuseStep 7272287 = 10908431) B10908431
theorem B4848191 : Blo 2153435 4848191 := bstep (se 1 (by rfl) ⟨3636143, by rfl⟩ : syracuseStep 4848191 = 7272287) B7272287
theorem B3232127 : Blo 2153435 3232127 := bstep (se 1 (by rfl) ⟨2424095, by rfl⟩ : syracuseStep 3232127 = 4848191) B4848191
theorem B2154751 : Blo 2153435 2154751 := bstep (se 1 (by rfl) ⟨1616063, by rfl⟩ : syracuseStep 2154751 = 3232127) B3232127
theorem B3232133 : Blo 2153435 3232133 := bbase (se 4 (by rfl) ⟨303012, by rfl⟩ : syracuseStep 3232133 = 606025) (by norm_num)
theorem B2154755 : Blo 2153435 2154755 := bstep (se 1 (by rfl) ⟨1616066, by rfl⟩ : syracuseStep 2154755 = 3232133) B3232133
theorem B3636157 : Blo 2153435 3636157 := bbase (se 3 (by rfl) ⟨681779, by rfl⟩ : syracuseStep 3636157 = 1363559) (by norm_num)
theorem B4848209 : Blo 2153435 4848209 := bstep (se 2 (by rfl) ⟨1818078, by rfl⟩ : syracuseStep 4848209 = 3636157) B3636157
theorem B3232139 : Blo 2153435 3232139 := bstep (se 1 (by rfl) ⟨2424104, by rfl⟩ : syracuseStep 3232139 = 4848209) B4848209
theorem B2154759 : Blo 2153435 2154759 := bstep (se 1 (by rfl) ⟨1616069, by rfl⟩ : syracuseStep 2154759 = 3232139) B3232139
theorem B2424109 : Blo 2153435 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B3232145 : Blo 2153435 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B2154763 : Blo 2153435 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B7272341 : Blo 2153435 7272341 := bbase (se 6 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 7272341 = 340891) (by norm_num)
theorem B4848227 : Blo 2153435 4848227 := bstep (se 1 (by rfl) ⟨3636170, by rfl⟩ : syracuseStep 4848227 = 7272341) B7272341
theorem B3232151 : Blo 2153435 3232151 := bstep (se 1 (by rfl) ⟨2424113, by rfl⟩ : syracuseStep 3232151 = 4848227) B4848227
theorem B2154767 : Blo 2153435 2154767 := bstep (se 1 (by rfl) ⟨1616075, by rfl⟩ : syracuseStep 2154767 = 3232151) B3232151
theorem B3232157 : Blo 2153435 3232157 := bbase (se 3 (by rfl) ⟨606029, by rfl⟩ : syracuseStep 3232157 = 1212059) (by norm_num)
theorem B2154771 : Blo 2153435 2154771 := bstep (se 1 (by rfl) ⟨1616078, by rfl⟩ : syracuseStep 2154771 = 3232157) B3232157
theorem B4848245 : Blo 2153435 4848245 := bbase (se 5 (by rfl) ⟨227261, by rfl⟩ : syracuseStep 4848245 = 454523) (by norm_num)
theorem B3232163 : Blo 2153435 3232163 := bstep (se 1 (by rfl) ⟨2424122, by rfl⟩ : syracuseStep 3232163 = 4848245) B4848245
theorem B2154775 : Blo 2153435 2154775 := bstep (se 1 (by rfl) ⟨1616081, by rfl⟩ : syracuseStep 2154775 = 3232163) B3232163
theorem B3276269 : Blo 2153435 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B2184179 : Blo 2153435 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B5824477 : Blo 2153435 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B7765969 : Blo 2153435 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B10354625 : Blo 2153435 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B6903083 : Blo 2153435 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B18408221 : Blo 2153435 18408221 := bstep (se 3 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 18408221 = 6903083) B6903083
theorem B12272147 : Blo 2153435 12272147 := bstep (se 1 (by rfl) ⟨9204110, by rfl⟩ : syracuseStep 12272147 = 18408221) B18408221
theorem B8181431 : Blo 2153435 8181431 := bstep (se 1 (by rfl) ⟨6136073, by rfl⟩ : syracuseStep 8181431 = 12272147) B12272147
theorem B5454287 : Blo 2153435 5454287 := bstep (se 1 (by rfl) ⟨4090715, by rfl⟩ : syracuseStep 5454287 = 8181431) B8181431
theorem B3636191 : Blo 2153435 3636191 := bstep (se 1 (by rfl) ⟨2727143, by rfl⟩ : syracuseStep 3636191 = 5454287) B5454287
theorem B2424127 : Blo 2153435 2424127 := bstep (se 1 (by rfl) ⟨1818095, by rfl⟩ : syracuseStep 2424127 = 3636191) B3636191
theorem B3232169 : Blo 2153435 3232169 := bstep (se 2 (by rfl) ⟨1212063, by rfl⟩ : syracuseStep 3232169 = 2424127) B2424127
theorem B2154779 : Blo 2153435 2154779 := bstep (se 1 (by rfl) ⟨1616084, by rfl⟩ : syracuseStep 2154779 = 3232169) B3232169
theorem B8181445 : Blo 2153435 8181445 := bbase (se 4 (by rfl) ⟨767010, by rfl⟩ : syracuseStep 8181445 = 1534021) (by norm_num)
theorem B10908593 : Blo 2153435 10908593 := bstep (se 2 (by rfl) ⟨4090722, by rfl⟩ : syracuseStep 10908593 = 8181445) B8181445
theorem B7272395 : Blo 2153435 7272395 := bstep (se 1 (by rfl) ⟨5454296, by rfl⟩ : syracuseStep 7272395 = 10908593) B10908593
theorem B4848263 : Blo 2153435 4848263 := bstep (se 1 (by rfl) ⟨3636197, by rfl⟩ : syracuseStep 4848263 = 7272395) B7272395
theorem B3232175 : Blo 2153435 3232175 := bstep (se 1 (by rfl) ⟨2424131, by rfl⟩ : syracuseStep 3232175 = 4848263) B4848263
theorem B2154783 : Blo 2153435 2154783 := bstep (se 1 (by rfl) ⟨1616087, by rfl⟩ : syracuseStep 2154783 = 3232175) B3232175
theorem B3232181 : Blo 2153435 3232181 := bbase (se 5 (by rfl) ⟨151508, by rfl⟩ : syracuseStep 3232181 = 303017) (by norm_num)
theorem B2154787 : Blo 2153435 2154787 := bstep (se 1 (by rfl) ⟨1616090, by rfl⟩ : syracuseStep 2154787 = 3232181) B3232181
theorem B5454317 : Blo 2153435 5454317 := bbase (se 3 (by rfl) ⟨1022684, by rfl⟩ : syracuseStep 5454317 = 2045369) (by norm_num)
theorem B3636211 : Blo 2153435 3636211 := bstep (se 1 (by rfl) ⟨2727158, by rfl⟩ : syracuseStep 3636211 = 5454317) B5454317
theorem B4848281 : Blo 2153435 4848281 := bstep (se 2 (by rfl) ⟨1818105, by rfl⟩ : syracuseStep 4848281 = 3636211) B3636211
theorem B3232187 : Blo 2153435 3232187 := bstep (se 1 (by rfl) ⟨2424140, by rfl⟩ : syracuseStep 3232187 = 4848281) B4848281
theorem B2154791 : Blo 2153435 2154791 := bstep (se 1 (by rfl) ⟨1616093, by rfl⟩ : syracuseStep 2154791 = 3232187) B3232187
theorem B2424145 : Blo 2153435 2424145 := bbase (se 2 (by rfl) ⟨909054, by rfl⟩ : syracuseStep 2424145 = 1818109) (by norm_num)
theorem B3232193 : Blo 2153435 3232193 := bstep (se 2 (by rfl) ⟨1212072, by rfl⟩ : syracuseStep 3232193 = 2424145) B2424145
theorem B2154795 : Blo 2153435 2154795 := bstep (se 1 (by rfl) ⟨1616096, by rfl⟩ : syracuseStep 2154795 = 3232193) B3232193
theorem B2301049 : Blo 2153435 2301049 := bbase (se 2 (by rfl) ⟨862893, by rfl⟩ : syracuseStep 2301049 = 1725787) (by norm_num)
theorem B3068065 : Blo 2153435 3068065 := bstep (se 2 (by rfl) ⟨1150524, by rfl⟩ : syracuseStep 3068065 = 2301049) B2301049
theorem B4090753 : Blo 2153435 4090753 := bstep (se 2 (by rfl) ⟨1534032, by rfl⟩ : syracuseStep 4090753 = 3068065) B3068065
theorem B5454337 : Blo 2153435 5454337 := bstep (se 2 (by rfl) ⟨2045376, by rfl⟩ : syracuseStep 5454337 = 4090753) B4090753
theorem B7272449 : Blo 2153435 7272449 := bstep (se 2 (by rfl) ⟨2727168, by rfl⟩ : syracuseStep 7272449 = 5454337) B5454337
theorem B4848299 : Blo 2153435 4848299 := bstep (se 1 (by rfl) ⟨3636224, by rfl⟩ : syracuseStep 4848299 = 7272449) B7272449
theorem B3232199 : Blo 2153435 3232199 := bstep (se 1 (by rfl) ⟨2424149, by rfl⟩ : syracuseStep 3232199 = 4848299) B4848299
theorem B2154799 : Blo 2153435 2154799 := bstep (se 1 (by rfl) ⟨1616099, by rfl⟩ : syracuseStep 2154799 = 3232199) B3232199
theorem B3232205 : Blo 2153435 3232205 := bbase (se 3 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 3232205 = 1212077) (by norm_num)
theorem B2154803 : Blo 2153435 2154803 := bstep (se 1 (by rfl) ⟨1616102, by rfl⟩ : syracuseStep 2154803 = 3232205) B3232205
theorem B4848317 : Blo 2153435 4848317 := bbase (se 3 (by rfl) ⟨909059, by rfl⟩ : syracuseStep 4848317 = 1818119) (by norm_num)
theorem B3232211 : Blo 2153435 3232211 := bstep (se 1 (by rfl) ⟨2424158, by rfl⟩ : syracuseStep 3232211 = 4848317) B4848317
theorem B2154807 : Blo 2153435 2154807 := bstep (se 1 (by rfl) ⟨1616105, by rfl⟩ : syracuseStep 2154807 = 3232211) B3232211
theorem B3636245 : Blo 2153435 3636245 := bbase (se 6 (by rfl) ⟨85224, by rfl⟩ : syracuseStep 3636245 = 170449) (by norm_num)
theorem B2424163 : Blo 2153435 2424163 := bstep (se 1 (by rfl) ⟨1818122, by rfl⟩ : syracuseStep 2424163 = 3636245) B3636245
theorem B3232217 : Blo 2153435 3232217 := bstep (se 2 (by rfl) ⟨1212081, by rfl⟩ : syracuseStep 3232217 = 2424163) B2424163
theorem B2154811 : Blo 2153435 2154811 := bstep (se 1 (by rfl) ⟨1616108, by rfl⟩ : syracuseStep 2154811 = 3232217) B3232217
theorem B4914485 : Blo 2153435 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B3276323 : Blo 2153435 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2184215 : Blo 2153435 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B23298293 : Blo 2153435 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B15532195 : Blo 2153435 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B20709593 : Blo 2153435 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B13806395 : Blo 2153435 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B9204263 : Blo 2153435 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B6136175 : Blo 2153435 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B16363133 : Blo 2153435 16363133 := bstep (se 3 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 16363133 = 6136175) B6136175
theorem B10908755 : Blo 2153435 10908755 := bstep (se 1 (by rfl) ⟨8181566, by rfl⟩ : syracuseStep 10908755 = 16363133) B16363133
theorem B7272503 : Blo 2153435 7272503 := bstep (se 1 (by rfl) ⟨5454377, by rfl⟩ : syracuseStep 7272503 = 10908755) B10908755
theorem B4848335 : Blo 2153435 4848335 := bstep (se 1 (by rfl) ⟨3636251, by rfl⟩ : syracuseStep 4848335 = 7272503) B7272503
theorem B3232223 : Blo 2153435 3232223 := bstep (se 1 (by rfl) ⟨2424167, by rfl⟩ : syracuseStep 3232223 = 4848335) B4848335
theorem B2154815 : Blo 2153435 2154815 := bstep (se 1 (by rfl) ⟨1616111, by rfl⟩ : syracuseStep 2154815 = 3232223) B3232223
theorem B3232229 : Blo 2153435 3232229 := bbase (se 4 (by rfl) ⟨303021, by rfl⟩ : syracuseStep 3232229 = 606043) (by norm_num)
theorem B2154819 : Blo 2153435 2154819 := bstep (se 1 (by rfl) ⟨1616114, by rfl⟩ : syracuseStep 2154819 = 3232229) B3232229
theorem B10354837 : Blo 2153435 10354837 := bbase (se 6 (by rfl) ⟨242691, by rfl⟩ : syracuseStep 10354837 = 485383) (by norm_num)
theorem B13806449 : Blo 2153435 13806449 := bstep (se 2 (by rfl) ⟨5177418, by rfl⟩ : syracuseStep 13806449 = 10354837) B10354837
theorem B9204299 : Blo 2153435 9204299 := bstep (se 1 (by rfl) ⟨6903224, by rfl⟩ : syracuseStep 9204299 = 13806449) B13806449
theorem B6136199 : Blo 2153435 6136199 := bstep (se 1 (by rfl) ⟨4602149, by rfl⟩ : syracuseStep 6136199 = 9204299) B9204299
theorem B4090799 : Blo 2153435 4090799 := bstep (se 1 (by rfl) ⟨3068099, by rfl⟩ : syracuseStep 4090799 = 6136199) B6136199
theorem B2727199 : Blo 2153435 2727199 := bstep (se 1 (by rfl) ⟨2045399, by rfl⟩ : syracuseStep 2727199 = 4090799) B4090799
theorem B3636265 : Blo 2153435 3636265 := bstep (se 2 (by rfl) ⟨1363599, by rfl⟩ : syracuseStep 3636265 = 2727199) B2727199
theorem B4848353 : Blo 2153435 4848353 := bstep (se 2 (by rfl) ⟨1818132, by rfl⟩ : syracuseStep 4848353 = 3636265) B3636265
theorem B3232235 : Blo 2153435 3232235 := bstep (se 1 (by rfl) ⟨2424176, by rfl⟩ : syracuseStep 3232235 = 4848353) B4848353
theorem B2154823 : Blo 2153435 2154823 := bstep (se 1 (by rfl) ⟨1616117, by rfl⟩ : syracuseStep 2154823 = 3232235) B3232235
theorem B2424181 : Blo 2153435 2424181 := bbase (se 5 (by rfl) ⟨113633, by rfl⟩ : syracuseStep 2424181 = 227267) (by norm_num)
theorem B3232241 : Blo 2153435 3232241 := bstep (se 2 (by rfl) ⟨1212090, by rfl⟩ : syracuseStep 3232241 = 2424181) B2424181
theorem B2154827 : Blo 2153435 2154827 := bstep (se 1 (by rfl) ⟨1616120, by rfl⟩ : syracuseStep 2154827 = 3232241) B3232241
theorem B2727209 : Blo 2153435 2727209 := bbase (se 2 (by rfl) ⟨1022703, by rfl⟩ : syracuseStep 2727209 = 2045407) (by norm_num)
theorem B7272557 : Blo 2153435 7272557 := bstep (se 3 (by rfl) ⟨1363604, by rfl⟩ : syracuseStep 7272557 = 2727209) B2727209
theorem B4848371 : Blo 2153435 4848371 := bstep (se 1 (by rfl) ⟨3636278, by rfl⟩ : syracuseStep 4848371 = 7272557) B7272557
theorem B3232247 : Blo 2153435 3232247 := bstep (se 1 (by rfl) ⟨2424185, by rfl⟩ : syracuseStep 3232247 = 4848371) B4848371
theorem B2154831 : Blo 2153435 2154831 := bstep (se 1 (by rfl) ⟨1616123, by rfl⟩ : syracuseStep 2154831 = 3232247) B3232247
theorem B3232253 : Blo 2153435 3232253 := bbase (se 3 (by rfl) ⟨606047, by rfl⟩ : syracuseStep 3232253 = 1212095) (by norm_num)
theorem B2154835 : Blo 2153435 2154835 := bstep (se 1 (by rfl) ⟨1616126, by rfl⟩ : syracuseStep 2154835 = 3232253) B3232253
theorem B4848389 : Blo 2153435 4848389 := bbase (se 4 (by rfl) ⟨454536, by rfl⟩ : syracuseStep 4848389 = 909073) (by norm_num)
theorem B3232259 : Blo 2153435 3232259 := bstep (se 1 (by rfl) ⟨2424194, by rfl⟩ : syracuseStep 3232259 = 4848389) B4848389
theorem B2154839 : Blo 2153435 2154839 := bstep (se 1 (by rfl) ⟨1616129, by rfl⟩ : syracuseStep 2154839 = 3232259) B3232259
theorem B4090837 : Blo 2153435 4090837 := bbase (se 7 (by rfl) ⟨47939, by rfl⟩ : syracuseStep 4090837 = 95879) (by norm_num)
theorem B5454449 : Blo 2153435 5454449 := bstep (se 2 (by rfl) ⟨2045418, by rfl⟩ : syracuseStep 5454449 = 4090837) B4090837
theorem B3636299 : Blo 2153435 3636299 := bstep (se 1 (by rfl) ⟨2727224, by rfl⟩ : syracuseStep 3636299 = 5454449) B5454449
theorem B2424199 : Blo 2153435 2424199 := bstep (se 1 (by rfl) ⟨1818149, by rfl⟩ : syracuseStep 2424199 = 3636299) B3636299
theorem B3232265 : Blo 2153435 3232265 := bstep (se 2 (by rfl) ⟨1212099, by rfl⟩ : syracuseStep 3232265 = 2424199) B2424199
theorem B2154843 : Blo 2153435 2154843 := bstep (se 1 (by rfl) ⟨1616132, by rfl⟩ : syracuseStep 2154843 = 3232265) B3232265
theorem B10908917 : Blo 2153435 10908917 := bbase (se 5 (by rfl) ⟨511355, by rfl⟩ : syracuseStep 10908917 = 1022711) (by norm_num)
theorem B7272611 : Blo 2153435 7272611 := bstep (se 1 (by rfl) ⟨5454458, by rfl⟩ : syracuseStep 7272611 = 10908917) B10908917
theorem B4848407 : Blo 2153435 4848407 := bstep (se 1 (by rfl) ⟨3636305, by rfl⟩ : syracuseStep 4848407 = 7272611) B7272611
theorem B3232271 : Blo 2153435 3232271 := bstep (se 1 (by rfl) ⟨2424203, by rfl⟩ : syracuseStep 3232271 = 4848407) B4848407
theorem B2154847 : Blo 2153435 2154847 := bstep (se 1 (by rfl) ⟨1616135, by rfl⟩ : syracuseStep 2154847 = 3232271) B3232271
theorem B3232277 : Blo 2153435 3232277 := bbase (se 6 (by rfl) ⟨75756, by rfl⟩ : syracuseStep 3232277 = 151513) (by norm_num)
theorem B2154851 : Blo 2153435 2154851 := bstep (se 1 (by rfl) ⟨1616138, by rfl⟩ : syracuseStep 2154851 = 3232277) B3232277
theorem B11649365 : Blo 2153435 11649365 := bbase (se 10 (by rfl) ⟨17064, by rfl⟩ : syracuseStep 11649365 = 34129) (by norm_num)
theorem B7766243 : Blo 2153435 7766243 := bstep (se 1 (by rfl) ⟨5824682, by rfl⟩ : syracuseStep 7766243 = 11649365) B11649365
theorem B5177495 : Blo 2153435 5177495 := bstep (se 1 (by rfl) ⟨3883121, by rfl⟩ : syracuseStep 5177495 = 7766243) B7766243
theorem B3451663 : Blo 2153435 3451663 := bstep (se 1 (by rfl) ⟨2588747, by rfl⟩ : syracuseStep 3451663 = 5177495) B5177495
theorem B18408869 : Blo 2153435 18408869 := bstep (se 4 (by rfl) ⟨1725831, by rfl⟩ : syracuseStep 18408869 = 3451663) B3451663
theorem B12272579 : Blo 2153435 12272579 := bstep (se 1 (by rfl) ⟨9204434, by rfl⟩ : syracuseStep 12272579 = 18408869) B18408869
theorem B8181719 : Blo 2153435 8181719 := bstep (se 1 (by rfl) ⟨6136289, by rfl⟩ : syracuseStep 8181719 = 12272579) B12272579
theorem B5454479 : Blo 2153435 5454479 := bstep (se 1 (by rfl) ⟨4090859, by rfl⟩ : syracuseStep 5454479 = 8181719) B8181719
theorem B3636319 : Blo 2153435 3636319 := bstep (se 1 (by rfl) ⟨2727239, by rfl⟩ : syracuseStep 3636319 = 5454479) B5454479
theorem B4848425 : Blo 2153435 4848425 := bstep (se 2 (by rfl) ⟨1818159, by rfl⟩ : syracuseStep 4848425 = 3636319) B3636319
theorem B3232283 : Blo 2153435 3232283 := bstep (se 1 (by rfl) ⟨2424212, by rfl⟩ : syracuseStep 3232283 = 4848425) B4848425
theorem B2154855 : Blo 2153435 2154855 := bstep (se 1 (by rfl) ⟨1616141, by rfl⟩ : syracuseStep 2154855 = 3232283) B3232283
theorem B2424217 : Blo 2153435 2424217 := bbase (se 2 (by rfl) ⟨909081, by rfl⟩ : syracuseStep 2424217 = 1818163) (by norm_num)
theorem B3232289 : Blo 2153435 3232289 := bstep (se 2 (by rfl) ⟨1212108, by rfl⟩ : syracuseStep 3232289 = 2424217) B2424217
theorem B2154859 : Blo 2153435 2154859 := bstep (se 1 (by rfl) ⟨1616144, by rfl⟩ : syracuseStep 2154859 = 3232289) B3232289
theorem B8181749 : Blo 2153435 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B5454499 : Blo 2153435 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B7272665 : Blo 2153435 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B4848443 : Blo 2153435 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B3232295 : Blo 2153435 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B2154863 : Blo 2153435 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B3232301 : Blo 2153435 3232301 := bbase (se 3 (by rfl) ⟨606056, by rfl⟩ : syracuseStep 3232301 = 1212113) (by norm_num)
theorem B2154867 : Blo 2153435 2154867 := bstep (se 1 (by rfl) ⟨1616150, by rfl⟩ : syracuseStep 2154867 = 3232301) B3232301
theorem B4848461 : Blo 2153435 4848461 := bbase (se 3 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 4848461 = 1818173) (by norm_num)
theorem B3232307 : Blo 2153435 3232307 := bstep (se 1 (by rfl) ⟨2424230, by rfl⟩ : syracuseStep 3232307 = 4848461) B4848461
theorem B2154871 : Blo 2153435 2154871 := bstep (se 1 (by rfl) ⟨1616153, by rfl⟩ : syracuseStep 2154871 = 3232307) B3232307
theorem B2727265 : Blo 2153435 2727265 := bbase (se 2 (by rfl) ⟨1022724, by rfl⟩ : syracuseStep 2727265 = 2045449) (by norm_num)
theorem B3636353 : Blo 2153435 3636353 := bstep (se 2 (by rfl) ⟨1363632, by rfl⟩ : syracuseStep 3636353 = 2727265) B2727265
theorem B2424235 : Blo 2153435 2424235 := bstep (se 1 (by rfl) ⟨1818176, by rfl⟩ : syracuseStep 2424235 = 3636353) B3636353
theorem B3232313 : Blo 2153435 3232313 := bstep (se 2 (by rfl) ⟨1212117, by rfl⟩ : syracuseStep 3232313 = 2424235) B2424235
theorem B2154875 : Blo 2153435 2154875 := bstep (se 1 (by rfl) ⟨1616156, by rfl⟩ : syracuseStep 2154875 = 3232313) B3232313
theorem B24545429 : Blo 2153435 24545429 := bbase (se 6 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 24545429 = 1150567) (by norm_num)
theorem B16363619 : Blo 2153435 16363619 := bstep (se 1 (by rfl) ⟨12272714, by rfl⟩ : syracuseStep 16363619 = 24545429) B24545429
theorem B10909079 : Blo 2153435 10909079 := bstep (se 1 (by rfl) ⟨8181809, by rfl⟩ : syracuseStep 10909079 = 16363619) B16363619
theorem B7272719 : Blo 2153435 7272719 := bstep (se 1 (by rfl) ⟨5454539, by rfl⟩ : syracuseStep 7272719 = 10909079) B10909079
theorem B4848479 : Blo 2153435 4848479 := bstep (se 1 (by rfl) ⟨3636359, by rfl⟩ : syracuseStep 4848479 = 7272719) B7272719
theorem B3232319 : Blo 2153435 3232319 := bstep (se 1 (by rfl) ⟨2424239, by rfl⟩ : syracuseStep 3232319 = 4848479) B4848479
theorem B2154879 : Blo 2153435 2154879 := bstep (se 1 (by rfl) ⟨1616159, by rfl⟩ : syracuseStep 2154879 = 3232319) B3232319
theorem B3232325 : Blo 2153435 3232325 := bbase (se 4 (by rfl) ⟨303030, by rfl⟩ : syracuseStep 3232325 = 606061) (by norm_num)
theorem B2154883 : Blo 2153435 2154883 := bstep (se 1 (by rfl) ⟨1616162, by rfl⟩ : syracuseStep 2154883 = 3232325) B3232325
theorem B3636373 : Blo 2153435 3636373 := bbase (se 6 (by rfl) ⟨85227, by rfl⟩ : syracuseStep 3636373 = 170455) (by norm_num)
theorem B4848497 : Blo 2153435 4848497 := bstep (se 2 (by rfl) ⟨1818186, by rfl⟩ : syracuseStep 4848497 = 3636373) B3636373
theorem B3232331 : Blo 2153435 3232331 := bstep (se 1 (by rfl) ⟨2424248, by rfl⟩ : syracuseStep 3232331 = 4848497) B4848497
theorem B2154887 : Blo 2153435 2154887 := bstep (se 1 (by rfl) ⟨1616165, by rfl⟩ : syracuseStep 2154887 = 3232331) B3232331
theorem B2424253 : Blo 2153435 2424253 := bbase (se 3 (by rfl) ⟨454547, by rfl⟩ : syracuseStep 2424253 = 909095) (by norm_num)
theorem B3232337 : Blo 2153435 3232337 := bstep (se 2 (by rfl) ⟨1212126, by rfl⟩ : syracuseStep 3232337 = 2424253) B2424253
theorem B2154891 : Blo 2153435 2154891 := bstep (se 1 (by rfl) ⟨1616168, by rfl⟩ : syracuseStep 2154891 = 3232337) B3232337
theorem B7272773 : Blo 2153435 7272773 := bbase (se 4 (by rfl) ⟨681822, by rfl⟩ : syracuseStep 7272773 = 1363645) (by norm_num)
theorem B4848515 : Blo 2153435 4848515 := bstep (se 1 (by rfl) ⟨3636386, by rfl⟩ : syracuseStep 4848515 = 7272773) B7272773
theorem B3232343 : Blo 2153435 3232343 := bstep (se 1 (by rfl) ⟨2424257, by rfl⟩ : syracuseStep 3232343 = 4848515) B4848515
theorem B2154895 : Blo 2153435 2154895 := bstep (se 1 (by rfl) ⟨1616171, by rfl⟩ : syracuseStep 2154895 = 3232343) B3232343
theorem B3232349 : Blo 2153435 3232349 := bbase (se 3 (by rfl) ⟨606065, by rfl⟩ : syracuseStep 3232349 = 1212131) (by norm_num)
theorem B2154899 : Blo 2153435 2154899 := bstep (se 1 (by rfl) ⟨1616174, by rfl⟩ : syracuseStep 2154899 = 3232349) B3232349
theorem B4848533 : Blo 2153435 4848533 := bbase (se 6 (by rfl) ⟨113637, by rfl⟩ : syracuseStep 4848533 = 227275) (by norm_num)
theorem B3232355 : Blo 2153435 3232355 := bstep (se 1 (by rfl) ⟨2424266, by rfl⟩ : syracuseStep 3232355 = 4848533) B4848533
theorem B2154903 : Blo 2153435 2154903 := bstep (se 1 (by rfl) ⟨1616177, by rfl⟩ : syracuseStep 2154903 = 3232355) B3232355
theorem B5177621 : Blo 2153435 5177621 := bbase (se 6 (by rfl) ⟨121350, by rfl⟩ : syracuseStep 5177621 = 242701) (by norm_num)
theorem B3451747 : Blo 2153435 3451747 := bstep (se 1 (by rfl) ⟨2588810, by rfl⟩ : syracuseStep 3451747 = 5177621) B5177621
theorem B4602329 : Blo 2153435 4602329 := bstep (se 2 (by rfl) ⟨1725873, by rfl⟩ : syracuseStep 4602329 = 3451747) B3451747
theorem B3068219 : Blo 2153435 3068219 := bstep (se 1 (by rfl) ⟨2301164, by rfl⟩ : syracuseStep 3068219 = 4602329) B4602329
theorem B8181917 : Blo 2153435 8181917 := bstep (se 3 (by rfl) ⟨1534109, by rfl⟩ : syracuseStep 8181917 = 3068219) B3068219
theorem B5454611 : Blo 2153435 5454611 := bstep (se 1 (by rfl) ⟨4090958, by rfl⟩ : syracuseStep 5454611 = 8181917) B8181917
theorem B3636407 : Blo 2153435 3636407 := bstep (se 1 (by rfl) ⟨2727305, by rfl⟩ : syracuseStep 3636407 = 5454611) B5454611
theorem B2424271 : Blo 2153435 2424271 := bstep (se 1 (by rfl) ⟨1818203, by rfl⟩ : syracuseStep 2424271 = 3636407) B3636407
theorem B3232361 : Blo 2153435 3232361 := bstep (se 2 (by rfl) ⟨1212135, by rfl⟩ : syracuseStep 3232361 = 2424271) B2424271
theorem B2154907 : Blo 2153435 2154907 := bstep (se 1 (by rfl) ⟨1616180, by rfl⟩ : syracuseStep 2154907 = 3232361) B3232361
theorem B5177629 : Blo 2153435 5177629 := bbase (se 3 (by rfl) ⟨970805, by rfl⟩ : syracuseStep 5177629 = 1941611) (by norm_num)
theorem B6903505 : Blo 2153435 6903505 := bstep (se 2 (by rfl) ⟨2588814, by rfl⟩ : syracuseStep 6903505 = 5177629) B5177629
theorem B9204673 : Blo 2153435 9204673 := bstep (se 2 (by rfl) ⟨3451752, by rfl⟩ : syracuseStep 9204673 = 6903505) B6903505
theorem B12272897 : Blo 2153435 12272897 := bstep (se 2 (by rfl) ⟨4602336, by rfl⟩ : syracuseStep 12272897 = 9204673) B9204673
theorem B8181931 : Blo 2153435 8181931 := bstep (se 1 (by rfl) ⟨6136448, by rfl⟩ : syracuseStep 8181931 = 12272897) B12272897
theorem B10909241 : Blo 2153435 10909241 := bstep (se 2 (by rfl) ⟨4090965, by rfl⟩ : syracuseStep 10909241 = 8181931) B8181931
theorem B7272827 : Blo 2153435 7272827 := bstep (se 1 (by rfl) ⟨5454620, by rfl⟩ : syracuseStep 7272827 = 10909241) B10909241
theorem B4848551 : Blo 2153435 4848551 := bstep (se 1 (by rfl) ⟨3636413, by rfl⟩ : syracuseStep 4848551 = 7272827) B7272827
theorem B3232367 : Blo 2153435 3232367 := bstep (se 1 (by rfl) ⟨2424275, by rfl⟩ : syracuseStep 3232367 = 4848551) B4848551
theorem B2154911 : Blo 2153435 2154911 := bstep (se 1 (by rfl) ⟨1616183, by rfl⟩ : syracuseStep 2154911 = 3232367) B3232367
theorem B3232373 : Blo 2153435 3232373 := bbase (se 5 (by rfl) ⟨151517, by rfl⟩ : syracuseStep 3232373 = 303035) (by norm_num)
theorem B2154915 : Blo 2153435 2154915 := bstep (se 1 (by rfl) ⟨1616186, by rfl⟩ : syracuseStep 2154915 = 3232373) B3232373
theorem B4090981 : Blo 2153435 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B5454641 : Blo 2153435 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B3636427 : Blo 2153435 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B4848569 : Blo 2153435 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B3232379 : Blo 2153435 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B2154919 : Blo 2153435 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B2424289 : Blo 2153435 2424289 := bbase (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) (by norm_num)
theorem B3232385 : Blo 2153435 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B2154923 : Blo 2153435 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B5454661 : Blo 2153435 5454661 := bbase (se 4 (by rfl) ⟨511374, by rfl⟩ : syracuseStep 5454661 = 1022749) (by norm_num)
theorem B7272881 : Blo 2153435 7272881 := bstep (se 2 (by rfl) ⟨2727330, by rfl⟩ : syracuseStep 7272881 = 5454661) B5454661
theorem B4848587 : Blo 2153435 4848587 := bstep (se 1 (by rfl) ⟨3636440, by rfl⟩ : syracuseStep 4848587 = 7272881) B7272881
theorem B3232391 : Blo 2153435 3232391 := bstep (se 1 (by rfl) ⟨2424293, by rfl⟩ : syracuseStep 3232391 = 4848587) B4848587
theorem B2154927 : Blo 2153435 2154927 := bstep (se 1 (by rfl) ⟨1616195, by rfl⟩ : syracuseStep 2154927 = 3232391) B3232391
theorem B3232397 : Blo 2153435 3232397 := bbase (se 3 (by rfl) ⟨606074, by rfl⟩ : syracuseStep 3232397 = 1212149) (by norm_num)
theorem B2154931 : Blo 2153435 2154931 := bstep (se 1 (by rfl) ⟨1616198, by rfl⟩ : syracuseStep 2154931 = 3232397) B3232397
theorem B4848605 : Blo 2153435 4848605 := bbase (se 3 (by rfl) ⟨909113, by rfl⟩ : syracuseStep 4848605 = 1818227) (by norm_num)
theorem B3232403 : Blo 2153435 3232403 := bstep (se 1 (by rfl) ⟨2424302, by rfl⟩ : syracuseStep 3232403 = 4848605) B4848605
theorem B2154935 : Blo 2153435 2154935 := bstep (se 1 (by rfl) ⟨1616201, by rfl⟩ : syracuseStep 2154935 = 3232403) B3232403
theorem B3636461 : Blo 2153435 3636461 := bbase (se 3 (by rfl) ⟨681836, by rfl⟩ : syracuseStep 3636461 = 1363673) (by norm_num)
theorem B2424307 : Blo 2153435 2424307 := bstep (se 1 (by rfl) ⟨1818230, by rfl⟩ : syracuseStep 2424307 = 3636461) B3636461
theorem B3232409 : Blo 2153435 3232409 := bstep (se 2 (by rfl) ⟨1212153, by rfl⟩ : syracuseStep 3232409 = 2424307) B2424307
theorem B2154939 : Blo 2153435 2154939 := bstep (se 1 (by rfl) ⟨1616204, by rfl⟩ : syracuseStep 2154939 = 3232409) B3232409
theorem B13106069 : Blo 2153435 13106069 := bbase (se 6 (by rfl) ⟨307173, by rfl⟩ : syracuseStep 13106069 = 614347) (by norm_num)
theorem B8737379 : Blo 2153435 8737379 := bstep (se 1 (by rfl) ⟨6553034, by rfl⟩ : syracuseStep 8737379 = 13106069) B13106069
theorem B5824919 : Blo 2153435 5824919 := bstep (se 1 (by rfl) ⟨4368689, by rfl⟩ : syracuseStep 5824919 = 8737379) B8737379
theorem B15533117 : Blo 2153435 15533117 := bstep (se 3 (by rfl) ⟨2912459, by rfl⟩ : syracuseStep 15533117 = 5824919) B5824919
theorem B10355411 : Blo 2153435 10355411 := bstep (se 1 (by rfl) ⟨7766558, by rfl⟩ : syracuseStep 10355411 = 15533117) B15533117
theorem B27614429 : Blo 2153435 27614429 := bstep (se 3 (by rfl) ⟨5177705, by rfl⟩ : syracuseStep 27614429 = 10355411) B10355411
theorem B18409619 : Blo 2153435 18409619 := bstep (se 1 (by rfl) ⟨13807214, by rfl⟩ : syracuseStep 18409619 = 27614429) B27614429
theorem B12273079 : Blo 2153435 12273079 := bstep (se 1 (by rfl) ⟨9204809, by rfl⟩ : syracuseStep 12273079 = 18409619) B18409619
theorem B16364105 : Blo 2153435 16364105 := bstep (se 2 (by rfl) ⟨6136539, by rfl⟩ : syracuseStep 16364105 = 12273079) B12273079
theorem B10909403 : Blo 2153435 10909403 := bstep (se 1 (by rfl) ⟨8182052, by rfl⟩ : syracuseStep 10909403 = 16364105) B16364105
theorem B7272935 : Blo 2153435 7272935 := bstep (se 1 (by rfl) ⟨5454701, by rfl⟩ : syracuseStep 7272935 = 10909403) B10909403
theorem B4848623 : Blo 2153435 4848623 := bstep (se 1 (by rfl) ⟨3636467, by rfl⟩ : syracuseStep 4848623 = 7272935) B7272935
theorem B3232415 : Blo 2153435 3232415 := bstep (se 1 (by rfl) ⟨2424311, by rfl⟩ : syracuseStep 3232415 = 4848623) B4848623
theorem B2154943 : Blo 2153435 2154943 := bstep (se 1 (by rfl) ⟨1616207, by rfl⟩ : syracuseStep 2154943 = 3232415) B3232415
theorem B3232421 : Blo 2153435 3232421 := bbase (se 4 (by rfl) ⟨303039, by rfl⟩ : syracuseStep 3232421 = 606079) (by norm_num)
theorem B2154947 : Blo 2153435 2154947 := bstep (se 1 (by rfl) ⟨1616210, by rfl⟩ : syracuseStep 2154947 = 3232421) B3232421
theorem B2727361 : Blo 2153435 2727361 := bbase (se 2 (by rfl) ⟨1022760, by rfl⟩ : syracuseStep 2727361 = 2045521) (by norm_num)
theorem B3636481 : Blo 2153435 3636481 := bstep (se 2 (by rfl) ⟨1363680, by rfl⟩ : syracuseStep 3636481 = 2727361) B2727361
theorem B4848641 : Blo 2153435 4848641 := bstep (se 2 (by rfl) ⟨1818240, by rfl⟩ : syracuseStep 4848641 = 3636481) B3636481
theorem B3232427 : Blo 2153435 3232427 := bstep (se 1 (by rfl) ⟨2424320, by rfl⟩ : syracuseStep 3232427 = 4848641) B4848641
theorem B2154951 : Blo 2153435 2154951 := bstep (se 1 (by rfl) ⟨1616213, by rfl⟩ : syracuseStep 2154951 = 3232427) B3232427
theorem B2424325 : Blo 2153435 2424325 := bbase (se 4 (by rfl) ⟨227280, by rfl⟩ : syracuseStep 2424325 = 454561) (by norm_num)
theorem B3232433 : Blo 2153435 3232433 := bstep (se 2 (by rfl) ⟨1212162, by rfl⟩ : syracuseStep 3232433 = 2424325) B2424325
theorem B2154955 : Blo 2153435 2154955 := bstep (se 1 (by rfl) ⟨1616216, by rfl⟩ : syracuseStep 2154955 = 3232433) B3232433
theorem B3068293 : Blo 2153435 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B4091057 : Blo 2153435 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B2727371 : Blo 2153435 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B7272989 : Blo 2153435 7272989 := bstep (se 3 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 7272989 = 2727371) B2727371
theorem B4848659 : Blo 2153435 4848659 := bstep (se 1 (by rfl) ⟨3636494, by rfl⟩ : syracuseStep 4848659 = 7272989) B7272989
theorem B3232439 : Blo 2153435 3232439 := bstep (se 1 (by rfl) ⟨2424329, by rfl⟩ : syracuseStep 3232439 = 4848659) B4848659
theorem B2154959 : Blo 2153435 2154959 := bstep (se 1 (by rfl) ⟨1616219, by rfl⟩ : syracuseStep 2154959 = 3232439) B3232439
theorem B3232445 : Blo 2153435 3232445 := bbase (se 3 (by rfl) ⟨606083, by rfl⟩ : syracuseStep 3232445 = 1212167) (by norm_num)
theorem B2154963 : Blo 2153435 2154963 := bstep (se 1 (by rfl) ⟨1616222, by rfl⟩ : syracuseStep 2154963 = 3232445) B3232445
theorem B4848677 : Blo 2153435 4848677 := bbase (se 4 (by rfl) ⟨454563, by rfl⟩ : syracuseStep 4848677 = 909127) (by norm_num)
theorem B3232451 : Blo 2153435 3232451 := bstep (se 1 (by rfl) ⟨2424338, by rfl⟩ : syracuseStep 3232451 = 4848677) B4848677
theorem B2154967 : Blo 2153435 2154967 := bstep (se 1 (by rfl) ⟨1616225, by rfl⟩ : syracuseStep 2154967 = 3232451) B3232451
theorem B5454773 : Blo 2153435 5454773 := bbase (se 5 (by rfl) ⟨255692, by rfl⟩ : syracuseStep 5454773 = 511385) (by norm_num)
theorem B3636515 : Blo 2153435 3636515 := bstep (se 1 (by rfl) ⟨2727386, by rfl⟩ : syracuseStep 3636515 = 5454773) B5454773
theorem B2424343 : Blo 2153435 2424343 := bstep (se 1 (by rfl) ⟨1818257, by rfl⟩ : syracuseStep 2424343 = 3636515) B3636515
theorem B3232457 : Blo 2153435 3232457 := bstep (se 2 (by rfl) ⟨1212171, by rfl⟩ : syracuseStep 3232457 = 2424343) B2424343
theorem B2154971 : Blo 2153435 2154971 := bstep (se 1 (by rfl) ⟨1616228, by rfl⟩ : syracuseStep 2154971 = 3232457) B3232457
theorem B2457425 : Blo 2153435 2457425 := bbase (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) (by norm_num)
theorem B6553133 : Blo 2153435 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B4368755 : Blo 2153435 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B11650013 : Blo 2153435 11650013 := bstep (se 3 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 11650013 = 4368755) B4368755
theorem B7766675 : Blo 2153435 7766675 := bstep (se 1 (by rfl) ⟨5825006, by rfl⟩ : syracuseStep 7766675 = 11650013) B11650013
theorem B5177783 : Blo 2153435 5177783 := bstep (se 1 (by rfl) ⟨3883337, by rfl⟩ : syracuseStep 5177783 = 7766675) B7766675
theorem B13807421 : Blo 2153435 13807421 := bstep (se 3 (by rfl) ⟨2588891, by rfl⟩ : syracuseStep 13807421 = 5177783) B5177783
theorem B9204947 : Blo 2153435 9204947 := bstep (se 1 (by rfl) ⟨6903710, by rfl⟩ : syracuseStep 9204947 = 13807421) B13807421
theorem B6136631 : Blo 2153435 6136631 := bstep (se 1 (by rfl) ⟨4602473, by rfl⟩ : syracuseStep 6136631 = 9204947) B9204947
theorem B4091087 : Blo 2153435 4091087 := bstep (se 1 (by rfl) ⟨3068315, by rfl⟩ : syracuseStep 4091087 = 6136631) B6136631
theorem B10909565 : Blo 2153435 10909565 := bstep (se 3 (by rfl) ⟨2045543, by rfl⟩ : syracuseStep 10909565 = 4091087) B4091087
theorem B7273043 : Blo 2153435 7273043 := bstep (se 1 (by rfl) ⟨5454782, by rfl⟩ : syracuseStep 7273043 = 10909565) B10909565
theorem B4848695 : Blo 2153435 4848695 := bstep (se 1 (by rfl) ⟨3636521, by rfl⟩ : syracuseStep 4848695 = 7273043) B7273043
theorem B3232463 : Blo 2153435 3232463 := bstep (se 1 (by rfl) ⟨2424347, by rfl⟩ : syracuseStep 3232463 = 4848695) B4848695
theorem B2154975 : Blo 2153435 2154975 := bstep (se 1 (by rfl) ⟨1616231, by rfl⟩ : syracuseStep 2154975 = 3232463) B3232463
theorem B3232469 : Blo 2153435 3232469 := bbase (se 7 (by rfl) ⟨37880, by rfl⟩ : syracuseStep 3232469 = 75761) (by norm_num)
theorem B2154979 : Blo 2153435 2154979 := bstep (se 1 (by rfl) ⟨1616234, by rfl⟩ : syracuseStep 2154979 = 3232469) B3232469
theorem B5825029 : Blo 2153435 5825029 := bbase (se 4 (by rfl) ⟨546096, by rfl⟩ : syracuseStep 5825029 = 1092193) (by norm_num)
theorem B7766705 : Blo 2153435 7766705 := bstep (se 2 (by rfl) ⟨2912514, by rfl⟩ : syracuseStep 7766705 = 5825029) B5825029
theorem B5177803 : Blo 2153435 5177803 := bstep (se 1 (by rfl) ⟨3883352, by rfl⟩ : syracuseStep 5177803 = 7766705) B7766705
theorem B6903737 : Blo 2153435 6903737 := bstep (se 2 (by rfl) ⟨2588901, by rfl⟩ : syracuseStep 6903737 = 5177803) B5177803
theorem B4602491 : Blo 2153435 4602491 := bstep (se 1 (by rfl) ⟨3451868, by rfl⟩ : syracuseStep 4602491 = 6903737) B6903737
theorem B3068327 : Blo 2153435 3068327 := bstep (se 1 (by rfl) ⟨2301245, by rfl⟩ : syracuseStep 3068327 = 4602491) B4602491
theorem B8182205 : Blo 2153435 8182205 := bstep (se 3 (by rfl) ⟨1534163, by rfl⟩ : syracuseStep 8182205 = 3068327) B3068327
theorem B5454803 : Blo 2153435 5454803 := bstep (se 1 (by rfl) ⟨4091102, by rfl⟩ : syracuseStep 5454803 = 8182205) B8182205
theorem B3636535 : Blo 2153435 3636535 := bstep (se 1 (by rfl) ⟨2727401, by rfl⟩ : syracuseStep 3636535 = 5454803) B5454803
theorem B4848713 : Blo 2153435 4848713 := bstep (se 2 (by rfl) ⟨1818267, by rfl⟩ : syracuseStep 4848713 = 3636535) B3636535
theorem B3232475 : Blo 2153435 3232475 := bstep (se 1 (by rfl) ⟨2424356, by rfl⟩ : syracuseStep 3232475 = 4848713) B4848713
theorem B2154983 : Blo 2153435 2154983 := bstep (se 1 (by rfl) ⟨1616237, by rfl⟩ : syracuseStep 2154983 = 3232475) B3232475
theorem B2424361 : Blo 2153435 2424361 := bbase (se 2 (by rfl) ⟨909135, by rfl⟩ : syracuseStep 2424361 = 1818271) (by norm_num)
theorem B3232481 : Blo 2153435 3232481 := bstep (se 2 (by rfl) ⟨1212180, by rfl⟩ : syracuseStep 3232481 = 2424361) B2424361
theorem B2154987 : Blo 2153435 2154987 := bstep (se 1 (by rfl) ⟨1616240, by rfl⟩ : syracuseStep 2154987 = 3232481) B3232481
theorem B20711285 : Blo 2153435 20711285 := bbase (se 5 (by rfl) ⟨970841, by rfl⟩ : syracuseStep 20711285 = 1941683) (by norm_num)
theorem B13807523 : Blo 2153435 13807523 := bstep (se 1 (by rfl) ⟨10355642, by rfl⟩ : syracuseStep 13807523 = 20711285) B20711285
theorem B9205015 : Blo 2153435 9205015 := bstep (se 1 (by rfl) ⟨6903761, by rfl⟩ : syracuseStep 9205015 = 13807523) B13807523
theorem B12273353 : Blo 2153435 12273353 := bstep (se 2 (by rfl) ⟨4602507, by rfl⟩ : syracuseStep 12273353 = 9205015) B9205015
theorem B8182235 : Blo 2153435 8182235 := bstep (se 1 (by rfl) ⟨6136676, by rfl⟩ : syracuseStep 8182235 = 12273353) B12273353
theorem B5454823 : Blo 2153435 5454823 := bstep (se 1 (by rfl) ⟨4091117, by rfl⟩ : syracuseStep 5454823 = 8182235) B8182235
theorem B7273097 : Blo 2153435 7273097 := bstep (se 2 (by rfl) ⟨2727411, by rfl⟩ : syracuseStep 7273097 = 5454823) B5454823
theorem B4848731 : Blo 2153435 4848731 := bstep (se 1 (by rfl) ⟨3636548, by rfl⟩ : syracuseStep 4848731 = 7273097) B7273097
theorem B3232487 : Blo 2153435 3232487 := bstep (se 1 (by rfl) ⟨2424365, by rfl⟩ : syracuseStep 3232487 = 4848731) B4848731
theorem B2154991 : Blo 2153435 2154991 := bstep (se 1 (by rfl) ⟨1616243, by rfl⟩ : syracuseStep 2154991 = 3232487) B3232487
theorem B3232493 : Blo 2153435 3232493 := bbase (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) (by norm_num)
theorem B2154995 : Blo 2153435 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B4848749 : Blo 2153435 4848749 := bbase (se 3 (by rfl) ⟨909140, by rfl⟩ : syracuseStep 4848749 = 1818281) (by norm_num)
theorem B3232499 : Blo 2153435 3232499 := bstep (se 1 (by rfl) ⟨2424374, by rfl⟩ : syracuseStep 3232499 = 4848749) B4848749
theorem B2154999 : Blo 2153435 2154999 := bstep (se 1 (by rfl) ⟨1616249, by rfl⟩ : syracuseStep 2154999 = 3232499) B3232499
theorem B4091141 : Blo 2153435 4091141 := bbase (se 4 (by rfl) ⟨383544, by rfl⟩ : syracuseStep 4091141 = 767089) (by norm_num)
theorem B2727427 : Blo 2153435 2727427 := bstep (se 1 (by rfl) ⟨2045570, by rfl⟩ : syracuseStep 2727427 = 4091141) B4091141
theorem B3636569 : Blo 2153435 3636569 := bstep (se 2 (by rfl) ⟨1363713, by rfl⟩ : syracuseStep 3636569 = 2727427) B2727427
theorem B2424379 : Blo 2153435 2424379 := bstep (se 1 (by rfl) ⟨1818284, by rfl⟩ : syracuseStep 2424379 = 3636569) B3636569
theorem B3232505 : Blo 2153435 3232505 := bstep (se 2 (by rfl) ⟨1212189, by rfl⟩ : syracuseStep 3232505 = 2424379) B2424379
theorem B2155003 : Blo 2153435 2155003 := bstep (se 1 (by rfl) ⟨1616252, by rfl⟩ : syracuseStep 2155003 = 3232505) B3232505
theorem B6998005 : Blo 2153435 6998005 := bbase (se 5 (by rfl) ⟨328031, by rfl⟩ : syracuseStep 6998005 = 656063) (by norm_num)
theorem B9330673 : Blo 2153435 9330673 := bstep (se 2 (by rfl) ⟨3499002, by rfl⟩ : syracuseStep 9330673 = 6998005) B6998005
theorem B12440897 : Blo 2153435 12440897 := bstep (se 2 (by rfl) ⟨4665336, by rfl⟩ : syracuseStep 12440897 = 9330673) B9330673
theorem B8293931 : Blo 2153435 8293931 := bstep (se 1 (by rfl) ⟨6220448, by rfl⟩ : syracuseStep 8293931 = 12440897) B12440897
theorem B5529287 : Blo 2153435 5529287 := bstep (se 1 (by rfl) ⟨4146965, by rfl⟩ : syracuseStep 5529287 = 8293931) B8293931
theorem B3686191 : Blo 2153435 3686191 := bstep (se 1 (by rfl) ⟨2764643, by rfl⟩ : syracuseStep 3686191 = 5529287) B5529287
theorem B19659685 : Blo 2153435 19659685 := bstep (se 4 (by rfl) ⟨1843095, by rfl⟩ : syracuseStep 19659685 = 3686191) B3686191
theorem B26212913 : Blo 2153435 26212913 := bstep (se 2 (by rfl) ⟨9829842, by rfl⟩ : syracuseStep 26212913 = 19659685) B19659685
theorem B17475275 : Blo 2153435 17475275 := bstep (se 1 (by rfl) ⟨13106456, by rfl⟩ : syracuseStep 17475275 = 26212913) B26212913
theorem B46600733 : Blo 2153435 46600733 := bstep (se 3 (by rfl) ⟨8737637, by rfl⟩ : syracuseStep 46600733 = 17475275) B17475275
theorem B31067155 : Blo 2153435 31067155 := bstep (se 1 (by rfl) ⟨23300366, by rfl⟩ : syracuseStep 31067155 = 46600733) B46600733
theorem B41422873 : Blo 2153435 41422873 := bstep (se 2 (by rfl) ⟨15533577, by rfl⟩ : syracuseStep 41422873 = 31067155) B31067155
theorem B55230497 : Blo 2153435 55230497 := bstep (se 2 (by rfl) ⟨20711436, by rfl⟩ : syracuseStep 55230497 = 41422873) B41422873
theorem B36820331 : Blo 2153435 36820331 := bstep (se 1 (by rfl) ⟨27615248, by rfl⟩ : syracuseStep 36820331 = 55230497) B55230497
theorem B24546887 : Blo 2153435 24546887 := bstep (se 1 (by rfl) ⟨18410165, by rfl⟩ : syracuseStep 24546887 = 36820331) B36820331
theorem B16364591 : Blo 2153435 16364591 := bstep (se 1 (by rfl) ⟨12273443, by rfl⟩ : syracuseStep 16364591 = 24546887) B24546887
theorem B10909727 : Blo 2153435 10909727 := bstep (se 1 (by rfl) ⟨8182295, by rfl⟩ : syracuseStep 10909727 = 16364591) B16364591
theorem B7273151 : Blo 2153435 7273151 := bstep (se 1 (by rfl) ⟨5454863, by rfl⟩ : syracuseStep 7273151 = 10909727) B10909727
theorem B4848767 : Blo 2153435 4848767 := bstep (se 1 (by rfl) ⟨3636575, by rfl⟩ : syracuseStep 4848767 = 7273151) B7273151
theorem B3232511 : Blo 2153435 3232511 := bstep (se 1 (by rfl) ⟨2424383, by rfl⟩ : syracuseStep 3232511 = 4848767) B4848767
theorem B2155007 : Blo 2153435 2155007 := bstep (se 1 (by rfl) ⟨1616255, by rfl⟩ : syracuseStep 2155007 = 3232511) B3232511
theorem B3232517 : Blo 2153435 3232517 := bbase (se 4 (by rfl) ⟨303048, by rfl⟩ : syracuseStep 3232517 = 606097) (by norm_num)
theorem B2155011 : Blo 2153435 2155011 := bstep (se 1 (by rfl) ⟨1616258, by rfl⟩ : syracuseStep 2155011 = 3232517) B3232517
theorem B3636589 : Blo 2153435 3636589 := bbase (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) (by norm_num)
theorem B4848785 : Blo 2153435 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B3232523 : Blo 2153435 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B2155015 : Blo 2153435 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B2424397 : Blo 2153435 2424397 := bbase (se 3 (by rfl) ⟨454574, by rfl⟩ : syracuseStep 2424397 = 909149) (by norm_num)
theorem B3232529 : Blo 2153435 3232529 := bstep (se 2 (by rfl) ⟨1212198, by rfl⟩ : syracuseStep 3232529 = 2424397) B2424397
theorem B2155019 : Blo 2153435 2155019 := bstep (se 1 (by rfl) ⟨1616264, by rfl⟩ : syracuseStep 2155019 = 3232529) B3232529
theorem B7273205 : Blo 2153435 7273205 := bbase (se 5 (by rfl) ⟨340931, by rfl⟩ : syracuseStep 7273205 = 681863) (by norm_num)
theorem B4848803 : Blo 2153435 4848803 := bstep (se 1 (by rfl) ⟨3636602, by rfl⟩ : syracuseStep 4848803 = 7273205) B7273205
theorem B3232535 : Blo 2153435 3232535 := bstep (se 1 (by rfl) ⟨2424401, by rfl⟩ : syracuseStep 3232535 = 4848803) B4848803
theorem B2155023 : Blo 2153435 2155023 := bstep (se 1 (by rfl) ⟨1616267, by rfl⟩ : syracuseStep 2155023 = 3232535) B3232535
theorem B3232541 : Blo 2153435 3232541 := bbase (se 3 (by rfl) ⟨606101, by rfl⟩ : syracuseStep 3232541 = 1212203) (by norm_num)
theorem B2155027 : Blo 2153435 2155027 := bstep (se 1 (by rfl) ⟨1616270, by rfl⟩ : syracuseStep 2155027 = 3232541) B3232541
theorem B4848821 : Blo 2153435 4848821 := bbase (se 5 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 4848821 = 454577) (by norm_num)
theorem B3232547 : Blo 2153435 3232547 := bstep (se 1 (by rfl) ⟨2424410, by rfl⟩ : syracuseStep 3232547 = 4848821) B4848821
theorem B2155031 : Blo 2153435 2155031 := bstep (se 1 (by rfl) ⟨1616273, by rfl⟩ : syracuseStep 2155031 = 3232547) B3232547
theorem B2301301 : Blo 2153435 2301301 := bbase (se 5 (by rfl) ⟨107873, by rfl⟩ : syracuseStep 2301301 = 215747) (by norm_num)
theorem B12273605 : Blo 2153435 12273605 := bstep (se 4 (by rfl) ⟨1150650, by rfl⟩ : syracuseStep 12273605 = 2301301) B2301301
theorem B8182403 : Blo 2153435 8182403 := bstep (se 1 (by rfl) ⟨6136802, by rfl⟩ : syracuseStep 8182403 = 12273605) B12273605
theorem B5454935 : Blo 2153435 5454935 := bstep (se 1 (by rfl) ⟨4091201, by rfl⟩ : syracuseStep 5454935 = 8182403) B8182403
theorem B3636623 : Blo 2153435 3636623 := bstep (se 1 (by rfl) ⟨2727467, by rfl⟩ : syracuseStep 3636623 = 5454935) B5454935
theorem B2424415 : Blo 2153435 2424415 := bstep (se 1 (by rfl) ⟨1818311, by rfl⟩ : syracuseStep 2424415 = 3636623) B3636623
theorem B3232553 : Blo 2153435 3232553 := bstep (se 2 (by rfl) ⟨1212207, by rfl⟩ : syracuseStep 3232553 = 2424415) B2424415
theorem B2155035 : Blo 2153435 2155035 := bstep (se 1 (by rfl) ⟨1616276, by rfl⟩ : syracuseStep 2155035 = 3232553) B3232553
theorem B2301305 : Blo 2153435 2301305 := bbase (se 2 (by rfl) ⟨862989, by rfl⟩ : syracuseStep 2301305 = 1725979) (by norm_num)
theorem B6136813 : Blo 2153435 6136813 := bstep (se 3 (by rfl) ⟨1150652, by rfl⟩ : syracuseStep 6136813 = 2301305) B2301305
theorem B8182417 : Blo 2153435 8182417 := bstep (se 2 (by rfl) ⟨3068406, by rfl⟩ : syracuseStep 8182417 = 6136813) B6136813
theorem B10909889 : Blo 2153435 10909889 := bstep (se 2 (by rfl) ⟨4091208, by rfl⟩ : syracuseStep 10909889 = 8182417) B8182417
theorem B7273259 : Blo 2153435 7273259 := bstep (se 1 (by rfl) ⟨5454944, by rfl⟩ : syracuseStep 7273259 = 10909889) B10909889
theorem B4848839 : Blo 2153435 4848839 := bstep (se 1 (by rfl) ⟨3636629, by rfl⟩ : syracuseStep 4848839 = 7273259) B7273259
theorem B3232559 : Blo 2153435 3232559 := bstep (se 1 (by rfl) ⟨2424419, by rfl⟩ : syracuseStep 3232559 = 4848839) B4848839
theorem B2155039 : Blo 2153435 2155039 := bstep (se 1 (by rfl) ⟨1616279, by rfl⟩ : syracuseStep 2155039 = 3232559) B3232559
theorem B3232565 : Blo 2153435 3232565 := bbase (se 5 (by rfl) ⟨151526, by rfl⟩ : syracuseStep 3232565 = 303053) (by norm_num)
theorem B2155043 : Blo 2153435 2155043 := bstep (se 1 (by rfl) ⟨1616282, by rfl⟩ : syracuseStep 2155043 = 3232565) B3232565
theorem B5454965 : Blo 2153435 5454965 := bbase (se 5 (by rfl) ⟨255701, by rfl⟩ : syracuseStep 5454965 = 511403) (by norm_num)
theorem B3636643 : Blo 2153435 3636643 := bstep (se 1 (by rfl) ⟨2727482, by rfl⟩ : syracuseStep 3636643 = 5454965) B5454965
theorem B4848857 : Blo 2153435 4848857 := bstep (se 2 (by rfl) ⟨1818321, by rfl⟩ : syracuseStep 4848857 = 3636643) B3636643
theorem B3232571 : Blo 2153435 3232571 := bstep (se 1 (by rfl) ⟨2424428, by rfl⟩ : syracuseStep 3232571 = 4848857) B4848857
theorem B2155047 : Blo 2153435 2155047 := bstep (se 1 (by rfl) ⟨1616285, by rfl⟩ : syracuseStep 2155047 = 3232571) B3232571
theorem B2424433 : Blo 2153435 2424433 := bbase (se 2 (by rfl) ⟨909162, by rfl⟩ : syracuseStep 2424433 = 1818325) (by norm_num)
theorem B3232577 : Blo 2153435 3232577 := bstep (se 2 (by rfl) ⟨1212216, by rfl⟩ : syracuseStep 3232577 = 2424433) B2424433
theorem B2155051 : Blo 2153435 2155051 := bstep (se 1 (by rfl) ⟨1616288, by rfl⟩ : syracuseStep 2155051 = 3232577) B3232577
theorem B3546821 : Blo 2153435 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2364547 : Blo 2153435 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3152729 : Blo 2153435 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B8407277 : Blo 2153435 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B5604851 : Blo 2153435 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B3736567 : Blo 2153435 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B19928357 : Blo 2153435 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B13285571 : Blo 2153435 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B141712757 : Blo 2153435 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B94475171 : Blo 2153435 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B251933789 : Blo 2153435 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B167955859 : Blo 2153435 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B223941145 : Blo 2153435 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B298588193 : Blo 2153435 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B199058795 : Blo 2153435 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B132705863 : Blo 2153435 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B88470575 : Blo 2153435 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B58980383 : Blo 2153435 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B39320255 : Blo 2153435 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B26213503 : Blo 2153435 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B34951337 : Blo 2153435 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B23300891 : Blo 2153435 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B15533927 : Blo 2153435 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B10355951 : Blo 2153435 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B6903967 : Blo 2153435 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B9205289 : Blo 2153435 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B6136859 : Blo 2153435 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B4091239 : Blo 2153435 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B5454985 : Blo 2153435 5454985 := bstep (se 2 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 5454985 = 4091239) B4091239
theorem B7273313 : Blo 2153435 7273313 := bstep (se 2 (by rfl) ⟨2727492, by rfl⟩ : syracuseStep 7273313 = 5454985) B5454985
theorem B4848875 : Blo 2153435 4848875 := bstep (se 1 (by rfl) ⟨3636656, by rfl⟩ : syracuseStep 4848875 = 7273313) B7273313
theorem B3232583 : Blo 2153435 3232583 := bstep (se 1 (by rfl) ⟨2424437, by rfl⟩ : syracuseStep 3232583 = 4848875) B4848875
theorem B2155055 : Blo 2153435 2155055 := bstep (se 1 (by rfl) ⟨1616291, by rfl⟩ : syracuseStep 2155055 = 3232583) B3232583
theorem B3232589 : Blo 2153435 3232589 := bbase (se 3 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 3232589 = 1212221) (by norm_num)
theorem B2155059 : Blo 2153435 2155059 := bstep (se 1 (by rfl) ⟨1616294, by rfl⟩ : syracuseStep 2155059 = 3232589) B3232589
theorem B4848893 : Blo 2153435 4848893 := bbase (se 3 (by rfl) ⟨909167, by rfl⟩ : syracuseStep 4848893 = 1818335) (by norm_num)
theorem B3232595 : Blo 2153435 3232595 := bstep (se 1 (by rfl) ⟨2424446, by rfl⟩ : syracuseStep 3232595 = 4848893) B4848893
theorem B2155063 : Blo 2153435 2155063 := bstep (se 1 (by rfl) ⟨1616297, by rfl⟩ : syracuseStep 2155063 = 3232595) B3232595
theorem B3636677 : Blo 2153435 3636677 := bbase (se 4 (by rfl) ⟨340938, by rfl⟩ : syracuseStep 3636677 = 681877) (by norm_num)
theorem B2424451 : Blo 2153435 2424451 := bstep (se 1 (by rfl) ⟨1818338, by rfl⟩ : syracuseStep 2424451 = 3636677) B3636677
theorem B3232601 : Blo 2153435 3232601 := bstep (se 2 (by rfl) ⟨1212225, by rfl⟩ : syracuseStep 3232601 = 2424451) B2424451
theorem B2155067 : Blo 2153435 2155067 := bstep (se 1 (by rfl) ⟨1616300, by rfl⟩ : syracuseStep 2155067 = 3232601) B3232601
theorem B16365077 : Blo 2153435 16365077 := bbase (se 6 (by rfl) ⟨383556, by rfl⟩ : syracuseStep 16365077 = 767113) (by norm_num)
theorem B10910051 : Blo 2153435 10910051 := bstep (se 1 (by rfl) ⟨8182538, by rfl⟩ : syracuseStep 10910051 = 16365077) B16365077
theorem B7273367 : Blo 2153435 7273367 := bstep (se 1 (by rfl) ⟨5455025, by rfl⟩ : syracuseStep 7273367 = 10910051) B10910051
theorem B4848911 : Blo 2153435 4848911 := bstep (se 1 (by rfl) ⟨3636683, by rfl⟩ : syracuseStep 4848911 = 7273367) B7273367
theorem B3232607 : Blo 2153435 3232607 := bstep (se 1 (by rfl) ⟨2424455, by rfl⟩ : syracuseStep 3232607 = 4848911) B4848911
theorem B2155071 : Blo 2153435 2155071 := bstep (se 1 (by rfl) ⟨1616303, by rfl⟩ : syracuseStep 2155071 = 3232607) B3232607
theorem B3232613 : Blo 2153435 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B2155075 : Blo 2153435 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B4091285 : Blo 2153435 4091285 := bbase (se 6 (by rfl) ⟨95889, by rfl⟩ : syracuseStep 4091285 = 191779) (by norm_num)
theorem B2727523 : Blo 2153435 2727523 := bstep (se 1 (by rfl) ⟨2045642, by rfl⟩ : syracuseStep 2727523 = 4091285) B4091285
theorem B3636697 : Blo 2153435 3636697 := bstep (se 2 (by rfl) ⟨1363761, by rfl⟩ : syracuseStep 3636697 = 2727523) B2727523
theorem B4848929 : Blo 2153435 4848929 := bstep (se 2 (by rfl) ⟨1818348, by rfl⟩ : syracuseStep 4848929 = 3636697) B3636697
theorem B3232619 : Blo 2153435 3232619 := bstep (se 1 (by rfl) ⟨2424464, by rfl⟩ : syracuseStep 3232619 = 4848929) B4848929
theorem B2155079 : Blo 2153435 2155079 := bstep (se 1 (by rfl) ⟨1616309, by rfl⟩ : syracuseStep 2155079 = 3232619) B3232619
theorem B2424469 : Blo 2153435 2424469 := bbase (se 6 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 2424469 = 113647) (by norm_num)
theorem B3232625 : Blo 2153435 3232625 := bstep (se 2 (by rfl) ⟨1212234, by rfl⟩ : syracuseStep 3232625 = 2424469) B2424469
theorem B2155083 : Blo 2153435 2155083 := bstep (se 1 (by rfl) ⟨1616312, by rfl⟩ : syracuseStep 2155083 = 3232625) B3232625
theorem B2727533 : Blo 2153435 2727533 := bbase (se 3 (by rfl) ⟨511412, by rfl⟩ : syracuseStep 2727533 = 1022825) (by norm_num)
theorem B7273421 : Blo 2153435 7273421 := bstep (se 3 (by rfl) ⟨1363766, by rfl⟩ : syracuseStep 7273421 = 2727533) B2727533
theorem B4848947 : Blo 2153435 4848947 := bstep (se 1 (by rfl) ⟨3636710, by rfl⟩ : syracuseStep 4848947 = 7273421) B7273421
theorem B3232631 : Blo 2153435 3232631 := bstep (se 1 (by rfl) ⟨2424473, by rfl⟩ : syracuseStep 3232631 = 4848947) B4848947
theorem B2155087 : Blo 2153435 2155087 := bstep (se 1 (by rfl) ⟨1616315, by rfl⟩ : syracuseStep 2155087 = 3232631) B3232631
theorem B3232637 : Blo 2153435 3232637 := bbase (se 3 (by rfl) ⟨606119, by rfl⟩ : syracuseStep 3232637 = 1212239) (by norm_num)
theorem B2155091 : Blo 2153435 2155091 := bstep (se 1 (by rfl) ⟨1616318, by rfl⟩ : syracuseStep 2155091 = 3232637) B3232637
theorem B4848965 : Blo 2153435 4848965 := bbase (se 4 (by rfl) ⟨454590, by rfl⟩ : syracuseStep 4848965 = 909181) (by norm_num)
theorem B3232643 : Blo 2153435 3232643 := bstep (se 1 (by rfl) ⟨2424482, by rfl⟩ : syracuseStep 3232643 = 4848965) B4848965
theorem B2155095 : Blo 2153435 2155095 := bstep (se 1 (by rfl) ⟨1616321, by rfl⟩ : syracuseStep 2155095 = 3232643) B3232643
theorem B2589041 : Blo 2153435 2589041 := bbase (se 2 (by rfl) ⟨970890, by rfl⟩ : syracuseStep 2589041 = 1941781) (by norm_num)
theorem B6904109 : Blo 2153435 6904109 := bstep (se 3 (by rfl) ⟨1294520, by rfl⟩ : syracuseStep 6904109 = 2589041) B2589041
theorem B4602739 : Blo 2153435 4602739 := bstep (se 1 (by rfl) ⟨3452054, by rfl⟩ : syracuseStep 4602739 = 6904109) B6904109
theorem B6136985 : Blo 2153435 6136985 := bstep (se 2 (by rfl) ⟨2301369, by rfl⟩ : syracuseStep 6136985 = 4602739) B4602739
theorem B4091323 : Blo 2153435 4091323 := bstep (se 1 (by rfl) ⟨3068492, by rfl⟩ : syracuseStep 4091323 = 6136985) B6136985
theorem B5455097 : Blo 2153435 5455097 := bstep (se 2 (by rfl) ⟨2045661, by rfl⟩ : syracuseStep 5455097 = 4091323) B4091323
theorem B3636731 : Blo 2153435 3636731 := bstep (se 1 (by rfl) ⟨2727548, by rfl⟩ : syracuseStep 3636731 = 5455097) B5455097
theorem B2424487 : Blo 2153435 2424487 := bstep (se 1 (by rfl) ⟨1818365, by rfl⟩ : syracuseStep 2424487 = 3636731) B3636731
theorem B3232649 : Blo 2153435 3232649 := bstep (se 2 (by rfl) ⟨1212243, by rfl⟩ : syracuseStep 3232649 = 2424487) B2424487
theorem B2155099 : Blo 2153435 2155099 := bstep (se 1 (by rfl) ⟨1616324, by rfl⟩ : syracuseStep 2155099 = 3232649) B3232649
theorem B10910213 : Blo 2153435 10910213 := bbase (se 4 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 10910213 = 2045665) (by norm_num)
theorem B7273475 : Blo 2153435 7273475 := bstep (se 1 (by rfl) ⟨5455106, by rfl⟩ : syracuseStep 7273475 = 10910213) B10910213
theorem B4848983 : Blo 2153435 4848983 := bstep (se 1 (by rfl) ⟨3636737, by rfl⟩ : syracuseStep 4848983 = 7273475) B7273475
theorem B3232655 : Blo 2153435 3232655 := bstep (se 1 (by rfl) ⟨2424491, by rfl⟩ : syracuseStep 3232655 = 4848983) B4848983
theorem B2155103 : Blo 2153435 2155103 := bstep (se 1 (by rfl) ⟨1616327, by rfl⟩ : syracuseStep 2155103 = 3232655) B3232655
theorem B3232661 : Blo 2153435 3232661 := bbase (se 6 (by rfl) ⟨75765, by rfl⟩ : syracuseStep 3232661 = 151531) (by norm_num)
theorem B2155107 : Blo 2153435 2155107 := bstep (se 1 (by rfl) ⟨1616330, by rfl⟩ : syracuseStep 2155107 = 3232661) B3232661
theorem B12274037 : Blo 2153435 12274037 := bbase (se 5 (by rfl) ⟨575345, by rfl⟩ : syracuseStep 12274037 = 1150691) (by norm_num)
theorem B8182691 : Blo 2153435 8182691 := bstep (se 1 (by rfl) ⟨6137018, by rfl⟩ : syracuseStep 8182691 = 12274037) B12274037
theorem B5455127 : Blo 2153435 5455127 := bstep (se 1 (by rfl) ⟨4091345, by rfl⟩ : syracuseStep 5455127 = 8182691) B8182691
theorem B3636751 : Blo 2153435 3636751 := bstep (se 1 (by rfl) ⟨2727563, by rfl⟩ : syracuseStep 3636751 = 5455127) B5455127
theorem B4849001 : Blo 2153435 4849001 := bstep (se 2 (by rfl) ⟨1818375, by rfl⟩ : syracuseStep 4849001 = 3636751) B3636751
theorem B3232667 : Blo 2153435 3232667 := bstep (se 1 (by rfl) ⟨2424500, by rfl⟩ : syracuseStep 3232667 = 4849001) B4849001
theorem B2155111 : Blo 2153435 2155111 := bstep (se 1 (by rfl) ⟨1616333, by rfl⟩ : syracuseStep 2155111 = 3232667) B3232667
theorem B2424505 : Blo 2153435 2424505 := bbase (se 2 (by rfl) ⟨909189, by rfl⟩ : syracuseStep 2424505 = 1818379) (by norm_num)
theorem B3232673 : Blo 2153435 3232673 := bstep (se 2 (by rfl) ⟨1212252, by rfl⟩ : syracuseStep 3232673 = 2424505) B2424505
theorem B2155115 : Blo 2153435 2155115 := bstep (se 1 (by rfl) ⟨1616336, by rfl⟩ : syracuseStep 2155115 = 3232673) B3232673
theorem B4602781 : Blo 2153435 4602781 := bbase (se 3 (by rfl) ⟨863021, by rfl⟩ : syracuseStep 4602781 = 1726043) (by norm_num)
theorem B6137041 : Blo 2153435 6137041 := bstep (se 2 (by rfl) ⟨2301390, by rfl⟩ : syracuseStep 6137041 = 4602781) B4602781
theorem B8182721 : Blo 2153435 8182721 := bstep (se 2 (by rfl) ⟨3068520, by rfl⟩ : syracuseStep 8182721 = 6137041) B6137041
theorem B5455147 : Blo 2153435 5455147 := bstep (se 1 (by rfl) ⟨4091360, by rfl⟩ : syracuseStep 5455147 = 8182721) B8182721
theorem B7273529 : Blo 2153435 7273529 := bstep (se 2 (by rfl) ⟨2727573, by rfl⟩ : syracuseStep 7273529 = 5455147) B5455147
theorem B4849019 : Blo 2153435 4849019 := bstep (se 1 (by rfl) ⟨3636764, by rfl⟩ : syracuseStep 4849019 = 7273529) B7273529
theorem B3232679 : Blo 2153435 3232679 := bstep (se 1 (by rfl) ⟨2424509, by rfl⟩ : syracuseStep 3232679 = 4849019) B4849019
theorem B2155119 : Blo 2153435 2155119 := bstep (se 1 (by rfl) ⟨1616339, by rfl⟩ : syracuseStep 2155119 = 3232679) B3232679
theorem B3232685 : Blo 2153435 3232685 := bbase (se 3 (by rfl) ⟨606128, by rfl⟩ : syracuseStep 3232685 = 1212257) (by norm_num)
theorem B2155123 : Blo 2153435 2155123 := bstep (se 1 (by rfl) ⟨1616342, by rfl⟩ : syracuseStep 2155123 = 3232685) B3232685
theorem B4849037 : Blo 2153435 4849037 := bbase (se 3 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 4849037 = 1818389) (by norm_num)
theorem B3232691 : Blo 2153435 3232691 := bstep (se 1 (by rfl) ⟨2424518, by rfl⟩ : syracuseStep 3232691 = 4849037) B4849037
theorem B2155127 : Blo 2153435 2155127 := bstep (se 1 (by rfl) ⟨1616345, by rfl⟩ : syracuseStep 2155127 = 3232691) B3232691
theorem B2727589 : Blo 2153435 2727589 := bbase (se 4 (by rfl) ⟨255711, by rfl⟩ : syracuseStep 2727589 = 511423) (by norm_num)
theorem B3636785 : Blo 2153435 3636785 := bstep (se 2 (by rfl) ⟨1363794, by rfl⟩ : syracuseStep 3636785 = 2727589) B2727589
theorem B2424523 : Blo 2153435 2424523 := bstep (se 1 (by rfl) ⟨1818392, by rfl⟩ : syracuseStep 2424523 = 3636785) B3636785
theorem B3232697 : Blo 2153435 3232697 := bstep (se 2 (by rfl) ⟨1212261, by rfl⟩ : syracuseStep 3232697 = 2424523) B2424523
theorem B2155131 : Blo 2153435 2155131 := bstep (se 1 (by rfl) ⟨1616348, by rfl⟩ : syracuseStep 2155131 = 3232697) B3232697
theorem B19660853 : Blo 2153435 19660853 := bbase (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) (by norm_num)
theorem B52428941 : Blo 2153435 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B34952627 : Blo 2153435 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B23301751 : Blo 2153435 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B31069001 : Blo 2153435 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B20712667 : Blo 2153435 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B27616889 : Blo 2153435 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B18411259 : Blo 2153435 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B24548345 : Blo 2153435 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B16365563 : Blo 2153435 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B10910375 : Blo 2153435 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B7273583 : Blo 2153435 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B4849055 : Blo 2153435 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B3232703 : Blo 2153435 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B2155135 : Blo 2153435 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B3232709 : Blo 2153435 3232709 := bbase (se 4 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 3232709 = 606133) (by norm_num)
theorem B2155139 : Blo 2153435 2155139 := bstep (se 1 (by rfl) ⟨1616354, by rfl⟩ : syracuseStep 2155139 = 3232709) B3232709
theorem B3636805 : Blo 2153435 3636805 := bbase (se 4 (by rfl) ⟨340950, by rfl⟩ : syracuseStep 3636805 = 681901) (by norm_num)
theorem B4849073 : Blo 2153435 4849073 := bstep (se 2 (by rfl) ⟨1818402, by rfl⟩ : syracuseStep 4849073 = 3636805) B3636805
theorem B3232715 : Blo 2153435 3232715 := bstep (se 1 (by rfl) ⟨2424536, by rfl⟩ : syracuseStep 3232715 = 4849073) B4849073
theorem B2155143 : Blo 2153435 2155143 := bstep (se 1 (by rfl) ⟨1616357, by rfl⟩ : syracuseStep 2155143 = 3232715) B3232715
theorem B2424541 : Blo 2153435 2424541 := bbase (se 3 (by rfl) ⟨454601, by rfl⟩ : syracuseStep 2424541 = 909203) (by norm_num)
theorem B3232721 : Blo 2153435 3232721 := bstep (se 2 (by rfl) ⟨1212270, by rfl⟩ : syracuseStep 3232721 = 2424541) B2424541
theorem B2155147 : Blo 2153435 2155147 := bstep (se 1 (by rfl) ⟨1616360, by rfl⟩ : syracuseStep 2155147 = 3232721) B3232721
theorem B7273637 : Blo 2153435 7273637 := bbase (se 4 (by rfl) ⟨681903, by rfl⟩ : syracuseStep 7273637 = 1363807) (by norm_num)
theorem B4849091 : Blo 2153435 4849091 := bstep (se 1 (by rfl) ⟨3636818, by rfl⟩ : syracuseStep 4849091 = 7273637) B7273637
theorem B3232727 : Blo 2153435 3232727 := bstep (se 1 (by rfl) ⟨2424545, by rfl⟩ : syracuseStep 3232727 = 4849091) B4849091
theorem B2155151 : Blo 2153435 2155151 := bstep (se 1 (by rfl) ⟨1616363, by rfl⟩ : syracuseStep 2155151 = 3232727) B3232727
theorem B3232733 : Blo 2153435 3232733 := bbase (se 3 (by rfl) ⟨606137, by rfl⟩ : syracuseStep 3232733 = 1212275) (by norm_num)
theorem B2155155 : Blo 2153435 2155155 := bstep (se 1 (by rfl) ⟨1616366, by rfl⟩ : syracuseStep 2155155 = 3232733) B3232733
theorem B4849109 : Blo 2153435 4849109 := bbase (se 7 (by rfl) ⟨56825, by rfl⟩ : syracuseStep 4849109 = 113651) (by norm_num)
theorem B3232739 : Blo 2153435 3232739 := bstep (se 1 (by rfl) ⟨2424554, by rfl⟩ : syracuseStep 3232739 = 4849109) B4849109
theorem B2155159 : Blo 2153435 2155159 := bstep (se 1 (by rfl) ⟨1616369, by rfl⟩ : syracuseStep 2155159 = 3232739) B3232739
theorem B6220901 : Blo 2153435 6220901 := bbase (se 4 (by rfl) ⟨583209, by rfl⟩ : syracuseStep 6220901 = 1166419) (by norm_num)
theorem B16589069 : Blo 2153435 16589069 := bstep (se 3 (by rfl) ⟨3110450, by rfl⟩ : syracuseStep 16589069 = 6220901) B6220901
theorem B11059379 : Blo 2153435 11059379 := bstep (se 1 (by rfl) ⟨8294534, by rfl⟩ : syracuseStep 11059379 = 16589069) B16589069
theorem B7372919 : Blo 2153435 7372919 := bstep (se 1 (by rfl) ⟨5529689, by rfl⟩ : syracuseStep 7372919 = 11059379) B11059379
theorem B4915279 : Blo 2153435 4915279 := bstep (se 1 (by rfl) ⟨3686459, by rfl⟩ : syracuseStep 4915279 = 7372919) B7372919
theorem B6553705 : Blo 2153435 6553705 := bstep (se 2 (by rfl) ⟨2457639, by rfl⟩ : syracuseStep 6553705 = 4915279) B4915279
theorem B8738273 : Blo 2153435 8738273 := bstep (se 2 (by rfl) ⟨3276852, by rfl⟩ : syracuseStep 8738273 = 6553705) B6553705
theorem B5825515 : Blo 2153435 5825515 := bstep (se 1 (by rfl) ⟨4369136, by rfl⟩ : syracuseStep 5825515 = 8738273) B8738273
theorem B7767353 : Blo 2153435 7767353 := bstep (se 2 (by rfl) ⟨2912757, by rfl⟩ : syracuseStep 7767353 = 5825515) B5825515
theorem B20712941 : Blo 2153435 20712941 := bstep (se 3 (by rfl) ⟨3883676, by rfl⟩ : syracuseStep 20712941 = 7767353) B7767353
theorem B13808627 : Blo 2153435 13808627 := bstep (se 1 (by rfl) ⟨10356470, by rfl⟩ : syracuseStep 13808627 = 20712941) B20712941
theorem B9205751 : Blo 2153435 9205751 := bstep (se 1 (by rfl) ⟨6904313, by rfl⟩ : syracuseStep 9205751 = 13808627) B13808627
theorem B6137167 : Blo 2153435 6137167 := bstep (se 1 (by rfl) ⟨4602875, by rfl⟩ : syracuseStep 6137167 = 9205751) B9205751
theorem B8182889 : Blo 2153435 8182889 := bstep (se 2 (by rfl) ⟨3068583, by rfl⟩ : syracuseStep 8182889 = 6137167) B6137167
theorem B5455259 : Blo 2153435 5455259 := bstep (se 1 (by rfl) ⟨4091444, by rfl⟩ : syracuseStep 5455259 = 8182889) B8182889
theorem B3636839 : Blo 2153435 3636839 := bstep (se 1 (by rfl) ⟨2727629, by rfl⟩ : syracuseStep 3636839 = 5455259) B5455259
theorem B2424559 : Blo 2153435 2424559 := bstep (se 1 (by rfl) ⟨1818419, by rfl⟩ : syracuseStep 2424559 = 3636839) B3636839
theorem B3232745 : Blo 2153435 3232745 := bstep (se 2 (by rfl) ⟨1212279, by rfl⟩ : syracuseStep 3232745 = 2424559) B2424559
theorem B2155163 : Blo 2153435 2155163 := bstep (se 1 (by rfl) ⟨1616372, by rfl⟩ : syracuseStep 2155163 = 3232745) B3232745
theorem B6904325 : Blo 2153435 6904325 := bbase (se 4 (by rfl) ⟨647280, by rfl⟩ : syracuseStep 6904325 = 1294561) (by norm_num)
theorem B18411533 : Blo 2153435 18411533 := bstep (se 3 (by rfl) ⟨3452162, by rfl⟩ : syracuseStep 18411533 = 6904325) B6904325
theorem B12274355 : Blo 2153435 12274355 := bstep (se 1 (by rfl) ⟨9205766, by rfl⟩ : syracuseStep 12274355 = 18411533) B18411533
theorem B8182903 : Blo 2153435 8182903 := bstep (se 1 (by rfl) ⟨6137177, by rfl⟩ : syracuseStep 8182903 = 12274355) B12274355
theorem B10910537 : Blo 2153435 10910537 := bstep (se 2 (by rfl) ⟨4091451, by rfl⟩ : syracuseStep 10910537 = 8182903) B8182903
theorem B7273691 : Blo 2153435 7273691 := bstep (se 1 (by rfl) ⟨5455268, by rfl⟩ : syracuseStep 7273691 = 10910537) B10910537
theorem B4849127 : Blo 2153435 4849127 := bstep (se 1 (by rfl) ⟨3636845, by rfl⟩ : syracuseStep 4849127 = 7273691) B7273691
theorem B3232751 : Blo 2153435 3232751 := bstep (se 1 (by rfl) ⟨2424563, by rfl⟩ : syracuseStep 3232751 = 4849127) B4849127
theorem B2155167 : Blo 2153435 2155167 := bstep (se 1 (by rfl) ⟨1616375, by rfl⟩ : syracuseStep 2155167 = 3232751) B3232751
theorem B3232757 : Blo 2153435 3232757 := bbase (se 5 (by rfl) ⟨151535, by rfl⟩ : syracuseStep 3232757 = 303071) (by norm_num)
theorem B2155171 : Blo 2153435 2155171 := bstep (se 1 (by rfl) ⟨1616378, by rfl⟩ : syracuseStep 2155171 = 3232757) B3232757
theorem B4602901 : Blo 2153435 4602901 := bbase (se 6 (by rfl) ⟨107880, by rfl⟩ : syracuseStep 4602901 = 215761) (by norm_num)
theorem B6137201 : Blo 2153435 6137201 := bstep (se 2 (by rfl) ⟨2301450, by rfl⟩ : syracuseStep 6137201 = 4602901) B4602901
theorem B4091467 : Blo 2153435 4091467 := bstep (se 1 (by rfl) ⟨3068600, by rfl⟩ : syracuseStep 4091467 = 6137201) B6137201
theorem B5455289 : Blo 2153435 5455289 := bstep (se 2 (by rfl) ⟨2045733, by rfl⟩ : syracuseStep 5455289 = 4091467) B4091467
theorem B3636859 : Blo 2153435 3636859 := bstep (se 1 (by rfl) ⟨2727644, by rfl⟩ : syracuseStep 3636859 = 5455289) B5455289
theorem B4849145 : Blo 2153435 4849145 := bstep (se 2 (by rfl) ⟨1818429, by rfl⟩ : syracuseStep 4849145 = 3636859) B3636859
theorem B3232763 : Blo 2153435 3232763 := bstep (se 1 (by rfl) ⟨2424572, by rfl⟩ : syracuseStep 3232763 = 4849145) B4849145
theorem B2155175 : Blo 2153435 2155175 := bstep (se 1 (by rfl) ⟨1616381, by rfl⟩ : syracuseStep 2155175 = 3232763) B3232763
theorem B2424577 : Blo 2153435 2424577 := bbase (se 2 (by rfl) ⟨909216, by rfl⟩ : syracuseStep 2424577 = 1818433) (by norm_num)
theorem B3232769 : Blo 2153435 3232769 := bstep (se 2 (by rfl) ⟨1212288, by rfl⟩ : syracuseStep 3232769 = 2424577) B2424577
theorem B2155179 : Blo 2153435 2155179 := bstep (se 1 (by rfl) ⟨1616384, by rfl⟩ : syracuseStep 2155179 = 3232769) B3232769
theorem B5455309 : Blo 2153435 5455309 := bbase (se 3 (by rfl) ⟨1022870, by rfl⟩ : syracuseStep 5455309 = 2045741) (by norm_num)
theorem B7273745 : Blo 2153435 7273745 := bstep (se 2 (by rfl) ⟨2727654, by rfl⟩ : syracuseStep 7273745 = 5455309) B5455309
theorem B4849163 : Blo 2153435 4849163 := bstep (se 1 (by rfl) ⟨3636872, by rfl⟩ : syracuseStep 4849163 = 7273745) B7273745
theorem B3232775 : Blo 2153435 3232775 := bstep (se 1 (by rfl) ⟨2424581, by rfl⟩ : syracuseStep 3232775 = 4849163) B4849163
theorem B2155183 : Blo 2153435 2155183 := bstep (se 1 (by rfl) ⟨1616387, by rfl⟩ : syracuseStep 2155183 = 3232775) B3232775
theorem B3232781 : Blo 2153435 3232781 := bbase (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) (by norm_num)
theorem B2155187 : Blo 2153435 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B4849181 : Blo 2153435 4849181 := bbase (se 3 (by rfl) ⟨909221, by rfl⟩ : syracuseStep 4849181 = 1818443) (by norm_num)
theorem B3232787 : Blo 2153435 3232787 := bstep (se 1 (by rfl) ⟨2424590, by rfl⟩ : syracuseStep 3232787 = 4849181) B4849181
theorem B2155191 : Blo 2153435 2155191 := bstep (se 1 (by rfl) ⟨1616393, by rfl⟩ : syracuseStep 2155191 = 3232787) B3232787
theorem B3636893 : Blo 2153435 3636893 := bbase (se 3 (by rfl) ⟨681917, by rfl⟩ : syracuseStep 3636893 = 1363835) (by norm_num)
theorem B2424595 : Blo 2153435 2424595 := bstep (se 1 (by rfl) ⟨1818446, by rfl⟩ : syracuseStep 2424595 = 3636893) B3636893
theorem B3232793 : Blo 2153435 3232793 := bstep (se 2 (by rfl) ⟨1212297, by rfl⟩ : syracuseStep 3232793 = 2424595) B2424595
theorem B2155195 : Blo 2153435 2155195 := bstep (se 1 (by rfl) ⟨1616396, by rfl⟩ : syracuseStep 2155195 = 3232793) B3232793
theorem B6553813 : Blo 2153435 6553813 := bbase (se 7 (by rfl) ⟨76802, by rfl⟩ : syracuseStep 6553813 = 153605) (by norm_num)
theorem B8738417 : Blo 2153435 8738417 := bstep (se 2 (by rfl) ⟨3276906, by rfl⟩ : syracuseStep 8738417 = 6553813) B6553813
theorem B5825611 : Blo 2153435 5825611 := bstep (se 1 (by rfl) ⟨4369208, by rfl⟩ : syracuseStep 5825611 = 8738417) B8738417
theorem B31069925 : Blo 2153435 31069925 := bstep (se 4 (by rfl) ⟨2912805, by rfl⟩ : syracuseStep 31069925 = 5825611) B5825611
theorem B20713283 : Blo 2153435 20713283 := bstep (se 1 (by rfl) ⟨15534962, by rfl⟩ : syracuseStep 20713283 = 31069925) B31069925
theorem B13808855 : Blo 2153435 13808855 := bstep (se 1 (by rfl) ⟨10356641, by rfl⟩ : syracuseStep 13808855 = 20713283) B20713283
theorem B9205903 : Blo 2153435 9205903 := bstep (se 1 (by rfl) ⟨6904427, by rfl⟩ : syracuseStep 9205903 = 13808855) B13808855
theorem B12274537 : Blo 2153435 12274537 := bstep (se 2 (by rfl) ⟨4602951, by rfl⟩ : syracuseStep 12274537 = 9205903) B9205903
theorem B16366049 : Blo 2153435 16366049 := bstep (se 2 (by rfl) ⟨6137268, by rfl⟩ : syracuseStep 16366049 = 12274537) B12274537
theorem B10910699 : Blo 2153435 10910699 := bstep (se 1 (by rfl) ⟨8183024, by rfl⟩ : syracuseStep 10910699 = 16366049) B16366049
theorem B7273799 : Blo 2153435 7273799 := bstep (se 1 (by rfl) ⟨5455349, by rfl⟩ : syracuseStep 7273799 = 10910699) B10910699
theorem B4849199 : Blo 2153435 4849199 := bstep (se 1 (by rfl) ⟨3636899, by rfl⟩ : syracuseStep 4849199 = 7273799) B7273799
theorem B3232799 : Blo 2153435 3232799 := bstep (se 1 (by rfl) ⟨2424599, by rfl⟩ : syracuseStep 3232799 = 4849199) B4849199
theorem B2155199 : Blo 2153435 2155199 := bstep (se 1 (by rfl) ⟨1616399, by rfl⟩ : syracuseStep 2155199 = 3232799) B3232799
theorem B3232805 : Blo 2153435 3232805 := bbase (se 4 (by rfl) ⟨303075, by rfl⟩ : syracuseStep 3232805 = 606151) (by norm_num)
theorem B2155203 : Blo 2153435 2155203 := bstep (se 1 (by rfl) ⟨1616402, by rfl⟩ : syracuseStep 2155203 = 3232805) B3232805
theorem B2727685 : Blo 2153435 2727685 := bbase (se 4 (by rfl) ⟨255720, by rfl⟩ : syracuseStep 2727685 = 511441) (by norm_num)
theorem B3636913 : Blo 2153435 3636913 := bstep (se 2 (by rfl) ⟨1363842, by rfl⟩ : syracuseStep 3636913 = 2727685) B2727685
theorem B4849217 : Blo 2153435 4849217 := bstep (se 2 (by rfl) ⟨1818456, by rfl⟩ : syracuseStep 4849217 = 3636913) B3636913
theorem B3232811 : Blo 2153435 3232811 := bstep (se 1 (by rfl) ⟨2424608, by rfl⟩ : syracuseStep 3232811 = 4849217) B4849217
theorem B2155207 : Blo 2153435 2155207 := bstep (se 1 (by rfl) ⟨1616405, by rfl⟩ : syracuseStep 2155207 = 3232811) B3232811
theorem B2424613 : Blo 2153435 2424613 := bbase (se 4 (by rfl) ⟨227307, by rfl⟩ : syracuseStep 2424613 = 454615) (by norm_num)
theorem B3232817 : Blo 2153435 3232817 := bstep (se 2 (by rfl) ⟨1212306, by rfl⟩ : syracuseStep 3232817 = 2424613) B2424613
theorem B2155211 : Blo 2153435 2155211 := bstep (se 1 (by rfl) ⟨1616408, by rfl⟩ : syracuseStep 2155211 = 3232817) B3232817
theorem B9205973 : Blo 2153435 9205973 := bbase (se 7 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 9205973 = 215765) (by norm_num)
theorem B6137315 : Blo 2153435 6137315 := bstep (se 1 (by rfl) ⟨4602986, by rfl⟩ : syracuseStep 6137315 = 9205973) B9205973
theorem B4091543 : Blo 2153435 4091543 := bstep (se 1 (by rfl) ⟨3068657, by rfl⟩ : syracuseStep 4091543 = 6137315) B6137315
theorem B2727695 : Blo 2153435 2727695 := bstep (se 1 (by rfl) ⟨2045771, by rfl⟩ : syracuseStep 2727695 = 4091543) B4091543
theorem B7273853 : Blo 2153435 7273853 := bstep (se 3 (by rfl) ⟨1363847, by rfl⟩ : syracuseStep 7273853 = 2727695) B2727695
theorem B4849235 : Blo 2153435 4849235 := bstep (se 1 (by rfl) ⟨3636926, by rfl⟩ : syracuseStep 4849235 = 7273853) B7273853
theorem B3232823 : Blo 2153435 3232823 := bstep (se 1 (by rfl) ⟨2424617, by rfl⟩ : syracuseStep 3232823 = 4849235) B4849235
theorem B2155215 : Blo 2153435 2155215 := bstep (se 1 (by rfl) ⟨1616411, by rfl⟩ : syracuseStep 2155215 = 3232823) B3232823
theorem B3232829 : Blo 2153435 3232829 := bbase (se 3 (by rfl) ⟨606155, by rfl⟩ : syracuseStep 3232829 = 1212311) (by norm_num)
theorem B2155219 : Blo 2153435 2155219 := bstep (se 1 (by rfl) ⟨1616414, by rfl⟩ : syracuseStep 2155219 = 3232829) B3232829
theorem B4849253 : Blo 2153435 4849253 := bbase (se 4 (by rfl) ⟨454617, by rfl⟩ : syracuseStep 4849253 = 909235) (by norm_num)
theorem B3232835 : Blo 2153435 3232835 := bstep (se 1 (by rfl) ⟨2424626, by rfl⟩ : syracuseStep 3232835 = 4849253) B4849253
theorem B2155223 : Blo 2153435 2155223 := bstep (se 1 (by rfl) ⟨1616417, by rfl⟩ : syracuseStep 2155223 = 3232835) B3232835
theorem B5455421 : Blo 2153435 5455421 := bbase (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) (by norm_num)
theorem B3636947 : Blo 2153435 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B2424631 : Blo 2153435 2424631 := bstep (se 1 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 2424631 = 3636947) B3636947
theorem B3232841 : Blo 2153435 3232841 := bstep (se 2 (by rfl) ⟨1212315, by rfl⟩ : syracuseStep 3232841 = 2424631) B2424631
theorem B2155227 : Blo 2153435 2155227 := bstep (se 1 (by rfl) ⟨1616420, by rfl⟩ : syracuseStep 2155227 = 3232841) B3232841
theorem B4091573 : Blo 2153435 4091573 := bbase (se 5 (by rfl) ⟨191792, by rfl⟩ : syracuseStep 4091573 = 383585) (by norm_num)
theorem B10910861 : Blo 2153435 10910861 := bstep (se 3 (by rfl) ⟨2045786, by rfl⟩ : syracuseStep 10910861 = 4091573) B4091573
theorem B7273907 : Blo 2153435 7273907 := bstep (se 1 (by rfl) ⟨5455430, by rfl⟩ : syracuseStep 7273907 = 10910861) B10910861
theorem B4849271 : Blo 2153435 4849271 := bstep (se 1 (by rfl) ⟨3636953, by rfl⟩ : syracuseStep 4849271 = 7273907) B7273907
theorem B3232847 : Blo 2153435 3232847 := bstep (se 1 (by rfl) ⟨2424635, by rfl⟩ : syracuseStep 3232847 = 4849271) B4849271
theorem B2155231 : Blo 2153435 2155231 := bstep (se 1 (by rfl) ⟨1616423, by rfl⟩ : syracuseStep 2155231 = 3232847) B3232847
theorem B3232853 : Blo 2153435 3232853 := bbase (se 8 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 3232853 = 37885) (by norm_num)
theorem B2155235 : Blo 2153435 2155235 := bstep (se 1 (by rfl) ⟨1616426, by rfl⟩ : syracuseStep 2155235 = 3232853) B3232853
theorem B15535253 : Blo 2153435 15535253 := bbase (se 6 (by rfl) ⟨364107, by rfl⟩ : syracuseStep 15535253 = 728215) (by norm_num)
theorem B10356835 : Blo 2153435 10356835 := bstep (se 1 (by rfl) ⟨7767626, by rfl⟩ : syracuseStep 10356835 = 15535253) B15535253
theorem B13809113 : Blo 2153435 13809113 := bstep (se 2 (by rfl) ⟨5178417, by rfl⟩ : syracuseStep 13809113 = 10356835) B10356835
theorem B9206075 : Blo 2153435 9206075 := bstep (se 1 (by rfl) ⟨6904556, by rfl⟩ : syracuseStep 9206075 = 13809113) B13809113
theorem B6137383 : Blo 2153435 6137383 := bstep (se 1 (by rfl) ⟨4603037, by rfl⟩ : syracuseStep 6137383 = 9206075) B9206075
theorem B8183177 : Blo 2153435 8183177 := bstep (se 2 (by rfl) ⟨3068691, by rfl⟩ : syracuseStep 8183177 = 6137383) B6137383
theorem B5455451 : Blo 2153435 5455451 := bstep (se 1 (by rfl) ⟨4091588, by rfl⟩ : syracuseStep 5455451 = 8183177) B8183177
theorem B3636967 : Blo 2153435 3636967 := bstep (se 1 (by rfl) ⟨2727725, by rfl⟩ : syracuseStep 3636967 = 5455451) B5455451
theorem B4849289 : Blo 2153435 4849289 := bstep (se 2 (by rfl) ⟨1818483, by rfl⟩ : syracuseStep 4849289 = 3636967) B3636967
theorem B3232859 : Blo 2153435 3232859 := bstep (se 1 (by rfl) ⟨2424644, by rfl⟩ : syracuseStep 3232859 = 4849289) B4849289
theorem B2155239 : Blo 2153435 2155239 := bstep (se 1 (by rfl) ⟨1616429, by rfl⟩ : syracuseStep 2155239 = 3232859) B3232859
theorem B2424649 : Blo 2153435 2424649 := bbase (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) (by norm_num)
theorem B3232865 : Blo 2153435 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B2155243 : Blo 2153435 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B2184653 : Blo 2153435 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B5825741 : Blo 2153435 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B15535309 : Blo 2153435 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B20713745 : Blo 2153435 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B13809163 : Blo 2153435 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B18412217 : Blo 2153435 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B12274811 : Blo 2153435 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B8183207 : Blo 2153435 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B5455471 : Blo 2153435 5455471 := bstep (se 1 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 5455471 = 8183207) B8183207
theorem B7273961 : Blo 2153435 7273961 := bstep (se 2 (by rfl) ⟨2727735, by rfl⟩ : syracuseStep 7273961 = 5455471) B5455471
theorem B4849307 : Blo 2153435 4849307 := bstep (se 1 (by rfl) ⟨3636980, by rfl⟩ : syracuseStep 4849307 = 7273961) B7273961
theorem B3232871 : Blo 2153435 3232871 := bstep (se 1 (by rfl) ⟨2424653, by rfl⟩ : syracuseStep 3232871 = 4849307) B4849307
theorem B2155247 : Blo 2153435 2155247 := bstep (se 1 (by rfl) ⟨1616435, by rfl⟩ : syracuseStep 2155247 = 3232871) B3232871
theorem B3232877 : Blo 2153435 3232877 := bbase (se 3 (by rfl) ⟨606164, by rfl⟩ : syracuseStep 3232877 = 1212329) (by norm_num)
theorem B2155251 : Blo 2153435 2155251 := bstep (se 1 (by rfl) ⟨1616438, by rfl⟩ : syracuseStep 2155251 = 3232877) B3232877
theorem B4849325 : Blo 2153435 4849325 := bbase (se 3 (by rfl) ⟨909248, by rfl⟩ : syracuseStep 4849325 = 1818497) (by norm_num)
theorem B3232883 : Blo 2153435 3232883 := bstep (se 1 (by rfl) ⟨2424662, by rfl⟩ : syracuseStep 3232883 = 4849325) B4849325
theorem B2155255 : Blo 2153435 2155255 := bstep (se 1 (by rfl) ⟨1616441, by rfl⟩ : syracuseStep 2155255 = 3232883) B3232883
theorem B7767701 : Blo 2153435 7767701 := bbase (se 6 (by rfl) ⟨182055, by rfl⟩ : syracuseStep 7767701 = 364111) (by norm_num)
theorem B5178467 : Blo 2153435 5178467 := bstep (se 1 (by rfl) ⟨3883850, by rfl⟩ : syracuseStep 5178467 = 7767701) B7767701
theorem B3452311 : Blo 2153435 3452311 := bstep (se 1 (by rfl) ⟨2589233, by rfl⟩ : syracuseStep 3452311 = 5178467) B5178467
theorem B4603081 : Blo 2153435 4603081 := bstep (se 2 (by rfl) ⟨1726155, by rfl⟩ : syracuseStep 4603081 = 3452311) B3452311
theorem B6137441 : Blo 2153435 6137441 := bstep (se 2 (by rfl) ⟨2301540, by rfl⟩ : syracuseStep 6137441 = 4603081) B4603081
theorem B4091627 : Blo 2153435 4091627 := bstep (se 1 (by rfl) ⟨3068720, by rfl⟩ : syracuseStep 4091627 = 6137441) B6137441
theorem B2727751 : Blo 2153435 2727751 := bstep (se 1 (by rfl) ⟨2045813, by rfl⟩ : syracuseStep 2727751 = 4091627) B4091627
theorem B3637001 : Blo 2153435 3637001 := bstep (se 2 (by rfl) ⟨1363875, by rfl⟩ : syracuseStep 3637001 = 2727751) B2727751
theorem B2424667 : Blo 2153435 2424667 := bstep (se 1 (by rfl) ⟨1818500, by rfl⟩ : syracuseStep 2424667 = 3637001) B3637001
theorem B3232889 : Blo 2153435 3232889 := bstep (se 2 (by rfl) ⟨1212333, by rfl⟩ : syracuseStep 3232889 = 2424667) B2424667
theorem B2155259 : Blo 2153435 2155259 := bstep (se 1 (by rfl) ⟨1616444, by rfl⟩ : syracuseStep 2155259 = 3232889) B3232889
theorem B2491285 : Blo 2153435 2491285 := bbase (se 6 (by rfl) ⟨58389, by rfl⟩ : syracuseStep 2491285 = 116779) (by norm_num)
theorem B3321713 : Blo 2153435 3321713 := bstep (se 2 (by rfl) ⟨1245642, by rfl⟩ : syracuseStep 3321713 = 2491285) B2491285
theorem B8857901 : Blo 2153435 8857901 := bstep (se 3 (by rfl) ⟨1660856, by rfl⟩ : syracuseStep 8857901 = 3321713) B3321713
theorem B5905267 : Blo 2153435 5905267 := bstep (se 1 (by rfl) ⟨4428950, by rfl⟩ : syracuseStep 5905267 = 8857901) B8857901
theorem B31494757 : Blo 2153435 31494757 := bstep (se 4 (by rfl) ⟨2952633, by rfl⟩ : syracuseStep 31494757 = 5905267) B5905267
theorem B41993009 : Blo 2153435 41993009 := bstep (se 2 (by rfl) ⟨15747378, by rfl⟩ : syracuseStep 41993009 = 31494757) B31494757
theorem B27995339 : Blo 2153435 27995339 := bstep (se 1 (by rfl) ⟨20996504, by rfl⟩ : syracuseStep 27995339 = 41993009) B41993009
theorem B74654237 : Blo 2153435 74654237 := bstep (se 3 (by rfl) ⟨13997669, by rfl⟩ : syracuseStep 74654237 = 27995339) B27995339
theorem B49769491 : Blo 2153435 49769491 := bstep (se 1 (by rfl) ⟨37327118, by rfl⟩ : syracuseStep 49769491 = 74654237) B74654237
theorem B66359321 : Blo 2153435 66359321 := bstep (se 2 (by rfl) ⟨24884745, by rfl⟩ : syracuseStep 66359321 = 49769491) B49769491
theorem B44239547 : Blo 2153435 44239547 := bstep (se 1 (by rfl) ⟨33179660, by rfl⟩ : syracuseStep 44239547 = 66359321) B66359321
theorem B117972125 : Blo 2153435 117972125 := bstep (se 3 (by rfl) ⟨22119773, by rfl⟩ : syracuseStep 117972125 = 44239547) B44239547
theorem B78648083 : Blo 2153435 78648083 := bstep (se 1 (by rfl) ⟨58986062, by rfl⟩ : syracuseStep 78648083 = 117972125) B117972125
theorem B52432055 : Blo 2153435 52432055 := bstep (se 1 (by rfl) ⟨39324041, by rfl⟩ : syracuseStep 52432055 = 78648083) B78648083
theorem B34954703 : Blo 2153435 34954703 := bstep (se 1 (by rfl) ⟨26216027, by rfl⟩ : syracuseStep 34954703 = 52432055) B52432055
theorem B23303135 : Blo 2153435 23303135 := bstep (se 1 (by rfl) ⟨17477351, by rfl⟩ : syracuseStep 23303135 = 34954703) B34954703
theorem B15535423 : Blo 2153435 15535423 := bstep (se 1 (by rfl) ⟨11651567, by rfl⟩ : syracuseStep 15535423 = 23303135) B23303135
theorem B20713897 : Blo 2153435 20713897 := bstep (se 2 (by rfl) ⟨7767711, by rfl⟩ : syracuseStep 20713897 = 15535423) B15535423
theorem B27618529 : Blo 2153435 27618529 := bstep (se 2 (by rfl) ⟨10356948, by rfl⟩ : syracuseStep 27618529 = 20713897) B20713897
theorem B36824705 : Blo 2153435 36824705 := bstep (se 2 (by rfl) ⟨13809264, by rfl⟩ : syracuseStep 36824705 = 27618529) B27618529
theorem B24549803 : Blo 2153435 24549803 := bstep (se 1 (by rfl) ⟨18412352, by rfl⟩ : syracuseStep 24549803 = 36824705) B36824705
theorem B16366535 : Blo 2153435 16366535 := bstep (se 1 (by rfl) ⟨12274901, by rfl⟩ : syracuseStep 16366535 = 24549803) B24549803
theorem B10911023 : Blo 2153435 10911023 := bstep (se 1 (by rfl) ⟨8183267, by rfl⟩ : syracuseStep 10911023 = 16366535) B16366535
theorem B7274015 : Blo 2153435 7274015 := bstep (se 1 (by rfl) ⟨5455511, by rfl⟩ : syracuseStep 7274015 = 10911023) B10911023
theorem B4849343 : Blo 2153435 4849343 := bstep (se 1 (by rfl) ⟨3637007, by rfl⟩ : syracuseStep 4849343 = 7274015) B7274015
theorem B3232895 : Blo 2153435 3232895 := bstep (se 1 (by rfl) ⟨2424671, by rfl⟩ : syracuseStep 3232895 = 4849343) B4849343
theorem B2155263 : Blo 2153435 2155263 := bstep (se 1 (by rfl) ⟨1616447, by rfl⟩ : syracuseStep 2155263 = 3232895) B3232895
theorem B3232901 : Blo 2153435 3232901 := bbase (se 4 (by rfl) ⟨303084, by rfl⟩ : syracuseStep 3232901 = 606169) (by norm_num)
theorem B2155267 : Blo 2153435 2155267 := bstep (se 1 (by rfl) ⟨1616450, by rfl⟩ : syracuseStep 2155267 = 3232901) B3232901
theorem B3637021 : Blo 2153435 3637021 := bbase (se 3 (by rfl) ⟨681941, by rfl⟩ : syracuseStep 3637021 = 1363883) (by norm_num)
theorem B4849361 : Blo 2153435 4849361 := bstep (se 2 (by rfl) ⟨1818510, by rfl⟩ : syracuseStep 4849361 = 3637021) B3637021
theorem B3232907 : Blo 2153435 3232907 := bstep (se 1 (by rfl) ⟨2424680, by rfl⟩ : syracuseStep 3232907 = 4849361) B4849361
theorem B2155271 : Blo 2153435 2155271 := bstep (se 1 (by rfl) ⟨1616453, by rfl⟩ : syracuseStep 2155271 = 3232907) B3232907
theorem B2424685 : Blo 2153435 2424685 := bbase (se 3 (by rfl) ⟨454628, by rfl⟩ : syracuseStep 2424685 = 909257) (by norm_num)
theorem B3232913 : Blo 2153435 3232913 := bstep (se 2 (by rfl) ⟨1212342, by rfl⟩ : syracuseStep 3232913 = 2424685) B2424685
theorem B2155275 : Blo 2153435 2155275 := bstep (se 1 (by rfl) ⟨1616456, by rfl⟩ : syracuseStep 2155275 = 3232913) B3232913
theorem B7274069 : Blo 2153435 7274069 := bbase (se 8 (by rfl) ⟨42621, by rfl⟩ : syracuseStep 7274069 = 85243) (by norm_num)
theorem B4849379 : Blo 2153435 4849379 := bstep (se 1 (by rfl) ⟨3637034, by rfl⟩ : syracuseStep 4849379 = 7274069) B7274069
theorem B3232919 : Blo 2153435 3232919 := bstep (se 1 (by rfl) ⟨2424689, by rfl⟩ : syracuseStep 3232919 = 4849379) B4849379
theorem B2155279 : Blo 2153435 2155279 := bstep (se 1 (by rfl) ⟨1616459, by rfl⟩ : syracuseStep 2155279 = 3232919) B3232919
theorem B3232925 : Blo 2153435 3232925 := bbase (se 3 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 3232925 = 1212347) (by norm_num)
theorem B2155283 : Blo 2153435 2155283 := bstep (se 1 (by rfl) ⟨1616462, by rfl⟩ : syracuseStep 2155283 = 3232925) B3232925
theorem B4849397 : Blo 2153435 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B3232931 : Blo 2153435 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B2155287 : Blo 2153435 2155287 := bstep (se 1 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 2155287 = 3232931) B3232931
theorem B5825861 : Blo 2153435 5825861 := bbase (se 4 (by rfl) ⟨546174, by rfl⟩ : syracuseStep 5825861 = 1092349) (by norm_num)
theorem B3883907 : Blo 2153435 3883907 := bstep (se 1 (by rfl) ⟨2912930, by rfl⟩ : syracuseStep 3883907 = 5825861) B5825861
theorem B10357085 : Blo 2153435 10357085 := bstep (se 3 (by rfl) ⟨1941953, by rfl⟩ : syracuseStep 10357085 = 3883907) B3883907
theorem B27618893 : Blo 2153435 27618893 := bstep (se 3 (by rfl) ⟨5178542, by rfl⟩ : syracuseStep 27618893 = 10357085) B10357085
theorem B18412595 : Blo 2153435 18412595 := bstep (se 1 (by rfl) ⟨13809446, by rfl⟩ : syracuseStep 18412595 = 27618893) B27618893
theorem B12275063 : Blo 2153435 12275063 := bstep (se 1 (by rfl) ⟨9206297, by rfl⟩ : syracuseStep 12275063 = 18412595) B18412595
theorem B8183375 : Blo 2153435 8183375 := bstep (se 1 (by rfl) ⟨6137531, by rfl⟩ : syracuseStep 8183375 = 12275063) B12275063
theorem B5455583 : Blo 2153435 5455583 := bstep (se 1 (by rfl) ⟨4091687, by rfl⟩ : syracuseStep 5455583 = 8183375) B8183375
theorem B3637055 : Blo 2153435 3637055 := bstep (se 1 (by rfl) ⟨2727791, by rfl⟩ : syracuseStep 3637055 = 5455583) B5455583
theorem B2424703 : Blo 2153435 2424703 := bstep (se 1 (by rfl) ⟨1818527, by rfl⟩ : syracuseStep 2424703 = 3637055) B3637055
theorem B3232937 : Blo 2153435 3232937 := bstep (se 2 (by rfl) ⟨1212351, by rfl⟩ : syracuseStep 3232937 = 2424703) B2424703
theorem B2155291 : Blo 2153435 2155291 := bstep (se 1 (by rfl) ⟨1616468, by rfl⟩ : syracuseStep 2155291 = 3232937) B3232937
theorem B4603157 : Blo 2153435 4603157 := bbase (se 6 (by rfl) ⟨107886, by rfl⟩ : syracuseStep 4603157 = 215773) (by norm_num)
theorem B3068771 : Blo 2153435 3068771 := bstep (se 1 (by rfl) ⟨2301578, by rfl⟩ : syracuseStep 3068771 = 4603157) B4603157
theorem B8183389 : Blo 2153435 8183389 := bstep (se 3 (by rfl) ⟨1534385, by rfl⟩ : syracuseStep 8183389 = 3068771) B3068771
theorem B10911185 : Blo 2153435 10911185 := bstep (se 2 (by rfl) ⟨4091694, by rfl⟩ : syracuseStep 10911185 = 8183389) B8183389
theorem B7274123 : Blo 2153435 7274123 := bstep (se 1 (by rfl) ⟨5455592, by rfl⟩ : syracuseStep 7274123 = 10911185) B10911185
theorem B4849415 : Blo 2153435 4849415 := bstep (se 1 (by rfl) ⟨3637061, by rfl⟩ : syracuseStep 4849415 = 7274123) B7274123
theorem B3232943 : Blo 2153435 3232943 := bstep (se 1 (by rfl) ⟨2424707, by rfl⟩ : syracuseStep 3232943 = 4849415) B4849415
theorem B2155295 : Blo 2153435 2155295 := bstep (se 1 (by rfl) ⟨1616471, by rfl⟩ : syracuseStep 2155295 = 3232943) B3232943
theorem B3232949 : Blo 2153435 3232949 := bbase (se 5 (by rfl) ⟨151544, by rfl⟩ : syracuseStep 3232949 = 303089) (by norm_num)
theorem B2155299 : Blo 2153435 2155299 := bstep (se 1 (by rfl) ⟨1616474, by rfl⟩ : syracuseStep 2155299 = 3232949) B3232949
theorem B5455613 : Blo 2153435 5455613 := bbase (se 3 (by rfl) ⟨1022927, by rfl⟩ : syracuseStep 5455613 = 2045855) (by norm_num)
theorem B3637075 : Blo 2153435 3637075 := bstep (se 1 (by rfl) ⟨2727806, by rfl⟩ : syracuseStep 3637075 = 5455613) B5455613
theorem B4849433 : Blo 2153435 4849433 := bstep (se 2 (by rfl) ⟨1818537, by rfl⟩ : syracuseStep 4849433 = 3637075) B3637075
theorem B3232955 : Blo 2153435 3232955 := bstep (se 1 (by rfl) ⟨2424716, by rfl⟩ : syracuseStep 3232955 = 4849433) B4849433
theorem B2155303 : Blo 2153435 2155303 := bstep (se 1 (by rfl) ⟨1616477, by rfl⟩ : syracuseStep 2155303 = 3232955) B3232955
theorem B2424721 : Blo 2153435 2424721 := bbase (se 2 (by rfl) ⟨909270, by rfl⟩ : syracuseStep 2424721 = 1818541) (by norm_num)
theorem B3232961 : Blo 2153435 3232961 := bstep (se 2 (by rfl) ⟨1212360, by rfl⟩ : syracuseStep 3232961 = 2424721) B2424721
theorem B2155307 : Blo 2153435 2155307 := bstep (se 1 (by rfl) ⟨1616480, by rfl⟩ : syracuseStep 2155307 = 3232961) B3232961
theorem B4091725 : Blo 2153435 4091725 := bbase (se 3 (by rfl) ⟨767198, by rfl⟩ : syracuseStep 4091725 = 1534397) (by norm_num)
theorem B5455633 : Blo 2153435 5455633 := bstep (se 2 (by rfl) ⟨2045862, by rfl⟩ : syracuseStep 5455633 = 4091725) B4091725
theorem B7274177 : Blo 2153435 7274177 := bstep (se 2 (by rfl) ⟨2727816, by rfl⟩ : syracuseStep 7274177 = 5455633) B5455633
theorem B4849451 : Blo 2153435 4849451 := bstep (se 1 (by rfl) ⟨3637088, by rfl⟩ : syracuseStep 4849451 = 7274177) B7274177
theorem B3232967 : Blo 2153435 3232967 := bstep (se 1 (by rfl) ⟨2424725, by rfl⟩ : syracuseStep 3232967 = 4849451) B4849451
theorem B2155311 : Blo 2153435 2155311 := bstep (se 1 (by rfl) ⟨1616483, by rfl⟩ : syracuseStep 2155311 = 3232967) B3232967
theorem B3232973 : Blo 2153435 3232973 := bbase (se 3 (by rfl) ⟨606182, by rfl⟩ : syracuseStep 3232973 = 1212365) (by norm_num)
theorem B2155315 : Blo 2153435 2155315 := bstep (se 1 (by rfl) ⟨1616486, by rfl⟩ : syracuseStep 2155315 = 3232973) B3232973
theorem B4849469 : Blo 2153435 4849469 := bbase (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) (by norm_num)
theorem B3232979 : Blo 2153435 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B2155319 : Blo 2153435 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B3637109 : Blo 2153435 3637109 := bbase (se 5 (by rfl) ⟨170489, by rfl⟩ : syracuseStep 3637109 = 340979) (by norm_num)
theorem B2424739 : Blo 2153435 2424739 := bstep (se 1 (by rfl) ⟨1818554, by rfl⟩ : syracuseStep 2424739 = 3637109) B3637109
theorem B3232985 : Blo 2153435 3232985 := bstep (se 2 (by rfl) ⟨1212369, by rfl⟩ : syracuseStep 3232985 = 2424739) B2424739
theorem B2155323 : Blo 2153435 2155323 := bstep (se 1 (by rfl) ⟨1616492, by rfl⟩ : syracuseStep 2155323 = 3232985) B3232985
theorem B5178629 : Blo 2153435 5178629 := bbase (se 4 (by rfl) ⟨485496, by rfl⟩ : syracuseStep 5178629 = 970993) (by norm_num)
theorem B3452419 : Blo 2153435 3452419 := bstep (se 1 (by rfl) ⟨2589314, by rfl⟩ : syracuseStep 3452419 = 5178629) B5178629
theorem B4603225 : Blo 2153435 4603225 := bstep (se 2 (by rfl) ⟨1726209, by rfl⟩ : syracuseStep 4603225 = 3452419) B3452419
theorem B6137633 : Blo 2153435 6137633 := bstep (se 2 (by rfl) ⟨2301612, by rfl⟩ : syracuseStep 6137633 = 4603225) B4603225
theorem B16367021 : Blo 2153435 16367021 := bstep (se 3 (by rfl) ⟨3068816, by rfl⟩ : syracuseStep 16367021 = 6137633) B6137633
theorem B10911347 : Blo 2153435 10911347 := bstep (se 1 (by rfl) ⟨8183510, by rfl⟩ : syracuseStep 10911347 = 16367021) B16367021
theorem B7274231 : Blo 2153435 7274231 := bstep (se 1 (by rfl) ⟨5455673, by rfl⟩ : syracuseStep 7274231 = 10911347) B10911347
theorem B4849487 : Blo 2153435 4849487 := bstep (se 1 (by rfl) ⟨3637115, by rfl⟩ : syracuseStep 4849487 = 7274231) B7274231
theorem B3232991 : Blo 2153435 3232991 := bstep (se 1 (by rfl) ⟨2424743, by rfl⟩ : syracuseStep 3232991 = 4849487) B4849487
theorem B2155327 : Blo 2153435 2155327 := bstep (se 1 (by rfl) ⟨1616495, by rfl⟩ : syracuseStep 2155327 = 3232991) B3232991
theorem B3232997 : Blo 2153435 3232997 := bbase (se 4 (by rfl) ⟨303093, by rfl⟩ : syracuseStep 3232997 = 606187) (by norm_num)
theorem B2155331 : Blo 2153435 2155331 := bstep (se 1 (by rfl) ⟨1616498, by rfl⟩ : syracuseStep 2155331 = 3232997) B3232997
theorem B5530133 : Blo 2153435 5530133 := bbase (se 6 (by rfl) ⟨129612, by rfl⟩ : syracuseStep 5530133 = 259225) (by norm_num)
theorem B3686755 : Blo 2153435 3686755 := bstep (se 1 (by rfl) ⟨2765066, by rfl⟩ : syracuseStep 3686755 = 5530133) B5530133
theorem B4915673 : Blo 2153435 4915673 := bstep (se 2 (by rfl) ⟨1843377, by rfl⟩ : syracuseStep 4915673 = 3686755) B3686755
theorem B3277115 : Blo 2153435 3277115 := bstep (se 1 (by rfl) ⟨2457836, by rfl⟩ : syracuseStep 3277115 = 4915673) B4915673
theorem B2184743 : Blo 2153435 2184743 := bstep (se 1 (by rfl) ⟨1638557, by rfl⟩ : syracuseStep 2184743 = 3277115) B3277115
theorem B5825981 : Blo 2153435 5825981 := bstep (se 3 (by rfl) ⟨1092371, by rfl⟩ : syracuseStep 5825981 = 2184743) B2184743
theorem B3883987 : Blo 2153435 3883987 := bstep (se 1 (by rfl) ⟨2912990, by rfl⟩ : syracuseStep 3883987 = 5825981) B5825981
theorem B5178649 : Blo 2153435 5178649 := bstep (se 2 (by rfl) ⟨1941993, by rfl⟩ : syracuseStep 5178649 = 3883987) B3883987
theorem B6904865 : Blo 2153435 6904865 := bstep (se 2 (by rfl) ⟨2589324, by rfl⟩ : syracuseStep 6904865 = 5178649) B5178649
theorem B4603243 : Blo 2153435 4603243 := bstep (se 1 (by rfl) ⟨3452432, by rfl⟩ : syracuseStep 4603243 = 6904865) B6904865
theorem B6137657 : Blo 2153435 6137657 := bstep (se 2 (by rfl) ⟨2301621, by rfl⟩ : syracuseStep 6137657 = 4603243) B4603243
theorem B4091771 : Blo 2153435 4091771 := bstep (se 1 (by rfl) ⟨3068828, by rfl⟩ : syracuseStep 4091771 = 6137657) B6137657
theorem B2727847 : Blo 2153435 2727847 := bstep (se 1 (by rfl) ⟨2045885, by rfl⟩ : syracuseStep 2727847 = 4091771) B4091771
theorem B3637129 : Blo 2153435 3637129 := bstep (se 2 (by rfl) ⟨1363923, by rfl⟩ : syracuseStep 3637129 = 2727847) B2727847
theorem B4849505 : Blo 2153435 4849505 := bstep (se 2 (by rfl) ⟨1818564, by rfl⟩ : syracuseStep 4849505 = 3637129) B3637129
theorem B3233003 : Blo 2153435 3233003 := bstep (se 1 (by rfl) ⟨2424752, by rfl⟩ : syracuseStep 3233003 = 4849505) B4849505
theorem B2155335 : Blo 2153435 2155335 := bstep (se 1 (by rfl) ⟨1616501, by rfl⟩ : syracuseStep 2155335 = 3233003) B3233003
theorem B2424757 : Blo 2153435 2424757 := bbase (se 5 (by rfl) ⟨113660, by rfl⟩ : syracuseStep 2424757 = 227321) (by norm_num)
theorem B3233009 : Blo 2153435 3233009 := bstep (se 2 (by rfl) ⟨1212378, by rfl⟩ : syracuseStep 3233009 = 2424757) B2424757
theorem B2155339 : Blo 2153435 2155339 := bstep (se 1 (by rfl) ⟨1616504, by rfl⟩ : syracuseStep 2155339 = 3233009) B3233009
theorem B2727857 : Blo 2153435 2727857 := bbase (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) (by norm_num)
theorem B7274285 : Blo 2153435 7274285 := bstep (se 3 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 7274285 = 2727857) B2727857
theorem B4849523 : Blo 2153435 4849523 := bstep (se 1 (by rfl) ⟨3637142, by rfl⟩ : syracuseStep 4849523 = 7274285) B7274285
theorem B3233015 : Blo 2153435 3233015 := bstep (se 1 (by rfl) ⟨2424761, by rfl⟩ : syracuseStep 3233015 = 4849523) B4849523
theorem B2155343 : Blo 2153435 2155343 := bstep (se 1 (by rfl) ⟨1616507, by rfl⟩ : syracuseStep 2155343 = 3233015) B3233015
theorem B3233021 : Blo 2153435 3233021 := bbase (se 3 (by rfl) ⟨606191, by rfl⟩ : syracuseStep 3233021 = 1212383) (by norm_num)
theorem B2155347 : Blo 2153435 2155347 := bstep (se 1 (by rfl) ⟨1616510, by rfl⟩ : syracuseStep 2155347 = 3233021) B3233021
theorem B4849541 : Blo 2153435 4849541 := bbase (se 4 (by rfl) ⟨454644, by rfl⟩ : syracuseStep 4849541 = 909289) (by norm_num)
theorem B3233027 : Blo 2153435 3233027 := bstep (se 1 (by rfl) ⟨2424770, by rfl⟩ : syracuseStep 3233027 = 4849541) B4849541
theorem B2155351 : Blo 2153435 2155351 := bstep (se 1 (by rfl) ⟨1616513, by rfl⟩ : syracuseStep 2155351 = 3233027) B3233027
theorem B2589349 : Blo 2153435 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B3452465 : Blo 2153435 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B2301643 : Blo 2153435 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B3068857 : Blo 2153435 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B4091809 : Blo 2153435 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B5455745 : Blo 2153435 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B3637163 : Blo 2153435 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B2424775 : Blo 2153435 2424775 := bstep (se 1 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 2424775 = 3637163) B3637163
theorem B3233033 : Blo 2153435 3233033 := bstep (se 2 (by rfl) ⟨1212387, by rfl⟩ : syracuseStep 3233033 = 2424775) B2424775
theorem B2155355 : Blo 2153435 2155355 := bstep (se 1 (by rfl) ⟨1616516, by rfl⟩ : syracuseStep 2155355 = 3233033) B3233033
theorem B10911509 : Blo 2153435 10911509 := bbase (se 6 (by rfl) ⟨255738, by rfl⟩ : syracuseStep 10911509 = 511477) (by norm_num)
theorem B7274339 : Blo 2153435 7274339 := bstep (se 1 (by rfl) ⟨5455754, by rfl⟩ : syracuseStep 7274339 = 10911509) B10911509
theorem B4849559 : Blo 2153435 4849559 := bstep (se 1 (by rfl) ⟨3637169, by rfl⟩ : syracuseStep 4849559 = 7274339) B7274339
theorem B3233039 : Blo 2153435 3233039 := bstep (se 1 (by rfl) ⟨2424779, by rfl⟩ : syracuseStep 3233039 = 4849559) B4849559
theorem B2155359 : Blo 2153435 2155359 := bstep (se 1 (by rfl) ⟨1616519, by rfl⟩ : syracuseStep 2155359 = 3233039) B3233039
theorem B3233045 : Blo 2153435 3233045 := bbase (se 6 (by rfl) ⟨75774, by rfl⟩ : syracuseStep 3233045 = 151549) (by norm_num)
theorem B2155363 : Blo 2153435 2155363 := bstep (se 1 (by rfl) ⟨1616522, by rfl⟩ : syracuseStep 2155363 = 3233045) B3233045
theorem B17478197 : Blo 2153435 17478197 := bbase (se 5 (by rfl) ⟨819290, by rfl⟩ : syracuseStep 17478197 = 1638581) (by norm_num)
theorem B11652131 : Blo 2153435 11652131 := bstep (se 1 (by rfl) ⟨8739098, by rfl⟩ : syracuseStep 11652131 = 17478197) B17478197
theorem B31072349 : Blo 2153435 31072349 := bstep (se 3 (by rfl) ⟨5826065, by rfl⟩ : syracuseStep 31072349 = 11652131) B11652131
theorem B20714899 : Blo 2153435 20714899 := bstep (se 1 (by rfl) ⟨15536174, by rfl⟩ : syracuseStep 20714899 = 31072349) B31072349
theorem B27619865 : Blo 2153435 27619865 := bstep (se 2 (by rfl) ⟨10357449, by rfl⟩ : syracuseStep 27619865 = 20714899) B20714899
theorem B18413243 : Blo 2153435 18413243 := bstep (se 1 (by rfl) ⟨13809932, by rfl⟩ : syracuseStep 18413243 = 27619865) B27619865
theorem B12275495 : Blo 2153435 12275495 := bstep (se 1 (by rfl) ⟨9206621, by rfl⟩ : syracuseStep 12275495 = 18413243) B18413243
theorem B8183663 : Blo 2153435 8183663 := bstep (se 1 (by rfl) ⟨6137747, by rfl⟩ : syracuseStep 8183663 = 12275495) B12275495
theorem B5455775 : Blo 2153435 5455775 := bstep (se 1 (by rfl) ⟨4091831, by rfl⟩ : syracuseStep 5455775 = 8183663) B8183663
theorem B3637183 : Blo 2153435 3637183 := bstep (se 1 (by rfl) ⟨2727887, by rfl⟩ : syracuseStep 3637183 = 5455775) B5455775
theorem B4849577 : Blo 2153435 4849577 := bstep (se 2 (by rfl) ⟨1818591, by rfl⟩ : syracuseStep 4849577 = 3637183) B3637183
theorem B3233051 : Blo 2153435 3233051 := bstep (se 1 (by rfl) ⟨2424788, by rfl⟩ : syracuseStep 3233051 = 4849577) B4849577
theorem B2155367 : Blo 2153435 2155367 := bstep (se 1 (by rfl) ⟨1616525, by rfl⟩ : syracuseStep 2155367 = 3233051) B3233051
theorem B2424793 : Blo 2153435 2424793 := bbase (se 2 (by rfl) ⟨909297, by rfl⟩ : syracuseStep 2424793 = 1818595) (by norm_num)
theorem B3233057 : Blo 2153435 3233057 := bstep (se 2 (by rfl) ⟨1212396, by rfl⟩ : syracuseStep 3233057 = 2424793) B2424793
theorem B2155371 : Blo 2153435 2155371 := bstep (se 1 (by rfl) ⟨1616528, by rfl⟩ : syracuseStep 2155371 = 3233057) B3233057
theorem B3068885 : Blo 2153435 3068885 := bbase (se 7 (by rfl) ⟨35963, by rfl⟩ : syracuseStep 3068885 = 71927) (by norm_num)
theorem B8183693 : Blo 2153435 8183693 := bstep (se 3 (by rfl) ⟨1534442, by rfl⟩ : syracuseStep 8183693 = 3068885) B3068885
theorem B5455795 : Blo 2153435 5455795 := bstep (se 1 (by rfl) ⟨4091846, by rfl⟩ : syracuseStep 5455795 = 8183693) B8183693
theorem B7274393 : Blo 2153435 7274393 := bstep (se 2 (by rfl) ⟨2727897, by rfl⟩ : syracuseStep 7274393 = 5455795) B5455795
theorem B4849595 : Blo 2153435 4849595 := bstep (se 1 (by rfl) ⟨3637196, by rfl⟩ : syracuseStep 4849595 = 7274393) B7274393
theorem B3233063 : Blo 2153435 3233063 := bstep (se 1 (by rfl) ⟨2424797, by rfl⟩ : syracuseStep 3233063 = 4849595) B4849595
theorem B2155375 : Blo 2153435 2155375 := bstep (se 1 (by rfl) ⟨1616531, by rfl⟩ : syracuseStep 2155375 = 3233063) B3233063
theorem B3233069 : Blo 2153435 3233069 := bbase (se 3 (by rfl) ⟨606200, by rfl⟩ : syracuseStep 3233069 = 1212401) (by norm_num)
theorem B2155379 : Blo 2153435 2155379 := bstep (se 1 (by rfl) ⟨1616534, by rfl⟩ : syracuseStep 2155379 = 3233069) B3233069
theorem B4849613 : Blo 2153435 4849613 := bbase (se 3 (by rfl) ⟨909302, by rfl⟩ : syracuseStep 4849613 = 1818605) (by norm_num)
theorem B3233075 : Blo 2153435 3233075 := bstep (se 1 (by rfl) ⟨2424806, by rfl⟩ : syracuseStep 3233075 = 4849613) B4849613
theorem B2155383 : Blo 2153435 2155383 := bstep (se 1 (by rfl) ⟨1616537, by rfl⟩ : syracuseStep 2155383 = 3233075) B3233075
theorem B2727913 : Blo 2153435 2727913 := bbase (se 2 (by rfl) ⟨1022967, by rfl⟩ : syracuseStep 2727913 = 2045935) (by norm_num)
theorem B3637217 : Blo 2153435 3637217 := bstep (se 2 (by rfl) ⟨1363956, by rfl⟩ : syracuseStep 3637217 = 2727913) B2727913
theorem B2424811 : Blo 2153435 2424811 := bstep (se 1 (by rfl) ⟨1818608, by rfl⟩ : syracuseStep 2424811 = 3637217) B3637217
theorem B3233081 : Blo 2153435 3233081 := bstep (se 2 (by rfl) ⟨1212405, by rfl⟩ : syracuseStep 3233081 = 2424811) B2424811
theorem B2155387 : Blo 2153435 2155387 := bstep (se 1 (by rfl) ⟨1616540, by rfl⟩ : syracuseStep 2155387 = 3233081) B3233081
theorem B11060549 : Blo 2153435 11060549 := bbase (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) (by norm_num)
theorem B7373699 : Blo 2153435 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B4915799 : Blo 2153435 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B3277199 : Blo 2153435 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B8739197 : Blo 2153435 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B5826131 : Blo 2153435 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B3884087 : Blo 2153435 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B2589391 : Blo 2153435 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B13810085 : Blo 2153435 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B9206723 : Blo 2153435 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B24551261 : Blo 2153435 24551261 := bstep (se 3 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 24551261 = 9206723) B9206723
theorem B16367507 : Blo 2153435 16367507 := bstep (se 1 (by rfl) ⟨12275630, by rfl⟩ : syracuseStep 16367507 = 24551261) B24551261
theorem B10911671 : Blo 2153435 10911671 := bstep (se 1 (by rfl) ⟨8183753, by rfl⟩ : syracuseStep 10911671 = 16367507) B16367507
theorem B7274447 : Blo 2153435 7274447 := bstep (se 1 (by rfl) ⟨5455835, by rfl⟩ : syracuseStep 7274447 = 10911671) B10911671
theorem B4849631 : Blo 2153435 4849631 := bstep (se 1 (by rfl) ⟨3637223, by rfl⟩ : syracuseStep 4849631 = 7274447) B7274447
theorem B3233087 : Blo 2153435 3233087 := bstep (se 1 (by rfl) ⟨2424815, by rfl⟩ : syracuseStep 3233087 = 4849631) B4849631
theorem B2155391 : Blo 2153435 2155391 := bstep (se 1 (by rfl) ⟨1616543, by rfl⟩ : syracuseStep 2155391 = 3233087) B3233087
theorem B3233093 : Blo 2153435 3233093 := bbase (se 4 (by rfl) ⟨303102, by rfl⟩ : syracuseStep 3233093 = 606205) (by norm_num)
theorem B2155395 : Blo 2153435 2155395 := bstep (se 1 (by rfl) ⟨1616546, by rfl⟩ : syracuseStep 2155395 = 3233093) B3233093
theorem B3637237 : Blo 2153435 3637237 := bbase (se 5 (by rfl) ⟨170495, by rfl⟩ : syracuseStep 3637237 = 340991) (by norm_num)
theorem B4849649 : Blo 2153435 4849649 := bstep (se 2 (by rfl) ⟨1818618, by rfl⟩ : syracuseStep 4849649 = 3637237) B3637237
theorem B3233099 : Blo 2153435 3233099 := bstep (se 1 (by rfl) ⟨2424824, by rfl⟩ : syracuseStep 3233099 = 4849649) B4849649
theorem B2155399 : Blo 2153435 2155399 := bstep (se 1 (by rfl) ⟨1616549, by rfl⟩ : syracuseStep 2155399 = 3233099) B3233099
theorem B2424829 : Blo 2153435 2424829 := bbase (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) (by norm_num)
theorem B3233105 : Blo 2153435 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B2155403 : Blo 2153435 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B7274501 : Blo 2153435 7274501 := bbase (se 4 (by rfl) ⟨681984, by rfl⟩ : syracuseStep 7274501 = 1363969) (by norm_num)
theorem B4849667 : Blo 2153435 4849667 := bstep (se 1 (by rfl) ⟨3637250, by rfl⟩ : syracuseStep 4849667 = 7274501) B7274501
theorem B3233111 : Blo 2153435 3233111 := bstep (se 1 (by rfl) ⟨2424833, by rfl⟩ : syracuseStep 3233111 = 4849667) B4849667
theorem B2155407 : Blo 2153435 2155407 := bstep (se 1 (by rfl) ⟨1616555, by rfl⟩ : syracuseStep 2155407 = 3233111) B3233111
theorem B3233117 : Blo 2153435 3233117 := bbase (se 3 (by rfl) ⟨606209, by rfl⟩ : syracuseStep 3233117 = 1212419) (by norm_num)
theorem B2155411 : Blo 2153435 2155411 := bstep (se 1 (by rfl) ⟨1616558, by rfl⟩ : syracuseStep 2155411 = 3233117) B3233117
theorem B4849685 : Blo 2153435 4849685 := bbase (se 6 (by rfl) ⟨113664, by rfl⟩ : syracuseStep 4849685 = 227329) (by norm_num)
theorem B3233123 : Blo 2153435 3233123 := bstep (se 1 (by rfl) ⟨2424842, by rfl⟩ : syracuseStep 3233123 = 4849685) B4849685
theorem B2155415 : Blo 2153435 2155415 := bstep (se 1 (by rfl) ⟨1616561, by rfl⟩ : syracuseStep 2155415 = 3233123) B3233123
theorem B8183861 : Blo 2153435 8183861 := bbase (se 5 (by rfl) ⟨383618, by rfl⟩ : syracuseStep 8183861 = 767237) (by norm_num)
theorem B5455907 : Blo 2153435 5455907 := bstep (se 1 (by rfl) ⟨4091930, by rfl⟩ : syracuseStep 5455907 = 8183861) B8183861
theorem B3637271 : Blo 2153435 3637271 := bstep (se 1 (by rfl) ⟨2727953, by rfl⟩ : syracuseStep 3637271 = 5455907) B5455907
theorem B2424847 : Blo 2153435 2424847 := bstep (se 1 (by rfl) ⟨1818635, by rfl⟩ : syracuseStep 2424847 = 3637271) B3637271
theorem B3233129 : Blo 2153435 3233129 := bstep (se 2 (by rfl) ⟨1212423, by rfl⟩ : syracuseStep 3233129 = 2424847) B2424847
theorem B2155419 : Blo 2153435 2155419 := bstep (se 1 (by rfl) ⟨1616564, by rfl⟩ : syracuseStep 2155419 = 3233129) B3233129
theorem B3452573 : Blo 2153435 3452573 := bbase (se 3 (by rfl) ⟨647357, by rfl⟩ : syracuseStep 3452573 = 1294715) (by norm_num)
theorem B2301715 : Blo 2153435 2301715 := bstep (se 1 (by rfl) ⟨1726286, by rfl⟩ : syracuseStep 2301715 = 3452573) B3452573
theorem B12275813 : Blo 2153435 12275813 := bstep (se 4 (by rfl) ⟨1150857, by rfl⟩ : syracuseStep 12275813 = 2301715) B2301715
theorem B8183875 : Blo 2153435 8183875 := bstep (se 1 (by rfl) ⟨6137906, by rfl⟩ : syracuseStep 8183875 = 12275813) B12275813
theorem B10911833 : Blo 2153435 10911833 := bstep (se 2 (by rfl) ⟨4091937, by rfl⟩ : syracuseStep 10911833 = 8183875) B8183875
theorem B7274555 : Blo 2153435 7274555 := bstep (se 1 (by rfl) ⟨5455916, by rfl⟩ : syracuseStep 7274555 = 10911833) B10911833
theorem B4849703 : Blo 2153435 4849703 := bstep (se 1 (by rfl) ⟨3637277, by rfl⟩ : syracuseStep 4849703 = 7274555) B7274555
theorem B3233135 : Blo 2153435 3233135 := bstep (se 1 (by rfl) ⟨2424851, by rfl⟩ : syracuseStep 3233135 = 4849703) B4849703
theorem B2155423 : Blo 2153435 2155423 := bstep (se 1 (by rfl) ⟨1616567, by rfl⟩ : syracuseStep 2155423 = 3233135) B3233135
theorem B3233141 : Blo 2153435 3233141 := bbase (se 5 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 3233141 = 303107) (by norm_num)
theorem B2155427 : Blo 2153435 2155427 := bstep (se 1 (by rfl) ⟨1616570, by rfl⟩ : syracuseStep 2155427 = 3233141) B3233141
theorem B3068965 : Blo 2153435 3068965 := bbase (se 4 (by rfl) ⟨287715, by rfl⟩ : syracuseStep 3068965 = 575431) (by norm_num)
theorem B4091953 : Blo 2153435 4091953 := bstep (se 2 (by rfl) ⟨1534482, by rfl⟩ : syracuseStep 4091953 = 3068965) B3068965
theorem B5455937 : Blo 2153435 5455937 := bstep (se 2 (by rfl) ⟨2045976, by rfl⟩ : syracuseStep 5455937 = 4091953) B4091953
theorem B3637291 : Blo 2153435 3637291 := bstep (se 1 (by rfl) ⟨2727968, by rfl⟩ : syracuseStep 3637291 = 5455937) B5455937
theorem B4849721 : Blo 2153435 4849721 := bstep (se 2 (by rfl) ⟨1818645, by rfl⟩ : syracuseStep 4849721 = 3637291) B3637291
theorem B3233147 : Blo 2153435 3233147 := bstep (se 1 (by rfl) ⟨2424860, by rfl⟩ : syracuseStep 3233147 = 4849721) B4849721
theorem B2155431 : Blo 2153435 2155431 := bstep (se 1 (by rfl) ⟨1616573, by rfl⟩ : syracuseStep 2155431 = 3233147) B3233147
theorem B2424865 : Blo 2153435 2424865 := bbase (se 2 (by rfl) ⟨909324, by rfl⟩ : syracuseStep 2424865 = 1818649) (by norm_num)
theorem B3233153 : Blo 2153435 3233153 := bstep (se 2 (by rfl) ⟨1212432, by rfl⟩ : syracuseStep 3233153 = 2424865) B2424865
theorem B2155435 : Blo 2153435 2155435 := bstep (se 1 (by rfl) ⟨1616576, by rfl⟩ : syracuseStep 2155435 = 3233153) B3233153
theorem C0 (j : ℕ) (h1 : 538358 ≤ j) (h2 : j ≤ 538858) : Blo 2153435 (4 * j + 3) := by
  interval_cases j
  · exact B2153435
  · exact B2153439
  · exact B2153443
  · exact B2153447
  · exact B2153451
  · exact B2153455
  · exact B2153459
  · exact B2153463
  · exact B2153467
  · exact B2153471
  · exact B2153475
  · exact B2153479
  · exact B2153483
  · exact B2153487
  · exact B2153491
  · exact B2153495
  · exact B2153499
  · exact B2153503
  · exact B2153507
  · exact B2153511
  · exact B2153515
  · exact B2153519
  · exact B2153523
  · exact B2153527
  · exact B2153531
  · exact B2153535
  · exact B2153539
  · exact B2153543
  · exact B2153547
  · exact B2153551
  · exact B2153555
  · exact B2153559
  · exact B2153563
  · exact B2153567
  · exact B2153571
  · exact B2153575
  · exact B2153579
  · exact B2153583
  · exact B2153587
  · exact B2153591
  · exact B2153595
  · exact B2153599
  · exact B2153603
  · exact B2153607
  · exact B2153611
  · exact B2153615
  · exact B2153619
  · exact B2153623
  · exact B2153627
  · exact B2153631
  · exact B2153635
  · exact B2153639
  · exact B2153643
  · exact B2153647
  · exact B2153651
  · exact B2153655
  · exact B2153659
  · exact B2153663
  · exact B2153667
  · exact B2153671
  · exact B2153675
  · exact B2153679
  · exact B2153683
  · exact B2153687
  · exact B2153691
  · exact B2153695
  · exact B2153699
  · exact B2153703
  · exact B2153707
  · exact B2153711
  · exact B2153715
  · exact B2153719
  · exact B2153723
  · exact B2153727
  · exact B2153731
  · exact B2153735
  · exact B2153739
  · exact B2153743
  · exact B2153747
  · exact B2153751
  · exact B2153755
  · exact B2153759
  · exact B2153763
  · exact B2153767
  · exact B2153771
  · exact B2153775
  · exact B2153779
  · exact B2153783
  · exact B2153787
  · exact B2153791
  · exact B2153795
  · exact B2153799
  · exact B2153803
  · exact B2153807
  · exact B2153811
  · exact B2153815
  · exact B2153819
  · exact B2153823
  · exact B2153827
  · exact B2153831
  · exact B2153835
  · exact B2153839
  · exact B2153843
  · exact B2153847
  · exact B2153851
  · exact B2153855
  · exact B2153859
  · exact B2153863
  · exact B2153867
  · exact B2153871
  · exact B2153875
  · exact B2153879
  · exact B2153883
  · exact B2153887
  · exact B2153891
  · exact B2153895
  · exact B2153899
  · exact B2153903
  · exact B2153907
  · exact B2153911
  · exact B2153915
  · exact B2153919
  · exact B2153923
  · exact B2153927
  · exact B2153931
  · exact B2153935
  · exact B2153939
  · exact B2153943
  · exact B2153947
  · exact B2153951
  · exact B2153955
  · exact B2153959
  · exact B2153963
  · exact B2153967
  · exact B2153971
  · exact B2153975
  · exact B2153979
  · exact B2153983
  · exact B2153987
  · exact B2153991
  · exact B2153995
  · exact B2153999
  · exact B2154003
  · exact B2154007
  · exact B2154011
  · exact B2154015
  · exact B2154019
  · exact B2154023
  · exact B2154027
  · exact B2154031
  · exact B2154035
  · exact B2154039
  · exact B2154043
  · exact B2154047
  · exact B2154051
  · exact B2154055
  · exact B2154059
  · exact B2154063
  · exact B2154067
  · exact B2154071
  · exact B2154075
  · exact B2154079
  · exact B2154083
  · exact B2154087
  · exact B2154091
  · exact B2154095
  · exact B2154099
  · exact B2154103
  · exact B2154107
  · exact B2154111
  · exact B2154115
  · exact B2154119
  · exact B2154123
  · exact B2154127
  · exact B2154131
  · exact B2154135
  · exact B2154139
  · exact B2154143
  · exact B2154147
  · exact B2154151
  · exact B2154155
  · exact B2154159
  · exact B2154163
  · exact B2154167
  · exact B2154171
  · exact B2154175
  · exact B2154179
  · exact B2154183
  · exact B2154187
  · exact B2154191
  · exact B2154195
  · exact B2154199
  · exact B2154203
  · exact B2154207
  · exact B2154211
  · exact B2154215
  · exact B2154219
  · exact B2154223
  · exact B2154227
  · exact B2154231
  · exact B2154235
  · exact B2154239
  · exact B2154243
  · exact B2154247
  · exact B2154251
  · exact B2154255
  · exact B2154259
  · exact B2154263
  · exact B2154267
  · exact B2154271
  · exact B2154275
  · exact B2154279
  · exact B2154283
  · exact B2154287
  · exact B2154291
  · exact B2154295
  · exact B2154299
  · exact B2154303
  · exact B2154307
  · exact B2154311
  · exact B2154315
  · exact B2154319
  · exact B2154323
  · exact B2154327
  · exact B2154331
  · exact B2154335
  · exact B2154339
  · exact B2154343
  · exact B2154347
  · exact B2154351
  · exact B2154355
  · exact B2154359
  · exact B2154363
  · exact B2154367
  · exact B2154371
  · exact B2154375
  · exact B2154379
  · exact B2154383
  · exact B2154387
  · exact B2154391
  · exact B2154395
  · exact B2154399
  · exact B2154403
  · exact B2154407
  · exact B2154411
  · exact B2154415
  · exact B2154419
  · exact B2154423
  · exact B2154427
  · exact B2154431
  · exact B2154435
  · exact B2154439
  · exact B2154443
  · exact B2154447
  · exact B2154451
  · exact B2154455
  · exact B2154459
  · exact B2154463
  · exact B2154467
  · exact B2154471
  · exact B2154475
  · exact B2154479
  · exact B2154483
  · exact B2154487
  · exact B2154491
  · exact B2154495
  · exact B2154499
  · exact B2154503
  · exact B2154507
  · exact B2154511
  · exact B2154515
  · exact B2154519
  · exact B2154523
  · exact B2154527
  · exact B2154531
  · exact B2154535
  · exact B2154539
  · exact B2154543
  · exact B2154547
  · exact B2154551
  · exact B2154555
  · exact B2154559
  · exact B2154563
  · exact B2154567
  · exact B2154571
  · exact B2154575
  · exact B2154579
  · exact B2154583
  · exact B2154587
  · exact B2154591
  · exact B2154595
  · exact B2154599
  · exact B2154603
  · exact B2154607
  · exact B2154611
  · exact B2154615
  · exact B2154619
  · exact B2154623
  · exact B2154627
  · exact B2154631
  · exact B2154635
  · exact B2154639
  · exact B2154643
  · exact B2154647
  · exact B2154651
  · exact B2154655
  · exact B2154659
  · exact B2154663
  · exact B2154667
  · exact B2154671
  · exact B2154675
  · exact B2154679
  · exact B2154683
  · exact B2154687
  · exact B2154691
  · exact B2154695
  · exact B2154699
  · exact B2154703
  · exact B2154707
  · exact B2154711
  · exact B2154715
  · exact B2154719
  · exact B2154723
  · exact B2154727
  · exact B2154731
  · exact B2154735
  · exact B2154739
  · exact B2154743
  · exact B2154747
  · exact B2154751
  · exact B2154755
  · exact B2154759
  · exact B2154763
  · exact B2154767
  · exact B2154771
  · exact B2154775
  · exact B2154779
  · exact B2154783
  · exact B2154787
  · exact B2154791
  · exact B2154795
  · exact B2154799
  · exact B2154803
  · exact B2154807
  · exact B2154811
  · exact B2154815
  · exact B2154819
  · exact B2154823
  · exact B2154827
  · exact B2154831
  · exact B2154835
  · exact B2154839
  · exact B2154843
  · exact B2154847
  · exact B2154851
  · exact B2154855
  · exact B2154859
  · exact B2154863
  · exact B2154867
  · exact B2154871
  · exact B2154875
  · exact B2154879
  · exact B2154883
  · exact B2154887
  · exact B2154891
  · exact B2154895
  · exact B2154899
  · exact B2154903
  · exact B2154907
  · exact B2154911
  · exact B2154915
  · exact B2154919
  · exact B2154923
  · exact B2154927
  · exact B2154931
  · exact B2154935
  · exact B2154939
  · exact B2154943
  · exact B2154947
  · exact B2154951
  · exact B2154955
  · exact B2154959
  · exact B2154963
  · exact B2154967
  · exact B2154971
  · exact B2154975
  · exact B2154979
  · exact B2154983
  · exact B2154987
  · exact B2154991
  · exact B2154995
  · exact B2154999
  · exact B2155003
  · exact B2155007
  · exact B2155011
  · exact B2155015
  · exact B2155019
  · exact B2155023
  · exact B2155027
  · exact B2155031
  · exact B2155035
  · exact B2155039
  · exact B2155043
  · exact B2155047
  · exact B2155051
  · exact B2155055
  · exact B2155059
  · exact B2155063
  · exact B2155067
  · exact B2155071
  · exact B2155075
  · exact B2155079
  · exact B2155083
  · exact B2155087
  · exact B2155091
  · exact B2155095
  · exact B2155099
  · exact B2155103
  · exact B2155107
  · exact B2155111
  · exact B2155115
  · exact B2155119
  · exact B2155123
  · exact B2155127
  · exact B2155131
  · exact B2155135
  · exact B2155139
  · exact B2155143
  · exact B2155147
  · exact B2155151
  · exact B2155155
  · exact B2155159
  · exact B2155163
  · exact B2155167
  · exact B2155171
  · exact B2155175
  · exact B2155179
  · exact B2155183
  · exact B2155187
  · exact B2155191
  · exact B2155195
  · exact B2155199
  · exact B2155203
  · exact B2155207
  · exact B2155211
  · exact B2155215
  · exact B2155219
  · exact B2155223
  · exact B2155227
  · exact B2155231
  · exact B2155235
  · exact B2155239
  · exact B2155243
  · exact B2155247
  · exact B2155251
  · exact B2155255
  · exact B2155259
  · exact B2155263
  · exact B2155267
  · exact B2155271
  · exact B2155275
  · exact B2155279
  · exact B2155283
  · exact B2155287
  · exact B2155291
  · exact B2155295
  · exact B2155299
  · exact B2155303
  · exact B2155307
  · exact B2155311
  · exact B2155315
  · exact B2155319
  · exact B2155323
  · exact B2155327
  · exact B2155331
  · exact B2155335
  · exact B2155339
  · exact B2155343
  · exact B2155347
  · exact B2155351
  · exact B2155355
  · exact B2155359
  · exact B2155363
  · exact B2155367
  · exact B2155371
  · exact B2155375
  · exact B2155379
  · exact B2155383
  · exact B2155387
  · exact B2155391
  · exact B2155395
  · exact B2155399
  · exact B2155403
  · exact B2155407
  · exact B2155411
  · exact B2155415
  · exact B2155419
  · exact B2155423
  · exact B2155427
  · exact B2155431
  · exact B2155435
theorem solution (m : ℕ) (hlo : 2153435 ≤ m) (hhi : m ≤ 2155435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 538358 ≤ j := by omega
    have hj2 : j ≤ 538858 := by omega
    have hb : Blo 2153435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
