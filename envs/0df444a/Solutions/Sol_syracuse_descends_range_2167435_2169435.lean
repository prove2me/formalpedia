-- Prove2me | solution 1 for syracuse_descends_range_2167435_2169435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:43.884868+00:00
-- url     : https://prove2.me/submissions/4ad10163-e564-4d75-ad13-afd587c416a2

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

theorem B2438365 : Blo 2167435 2438365 := bbase (se 3 (by rfl) ⟨457193, by rfl⟩ : syracuseStep 2438365 = 914387) (by norm_num)
theorem B3251153 : Blo 2167435 3251153 := bstep (se 2 (by rfl) ⟨1219182, by rfl⟩ : syracuseStep 3251153 = 2438365) B2438365
theorem B2167435 : Blo 2167435 2167435 := bstep (se 1 (by rfl) ⟨1625576, by rfl⟩ : syracuseStep 2167435 = 3251153) B3251153
theorem B7315109 : Blo 2167435 7315109 := bbase (se 4 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 7315109 = 1371583) (by norm_num)
theorem B4876739 : Blo 2167435 4876739 := bstep (se 1 (by rfl) ⟨3657554, by rfl⟩ : syracuseStep 4876739 = 7315109) B7315109
theorem B3251159 : Blo 2167435 3251159 := bstep (se 1 (by rfl) ⟨2438369, by rfl⟩ : syracuseStep 3251159 = 4876739) B4876739
theorem B2167439 : Blo 2167435 2167439 := bstep (se 1 (by rfl) ⟨1625579, by rfl⟩ : syracuseStep 2167439 = 3251159) B3251159
theorem B3251165 : Blo 2167435 3251165 := bbase (se 3 (by rfl) ⟨609593, by rfl⟩ : syracuseStep 3251165 = 1219187) (by norm_num)
theorem B2167443 : Blo 2167435 2167443 := bstep (se 1 (by rfl) ⟨1625582, by rfl⟩ : syracuseStep 2167443 = 3251165) B3251165
theorem B4876757 : Blo 2167435 4876757 := bbase (se 7 (by rfl) ⟨57149, by rfl⟩ : syracuseStep 4876757 = 114299) (by norm_num)
theorem B3251171 : Blo 2167435 3251171 := bstep (se 1 (by rfl) ⟨2438378, by rfl⟩ : syracuseStep 3251171 = 4876757) B4876757
theorem B2167447 : Blo 2167435 2167447 := bstep (se 1 (by rfl) ⟨1625585, by rfl⟩ : syracuseStep 2167447 = 3251171) B3251171
theorem B8455637 : Blo 2167435 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B22548365 : Blo 2167435 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B15032243 : Blo 2167435 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B10021495 : Blo 2167435 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B13361993 : Blo 2167435 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B8907995 : Blo 2167435 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B23754653 : Blo 2167435 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B15836435 : Blo 2167435 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B10557623 : Blo 2167435 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B7038415 : Blo 2167435 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B9384553 : Blo 2167435 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B12512737 : Blo 2167435 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B66734597 : Blo 2167435 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B44489731 : Blo 2167435 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B59319641 : Blo 2167435 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B158185709 : Blo 2167435 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B105457139 : Blo 2167435 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B70304759 : Blo 2167435 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B46869839 : Blo 2167435 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B31246559 : Blo 2167435 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B20831039 : Blo 2167435 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B13887359 : Blo 2167435 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B9258239 : Blo 2167435 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B6172159 : Blo 2167435 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B8229545 : Blo 2167435 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B5486363 : Blo 2167435 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B3657575 : Blo 2167435 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B2438383 : Blo 2167435 2438383 := bstep (se 1 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 2438383 = 3657575) B3657575
theorem B3251177 : Blo 2167435 3251177 := bstep (se 2 (by rfl) ⟨1219191, by rfl⟩ : syracuseStep 3251177 = 2438383) B2438383
theorem B2167451 : Blo 2167435 2167451 := bstep (se 1 (by rfl) ⟨1625588, by rfl⟩ : syracuseStep 2167451 = 3251177) B3251177
theorem B7811653 : Blo 2167435 7811653 := bbase (se 4 (by rfl) ⟨732342, by rfl⟩ : syracuseStep 7811653 = 1464685) (by norm_num)
theorem B10415537 : Blo 2167435 10415537 := bstep (se 2 (by rfl) ⟨3905826, by rfl⟩ : syracuseStep 10415537 = 7811653) B7811653
theorem B6943691 : Blo 2167435 6943691 := bstep (se 1 (by rfl) ⟨5207768, by rfl⟩ : syracuseStep 6943691 = 10415537) B10415537
theorem B18516509 : Blo 2167435 18516509 := bstep (se 3 (by rfl) ⟨3471845, by rfl⟩ : syracuseStep 18516509 = 6943691) B6943691
theorem B12344339 : Blo 2167435 12344339 := bstep (se 1 (by rfl) ⟨9258254, by rfl⟩ : syracuseStep 12344339 = 18516509) B18516509
theorem B8229559 : Blo 2167435 8229559 := bstep (se 1 (by rfl) ⟨6172169, by rfl⟩ : syracuseStep 8229559 = 12344339) B12344339
theorem B10972745 : Blo 2167435 10972745 := bstep (se 2 (by rfl) ⟨4114779, by rfl⟩ : syracuseStep 10972745 = 8229559) B8229559
theorem B7315163 : Blo 2167435 7315163 := bstep (se 1 (by rfl) ⟨5486372, by rfl⟩ : syracuseStep 7315163 = 10972745) B10972745
theorem B4876775 : Blo 2167435 4876775 := bstep (se 1 (by rfl) ⟨3657581, by rfl⟩ : syracuseStep 4876775 = 7315163) B7315163
theorem B3251183 : Blo 2167435 3251183 := bstep (se 1 (by rfl) ⟨2438387, by rfl⟩ : syracuseStep 3251183 = 4876775) B4876775
theorem B2167455 : Blo 2167435 2167455 := bstep (se 1 (by rfl) ⟨1625591, by rfl⟩ : syracuseStep 2167455 = 3251183) B3251183
theorem B3251189 : Blo 2167435 3251189 := bbase (se 5 (by rfl) ⟨152399, by rfl⟩ : syracuseStep 3251189 = 304799) (by norm_num)
theorem B2167459 : Blo 2167435 2167459 := bstep (se 1 (by rfl) ⟨1625594, by rfl⟩ : syracuseStep 2167459 = 3251189) B3251189
theorem B5207789 : Blo 2167435 5207789 := bbase (se 3 (by rfl) ⟨976460, by rfl⟩ : syracuseStep 5207789 = 1952921) (by norm_num)
theorem B3471859 : Blo 2167435 3471859 := bstep (se 1 (by rfl) ⟨2603894, by rfl⟩ : syracuseStep 3471859 = 5207789) B5207789
theorem B4629145 : Blo 2167435 4629145 := bstep (se 2 (by rfl) ⟨1735929, by rfl⟩ : syracuseStep 4629145 = 3471859) B3471859
theorem B6172193 : Blo 2167435 6172193 := bstep (se 2 (by rfl) ⟨2314572, by rfl⟩ : syracuseStep 6172193 = 4629145) B4629145
theorem B4114795 : Blo 2167435 4114795 := bstep (se 1 (by rfl) ⟨3086096, by rfl⟩ : syracuseStep 4114795 = 6172193) B6172193
theorem B5486393 : Blo 2167435 5486393 := bstep (se 2 (by rfl) ⟨2057397, by rfl⟩ : syracuseStep 5486393 = 4114795) B4114795
theorem B3657595 : Blo 2167435 3657595 := bstep (se 1 (by rfl) ⟨2743196, by rfl⟩ : syracuseStep 3657595 = 5486393) B5486393
theorem B4876793 : Blo 2167435 4876793 := bstep (se 2 (by rfl) ⟨1828797, by rfl⟩ : syracuseStep 4876793 = 3657595) B3657595
theorem B3251195 : Blo 2167435 3251195 := bstep (se 1 (by rfl) ⟨2438396, by rfl⟩ : syracuseStep 3251195 = 4876793) B4876793
theorem B2167463 : Blo 2167435 2167463 := bstep (se 1 (by rfl) ⟨1625597, by rfl⟩ : syracuseStep 2167463 = 3251195) B3251195
theorem B2438401 : Blo 2167435 2438401 := bbase (se 2 (by rfl) ⟨914400, by rfl⟩ : syracuseStep 2438401 = 1828801) (by norm_num)
theorem B3251201 : Blo 2167435 3251201 := bstep (se 2 (by rfl) ⟨1219200, by rfl⟩ : syracuseStep 3251201 = 2438401) B2438401
theorem B2167467 : Blo 2167435 2167467 := bstep (se 1 (by rfl) ⟨1625600, by rfl⟩ : syracuseStep 2167467 = 3251201) B3251201
theorem B5486413 : Blo 2167435 5486413 := bbase (se 3 (by rfl) ⟨1028702, by rfl⟩ : syracuseStep 5486413 = 2057405) (by norm_num)
theorem B7315217 : Blo 2167435 7315217 := bstep (se 2 (by rfl) ⟨2743206, by rfl⟩ : syracuseStep 7315217 = 5486413) B5486413
theorem B4876811 : Blo 2167435 4876811 := bstep (se 1 (by rfl) ⟨3657608, by rfl⟩ : syracuseStep 4876811 = 7315217) B7315217
theorem B3251207 : Blo 2167435 3251207 := bstep (se 1 (by rfl) ⟨2438405, by rfl⟩ : syracuseStep 3251207 = 4876811) B4876811
theorem B2167471 : Blo 2167435 2167471 := bstep (se 1 (by rfl) ⟨1625603, by rfl⟩ : syracuseStep 2167471 = 3251207) B3251207
theorem B3251213 : Blo 2167435 3251213 := bbase (se 3 (by rfl) ⟨609602, by rfl⟩ : syracuseStep 3251213 = 1219205) (by norm_num)
theorem B2167475 : Blo 2167435 2167475 := bstep (se 1 (by rfl) ⟨1625606, by rfl⟩ : syracuseStep 2167475 = 3251213) B3251213
theorem B4876829 : Blo 2167435 4876829 := bbase (se 3 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 4876829 = 1828811) (by norm_num)
theorem B3251219 : Blo 2167435 3251219 := bstep (se 1 (by rfl) ⟨2438414, by rfl⟩ : syracuseStep 3251219 = 4876829) B4876829
theorem B2167479 : Blo 2167435 2167479 := bstep (se 1 (by rfl) ⟨1625609, by rfl⟩ : syracuseStep 2167479 = 3251219) B3251219
theorem B3657629 : Blo 2167435 3657629 := bbase (se 3 (by rfl) ⟨685805, by rfl⟩ : syracuseStep 3657629 = 1371611) (by norm_num)
theorem B2438419 : Blo 2167435 2438419 := bstep (se 1 (by rfl) ⟨1828814, by rfl⟩ : syracuseStep 2438419 = 3657629) B3657629
theorem B3251225 : Blo 2167435 3251225 := bstep (se 2 (by rfl) ⟨1219209, by rfl⟩ : syracuseStep 3251225 = 2438419) B2438419
theorem B2167483 : Blo 2167435 2167483 := bstep (se 1 (by rfl) ⟨1625612, by rfl⟩ : syracuseStep 2167483 = 3251225) B3251225
theorem B20831381 : Blo 2167435 20831381 := bbase (se 6 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 20831381 = 976471) (by norm_num)
theorem B13887587 : Blo 2167435 13887587 := bstep (se 1 (by rfl) ⟨10415690, by rfl⟩ : syracuseStep 13887587 = 20831381) B20831381
theorem B9258391 : Blo 2167435 9258391 := bstep (se 1 (by rfl) ⟨6943793, by rfl⟩ : syracuseStep 9258391 = 13887587) B13887587
theorem B12344521 : Blo 2167435 12344521 := bstep (se 2 (by rfl) ⟨4629195, by rfl⟩ : syracuseStep 12344521 = 9258391) B9258391
theorem B16459361 : Blo 2167435 16459361 := bstep (se 2 (by rfl) ⟨6172260, by rfl⟩ : syracuseStep 16459361 = 12344521) B12344521
theorem B10972907 : Blo 2167435 10972907 := bstep (se 1 (by rfl) ⟨8229680, by rfl⟩ : syracuseStep 10972907 = 16459361) B16459361
theorem B7315271 : Blo 2167435 7315271 := bstep (se 1 (by rfl) ⟨5486453, by rfl⟩ : syracuseStep 7315271 = 10972907) B10972907
theorem B4876847 : Blo 2167435 4876847 := bstep (se 1 (by rfl) ⟨3657635, by rfl⟩ : syracuseStep 4876847 = 7315271) B7315271
theorem B3251231 : Blo 2167435 3251231 := bstep (se 1 (by rfl) ⟨2438423, by rfl⟩ : syracuseStep 3251231 = 4876847) B4876847
theorem B2167487 : Blo 2167435 2167487 := bstep (se 1 (by rfl) ⟨1625615, by rfl⟩ : syracuseStep 2167487 = 3251231) B3251231
theorem B3251237 : Blo 2167435 3251237 := bbase (se 4 (by rfl) ⟨304803, by rfl⟩ : syracuseStep 3251237 = 609607) (by norm_num)
theorem B2167491 : Blo 2167435 2167491 := bstep (se 1 (by rfl) ⟨1625618, by rfl⟩ : syracuseStep 2167491 = 3251237) B3251237
theorem B2743237 : Blo 2167435 2743237 := bbase (se 4 (by rfl) ⟨257178, by rfl⟩ : syracuseStep 2743237 = 514357) (by norm_num)
theorem B3657649 : Blo 2167435 3657649 := bstep (se 2 (by rfl) ⟨1371618, by rfl⟩ : syracuseStep 3657649 = 2743237) B2743237
theorem B4876865 : Blo 2167435 4876865 := bstep (se 2 (by rfl) ⟨1828824, by rfl⟩ : syracuseStep 4876865 = 3657649) B3657649
theorem B3251243 : Blo 2167435 3251243 := bstep (se 1 (by rfl) ⟨2438432, by rfl⟩ : syracuseStep 3251243 = 4876865) B4876865
theorem B2167495 : Blo 2167435 2167495 := bstep (se 1 (by rfl) ⟨1625621, by rfl⟩ : syracuseStep 2167495 = 3251243) B3251243
theorem B2438437 : Blo 2167435 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B3251249 : Blo 2167435 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B2167499 : Blo 2167435 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B5207885 : Blo 2167435 5207885 := bbase (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) (by norm_num)
theorem B3471923 : Blo 2167435 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B9258461 : Blo 2167435 9258461 := bstep (se 3 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 9258461 = 3471923) B3471923
theorem B6172307 : Blo 2167435 6172307 := bstep (se 1 (by rfl) ⟨4629230, by rfl⟩ : syracuseStep 6172307 = 9258461) B9258461
theorem B4114871 : Blo 2167435 4114871 := bstep (se 1 (by rfl) ⟨3086153, by rfl⟩ : syracuseStep 4114871 = 6172307) B6172307
theorem B2743247 : Blo 2167435 2743247 := bstep (se 1 (by rfl) ⟨2057435, by rfl⟩ : syracuseStep 2743247 = 4114871) B4114871
theorem B7315325 : Blo 2167435 7315325 := bstep (se 3 (by rfl) ⟨1371623, by rfl⟩ : syracuseStep 7315325 = 2743247) B2743247
theorem B4876883 : Blo 2167435 4876883 := bstep (se 1 (by rfl) ⟨3657662, by rfl⟩ : syracuseStep 4876883 = 7315325) B7315325
theorem B3251255 : Blo 2167435 3251255 := bstep (se 1 (by rfl) ⟨2438441, by rfl⟩ : syracuseStep 3251255 = 4876883) B4876883
theorem B2167503 : Blo 2167435 2167503 := bstep (se 1 (by rfl) ⟨1625627, by rfl⟩ : syracuseStep 2167503 = 3251255) B3251255
theorem B3251261 : Blo 2167435 3251261 := bbase (se 3 (by rfl) ⟨609611, by rfl⟩ : syracuseStep 3251261 = 1219223) (by norm_num)
theorem B2167507 : Blo 2167435 2167507 := bstep (se 1 (by rfl) ⟨1625630, by rfl⟩ : syracuseStep 2167507 = 3251261) B3251261
theorem B4876901 : Blo 2167435 4876901 := bbase (se 4 (by rfl) ⟨457209, by rfl⟩ : syracuseStep 4876901 = 914419) (by norm_num)
theorem B3251267 : Blo 2167435 3251267 := bstep (se 1 (by rfl) ⟨2438450, by rfl⟩ : syracuseStep 3251267 = 4876901) B4876901
theorem B2167511 : Blo 2167435 2167511 := bstep (se 1 (by rfl) ⟨1625633, by rfl⟩ : syracuseStep 2167511 = 3251267) B3251267
theorem B5486525 : Blo 2167435 5486525 := bbase (se 3 (by rfl) ⟨1028723, by rfl⟩ : syracuseStep 5486525 = 2057447) (by norm_num)
theorem B3657683 : Blo 2167435 3657683 := bstep (se 1 (by rfl) ⟨2743262, by rfl⟩ : syracuseStep 3657683 = 5486525) B5486525
theorem B2438455 : Blo 2167435 2438455 := bstep (se 1 (by rfl) ⟨1828841, by rfl⟩ : syracuseStep 2438455 = 3657683) B3657683
theorem B3251273 : Blo 2167435 3251273 := bstep (se 2 (by rfl) ⟨1219227, by rfl⟩ : syracuseStep 3251273 = 2438455) B2438455
theorem B2167515 : Blo 2167435 2167515 := bstep (se 1 (by rfl) ⟨1625636, by rfl⟩ : syracuseStep 2167515 = 3251273) B3251273
theorem B4114901 : Blo 2167435 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B10973069 : Blo 2167435 10973069 := bstep (se 3 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 10973069 = 4114901) B4114901
theorem B7315379 : Blo 2167435 7315379 := bstep (se 1 (by rfl) ⟨5486534, by rfl⟩ : syracuseStep 7315379 = 10973069) B10973069
theorem B4876919 : Blo 2167435 4876919 := bstep (se 1 (by rfl) ⟨3657689, by rfl⟩ : syracuseStep 4876919 = 7315379) B7315379
theorem B3251279 : Blo 2167435 3251279 := bstep (se 1 (by rfl) ⟨2438459, by rfl⟩ : syracuseStep 3251279 = 4876919) B4876919
theorem B2167519 : Blo 2167435 2167519 := bstep (se 1 (by rfl) ⟨1625639, by rfl⟩ : syracuseStep 2167519 = 3251279) B3251279
theorem B3251285 : Blo 2167435 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B2167523 : Blo 2167435 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B3905957 : Blo 2167435 3905957 := bbase (se 4 (by rfl) ⟨366183, by rfl⟩ : syracuseStep 3905957 = 732367) (by norm_num)
theorem B2603971 : Blo 2167435 2603971 := bstep (se 1 (by rfl) ⟨1952978, by rfl⟩ : syracuseStep 2603971 = 3905957) B3905957
theorem B13887845 : Blo 2167435 13887845 := bstep (se 4 (by rfl) ⟨1301985, by rfl⟩ : syracuseStep 13887845 = 2603971) B2603971
theorem B9258563 : Blo 2167435 9258563 := bstep (se 1 (by rfl) ⟨6943922, by rfl⟩ : syracuseStep 9258563 = 13887845) B13887845
theorem B6172375 : Blo 2167435 6172375 := bstep (se 1 (by rfl) ⟨4629281, by rfl⟩ : syracuseStep 6172375 = 9258563) B9258563
theorem B8229833 : Blo 2167435 8229833 := bstep (se 2 (by rfl) ⟨3086187, by rfl⟩ : syracuseStep 8229833 = 6172375) B6172375
theorem B5486555 : Blo 2167435 5486555 := bstep (se 1 (by rfl) ⟨4114916, by rfl⟩ : syracuseStep 5486555 = 8229833) B8229833
theorem B3657703 : Blo 2167435 3657703 := bstep (se 1 (by rfl) ⟨2743277, by rfl⟩ : syracuseStep 3657703 = 5486555) B5486555
theorem B4876937 : Blo 2167435 4876937 := bstep (se 2 (by rfl) ⟨1828851, by rfl⟩ : syracuseStep 4876937 = 3657703) B3657703
theorem B3251291 : Blo 2167435 3251291 := bstep (se 1 (by rfl) ⟨2438468, by rfl⟩ : syracuseStep 3251291 = 4876937) B4876937
theorem B2167527 : Blo 2167435 2167527 := bstep (se 1 (by rfl) ⟨1625645, by rfl⟩ : syracuseStep 2167527 = 3251291) B3251291
theorem B2438473 : Blo 2167435 2438473 := bbase (se 2 (by rfl) ⟨914427, by rfl⟩ : syracuseStep 2438473 = 1828855) (by norm_num)
theorem B3251297 : Blo 2167435 3251297 := bstep (se 2 (by rfl) ⟨1219236, by rfl⟩ : syracuseStep 3251297 = 2438473) B2438473
theorem B2167531 : Blo 2167435 2167531 := bstep (se 1 (by rfl) ⟨1625648, by rfl⟩ : syracuseStep 2167531 = 3251297) B3251297
theorem B31247765 : Blo 2167435 31247765 := bbase (se 6 (by rfl) ⟨732369, by rfl⟩ : syracuseStep 31247765 = 1464739) (by norm_num)
theorem B20831843 : Blo 2167435 20831843 := bstep (se 1 (by rfl) ⟨15623882, by rfl⟩ : syracuseStep 20831843 = 31247765) B31247765
theorem B13887895 : Blo 2167435 13887895 := bstep (se 1 (by rfl) ⟨10415921, by rfl⟩ : syracuseStep 13887895 = 20831843) B20831843
theorem B18517193 : Blo 2167435 18517193 := bstep (se 2 (by rfl) ⟨6943947, by rfl⟩ : syracuseStep 18517193 = 13887895) B13887895
theorem B12344795 : Blo 2167435 12344795 := bstep (se 1 (by rfl) ⟨9258596, by rfl⟩ : syracuseStep 12344795 = 18517193) B18517193
theorem B8229863 : Blo 2167435 8229863 := bstep (se 1 (by rfl) ⟨6172397, by rfl⟩ : syracuseStep 8229863 = 12344795) B12344795
theorem B5486575 : Blo 2167435 5486575 := bstep (se 1 (by rfl) ⟨4114931, by rfl⟩ : syracuseStep 5486575 = 8229863) B8229863
theorem B7315433 : Blo 2167435 7315433 := bstep (se 2 (by rfl) ⟨2743287, by rfl⟩ : syracuseStep 7315433 = 5486575) B5486575
theorem B4876955 : Blo 2167435 4876955 := bstep (se 1 (by rfl) ⟨3657716, by rfl⟩ : syracuseStep 4876955 = 7315433) B7315433
theorem B3251303 : Blo 2167435 3251303 := bstep (se 1 (by rfl) ⟨2438477, by rfl⟩ : syracuseStep 3251303 = 4876955) B4876955
theorem B2167535 : Blo 2167435 2167535 := bstep (se 1 (by rfl) ⟨1625651, by rfl⟩ : syracuseStep 2167535 = 3251303) B3251303
theorem B3251309 : Blo 2167435 3251309 := bbase (se 3 (by rfl) ⟨609620, by rfl⟩ : syracuseStep 3251309 = 1219241) (by norm_num)
theorem B2167539 : Blo 2167435 2167539 := bstep (se 1 (by rfl) ⟨1625654, by rfl⟩ : syracuseStep 2167539 = 3251309) B3251309
theorem B4876973 : Blo 2167435 4876973 := bbase (se 3 (by rfl) ⟨914432, by rfl⟩ : syracuseStep 4876973 = 1828865) (by norm_num)
theorem B3251315 : Blo 2167435 3251315 := bstep (se 1 (by rfl) ⟨2438486, by rfl⟩ : syracuseStep 3251315 = 4876973) B4876973
theorem B2167543 : Blo 2167435 2167543 := bstep (se 1 (by rfl) ⟨1625657, by rfl⟩ : syracuseStep 2167543 = 3251315) B3251315
theorem B4629325 : Blo 2167435 4629325 := bbase (se 3 (by rfl) ⟨867998, by rfl⟩ : syracuseStep 4629325 = 1735997) (by norm_num)
theorem B6172433 : Blo 2167435 6172433 := bstep (se 2 (by rfl) ⟨2314662, by rfl⟩ : syracuseStep 6172433 = 4629325) B4629325
theorem B4114955 : Blo 2167435 4114955 := bstep (se 1 (by rfl) ⟨3086216, by rfl⟩ : syracuseStep 4114955 = 6172433) B6172433
theorem B2743303 : Blo 2167435 2743303 := bstep (se 1 (by rfl) ⟨2057477, by rfl⟩ : syracuseStep 2743303 = 4114955) B4114955
theorem B3657737 : Blo 2167435 3657737 := bstep (se 2 (by rfl) ⟨1371651, by rfl⟩ : syracuseStep 3657737 = 2743303) B2743303
theorem B2438491 : Blo 2167435 2438491 := bstep (se 1 (by rfl) ⟨1828868, by rfl⟩ : syracuseStep 2438491 = 3657737) B3657737
theorem B3251321 : Blo 2167435 3251321 := bstep (se 2 (by rfl) ⟨1219245, by rfl⟩ : syracuseStep 3251321 = 2438491) B2438491
theorem B2167547 : Blo 2167435 2167547 := bstep (se 1 (by rfl) ⟨1625660, by rfl⟩ : syracuseStep 2167547 = 3251321) B3251321
theorem B4013309 : Blo 2167435 4013309 := bbase (se 3 (by rfl) ⟨752495, by rfl⟩ : syracuseStep 4013309 = 1504991) (by norm_num)
theorem B2675539 : Blo 2167435 2675539 := bstep (se 1 (by rfl) ⟨2006654, by rfl⟩ : syracuseStep 2675539 = 4013309) B4013309
theorem B3567385 : Blo 2167435 3567385 := bstep (se 2 (by rfl) ⟨1337769, by rfl⟩ : syracuseStep 3567385 = 2675539) B2675539
theorem B4756513 : Blo 2167435 4756513 := bstep (se 2 (by rfl) ⟨1783692, by rfl⟩ : syracuseStep 4756513 = 3567385) B3567385
theorem B101472277 : Blo 2167435 101472277 := bstep (se 6 (by rfl) ⟨2378256, by rfl⟩ : syracuseStep 101472277 = 4756513) B4756513
theorem B135296369 : Blo 2167435 135296369 := bstep (se 2 (by rfl) ⟨50736138, by rfl⟩ : syracuseStep 135296369 = 101472277) B101472277
theorem B90197579 : Blo 2167435 90197579 := bstep (se 1 (by rfl) ⟨67648184, by rfl⟩ : syracuseStep 90197579 = 135296369) B135296369
theorem B60131719 : Blo 2167435 60131719 := bstep (se 1 (by rfl) ⟨45098789, by rfl⟩ : syracuseStep 60131719 = 90197579) B90197579
theorem B80175625 : Blo 2167435 80175625 := bstep (se 2 (by rfl) ⟨30065859, by rfl⟩ : syracuseStep 80175625 = 60131719) B60131719
theorem B427603333 : Blo 2167435 427603333 := bstep (se 4 (by rfl) ⟨40087812, by rfl⟩ : syracuseStep 427603333 = 80175625) B80175625
theorem B570137777 : Blo 2167435 570137777 := bstep (se 2 (by rfl) ⟨213801666, by rfl⟩ : syracuseStep 570137777 = 427603333) B427603333
theorem B380091851 : Blo 2167435 380091851 := bstep (se 1 (by rfl) ⟨285068888, by rfl⟩ : syracuseStep 380091851 = 570137777) B570137777
theorem B253394567 : Blo 2167435 253394567 := bstep (se 1 (by rfl) ⟨190045925, by rfl⟩ : syracuseStep 253394567 = 380091851) B380091851
theorem B168929711 : Blo 2167435 168929711 := bstep (se 1 (by rfl) ⟨126697283, by rfl⟩ : syracuseStep 168929711 = 253394567) B253394567
theorem B112619807 : Blo 2167435 112619807 := bstep (se 1 (by rfl) ⟨84464855, by rfl⟩ : syracuseStep 112619807 = 168929711) B168929711
theorem B75079871 : Blo 2167435 75079871 := bstep (se 1 (by rfl) ⟨56309903, by rfl⟩ : syracuseStep 75079871 = 112619807) B112619807
theorem B50053247 : Blo 2167435 50053247 := bstep (se 1 (by rfl) ⟨37539935, by rfl⟩ : syracuseStep 50053247 = 75079871) B75079871
theorem B33368831 : Blo 2167435 33368831 := bstep (se 1 (by rfl) ⟨25026623, by rfl⟩ : syracuseStep 33368831 = 50053247) B50053247
theorem B22245887 : Blo 2167435 22245887 := bstep (se 1 (by rfl) ⟨16684415, by rfl⟩ : syracuseStep 22245887 = 33368831) B33368831
theorem B59322365 : Blo 2167435 59322365 := bstep (se 3 (by rfl) ⟨11122943, by rfl⟩ : syracuseStep 59322365 = 22245887) B22245887
theorem B39548243 : Blo 2167435 39548243 := bstep (se 1 (by rfl) ⟨29661182, by rfl⟩ : syracuseStep 39548243 = 59322365) B59322365
theorem B26365495 : Blo 2167435 26365495 := bstep (se 1 (by rfl) ⟨19774121, by rfl⟩ : syracuseStep 26365495 = 39548243) B39548243
theorem B35153993 : Blo 2167435 35153993 := bstep (se 2 (by rfl) ⟨13182747, by rfl⟩ : syracuseStep 35153993 = 26365495) B26365495
theorem B23435995 : Blo 2167435 23435995 := bstep (se 1 (by rfl) ⟨17576996, by rfl⟩ : syracuseStep 23435995 = 35153993) B35153993
theorem B31247993 : Blo 2167435 31247993 := bstep (se 2 (by rfl) ⟨11717997, by rfl⟩ : syracuseStep 31247993 = 23435995) B23435995
theorem B20831995 : Blo 2167435 20831995 := bstep (se 1 (by rfl) ⟨15623996, by rfl⟩ : syracuseStep 20831995 = 31247993) B31247993
theorem B27775993 : Blo 2167435 27775993 := bstep (se 2 (by rfl) ⟨10415997, by rfl⟩ : syracuseStep 27775993 = 20831995) B20831995
theorem B37034657 : Blo 2167435 37034657 := bstep (se 2 (by rfl) ⟨13887996, by rfl⟩ : syracuseStep 37034657 = 27775993) B27775993
theorem B24689771 : Blo 2167435 24689771 := bstep (se 1 (by rfl) ⟨18517328, by rfl⟩ : syracuseStep 24689771 = 37034657) B37034657
theorem B16459847 : Blo 2167435 16459847 := bstep (se 1 (by rfl) ⟨12344885, by rfl⟩ : syracuseStep 16459847 = 24689771) B24689771
theorem B10973231 : Blo 2167435 10973231 := bstep (se 1 (by rfl) ⟨8229923, by rfl⟩ : syracuseStep 10973231 = 16459847) B16459847
theorem B7315487 : Blo 2167435 7315487 := bstep (se 1 (by rfl) ⟨5486615, by rfl⟩ : syracuseStep 7315487 = 10973231) B10973231
theorem B4876991 : Blo 2167435 4876991 := bstep (se 1 (by rfl) ⟨3657743, by rfl⟩ : syracuseStep 4876991 = 7315487) B7315487
theorem B3251327 : Blo 2167435 3251327 := bstep (se 1 (by rfl) ⟨2438495, by rfl⟩ : syracuseStep 3251327 = 4876991) B4876991
theorem B2167551 : Blo 2167435 2167551 := bstep (se 1 (by rfl) ⟨1625663, by rfl⟩ : syracuseStep 2167551 = 3251327) B3251327
theorem B3251333 : Blo 2167435 3251333 := bbase (se 4 (by rfl) ⟨304812, by rfl⟩ : syracuseStep 3251333 = 609625) (by norm_num)
theorem B2167555 : Blo 2167435 2167555 := bstep (se 1 (by rfl) ⟨1625666, by rfl⟩ : syracuseStep 2167555 = 3251333) B3251333
theorem B3657757 : Blo 2167435 3657757 := bbase (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) (by norm_num)
theorem B4877009 : Blo 2167435 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B3251339 : Blo 2167435 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B2167559 : Blo 2167435 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B2438509 : Blo 2167435 2438509 := bbase (se 3 (by rfl) ⟨457220, by rfl⟩ : syracuseStep 2438509 = 914441) (by norm_num)
theorem B3251345 : Blo 2167435 3251345 := bstep (se 2 (by rfl) ⟨1219254, by rfl⟩ : syracuseStep 3251345 = 2438509) B2438509
theorem B2167563 : Blo 2167435 2167563 := bstep (se 1 (by rfl) ⟨1625672, by rfl⟩ : syracuseStep 2167563 = 3251345) B3251345
theorem B7315541 : Blo 2167435 7315541 := bbase (se 8 (by rfl) ⟨42864, by rfl⟩ : syracuseStep 7315541 = 85729) (by norm_num)
theorem B4877027 : Blo 2167435 4877027 := bstep (se 1 (by rfl) ⟨3657770, by rfl⟩ : syracuseStep 4877027 = 7315541) B7315541
theorem B3251351 : Blo 2167435 3251351 := bstep (se 1 (by rfl) ⟨2438513, by rfl⟩ : syracuseStep 3251351 = 4877027) B4877027
theorem B2167567 : Blo 2167435 2167567 := bstep (se 1 (by rfl) ⟨1625675, by rfl⟩ : syracuseStep 2167567 = 3251351) B3251351
theorem B3251357 : Blo 2167435 3251357 := bbase (se 3 (by rfl) ⟨609629, by rfl⟩ : syracuseStep 3251357 = 1219259) (by norm_num)
theorem B2167571 : Blo 2167435 2167571 := bstep (se 1 (by rfl) ⟨1625678, by rfl⟩ : syracuseStep 2167571 = 3251357) B3251357
theorem B4877045 : Blo 2167435 4877045 := bbase (se 5 (by rfl) ⟨228611, by rfl⟩ : syracuseStep 4877045 = 457223) (by norm_num)
theorem B3251363 : Blo 2167435 3251363 := bstep (se 1 (by rfl) ⟨2438522, by rfl⟩ : syracuseStep 3251363 = 4877045) B4877045
theorem B2167575 : Blo 2167435 2167575 := bstep (se 1 (by rfl) ⟨1625681, by rfl⟩ : syracuseStep 2167575 = 3251363) B3251363
theorem B7812101 : Blo 2167435 7812101 := bbase (se 4 (by rfl) ⟨732384, by rfl⟩ : syracuseStep 7812101 = 1464769) (by norm_num)
theorem B5208067 : Blo 2167435 5208067 := bstep (se 1 (by rfl) ⟨3906050, by rfl⟩ : syracuseStep 5208067 = 7812101) B7812101
theorem B27776357 : Blo 2167435 27776357 := bstep (se 4 (by rfl) ⟨2604033, by rfl⟩ : syracuseStep 27776357 = 5208067) B5208067
theorem B18517571 : Blo 2167435 18517571 := bstep (se 1 (by rfl) ⟨13888178, by rfl⟩ : syracuseStep 18517571 = 27776357) B27776357
theorem B12345047 : Blo 2167435 12345047 := bstep (se 1 (by rfl) ⟨9258785, by rfl⟩ : syracuseStep 12345047 = 18517571) B18517571
theorem B8230031 : Blo 2167435 8230031 := bstep (se 1 (by rfl) ⟨6172523, by rfl⟩ : syracuseStep 8230031 = 12345047) B12345047
theorem B5486687 : Blo 2167435 5486687 := bstep (se 1 (by rfl) ⟨4115015, by rfl⟩ : syracuseStep 5486687 = 8230031) B8230031
theorem B3657791 : Blo 2167435 3657791 := bstep (se 1 (by rfl) ⟨2743343, by rfl⟩ : syracuseStep 3657791 = 5486687) B5486687
theorem B2438527 : Blo 2167435 2438527 := bstep (se 1 (by rfl) ⟨1828895, by rfl⟩ : syracuseStep 2438527 = 3657791) B3657791
theorem B3251369 : Blo 2167435 3251369 := bstep (se 2 (by rfl) ⟨1219263, by rfl⟩ : syracuseStep 3251369 = 2438527) B2438527
theorem B2167579 : Blo 2167435 2167579 := bstep (se 1 (by rfl) ⟨1625684, by rfl⟩ : syracuseStep 2167579 = 3251369) B3251369
theorem B5208077 : Blo 2167435 5208077 := bbase (se 3 (by rfl) ⟨976514, by rfl⟩ : syracuseStep 5208077 = 1953029) (by norm_num)
theorem B3472051 : Blo 2167435 3472051 := bstep (se 1 (by rfl) ⟨2604038, by rfl⟩ : syracuseStep 3472051 = 5208077) B5208077
theorem B4629401 : Blo 2167435 4629401 := bstep (se 2 (by rfl) ⟨1736025, by rfl⟩ : syracuseStep 4629401 = 3472051) B3472051
theorem B3086267 : Blo 2167435 3086267 := bstep (se 1 (by rfl) ⟨2314700, by rfl⟩ : syracuseStep 3086267 = 4629401) B4629401
theorem B8230045 : Blo 2167435 8230045 := bstep (se 3 (by rfl) ⟨1543133, by rfl⟩ : syracuseStep 8230045 = 3086267) B3086267
theorem B10973393 : Blo 2167435 10973393 := bstep (se 2 (by rfl) ⟨4115022, by rfl⟩ : syracuseStep 10973393 = 8230045) B8230045
theorem B7315595 : Blo 2167435 7315595 := bstep (se 1 (by rfl) ⟨5486696, by rfl⟩ : syracuseStep 7315595 = 10973393) B10973393
theorem B4877063 : Blo 2167435 4877063 := bstep (se 1 (by rfl) ⟨3657797, by rfl⟩ : syracuseStep 4877063 = 7315595) B7315595
theorem B3251375 : Blo 2167435 3251375 := bstep (se 1 (by rfl) ⟨2438531, by rfl⟩ : syracuseStep 3251375 = 4877063) B4877063
theorem B2167583 : Blo 2167435 2167583 := bstep (se 1 (by rfl) ⟨1625687, by rfl⟩ : syracuseStep 2167583 = 3251375) B3251375
theorem B3251381 : Blo 2167435 3251381 := bbase (se 5 (by rfl) ⟨152408, by rfl⟩ : syracuseStep 3251381 = 304817) (by norm_num)
theorem B2167587 : Blo 2167435 2167587 := bstep (se 1 (by rfl) ⟨1625690, by rfl⟩ : syracuseStep 2167587 = 3251381) B3251381
theorem B5486717 : Blo 2167435 5486717 := bbase (se 3 (by rfl) ⟨1028759, by rfl⟩ : syracuseStep 5486717 = 2057519) (by norm_num)
theorem B3657811 : Blo 2167435 3657811 := bstep (se 1 (by rfl) ⟨2743358, by rfl⟩ : syracuseStep 3657811 = 5486717) B5486717
theorem B4877081 : Blo 2167435 4877081 := bstep (se 2 (by rfl) ⟨1828905, by rfl⟩ : syracuseStep 4877081 = 3657811) B3657811
theorem B3251387 : Blo 2167435 3251387 := bstep (se 1 (by rfl) ⟨2438540, by rfl⟩ : syracuseStep 3251387 = 4877081) B4877081
theorem B2167591 : Blo 2167435 2167591 := bstep (se 1 (by rfl) ⟨1625693, by rfl⟩ : syracuseStep 2167591 = 3251387) B3251387
theorem B2438545 : Blo 2167435 2438545 := bbase (se 2 (by rfl) ⟨914454, by rfl⟩ : syracuseStep 2438545 = 1828909) (by norm_num)
theorem B3251393 : Blo 2167435 3251393 := bstep (se 2 (by rfl) ⟨1219272, by rfl⟩ : syracuseStep 3251393 = 2438545) B2438545
theorem B2167595 : Blo 2167435 2167595 := bstep (se 1 (by rfl) ⟨1625696, by rfl⟩ : syracuseStep 2167595 = 3251393) B3251393
theorem B4115053 : Blo 2167435 4115053 := bbase (se 3 (by rfl) ⟨771572, by rfl⟩ : syracuseStep 4115053 = 1543145) (by norm_num)
theorem B5486737 : Blo 2167435 5486737 := bstep (se 2 (by rfl) ⟨2057526, by rfl⟩ : syracuseStep 5486737 = 4115053) B4115053
theorem B7315649 : Blo 2167435 7315649 := bstep (se 2 (by rfl) ⟨2743368, by rfl⟩ : syracuseStep 7315649 = 5486737) B5486737
theorem B4877099 : Blo 2167435 4877099 := bstep (se 1 (by rfl) ⟨3657824, by rfl⟩ : syracuseStep 4877099 = 7315649) B7315649
theorem B3251399 : Blo 2167435 3251399 := bstep (se 1 (by rfl) ⟨2438549, by rfl⟩ : syracuseStep 3251399 = 4877099) B4877099
theorem B2167599 : Blo 2167435 2167599 := bstep (se 1 (by rfl) ⟨1625699, by rfl⟩ : syracuseStep 2167599 = 3251399) B3251399
theorem B3251405 : Blo 2167435 3251405 := bbase (se 3 (by rfl) ⟨609638, by rfl⟩ : syracuseStep 3251405 = 1219277) (by norm_num)
theorem B2167603 : Blo 2167435 2167603 := bstep (se 1 (by rfl) ⟨1625702, by rfl⟩ : syracuseStep 2167603 = 3251405) B3251405
theorem B4877117 : Blo 2167435 4877117 := bbase (se 3 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 4877117 = 1828919) (by norm_num)
theorem B3251411 : Blo 2167435 3251411 := bstep (se 1 (by rfl) ⟨2438558, by rfl⟩ : syracuseStep 3251411 = 4877117) B4877117
theorem B2167607 : Blo 2167435 2167607 := bstep (se 1 (by rfl) ⟨1625705, by rfl⟩ : syracuseStep 2167607 = 3251411) B3251411
theorem B3657845 : Blo 2167435 3657845 := bbase (se 5 (by rfl) ⟨171461, by rfl⟩ : syracuseStep 3657845 = 342923) (by norm_num)
theorem B2438563 : Blo 2167435 2438563 := bstep (se 1 (by rfl) ⟨1828922, by rfl⟩ : syracuseStep 2438563 = 3657845) B3657845
theorem B3251417 : Blo 2167435 3251417 := bstep (se 2 (by rfl) ⟨1219281, by rfl⟩ : syracuseStep 3251417 = 2438563) B2438563
theorem B2167611 : Blo 2167435 2167611 := bstep (se 1 (by rfl) ⟨1625708, by rfl⟩ : syracuseStep 2167611 = 3251417) B3251417
theorem B4629469 : Blo 2167435 4629469 := bbase (se 3 (by rfl) ⟨868025, by rfl⟩ : syracuseStep 4629469 = 1736051) (by norm_num)
theorem B6172625 : Blo 2167435 6172625 := bstep (se 2 (by rfl) ⟨2314734, by rfl⟩ : syracuseStep 6172625 = 4629469) B4629469
theorem B16460333 : Blo 2167435 16460333 := bstep (se 3 (by rfl) ⟨3086312, by rfl⟩ : syracuseStep 16460333 = 6172625) B6172625
theorem B10973555 : Blo 2167435 10973555 := bstep (se 1 (by rfl) ⟨8230166, by rfl⟩ : syracuseStep 10973555 = 16460333) B16460333
theorem B7315703 : Blo 2167435 7315703 := bstep (se 1 (by rfl) ⟨5486777, by rfl⟩ : syracuseStep 7315703 = 10973555) B10973555
theorem B4877135 : Blo 2167435 4877135 := bstep (se 1 (by rfl) ⟨3657851, by rfl⟩ : syracuseStep 4877135 = 7315703) B7315703
theorem B3251423 : Blo 2167435 3251423 := bstep (se 1 (by rfl) ⟨2438567, by rfl⟩ : syracuseStep 3251423 = 4877135) B4877135
theorem B2167615 : Blo 2167435 2167615 := bstep (se 1 (by rfl) ⟨1625711, by rfl⟩ : syracuseStep 2167615 = 3251423) B3251423
theorem B3251429 : Blo 2167435 3251429 := bbase (se 4 (by rfl) ⟨304821, by rfl⟩ : syracuseStep 3251429 = 609643) (by norm_num)
theorem B2167619 : Blo 2167435 2167619 := bstep (se 1 (by rfl) ⟨1625714, by rfl⟩ : syracuseStep 2167619 = 3251429) B3251429
theorem B9385301 : Blo 2167435 9385301 := bbase (se 13 (by rfl) ⟨1718, by rfl⟩ : syracuseStep 9385301 = 3437) (by norm_num)
theorem B6256867 : Blo 2167435 6256867 := bstep (se 1 (by rfl) ⟨4692650, by rfl⟩ : syracuseStep 6256867 = 9385301) B9385301
theorem B8342489 : Blo 2167435 8342489 := bstep (se 2 (by rfl) ⟨3128433, by rfl⟩ : syracuseStep 8342489 = 6256867) B6256867
theorem B5561659 : Blo 2167435 5561659 := bstep (se 1 (by rfl) ⟨4171244, by rfl⟩ : syracuseStep 5561659 = 8342489) B8342489
theorem B7415545 : Blo 2167435 7415545 := bstep (se 2 (by rfl) ⟨2780829, by rfl⟩ : syracuseStep 7415545 = 5561659) B5561659
theorem B9887393 : Blo 2167435 9887393 := bstep (se 2 (by rfl) ⟨3707772, by rfl⟩ : syracuseStep 9887393 = 7415545) B7415545
theorem B26366381 : Blo 2167435 26366381 := bstep (se 3 (by rfl) ⟨4943696, by rfl⟩ : syracuseStep 26366381 = 9887393) B9887393
theorem B17577587 : Blo 2167435 17577587 := bstep (se 1 (by rfl) ⟨13183190, by rfl⟩ : syracuseStep 17577587 = 26366381) B26366381
theorem B11718391 : Blo 2167435 11718391 := bstep (se 1 (by rfl) ⟨8788793, by rfl⟩ : syracuseStep 11718391 = 17577587) B17577587
theorem B15624521 : Blo 2167435 15624521 := bstep (se 2 (by rfl) ⟨5859195, by rfl⟩ : syracuseStep 15624521 = 11718391) B11718391
theorem B10416347 : Blo 2167435 10416347 := bstep (se 1 (by rfl) ⟨7812260, by rfl⟩ : syracuseStep 10416347 = 15624521) B15624521
theorem B6944231 : Blo 2167435 6944231 := bstep (se 1 (by rfl) ⟨5208173, by rfl⟩ : syracuseStep 6944231 = 10416347) B10416347
theorem B4629487 : Blo 2167435 4629487 := bstep (se 1 (by rfl) ⟨3472115, by rfl⟩ : syracuseStep 4629487 = 6944231) B6944231
theorem B6172649 : Blo 2167435 6172649 := bstep (se 2 (by rfl) ⟨2314743, by rfl⟩ : syracuseStep 6172649 = 4629487) B4629487
theorem B4115099 : Blo 2167435 4115099 := bstep (se 1 (by rfl) ⟨3086324, by rfl⟩ : syracuseStep 4115099 = 6172649) B6172649
theorem B2743399 : Blo 2167435 2743399 := bstep (se 1 (by rfl) ⟨2057549, by rfl⟩ : syracuseStep 2743399 = 4115099) B4115099
theorem B3657865 : Blo 2167435 3657865 := bstep (se 2 (by rfl) ⟨1371699, by rfl⟩ : syracuseStep 3657865 = 2743399) B2743399
theorem B4877153 : Blo 2167435 4877153 := bstep (se 2 (by rfl) ⟨1828932, by rfl⟩ : syracuseStep 4877153 = 3657865) B3657865
theorem B3251435 : Blo 2167435 3251435 := bstep (se 1 (by rfl) ⟨2438576, by rfl⟩ : syracuseStep 3251435 = 4877153) B4877153
theorem B2167623 : Blo 2167435 2167623 := bstep (se 1 (by rfl) ⟨1625717, by rfl⟩ : syracuseStep 2167623 = 3251435) B3251435
theorem B2438581 : Blo 2167435 2438581 := bbase (se 5 (by rfl) ⟨114308, by rfl⟩ : syracuseStep 2438581 = 228617) (by norm_num)
theorem B3251441 : Blo 2167435 3251441 := bstep (se 2 (by rfl) ⟨1219290, by rfl⟩ : syracuseStep 3251441 = 2438581) B2438581
theorem B2167627 : Blo 2167435 2167627 := bstep (se 1 (by rfl) ⟨1625720, by rfl⟩ : syracuseStep 2167627 = 3251441) B3251441
theorem B2743409 : Blo 2167435 2743409 := bbase (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) (by norm_num)
theorem B7315757 : Blo 2167435 7315757 := bstep (se 3 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 7315757 = 2743409) B2743409
theorem B4877171 : Blo 2167435 4877171 := bstep (se 1 (by rfl) ⟨3657878, by rfl⟩ : syracuseStep 4877171 = 7315757) B7315757
theorem B3251447 : Blo 2167435 3251447 := bstep (se 1 (by rfl) ⟨2438585, by rfl⟩ : syracuseStep 3251447 = 4877171) B4877171
theorem B2167631 : Blo 2167435 2167631 := bstep (se 1 (by rfl) ⟨1625723, by rfl⟩ : syracuseStep 2167631 = 3251447) B3251447
theorem B3251453 : Blo 2167435 3251453 := bbase (se 3 (by rfl) ⟨609647, by rfl⟩ : syracuseStep 3251453 = 1219295) (by norm_num)
theorem B2167635 : Blo 2167435 2167635 := bstep (se 1 (by rfl) ⟨1625726, by rfl⟩ : syracuseStep 2167635 = 3251453) B3251453
theorem B4877189 : Blo 2167435 4877189 := bbase (se 4 (by rfl) ⟨457236, by rfl⟩ : syracuseStep 4877189 = 914473) (by norm_num)
theorem B3251459 : Blo 2167435 3251459 := bstep (se 1 (by rfl) ⟨2438594, by rfl⟩ : syracuseStep 3251459 = 4877189) B4877189
theorem B2167639 : Blo 2167435 2167639 := bstep (se 1 (by rfl) ⟨1625729, by rfl⟩ : syracuseStep 2167639 = 3251459) B3251459
theorem B2314765 : Blo 2167435 2314765 := bbase (se 3 (by rfl) ⟨434018, by rfl⟩ : syracuseStep 2314765 = 868037) (by norm_num)
theorem B3086353 : Blo 2167435 3086353 := bstep (se 2 (by rfl) ⟨1157382, by rfl⟩ : syracuseStep 3086353 = 2314765) B2314765
theorem B4115137 : Blo 2167435 4115137 := bstep (se 2 (by rfl) ⟨1543176, by rfl⟩ : syracuseStep 4115137 = 3086353) B3086353
theorem B5486849 : Blo 2167435 5486849 := bstep (se 2 (by rfl) ⟨2057568, by rfl⟩ : syracuseStep 5486849 = 4115137) B4115137
theorem B3657899 : Blo 2167435 3657899 := bstep (se 1 (by rfl) ⟨2743424, by rfl⟩ : syracuseStep 3657899 = 5486849) B5486849
theorem B2438599 : Blo 2167435 2438599 := bstep (se 1 (by rfl) ⟨1828949, by rfl⟩ : syracuseStep 2438599 = 3657899) B3657899
theorem B3251465 : Blo 2167435 3251465 := bstep (se 2 (by rfl) ⟨1219299, by rfl⟩ : syracuseStep 3251465 = 2438599) B2438599
theorem B2167643 : Blo 2167435 2167643 := bstep (se 1 (by rfl) ⟨1625732, by rfl⟩ : syracuseStep 2167643 = 3251465) B3251465
theorem B10973717 : Blo 2167435 10973717 := bbase (se 6 (by rfl) ⟨257196, by rfl⟩ : syracuseStep 10973717 = 514393) (by norm_num)
theorem B7315811 : Blo 2167435 7315811 := bstep (se 1 (by rfl) ⟨5486858, by rfl⟩ : syracuseStep 7315811 = 10973717) B10973717
theorem B4877207 : Blo 2167435 4877207 := bstep (se 1 (by rfl) ⟨3657905, by rfl⟩ : syracuseStep 4877207 = 7315811) B7315811
theorem B3251471 : Blo 2167435 3251471 := bstep (se 1 (by rfl) ⟨2438603, by rfl⟩ : syracuseStep 3251471 = 4877207) B4877207
theorem B2167647 : Blo 2167435 2167647 := bstep (se 1 (by rfl) ⟨1625735, by rfl⟩ : syracuseStep 2167647 = 3251471) B3251471
theorem B3251477 : Blo 2167435 3251477 := bbase (se 6 (by rfl) ⟨76206, by rfl⟩ : syracuseStep 3251477 = 152413) (by norm_num)
theorem B2167651 : Blo 2167435 2167651 := bstep (se 1 (by rfl) ⟨1625738, by rfl⟩ : syracuseStep 2167651 = 3251477) B3251477
theorem B4394461 : Blo 2167435 4394461 := bbase (se 3 (by rfl) ⟨823961, by rfl⟩ : syracuseStep 4394461 = 1647923) (by norm_num)
theorem B5859281 : Blo 2167435 5859281 := bstep (se 2 (by rfl) ⟨2197230, by rfl⟩ : syracuseStep 5859281 = 4394461) B4394461
theorem B3906187 : Blo 2167435 3906187 := bstep (se 1 (by rfl) ⟨2929640, by rfl⟩ : syracuseStep 3906187 = 5859281) B5859281
theorem B20832997 : Blo 2167435 20832997 := bstep (se 4 (by rfl) ⟨1953093, by rfl⟩ : syracuseStep 20832997 = 3906187) B3906187
theorem B27777329 : Blo 2167435 27777329 := bstep (se 2 (by rfl) ⟨10416498, by rfl⟩ : syracuseStep 27777329 = 20832997) B20832997
theorem B18518219 : Blo 2167435 18518219 := bstep (se 1 (by rfl) ⟨13888664, by rfl⟩ : syracuseStep 18518219 = 27777329) B27777329
theorem B12345479 : Blo 2167435 12345479 := bstep (se 1 (by rfl) ⟨9259109, by rfl⟩ : syracuseStep 12345479 = 18518219) B18518219
theorem B8230319 : Blo 2167435 8230319 := bstep (se 1 (by rfl) ⟨6172739, by rfl⟩ : syracuseStep 8230319 = 12345479) B12345479
theorem B5486879 : Blo 2167435 5486879 := bstep (se 1 (by rfl) ⟨4115159, by rfl⟩ : syracuseStep 5486879 = 8230319) B8230319
theorem B3657919 : Blo 2167435 3657919 := bstep (se 1 (by rfl) ⟨2743439, by rfl⟩ : syracuseStep 3657919 = 5486879) B5486879
theorem B4877225 : Blo 2167435 4877225 := bstep (se 2 (by rfl) ⟨1828959, by rfl⟩ : syracuseStep 4877225 = 3657919) B3657919
theorem B3251483 : Blo 2167435 3251483 := bstep (se 1 (by rfl) ⟨2438612, by rfl⟩ : syracuseStep 3251483 = 4877225) B4877225
theorem B2167655 : Blo 2167435 2167655 := bstep (se 1 (by rfl) ⟨1625741, by rfl⟩ : syracuseStep 2167655 = 3251483) B3251483
theorem B2438617 : Blo 2167435 2438617 := bbase (se 2 (by rfl) ⟨914481, by rfl⟩ : syracuseStep 2438617 = 1828963) (by norm_num)
theorem B3251489 : Blo 2167435 3251489 := bstep (se 2 (by rfl) ⟨1219308, by rfl⟩ : syracuseStep 3251489 = 2438617) B2438617
theorem B2167659 : Blo 2167435 2167659 := bstep (se 1 (by rfl) ⟨1625744, by rfl⟩ : syracuseStep 2167659 = 3251489) B3251489
theorem B3086381 : Blo 2167435 3086381 := bbase (se 3 (by rfl) ⟨578696, by rfl⟩ : syracuseStep 3086381 = 1157393) (by norm_num)
theorem B8230349 : Blo 2167435 8230349 := bstep (se 3 (by rfl) ⟨1543190, by rfl⟩ : syracuseStep 8230349 = 3086381) B3086381
theorem B5486899 : Blo 2167435 5486899 := bstep (se 1 (by rfl) ⟨4115174, by rfl⟩ : syracuseStep 5486899 = 8230349) B8230349
theorem B7315865 : Blo 2167435 7315865 := bstep (se 2 (by rfl) ⟨2743449, by rfl⟩ : syracuseStep 7315865 = 5486899) B5486899
theorem B4877243 : Blo 2167435 4877243 := bstep (se 1 (by rfl) ⟨3657932, by rfl⟩ : syracuseStep 4877243 = 7315865) B7315865
theorem B3251495 : Blo 2167435 3251495 := bstep (se 1 (by rfl) ⟨2438621, by rfl⟩ : syracuseStep 3251495 = 4877243) B4877243
theorem B2167663 : Blo 2167435 2167663 := bstep (se 1 (by rfl) ⟨1625747, by rfl⟩ : syracuseStep 2167663 = 3251495) B3251495
theorem B3251501 : Blo 2167435 3251501 := bbase (se 3 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 3251501 = 1219313) (by norm_num)
theorem B2167667 : Blo 2167435 2167667 := bstep (se 1 (by rfl) ⟨1625750, by rfl⟩ : syracuseStep 2167667 = 3251501) B3251501
theorem B4877261 : Blo 2167435 4877261 := bbase (se 3 (by rfl) ⟨914486, by rfl⟩ : syracuseStep 4877261 = 1828973) (by norm_num)
theorem B3251507 : Blo 2167435 3251507 := bstep (se 1 (by rfl) ⟨2438630, by rfl⟩ : syracuseStep 3251507 = 4877261) B4877261
theorem B2167671 : Blo 2167435 2167671 := bstep (se 1 (by rfl) ⟨1625753, by rfl⟩ : syracuseStep 2167671 = 3251507) B3251507
theorem B2743465 : Blo 2167435 2743465 := bbase (se 2 (by rfl) ⟨1028799, by rfl⟩ : syracuseStep 2743465 = 2057599) (by norm_num)
theorem B3657953 : Blo 2167435 3657953 := bstep (se 2 (by rfl) ⟨1371732, by rfl⟩ : syracuseStep 3657953 = 2743465) B2743465
theorem B2438635 : Blo 2167435 2438635 := bstep (se 1 (by rfl) ⟨1828976, by rfl⟩ : syracuseStep 2438635 = 3657953) B3657953
theorem B3251513 : Blo 2167435 3251513 := bstep (se 2 (by rfl) ⟨1219317, by rfl⟩ : syracuseStep 3251513 = 2438635) B2438635
theorem B2167675 : Blo 2167435 2167675 := bstep (se 1 (by rfl) ⟨1625756, by rfl⟩ : syracuseStep 2167675 = 3251513) B3251513
theorem B10416613 : Blo 2167435 10416613 := bbase (se 4 (by rfl) ⟨976557, by rfl⟩ : syracuseStep 10416613 = 1953115) (by norm_num)
theorem B13888817 : Blo 2167435 13888817 := bstep (se 2 (by rfl) ⟨5208306, by rfl⟩ : syracuseStep 13888817 = 10416613) B10416613
theorem B9259211 : Blo 2167435 9259211 := bstep (se 1 (by rfl) ⟨6944408, by rfl⟩ : syracuseStep 9259211 = 13888817) B13888817
theorem B24691229 : Blo 2167435 24691229 := bstep (se 3 (by rfl) ⟨4629605, by rfl⟩ : syracuseStep 24691229 = 9259211) B9259211
theorem B16460819 : Blo 2167435 16460819 := bstep (se 1 (by rfl) ⟨12345614, by rfl⟩ : syracuseStep 16460819 = 24691229) B24691229
theorem B10973879 : Blo 2167435 10973879 := bstep (se 1 (by rfl) ⟨8230409, by rfl⟩ : syracuseStep 10973879 = 16460819) B16460819
theorem B7315919 : Blo 2167435 7315919 := bstep (se 1 (by rfl) ⟨5486939, by rfl⟩ : syracuseStep 7315919 = 10973879) B10973879
theorem B4877279 : Blo 2167435 4877279 := bstep (se 1 (by rfl) ⟨3657959, by rfl⟩ : syracuseStep 4877279 = 7315919) B7315919
theorem B3251519 : Blo 2167435 3251519 := bstep (se 1 (by rfl) ⟨2438639, by rfl⟩ : syracuseStep 3251519 = 4877279) B4877279
theorem B2167679 : Blo 2167435 2167679 := bstep (se 1 (by rfl) ⟨1625759, by rfl⟩ : syracuseStep 2167679 = 3251519) B3251519
theorem B3251525 : Blo 2167435 3251525 := bbase (se 4 (by rfl) ⟨304830, by rfl⟩ : syracuseStep 3251525 = 609661) (by norm_num)
theorem B2167683 : Blo 2167435 2167683 := bstep (se 1 (by rfl) ⟨1625762, by rfl⟩ : syracuseStep 2167683 = 3251525) B3251525
theorem B3657973 : Blo 2167435 3657973 := bbase (se 5 (by rfl) ⟨171467, by rfl⟩ : syracuseStep 3657973 = 342935) (by norm_num)
theorem B4877297 : Blo 2167435 4877297 := bstep (se 2 (by rfl) ⟨1828986, by rfl⟩ : syracuseStep 4877297 = 3657973) B3657973
theorem B3251531 : Blo 2167435 3251531 := bstep (se 1 (by rfl) ⟨2438648, by rfl⟩ : syracuseStep 3251531 = 4877297) B4877297
theorem B2167687 : Blo 2167435 2167687 := bstep (se 1 (by rfl) ⟨1625765, by rfl⟩ : syracuseStep 2167687 = 3251531) B3251531
theorem B2438653 : Blo 2167435 2438653 := bbase (se 3 (by rfl) ⟨457247, by rfl⟩ : syracuseStep 2438653 = 914495) (by norm_num)
theorem B3251537 : Blo 2167435 3251537 := bstep (se 2 (by rfl) ⟨1219326, by rfl⟩ : syracuseStep 3251537 = 2438653) B2438653
theorem B2167691 : Blo 2167435 2167691 := bstep (se 1 (by rfl) ⟨1625768, by rfl⟩ : syracuseStep 2167691 = 3251537) B3251537
theorem B7315973 : Blo 2167435 7315973 := bbase (se 4 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 7315973 = 1371745) (by norm_num)
theorem B4877315 : Blo 2167435 4877315 := bstep (se 1 (by rfl) ⟨3657986, by rfl⟩ : syracuseStep 4877315 = 7315973) B7315973
theorem B3251543 : Blo 2167435 3251543 := bstep (se 1 (by rfl) ⟨2438657, by rfl⟩ : syracuseStep 3251543 = 4877315) B4877315
theorem B2167695 : Blo 2167435 2167695 := bstep (se 1 (by rfl) ⟨1625771, by rfl⟩ : syracuseStep 2167695 = 3251543) B3251543
theorem B3251549 : Blo 2167435 3251549 := bbase (se 3 (by rfl) ⟨609665, by rfl⟩ : syracuseStep 3251549 = 1219331) (by norm_num)
theorem B2167699 : Blo 2167435 2167699 := bstep (se 1 (by rfl) ⟨1625774, by rfl⟩ : syracuseStep 2167699 = 3251549) B3251549
theorem B4877333 : Blo 2167435 4877333 := bbase (se 6 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 4877333 = 228625) (by norm_num)
theorem B3251555 : Blo 2167435 3251555 := bstep (se 1 (by rfl) ⟨2438666, by rfl⟩ : syracuseStep 3251555 = 4877333) B4877333
theorem B2167703 : Blo 2167435 2167703 := bstep (se 1 (by rfl) ⟨1625777, by rfl⟩ : syracuseStep 2167703 = 3251555) B3251555
theorem B8230517 : Blo 2167435 8230517 := bbase (se 5 (by rfl) ⟨385805, by rfl⟩ : syracuseStep 8230517 = 771611) (by norm_num)
theorem B5487011 : Blo 2167435 5487011 := bstep (se 1 (by rfl) ⟨4115258, by rfl⟩ : syracuseStep 5487011 = 8230517) B8230517
theorem B3658007 : Blo 2167435 3658007 := bstep (se 1 (by rfl) ⟨2743505, by rfl⟩ : syracuseStep 3658007 = 5487011) B5487011
theorem B2438671 : Blo 2167435 2438671 := bstep (se 1 (by rfl) ⟨1829003, by rfl⟩ : syracuseStep 2438671 = 3658007) B3658007
theorem B3251561 : Blo 2167435 3251561 := bstep (se 2 (by rfl) ⟨1219335, by rfl⟩ : syracuseStep 3251561 = 2438671) B2438671
theorem B2167707 : Blo 2167435 2167707 := bstep (se 1 (by rfl) ⟨1625780, by rfl⟩ : syracuseStep 2167707 = 3251561) B3251561
theorem B2314837 : Blo 2167435 2314837 := bbase (se 8 (by rfl) ⟨13563, by rfl⟩ : syracuseStep 2314837 = 27127) (by norm_num)
theorem B12345797 : Blo 2167435 12345797 := bstep (se 4 (by rfl) ⟨1157418, by rfl⟩ : syracuseStep 12345797 = 2314837) B2314837
theorem B8230531 : Blo 2167435 8230531 := bstep (se 1 (by rfl) ⟨6172898, by rfl⟩ : syracuseStep 8230531 = 12345797) B12345797
theorem B10974041 : Blo 2167435 10974041 := bstep (se 2 (by rfl) ⟨4115265, by rfl⟩ : syracuseStep 10974041 = 8230531) B8230531
theorem B7316027 : Blo 2167435 7316027 := bstep (se 1 (by rfl) ⟨5487020, by rfl⟩ : syracuseStep 7316027 = 10974041) B10974041
theorem B4877351 : Blo 2167435 4877351 := bstep (se 1 (by rfl) ⟨3658013, by rfl⟩ : syracuseStep 4877351 = 7316027) B7316027
theorem B3251567 : Blo 2167435 3251567 := bstep (se 1 (by rfl) ⟨2438675, by rfl⟩ : syracuseStep 3251567 = 4877351) B4877351
theorem B2167711 : Blo 2167435 2167711 := bstep (se 1 (by rfl) ⟨1625783, by rfl⟩ : syracuseStep 2167711 = 3251567) B3251567
theorem B3251573 : Blo 2167435 3251573 := bbase (se 5 (by rfl) ⟨152417, by rfl⟩ : syracuseStep 3251573 = 304835) (by norm_num)
theorem B2167715 : Blo 2167435 2167715 := bstep (se 1 (by rfl) ⟨1625786, by rfl⟩ : syracuseStep 2167715 = 3251573) B3251573
theorem B3086461 : Blo 2167435 3086461 := bbase (se 3 (by rfl) ⟨578711, by rfl⟩ : syracuseStep 3086461 = 1157423) (by norm_num)
theorem B4115281 : Blo 2167435 4115281 := bstep (se 2 (by rfl) ⟨1543230, by rfl⟩ : syracuseStep 4115281 = 3086461) B3086461
theorem B5487041 : Blo 2167435 5487041 := bstep (se 2 (by rfl) ⟨2057640, by rfl⟩ : syracuseStep 5487041 = 4115281) B4115281
theorem B3658027 : Blo 2167435 3658027 := bstep (se 1 (by rfl) ⟨2743520, by rfl⟩ : syracuseStep 3658027 = 5487041) B5487041
theorem B4877369 : Blo 2167435 4877369 := bstep (se 2 (by rfl) ⟨1829013, by rfl⟩ : syracuseStep 4877369 = 3658027) B3658027
theorem B3251579 : Blo 2167435 3251579 := bstep (se 1 (by rfl) ⟨2438684, by rfl⟩ : syracuseStep 3251579 = 4877369) B4877369
theorem B2167719 : Blo 2167435 2167719 := bstep (se 1 (by rfl) ⟨1625789, by rfl⟩ : syracuseStep 2167719 = 3251579) B3251579
theorem B2438689 : Blo 2167435 2438689 := bbase (se 2 (by rfl) ⟨914508, by rfl⟩ : syracuseStep 2438689 = 1829017) (by norm_num)
theorem B3251585 : Blo 2167435 3251585 := bstep (se 2 (by rfl) ⟨1219344, by rfl⟩ : syracuseStep 3251585 = 2438689) B2438689
theorem B2167723 : Blo 2167435 2167723 := bstep (se 1 (by rfl) ⟨1625792, by rfl⟩ : syracuseStep 2167723 = 3251585) B3251585
theorem B5487061 : Blo 2167435 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B7316081 : Blo 2167435 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B4877387 : Blo 2167435 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B3251591 : Blo 2167435 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B2167727 : Blo 2167435 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B3251597 : Blo 2167435 3251597 := bbase (se 3 (by rfl) ⟨609674, by rfl⟩ : syracuseStep 3251597 = 1219349) (by norm_num)
theorem B2167731 : Blo 2167435 2167731 := bstep (se 1 (by rfl) ⟨1625798, by rfl⟩ : syracuseStep 2167731 = 3251597) B3251597
theorem B4877405 : Blo 2167435 4877405 := bbase (se 3 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 4877405 = 1829027) (by norm_num)
theorem B3251603 : Blo 2167435 3251603 := bstep (se 1 (by rfl) ⟨2438702, by rfl⟩ : syracuseStep 3251603 = 4877405) B4877405
theorem B2167735 : Blo 2167435 2167735 := bstep (se 1 (by rfl) ⟨1625801, by rfl⟩ : syracuseStep 2167735 = 3251603) B3251603
theorem B3658061 : Blo 2167435 3658061 := bbase (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) (by norm_num)
theorem B2438707 : Blo 2167435 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B3251609 : Blo 2167435 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B2167739 : Blo 2167435 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B5279525 : Blo 2167435 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B3519683 : Blo 2167435 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2346455 : Blo 2167435 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B6257213 : Blo 2167435 6257213 := bstep (se 3 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 6257213 = 2346455) B2346455
theorem B4171475 : Blo 2167435 4171475 := bstep (se 1 (by rfl) ⟨3128606, by rfl⟩ : syracuseStep 4171475 = 6257213) B6257213
theorem B2780983 : Blo 2167435 2780983 := bstep (se 1 (by rfl) ⟨2085737, by rfl⟩ : syracuseStep 2780983 = 4171475) B4171475
theorem B14831909 : Blo 2167435 14831909 := bstep (se 4 (by rfl) ⟨1390491, by rfl⟩ : syracuseStep 14831909 = 2780983) B2780983
theorem B9887939 : Blo 2167435 9887939 := bstep (se 1 (by rfl) ⟨7415954, by rfl⟩ : syracuseStep 9887939 = 14831909) B14831909
theorem B6591959 : Blo 2167435 6591959 := bstep (se 1 (by rfl) ⟨4943969, by rfl⟩ : syracuseStep 6591959 = 9887939) B9887939
theorem B4394639 : Blo 2167435 4394639 := bstep (se 1 (by rfl) ⟨3295979, by rfl⟩ : syracuseStep 4394639 = 6591959) B6591959
theorem B2929759 : Blo 2167435 2929759 := bstep (se 1 (by rfl) ⟨2197319, by rfl⟩ : syracuseStep 2929759 = 4394639) B4394639
theorem B15625381 : Blo 2167435 15625381 := bstep (se 4 (by rfl) ⟨1464879, by rfl⟩ : syracuseStep 15625381 = 2929759) B2929759
theorem B20833841 : Blo 2167435 20833841 := bstep (se 2 (by rfl) ⟨7812690, by rfl⟩ : syracuseStep 20833841 = 15625381) B15625381
theorem B13889227 : Blo 2167435 13889227 := bstep (se 1 (by rfl) ⟨10416920, by rfl⟩ : syracuseStep 13889227 = 20833841) B20833841
theorem B18518969 : Blo 2167435 18518969 := bstep (se 2 (by rfl) ⟨6944613, by rfl⟩ : syracuseStep 18518969 = 13889227) B13889227
theorem B12345979 : Blo 2167435 12345979 := bstep (se 1 (by rfl) ⟨9259484, by rfl⟩ : syracuseStep 12345979 = 18518969) B18518969
theorem B16461305 : Blo 2167435 16461305 := bstep (se 2 (by rfl) ⟨6172989, by rfl⟩ : syracuseStep 16461305 = 12345979) B12345979
theorem B10974203 : Blo 2167435 10974203 := bstep (se 1 (by rfl) ⟨8230652, by rfl⟩ : syracuseStep 10974203 = 16461305) B16461305
theorem B7316135 : Blo 2167435 7316135 := bstep (se 1 (by rfl) ⟨5487101, by rfl⟩ : syracuseStep 7316135 = 10974203) B10974203
theorem B4877423 : Blo 2167435 4877423 := bstep (se 1 (by rfl) ⟨3658067, by rfl⟩ : syracuseStep 4877423 = 7316135) B7316135
theorem B3251615 : Blo 2167435 3251615 := bstep (se 1 (by rfl) ⟨2438711, by rfl⟩ : syracuseStep 3251615 = 4877423) B4877423
theorem B2167743 : Blo 2167435 2167743 := bstep (se 1 (by rfl) ⟨1625807, by rfl⟩ : syracuseStep 2167743 = 3251615) B3251615
theorem B3251621 : Blo 2167435 3251621 := bbase (se 4 (by rfl) ⟨304839, by rfl⟩ : syracuseStep 3251621 = 609679) (by norm_num)
theorem B2167747 : Blo 2167435 2167747 := bstep (se 1 (by rfl) ⟨1625810, by rfl⟩ : syracuseStep 2167747 = 3251621) B3251621
theorem B2743561 : Blo 2167435 2743561 := bbase (se 2 (by rfl) ⟨1028835, by rfl⟩ : syracuseStep 2743561 = 2057671) (by norm_num)
theorem B3658081 : Blo 2167435 3658081 := bstep (se 2 (by rfl) ⟨1371780, by rfl⟩ : syracuseStep 3658081 = 2743561) B2743561
theorem B4877441 : Blo 2167435 4877441 := bstep (se 2 (by rfl) ⟨1829040, by rfl⟩ : syracuseStep 4877441 = 3658081) B3658081
theorem B3251627 : Blo 2167435 3251627 := bstep (se 1 (by rfl) ⟨2438720, by rfl⟩ : syracuseStep 3251627 = 4877441) B4877441
theorem B2167751 : Blo 2167435 2167751 := bstep (se 1 (by rfl) ⟨1625813, by rfl⟩ : syracuseStep 2167751 = 3251627) B3251627
theorem B2438725 : Blo 2167435 2438725 := bbase (se 4 (by rfl) ⟨228630, by rfl⟩ : syracuseStep 2438725 = 457261) (by norm_num)
theorem B3251633 : Blo 2167435 3251633 := bstep (se 2 (by rfl) ⟨1219362, by rfl⟩ : syracuseStep 3251633 = 2438725) B2438725
theorem B2167755 : Blo 2167435 2167755 := bstep (se 1 (by rfl) ⟨1625816, by rfl⟩ : syracuseStep 2167755 = 3251633) B3251633
theorem B4115357 : Blo 2167435 4115357 := bbase (se 3 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 4115357 = 1543259) (by norm_num)
theorem B2743571 : Blo 2167435 2743571 := bstep (se 1 (by rfl) ⟨2057678, by rfl⟩ : syracuseStep 2743571 = 4115357) B4115357
theorem B7316189 : Blo 2167435 7316189 := bstep (se 3 (by rfl) ⟨1371785, by rfl⟩ : syracuseStep 7316189 = 2743571) B2743571
theorem B4877459 : Blo 2167435 4877459 := bstep (se 1 (by rfl) ⟨3658094, by rfl⟩ : syracuseStep 4877459 = 7316189) B7316189
theorem B3251639 : Blo 2167435 3251639 := bstep (se 1 (by rfl) ⟨2438729, by rfl⟩ : syracuseStep 3251639 = 4877459) B4877459
theorem B2167759 : Blo 2167435 2167759 := bstep (se 1 (by rfl) ⟨1625819, by rfl⟩ : syracuseStep 2167759 = 3251639) B3251639
theorem B3251645 : Blo 2167435 3251645 := bbase (se 3 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 3251645 = 1219367) (by norm_num)
theorem B2167763 : Blo 2167435 2167763 := bstep (se 1 (by rfl) ⟨1625822, by rfl⟩ : syracuseStep 2167763 = 3251645) B3251645
theorem B4877477 : Blo 2167435 4877477 := bbase (se 4 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 4877477 = 914527) (by norm_num)
theorem B3251651 : Blo 2167435 3251651 := bstep (se 1 (by rfl) ⟨2438738, by rfl⟩ : syracuseStep 3251651 = 4877477) B4877477
theorem B2167767 : Blo 2167435 2167767 := bstep (se 1 (by rfl) ⟨1625825, by rfl⟩ : syracuseStep 2167767 = 3251651) B3251651
theorem B5487173 : Blo 2167435 5487173 := bbase (se 4 (by rfl) ⟨514422, by rfl⟩ : syracuseStep 5487173 = 1028845) (by norm_num)
theorem B3658115 : Blo 2167435 3658115 := bstep (se 1 (by rfl) ⟨2743586, by rfl⟩ : syracuseStep 3658115 = 5487173) B5487173
theorem B2438743 : Blo 2167435 2438743 := bstep (se 1 (by rfl) ⟨1829057, by rfl⟩ : syracuseStep 2438743 = 3658115) B3658115
theorem B3251657 : Blo 2167435 3251657 := bstep (se 2 (by rfl) ⟨1219371, by rfl⟩ : syracuseStep 3251657 = 2438743) B2438743
theorem B2167771 : Blo 2167435 2167771 := bstep (se 1 (by rfl) ⟨1625828, by rfl⟩ : syracuseStep 2167771 = 3251657) B3251657
theorem B2604269 : Blo 2167435 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B6944717 : Blo 2167435 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B4629811 : Blo 2167435 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B6173081 : Blo 2167435 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B4115387 : Blo 2167435 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B10974365 : Blo 2167435 10974365 := bstep (se 3 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 10974365 = 4115387) B4115387
theorem B7316243 : Blo 2167435 7316243 := bstep (se 1 (by rfl) ⟨5487182, by rfl⟩ : syracuseStep 7316243 = 10974365) B10974365
theorem B4877495 : Blo 2167435 4877495 := bstep (se 1 (by rfl) ⟨3658121, by rfl⟩ : syracuseStep 4877495 = 7316243) B7316243
theorem B3251663 : Blo 2167435 3251663 := bstep (se 1 (by rfl) ⟨2438747, by rfl⟩ : syracuseStep 3251663 = 4877495) B4877495
theorem B2167775 : Blo 2167435 2167775 := bstep (se 1 (by rfl) ⟨1625831, by rfl⟩ : syracuseStep 2167775 = 3251663) B3251663
theorem B3251669 : Blo 2167435 3251669 := bbase (se 7 (by rfl) ⟨38105, by rfl⟩ : syracuseStep 3251669 = 76211) (by norm_num)
theorem B2167779 : Blo 2167435 2167779 := bstep (se 1 (by rfl) ⟨1625834, by rfl⟩ : syracuseStep 2167779 = 3251669) B3251669
theorem B8230805 : Blo 2167435 8230805 := bbase (se 6 (by rfl) ⟨192909, by rfl⟩ : syracuseStep 8230805 = 385819) (by norm_num)
theorem B5487203 : Blo 2167435 5487203 := bstep (se 1 (by rfl) ⟨4115402, by rfl⟩ : syracuseStep 5487203 = 8230805) B8230805
theorem B3658135 : Blo 2167435 3658135 := bstep (se 1 (by rfl) ⟨2743601, by rfl⟩ : syracuseStep 3658135 = 5487203) B5487203
theorem B4877513 : Blo 2167435 4877513 := bstep (se 2 (by rfl) ⟨1829067, by rfl⟩ : syracuseStep 4877513 = 3658135) B3658135
theorem B3251675 : Blo 2167435 3251675 := bstep (se 1 (by rfl) ⟨2438756, by rfl⟩ : syracuseStep 3251675 = 4877513) B4877513
theorem B2167783 : Blo 2167435 2167783 := bstep (se 1 (by rfl) ⟨1625837, by rfl⟩ : syracuseStep 2167783 = 3251675) B3251675
theorem B2438761 : Blo 2167435 2438761 := bbase (se 2 (by rfl) ⟨914535, by rfl⟩ : syracuseStep 2438761 = 1829071) (by norm_num)
theorem B3251681 : Blo 2167435 3251681 := bstep (se 2 (by rfl) ⟨1219380, by rfl⟩ : syracuseStep 3251681 = 2438761) B2438761
theorem B2167787 : Blo 2167435 2167787 := bstep (se 1 (by rfl) ⟨1625840, by rfl⟩ : syracuseStep 2167787 = 3251681) B3251681
theorem B4629845 : Blo 2167435 4629845 := bbase (se 12 (by rfl) ⟨1695, by rfl⟩ : syracuseStep 4629845 = 3391) (by norm_num)
theorem B12346253 : Blo 2167435 12346253 := bstep (se 3 (by rfl) ⟨2314922, by rfl⟩ : syracuseStep 12346253 = 4629845) B4629845
theorem B8230835 : Blo 2167435 8230835 := bstep (se 1 (by rfl) ⟨6173126, by rfl⟩ : syracuseStep 8230835 = 12346253) B12346253
theorem B5487223 : Blo 2167435 5487223 := bstep (se 1 (by rfl) ⟨4115417, by rfl⟩ : syracuseStep 5487223 = 8230835) B8230835
theorem B7316297 : Blo 2167435 7316297 := bstep (se 2 (by rfl) ⟨2743611, by rfl⟩ : syracuseStep 7316297 = 5487223) B5487223
theorem B4877531 : Blo 2167435 4877531 := bstep (se 1 (by rfl) ⟨3658148, by rfl⟩ : syracuseStep 4877531 = 7316297) B7316297
theorem B3251687 : Blo 2167435 3251687 := bstep (se 1 (by rfl) ⟨2438765, by rfl⟩ : syracuseStep 3251687 = 4877531) B4877531
theorem B2167791 : Blo 2167435 2167791 := bstep (se 1 (by rfl) ⟨1625843, by rfl⟩ : syracuseStep 2167791 = 3251687) B3251687
theorem B3251693 : Blo 2167435 3251693 := bbase (se 3 (by rfl) ⟨609692, by rfl⟩ : syracuseStep 3251693 = 1219385) (by norm_num)
theorem B2167795 : Blo 2167435 2167795 := bstep (se 1 (by rfl) ⟨1625846, by rfl⟩ : syracuseStep 2167795 = 3251693) B3251693
theorem B4877549 : Blo 2167435 4877549 := bbase (se 3 (by rfl) ⟨914540, by rfl⟩ : syracuseStep 4877549 = 1829081) (by norm_num)
theorem B3251699 : Blo 2167435 3251699 := bstep (se 1 (by rfl) ⟨2438774, by rfl⟩ : syracuseStep 3251699 = 4877549) B4877549
theorem B2167799 : Blo 2167435 2167799 := bstep (se 1 (by rfl) ⟨1625849, by rfl⟩ : syracuseStep 2167799 = 3251699) B3251699
theorem B3086581 : Blo 2167435 3086581 := bbase (se 5 (by rfl) ⟨144683, by rfl⟩ : syracuseStep 3086581 = 289367) (by norm_num)
theorem B4115441 : Blo 2167435 4115441 := bstep (se 2 (by rfl) ⟨1543290, by rfl⟩ : syracuseStep 4115441 = 3086581) B3086581
theorem B2743627 : Blo 2167435 2743627 := bstep (se 1 (by rfl) ⟨2057720, by rfl⟩ : syracuseStep 2743627 = 4115441) B4115441
theorem B3658169 : Blo 2167435 3658169 := bstep (se 2 (by rfl) ⟨1371813, by rfl⟩ : syracuseStep 3658169 = 2743627) B2743627
theorem B2438779 : Blo 2167435 2438779 := bstep (se 1 (by rfl) ⟨1829084, by rfl⟩ : syracuseStep 2438779 = 3658169) B3658169
theorem B3251705 : Blo 2167435 3251705 := bstep (se 2 (by rfl) ⟨1219389, by rfl⟩ : syracuseStep 3251705 = 2438779) B2438779
theorem B2167803 : Blo 2167435 2167803 := bstep (se 1 (by rfl) ⟨1625852, by rfl⟩ : syracuseStep 2167803 = 3251705) B3251705
theorem B46877525 : Blo 2167435 46877525 := bbase (se 9 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 46877525 = 274673) (by norm_num)
theorem B31251683 : Blo 2167435 31251683 := bstep (se 1 (by rfl) ⟨23438762, by rfl⟩ : syracuseStep 31251683 = 46877525) B46877525
theorem B83337821 : Blo 2167435 83337821 := bstep (se 3 (by rfl) ⟨15625841, by rfl⟩ : syracuseStep 83337821 = 31251683) B31251683
theorem B55558547 : Blo 2167435 55558547 := bstep (se 1 (by rfl) ⟨41668910, by rfl⟩ : syracuseStep 55558547 = 83337821) B83337821
theorem B37039031 : Blo 2167435 37039031 := bstep (se 1 (by rfl) ⟨27779273, by rfl⟩ : syracuseStep 37039031 = 55558547) B55558547
theorem B24692687 : Blo 2167435 24692687 := bstep (se 1 (by rfl) ⟨18519515, by rfl⟩ : syracuseStep 24692687 = 37039031) B37039031
theorem B16461791 : Blo 2167435 16461791 := bstep (se 1 (by rfl) ⟨12346343, by rfl⟩ : syracuseStep 16461791 = 24692687) B24692687
theorem B10974527 : Blo 2167435 10974527 := bstep (se 1 (by rfl) ⟨8230895, by rfl⟩ : syracuseStep 10974527 = 16461791) B16461791
theorem B7316351 : Blo 2167435 7316351 := bstep (se 1 (by rfl) ⟨5487263, by rfl⟩ : syracuseStep 7316351 = 10974527) B10974527
theorem B4877567 : Blo 2167435 4877567 := bstep (se 1 (by rfl) ⟨3658175, by rfl⟩ : syracuseStep 4877567 = 7316351) B7316351
theorem B3251711 : Blo 2167435 3251711 := bstep (se 1 (by rfl) ⟨2438783, by rfl⟩ : syracuseStep 3251711 = 4877567) B4877567
theorem B2167807 : Blo 2167435 2167807 := bstep (se 1 (by rfl) ⟨1625855, by rfl⟩ : syracuseStep 2167807 = 3251711) B3251711
theorem B3251717 : Blo 2167435 3251717 := bbase (se 4 (by rfl) ⟨304848, by rfl⟩ : syracuseStep 3251717 = 609697) (by norm_num)
theorem B2167811 : Blo 2167435 2167811 := bstep (se 1 (by rfl) ⟨1625858, by rfl⟩ : syracuseStep 2167811 = 3251717) B3251717
theorem B3658189 : Blo 2167435 3658189 := bbase (se 3 (by rfl) ⟨685910, by rfl⟩ : syracuseStep 3658189 = 1371821) (by norm_num)
theorem B4877585 : Blo 2167435 4877585 := bstep (se 2 (by rfl) ⟨1829094, by rfl⟩ : syracuseStep 4877585 = 3658189) B3658189
theorem B3251723 : Blo 2167435 3251723 := bstep (se 1 (by rfl) ⟨2438792, by rfl⟩ : syracuseStep 3251723 = 4877585) B4877585
theorem B2167815 : Blo 2167435 2167815 := bstep (se 1 (by rfl) ⟨1625861, by rfl⟩ : syracuseStep 2167815 = 3251723) B3251723
theorem B2438797 : Blo 2167435 2438797 := bbase (se 3 (by rfl) ⟨457274, by rfl⟩ : syracuseStep 2438797 = 914549) (by norm_num)
theorem B3251729 : Blo 2167435 3251729 := bstep (se 2 (by rfl) ⟨1219398, by rfl⟩ : syracuseStep 3251729 = 2438797) B2438797
theorem B2167819 : Blo 2167435 2167819 := bstep (se 1 (by rfl) ⟨1625864, by rfl⟩ : syracuseStep 2167819 = 3251729) B3251729
theorem B7316405 : Blo 2167435 7316405 := bbase (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) (by norm_num)
theorem B4877603 : Blo 2167435 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B3251735 : Blo 2167435 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B2167823 : Blo 2167435 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B3251741 : Blo 2167435 3251741 := bbase (se 3 (by rfl) ⟨609701, by rfl⟩ : syracuseStep 3251741 = 1219403) (by norm_num)
theorem B2167827 : Blo 2167435 2167827 := bstep (se 1 (by rfl) ⟨1625870, by rfl⟩ : syracuseStep 2167827 = 3251741) B3251741
theorem B4877621 : Blo 2167435 4877621 := bbase (se 5 (by rfl) ⟨228638, by rfl⟩ : syracuseStep 4877621 = 457277) (by norm_num)
theorem B3251747 : Blo 2167435 3251747 := bstep (se 1 (by rfl) ⟨2438810, by rfl⟩ : syracuseStep 3251747 = 4877621) B4877621
theorem B2167831 : Blo 2167435 2167831 := bstep (se 1 (by rfl) ⟨1625873, by rfl⟩ : syracuseStep 2167831 = 3251747) B3251747
theorem B6257477 : Blo 2167435 6257477 := bbase (se 4 (by rfl) ⟨586638, by rfl⟩ : syracuseStep 6257477 = 1173277) (by norm_num)
theorem B16686605 : Blo 2167435 16686605 := bstep (se 3 (by rfl) ⟨3128738, by rfl⟩ : syracuseStep 16686605 = 6257477) B6257477
theorem B44497613 : Blo 2167435 44497613 := bstep (se 3 (by rfl) ⟨8343302, by rfl⟩ : syracuseStep 44497613 = 16686605) B16686605
theorem B118660301 : Blo 2167435 118660301 := bstep (se 3 (by rfl) ⟨22248806, by rfl⟩ : syracuseStep 118660301 = 44497613) B44497613
theorem B79106867 : Blo 2167435 79106867 := bstep (se 1 (by rfl) ⟨59330150, by rfl⟩ : syracuseStep 79106867 = 118660301) B118660301
theorem B52737911 : Blo 2167435 52737911 := bstep (se 1 (by rfl) ⟨39553433, by rfl⟩ : syracuseStep 52737911 = 79106867) B79106867
theorem B35158607 : Blo 2167435 35158607 := bstep (se 1 (by rfl) ⟨26368955, by rfl⟩ : syracuseStep 35158607 = 52737911) B52737911
theorem B23439071 : Blo 2167435 23439071 := bstep (se 1 (by rfl) ⟨17579303, by rfl⟩ : syracuseStep 23439071 = 35158607) B35158607
theorem B15626047 : Blo 2167435 15626047 := bstep (se 1 (by rfl) ⟨11719535, by rfl⟩ : syracuseStep 15626047 = 23439071) B23439071
theorem B20834729 : Blo 2167435 20834729 := bstep (se 2 (by rfl) ⟨7813023, by rfl⟩ : syracuseStep 20834729 = 15626047) B15626047
theorem B13889819 : Blo 2167435 13889819 := bstep (se 1 (by rfl) ⟨10417364, by rfl⟩ : syracuseStep 13889819 = 20834729) B20834729
theorem B9259879 : Blo 2167435 9259879 := bstep (se 1 (by rfl) ⟨6944909, by rfl⟩ : syracuseStep 9259879 = 13889819) B13889819
theorem B12346505 : Blo 2167435 12346505 := bstep (se 2 (by rfl) ⟨4629939, by rfl⟩ : syracuseStep 12346505 = 9259879) B9259879
theorem B8231003 : Blo 2167435 8231003 := bstep (se 1 (by rfl) ⟨6173252, by rfl⟩ : syracuseStep 8231003 = 12346505) B12346505
theorem B5487335 : Blo 2167435 5487335 := bstep (se 1 (by rfl) ⟨4115501, by rfl⟩ : syracuseStep 5487335 = 8231003) B8231003
theorem B3658223 : Blo 2167435 3658223 := bstep (se 1 (by rfl) ⟨2743667, by rfl⟩ : syracuseStep 3658223 = 5487335) B5487335
theorem B2438815 : Blo 2167435 2438815 := bstep (se 1 (by rfl) ⟨1829111, by rfl⟩ : syracuseStep 2438815 = 3658223) B3658223
theorem B3251753 : Blo 2167435 3251753 := bstep (se 2 (by rfl) ⟨1219407, by rfl⟩ : syracuseStep 3251753 = 2438815) B2438815
theorem B2167835 : Blo 2167435 2167835 := bstep (se 1 (by rfl) ⟨1625876, by rfl⟩ : syracuseStep 2167835 = 3251753) B3251753
theorem B2197417 : Blo 2167435 2197417 := bbase (se 2 (by rfl) ⟨824031, by rfl⟩ : syracuseStep 2197417 = 1648063) (by norm_num)
theorem B2929889 : Blo 2167435 2929889 := bstep (se 2 (by rfl) ⟨1098708, by rfl⟩ : syracuseStep 2929889 = 2197417) B2197417
theorem B7813037 : Blo 2167435 7813037 := bstep (se 3 (by rfl) ⟨1464944, by rfl⟩ : syracuseStep 7813037 = 2929889) B2929889
theorem B20834765 : Blo 2167435 20834765 := bstep (se 3 (by rfl) ⟨3906518, by rfl⟩ : syracuseStep 20834765 = 7813037) B7813037
theorem B13889843 : Blo 2167435 13889843 := bstep (se 1 (by rfl) ⟨10417382, by rfl⟩ : syracuseStep 13889843 = 20834765) B20834765
theorem B9259895 : Blo 2167435 9259895 := bstep (se 1 (by rfl) ⟨6944921, by rfl⟩ : syracuseStep 9259895 = 13889843) B13889843
theorem B6173263 : Blo 2167435 6173263 := bstep (se 1 (by rfl) ⟨4629947, by rfl⟩ : syracuseStep 6173263 = 9259895) B9259895
theorem B8231017 : Blo 2167435 8231017 := bstep (se 2 (by rfl) ⟨3086631, by rfl⟩ : syracuseStep 8231017 = 6173263) B6173263
theorem B10974689 : Blo 2167435 10974689 := bstep (se 2 (by rfl) ⟨4115508, by rfl⟩ : syracuseStep 10974689 = 8231017) B8231017
theorem B7316459 : Blo 2167435 7316459 := bstep (se 1 (by rfl) ⟨5487344, by rfl⟩ : syracuseStep 7316459 = 10974689) B10974689
theorem B4877639 : Blo 2167435 4877639 := bstep (se 1 (by rfl) ⟨3658229, by rfl⟩ : syracuseStep 4877639 = 7316459) B7316459
theorem B3251759 : Blo 2167435 3251759 := bstep (se 1 (by rfl) ⟨2438819, by rfl⟩ : syracuseStep 3251759 = 4877639) B4877639
theorem B2167839 : Blo 2167435 2167839 := bstep (se 1 (by rfl) ⟨1625879, by rfl⟩ : syracuseStep 2167839 = 3251759) B3251759
theorem B3251765 : Blo 2167435 3251765 := bbase (se 5 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 3251765 = 304853) (by norm_num)
theorem B2167843 : Blo 2167435 2167843 := bstep (se 1 (by rfl) ⟨1625882, by rfl⟩ : syracuseStep 2167843 = 3251765) B3251765
theorem B5487365 : Blo 2167435 5487365 := bbase (se 4 (by rfl) ⟨514440, by rfl⟩ : syracuseStep 5487365 = 1028881) (by norm_num)
theorem B3658243 : Blo 2167435 3658243 := bstep (se 1 (by rfl) ⟨2743682, by rfl⟩ : syracuseStep 3658243 = 5487365) B5487365
theorem B4877657 : Blo 2167435 4877657 := bstep (se 2 (by rfl) ⟨1829121, by rfl⟩ : syracuseStep 4877657 = 3658243) B3658243
theorem B3251771 : Blo 2167435 3251771 := bstep (se 1 (by rfl) ⟨2438828, by rfl⟩ : syracuseStep 3251771 = 4877657) B4877657
theorem B2167847 : Blo 2167435 2167847 := bstep (se 1 (by rfl) ⟨1625885, by rfl⟩ : syracuseStep 2167847 = 3251771) B3251771
theorem B2438833 : Blo 2167435 2438833 := bbase (se 2 (by rfl) ⟨914562, by rfl⟩ : syracuseStep 2438833 = 1829125) (by norm_num)
theorem B3251777 : Blo 2167435 3251777 := bstep (se 2 (by rfl) ⟨1219416, by rfl⟩ : syracuseStep 3251777 = 2438833) B2438833
theorem B2167851 : Blo 2167435 2167851 := bstep (se 1 (by rfl) ⟨1625888, by rfl⟩ : syracuseStep 2167851 = 3251777) B3251777
theorem B5279797 : Blo 2167435 5279797 := bbase (se 5 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 5279797 = 494981) (by norm_num)
theorem B7039729 : Blo 2167435 7039729 := bstep (se 2 (by rfl) ⟨2639898, by rfl⟩ : syracuseStep 7039729 = 5279797) B5279797
theorem B37545221 : Blo 2167435 37545221 := bstep (se 4 (by rfl) ⟨3519864, by rfl⟩ : syracuseStep 37545221 = 7039729) B7039729
theorem B25030147 : Blo 2167435 25030147 := bstep (se 1 (by rfl) ⟨18772610, by rfl⟩ : syracuseStep 25030147 = 37545221) B37545221
theorem B33373529 : Blo 2167435 33373529 := bstep (se 2 (by rfl) ⟨12515073, by rfl⟩ : syracuseStep 33373529 = 25030147) B25030147
theorem B22249019 : Blo 2167435 22249019 := bstep (se 1 (by rfl) ⟨16686764, by rfl⟩ : syracuseStep 22249019 = 33373529) B33373529
theorem B14832679 : Blo 2167435 14832679 := bstep (se 1 (by rfl) ⟨11124509, by rfl⟩ : syracuseStep 14832679 = 22249019) B22249019
theorem B19776905 : Blo 2167435 19776905 := bstep (se 2 (by rfl) ⟨7416339, by rfl⟩ : syracuseStep 19776905 = 14832679) B14832679
theorem B13184603 : Blo 2167435 13184603 := bstep (se 1 (by rfl) ⟨9888452, by rfl⟩ : syracuseStep 13184603 = 19776905) B19776905
theorem B8789735 : Blo 2167435 8789735 := bstep (se 1 (by rfl) ⟨6592301, by rfl⟩ : syracuseStep 8789735 = 13184603) B13184603
theorem B5859823 : Blo 2167435 5859823 := bstep (se 1 (by rfl) ⟨4394867, by rfl⟩ : syracuseStep 5859823 = 8789735) B8789735
theorem B7813097 : Blo 2167435 7813097 := bstep (se 2 (by rfl) ⟨2929911, by rfl⟩ : syracuseStep 7813097 = 5859823) B5859823
theorem B5208731 : Blo 2167435 5208731 := bstep (se 1 (by rfl) ⟨3906548, by rfl⟩ : syracuseStep 5208731 = 7813097) B7813097
theorem B3472487 : Blo 2167435 3472487 := bstep (se 1 (by rfl) ⟨2604365, by rfl⟩ : syracuseStep 3472487 = 5208731) B5208731
theorem B2314991 : Blo 2167435 2314991 := bstep (se 1 (by rfl) ⟨1736243, by rfl⟩ : syracuseStep 2314991 = 3472487) B3472487
theorem B6173309 : Blo 2167435 6173309 := bstep (se 3 (by rfl) ⟨1157495, by rfl⟩ : syracuseStep 6173309 = 2314991) B2314991
theorem B4115539 : Blo 2167435 4115539 := bstep (se 1 (by rfl) ⟨3086654, by rfl⟩ : syracuseStep 4115539 = 6173309) B6173309
theorem B5487385 : Blo 2167435 5487385 := bstep (se 2 (by rfl) ⟨2057769, by rfl⟩ : syracuseStep 5487385 = 4115539) B4115539
theorem B7316513 : Blo 2167435 7316513 := bstep (se 2 (by rfl) ⟨2743692, by rfl⟩ : syracuseStep 7316513 = 5487385) B5487385
theorem B4877675 : Blo 2167435 4877675 := bstep (se 1 (by rfl) ⟨3658256, by rfl⟩ : syracuseStep 4877675 = 7316513) B7316513
theorem B3251783 : Blo 2167435 3251783 := bstep (se 1 (by rfl) ⟨2438837, by rfl⟩ : syracuseStep 3251783 = 4877675) B4877675
theorem B2167855 : Blo 2167435 2167855 := bstep (se 1 (by rfl) ⟨1625891, by rfl⟩ : syracuseStep 2167855 = 3251783) B3251783
theorem B3251789 : Blo 2167435 3251789 := bbase (se 3 (by rfl) ⟨609710, by rfl⟩ : syracuseStep 3251789 = 1219421) (by norm_num)
theorem B2167859 : Blo 2167435 2167859 := bstep (se 1 (by rfl) ⟨1625894, by rfl⟩ : syracuseStep 2167859 = 3251789) B3251789
theorem B4877693 : Blo 2167435 4877693 := bbase (se 3 (by rfl) ⟨914567, by rfl⟩ : syracuseStep 4877693 = 1829135) (by norm_num)
theorem B3251795 : Blo 2167435 3251795 := bstep (se 1 (by rfl) ⟨2438846, by rfl⟩ : syracuseStep 3251795 = 4877693) B4877693
theorem B2167863 : Blo 2167435 2167863 := bstep (se 1 (by rfl) ⟨1625897, by rfl⟩ : syracuseStep 2167863 = 3251795) B3251795
theorem B3658277 : Blo 2167435 3658277 := bbase (se 4 (by rfl) ⟨342963, by rfl⟩ : syracuseStep 3658277 = 685927) (by norm_num)
theorem B2438851 : Blo 2167435 2438851 := bstep (se 1 (by rfl) ⟨1829138, by rfl⟩ : syracuseStep 2438851 = 3658277) B3658277
theorem B3251801 : Blo 2167435 3251801 := bstep (se 2 (by rfl) ⟨1219425, by rfl⟩ : syracuseStep 3251801 = 2438851) B2438851
theorem B2167867 : Blo 2167435 2167867 := bstep (se 1 (by rfl) ⟨1625900, by rfl⟩ : syracuseStep 2167867 = 3251801) B3251801
theorem B3086677 : Blo 2167435 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B16462277 : Blo 2167435 16462277 := bstep (se 4 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 16462277 = 3086677) B3086677
theorem B10974851 : Blo 2167435 10974851 := bstep (se 1 (by rfl) ⟨8231138, by rfl⟩ : syracuseStep 10974851 = 16462277) B16462277
theorem B7316567 : Blo 2167435 7316567 := bstep (se 1 (by rfl) ⟨5487425, by rfl⟩ : syracuseStep 7316567 = 10974851) B10974851
theorem B4877711 : Blo 2167435 4877711 := bstep (se 1 (by rfl) ⟨3658283, by rfl⟩ : syracuseStep 4877711 = 7316567) B7316567
theorem B3251807 : Blo 2167435 3251807 := bstep (se 1 (by rfl) ⟨2438855, by rfl⟩ : syracuseStep 3251807 = 4877711) B4877711
theorem B2167871 : Blo 2167435 2167871 := bstep (se 1 (by rfl) ⟨1625903, by rfl⟩ : syracuseStep 2167871 = 3251807) B3251807
theorem B3251813 : Blo 2167435 3251813 := bbase (se 4 (by rfl) ⟨304857, by rfl⟩ : syracuseStep 3251813 = 609715) (by norm_num)
theorem B2167875 : Blo 2167435 2167875 := bstep (se 1 (by rfl) ⟨1625906, by rfl⟩ : syracuseStep 2167875 = 3251813) B3251813
theorem B2315017 : Blo 2167435 2315017 := bbase (se 2 (by rfl) ⟨868131, by rfl⟩ : syracuseStep 2315017 = 1736263) (by norm_num)
theorem B3086689 : Blo 2167435 3086689 := bstep (se 2 (by rfl) ⟨1157508, by rfl⟩ : syracuseStep 3086689 = 2315017) B2315017
theorem B4115585 : Blo 2167435 4115585 := bstep (se 2 (by rfl) ⟨1543344, by rfl⟩ : syracuseStep 4115585 = 3086689) B3086689
theorem B2743723 : Blo 2167435 2743723 := bstep (se 1 (by rfl) ⟨2057792, by rfl⟩ : syracuseStep 2743723 = 4115585) B4115585
theorem B3658297 : Blo 2167435 3658297 := bstep (se 2 (by rfl) ⟨1371861, by rfl⟩ : syracuseStep 3658297 = 2743723) B2743723
theorem B4877729 : Blo 2167435 4877729 := bstep (se 2 (by rfl) ⟨1829148, by rfl⟩ : syracuseStep 4877729 = 3658297) B3658297
theorem B3251819 : Blo 2167435 3251819 := bstep (se 1 (by rfl) ⟨2438864, by rfl⟩ : syracuseStep 3251819 = 4877729) B4877729
theorem B2167879 : Blo 2167435 2167879 := bstep (se 1 (by rfl) ⟨1625909, by rfl⟩ : syracuseStep 2167879 = 3251819) B3251819
theorem B2438869 : Blo 2167435 2438869 := bbase (se 7 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 2438869 = 57161) (by norm_num)
theorem B3251825 : Blo 2167435 3251825 := bstep (se 2 (by rfl) ⟨1219434, by rfl⟩ : syracuseStep 3251825 = 2438869) B2438869
theorem B2167883 : Blo 2167435 2167883 := bstep (se 1 (by rfl) ⟨1625912, by rfl⟩ : syracuseStep 2167883 = 3251825) B3251825
theorem B2743733 : Blo 2167435 2743733 := bbase (se 5 (by rfl) ⟨128612, by rfl⟩ : syracuseStep 2743733 = 257225) (by norm_num)
theorem B7316621 : Blo 2167435 7316621 := bstep (se 3 (by rfl) ⟨1371866, by rfl⟩ : syracuseStep 7316621 = 2743733) B2743733
theorem B4877747 : Blo 2167435 4877747 := bstep (se 1 (by rfl) ⟨3658310, by rfl⟩ : syracuseStep 4877747 = 7316621) B7316621
theorem B3251831 : Blo 2167435 3251831 := bstep (se 1 (by rfl) ⟨2438873, by rfl⟩ : syracuseStep 3251831 = 4877747) B4877747
theorem B2167887 : Blo 2167435 2167887 := bstep (se 1 (by rfl) ⟨1625915, by rfl⟩ : syracuseStep 2167887 = 3251831) B3251831
theorem B3251837 : Blo 2167435 3251837 := bbase (se 3 (by rfl) ⟨609719, by rfl⟩ : syracuseStep 3251837 = 1219439) (by norm_num)
theorem B2167891 : Blo 2167435 2167891 := bstep (se 1 (by rfl) ⟨1625918, by rfl⟩ : syracuseStep 2167891 = 3251837) B3251837
theorem B4877765 : Blo 2167435 4877765 := bbase (se 4 (by rfl) ⟨457290, by rfl⟩ : syracuseStep 4877765 = 914581) (by norm_num)
theorem B3251843 : Blo 2167435 3251843 := bstep (se 1 (by rfl) ⟨2438882, by rfl⟩ : syracuseStep 3251843 = 4877765) B4877765
theorem B2167895 : Blo 2167435 2167895 := bstep (se 1 (by rfl) ⟨1625921, by rfl⟩ : syracuseStep 2167895 = 3251843) B3251843
theorem B3708245 : Blo 2167435 3708245 := bbase (se 14 (by rfl) ⟨339, by rfl⟩ : syracuseStep 3708245 = 679) (by norm_num)
theorem B2472163 : Blo 2167435 2472163 := bstep (se 1 (by rfl) ⟨1854122, by rfl⟩ : syracuseStep 2472163 = 3708245) B3708245
theorem B13184869 : Blo 2167435 13184869 := bstep (se 4 (by rfl) ⟨1236081, by rfl⟩ : syracuseStep 13184869 = 2472163) B2472163
theorem B17579825 : Blo 2167435 17579825 := bstep (se 2 (by rfl) ⟨6592434, by rfl⟩ : syracuseStep 17579825 = 13184869) B13184869
theorem B11719883 : Blo 2167435 11719883 := bstep (se 1 (by rfl) ⟨8789912, by rfl⟩ : syracuseStep 11719883 = 17579825) B17579825
theorem B7813255 : Blo 2167435 7813255 := bstep (se 1 (by rfl) ⟨5859941, by rfl⟩ : syracuseStep 7813255 = 11719883) B11719883
theorem B10417673 : Blo 2167435 10417673 := bstep (se 2 (by rfl) ⟨3906627, by rfl⟩ : syracuseStep 10417673 = 7813255) B7813255
theorem B6945115 : Blo 2167435 6945115 := bstep (se 1 (by rfl) ⟨5208836, by rfl⟩ : syracuseStep 6945115 = 10417673) B10417673
theorem B9260153 : Blo 2167435 9260153 := bstep (se 2 (by rfl) ⟨3472557, by rfl⟩ : syracuseStep 9260153 = 6945115) B6945115
theorem B6173435 : Blo 2167435 6173435 := bstep (se 1 (by rfl) ⟨4630076, by rfl⟩ : syracuseStep 6173435 = 9260153) B9260153
theorem B4115623 : Blo 2167435 4115623 := bstep (se 1 (by rfl) ⟨3086717, by rfl⟩ : syracuseStep 4115623 = 6173435) B6173435
theorem B5487497 : Blo 2167435 5487497 := bstep (se 2 (by rfl) ⟨2057811, by rfl⟩ : syracuseStep 5487497 = 4115623) B4115623
theorem B3658331 : Blo 2167435 3658331 := bstep (se 1 (by rfl) ⟨2743748, by rfl⟩ : syracuseStep 3658331 = 5487497) B5487497
theorem B2438887 : Blo 2167435 2438887 := bstep (se 1 (by rfl) ⟨1829165, by rfl⟩ : syracuseStep 2438887 = 3658331) B3658331
theorem B3251849 : Blo 2167435 3251849 := bstep (se 2 (by rfl) ⟨1219443, by rfl⟩ : syracuseStep 3251849 = 2438887) B2438887
theorem B2167899 : Blo 2167435 2167899 := bstep (se 1 (by rfl) ⟨1625924, by rfl⟩ : syracuseStep 2167899 = 3251849) B3251849
theorem B10975013 : Blo 2167435 10975013 := bbase (se 4 (by rfl) ⟨1028907, by rfl⟩ : syracuseStep 10975013 = 2057815) (by norm_num)
theorem B7316675 : Blo 2167435 7316675 := bstep (se 1 (by rfl) ⟨5487506, by rfl⟩ : syracuseStep 7316675 = 10975013) B10975013
theorem B4877783 : Blo 2167435 4877783 := bstep (se 1 (by rfl) ⟨3658337, by rfl⟩ : syracuseStep 4877783 = 7316675) B7316675
theorem B3251855 : Blo 2167435 3251855 := bstep (se 1 (by rfl) ⟨2438891, by rfl⟩ : syracuseStep 3251855 = 4877783) B4877783
theorem B2167903 : Blo 2167435 2167903 := bstep (se 1 (by rfl) ⟨1625927, by rfl⟩ : syracuseStep 2167903 = 3251855) B3251855
theorem B3251861 : Blo 2167435 3251861 := bbase (se 6 (by rfl) ⟨76215, by rfl⟩ : syracuseStep 3251861 = 152431) (by norm_num)
theorem B2167907 : Blo 2167435 2167907 := bstep (se 1 (by rfl) ⟨1625930, by rfl⟩ : syracuseStep 2167907 = 3251861) B3251861
theorem B5859973 : Blo 2167435 5859973 := bbase (se 4 (by rfl) ⟨549372, by rfl⟩ : syracuseStep 5859973 = 1098745) (by norm_num)
theorem B7813297 : Blo 2167435 7813297 := bstep (se 2 (by rfl) ⟨2929986, by rfl⟩ : syracuseStep 7813297 = 5859973) B5859973
theorem B10417729 : Blo 2167435 10417729 := bstep (se 2 (by rfl) ⟨3906648, by rfl⟩ : syracuseStep 10417729 = 7813297) B7813297
theorem B13890305 : Blo 2167435 13890305 := bstep (se 2 (by rfl) ⟨5208864, by rfl⟩ : syracuseStep 13890305 = 10417729) B10417729
theorem B9260203 : Blo 2167435 9260203 := bstep (se 1 (by rfl) ⟨6945152, by rfl⟩ : syracuseStep 9260203 = 13890305) B13890305
theorem B12346937 : Blo 2167435 12346937 := bstep (se 2 (by rfl) ⟨4630101, by rfl⟩ : syracuseStep 12346937 = 9260203) B9260203
theorem B8231291 : Blo 2167435 8231291 := bstep (se 1 (by rfl) ⟨6173468, by rfl⟩ : syracuseStep 8231291 = 12346937) B12346937
theorem B5487527 : Blo 2167435 5487527 := bstep (se 1 (by rfl) ⟨4115645, by rfl⟩ : syracuseStep 5487527 = 8231291) B8231291
theorem B3658351 : Blo 2167435 3658351 := bstep (se 1 (by rfl) ⟨2743763, by rfl⟩ : syracuseStep 3658351 = 5487527) B5487527
theorem B4877801 : Blo 2167435 4877801 := bstep (se 2 (by rfl) ⟨1829175, by rfl⟩ : syracuseStep 4877801 = 3658351) B3658351
theorem B3251867 : Blo 2167435 3251867 := bstep (se 1 (by rfl) ⟨2438900, by rfl⟩ : syracuseStep 3251867 = 4877801) B4877801
theorem B2167911 : Blo 2167435 2167911 := bstep (se 1 (by rfl) ⟨1625933, by rfl⟩ : syracuseStep 2167911 = 3251867) B3251867
theorem B2438905 : Blo 2167435 2438905 := bbase (se 2 (by rfl) ⟨914589, by rfl⟩ : syracuseStep 2438905 = 1829179) (by norm_num)
theorem B3251873 : Blo 2167435 3251873 := bstep (se 2 (by rfl) ⟨1219452, by rfl⟩ : syracuseStep 3251873 = 2438905) B2438905
theorem B2167915 : Blo 2167435 2167915 := bstep (se 1 (by rfl) ⟨1625936, by rfl⟩ : syracuseStep 2167915 = 3251873) B3251873
theorem B3472589 : Blo 2167435 3472589 := bbase (se 3 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 3472589 = 1302221) (by norm_num)
theorem B9260237 : Blo 2167435 9260237 := bstep (se 3 (by rfl) ⟨1736294, by rfl⟩ : syracuseStep 9260237 = 3472589) B3472589
theorem B6173491 : Blo 2167435 6173491 := bstep (se 1 (by rfl) ⟨4630118, by rfl⟩ : syracuseStep 6173491 = 9260237) B9260237
theorem B8231321 : Blo 2167435 8231321 := bstep (se 2 (by rfl) ⟨3086745, by rfl⟩ : syracuseStep 8231321 = 6173491) B6173491
theorem B5487547 : Blo 2167435 5487547 := bstep (se 1 (by rfl) ⟨4115660, by rfl⟩ : syracuseStep 5487547 = 8231321) B8231321
theorem B7316729 : Blo 2167435 7316729 := bstep (se 2 (by rfl) ⟨2743773, by rfl⟩ : syracuseStep 7316729 = 5487547) B5487547
theorem B4877819 : Blo 2167435 4877819 := bstep (se 1 (by rfl) ⟨3658364, by rfl⟩ : syracuseStep 4877819 = 7316729) B7316729
theorem B3251879 : Blo 2167435 3251879 := bstep (se 1 (by rfl) ⟨2438909, by rfl⟩ : syracuseStep 3251879 = 4877819) B4877819
theorem B2167919 : Blo 2167435 2167919 := bstep (se 1 (by rfl) ⟨1625939, by rfl⟩ : syracuseStep 2167919 = 3251879) B3251879
theorem B3251885 : Blo 2167435 3251885 := bbase (se 3 (by rfl) ⟨609728, by rfl⟩ : syracuseStep 3251885 = 1219457) (by norm_num)
theorem B2167923 : Blo 2167435 2167923 := bstep (se 1 (by rfl) ⟨1625942, by rfl⟩ : syracuseStep 2167923 = 3251885) B3251885
theorem B4877837 : Blo 2167435 4877837 := bbase (se 3 (by rfl) ⟨914594, by rfl⟩ : syracuseStep 4877837 = 1829189) (by norm_num)
theorem B3251891 : Blo 2167435 3251891 := bstep (se 1 (by rfl) ⟨2438918, by rfl⟩ : syracuseStep 3251891 = 4877837) B4877837
theorem B2167927 : Blo 2167435 2167927 := bstep (se 1 (by rfl) ⟨1625945, by rfl⟩ : syracuseStep 2167927 = 3251891) B3251891
theorem B2743789 : Blo 2167435 2743789 := bbase (se 3 (by rfl) ⟨514460, by rfl⟩ : syracuseStep 2743789 = 1028921) (by norm_num)
theorem B3658385 : Blo 2167435 3658385 := bstep (se 2 (by rfl) ⟨1371894, by rfl⟩ : syracuseStep 3658385 = 2743789) B2743789
theorem B2438923 : Blo 2167435 2438923 := bstep (se 1 (by rfl) ⟨1829192, by rfl⟩ : syracuseStep 2438923 = 3658385) B3658385
theorem B3251897 : Blo 2167435 3251897 := bstep (se 2 (by rfl) ⟨1219461, by rfl⟩ : syracuseStep 3251897 = 2438923) B2438923
theorem B2167931 : Blo 2167435 2167931 := bstep (se 1 (by rfl) ⟨1625948, by rfl⟩ : syracuseStep 2167931 = 3251897) B3251897
theorem B5860037 : Blo 2167435 5860037 := bbase (se 4 (by rfl) ⟨549378, by rfl⟩ : syracuseStep 5860037 = 1098757) (by norm_num)
theorem B15626765 : Blo 2167435 15626765 := bstep (se 3 (by rfl) ⟨2930018, by rfl⟩ : syracuseStep 15626765 = 5860037) B5860037
theorem B10417843 : Blo 2167435 10417843 := bstep (se 1 (by rfl) ⟨7813382, by rfl⟩ : syracuseStep 10417843 = 15626765) B15626765
theorem B13890457 : Blo 2167435 13890457 := bstep (se 2 (by rfl) ⟨5208921, by rfl⟩ : syracuseStep 13890457 = 10417843) B10417843
theorem B18520609 : Blo 2167435 18520609 := bstep (se 2 (by rfl) ⟨6945228, by rfl⟩ : syracuseStep 18520609 = 13890457) B13890457
theorem B24694145 : Blo 2167435 24694145 := bstep (se 2 (by rfl) ⟨9260304, by rfl⟩ : syracuseStep 24694145 = 18520609) B18520609
theorem B16462763 : Blo 2167435 16462763 := bstep (se 1 (by rfl) ⟨12347072, by rfl⟩ : syracuseStep 16462763 = 24694145) B24694145
theorem B10975175 : Blo 2167435 10975175 := bstep (se 1 (by rfl) ⟨8231381, by rfl⟩ : syracuseStep 10975175 = 16462763) B16462763
theorem B7316783 : Blo 2167435 7316783 := bstep (se 1 (by rfl) ⟨5487587, by rfl⟩ : syracuseStep 7316783 = 10975175) B10975175
theorem B4877855 : Blo 2167435 4877855 := bstep (se 1 (by rfl) ⟨3658391, by rfl⟩ : syracuseStep 4877855 = 7316783) B7316783
theorem B3251903 : Blo 2167435 3251903 := bstep (se 1 (by rfl) ⟨2438927, by rfl⟩ : syracuseStep 3251903 = 4877855) B4877855
theorem B2167935 : Blo 2167435 2167935 := bstep (se 1 (by rfl) ⟨1625951, by rfl⟩ : syracuseStep 2167935 = 3251903) B3251903
theorem B3251909 : Blo 2167435 3251909 := bbase (se 4 (by rfl) ⟨304866, by rfl⟩ : syracuseStep 3251909 = 609733) (by norm_num)
theorem B2167939 : Blo 2167435 2167939 := bstep (se 1 (by rfl) ⟨1625954, by rfl⟩ : syracuseStep 2167939 = 3251909) B3251909
theorem B3658405 : Blo 2167435 3658405 := bbase (se 4 (by rfl) ⟨342975, by rfl⟩ : syracuseStep 3658405 = 685951) (by norm_num)
theorem B4877873 : Blo 2167435 4877873 := bstep (se 2 (by rfl) ⟨1829202, by rfl⟩ : syracuseStep 4877873 = 3658405) B3658405
theorem B3251915 : Blo 2167435 3251915 := bstep (se 1 (by rfl) ⟨2438936, by rfl⟩ : syracuseStep 3251915 = 4877873) B4877873
theorem B2167943 : Blo 2167435 2167943 := bstep (se 1 (by rfl) ⟨1625957, by rfl⟩ : syracuseStep 2167943 = 3251915) B3251915
theorem B2438941 : Blo 2167435 2438941 := bbase (se 3 (by rfl) ⟨457301, by rfl⟩ : syracuseStep 2438941 = 914603) (by norm_num)
theorem B3251921 : Blo 2167435 3251921 := bstep (se 2 (by rfl) ⟨1219470, by rfl⟩ : syracuseStep 3251921 = 2438941) B2438941
theorem B2167947 : Blo 2167435 2167947 := bstep (se 1 (by rfl) ⟨1625960, by rfl⟩ : syracuseStep 2167947 = 3251921) B3251921
theorem B7316837 : Blo 2167435 7316837 := bbase (se 4 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 7316837 = 1371907) (by norm_num)
theorem B4877891 : Blo 2167435 4877891 := bstep (se 1 (by rfl) ⟨3658418, by rfl⟩ : syracuseStep 4877891 = 7316837) B7316837
theorem B3251927 : Blo 2167435 3251927 := bstep (se 1 (by rfl) ⟨2438945, by rfl⟩ : syracuseStep 3251927 = 4877891) B4877891
theorem B2167951 : Blo 2167435 2167951 := bstep (se 1 (by rfl) ⟨1625963, by rfl⟩ : syracuseStep 2167951 = 3251927) B3251927
theorem B3251933 : Blo 2167435 3251933 := bbase (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) (by norm_num)
theorem B2167955 : Blo 2167435 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B4877909 : Blo 2167435 4877909 := bbase (se 8 (by rfl) ⟨28581, by rfl⟩ : syracuseStep 4877909 = 57163) (by norm_num)
theorem B3251939 : Blo 2167435 3251939 := bstep (se 1 (by rfl) ⟨2438954, by rfl⟩ : syracuseStep 3251939 = 4877909) B4877909
theorem B2167959 : Blo 2167435 2167959 := bstep (se 1 (by rfl) ⟨1625969, by rfl⟩ : syracuseStep 2167959 = 3251939) B3251939
theorem B4630213 : Blo 2167435 4630213 := bbase (se 4 (by rfl) ⟨434082, by rfl⟩ : syracuseStep 4630213 = 868165) (by norm_num)
theorem B6173617 : Blo 2167435 6173617 := bstep (se 2 (by rfl) ⟨2315106, by rfl⟩ : syracuseStep 6173617 = 4630213) B4630213
theorem B8231489 : Blo 2167435 8231489 := bstep (se 2 (by rfl) ⟨3086808, by rfl⟩ : syracuseStep 8231489 = 6173617) B6173617
theorem B5487659 : Blo 2167435 5487659 := bstep (se 1 (by rfl) ⟨4115744, by rfl⟩ : syracuseStep 5487659 = 8231489) B8231489
theorem B3658439 : Blo 2167435 3658439 := bstep (se 1 (by rfl) ⟨2743829, by rfl⟩ : syracuseStep 3658439 = 5487659) B5487659
theorem B2438959 : Blo 2167435 2438959 := bstep (se 1 (by rfl) ⟨1829219, by rfl⟩ : syracuseStep 2438959 = 3658439) B3658439
theorem B3251945 : Blo 2167435 3251945 := bstep (se 2 (by rfl) ⟨1219479, by rfl⟩ : syracuseStep 3251945 = 2438959) B2438959
theorem B2167963 : Blo 2167435 2167963 := bstep (se 1 (by rfl) ⟨1625972, by rfl⟩ : syracuseStep 2167963 = 3251945) B3251945
theorem B3906749 : Blo 2167435 3906749 := bbase (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) (by norm_num)
theorem B10417997 : Blo 2167435 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B27781325 : Blo 2167435 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B18520883 : Blo 2167435 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B12347255 : Blo 2167435 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B8231503 : Blo 2167435 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B10975337 : Blo 2167435 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B7316891 : Blo 2167435 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B4877927 : Blo 2167435 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B3251951 : Blo 2167435 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B2167967 : Blo 2167435 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B3251957 : Blo 2167435 3251957 := bbase (se 5 (by rfl) ⟨152435, by rfl⟩ : syracuseStep 3251957 = 304871) (by norm_num)
theorem B2167971 : Blo 2167435 2167971 := bstep (se 1 (by rfl) ⟨1625978, by rfl⟩ : syracuseStep 2167971 = 3251957) B3251957
theorem B3296333 : Blo 2167435 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B8790221 : Blo 2167435 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B5860147 : Blo 2167435 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B7813529 : Blo 2167435 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B5209019 : Blo 2167435 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B3472679 : Blo 2167435 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B9260477 : Blo 2167435 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B6173651 : Blo 2167435 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B4115767 : Blo 2167435 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B5487689 : Blo 2167435 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B3658459 : Blo 2167435 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B4877945 : Blo 2167435 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B3251963 : Blo 2167435 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B2167975 : Blo 2167435 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B2438977 : Blo 2167435 2438977 := bbase (se 2 (by rfl) ⟨914616, by rfl⟩ : syracuseStep 2438977 = 1829233) (by norm_num)
theorem B3251969 : Blo 2167435 3251969 := bstep (se 2 (by rfl) ⟨1219488, by rfl⟩ : syracuseStep 3251969 = 2438977) B2438977
theorem B2167979 : Blo 2167435 2167979 := bstep (se 1 (by rfl) ⟨1625984, by rfl⟩ : syracuseStep 2167979 = 3251969) B3251969
theorem B5487709 : Blo 2167435 5487709 := bbase (se 3 (by rfl) ⟨1028945, by rfl⟩ : syracuseStep 5487709 = 2057891) (by norm_num)
theorem B7316945 : Blo 2167435 7316945 := bstep (se 2 (by rfl) ⟨2743854, by rfl⟩ : syracuseStep 7316945 = 5487709) B5487709
theorem B4877963 : Blo 2167435 4877963 := bstep (se 1 (by rfl) ⟨3658472, by rfl⟩ : syracuseStep 4877963 = 7316945) B7316945
theorem B3251975 : Blo 2167435 3251975 := bstep (se 1 (by rfl) ⟨2438981, by rfl⟩ : syracuseStep 3251975 = 4877963) B4877963
theorem B2167983 : Blo 2167435 2167983 := bstep (se 1 (by rfl) ⟨1625987, by rfl⟩ : syracuseStep 2167983 = 3251975) B3251975
theorem B3251981 : Blo 2167435 3251981 := bbase (se 3 (by rfl) ⟨609746, by rfl⟩ : syracuseStep 3251981 = 1219493) (by norm_num)
theorem B2167987 : Blo 2167435 2167987 := bstep (se 1 (by rfl) ⟨1625990, by rfl⟩ : syracuseStep 2167987 = 3251981) B3251981
theorem B4877981 : Blo 2167435 4877981 := bbase (se 3 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 4877981 = 1829243) (by norm_num)
theorem B3251987 : Blo 2167435 3251987 := bstep (se 1 (by rfl) ⟨2438990, by rfl⟩ : syracuseStep 3251987 = 4877981) B4877981
theorem B2167991 : Blo 2167435 2167991 := bstep (se 1 (by rfl) ⟨1625993, by rfl⟩ : syracuseStep 2167991 = 3251987) B3251987
theorem B3658493 : Blo 2167435 3658493 := bbase (se 3 (by rfl) ⟨685967, by rfl⟩ : syracuseStep 3658493 = 1371935) (by norm_num)
theorem B2438995 : Blo 2167435 2438995 := bstep (se 1 (by rfl) ⟨1829246, by rfl⟩ : syracuseStep 2438995 = 3658493) B3658493
theorem B3251993 : Blo 2167435 3251993 := bstep (se 2 (by rfl) ⟨1219497, by rfl⟩ : syracuseStep 3251993 = 2438995) B2438995
theorem B2167995 : Blo 2167435 2167995 := bstep (se 1 (by rfl) ⟨1625996, by rfl⟩ : syracuseStep 2167995 = 3251993) B3251993
theorem B3472717 : Blo 2167435 3472717 := bbase (se 3 (by rfl) ⟨651134, by rfl⟩ : syracuseStep 3472717 = 1302269) (by norm_num)
theorem B4630289 : Blo 2167435 4630289 := bstep (se 2 (by rfl) ⟨1736358, by rfl⟩ : syracuseStep 4630289 = 3472717) B3472717
theorem B12347437 : Blo 2167435 12347437 := bstep (se 3 (by rfl) ⟨2315144, by rfl⟩ : syracuseStep 12347437 = 4630289) B4630289
theorem B16463249 : Blo 2167435 16463249 := bstep (se 2 (by rfl) ⟨6173718, by rfl⟩ : syracuseStep 16463249 = 12347437) B12347437
theorem B10975499 : Blo 2167435 10975499 := bstep (se 1 (by rfl) ⟨8231624, by rfl⟩ : syracuseStep 10975499 = 16463249) B16463249
theorem B7316999 : Blo 2167435 7316999 := bstep (se 1 (by rfl) ⟨5487749, by rfl⟩ : syracuseStep 7316999 = 10975499) B10975499
theorem B4877999 : Blo 2167435 4877999 := bstep (se 1 (by rfl) ⟨3658499, by rfl⟩ : syracuseStep 4877999 = 7316999) B7316999
theorem B3251999 : Blo 2167435 3251999 := bstep (se 1 (by rfl) ⟨2438999, by rfl⟩ : syracuseStep 3251999 = 4877999) B4877999
theorem B2167999 : Blo 2167435 2167999 := bstep (se 1 (by rfl) ⟨1625999, by rfl⟩ : syracuseStep 2167999 = 3251999) B3251999
theorem B3252005 : Blo 2167435 3252005 := bbase (se 4 (by rfl) ⟨304875, by rfl⟩ : syracuseStep 3252005 = 609751) (by norm_num)
theorem B2168003 : Blo 2167435 2168003 := bstep (se 1 (by rfl) ⟨1626002, by rfl⟩ : syracuseStep 2168003 = 3252005) B3252005
theorem B2743885 : Blo 2167435 2743885 := bbase (se 3 (by rfl) ⟨514478, by rfl⟩ : syracuseStep 2743885 = 1028957) (by norm_num)
theorem B3658513 : Blo 2167435 3658513 := bstep (se 2 (by rfl) ⟨1371942, by rfl⟩ : syracuseStep 3658513 = 2743885) B2743885
theorem B4878017 : Blo 2167435 4878017 := bstep (se 2 (by rfl) ⟨1829256, by rfl⟩ : syracuseStep 4878017 = 3658513) B3658513
theorem B3252011 : Blo 2167435 3252011 := bstep (se 1 (by rfl) ⟨2439008, by rfl⟩ : syracuseStep 3252011 = 4878017) B4878017
theorem B2168007 : Blo 2167435 2168007 := bstep (se 1 (by rfl) ⟨1626005, by rfl⟩ : syracuseStep 2168007 = 3252011) B3252011
theorem B2439013 : Blo 2167435 2439013 := bbase (se 4 (by rfl) ⟨228657, by rfl⟩ : syracuseStep 2439013 = 457315) (by norm_num)
theorem B3252017 : Blo 2167435 3252017 := bstep (se 2 (by rfl) ⟨1219506, by rfl⟩ : syracuseStep 3252017 = 2439013) B2439013
theorem B2168011 : Blo 2167435 2168011 := bstep (se 1 (by rfl) ⟨1626008, by rfl⟩ : syracuseStep 2168011 = 3252017) B3252017
theorem B6173765 : Blo 2167435 6173765 := bbase (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) (by norm_num)
theorem B4115843 : Blo 2167435 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B2743895 : Blo 2167435 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B7317053 : Blo 2167435 7317053 := bstep (se 3 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 7317053 = 2743895) B2743895
theorem B4878035 : Blo 2167435 4878035 := bstep (se 1 (by rfl) ⟨3658526, by rfl⟩ : syracuseStep 4878035 = 7317053) B7317053
theorem B3252023 : Blo 2167435 3252023 := bstep (se 1 (by rfl) ⟨2439017, by rfl⟩ : syracuseStep 3252023 = 4878035) B4878035
theorem B2168015 : Blo 2167435 2168015 := bstep (se 1 (by rfl) ⟨1626011, by rfl⟩ : syracuseStep 2168015 = 3252023) B3252023
theorem B3252029 : Blo 2167435 3252029 := bbase (se 3 (by rfl) ⟨609755, by rfl⟩ : syracuseStep 3252029 = 1219511) (by norm_num)
theorem B2168019 : Blo 2167435 2168019 := bstep (se 1 (by rfl) ⟨1626014, by rfl⟩ : syracuseStep 2168019 = 3252029) B3252029
theorem B4878053 : Blo 2167435 4878053 := bbase (se 4 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 4878053 = 914635) (by norm_num)
theorem B3252035 : Blo 2167435 3252035 := bstep (se 1 (by rfl) ⟨2439026, by rfl⟩ : syracuseStep 3252035 = 4878053) B4878053
theorem B2168023 : Blo 2167435 2168023 := bstep (se 1 (by rfl) ⟨1626017, by rfl⟩ : syracuseStep 2168023 = 3252035) B3252035
theorem B5487821 : Blo 2167435 5487821 := bbase (se 3 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 5487821 = 2057933) (by norm_num)
theorem B3658547 : Blo 2167435 3658547 := bstep (se 1 (by rfl) ⟨2743910, by rfl⟩ : syracuseStep 3658547 = 5487821) B5487821
theorem B2439031 : Blo 2167435 2439031 := bstep (se 1 (by rfl) ⟨1829273, by rfl⟩ : syracuseStep 2439031 = 3658547) B3658547
theorem B3252041 : Blo 2167435 3252041 := bstep (se 2 (by rfl) ⟨1219515, by rfl⟩ : syracuseStep 3252041 = 2439031) B2439031
theorem B2168027 : Blo 2167435 2168027 := bstep (se 1 (by rfl) ⟨1626020, by rfl⟩ : syracuseStep 2168027 = 3252041) B3252041
theorem B2604577 : Blo 2167435 2604577 := bbase (se 2 (by rfl) ⟨976716, by rfl⟩ : syracuseStep 2604577 = 1953433) (by norm_num)
theorem B3472769 : Blo 2167435 3472769 := bstep (se 2 (by rfl) ⟨1302288, by rfl⟩ : syracuseStep 3472769 = 2604577) B2604577
theorem B2315179 : Blo 2167435 2315179 := bstep (se 1 (by rfl) ⟨1736384, by rfl⟩ : syracuseStep 2315179 = 3472769) B3472769
theorem B3086905 : Blo 2167435 3086905 := bstep (se 2 (by rfl) ⟨1157589, by rfl⟩ : syracuseStep 3086905 = 2315179) B2315179
theorem B4115873 : Blo 2167435 4115873 := bstep (se 2 (by rfl) ⟨1543452, by rfl⟩ : syracuseStep 4115873 = 3086905) B3086905
theorem B10975661 : Blo 2167435 10975661 := bstep (se 3 (by rfl) ⟨2057936, by rfl⟩ : syracuseStep 10975661 = 4115873) B4115873
theorem B7317107 : Blo 2167435 7317107 := bstep (se 1 (by rfl) ⟨5487830, by rfl⟩ : syracuseStep 7317107 = 10975661) B10975661
theorem B4878071 : Blo 2167435 4878071 := bstep (se 1 (by rfl) ⟨3658553, by rfl⟩ : syracuseStep 4878071 = 7317107) B7317107
theorem B3252047 : Blo 2167435 3252047 := bstep (se 1 (by rfl) ⟨2439035, by rfl⟩ : syracuseStep 3252047 = 4878071) B4878071
theorem B2168031 : Blo 2167435 2168031 := bstep (se 1 (by rfl) ⟨1626023, by rfl⟩ : syracuseStep 2168031 = 3252047) B3252047
theorem B3252053 : Blo 2167435 3252053 := bbase (se 9 (by rfl) ⟨9527, by rfl⟩ : syracuseStep 3252053 = 19055) (by norm_num)
theorem B2168035 : Blo 2167435 2168035 := bstep (se 1 (by rfl) ⟨1626026, by rfl⟩ : syracuseStep 2168035 = 3252053) B3252053
theorem B40096853 : Blo 2167435 40096853 := bbase (se 8 (by rfl) ⟨234942, by rfl⟩ : syracuseStep 40096853 = 469885) (by norm_num)
theorem B26731235 : Blo 2167435 26731235 := bstep (se 1 (by rfl) ⟨20048426, by rfl⟩ : syracuseStep 26731235 = 40096853) B40096853
theorem B17820823 : Blo 2167435 17820823 := bstep (se 1 (by rfl) ⟨13365617, by rfl⟩ : syracuseStep 17820823 = 26731235) B26731235
theorem B23761097 : Blo 2167435 23761097 := bstep (se 2 (by rfl) ⟨8910411, by rfl⟩ : syracuseStep 23761097 = 17820823) B17820823
theorem B15840731 : Blo 2167435 15840731 := bstep (se 1 (by rfl) ⟨11880548, by rfl⟩ : syracuseStep 15840731 = 23761097) B23761097
theorem B42241949 : Blo 2167435 42241949 := bstep (se 3 (by rfl) ⟨7920365, by rfl⟩ : syracuseStep 42241949 = 15840731) B15840731
theorem B28161299 : Blo 2167435 28161299 := bstep (se 1 (by rfl) ⟨21120974, by rfl⟩ : syracuseStep 28161299 = 42241949) B42241949
theorem B18774199 : Blo 2167435 18774199 := bstep (se 1 (by rfl) ⟨14080649, by rfl⟩ : syracuseStep 18774199 = 28161299) B28161299
theorem B100129061 : Blo 2167435 100129061 := bstep (se 4 (by rfl) ⟨9387099, by rfl⟩ : syracuseStep 100129061 = 18774199) B18774199
theorem B66752707 : Blo 2167435 66752707 := bstep (se 1 (by rfl) ⟨50064530, by rfl⟩ : syracuseStep 66752707 = 100129061) B100129061
theorem B89003609 : Blo 2167435 89003609 := bstep (se 2 (by rfl) ⟨33376353, by rfl⟩ : syracuseStep 89003609 = 66752707) B66752707
theorem B59335739 : Blo 2167435 59335739 := bstep (se 1 (by rfl) ⟨44501804, by rfl⟩ : syracuseStep 59335739 = 89003609) B89003609
theorem B39557159 : Blo 2167435 39557159 := bstep (se 1 (by rfl) ⟨29667869, by rfl⟩ : syracuseStep 39557159 = 59335739) B59335739
theorem B26371439 : Blo 2167435 26371439 := bstep (se 1 (by rfl) ⟨19778579, by rfl⟩ : syracuseStep 26371439 = 39557159) B39557159
theorem B17580959 : Blo 2167435 17580959 := bstep (se 1 (by rfl) ⟨13185719, by rfl⟩ : syracuseStep 17580959 = 26371439) B26371439
theorem B11720639 : Blo 2167435 11720639 := bstep (se 1 (by rfl) ⟨8790479, by rfl⟩ : syracuseStep 11720639 = 17580959) B17580959
theorem B7813759 : Blo 2167435 7813759 := bstep (se 1 (by rfl) ⟨5860319, by rfl⟩ : syracuseStep 7813759 = 11720639) B11720639
theorem B10418345 : Blo 2167435 10418345 := bstep (se 2 (by rfl) ⟨3906879, by rfl⟩ : syracuseStep 10418345 = 7813759) B7813759
theorem B6945563 : Blo 2167435 6945563 := bstep (se 1 (by rfl) ⟨5209172, by rfl⟩ : syracuseStep 6945563 = 10418345) B10418345
theorem B4630375 : Blo 2167435 4630375 := bstep (se 1 (by rfl) ⟨3472781, by rfl⟩ : syracuseStep 4630375 = 6945563) B6945563
theorem B6173833 : Blo 2167435 6173833 := bstep (se 2 (by rfl) ⟨2315187, by rfl⟩ : syracuseStep 6173833 = 4630375) B4630375
theorem B8231777 : Blo 2167435 8231777 := bstep (se 2 (by rfl) ⟨3086916, by rfl⟩ : syracuseStep 8231777 = 6173833) B6173833
theorem B5487851 : Blo 2167435 5487851 := bstep (se 1 (by rfl) ⟨4115888, by rfl⟩ : syracuseStep 5487851 = 8231777) B8231777
theorem B3658567 : Blo 2167435 3658567 := bstep (se 1 (by rfl) ⟨2743925, by rfl⟩ : syracuseStep 3658567 = 5487851) B5487851
theorem B4878089 : Blo 2167435 4878089 := bstep (se 2 (by rfl) ⟨1829283, by rfl⟩ : syracuseStep 4878089 = 3658567) B3658567
theorem B3252059 : Blo 2167435 3252059 := bstep (se 1 (by rfl) ⟨2439044, by rfl⟩ : syracuseStep 3252059 = 4878089) B4878089
theorem B2168039 : Blo 2167435 2168039 := bstep (se 1 (by rfl) ⟨1626029, by rfl⟩ : syracuseStep 2168039 = 3252059) B3252059
theorem B2439049 : Blo 2167435 2439049 := bbase (se 2 (by rfl) ⟨914643, by rfl⟩ : syracuseStep 2439049 = 1829287) (by norm_num)
theorem B3252065 : Blo 2167435 3252065 := bstep (se 2 (by rfl) ⟨1219524, by rfl⟩ : syracuseStep 3252065 = 2439049) B2439049
theorem B2168043 : Blo 2167435 2168043 := bstep (se 1 (by rfl) ⟨1626032, by rfl⟩ : syracuseStep 2168043 = 3252065) B3252065
theorem B8344117 : Blo 2167435 8344117 := bbase (se 5 (by rfl) ⟨391130, by rfl⟩ : syracuseStep 8344117 = 782261) (by norm_num)
theorem B44501957 : Blo 2167435 44501957 := bstep (se 4 (by rfl) ⟨4172058, by rfl⟩ : syracuseStep 44501957 = 8344117) B8344117
theorem B29667971 : Blo 2167435 29667971 := bstep (se 1 (by rfl) ⟨22250978, by rfl⟩ : syracuseStep 29667971 = 44501957) B44501957
theorem B79114589 : Blo 2167435 79114589 := bstep (se 3 (by rfl) ⟨14833985, by rfl⟩ : syracuseStep 79114589 = 29667971) B29667971
theorem B52743059 : Blo 2167435 52743059 := bstep (se 1 (by rfl) ⟨39557294, by rfl⟩ : syracuseStep 52743059 = 79114589) B79114589
theorem B35162039 : Blo 2167435 35162039 := bstep (se 1 (by rfl) ⟨26371529, by rfl⟩ : syracuseStep 35162039 = 52743059) B52743059
theorem B93765437 : Blo 2167435 93765437 := bstep (se 3 (by rfl) ⟨17581019, by rfl⟩ : syracuseStep 93765437 = 35162039) B35162039
theorem B62510291 : Blo 2167435 62510291 := bstep (se 1 (by rfl) ⟨46882718, by rfl⟩ : syracuseStep 62510291 = 93765437) B93765437
theorem B41673527 : Blo 2167435 41673527 := bstep (se 1 (by rfl) ⟨31255145, by rfl⟩ : syracuseStep 41673527 = 62510291) B62510291
theorem B27782351 : Blo 2167435 27782351 := bstep (se 1 (by rfl) ⟨20836763, by rfl⟩ : syracuseStep 27782351 = 41673527) B41673527
theorem B18521567 : Blo 2167435 18521567 := bstep (se 1 (by rfl) ⟨13891175, by rfl⟩ : syracuseStep 18521567 = 27782351) B27782351
theorem B12347711 : Blo 2167435 12347711 := bstep (se 1 (by rfl) ⟨9260783, by rfl⟩ : syracuseStep 12347711 = 18521567) B18521567
theorem B8231807 : Blo 2167435 8231807 := bstep (se 1 (by rfl) ⟨6173855, by rfl⟩ : syracuseStep 8231807 = 12347711) B12347711
theorem B5487871 : Blo 2167435 5487871 := bstep (se 1 (by rfl) ⟨4115903, by rfl⟩ : syracuseStep 5487871 = 8231807) B8231807
theorem B7317161 : Blo 2167435 7317161 := bstep (se 2 (by rfl) ⟨2743935, by rfl⟩ : syracuseStep 7317161 = 5487871) B5487871
theorem B4878107 : Blo 2167435 4878107 := bstep (se 1 (by rfl) ⟨3658580, by rfl⟩ : syracuseStep 4878107 = 7317161) B7317161
theorem B3252071 : Blo 2167435 3252071 := bstep (se 1 (by rfl) ⟨2439053, by rfl⟩ : syracuseStep 3252071 = 4878107) B4878107
theorem B2168047 : Blo 2167435 2168047 := bstep (se 1 (by rfl) ⟨1626035, by rfl⟩ : syracuseStep 2168047 = 3252071) B3252071
theorem B3252077 : Blo 2167435 3252077 := bbase (se 3 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 3252077 = 1219529) (by norm_num)
theorem B2168051 : Blo 2167435 2168051 := bstep (se 1 (by rfl) ⟨1626038, by rfl⟩ : syracuseStep 2168051 = 3252077) B3252077
theorem B4878125 : Blo 2167435 4878125 := bbase (se 3 (by rfl) ⟨914648, by rfl⟩ : syracuseStep 4878125 = 1829297) (by norm_num)
theorem B3252083 : Blo 2167435 3252083 := bstep (se 1 (by rfl) ⟨2439062, by rfl⟩ : syracuseStep 3252083 = 4878125) B4878125
theorem B2168055 : Blo 2167435 2168055 := bstep (se 1 (by rfl) ⟨1626041, by rfl⟩ : syracuseStep 2168055 = 3252083) B3252083
theorem B9260837 : Blo 2167435 9260837 := bbase (se 4 (by rfl) ⟨868203, by rfl⟩ : syracuseStep 9260837 = 1736407) (by norm_num)
theorem B6173891 : Blo 2167435 6173891 := bstep (se 1 (by rfl) ⟨4630418, by rfl⟩ : syracuseStep 6173891 = 9260837) B9260837
theorem B4115927 : Blo 2167435 4115927 := bstep (se 1 (by rfl) ⟨3086945, by rfl⟩ : syracuseStep 4115927 = 6173891) B6173891
theorem B2743951 : Blo 2167435 2743951 := bstep (se 1 (by rfl) ⟨2057963, by rfl⟩ : syracuseStep 2743951 = 4115927) B4115927
theorem B3658601 : Blo 2167435 3658601 := bstep (se 2 (by rfl) ⟨1371975, by rfl⟩ : syracuseStep 3658601 = 2743951) B2743951
theorem B2439067 : Blo 2167435 2439067 := bstep (se 1 (by rfl) ⟨1829300, by rfl⟩ : syracuseStep 2439067 = 3658601) B3658601
theorem B3252089 : Blo 2167435 3252089 := bstep (se 2 (by rfl) ⟨1219533, by rfl⟩ : syracuseStep 3252089 = 2439067) B2439067
theorem B2168059 : Blo 2167435 2168059 := bstep (se 1 (by rfl) ⟨1626044, by rfl⟩ : syracuseStep 2168059 = 3252089) B3252089
theorem B5209229 : Blo 2167435 5209229 := bbase (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) (by norm_num)
theorem B13891277 : Blo 2167435 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B37043405 : Blo 2167435 37043405 := bstep (se 3 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 37043405 = 13891277) B13891277
theorem B24695603 : Blo 2167435 24695603 := bstep (se 1 (by rfl) ⟨18521702, by rfl⟩ : syracuseStep 24695603 = 37043405) B37043405
theorem B16463735 : Blo 2167435 16463735 := bstep (se 1 (by rfl) ⟨12347801, by rfl⟩ : syracuseStep 16463735 = 24695603) B24695603
theorem B10975823 : Blo 2167435 10975823 := bstep (se 1 (by rfl) ⟨8231867, by rfl⟩ : syracuseStep 10975823 = 16463735) B16463735
theorem B7317215 : Blo 2167435 7317215 := bstep (se 1 (by rfl) ⟨5487911, by rfl⟩ : syracuseStep 7317215 = 10975823) B10975823
theorem B4878143 : Blo 2167435 4878143 := bstep (se 1 (by rfl) ⟨3658607, by rfl⟩ : syracuseStep 4878143 = 7317215) B7317215
theorem B3252095 : Blo 2167435 3252095 := bstep (se 1 (by rfl) ⟨2439071, by rfl⟩ : syracuseStep 3252095 = 4878143) B4878143
theorem B2168063 : Blo 2167435 2168063 := bstep (se 1 (by rfl) ⟨1626047, by rfl⟩ : syracuseStep 2168063 = 3252095) B3252095
theorem B3252101 : Blo 2167435 3252101 := bbase (se 4 (by rfl) ⟨304884, by rfl⟩ : syracuseStep 3252101 = 609769) (by norm_num)
theorem B2168067 : Blo 2167435 2168067 := bstep (se 1 (by rfl) ⟨1626050, by rfl⟩ : syracuseStep 2168067 = 3252101) B3252101
theorem B3658621 : Blo 2167435 3658621 := bbase (se 3 (by rfl) ⟨685991, by rfl⟩ : syracuseStep 3658621 = 1371983) (by norm_num)
theorem B4878161 : Blo 2167435 4878161 := bstep (se 2 (by rfl) ⟨1829310, by rfl⟩ : syracuseStep 4878161 = 3658621) B3658621
theorem B3252107 : Blo 2167435 3252107 := bstep (se 1 (by rfl) ⟨2439080, by rfl⟩ : syracuseStep 3252107 = 4878161) B4878161
theorem B2168071 : Blo 2167435 2168071 := bstep (se 1 (by rfl) ⟨1626053, by rfl⟩ : syracuseStep 2168071 = 3252107) B3252107
theorem B2439085 : Blo 2167435 2439085 := bbase (se 3 (by rfl) ⟨457328, by rfl⟩ : syracuseStep 2439085 = 914657) (by norm_num)
theorem B3252113 : Blo 2167435 3252113 := bstep (se 2 (by rfl) ⟨1219542, by rfl⟩ : syracuseStep 3252113 = 2439085) B2439085
theorem B2168075 : Blo 2167435 2168075 := bstep (se 1 (by rfl) ⟨1626056, by rfl⟩ : syracuseStep 2168075 = 3252113) B3252113
theorem B7317269 : Blo 2167435 7317269 := bbase (se 6 (by rfl) ⟨171498, by rfl⟩ : syracuseStep 7317269 = 342997) (by norm_num)
theorem B4878179 : Blo 2167435 4878179 := bstep (se 1 (by rfl) ⟨3658634, by rfl⟩ : syracuseStep 4878179 = 7317269) B7317269
theorem B3252119 : Blo 2167435 3252119 := bstep (se 1 (by rfl) ⟨2439089, by rfl⟩ : syracuseStep 3252119 = 4878179) B4878179
theorem B2168079 : Blo 2167435 2168079 := bstep (se 1 (by rfl) ⟨1626059, by rfl⟩ : syracuseStep 2168079 = 3252119) B3252119
theorem B3252125 : Blo 2167435 3252125 := bbase (se 3 (by rfl) ⟨609773, by rfl⟩ : syracuseStep 3252125 = 1219547) (by norm_num)
theorem B2168083 : Blo 2167435 2168083 := bstep (se 1 (by rfl) ⟨1626062, by rfl⟩ : syracuseStep 2168083 = 3252125) B3252125
theorem B4878197 : Blo 2167435 4878197 := bbase (se 5 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 4878197 = 457331) (by norm_num)
theorem B3252131 : Blo 2167435 3252131 := bstep (se 1 (by rfl) ⟨2439098, by rfl⟩ : syracuseStep 3252131 = 4878197) B4878197
theorem B2168087 : Blo 2167435 2168087 := bstep (se 1 (by rfl) ⟨1626065, by rfl⟩ : syracuseStep 2168087 = 3252131) B3252131
theorem B3906973 : Blo 2167435 3906973 := bbase (se 3 (by rfl) ⟨732557, by rfl⟩ : syracuseStep 3906973 = 1465115) (by norm_num)
theorem B20837189 : Blo 2167435 20837189 := bstep (se 4 (by rfl) ⟨1953486, by rfl⟩ : syracuseStep 20837189 = 3906973) B3906973
theorem B13891459 : Blo 2167435 13891459 := bstep (se 1 (by rfl) ⟨10418594, by rfl⟩ : syracuseStep 13891459 = 20837189) B20837189
theorem B18521945 : Blo 2167435 18521945 := bstep (se 2 (by rfl) ⟨6945729, by rfl⟩ : syracuseStep 18521945 = 13891459) B13891459
theorem B12347963 : Blo 2167435 12347963 := bstep (se 1 (by rfl) ⟨9260972, by rfl⟩ : syracuseStep 12347963 = 18521945) B18521945
theorem B8231975 : Blo 2167435 8231975 := bstep (se 1 (by rfl) ⟨6173981, by rfl⟩ : syracuseStep 8231975 = 12347963) B12347963
theorem B5487983 : Blo 2167435 5487983 := bstep (se 1 (by rfl) ⟨4115987, by rfl⟩ : syracuseStep 5487983 = 8231975) B8231975
theorem B3658655 : Blo 2167435 3658655 := bstep (se 1 (by rfl) ⟨2743991, by rfl⟩ : syracuseStep 3658655 = 5487983) B5487983
theorem B2439103 : Blo 2167435 2439103 := bstep (se 1 (by rfl) ⟨1829327, by rfl⟩ : syracuseStep 2439103 = 3658655) B3658655
theorem B3252137 : Blo 2167435 3252137 := bstep (se 2 (by rfl) ⟨1219551, by rfl⟩ : syracuseStep 3252137 = 2439103) B2439103
theorem B2168091 : Blo 2167435 2168091 := bstep (se 1 (by rfl) ⟨1626068, by rfl⟩ : syracuseStep 2168091 = 3252137) B3252137
theorem B8231989 : Blo 2167435 8231989 := bbase (se 5 (by rfl) ⟨385874, by rfl⟩ : syracuseStep 8231989 = 771749) (by norm_num)
theorem B10975985 : Blo 2167435 10975985 := bstep (se 2 (by rfl) ⟨4115994, by rfl⟩ : syracuseStep 10975985 = 8231989) B8231989
theorem B7317323 : Blo 2167435 7317323 := bstep (se 1 (by rfl) ⟨5487992, by rfl⟩ : syracuseStep 7317323 = 10975985) B10975985
theorem B4878215 : Blo 2167435 4878215 := bstep (se 1 (by rfl) ⟨3658661, by rfl⟩ : syracuseStep 4878215 = 7317323) B7317323
theorem B3252143 : Blo 2167435 3252143 := bstep (se 1 (by rfl) ⟨2439107, by rfl⟩ : syracuseStep 3252143 = 4878215) B4878215
theorem B2168095 : Blo 2167435 2168095 := bstep (se 1 (by rfl) ⟨1626071, by rfl⟩ : syracuseStep 2168095 = 3252143) B3252143
theorem B3252149 : Blo 2167435 3252149 := bbase (se 5 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 3252149 = 304889) (by norm_num)
theorem B2168099 : Blo 2167435 2168099 := bstep (se 1 (by rfl) ⟨1626074, by rfl⟩ : syracuseStep 2168099 = 3252149) B3252149
theorem B5488013 : Blo 2167435 5488013 := bbase (se 3 (by rfl) ⟨1029002, by rfl⟩ : syracuseStep 5488013 = 2058005) (by norm_num)
theorem B3658675 : Blo 2167435 3658675 := bstep (se 1 (by rfl) ⟨2744006, by rfl⟩ : syracuseStep 3658675 = 5488013) B5488013
theorem B4878233 : Blo 2167435 4878233 := bstep (se 2 (by rfl) ⟨1829337, by rfl⟩ : syracuseStep 4878233 = 3658675) B3658675
theorem B3252155 : Blo 2167435 3252155 := bstep (se 1 (by rfl) ⟨2439116, by rfl⟩ : syracuseStep 3252155 = 4878233) B4878233
theorem B2168103 : Blo 2167435 2168103 := bstep (se 1 (by rfl) ⟨1626077, by rfl⟩ : syracuseStep 2168103 = 3252155) B3252155
theorem B2439121 : Blo 2167435 2439121 := bbase (se 2 (by rfl) ⟨914670, by rfl⟩ : syracuseStep 2439121 = 1829341) (by norm_num)
theorem B3252161 : Blo 2167435 3252161 := bstep (se 2 (by rfl) ⟨1219560, by rfl⟩ : syracuseStep 3252161 = 2439121) B2439121
theorem B2168107 : Blo 2167435 2168107 := bstep (se 1 (by rfl) ⟨1626080, by rfl⟩ : syracuseStep 2168107 = 3252161) B3252161
theorem B2604673 : Blo 2167435 2604673 := bbase (se 2 (by rfl) ⟨976752, by rfl⟩ : syracuseStep 2604673 = 1953505) (by norm_num)
theorem B3472897 : Blo 2167435 3472897 := bstep (se 2 (by rfl) ⟨1302336, by rfl⟩ : syracuseStep 3472897 = 2604673) B2604673
theorem B4630529 : Blo 2167435 4630529 := bstep (se 2 (by rfl) ⟨1736448, by rfl⟩ : syracuseStep 4630529 = 3472897) B3472897
theorem B3087019 : Blo 2167435 3087019 := bstep (se 1 (by rfl) ⟨2315264, by rfl⟩ : syracuseStep 3087019 = 4630529) B4630529
theorem B4116025 : Blo 2167435 4116025 := bstep (se 2 (by rfl) ⟨1543509, by rfl⟩ : syracuseStep 4116025 = 3087019) B3087019
theorem B5488033 : Blo 2167435 5488033 := bstep (se 2 (by rfl) ⟨2058012, by rfl⟩ : syracuseStep 5488033 = 4116025) B4116025
theorem B7317377 : Blo 2167435 7317377 := bstep (se 2 (by rfl) ⟨2744016, by rfl⟩ : syracuseStep 7317377 = 5488033) B5488033
theorem B4878251 : Blo 2167435 4878251 := bstep (se 1 (by rfl) ⟨3658688, by rfl⟩ : syracuseStep 4878251 = 7317377) B7317377
theorem B3252167 : Blo 2167435 3252167 := bstep (se 1 (by rfl) ⟨2439125, by rfl⟩ : syracuseStep 3252167 = 4878251) B4878251
theorem B2168111 : Blo 2167435 2168111 := bstep (se 1 (by rfl) ⟨1626083, by rfl⟩ : syracuseStep 2168111 = 3252167) B3252167
theorem B3252173 : Blo 2167435 3252173 := bbase (se 3 (by rfl) ⟨609782, by rfl⟩ : syracuseStep 3252173 = 1219565) (by norm_num)
theorem B2168115 : Blo 2167435 2168115 := bstep (se 1 (by rfl) ⟨1626086, by rfl⟩ : syracuseStep 2168115 = 3252173) B3252173
theorem B4878269 : Blo 2167435 4878269 := bbase (se 3 (by rfl) ⟨914675, by rfl⟩ : syracuseStep 4878269 = 1829351) (by norm_num)
theorem B3252179 : Blo 2167435 3252179 := bstep (se 1 (by rfl) ⟨2439134, by rfl⟩ : syracuseStep 3252179 = 4878269) B4878269
theorem B2168119 : Blo 2167435 2168119 := bstep (se 1 (by rfl) ⟨1626089, by rfl⟩ : syracuseStep 2168119 = 3252179) B3252179
theorem B3658709 : Blo 2167435 3658709 := bbase (se 7 (by rfl) ⟨42875, by rfl⟩ : syracuseStep 3658709 = 85751) (by norm_num)
theorem B2439139 : Blo 2167435 2439139 := bstep (se 1 (by rfl) ⟨1829354, by rfl⟩ : syracuseStep 2439139 = 3658709) B3658709
theorem B3252185 : Blo 2167435 3252185 := bstep (se 2 (by rfl) ⟨1219569, by rfl⟩ : syracuseStep 3252185 = 2439139) B2439139
theorem B2168123 : Blo 2167435 2168123 := bstep (se 1 (by rfl) ⟨1626092, by rfl⟩ : syracuseStep 2168123 = 3252185) B3252185
theorem B9261125 : Blo 2167435 9261125 := bbase (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) (by norm_num)
theorem B6174083 : Blo 2167435 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B16464221 : Blo 2167435 16464221 := bstep (se 3 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 16464221 = 6174083) B6174083
theorem B10976147 : Blo 2167435 10976147 := bstep (se 1 (by rfl) ⟨8232110, by rfl⟩ : syracuseStep 10976147 = 16464221) B16464221
theorem B7317431 : Blo 2167435 7317431 := bstep (se 1 (by rfl) ⟨5488073, by rfl⟩ : syracuseStep 7317431 = 10976147) B10976147
theorem B4878287 : Blo 2167435 4878287 := bstep (se 1 (by rfl) ⟨3658715, by rfl⟩ : syracuseStep 4878287 = 7317431) B7317431
theorem B3252191 : Blo 2167435 3252191 := bstep (se 1 (by rfl) ⟨2439143, by rfl⟩ : syracuseStep 3252191 = 4878287) B4878287
theorem B2168127 : Blo 2167435 2168127 := bstep (se 1 (by rfl) ⟨1626095, by rfl⟩ : syracuseStep 2168127 = 3252191) B3252191
theorem B3252197 : Blo 2167435 3252197 := bbase (se 4 (by rfl) ⟨304893, by rfl⟩ : syracuseStep 3252197 = 609787) (by norm_num)
theorem B2168131 : Blo 2167435 2168131 := bstep (se 1 (by rfl) ⟨1626098, by rfl⟩ : syracuseStep 2168131 = 3252197) B3252197
theorem B8790869 : Blo 2167435 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B23442317 : Blo 2167435 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B15628211 : Blo 2167435 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B10418807 : Blo 2167435 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B6945871 : Blo 2167435 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B9261161 : Blo 2167435 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B6174107 : Blo 2167435 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B4116071 : Blo 2167435 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B2744047 : Blo 2167435 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B3658729 : Blo 2167435 3658729 := bstep (se 2 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 3658729 = 2744047) B2744047
theorem B4878305 : Blo 2167435 4878305 := bstep (se 2 (by rfl) ⟨1829364, by rfl⟩ : syracuseStep 4878305 = 3658729) B3658729
theorem B3252203 : Blo 2167435 3252203 := bstep (se 1 (by rfl) ⟨2439152, by rfl⟩ : syracuseStep 3252203 = 4878305) B4878305
theorem B2168135 : Blo 2167435 2168135 := bstep (se 1 (by rfl) ⟨1626101, by rfl⟩ : syracuseStep 2168135 = 3252203) B3252203
theorem B2439157 : Blo 2167435 2439157 := bbase (se 5 (by rfl) ⟨114335, by rfl⟩ : syracuseStep 2439157 = 228671) (by norm_num)
theorem B3252209 : Blo 2167435 3252209 := bstep (se 2 (by rfl) ⟨1219578, by rfl⟩ : syracuseStep 3252209 = 2439157) B2439157
theorem B2168139 : Blo 2167435 2168139 := bstep (se 1 (by rfl) ⟨1626104, by rfl⟩ : syracuseStep 2168139 = 3252209) B3252209
theorem B2744057 : Blo 2167435 2744057 := bbase (se 2 (by rfl) ⟨1029021, by rfl⟩ : syracuseStep 2744057 = 2058043) (by norm_num)
theorem B7317485 : Blo 2167435 7317485 := bstep (se 3 (by rfl) ⟨1372028, by rfl⟩ : syracuseStep 7317485 = 2744057) B2744057
theorem B4878323 : Blo 2167435 4878323 := bstep (se 1 (by rfl) ⟨3658742, by rfl⟩ : syracuseStep 4878323 = 7317485) B7317485
theorem B3252215 : Blo 2167435 3252215 := bstep (se 1 (by rfl) ⟨2439161, by rfl⟩ : syracuseStep 3252215 = 4878323) B4878323
theorem B2168143 : Blo 2167435 2168143 := bstep (se 1 (by rfl) ⟨1626107, by rfl⟩ : syracuseStep 2168143 = 3252215) B3252215
theorem B3252221 : Blo 2167435 3252221 := bbase (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) (by norm_num)
theorem B2168147 : Blo 2167435 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B4878341 : Blo 2167435 4878341 := bbase (se 4 (by rfl) ⟨457344, by rfl⟩ : syracuseStep 4878341 = 914689) (by norm_num)
theorem B3252227 : Blo 2167435 3252227 := bstep (se 1 (by rfl) ⟨2439170, by rfl⟩ : syracuseStep 3252227 = 4878341) B4878341
theorem B2168151 : Blo 2167435 2168151 := bstep (se 1 (by rfl) ⟨1626113, by rfl⟩ : syracuseStep 2168151 = 3252227) B3252227
theorem B4116109 : Blo 2167435 4116109 := bbase (se 3 (by rfl) ⟨771770, by rfl⟩ : syracuseStep 4116109 = 1543541) (by norm_num)
theorem B5488145 : Blo 2167435 5488145 := bstep (se 2 (by rfl) ⟨2058054, by rfl⟩ : syracuseStep 5488145 = 4116109) B4116109
theorem B3658763 : Blo 2167435 3658763 := bstep (se 1 (by rfl) ⟨2744072, by rfl⟩ : syracuseStep 3658763 = 5488145) B5488145
theorem B2439175 : Blo 2167435 2439175 := bstep (se 1 (by rfl) ⟨1829381, by rfl⟩ : syracuseStep 2439175 = 3658763) B3658763
theorem B3252233 : Blo 2167435 3252233 := bstep (se 2 (by rfl) ⟨1219587, by rfl⟩ : syracuseStep 3252233 = 2439175) B2439175
theorem B2168155 : Blo 2167435 2168155 := bstep (se 1 (by rfl) ⟨1626116, by rfl⟩ : syracuseStep 2168155 = 3252233) B3252233
theorem B10976309 : Blo 2167435 10976309 := bbase (se 5 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 10976309 = 1029029) (by norm_num)
theorem B7317539 : Blo 2167435 7317539 := bstep (se 1 (by rfl) ⟨5488154, by rfl⟩ : syracuseStep 7317539 = 10976309) B10976309
theorem B4878359 : Blo 2167435 4878359 := bstep (se 1 (by rfl) ⟨3658769, by rfl⟩ : syracuseStep 4878359 = 7317539) B7317539
theorem B3252239 : Blo 2167435 3252239 := bstep (se 1 (by rfl) ⟨2439179, by rfl⟩ : syracuseStep 3252239 = 4878359) B4878359
theorem B2168159 : Blo 2167435 2168159 := bstep (se 1 (by rfl) ⟨1626119, by rfl⟩ : syracuseStep 2168159 = 3252239) B3252239
theorem B3252245 : Blo 2167435 3252245 := bbase (se 6 (by rfl) ⟨76224, by rfl⟩ : syracuseStep 3252245 = 152449) (by norm_num)
theorem B2168163 : Blo 2167435 2168163 := bstep (se 1 (by rfl) ⟨1626122, by rfl⟩ : syracuseStep 2168163 = 3252245) B3252245
theorem B35163989 : Blo 2167435 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B23442659 : Blo 2167435 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B15628439 : Blo 2167435 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B10418959 : Blo 2167435 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B13891945 : Blo 2167435 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B18522593 : Blo 2167435 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B12348395 : Blo 2167435 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B8232263 : Blo 2167435 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B5488175 : Blo 2167435 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B3658783 : Blo 2167435 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B4878377 : Blo 2167435 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B3252251 : Blo 2167435 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B2168167 : Blo 2167435 2168167 := bstep (se 1 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 2168167 = 3252251) B3252251
theorem B2439193 : Blo 2167435 2439193 := bbase (se 2 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 2439193 = 1829395) (by norm_num)
theorem B3252257 : Blo 2167435 3252257 := bstep (se 2 (by rfl) ⟨1219596, by rfl⟩ : syracuseStep 3252257 = 2439193) B2439193
theorem B2168171 : Blo 2167435 2168171 := bstep (se 1 (by rfl) ⟨1626128, by rfl⟩ : syracuseStep 2168171 = 3252257) B3252257
theorem B8232293 : Blo 2167435 8232293 := bbase (se 4 (by rfl) ⟨771777, by rfl⟩ : syracuseStep 8232293 = 1543555) (by norm_num)
theorem B5488195 : Blo 2167435 5488195 := bstep (se 1 (by rfl) ⟨4116146, by rfl⟩ : syracuseStep 5488195 = 8232293) B8232293
theorem B7317593 : Blo 2167435 7317593 := bstep (se 2 (by rfl) ⟨2744097, by rfl⟩ : syracuseStep 7317593 = 5488195) B5488195
theorem B4878395 : Blo 2167435 4878395 := bstep (se 1 (by rfl) ⟨3658796, by rfl⟩ : syracuseStep 4878395 = 7317593) B7317593
theorem B3252263 : Blo 2167435 3252263 := bstep (se 1 (by rfl) ⟨2439197, by rfl⟩ : syracuseStep 3252263 = 4878395) B4878395
theorem B2168175 : Blo 2167435 2168175 := bstep (se 1 (by rfl) ⟨1626131, by rfl⟩ : syracuseStep 2168175 = 3252263) B3252263
theorem B3252269 : Blo 2167435 3252269 := bbase (se 3 (by rfl) ⟨609800, by rfl⟩ : syracuseStep 3252269 = 1219601) (by norm_num)
theorem B2168179 : Blo 2167435 2168179 := bstep (se 1 (by rfl) ⟨1626134, by rfl⟩ : syracuseStep 2168179 = 3252269) B3252269
theorem B4878413 : Blo 2167435 4878413 := bbase (se 3 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 4878413 = 1829405) (by norm_num)
theorem B3252275 : Blo 2167435 3252275 := bstep (se 1 (by rfl) ⟨2439206, by rfl⟩ : syracuseStep 3252275 = 4878413) B4878413
theorem B2168183 : Blo 2167435 2168183 := bstep (se 1 (by rfl) ⟨1626137, by rfl⟩ : syracuseStep 2168183 = 3252275) B3252275
theorem B2744113 : Blo 2167435 2744113 := bbase (se 2 (by rfl) ⟨1029042, by rfl⟩ : syracuseStep 2744113 = 2058085) (by norm_num)
theorem B3658817 : Blo 2167435 3658817 := bstep (se 2 (by rfl) ⟨1372056, by rfl⟩ : syracuseStep 3658817 = 2744113) B2744113
theorem B2439211 : Blo 2167435 2439211 := bstep (se 1 (by rfl) ⟨1829408, by rfl⟩ : syracuseStep 2439211 = 3658817) B3658817
theorem B3252281 : Blo 2167435 3252281 := bstep (se 2 (by rfl) ⟨1219605, by rfl⟩ : syracuseStep 3252281 = 2439211) B2439211
theorem B2168187 : Blo 2167435 2168187 := bstep (se 1 (by rfl) ⟨1626140, by rfl⟩ : syracuseStep 2168187 = 3252281) B3252281
theorem B2930365 : Blo 2167435 2930365 := bbase (se 3 (by rfl) ⟨549443, by rfl⟩ : syracuseStep 2930365 = 1098887) (by norm_num)
theorem B3907153 : Blo 2167435 3907153 := bstep (se 2 (by rfl) ⟨1465182, by rfl⟩ : syracuseStep 3907153 = 2930365) B2930365
theorem B5209537 : Blo 2167435 5209537 := bstep (se 2 (by rfl) ⟨1953576, by rfl⟩ : syracuseStep 5209537 = 3907153) B3907153
theorem B6946049 : Blo 2167435 6946049 := bstep (se 2 (by rfl) ⟨2604768, by rfl⟩ : syracuseStep 6946049 = 5209537) B5209537
theorem B4630699 : Blo 2167435 4630699 := bstep (se 1 (by rfl) ⟨3473024, by rfl⟩ : syracuseStep 4630699 = 6946049) B6946049
theorem B24697061 : Blo 2167435 24697061 := bstep (se 4 (by rfl) ⟨2315349, by rfl⟩ : syracuseStep 24697061 = 4630699) B4630699
theorem B16464707 : Blo 2167435 16464707 := bstep (se 1 (by rfl) ⟨12348530, by rfl⟩ : syracuseStep 16464707 = 24697061) B24697061
theorem B10976471 : Blo 2167435 10976471 := bstep (se 1 (by rfl) ⟨8232353, by rfl⟩ : syracuseStep 10976471 = 16464707) B16464707
theorem B7317647 : Blo 2167435 7317647 := bstep (se 1 (by rfl) ⟨5488235, by rfl⟩ : syracuseStep 7317647 = 10976471) B10976471
theorem B4878431 : Blo 2167435 4878431 := bstep (se 1 (by rfl) ⟨3658823, by rfl⟩ : syracuseStep 4878431 = 7317647) B7317647
theorem B3252287 : Blo 2167435 3252287 := bstep (se 1 (by rfl) ⟨2439215, by rfl⟩ : syracuseStep 3252287 = 4878431) B4878431
theorem B2168191 : Blo 2167435 2168191 := bstep (se 1 (by rfl) ⟨1626143, by rfl⟩ : syracuseStep 2168191 = 3252287) B3252287
theorem B3252293 : Blo 2167435 3252293 := bbase (se 4 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 3252293 = 609805) (by norm_num)
theorem B2168195 : Blo 2167435 2168195 := bstep (se 1 (by rfl) ⟨1626146, by rfl⟩ : syracuseStep 2168195 = 3252293) B3252293
theorem B3658837 : Blo 2167435 3658837 := bbase (se 8 (by rfl) ⟨21438, by rfl⟩ : syracuseStep 3658837 = 42877) (by norm_num)
theorem B4878449 : Blo 2167435 4878449 := bstep (se 2 (by rfl) ⟨1829418, by rfl⟩ : syracuseStep 4878449 = 3658837) B3658837
theorem B3252299 : Blo 2167435 3252299 := bstep (se 1 (by rfl) ⟨2439224, by rfl⟩ : syracuseStep 3252299 = 4878449) B4878449
theorem B2168199 : Blo 2167435 2168199 := bstep (se 1 (by rfl) ⟨1626149, by rfl⟩ : syracuseStep 2168199 = 3252299) B3252299
theorem B2439229 : Blo 2167435 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B3252305 : Blo 2167435 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B2168203 : Blo 2167435 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B7317701 : Blo 2167435 7317701 := bbase (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) (by norm_num)
theorem B4878467 : Blo 2167435 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B3252311 : Blo 2167435 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B2168207 : Blo 2167435 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B3252317 : Blo 2167435 3252317 := bbase (se 3 (by rfl) ⟨609809, by rfl⟩ : syracuseStep 3252317 = 1219619) (by norm_num)
theorem B2168211 : Blo 2167435 2168211 := bstep (se 1 (by rfl) ⟨1626158, by rfl⟩ : syracuseStep 2168211 = 3252317) B3252317
theorem B4878485 : Blo 2167435 4878485 := bbase (se 6 (by rfl) ⟨114339, by rfl⟩ : syracuseStep 4878485 = 228679) (by norm_num)
theorem B3252323 : Blo 2167435 3252323 := bstep (se 1 (by rfl) ⟨2439242, by rfl⟩ : syracuseStep 3252323 = 4878485) B4878485
theorem B2168215 : Blo 2167435 2168215 := bstep (se 1 (by rfl) ⟨1626161, by rfl⟩ : syracuseStep 2168215 = 3252323) B3252323
theorem B3087173 : Blo 2167435 3087173 := bbase (se 4 (by rfl) ⟨289422, by rfl⟩ : syracuseStep 3087173 = 578845) (by norm_num)
theorem B8232461 : Blo 2167435 8232461 := bstep (se 3 (by rfl) ⟨1543586, by rfl⟩ : syracuseStep 8232461 = 3087173) B3087173
theorem B5488307 : Blo 2167435 5488307 := bstep (se 1 (by rfl) ⟨4116230, by rfl⟩ : syracuseStep 5488307 = 8232461) B8232461
theorem B3658871 : Blo 2167435 3658871 := bstep (se 1 (by rfl) ⟨2744153, by rfl⟩ : syracuseStep 3658871 = 5488307) B5488307
theorem B2439247 : Blo 2167435 2439247 := bstep (se 1 (by rfl) ⟨1829435, by rfl⟩ : syracuseStep 2439247 = 3658871) B3658871
theorem B3252329 : Blo 2167435 3252329 := bstep (se 2 (by rfl) ⟨1219623, by rfl⟩ : syracuseStep 3252329 = 2439247) B2439247
theorem B2168219 : Blo 2167435 2168219 := bstep (se 1 (by rfl) ⟨1626164, by rfl⟩ : syracuseStep 2168219 = 3252329) B3252329
theorem B66758357 : Blo 2167435 66758357 := bbase (se 7 (by rfl) ⟨782324, by rfl⟩ : syracuseStep 66758357 = 1564649) (by norm_num)
theorem B44505571 : Blo 2167435 44505571 := bstep (se 1 (by rfl) ⟨33379178, by rfl⟩ : syracuseStep 44505571 = 66758357) B66758357
theorem B59340761 : Blo 2167435 59340761 := bstep (se 2 (by rfl) ⟨22252785, by rfl⟩ : syracuseStep 59340761 = 44505571) B44505571
theorem B39560507 : Blo 2167435 39560507 := bstep (se 1 (by rfl) ⟨29670380, by rfl⟩ : syracuseStep 39560507 = 59340761) B59340761
theorem B26373671 : Blo 2167435 26373671 := bstep (se 1 (by rfl) ⟨19780253, by rfl⟩ : syracuseStep 26373671 = 39560507) B39560507
theorem B17582447 : Blo 2167435 17582447 := bstep (se 1 (by rfl) ⟨13186835, by rfl⟩ : syracuseStep 17582447 = 26373671) B26373671
theorem B46886525 : Blo 2167435 46886525 := bstep (se 3 (by rfl) ⟨8791223, by rfl⟩ : syracuseStep 46886525 = 17582447) B17582447
theorem B31257683 : Blo 2167435 31257683 := bstep (se 1 (by rfl) ⟨23443262, by rfl⟩ : syracuseStep 31257683 = 46886525) B46886525
theorem B20838455 : Blo 2167435 20838455 := bstep (se 1 (by rfl) ⟨15628841, by rfl⟩ : syracuseStep 20838455 = 31257683) B31257683
theorem B13892303 : Blo 2167435 13892303 := bstep (se 1 (by rfl) ⟨10419227, by rfl⟩ : syracuseStep 13892303 = 20838455) B20838455
theorem B9261535 : Blo 2167435 9261535 := bstep (se 1 (by rfl) ⟨6946151, by rfl⟩ : syracuseStep 9261535 = 13892303) B13892303
theorem B12348713 : Blo 2167435 12348713 := bstep (se 2 (by rfl) ⟨4630767, by rfl⟩ : syracuseStep 12348713 = 9261535) B9261535
theorem B8232475 : Blo 2167435 8232475 := bstep (se 1 (by rfl) ⟨6174356, by rfl⟩ : syracuseStep 8232475 = 12348713) B12348713
theorem B10976633 : Blo 2167435 10976633 := bstep (se 2 (by rfl) ⟨4116237, by rfl⟩ : syracuseStep 10976633 = 8232475) B8232475
theorem B7317755 : Blo 2167435 7317755 := bstep (se 1 (by rfl) ⟨5488316, by rfl⟩ : syracuseStep 7317755 = 10976633) B10976633
theorem B4878503 : Blo 2167435 4878503 := bstep (se 1 (by rfl) ⟨3658877, by rfl⟩ : syracuseStep 4878503 = 7317755) B7317755
theorem B3252335 : Blo 2167435 3252335 := bstep (se 1 (by rfl) ⟨2439251, by rfl⟩ : syracuseStep 3252335 = 4878503) B4878503
theorem B2168223 : Blo 2167435 2168223 := bstep (se 1 (by rfl) ⟨1626167, by rfl⟩ : syracuseStep 2168223 = 3252335) B3252335
theorem B3252341 : Blo 2167435 3252341 := bbase (se 5 (by rfl) ⟨152453, by rfl⟩ : syracuseStep 3252341 = 304907) (by norm_num)
theorem B2168227 : Blo 2167435 2168227 := bstep (se 1 (by rfl) ⟨1626170, by rfl⟩ : syracuseStep 2168227 = 3252341) B3252341
theorem B4116253 : Blo 2167435 4116253 := bbase (se 3 (by rfl) ⟨771797, by rfl⟩ : syracuseStep 4116253 = 1543595) (by norm_num)
theorem B5488337 : Blo 2167435 5488337 := bstep (se 2 (by rfl) ⟨2058126, by rfl⟩ : syracuseStep 5488337 = 4116253) B4116253
theorem B3658891 : Blo 2167435 3658891 := bstep (se 1 (by rfl) ⟨2744168, by rfl⟩ : syracuseStep 3658891 = 5488337) B5488337
theorem B4878521 : Blo 2167435 4878521 := bstep (se 2 (by rfl) ⟨1829445, by rfl⟩ : syracuseStep 4878521 = 3658891) B3658891
theorem B3252347 : Blo 2167435 3252347 := bstep (se 1 (by rfl) ⟨2439260, by rfl⟩ : syracuseStep 3252347 = 4878521) B4878521
theorem B2168231 : Blo 2167435 2168231 := bstep (se 1 (by rfl) ⟨1626173, by rfl⟩ : syracuseStep 2168231 = 3252347) B3252347
theorem B2439265 : Blo 2167435 2439265 := bbase (se 2 (by rfl) ⟨914724, by rfl⟩ : syracuseStep 2439265 = 1829449) (by norm_num)
theorem B3252353 : Blo 2167435 3252353 := bstep (se 2 (by rfl) ⟨1219632, by rfl⟩ : syracuseStep 3252353 = 2439265) B2439265
theorem B2168235 : Blo 2167435 2168235 := bstep (se 1 (by rfl) ⟨1626176, by rfl⟩ : syracuseStep 2168235 = 3252353) B3252353
theorem B5488357 : Blo 2167435 5488357 := bbase (se 4 (by rfl) ⟨514533, by rfl⟩ : syracuseStep 5488357 = 1029067) (by norm_num)
theorem B7317809 : Blo 2167435 7317809 := bstep (se 2 (by rfl) ⟨2744178, by rfl⟩ : syracuseStep 7317809 = 5488357) B5488357
theorem B4878539 : Blo 2167435 4878539 := bstep (se 1 (by rfl) ⟨3658904, by rfl⟩ : syracuseStep 4878539 = 7317809) B7317809
theorem B3252359 : Blo 2167435 3252359 := bstep (se 1 (by rfl) ⟨2439269, by rfl⟩ : syracuseStep 3252359 = 4878539) B4878539
theorem B2168239 : Blo 2167435 2168239 := bstep (se 1 (by rfl) ⟨1626179, by rfl⟩ : syracuseStep 2168239 = 3252359) B3252359
theorem B3252365 : Blo 2167435 3252365 := bbase (se 3 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 3252365 = 1219637) (by norm_num)
theorem B2168243 : Blo 2167435 2168243 := bstep (se 1 (by rfl) ⟨1626182, by rfl⟩ : syracuseStep 2168243 = 3252365) B3252365
theorem B4878557 : Blo 2167435 4878557 := bbase (se 3 (by rfl) ⟨914729, by rfl⟩ : syracuseStep 4878557 = 1829459) (by norm_num)
theorem B3252371 : Blo 2167435 3252371 := bstep (se 1 (by rfl) ⟨2439278, by rfl⟩ : syracuseStep 3252371 = 4878557) B4878557
theorem B2168247 : Blo 2167435 2168247 := bstep (se 1 (by rfl) ⟨1626185, by rfl⟩ : syracuseStep 2168247 = 3252371) B3252371
theorem B3658925 : Blo 2167435 3658925 := bbase (se 3 (by rfl) ⟨686048, by rfl⟩ : syracuseStep 3658925 = 1372097) (by norm_num)
theorem B2439283 : Blo 2167435 2439283 := bstep (se 1 (by rfl) ⟨1829462, by rfl⟩ : syracuseStep 2439283 = 3658925) B3658925
theorem B3252377 : Blo 2167435 3252377 := bstep (se 2 (by rfl) ⟨1219641, by rfl⟩ : syracuseStep 3252377 = 2439283) B2439283
theorem B2168251 : Blo 2167435 2168251 := bstep (se 1 (by rfl) ⟨1626188, by rfl⟩ : syracuseStep 2168251 = 3252377) B3252377
theorem B52748117 : Blo 2167435 52748117 := bbase (se 9 (by rfl) ⟨154535, by rfl⟩ : syracuseStep 52748117 = 309071) (by norm_num)
theorem B35165411 : Blo 2167435 35165411 := bstep (se 1 (by rfl) ⟨26374058, by rfl⟩ : syracuseStep 35165411 = 52748117) B52748117
theorem B23443607 : Blo 2167435 23443607 := bstep (se 1 (by rfl) ⟨17582705, by rfl⟩ : syracuseStep 23443607 = 35165411) B35165411
theorem B62516285 : Blo 2167435 62516285 := bstep (se 3 (by rfl) ⟨11721803, by rfl⟩ : syracuseStep 62516285 = 23443607) B23443607
theorem B41677523 : Blo 2167435 41677523 := bstep (se 1 (by rfl) ⟨31258142, by rfl⟩ : syracuseStep 41677523 = 62516285) B62516285
theorem B27785015 : Blo 2167435 27785015 := bstep (se 1 (by rfl) ⟨20838761, by rfl⟩ : syracuseStep 27785015 = 41677523) B41677523
theorem B18523343 : Blo 2167435 18523343 := bstep (se 1 (by rfl) ⟨13892507, by rfl⟩ : syracuseStep 18523343 = 27785015) B27785015
theorem B12348895 : Blo 2167435 12348895 := bstep (se 1 (by rfl) ⟨9261671, by rfl⟩ : syracuseStep 12348895 = 18523343) B18523343
theorem B16465193 : Blo 2167435 16465193 := bstep (se 2 (by rfl) ⟨6174447, by rfl⟩ : syracuseStep 16465193 = 12348895) B12348895
theorem B10976795 : Blo 2167435 10976795 := bstep (se 1 (by rfl) ⟨8232596, by rfl⟩ : syracuseStep 10976795 = 16465193) B16465193
theorem B7317863 : Blo 2167435 7317863 := bstep (se 1 (by rfl) ⟨5488397, by rfl⟩ : syracuseStep 7317863 = 10976795) B10976795
theorem B4878575 : Blo 2167435 4878575 := bstep (se 1 (by rfl) ⟨3658931, by rfl⟩ : syracuseStep 4878575 = 7317863) B7317863
theorem B3252383 : Blo 2167435 3252383 := bstep (se 1 (by rfl) ⟨2439287, by rfl⟩ : syracuseStep 3252383 = 4878575) B4878575
theorem B2168255 : Blo 2167435 2168255 := bstep (se 1 (by rfl) ⟨1626191, by rfl⟩ : syracuseStep 2168255 = 3252383) B3252383
theorem B3252389 : Blo 2167435 3252389 := bbase (se 4 (by rfl) ⟨304911, by rfl⟩ : syracuseStep 3252389 = 609823) (by norm_num)
theorem B2168259 : Blo 2167435 2168259 := bstep (se 1 (by rfl) ⟨1626194, by rfl⟩ : syracuseStep 2168259 = 3252389) B3252389
theorem B2744209 : Blo 2167435 2744209 := bbase (se 2 (by rfl) ⟨1029078, by rfl⟩ : syracuseStep 2744209 = 2058157) (by norm_num)
theorem B3658945 : Blo 2167435 3658945 := bstep (se 2 (by rfl) ⟨1372104, by rfl⟩ : syracuseStep 3658945 = 2744209) B2744209
theorem B4878593 : Blo 2167435 4878593 := bstep (se 2 (by rfl) ⟨1829472, by rfl⟩ : syracuseStep 4878593 = 3658945) B3658945
theorem B3252395 : Blo 2167435 3252395 := bstep (se 1 (by rfl) ⟨2439296, by rfl⟩ : syracuseStep 3252395 = 4878593) B4878593
theorem B2168263 : Blo 2167435 2168263 := bstep (se 1 (by rfl) ⟨1626197, by rfl⟩ : syracuseStep 2168263 = 3252395) B3252395
theorem B2439301 : Blo 2167435 2439301 := bbase (se 4 (by rfl) ⟨228684, by rfl⟩ : syracuseStep 2439301 = 457369) (by norm_num)
theorem B3252401 : Blo 2167435 3252401 := bstep (se 2 (by rfl) ⟨1219650, by rfl⟩ : syracuseStep 3252401 = 2439301) B2439301
theorem B2168267 : Blo 2167435 2168267 := bstep (se 1 (by rfl) ⟨1626200, by rfl⟩ : syracuseStep 2168267 = 3252401) B3252401
theorem B10419461 : Blo 2167435 10419461 := bbase (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) (by norm_num)
theorem B6946307 : Blo 2167435 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B4630871 : Blo 2167435 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B3087247 : Blo 2167435 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B4116329 : Blo 2167435 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B2744219 : Blo 2167435 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B7317917 : Blo 2167435 7317917 := bstep (se 3 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 7317917 = 2744219) B2744219
theorem B4878611 : Blo 2167435 4878611 := bstep (se 1 (by rfl) ⟨3658958, by rfl⟩ : syracuseStep 4878611 = 7317917) B7317917
theorem B3252407 : Blo 2167435 3252407 := bstep (se 1 (by rfl) ⟨2439305, by rfl⟩ : syracuseStep 3252407 = 4878611) B4878611
theorem B2168271 : Blo 2167435 2168271 := bstep (se 1 (by rfl) ⟨1626203, by rfl⟩ : syracuseStep 2168271 = 3252407) B3252407
theorem B3252413 : Blo 2167435 3252413 := bbase (se 3 (by rfl) ⟨609827, by rfl⟩ : syracuseStep 3252413 = 1219655) (by norm_num)
theorem B2168275 : Blo 2167435 2168275 := bstep (se 1 (by rfl) ⟨1626206, by rfl⟩ : syracuseStep 2168275 = 3252413) B3252413
theorem B4878629 : Blo 2167435 4878629 := bbase (se 4 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 4878629 = 914743) (by norm_num)
theorem B3252419 : Blo 2167435 3252419 := bstep (se 1 (by rfl) ⟨2439314, by rfl⟩ : syracuseStep 3252419 = 4878629) B4878629
theorem B2168279 : Blo 2167435 2168279 := bstep (se 1 (by rfl) ⟨1626209, by rfl⟩ : syracuseStep 2168279 = 3252419) B3252419
theorem B5488469 : Blo 2167435 5488469 := bbase (se 9 (by rfl) ⟨16079, by rfl⟩ : syracuseStep 5488469 = 32159) (by norm_num)
theorem B3658979 : Blo 2167435 3658979 := bstep (se 1 (by rfl) ⟨2744234, by rfl⟩ : syracuseStep 3658979 = 5488469) B5488469
theorem B2439319 : Blo 2167435 2439319 := bstep (se 1 (by rfl) ⟨1829489, by rfl⟩ : syracuseStep 2439319 = 3658979) B3658979
theorem B3252425 : Blo 2167435 3252425 := bstep (se 2 (by rfl) ⟨1219659, by rfl⟩ : syracuseStep 3252425 = 2439319) B2439319
theorem B2168283 : Blo 2167435 2168283 := bstep (se 1 (by rfl) ⟨1626212, by rfl⟩ : syracuseStep 2168283 = 3252425) B3252425
theorem B6946357 : Blo 2167435 6946357 := bbase (se 5 (by rfl) ⟨325610, by rfl⟩ : syracuseStep 6946357 = 651221) (by norm_num)
theorem B9261809 : Blo 2167435 9261809 := bstep (se 2 (by rfl) ⟨3473178, by rfl⟩ : syracuseStep 9261809 = 6946357) B6946357
theorem B6174539 : Blo 2167435 6174539 := bstep (se 1 (by rfl) ⟨4630904, by rfl⟩ : syracuseStep 6174539 = 9261809) B9261809
theorem B4116359 : Blo 2167435 4116359 := bstep (se 1 (by rfl) ⟨3087269, by rfl⟩ : syracuseStep 4116359 = 6174539) B6174539
theorem B10976957 : Blo 2167435 10976957 := bstep (se 3 (by rfl) ⟨2058179, by rfl⟩ : syracuseStep 10976957 = 4116359) B4116359
theorem B7317971 : Blo 2167435 7317971 := bstep (se 1 (by rfl) ⟨5488478, by rfl⟩ : syracuseStep 7317971 = 10976957) B10976957
theorem B4878647 : Blo 2167435 4878647 := bstep (se 1 (by rfl) ⟨3658985, by rfl⟩ : syracuseStep 4878647 = 7317971) B7317971
theorem B3252431 : Blo 2167435 3252431 := bstep (se 1 (by rfl) ⟨2439323, by rfl⟩ : syracuseStep 3252431 = 4878647) B4878647
theorem B2168287 : Blo 2167435 2168287 := bstep (se 1 (by rfl) ⟨1626215, by rfl⟩ : syracuseStep 2168287 = 3252431) B3252431
theorem B3252437 : Blo 2167435 3252437 := bbase (se 7 (by rfl) ⟨38114, by rfl⟩ : syracuseStep 3252437 = 76229) (by norm_num)
theorem B2168291 : Blo 2167435 2168291 := bstep (se 1 (by rfl) ⟨1626218, by rfl⟩ : syracuseStep 2168291 = 3252437) B3252437
theorem B2315461 : Blo 2167435 2315461 := bbase (se 4 (by rfl) ⟨217074, by rfl⟩ : syracuseStep 2315461 = 434149) (by norm_num)
theorem B3087281 : Blo 2167435 3087281 := bstep (se 2 (by rfl) ⟨1157730, by rfl⟩ : syracuseStep 3087281 = 2315461) B2315461
theorem B8232749 : Blo 2167435 8232749 := bstep (se 3 (by rfl) ⟨1543640, by rfl⟩ : syracuseStep 8232749 = 3087281) B3087281
theorem B5488499 : Blo 2167435 5488499 := bstep (se 1 (by rfl) ⟨4116374, by rfl⟩ : syracuseStep 5488499 = 8232749) B8232749
theorem B3658999 : Blo 2167435 3658999 := bstep (se 1 (by rfl) ⟨2744249, by rfl⟩ : syracuseStep 3658999 = 5488499) B5488499
theorem B4878665 : Blo 2167435 4878665 := bstep (se 2 (by rfl) ⟨1829499, by rfl⟩ : syracuseStep 4878665 = 3658999) B3658999
theorem B3252443 : Blo 2167435 3252443 := bstep (se 1 (by rfl) ⟨2439332, by rfl⟩ : syracuseStep 3252443 = 4878665) B4878665
theorem B2168295 : Blo 2167435 2168295 := bstep (se 1 (by rfl) ⟨1626221, by rfl⟩ : syracuseStep 2168295 = 3252443) B3252443
theorem B2439337 : Blo 2167435 2439337 := bbase (se 2 (by rfl) ⟨914751, by rfl⟩ : syracuseStep 2439337 = 1829503) (by norm_num)
theorem B3252449 : Blo 2167435 3252449 := bstep (se 2 (by rfl) ⟨1219668, by rfl⟩ : syracuseStep 3252449 = 2439337) B2439337
theorem B2168299 : Blo 2167435 2168299 := bstep (se 1 (by rfl) ⟨1626224, by rfl⟩ : syracuseStep 2168299 = 3252449) B3252449
theorem B9261877 : Blo 2167435 9261877 := bbase (se 5 (by rfl) ⟨434150, by rfl⟩ : syracuseStep 9261877 = 868301) (by norm_num)
theorem B12349169 : Blo 2167435 12349169 := bstep (se 2 (by rfl) ⟨4630938, by rfl⟩ : syracuseStep 12349169 = 9261877) B9261877
theorem B8232779 : Blo 2167435 8232779 := bstep (se 1 (by rfl) ⟨6174584, by rfl⟩ : syracuseStep 8232779 = 12349169) B12349169
theorem B5488519 : Blo 2167435 5488519 := bstep (se 1 (by rfl) ⟨4116389, by rfl⟩ : syracuseStep 5488519 = 8232779) B8232779
theorem B7318025 : Blo 2167435 7318025 := bstep (se 2 (by rfl) ⟨2744259, by rfl⟩ : syracuseStep 7318025 = 5488519) B5488519
theorem B4878683 : Blo 2167435 4878683 := bstep (se 1 (by rfl) ⟨3659012, by rfl⟩ : syracuseStep 4878683 = 7318025) B7318025
theorem B3252455 : Blo 2167435 3252455 := bstep (se 1 (by rfl) ⟨2439341, by rfl⟩ : syracuseStep 3252455 = 4878683) B4878683
theorem B2168303 : Blo 2167435 2168303 := bstep (se 1 (by rfl) ⟨1626227, by rfl⟩ : syracuseStep 2168303 = 3252455) B3252455
theorem B3252461 : Blo 2167435 3252461 := bbase (se 3 (by rfl) ⟨609836, by rfl⟩ : syracuseStep 3252461 = 1219673) (by norm_num)
theorem B2168307 : Blo 2167435 2168307 := bstep (se 1 (by rfl) ⟨1626230, by rfl⟩ : syracuseStep 2168307 = 3252461) B3252461
theorem B4878701 : Blo 2167435 4878701 := bbase (se 3 (by rfl) ⟨914756, by rfl⟩ : syracuseStep 4878701 = 1829513) (by norm_num)
theorem B3252467 : Blo 2167435 3252467 := bstep (se 1 (by rfl) ⟨2439350, by rfl⟩ : syracuseStep 3252467 = 4878701) B4878701
theorem B2168311 : Blo 2167435 2168311 := bstep (se 1 (by rfl) ⟨1626233, by rfl⟩ : syracuseStep 2168311 = 3252467) B3252467
theorem B4116413 : Blo 2167435 4116413 := bbase (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) (by norm_num)
theorem B2744275 : Blo 2167435 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B3659033 : Blo 2167435 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B2439355 : Blo 2167435 2439355 := bstep (se 1 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 2439355 = 3659033) B3659033
theorem B3252473 : Blo 2167435 3252473 := bstep (se 2 (by rfl) ⟨1219677, by rfl⟩ : syracuseStep 3252473 = 2439355) B2439355
theorem B2168315 : Blo 2167435 2168315 := bstep (se 1 (by rfl) ⟨1626236, by rfl⟩ : syracuseStep 2168315 = 3252473) B3252473
theorem B55571669 : Blo 2167435 55571669 := bbase (se 7 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 55571669 = 1302461) (by norm_num)
theorem B37047779 : Blo 2167435 37047779 := bstep (se 1 (by rfl) ⟨27785834, by rfl⟩ : syracuseStep 37047779 = 55571669) B55571669
theorem B24698519 : Blo 2167435 24698519 := bstep (se 1 (by rfl) ⟨18523889, by rfl⟩ : syracuseStep 24698519 = 37047779) B37047779
theorem B16465679 : Blo 2167435 16465679 := bstep (se 1 (by rfl) ⟨12349259, by rfl⟩ : syracuseStep 16465679 = 24698519) B24698519
theorem B10977119 : Blo 2167435 10977119 := bstep (se 1 (by rfl) ⟨8232839, by rfl⟩ : syracuseStep 10977119 = 16465679) B16465679
theorem B7318079 : Blo 2167435 7318079 := bstep (se 1 (by rfl) ⟨5488559, by rfl⟩ : syracuseStep 7318079 = 10977119) B10977119
theorem B4878719 : Blo 2167435 4878719 := bstep (se 1 (by rfl) ⟨3659039, by rfl⟩ : syracuseStep 4878719 = 7318079) B7318079
theorem B3252479 : Blo 2167435 3252479 := bstep (se 1 (by rfl) ⟨2439359, by rfl⟩ : syracuseStep 3252479 = 4878719) B4878719
theorem B2168319 : Blo 2167435 2168319 := bstep (se 1 (by rfl) ⟨1626239, by rfl⟩ : syracuseStep 2168319 = 3252479) B3252479
theorem B3252485 : Blo 2167435 3252485 := bbase (se 4 (by rfl) ⟨304920, by rfl⟩ : syracuseStep 3252485 = 609841) (by norm_num)
theorem B2168323 : Blo 2167435 2168323 := bstep (se 1 (by rfl) ⟨1626242, by rfl⟩ : syracuseStep 2168323 = 3252485) B3252485
theorem B3659053 : Blo 2167435 3659053 := bbase (se 3 (by rfl) ⟨686072, by rfl⟩ : syracuseStep 3659053 = 1372145) (by norm_num)
theorem B4878737 : Blo 2167435 4878737 := bstep (se 2 (by rfl) ⟨1829526, by rfl⟩ : syracuseStep 4878737 = 3659053) B3659053
theorem B3252491 : Blo 2167435 3252491 := bstep (se 1 (by rfl) ⟨2439368, by rfl⟩ : syracuseStep 3252491 = 4878737) B4878737
theorem B2168327 : Blo 2167435 2168327 := bstep (se 1 (by rfl) ⟨1626245, by rfl⟩ : syracuseStep 2168327 = 3252491) B3252491
theorem B2439373 : Blo 2167435 2439373 := bbase (se 3 (by rfl) ⟨457382, by rfl⟩ : syracuseStep 2439373 = 914765) (by norm_num)
theorem B3252497 : Blo 2167435 3252497 := bstep (se 2 (by rfl) ⟨1219686, by rfl⟩ : syracuseStep 3252497 = 2439373) B2439373
theorem B2168331 : Blo 2167435 2168331 := bstep (se 1 (by rfl) ⟨1626248, by rfl⟩ : syracuseStep 2168331 = 3252497) B3252497
theorem B7318133 : Blo 2167435 7318133 := bbase (se 5 (by rfl) ⟨343037, by rfl⟩ : syracuseStep 7318133 = 686075) (by norm_num)
theorem B4878755 : Blo 2167435 4878755 := bstep (se 1 (by rfl) ⟨3659066, by rfl⟩ : syracuseStep 4878755 = 7318133) B7318133
theorem B3252503 : Blo 2167435 3252503 := bstep (se 1 (by rfl) ⟨2439377, by rfl⟩ : syracuseStep 3252503 = 4878755) B4878755
theorem B2168335 : Blo 2167435 2168335 := bstep (se 1 (by rfl) ⟨1626251, by rfl⟩ : syracuseStep 2168335 = 3252503) B3252503
theorem B3252509 : Blo 2167435 3252509 := bbase (se 3 (by rfl) ⟨609845, by rfl⟩ : syracuseStep 3252509 = 1219691) (by norm_num)
theorem B2168339 : Blo 2167435 2168339 := bstep (se 1 (by rfl) ⟨1626254, by rfl⟩ : syracuseStep 2168339 = 3252509) B3252509
theorem B4878773 : Blo 2167435 4878773 := bbase (se 5 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 4878773 = 457385) (by norm_num)
theorem B3252515 : Blo 2167435 3252515 := bstep (se 1 (by rfl) ⟨2439386, by rfl⟩ : syracuseStep 3252515 = 4878773) B4878773
theorem B2168343 : Blo 2167435 2168343 := bstep (se 1 (by rfl) ⟨1626257, by rfl⟩ : syracuseStep 2168343 = 3252515) B3252515
theorem B4945349 : Blo 2167435 4945349 := bbase (se 4 (by rfl) ⟨463626, by rfl⟩ : syracuseStep 4945349 = 927253) (by norm_num)
theorem B3296899 : Blo 2167435 3296899 := bstep (se 1 (by rfl) ⟨2472674, by rfl⟩ : syracuseStep 3296899 = 4945349) B4945349
theorem B4395865 : Blo 2167435 4395865 := bstep (se 2 (by rfl) ⟨1648449, by rfl⟩ : syracuseStep 4395865 = 3296899) B3296899
theorem B5861153 : Blo 2167435 5861153 := bstep (se 2 (by rfl) ⟨2197932, by rfl⟩ : syracuseStep 5861153 = 4395865) B4395865
theorem B3907435 : Blo 2167435 3907435 := bstep (se 1 (by rfl) ⟨2930576, by rfl⟩ : syracuseStep 3907435 = 5861153) B5861153
theorem B5209913 : Blo 2167435 5209913 := bstep (se 2 (by rfl) ⟨1953717, by rfl⟩ : syracuseStep 5209913 = 3907435) B3907435
theorem B3473275 : Blo 2167435 3473275 := bstep (se 1 (by rfl) ⟨2604956, by rfl⟩ : syracuseStep 3473275 = 5209913) B5209913
theorem B4631033 : Blo 2167435 4631033 := bstep (se 2 (by rfl) ⟨1736637, by rfl⟩ : syracuseStep 4631033 = 3473275) B3473275
theorem B12349421 : Blo 2167435 12349421 := bstep (se 3 (by rfl) ⟨2315516, by rfl⟩ : syracuseStep 12349421 = 4631033) B4631033
theorem B8232947 : Blo 2167435 8232947 := bstep (se 1 (by rfl) ⟨6174710, by rfl⟩ : syracuseStep 8232947 = 12349421) B12349421
theorem B5488631 : Blo 2167435 5488631 := bstep (se 1 (by rfl) ⟨4116473, by rfl⟩ : syracuseStep 5488631 = 8232947) B8232947
theorem B3659087 : Blo 2167435 3659087 := bstep (se 1 (by rfl) ⟨2744315, by rfl⟩ : syracuseStep 3659087 = 5488631) B5488631
theorem B2439391 : Blo 2167435 2439391 := bstep (se 1 (by rfl) ⟨1829543, by rfl⟩ : syracuseStep 2439391 = 3659087) B3659087
theorem B3252521 : Blo 2167435 3252521 := bstep (se 2 (by rfl) ⟨1219695, by rfl⟩ : syracuseStep 3252521 = 2439391) B2439391
theorem B2168347 : Blo 2167435 2168347 := bstep (se 1 (by rfl) ⟨1626260, by rfl⟩ : syracuseStep 2168347 = 3252521) B3252521
theorem B2604961 : Blo 2167435 2604961 := bbase (se 2 (by rfl) ⟨976860, by rfl⟩ : syracuseStep 2604961 = 1953721) (by norm_num)
theorem B3473281 : Blo 2167435 3473281 := bstep (se 2 (by rfl) ⟨1302480, by rfl⟩ : syracuseStep 3473281 = 2604961) B2604961
theorem B4631041 : Blo 2167435 4631041 := bstep (se 2 (by rfl) ⟨1736640, by rfl⟩ : syracuseStep 4631041 = 3473281) B3473281
theorem B6174721 : Blo 2167435 6174721 := bstep (se 2 (by rfl) ⟨2315520, by rfl⟩ : syracuseStep 6174721 = 4631041) B4631041
theorem B8232961 : Blo 2167435 8232961 := bstep (se 2 (by rfl) ⟨3087360, by rfl⟩ : syracuseStep 8232961 = 6174721) B6174721
theorem B10977281 : Blo 2167435 10977281 := bstep (se 2 (by rfl) ⟨4116480, by rfl⟩ : syracuseStep 10977281 = 8232961) B8232961
theorem B7318187 : Blo 2167435 7318187 := bstep (se 1 (by rfl) ⟨5488640, by rfl⟩ : syracuseStep 7318187 = 10977281) B10977281
theorem B4878791 : Blo 2167435 4878791 := bstep (se 1 (by rfl) ⟨3659093, by rfl⟩ : syracuseStep 4878791 = 7318187) B7318187
theorem B3252527 : Blo 2167435 3252527 := bstep (se 1 (by rfl) ⟨2439395, by rfl⟩ : syracuseStep 3252527 = 4878791) B4878791
theorem B2168351 : Blo 2167435 2168351 := bstep (se 1 (by rfl) ⟨1626263, by rfl⟩ : syracuseStep 2168351 = 3252527) B3252527
theorem B3252533 : Blo 2167435 3252533 := bbase (se 5 (by rfl) ⟨152462, by rfl⟩ : syracuseStep 3252533 = 304925) (by norm_num)
theorem B2168355 : Blo 2167435 2168355 := bstep (se 1 (by rfl) ⟨1626266, by rfl⟩ : syracuseStep 2168355 = 3252533) B3252533
theorem B5488661 : Blo 2167435 5488661 := bbase (se 6 (by rfl) ⟨128640, by rfl⟩ : syracuseStep 5488661 = 257281) (by norm_num)
theorem B3659107 : Blo 2167435 3659107 := bstep (se 1 (by rfl) ⟨2744330, by rfl⟩ : syracuseStep 3659107 = 5488661) B5488661
theorem B4878809 : Blo 2167435 4878809 := bstep (se 2 (by rfl) ⟨1829553, by rfl⟩ : syracuseStep 4878809 = 3659107) B3659107
theorem B3252539 : Blo 2167435 3252539 := bstep (se 1 (by rfl) ⟨2439404, by rfl⟩ : syracuseStep 3252539 = 4878809) B4878809
theorem B2168359 : Blo 2167435 2168359 := bstep (se 1 (by rfl) ⟨1626269, by rfl⟩ : syracuseStep 2168359 = 3252539) B3252539
theorem B2439409 : Blo 2167435 2439409 := bbase (se 2 (by rfl) ⟨914778, by rfl⟩ : syracuseStep 2439409 = 1829557) (by norm_num)
theorem B3252545 : Blo 2167435 3252545 := bstep (se 2 (by rfl) ⟨1219704, by rfl⟩ : syracuseStep 3252545 = 2439409) B2439409
theorem B2168363 : Blo 2167435 2168363 := bstep (se 1 (by rfl) ⟨1626272, by rfl⟩ : syracuseStep 2168363 = 3252545) B3252545
theorem B7519301 : Blo 2167435 7519301 := bbase (se 4 (by rfl) ⟨704934, by rfl⟩ : syracuseStep 7519301 = 1409869) (by norm_num)
theorem B5012867 : Blo 2167435 5012867 := bstep (se 1 (by rfl) ⟨3759650, by rfl⟩ : syracuseStep 5012867 = 7519301) B7519301
theorem B3341911 : Blo 2167435 3341911 := bstep (se 1 (by rfl) ⟨2506433, by rfl⟩ : syracuseStep 3341911 = 5012867) B5012867
theorem B4455881 : Blo 2167435 4455881 := bstep (se 2 (by rfl) ⟨1670955, by rfl⟩ : syracuseStep 4455881 = 3341911) B3341911
theorem B2970587 : Blo 2167435 2970587 := bstep (se 1 (by rfl) ⟨2227940, by rfl⟩ : syracuseStep 2970587 = 4455881) B4455881
theorem B7921565 : Blo 2167435 7921565 := bstep (se 3 (by rfl) ⟨1485293, by rfl⟩ : syracuseStep 7921565 = 2970587) B2970587
theorem B5281043 : Blo 2167435 5281043 := bstep (se 1 (by rfl) ⟨3960782, by rfl⟩ : syracuseStep 5281043 = 7921565) B7921565
theorem B14082781 : Blo 2167435 14082781 := bstep (se 3 (by rfl) ⟨2640521, by rfl⟩ : syracuseStep 14082781 = 5281043) B5281043
theorem B18777041 : Blo 2167435 18777041 := bstep (se 2 (by rfl) ⟨7041390, by rfl⟩ : syracuseStep 18777041 = 14082781) B14082781
theorem B12518027 : Blo 2167435 12518027 := bstep (se 1 (by rfl) ⟨9388520, by rfl⟩ : syracuseStep 12518027 = 18777041) B18777041
theorem B8345351 : Blo 2167435 8345351 := bstep (se 1 (by rfl) ⟨6259013, by rfl⟩ : syracuseStep 8345351 = 12518027) B12518027
theorem B5563567 : Blo 2167435 5563567 := bstep (se 1 (by rfl) ⟨4172675, by rfl⟩ : syracuseStep 5563567 = 8345351) B8345351
theorem B7418089 : Blo 2167435 7418089 := bstep (se 2 (by rfl) ⟨2781783, by rfl⟩ : syracuseStep 7418089 = 5563567) B5563567
theorem B9890785 : Blo 2167435 9890785 := bstep (se 2 (by rfl) ⟨3709044, by rfl⟩ : syracuseStep 9890785 = 7418089) B7418089
theorem B13187713 : Blo 2167435 13187713 := bstep (se 2 (by rfl) ⟨4945392, by rfl⟩ : syracuseStep 13187713 = 9890785) B9890785
theorem B17583617 : Blo 2167435 17583617 := bstep (se 2 (by rfl) ⟨6593856, by rfl⟩ : syracuseStep 17583617 = 13187713) B13187713
theorem B11722411 : Blo 2167435 11722411 := bstep (se 1 (by rfl) ⟨8791808, by rfl⟩ : syracuseStep 11722411 = 17583617) B17583617
theorem B15629881 : Blo 2167435 15629881 := bstep (se 2 (by rfl) ⟨5861205, by rfl⟩ : syracuseStep 15629881 = 11722411) B11722411
theorem B20839841 : Blo 2167435 20839841 := bstep (se 2 (by rfl) ⟨7814940, by rfl⟩ : syracuseStep 20839841 = 15629881) B15629881
theorem B13893227 : Blo 2167435 13893227 := bstep (se 1 (by rfl) ⟨10419920, by rfl⟩ : syracuseStep 13893227 = 20839841) B20839841
theorem B9262151 : Blo 2167435 9262151 := bstep (se 1 (by rfl) ⟨6946613, by rfl⟩ : syracuseStep 9262151 = 13893227) B13893227
theorem B6174767 : Blo 2167435 6174767 := bstep (se 1 (by rfl) ⟨4631075, by rfl⟩ : syracuseStep 6174767 = 9262151) B9262151
theorem B4116511 : Blo 2167435 4116511 := bstep (se 1 (by rfl) ⟨3087383, by rfl⟩ : syracuseStep 4116511 = 6174767) B6174767
theorem B5488681 : Blo 2167435 5488681 := bstep (se 2 (by rfl) ⟨2058255, by rfl⟩ : syracuseStep 5488681 = 4116511) B4116511
theorem B7318241 : Blo 2167435 7318241 := bstep (se 2 (by rfl) ⟨2744340, by rfl⟩ : syracuseStep 7318241 = 5488681) B5488681
theorem B4878827 : Blo 2167435 4878827 := bstep (se 1 (by rfl) ⟨3659120, by rfl⟩ : syracuseStep 4878827 = 7318241) B7318241
theorem B3252551 : Blo 2167435 3252551 := bstep (se 1 (by rfl) ⟨2439413, by rfl⟩ : syracuseStep 3252551 = 4878827) B4878827
theorem B2168367 : Blo 2167435 2168367 := bstep (se 1 (by rfl) ⟨1626275, by rfl⟩ : syracuseStep 2168367 = 3252551) B3252551
theorem B3252557 : Blo 2167435 3252557 := bbase (se 3 (by rfl) ⟨609854, by rfl⟩ : syracuseStep 3252557 = 1219709) (by norm_num)
theorem B2168371 : Blo 2167435 2168371 := bstep (se 1 (by rfl) ⟨1626278, by rfl⟩ : syracuseStep 2168371 = 3252557) B3252557
theorem B4878845 : Blo 2167435 4878845 := bbase (se 3 (by rfl) ⟨914783, by rfl⟩ : syracuseStep 4878845 = 1829567) (by norm_num)
theorem B3252563 : Blo 2167435 3252563 := bstep (se 1 (by rfl) ⟨2439422, by rfl⟩ : syracuseStep 3252563 = 4878845) B4878845
theorem B2168375 : Blo 2167435 2168375 := bstep (se 1 (by rfl) ⟨1626281, by rfl⟩ : syracuseStep 2168375 = 3252563) B3252563
theorem B3659141 : Blo 2167435 3659141 := bbase (se 4 (by rfl) ⟨343044, by rfl⟩ : syracuseStep 3659141 = 686089) (by norm_num)
theorem B2439427 : Blo 2167435 2439427 := bstep (se 1 (by rfl) ⟨1829570, by rfl⟩ : syracuseStep 2439427 = 3659141) B3659141
theorem B3252569 : Blo 2167435 3252569 := bstep (se 2 (by rfl) ⟨1219713, by rfl⟩ : syracuseStep 3252569 = 2439427) B2439427
theorem B2168379 : Blo 2167435 2168379 := bstep (se 1 (by rfl) ⟨1626284, by rfl⟩ : syracuseStep 2168379 = 3252569) B3252569
theorem B16466165 : Blo 2167435 16466165 := bbase (se 5 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 16466165 = 1543703) (by norm_num)
theorem B10977443 : Blo 2167435 10977443 := bstep (se 1 (by rfl) ⟨8233082, by rfl⟩ : syracuseStep 10977443 = 16466165) B16466165
theorem B7318295 : Blo 2167435 7318295 := bstep (se 1 (by rfl) ⟨5488721, by rfl⟩ : syracuseStep 7318295 = 10977443) B10977443
theorem B4878863 : Blo 2167435 4878863 := bstep (se 1 (by rfl) ⟨3659147, by rfl⟩ : syracuseStep 4878863 = 7318295) B7318295
theorem B3252575 : Blo 2167435 3252575 := bstep (se 1 (by rfl) ⟨2439431, by rfl⟩ : syracuseStep 3252575 = 4878863) B4878863
theorem B2168383 : Blo 2167435 2168383 := bstep (se 1 (by rfl) ⟨1626287, by rfl⟩ : syracuseStep 2168383 = 3252575) B3252575
theorem B3252581 : Blo 2167435 3252581 := bbase (se 4 (by rfl) ⟨304929, by rfl⟩ : syracuseStep 3252581 = 609859) (by norm_num)
theorem B2168387 : Blo 2167435 2168387 := bstep (se 1 (by rfl) ⟨1626290, by rfl⟩ : syracuseStep 2168387 = 3252581) B3252581
theorem B4116557 : Blo 2167435 4116557 := bbase (se 3 (by rfl) ⟨771854, by rfl⟩ : syracuseStep 4116557 = 1543709) (by norm_num)
theorem B2744371 : Blo 2167435 2744371 := bstep (se 1 (by rfl) ⟨2058278, by rfl⟩ : syracuseStep 2744371 = 4116557) B4116557
theorem B3659161 : Blo 2167435 3659161 := bstep (se 2 (by rfl) ⟨1372185, by rfl⟩ : syracuseStep 3659161 = 2744371) B2744371
theorem B4878881 : Blo 2167435 4878881 := bstep (se 2 (by rfl) ⟨1829580, by rfl⟩ : syracuseStep 4878881 = 3659161) B3659161
theorem B3252587 : Blo 2167435 3252587 := bstep (se 1 (by rfl) ⟨2439440, by rfl⟩ : syracuseStep 3252587 = 4878881) B4878881
theorem B2168391 : Blo 2167435 2168391 := bstep (se 1 (by rfl) ⟨1626293, by rfl⟩ : syracuseStep 2168391 = 3252587) B3252587
theorem B2439445 : Blo 2167435 2439445 := bbase (se 6 (by rfl) ⟨57174, by rfl⟩ : syracuseStep 2439445 = 114349) (by norm_num)
theorem B3252593 : Blo 2167435 3252593 := bstep (se 2 (by rfl) ⟨1219722, by rfl⟩ : syracuseStep 3252593 = 2439445) B2439445
theorem B2168395 : Blo 2167435 2168395 := bstep (se 1 (by rfl) ⟨1626296, by rfl⟩ : syracuseStep 2168395 = 3252593) B3252593
theorem B2744381 : Blo 2167435 2744381 := bbase (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) (by norm_num)
theorem B7318349 : Blo 2167435 7318349 := bstep (se 3 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 7318349 = 2744381) B2744381
theorem B4878899 : Blo 2167435 4878899 := bstep (se 1 (by rfl) ⟨3659174, by rfl⟩ : syracuseStep 4878899 = 7318349) B7318349
theorem B3252599 : Blo 2167435 3252599 := bstep (se 1 (by rfl) ⟨2439449, by rfl⟩ : syracuseStep 3252599 = 4878899) B4878899
theorem B2168399 : Blo 2167435 2168399 := bstep (se 1 (by rfl) ⟨1626299, by rfl⟩ : syracuseStep 2168399 = 3252599) B3252599
theorem B3252605 : Blo 2167435 3252605 := bbase (se 3 (by rfl) ⟨609863, by rfl⟩ : syracuseStep 3252605 = 1219727) (by norm_num)
theorem B2168403 : Blo 2167435 2168403 := bstep (se 1 (by rfl) ⟨1626302, by rfl⟩ : syracuseStep 2168403 = 3252605) B3252605
theorem B4878917 : Blo 2167435 4878917 := bbase (se 4 (by rfl) ⟨457398, by rfl⟩ : syracuseStep 4878917 = 914797) (by norm_num)
theorem B3252611 : Blo 2167435 3252611 := bstep (se 1 (by rfl) ⟨2439458, by rfl⟩ : syracuseStep 3252611 = 4878917) B4878917
theorem B2168407 : Blo 2167435 2168407 := bstep (se 1 (by rfl) ⟨1626305, by rfl⟩ : syracuseStep 2168407 = 3252611) B3252611
theorem B2315585 : Blo 2167435 2315585 := bbase (se 2 (by rfl) ⟨868344, by rfl⟩ : syracuseStep 2315585 = 1736689) (by norm_num)
theorem B6174893 : Blo 2167435 6174893 := bstep (se 3 (by rfl) ⟨1157792, by rfl⟩ : syracuseStep 6174893 = 2315585) B2315585
theorem B4116595 : Blo 2167435 4116595 := bstep (se 1 (by rfl) ⟨3087446, by rfl⟩ : syracuseStep 4116595 = 6174893) B6174893
theorem B5488793 : Blo 2167435 5488793 := bstep (se 2 (by rfl) ⟨2058297, by rfl⟩ : syracuseStep 5488793 = 4116595) B4116595
theorem B3659195 : Blo 2167435 3659195 := bstep (se 1 (by rfl) ⟨2744396, by rfl⟩ : syracuseStep 3659195 = 5488793) B5488793
theorem B2439463 : Blo 2167435 2439463 := bstep (se 1 (by rfl) ⟨1829597, by rfl⟩ : syracuseStep 2439463 = 3659195) B3659195
theorem B3252617 : Blo 2167435 3252617 := bstep (se 2 (by rfl) ⟨1219731, by rfl⟩ : syracuseStep 3252617 = 2439463) B2439463
theorem B2168411 : Blo 2167435 2168411 := bstep (se 1 (by rfl) ⟨1626308, by rfl⟩ : syracuseStep 2168411 = 3252617) B3252617
theorem B10977605 : Blo 2167435 10977605 := bbase (se 4 (by rfl) ⟨1029150, by rfl⟩ : syracuseStep 10977605 = 2058301) (by norm_num)
theorem B7318403 : Blo 2167435 7318403 := bstep (se 1 (by rfl) ⟨5488802, by rfl⟩ : syracuseStep 7318403 = 10977605) B10977605
theorem B4878935 : Blo 2167435 4878935 := bstep (se 1 (by rfl) ⟨3659201, by rfl⟩ : syracuseStep 4878935 = 7318403) B7318403
theorem B3252623 : Blo 2167435 3252623 := bstep (se 1 (by rfl) ⟨2439467, by rfl⟩ : syracuseStep 3252623 = 4878935) B4878935
theorem B2168415 : Blo 2167435 2168415 := bstep (se 1 (by rfl) ⟨1626311, by rfl⟩ : syracuseStep 2168415 = 3252623) B3252623
theorem B3252629 : Blo 2167435 3252629 := bbase (se 6 (by rfl) ⟨76233, by rfl⟩ : syracuseStep 3252629 = 152467) (by norm_num)
theorem B2168419 : Blo 2167435 2168419 := bstep (se 1 (by rfl) ⟨1626314, by rfl⟩ : syracuseStep 2168419 = 3252629) B3252629
theorem B7519493 : Blo 2167435 7519493 := bbase (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) (by norm_num)
theorem B20051981 : Blo 2167435 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B13367987 : Blo 2167435 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B8911991 : Blo 2167435 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B23765309 : Blo 2167435 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B15843539 : Blo 2167435 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B42249437 : Blo 2167435 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B28166291 : Blo 2167435 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B18777527 : Blo 2167435 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B12518351 : Blo 2167435 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B8345567 : Blo 2167435 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B5563711 : Blo 2167435 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B29673125 : Blo 2167435 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B19782083 : Blo 2167435 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B13188055 : Blo 2167435 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B17584073 : Blo 2167435 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B11722715 : Blo 2167435 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B7815143 : Blo 2167435 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B5210095 : Blo 2167435 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B6946793 : Blo 2167435 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B4631195 : Blo 2167435 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B12349853 : Blo 2167435 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B8233235 : Blo 2167435 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B5488823 : Blo 2167435 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B3659215 : Blo 2167435 3659215 := bstep (se 1 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 3659215 = 5488823) B5488823
theorem B4878953 : Blo 2167435 4878953 := bstep (se 2 (by rfl) ⟨1829607, by rfl⟩ : syracuseStep 4878953 = 3659215) B3659215
theorem B3252635 : Blo 2167435 3252635 := bstep (se 1 (by rfl) ⟨2439476, by rfl⟩ : syracuseStep 3252635 = 4878953) B4878953
theorem B2168423 : Blo 2167435 2168423 := bstep (se 1 (by rfl) ⟨1626317, by rfl⟩ : syracuseStep 2168423 = 3252635) B3252635
theorem B2439481 : Blo 2167435 2439481 := bbase (se 2 (by rfl) ⟨914805, by rfl⟩ : syracuseStep 2439481 = 1829611) (by norm_num)
theorem B3252641 : Blo 2167435 3252641 := bstep (se 2 (by rfl) ⟨1219740, by rfl⟩ : syracuseStep 3252641 = 2439481) B2439481
theorem B2168427 : Blo 2167435 2168427 := bstep (se 1 (by rfl) ⟨1626320, by rfl⟩ : syracuseStep 2168427 = 3252641) B3252641
theorem B6174949 : Blo 2167435 6174949 := bbase (se 4 (by rfl) ⟨578901, by rfl⟩ : syracuseStep 6174949 = 1157803) (by norm_num)
theorem B8233265 : Blo 2167435 8233265 := bstep (se 2 (by rfl) ⟨3087474, by rfl⟩ : syracuseStep 8233265 = 6174949) B6174949
theorem B5488843 : Blo 2167435 5488843 := bstep (se 1 (by rfl) ⟨4116632, by rfl⟩ : syracuseStep 5488843 = 8233265) B8233265
theorem B7318457 : Blo 2167435 7318457 := bstep (se 2 (by rfl) ⟨2744421, by rfl⟩ : syracuseStep 7318457 = 5488843) B5488843
theorem B4878971 : Blo 2167435 4878971 := bstep (se 1 (by rfl) ⟨3659228, by rfl⟩ : syracuseStep 4878971 = 7318457) B7318457
theorem B3252647 : Blo 2167435 3252647 := bstep (se 1 (by rfl) ⟨2439485, by rfl⟩ : syracuseStep 3252647 = 4878971) B4878971
theorem B2168431 : Blo 2167435 2168431 := bstep (se 1 (by rfl) ⟨1626323, by rfl⟩ : syracuseStep 2168431 = 3252647) B3252647
theorem B3252653 : Blo 2167435 3252653 := bbase (se 3 (by rfl) ⟨609872, by rfl⟩ : syracuseStep 3252653 = 1219745) (by norm_num)
theorem B2168435 : Blo 2167435 2168435 := bstep (se 1 (by rfl) ⟨1626326, by rfl⟩ : syracuseStep 2168435 = 3252653) B3252653
theorem B4878989 : Blo 2167435 4878989 := bbase (se 3 (by rfl) ⟨914810, by rfl⟩ : syracuseStep 4878989 = 1829621) (by norm_num)
theorem B3252659 : Blo 2167435 3252659 := bstep (se 1 (by rfl) ⟨2439494, by rfl⟩ : syracuseStep 3252659 = 4878989) B4878989
theorem B2168439 : Blo 2167435 2168439 := bstep (se 1 (by rfl) ⟨1626329, by rfl⟩ : syracuseStep 2168439 = 3252659) B3252659
theorem B2744437 : Blo 2167435 2744437 := bbase (se 5 (by rfl) ⟨128645, by rfl⟩ : syracuseStep 2744437 = 257291) (by norm_num)
theorem B3659249 : Blo 2167435 3659249 := bstep (se 2 (by rfl) ⟨1372218, by rfl⟩ : syracuseStep 3659249 = 2744437) B2744437
theorem B2439499 : Blo 2167435 2439499 := bstep (se 1 (by rfl) ⟨1829624, by rfl⟩ : syracuseStep 2439499 = 3659249) B3659249
theorem B3252665 : Blo 2167435 3252665 := bstep (se 2 (by rfl) ⟨1219749, by rfl⟩ : syracuseStep 3252665 = 2439499) B2439499
theorem B2168443 : Blo 2167435 2168443 := bstep (se 1 (by rfl) ⟨1626332, by rfl⟩ : syracuseStep 2168443 = 3252665) B3252665
theorem B3709181 : Blo 2167435 3709181 := bbase (se 3 (by rfl) ⟨695471, by rfl⟩ : syracuseStep 3709181 = 1390943) (by norm_num)
theorem B2472787 : Blo 2167435 2472787 := bstep (se 1 (by rfl) ⟨1854590, by rfl⟩ : syracuseStep 2472787 = 3709181) B3709181
theorem B13188197 : Blo 2167435 13188197 := bstep (se 4 (by rfl) ⟨1236393, by rfl⟩ : syracuseStep 13188197 = 2472787) B2472787
theorem B35168525 : Blo 2167435 35168525 := bstep (se 3 (by rfl) ⟨6594098, by rfl⟩ : syracuseStep 35168525 = 13188197) B13188197
theorem B23445683 : Blo 2167435 23445683 := bstep (se 1 (by rfl) ⟨17584262, by rfl⟩ : syracuseStep 23445683 = 35168525) B35168525
theorem B15630455 : Blo 2167435 15630455 := bstep (se 1 (by rfl) ⟨11722841, by rfl⟩ : syracuseStep 15630455 = 23445683) B23445683
theorem B41681213 : Blo 2167435 41681213 := bstep (se 3 (by rfl) ⟨7815227, by rfl⟩ : syracuseStep 41681213 = 15630455) B15630455
theorem B27787475 : Blo 2167435 27787475 := bstep (se 1 (by rfl) ⟨20840606, by rfl⟩ : syracuseStep 27787475 = 41681213) B41681213
theorem B18524983 : Blo 2167435 18524983 := bstep (se 1 (by rfl) ⟨13893737, by rfl⟩ : syracuseStep 18524983 = 27787475) B27787475
theorem B24699977 : Blo 2167435 24699977 := bstep (se 2 (by rfl) ⟨9262491, by rfl⟩ : syracuseStep 24699977 = 18524983) B18524983
theorem B16466651 : Blo 2167435 16466651 := bstep (se 1 (by rfl) ⟨12349988, by rfl⟩ : syracuseStep 16466651 = 24699977) B24699977
theorem B10977767 : Blo 2167435 10977767 := bstep (se 1 (by rfl) ⟨8233325, by rfl⟩ : syracuseStep 10977767 = 16466651) B16466651
theorem B7318511 : Blo 2167435 7318511 := bstep (se 1 (by rfl) ⟨5488883, by rfl⟩ : syracuseStep 7318511 = 10977767) B10977767
theorem B4879007 : Blo 2167435 4879007 := bstep (se 1 (by rfl) ⟨3659255, by rfl⟩ : syracuseStep 4879007 = 7318511) B7318511
theorem B3252671 : Blo 2167435 3252671 := bstep (se 1 (by rfl) ⟨2439503, by rfl⟩ : syracuseStep 3252671 = 4879007) B4879007
theorem B2168447 : Blo 2167435 2168447 := bstep (se 1 (by rfl) ⟨1626335, by rfl⟩ : syracuseStep 2168447 = 3252671) B3252671
theorem B3252677 : Blo 2167435 3252677 := bbase (se 4 (by rfl) ⟨304938, by rfl⟩ : syracuseStep 3252677 = 609877) (by norm_num)
theorem B2168451 : Blo 2167435 2168451 := bstep (se 1 (by rfl) ⟨1626338, by rfl⟩ : syracuseStep 2168451 = 3252677) B3252677
theorem B3659269 : Blo 2167435 3659269 := bbase (se 4 (by rfl) ⟨343056, by rfl⟩ : syracuseStep 3659269 = 686113) (by norm_num)
theorem B4879025 : Blo 2167435 4879025 := bstep (se 2 (by rfl) ⟨1829634, by rfl⟩ : syracuseStep 4879025 = 3659269) B3659269
theorem B3252683 : Blo 2167435 3252683 := bstep (se 1 (by rfl) ⟨2439512, by rfl⟩ : syracuseStep 3252683 = 4879025) B4879025
theorem B2168455 : Blo 2167435 2168455 := bstep (se 1 (by rfl) ⟨1626341, by rfl⟩ : syracuseStep 2168455 = 3252683) B3252683
theorem B2439517 : Blo 2167435 2439517 := bbase (se 3 (by rfl) ⟨457409, by rfl⟩ : syracuseStep 2439517 = 914819) (by norm_num)
theorem B3252689 : Blo 2167435 3252689 := bstep (se 2 (by rfl) ⟨1219758, by rfl⟩ : syracuseStep 3252689 = 2439517) B2439517
theorem B2168459 : Blo 2167435 2168459 := bstep (se 1 (by rfl) ⟨1626344, by rfl⟩ : syracuseStep 2168459 = 3252689) B3252689
theorem B7318565 : Blo 2167435 7318565 := bbase (se 4 (by rfl) ⟨686115, by rfl⟩ : syracuseStep 7318565 = 1372231) (by norm_num)
theorem B4879043 : Blo 2167435 4879043 := bstep (se 1 (by rfl) ⟨3659282, by rfl⟩ : syracuseStep 4879043 = 7318565) B7318565
theorem B3252695 : Blo 2167435 3252695 := bstep (se 1 (by rfl) ⟨2439521, by rfl⟩ : syracuseStep 3252695 = 4879043) B4879043
theorem B2168463 : Blo 2167435 2168463 := bstep (se 1 (by rfl) ⟨1626347, by rfl⟩ : syracuseStep 2168463 = 3252695) B3252695
theorem B3252701 : Blo 2167435 3252701 := bbase (se 3 (by rfl) ⟨609881, by rfl⟩ : syracuseStep 3252701 = 1219763) (by norm_num)
theorem B2168467 : Blo 2167435 2168467 := bstep (se 1 (by rfl) ⟨1626350, by rfl⟩ : syracuseStep 2168467 = 3252701) B3252701
theorem B4879061 : Blo 2167435 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B3252707 : Blo 2167435 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B2168471 : Blo 2167435 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B9262613 : Blo 2167435 9262613 := bbase (se 6 (by rfl) ⟨217092, by rfl⟩ : syracuseStep 9262613 = 434185) (by norm_num)
theorem B6175075 : Blo 2167435 6175075 := bstep (se 1 (by rfl) ⟨4631306, by rfl⟩ : syracuseStep 6175075 = 9262613) B9262613
theorem B8233433 : Blo 2167435 8233433 := bstep (se 2 (by rfl) ⟨3087537, by rfl⟩ : syracuseStep 8233433 = 6175075) B6175075
theorem B5488955 : Blo 2167435 5488955 := bstep (se 1 (by rfl) ⟨4116716, by rfl⟩ : syracuseStep 5488955 = 8233433) B8233433
theorem B3659303 : Blo 2167435 3659303 := bstep (se 1 (by rfl) ⟨2744477, by rfl⟩ : syracuseStep 3659303 = 5488955) B5488955
theorem B2439535 : Blo 2167435 2439535 := bstep (se 1 (by rfl) ⟨1829651, by rfl⟩ : syracuseStep 2439535 = 3659303) B3659303
theorem B3252713 : Blo 2167435 3252713 := bstep (se 2 (by rfl) ⟨1219767, by rfl⟩ : syracuseStep 3252713 = 2439535) B2439535
theorem B2168475 : Blo 2167435 2168475 := bstep (se 1 (by rfl) ⟨1626356, by rfl⟩ : syracuseStep 2168475 = 3252713) B3252713
theorem B42250517 : Blo 2167435 42250517 := bbase (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) (by norm_num)
theorem B28167011 : Blo 2167435 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B18778007 : Blo 2167435 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B12518671 : Blo 2167435 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B16691561 : Blo 2167435 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B11127707 : Blo 2167435 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B7418471 : Blo 2167435 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B19782589 : Blo 2167435 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B26376785 : Blo 2167435 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B17584523 : Blo 2167435 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B11723015 : Blo 2167435 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B31261373 : Blo 2167435 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B20840915 : Blo 2167435 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B13893943 : Blo 2167435 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B18525257 : Blo 2167435 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B12350171 : Blo 2167435 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B8233447 : Blo 2167435 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B10977929 : Blo 2167435 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B7318619 : Blo 2167435 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B4879079 : Blo 2167435 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B3252719 : Blo 2167435 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B2168479 : Blo 2167435 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B3252725 : Blo 2167435 3252725 := bbase (se 5 (by rfl) ⟨152471, by rfl⟩ : syracuseStep 3252725 = 304943) (by norm_num)
theorem B2168483 : Blo 2167435 2168483 := bstep (se 1 (by rfl) ⟨1626362, by rfl⟩ : syracuseStep 2168483 = 3252725) B3252725
theorem B6175109 : Blo 2167435 6175109 := bbase (se 4 (by rfl) ⟨578916, by rfl⟩ : syracuseStep 6175109 = 1157833) (by norm_num)
theorem B4116739 : Blo 2167435 4116739 := bstep (se 1 (by rfl) ⟨3087554, by rfl⟩ : syracuseStep 4116739 = 6175109) B6175109
theorem B5488985 : Blo 2167435 5488985 := bstep (se 2 (by rfl) ⟨2058369, by rfl⟩ : syracuseStep 5488985 = 4116739) B4116739
theorem B3659323 : Blo 2167435 3659323 := bstep (se 1 (by rfl) ⟨2744492, by rfl⟩ : syracuseStep 3659323 = 5488985) B5488985
theorem B4879097 : Blo 2167435 4879097 := bstep (se 2 (by rfl) ⟨1829661, by rfl⟩ : syracuseStep 4879097 = 3659323) B3659323
theorem B3252731 : Blo 2167435 3252731 := bstep (se 1 (by rfl) ⟨2439548, by rfl⟩ : syracuseStep 3252731 = 4879097) B4879097
theorem B2168487 : Blo 2167435 2168487 := bstep (se 1 (by rfl) ⟨1626365, by rfl⟩ : syracuseStep 2168487 = 3252731) B3252731
theorem B2439553 : Blo 2167435 2439553 := bbase (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) (by norm_num)
theorem B3252737 : Blo 2167435 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B2168491 : Blo 2167435 2168491 := bstep (se 1 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 2168491 = 3252737) B3252737
theorem B5489005 : Blo 2167435 5489005 := bbase (se 3 (by rfl) ⟨1029188, by rfl⟩ : syracuseStep 5489005 = 2058377) (by norm_num)
theorem B7318673 : Blo 2167435 7318673 := bstep (se 2 (by rfl) ⟨2744502, by rfl⟩ : syracuseStep 7318673 = 5489005) B5489005
theorem B4879115 : Blo 2167435 4879115 := bstep (se 1 (by rfl) ⟨3659336, by rfl⟩ : syracuseStep 4879115 = 7318673) B7318673
theorem B3252743 : Blo 2167435 3252743 := bstep (se 1 (by rfl) ⟨2439557, by rfl⟩ : syracuseStep 3252743 = 4879115) B4879115
theorem B2168495 : Blo 2167435 2168495 := bstep (se 1 (by rfl) ⟨1626371, by rfl⟩ : syracuseStep 2168495 = 3252743) B3252743
theorem B3252749 : Blo 2167435 3252749 := bbase (se 3 (by rfl) ⟨609890, by rfl⟩ : syracuseStep 3252749 = 1219781) (by norm_num)
theorem B2168499 : Blo 2167435 2168499 := bstep (se 1 (by rfl) ⟨1626374, by rfl⟩ : syracuseStep 2168499 = 3252749) B3252749
theorem B4879133 : Blo 2167435 4879133 := bbase (se 3 (by rfl) ⟨914837, by rfl⟩ : syracuseStep 4879133 = 1829675) (by norm_num)
theorem B3252755 : Blo 2167435 3252755 := bstep (se 1 (by rfl) ⟨2439566, by rfl⟩ : syracuseStep 3252755 = 4879133) B4879133
theorem B2168503 : Blo 2167435 2168503 := bstep (se 1 (by rfl) ⟨1626377, by rfl⟩ : syracuseStep 2168503 = 3252755) B3252755
theorem B3659357 : Blo 2167435 3659357 := bbase (se 3 (by rfl) ⟨686129, by rfl⟩ : syracuseStep 3659357 = 1372259) (by norm_num)
theorem B2439571 : Blo 2167435 2439571 := bstep (se 1 (by rfl) ⟨1829678, by rfl⟩ : syracuseStep 2439571 = 3659357) B3659357
theorem B3252761 : Blo 2167435 3252761 := bstep (se 2 (by rfl) ⟨1219785, by rfl⟩ : syracuseStep 3252761 = 2439571) B2439571
theorem B2168507 : Blo 2167435 2168507 := bstep (se 1 (by rfl) ⟨1626380, by rfl⟩ : syracuseStep 2168507 = 3252761) B3252761
theorem B2605153 : Blo 2167435 2605153 := bbase (se 2 (by rfl) ⟨976932, by rfl⟩ : syracuseStep 2605153 = 1953865) (by norm_num)
theorem B3473537 : Blo 2167435 3473537 := bstep (se 2 (by rfl) ⟨1302576, by rfl⟩ : syracuseStep 3473537 = 2605153) B2605153
theorem B9262765 : Blo 2167435 9262765 := bstep (se 3 (by rfl) ⟨1736768, by rfl⟩ : syracuseStep 9262765 = 3473537) B3473537
theorem B12350353 : Blo 2167435 12350353 := bstep (se 2 (by rfl) ⟨4631382, by rfl⟩ : syracuseStep 12350353 = 9262765) B9262765
theorem B16467137 : Blo 2167435 16467137 := bstep (se 2 (by rfl) ⟨6175176, by rfl⟩ : syracuseStep 16467137 = 12350353) B12350353
theorem B10978091 : Blo 2167435 10978091 := bstep (se 1 (by rfl) ⟨8233568, by rfl⟩ : syracuseStep 10978091 = 16467137) B16467137
theorem B7318727 : Blo 2167435 7318727 := bstep (se 1 (by rfl) ⟨5489045, by rfl⟩ : syracuseStep 7318727 = 10978091) B10978091
theorem B4879151 : Blo 2167435 4879151 := bstep (se 1 (by rfl) ⟨3659363, by rfl⟩ : syracuseStep 4879151 = 7318727) B7318727
theorem B3252767 : Blo 2167435 3252767 := bstep (se 1 (by rfl) ⟨2439575, by rfl⟩ : syracuseStep 3252767 = 4879151) B4879151
theorem B2168511 : Blo 2167435 2168511 := bstep (se 1 (by rfl) ⟨1626383, by rfl⟩ : syracuseStep 2168511 = 3252767) B3252767
theorem B3252773 : Blo 2167435 3252773 := bbase (se 4 (by rfl) ⟨304947, by rfl⟩ : syracuseStep 3252773 = 609895) (by norm_num)
theorem B2168515 : Blo 2167435 2168515 := bstep (se 1 (by rfl) ⟨1626386, by rfl⟩ : syracuseStep 2168515 = 3252773) B3252773
theorem B2744533 : Blo 2167435 2744533 := bbase (se 7 (by rfl) ⟨32162, by rfl⟩ : syracuseStep 2744533 = 64325) (by norm_num)
theorem B3659377 : Blo 2167435 3659377 := bstep (se 2 (by rfl) ⟨1372266, by rfl⟩ : syracuseStep 3659377 = 2744533) B2744533
theorem B4879169 : Blo 2167435 4879169 := bstep (se 2 (by rfl) ⟨1829688, by rfl⟩ : syracuseStep 4879169 = 3659377) B3659377
theorem B3252779 : Blo 2167435 3252779 := bstep (se 1 (by rfl) ⟨2439584, by rfl⟩ : syracuseStep 3252779 = 4879169) B4879169
theorem B2168519 : Blo 2167435 2168519 := bstep (se 1 (by rfl) ⟨1626389, by rfl⟩ : syracuseStep 2168519 = 3252779) B3252779
theorem B2439589 : Blo 2167435 2439589 := bbase (se 4 (by rfl) ⟨228711, by rfl⟩ : syracuseStep 2439589 = 457423) (by norm_num)
theorem B3252785 : Blo 2167435 3252785 := bstep (se 2 (by rfl) ⟨1219794, by rfl⟩ : syracuseStep 3252785 = 2439589) B2439589
theorem B2168523 : Blo 2167435 2168523 := bstep (se 1 (by rfl) ⟨1626392, by rfl⟩ : syracuseStep 2168523 = 3252785) B3252785
theorem B6259477 : Blo 2167435 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B8345969 : Blo 2167435 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B5563979 : Blo 2167435 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B3709319 : Blo 2167435 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B9891517 : Blo 2167435 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B13188689 : Blo 2167435 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B8792459 : Blo 2167435 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B5861639 : Blo 2167435 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B3907759 : Blo 2167435 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B5210345 : Blo 2167435 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B13894253 : Blo 2167435 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B9262835 : Blo 2167435 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B6175223 : Blo 2167435 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B4116815 : Blo 2167435 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B2744543 : Blo 2167435 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B7318781 : Blo 2167435 7318781 := bstep (se 3 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 7318781 = 2744543) B2744543
theorem B4879187 : Blo 2167435 4879187 := bstep (se 1 (by rfl) ⟨3659390, by rfl⟩ : syracuseStep 4879187 = 7318781) B7318781
theorem B3252791 : Blo 2167435 3252791 := bstep (se 1 (by rfl) ⟨2439593, by rfl⟩ : syracuseStep 3252791 = 4879187) B4879187
theorem B2168527 : Blo 2167435 2168527 := bstep (se 1 (by rfl) ⟨1626395, by rfl⟩ : syracuseStep 2168527 = 3252791) B3252791
theorem B3252797 : Blo 2167435 3252797 := bbase (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) (by norm_num)
theorem B2168531 : Blo 2167435 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B4879205 : Blo 2167435 4879205 := bbase (se 4 (by rfl) ⟨457425, by rfl⟩ : syracuseStep 4879205 = 914851) (by norm_num)
theorem B3252803 : Blo 2167435 3252803 := bstep (se 1 (by rfl) ⟨2439602, by rfl⟩ : syracuseStep 3252803 = 4879205) B4879205
theorem B2168535 : Blo 2167435 2168535 := bstep (se 1 (by rfl) ⟨1626401, by rfl⟩ : syracuseStep 2168535 = 3252803) B3252803
theorem B5489117 : Blo 2167435 5489117 := bbase (se 3 (by rfl) ⟨1029209, by rfl⟩ : syracuseStep 5489117 = 2058419) (by norm_num)
theorem B3659411 : Blo 2167435 3659411 := bstep (se 1 (by rfl) ⟨2744558, by rfl⟩ : syracuseStep 3659411 = 5489117) B5489117
theorem B2439607 : Blo 2167435 2439607 := bstep (se 1 (by rfl) ⟨1829705, by rfl⟩ : syracuseStep 2439607 = 3659411) B3659411
theorem B3252809 : Blo 2167435 3252809 := bstep (se 2 (by rfl) ⟨1219803, by rfl⟩ : syracuseStep 3252809 = 2439607) B2439607
theorem B2168539 : Blo 2167435 2168539 := bstep (se 1 (by rfl) ⟨1626404, by rfl⟩ : syracuseStep 2168539 = 3252809) B3252809
theorem B4116845 : Blo 2167435 4116845 := bbase (se 3 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 4116845 = 1543817) (by norm_num)
theorem B10978253 : Blo 2167435 10978253 := bstep (se 3 (by rfl) ⟨2058422, by rfl⟩ : syracuseStep 10978253 = 4116845) B4116845
theorem B7318835 : Blo 2167435 7318835 := bstep (se 1 (by rfl) ⟨5489126, by rfl⟩ : syracuseStep 7318835 = 10978253) B10978253
theorem B4879223 : Blo 2167435 4879223 := bstep (se 1 (by rfl) ⟨3659417, by rfl⟩ : syracuseStep 4879223 = 7318835) B7318835
theorem B3252815 : Blo 2167435 3252815 := bstep (se 1 (by rfl) ⟨2439611, by rfl⟩ : syracuseStep 3252815 = 4879223) B4879223
theorem B2168543 : Blo 2167435 2168543 := bstep (se 1 (by rfl) ⟨1626407, by rfl⟩ : syracuseStep 2168543 = 3252815) B3252815
theorem B3252821 : Blo 2167435 3252821 := bbase (se 8 (by rfl) ⟨19059, by rfl⟩ : syracuseStep 3252821 = 38119) (by norm_num)
theorem B2168547 : Blo 2167435 2168547 := bstep (se 1 (by rfl) ⟨1626410, by rfl⟩ : syracuseStep 2168547 = 3252821) B3252821
theorem B10420805 : Blo 2167435 10420805 := bbase (se 4 (by rfl) ⟨976950, by rfl⟩ : syracuseStep 10420805 = 1953901) (by norm_num)
theorem B6947203 : Blo 2167435 6947203 := bstep (se 1 (by rfl) ⟨5210402, by rfl⟩ : syracuseStep 6947203 = 10420805) B10420805
theorem B9262937 : Blo 2167435 9262937 := bstep (se 2 (by rfl) ⟨3473601, by rfl⟩ : syracuseStep 9262937 = 6947203) B6947203
theorem B6175291 : Blo 2167435 6175291 := bstep (se 1 (by rfl) ⟨4631468, by rfl⟩ : syracuseStep 6175291 = 9262937) B9262937
theorem B8233721 : Blo 2167435 8233721 := bstep (se 2 (by rfl) ⟨3087645, by rfl⟩ : syracuseStep 8233721 = 6175291) B6175291
theorem B5489147 : Blo 2167435 5489147 := bstep (se 1 (by rfl) ⟨4116860, by rfl⟩ : syracuseStep 5489147 = 8233721) B8233721
theorem B3659431 : Blo 2167435 3659431 := bstep (se 1 (by rfl) ⟨2744573, by rfl⟩ : syracuseStep 3659431 = 5489147) B5489147
theorem B4879241 : Blo 2167435 4879241 := bstep (se 2 (by rfl) ⟨1829715, by rfl⟩ : syracuseStep 4879241 = 3659431) B3659431
theorem B3252827 : Blo 2167435 3252827 := bstep (se 1 (by rfl) ⟨2439620, by rfl⟩ : syracuseStep 3252827 = 4879241) B4879241
theorem B2168551 : Blo 2167435 2168551 := bstep (se 1 (by rfl) ⟨1626413, by rfl⟩ : syracuseStep 2168551 = 3252827) B3252827
theorem B2439625 : Blo 2167435 2439625 := bbase (se 2 (by rfl) ⟨914859, by rfl⟩ : syracuseStep 2439625 = 1829719) (by norm_num)
theorem B3252833 : Blo 2167435 3252833 := bstep (se 2 (by rfl) ⟨1219812, by rfl⟩ : syracuseStep 3252833 = 2439625) B2439625
theorem B2168555 : Blo 2167435 2168555 := bstep (se 1 (by rfl) ⟨1626416, by rfl⟩ : syracuseStep 2168555 = 3252833) B3252833
theorem B18525941 : Blo 2167435 18525941 := bbase (se 5 (by rfl) ⟨868403, by rfl⟩ : syracuseStep 18525941 = 1736807) (by norm_num)
theorem B12350627 : Blo 2167435 12350627 := bstep (se 1 (by rfl) ⟨9262970, by rfl⟩ : syracuseStep 12350627 = 18525941) B18525941
theorem B8233751 : Blo 2167435 8233751 := bstep (se 1 (by rfl) ⟨6175313, by rfl⟩ : syracuseStep 8233751 = 12350627) B12350627
theorem B5489167 : Blo 2167435 5489167 := bstep (se 1 (by rfl) ⟨4116875, by rfl⟩ : syracuseStep 5489167 = 8233751) B8233751
theorem B7318889 : Blo 2167435 7318889 := bstep (se 2 (by rfl) ⟨2744583, by rfl⟩ : syracuseStep 7318889 = 5489167) B5489167
theorem B4879259 : Blo 2167435 4879259 := bstep (se 1 (by rfl) ⟨3659444, by rfl⟩ : syracuseStep 4879259 = 7318889) B7318889
theorem B3252839 : Blo 2167435 3252839 := bstep (se 1 (by rfl) ⟨2439629, by rfl⟩ : syracuseStep 3252839 = 4879259) B4879259
theorem B2168559 : Blo 2167435 2168559 := bstep (se 1 (by rfl) ⟨1626419, by rfl⟩ : syracuseStep 2168559 = 3252839) B3252839
theorem B3252845 : Blo 2167435 3252845 := bbase (se 3 (by rfl) ⟨609908, by rfl⟩ : syracuseStep 3252845 = 1219817) (by norm_num)
theorem B2168563 : Blo 2167435 2168563 := bstep (se 1 (by rfl) ⟨1626422, by rfl⟩ : syracuseStep 2168563 = 3252845) B3252845
theorem B4879277 : Blo 2167435 4879277 := bbase (se 3 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 4879277 = 1829729) (by norm_num)
theorem B3252851 : Blo 2167435 3252851 := bstep (se 1 (by rfl) ⟨2439638, by rfl⟩ : syracuseStep 3252851 = 4879277) B4879277
theorem B2168567 : Blo 2167435 2168567 := bstep (se 1 (by rfl) ⟨1626425, by rfl⟩ : syracuseStep 2168567 = 3252851) B3252851
theorem B6175349 : Blo 2167435 6175349 := bbase (se 5 (by rfl) ⟨289469, by rfl⟩ : syracuseStep 6175349 = 578939) (by norm_num)
theorem B4116899 : Blo 2167435 4116899 := bstep (se 1 (by rfl) ⟨3087674, by rfl⟩ : syracuseStep 4116899 = 6175349) B6175349
theorem B2744599 : Blo 2167435 2744599 := bstep (se 1 (by rfl) ⟨2058449, by rfl⟩ : syracuseStep 2744599 = 4116899) B4116899
theorem B3659465 : Blo 2167435 3659465 := bstep (se 2 (by rfl) ⟨1372299, by rfl⟩ : syracuseStep 3659465 = 2744599) B2744599
theorem B2439643 : Blo 2167435 2439643 := bstep (se 1 (by rfl) ⟨1829732, by rfl⟩ : syracuseStep 2439643 = 3659465) B3659465
theorem B3252857 : Blo 2167435 3252857 := bstep (se 2 (by rfl) ⟨1219821, by rfl⟩ : syracuseStep 3252857 = 2439643) B2439643
theorem B2168571 : Blo 2167435 2168571 := bstep (se 1 (by rfl) ⟨1626428, by rfl⟩ : syracuseStep 2168571 = 3252857) B3252857
theorem B4396325 : Blo 2167435 4396325 := bbase (se 4 (by rfl) ⟨412155, by rfl⟩ : syracuseStep 4396325 = 824311) (by norm_num)
theorem B46894133 : Blo 2167435 46894133 := bstep (se 5 (by rfl) ⟨2198162, by rfl⟩ : syracuseStep 46894133 = 4396325) B4396325
theorem B31262755 : Blo 2167435 31262755 := bstep (se 1 (by rfl) ⟨23447066, by rfl⟩ : syracuseStep 31262755 = 46894133) B46894133
theorem B41683673 : Blo 2167435 41683673 := bstep (se 2 (by rfl) ⟨15631377, by rfl⟩ : syracuseStep 41683673 = 31262755) B31262755
theorem B27789115 : Blo 2167435 27789115 := bstep (se 1 (by rfl) ⟨20841836, by rfl⟩ : syracuseStep 27789115 = 41683673) B41683673
theorem B37052153 : Blo 2167435 37052153 := bstep (se 2 (by rfl) ⟨13894557, by rfl⟩ : syracuseStep 37052153 = 27789115) B27789115
theorem B24701435 : Blo 2167435 24701435 := bstep (se 1 (by rfl) ⟨18526076, by rfl⟩ : syracuseStep 24701435 = 37052153) B37052153
theorem B16467623 : Blo 2167435 16467623 := bstep (se 1 (by rfl) ⟨12350717, by rfl⟩ : syracuseStep 16467623 = 24701435) B24701435
theorem B10978415 : Blo 2167435 10978415 := bstep (se 1 (by rfl) ⟨8233811, by rfl⟩ : syracuseStep 10978415 = 16467623) B16467623
theorem B7318943 : Blo 2167435 7318943 := bstep (se 1 (by rfl) ⟨5489207, by rfl⟩ : syracuseStep 7318943 = 10978415) B10978415
theorem B4879295 : Blo 2167435 4879295 := bstep (se 1 (by rfl) ⟨3659471, by rfl⟩ : syracuseStep 4879295 = 7318943) B7318943
theorem B3252863 : Blo 2167435 3252863 := bstep (se 1 (by rfl) ⟨2439647, by rfl⟩ : syracuseStep 3252863 = 4879295) B4879295
theorem B2168575 : Blo 2167435 2168575 := bstep (se 1 (by rfl) ⟨1626431, by rfl⟩ : syracuseStep 2168575 = 3252863) B3252863
theorem B3252869 : Blo 2167435 3252869 := bbase (se 4 (by rfl) ⟨304956, by rfl⟩ : syracuseStep 3252869 = 609913) (by norm_num)
theorem B2168579 : Blo 2167435 2168579 := bstep (se 1 (by rfl) ⟨1626434, by rfl⟩ : syracuseStep 2168579 = 3252869) B3252869
theorem B3659485 : Blo 2167435 3659485 := bbase (se 3 (by rfl) ⟨686153, by rfl⟩ : syracuseStep 3659485 = 1372307) (by norm_num)
theorem B4879313 : Blo 2167435 4879313 := bstep (se 2 (by rfl) ⟨1829742, by rfl⟩ : syracuseStep 4879313 = 3659485) B3659485
theorem B3252875 : Blo 2167435 3252875 := bstep (se 1 (by rfl) ⟨2439656, by rfl⟩ : syracuseStep 3252875 = 4879313) B4879313
theorem B2168583 : Blo 2167435 2168583 := bstep (se 1 (by rfl) ⟨1626437, by rfl⟩ : syracuseStep 2168583 = 3252875) B3252875
theorem B2439661 : Blo 2167435 2439661 := bbase (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) (by norm_num)
theorem B3252881 : Blo 2167435 3252881 := bstep (se 2 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 3252881 = 2439661) B2439661
theorem B2168587 : Blo 2167435 2168587 := bstep (se 1 (by rfl) ⟨1626440, by rfl⟩ : syracuseStep 2168587 = 3252881) B3252881
theorem B7318997 : Blo 2167435 7318997 := bbase (se 7 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 7318997 = 171539) (by norm_num)
theorem B4879331 : Blo 2167435 4879331 := bstep (se 1 (by rfl) ⟨3659498, by rfl⟩ : syracuseStep 4879331 = 7318997) B7318997
theorem B3252887 : Blo 2167435 3252887 := bstep (se 1 (by rfl) ⟨2439665, by rfl⟩ : syracuseStep 3252887 = 4879331) B4879331
theorem B2168591 : Blo 2167435 2168591 := bstep (se 1 (by rfl) ⟨1626443, by rfl⟩ : syracuseStep 2168591 = 3252887) B3252887
theorem B3252893 : Blo 2167435 3252893 := bbase (se 3 (by rfl) ⟨609917, by rfl⟩ : syracuseStep 3252893 = 1219835) (by norm_num)
theorem B2168595 : Blo 2167435 2168595 := bstep (se 1 (by rfl) ⟨1626446, by rfl⟩ : syracuseStep 2168595 = 3252893) B3252893
theorem B4879349 : Blo 2167435 4879349 := bbase (se 5 (by rfl) ⟨228719, by rfl⟩ : syracuseStep 4879349 = 457439) (by norm_num)
theorem B3252899 : Blo 2167435 3252899 := bstep (se 1 (by rfl) ⟨2439674, by rfl⟩ : syracuseStep 3252899 = 4879349) B4879349
theorem B2168599 : Blo 2167435 2168599 := bstep (se 1 (by rfl) ⟨1626449, by rfl⟩ : syracuseStep 2168599 = 3252899) B3252899
theorem B6022885 : Blo 2167435 6022885 := bbase (se 4 (by rfl) ⟨564645, by rfl⟩ : syracuseStep 6022885 = 1129291) (by norm_num)
theorem B8030513 : Blo 2167435 8030513 := bstep (se 2 (by rfl) ⟨3011442, by rfl⟩ : syracuseStep 8030513 = 6022885) B6022885
theorem B5353675 : Blo 2167435 5353675 := bstep (se 1 (by rfl) ⟨4015256, by rfl⟩ : syracuseStep 5353675 = 8030513) B8030513
theorem B28552933 : Blo 2167435 28552933 := bstep (se 4 (by rfl) ⟨2676837, by rfl⟩ : syracuseStep 28552933 = 5353675) B5353675
theorem B38070577 : Blo 2167435 38070577 := bstep (se 2 (by rfl) ⟨14276466, by rfl⟩ : syracuseStep 38070577 = 28552933) B28552933
theorem B50760769 : Blo 2167435 50760769 := bstep (se 2 (by rfl) ⟨19035288, by rfl⟩ : syracuseStep 50760769 = 38070577) B38070577
theorem B67681025 : Blo 2167435 67681025 := bstep (se 2 (by rfl) ⟨25380384, by rfl⟩ : syracuseStep 67681025 = 50760769) B50760769
theorem B45120683 : Blo 2167435 45120683 := bstep (se 1 (by rfl) ⟨33840512, by rfl⟩ : syracuseStep 45120683 = 67681025) B67681025
theorem B120321821 : Blo 2167435 120321821 := bstep (se 3 (by rfl) ⟨22560341, by rfl⟩ : syracuseStep 120321821 = 45120683) B45120683
theorem B80214547 : Blo 2167435 80214547 := bstep (se 1 (by rfl) ⟨60160910, by rfl⟩ : syracuseStep 80214547 = 120321821) B120321821
theorem B106952729 : Blo 2167435 106952729 := bstep (se 2 (by rfl) ⟨40107273, by rfl⟩ : syracuseStep 106952729 = 80214547) B80214547
theorem B1140829109 : Blo 2167435 1140829109 := bstep (se 5 (by rfl) ⟨53476364, by rfl⟩ : syracuseStep 1140829109 = 106952729) B106952729
theorem B760552739 : Blo 2167435 760552739 := bstep (se 1 (by rfl) ⟨570414554, by rfl⟩ : syracuseStep 760552739 = 1140829109) B1140829109
theorem B507035159 : Blo 2167435 507035159 := bstep (se 1 (by rfl) ⟨380276369, by rfl⟩ : syracuseStep 507035159 = 760552739) B760552739
theorem B338023439 : Blo 2167435 338023439 := bstep (se 1 (by rfl) ⟨253517579, by rfl⟩ : syracuseStep 338023439 = 507035159) B507035159
theorem B225348959 : Blo 2167435 225348959 := bstep (se 1 (by rfl) ⟨169011719, by rfl⟩ : syracuseStep 225348959 = 338023439) B338023439
theorem B150232639 : Blo 2167435 150232639 := bstep (se 1 (by rfl) ⟨112674479, by rfl⟩ : syracuseStep 150232639 = 225348959) B225348959
theorem B200310185 : Blo 2167435 200310185 := bstep (se 2 (by rfl) ⟨75116319, by rfl⟩ : syracuseStep 200310185 = 150232639) B150232639
theorem B133540123 : Blo 2167435 133540123 := bstep (se 1 (by rfl) ⟨100155092, by rfl⟩ : syracuseStep 133540123 = 200310185) B200310185
theorem B178053497 : Blo 2167435 178053497 := bstep (se 2 (by rfl) ⟨66770061, by rfl⟩ : syracuseStep 178053497 = 133540123) B133540123
theorem B118702331 : Blo 2167435 118702331 := bstep (se 1 (by rfl) ⟨89026748, by rfl⟩ : syracuseStep 118702331 = 178053497) B178053497
theorem B79134887 : Blo 2167435 79134887 := bstep (se 1 (by rfl) ⟨59351165, by rfl⟩ : syracuseStep 79134887 = 118702331) B118702331
theorem B52756591 : Blo 2167435 52756591 := bstep (se 1 (by rfl) ⟨39567443, by rfl⟩ : syracuseStep 52756591 = 79134887) B79134887
theorem B70342121 : Blo 2167435 70342121 := bstep (se 2 (by rfl) ⟨26378295, by rfl⟩ : syracuseStep 70342121 = 52756591) B52756591
theorem B46894747 : Blo 2167435 46894747 := bstep (se 1 (by rfl) ⟨35171060, by rfl⟩ : syracuseStep 46894747 = 70342121) B70342121
theorem B62526329 : Blo 2167435 62526329 := bstep (se 2 (by rfl) ⟨23447373, by rfl⟩ : syracuseStep 62526329 = 46894747) B46894747
theorem B41684219 : Blo 2167435 41684219 := bstep (se 1 (by rfl) ⟨31263164, by rfl⟩ : syracuseStep 41684219 = 62526329) B62526329
theorem B27789479 : Blo 2167435 27789479 := bstep (se 1 (by rfl) ⟨20842109, by rfl⟩ : syracuseStep 27789479 = 41684219) B41684219
theorem B18526319 : Blo 2167435 18526319 := bstep (se 1 (by rfl) ⟨13894739, by rfl⟩ : syracuseStep 18526319 = 27789479) B27789479
theorem B12350879 : Blo 2167435 12350879 := bstep (se 1 (by rfl) ⟨9263159, by rfl⟩ : syracuseStep 12350879 = 18526319) B18526319
theorem B8233919 : Blo 2167435 8233919 := bstep (se 1 (by rfl) ⟨6175439, by rfl⟩ : syracuseStep 8233919 = 12350879) B12350879
theorem B5489279 : Blo 2167435 5489279 := bstep (se 1 (by rfl) ⟨4116959, by rfl⟩ : syracuseStep 5489279 = 8233919) B8233919
theorem B3659519 : Blo 2167435 3659519 := bstep (se 1 (by rfl) ⟨2744639, by rfl⟩ : syracuseStep 3659519 = 5489279) B5489279
theorem B2439679 : Blo 2167435 2439679 := bstep (se 1 (by rfl) ⟨1829759, by rfl⟩ : syracuseStep 2439679 = 3659519) B3659519
theorem B3252905 : Blo 2167435 3252905 := bstep (se 2 (by rfl) ⟨1219839, by rfl⟩ : syracuseStep 3252905 = 2439679) B2439679
theorem B2168603 : Blo 2167435 2168603 := bstep (se 1 (by rfl) ⟨1626452, by rfl⟩ : syracuseStep 2168603 = 3252905) B3252905
theorem B3087725 : Blo 2167435 3087725 := bbase (se 3 (by rfl) ⟨578948, by rfl⟩ : syracuseStep 3087725 = 1157897) (by norm_num)
theorem B8233933 : Blo 2167435 8233933 := bstep (se 3 (by rfl) ⟨1543862, by rfl⟩ : syracuseStep 8233933 = 3087725) B3087725
theorem B10978577 : Blo 2167435 10978577 := bstep (se 2 (by rfl) ⟨4116966, by rfl⟩ : syracuseStep 10978577 = 8233933) B8233933
theorem B7319051 : Blo 2167435 7319051 := bstep (se 1 (by rfl) ⟨5489288, by rfl⟩ : syracuseStep 7319051 = 10978577) B10978577
theorem B4879367 : Blo 2167435 4879367 := bstep (se 1 (by rfl) ⟨3659525, by rfl⟩ : syracuseStep 4879367 = 7319051) B7319051
theorem B3252911 : Blo 2167435 3252911 := bstep (se 1 (by rfl) ⟨2439683, by rfl⟩ : syracuseStep 3252911 = 4879367) B4879367
theorem B2168607 : Blo 2167435 2168607 := bstep (se 1 (by rfl) ⟨1626455, by rfl⟩ : syracuseStep 2168607 = 3252911) B3252911
theorem B3252917 : Blo 2167435 3252917 := bbase (se 5 (by rfl) ⟨152480, by rfl⟩ : syracuseStep 3252917 = 304961) (by norm_num)
theorem B2168611 : Blo 2167435 2168611 := bstep (se 1 (by rfl) ⟨1626458, by rfl⟩ : syracuseStep 2168611 = 3252917) B3252917
theorem B5489309 : Blo 2167435 5489309 := bbase (se 3 (by rfl) ⟨1029245, by rfl⟩ : syracuseStep 5489309 = 2058491) (by norm_num)
theorem B3659539 : Blo 2167435 3659539 := bstep (se 1 (by rfl) ⟨2744654, by rfl⟩ : syracuseStep 3659539 = 5489309) B5489309
theorem B4879385 : Blo 2167435 4879385 := bstep (se 2 (by rfl) ⟨1829769, by rfl⟩ : syracuseStep 4879385 = 3659539) B3659539
theorem B3252923 : Blo 2167435 3252923 := bstep (se 1 (by rfl) ⟨2439692, by rfl⟩ : syracuseStep 3252923 = 4879385) B4879385
theorem B2168615 : Blo 2167435 2168615 := bstep (se 1 (by rfl) ⟨1626461, by rfl⟩ : syracuseStep 2168615 = 3252923) B3252923
theorem B2439697 : Blo 2167435 2439697 := bbase (se 2 (by rfl) ⟨914886, by rfl⟩ : syracuseStep 2439697 = 1829773) (by norm_num)
theorem B3252929 : Blo 2167435 3252929 := bstep (se 2 (by rfl) ⟨1219848, by rfl⟩ : syracuseStep 3252929 = 2439697) B2439697
theorem B2168619 : Blo 2167435 2168619 := bstep (se 1 (by rfl) ⟨1626464, by rfl⟩ : syracuseStep 2168619 = 3252929) B3252929
theorem B4116997 : Blo 2167435 4116997 := bbase (se 4 (by rfl) ⟨385968, by rfl⟩ : syracuseStep 4116997 = 771937) (by norm_num)
theorem B5489329 : Blo 2167435 5489329 := bstep (se 2 (by rfl) ⟨2058498, by rfl⟩ : syracuseStep 5489329 = 4116997) B4116997
theorem B7319105 : Blo 2167435 7319105 := bstep (se 2 (by rfl) ⟨2744664, by rfl⟩ : syracuseStep 7319105 = 5489329) B5489329
theorem B4879403 : Blo 2167435 4879403 := bstep (se 1 (by rfl) ⟨3659552, by rfl⟩ : syracuseStep 4879403 = 7319105) B7319105
theorem B3252935 : Blo 2167435 3252935 := bstep (se 1 (by rfl) ⟨2439701, by rfl⟩ : syracuseStep 3252935 = 4879403) B4879403
theorem B2168623 : Blo 2167435 2168623 := bstep (se 1 (by rfl) ⟨1626467, by rfl⟩ : syracuseStep 2168623 = 3252935) B3252935
theorem B3252941 : Blo 2167435 3252941 := bbase (se 3 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 3252941 = 1219853) (by norm_num)
theorem B2168627 : Blo 2167435 2168627 := bstep (se 1 (by rfl) ⟨1626470, by rfl⟩ : syracuseStep 2168627 = 3252941) B3252941
theorem B4879421 : Blo 2167435 4879421 := bbase (se 3 (by rfl) ⟨914891, by rfl⟩ : syracuseStep 4879421 = 1829783) (by norm_num)
theorem B3252947 : Blo 2167435 3252947 := bstep (se 1 (by rfl) ⟨2439710, by rfl⟩ : syracuseStep 3252947 = 4879421) B4879421
theorem B2168631 : Blo 2167435 2168631 := bstep (se 1 (by rfl) ⟨1626473, by rfl⟩ : syracuseStep 2168631 = 3252947) B3252947
theorem B3659573 : Blo 2167435 3659573 := bbase (se 5 (by rfl) ⟨171542, by rfl⟩ : syracuseStep 3659573 = 343085) (by norm_num)
theorem B2439715 : Blo 2167435 2439715 := bstep (se 1 (by rfl) ⟨1829786, by rfl⟩ : syracuseStep 2439715 = 3659573) B3659573
theorem B3252953 : Blo 2167435 3252953 := bstep (se 2 (by rfl) ⟨1219857, by rfl⟩ : syracuseStep 3252953 = 2439715) B2439715
theorem B2168635 : Blo 2167435 2168635 := bstep (se 1 (by rfl) ⟨1626476, by rfl⟩ : syracuseStep 2168635 = 3252953) B3252953
theorem B6175541 : Blo 2167435 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B16468109 : Blo 2167435 16468109 := bstep (se 3 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 16468109 = 6175541) B6175541
theorem B10978739 : Blo 2167435 10978739 := bstep (se 1 (by rfl) ⟨8234054, by rfl⟩ : syracuseStep 10978739 = 16468109) B16468109
theorem B7319159 : Blo 2167435 7319159 := bstep (se 1 (by rfl) ⟨5489369, by rfl⟩ : syracuseStep 7319159 = 10978739) B10978739
theorem B4879439 : Blo 2167435 4879439 := bstep (se 1 (by rfl) ⟨3659579, by rfl⟩ : syracuseStep 4879439 = 7319159) B7319159
theorem B3252959 : Blo 2167435 3252959 := bstep (se 1 (by rfl) ⟨2439719, by rfl⟩ : syracuseStep 3252959 = 4879439) B4879439
theorem B2168639 : Blo 2167435 2168639 := bstep (se 1 (by rfl) ⟨1626479, by rfl⟩ : syracuseStep 2168639 = 3252959) B3252959
theorem B3252965 : Blo 2167435 3252965 := bbase (se 4 (by rfl) ⟨304965, by rfl⟩ : syracuseStep 3252965 = 609931) (by norm_num)
theorem B2168643 : Blo 2167435 2168643 := bstep (se 1 (by rfl) ⟨1626482, by rfl⟩ : syracuseStep 2168643 = 3252965) B3252965
theorem B2315837 : Blo 2167435 2315837 := bbase (se 3 (by rfl) ⟨434219, by rfl⟩ : syracuseStep 2315837 = 868439) (by norm_num)
theorem B6175565 : Blo 2167435 6175565 := bstep (se 3 (by rfl) ⟨1157918, by rfl⟩ : syracuseStep 6175565 = 2315837) B2315837
theorem B4117043 : Blo 2167435 4117043 := bstep (se 1 (by rfl) ⟨3087782, by rfl⟩ : syracuseStep 4117043 = 6175565) B6175565
theorem B2744695 : Blo 2167435 2744695 := bstep (se 1 (by rfl) ⟨2058521, by rfl⟩ : syracuseStep 2744695 = 4117043) B4117043
theorem B3659593 : Blo 2167435 3659593 := bstep (se 2 (by rfl) ⟨1372347, by rfl⟩ : syracuseStep 3659593 = 2744695) B2744695
theorem B4879457 : Blo 2167435 4879457 := bstep (se 2 (by rfl) ⟨1829796, by rfl⟩ : syracuseStep 4879457 = 3659593) B3659593
theorem B3252971 : Blo 2167435 3252971 := bstep (se 1 (by rfl) ⟨2439728, by rfl⟩ : syracuseStep 3252971 = 4879457) B4879457
theorem B2168647 : Blo 2167435 2168647 := bstep (se 1 (by rfl) ⟨1626485, by rfl⟩ : syracuseStep 2168647 = 3252971) B3252971
theorem B2439733 : Blo 2167435 2439733 := bbase (se 5 (by rfl) ⟨114362, by rfl⟩ : syracuseStep 2439733 = 228725) (by norm_num)
theorem B3252977 : Blo 2167435 3252977 := bstep (se 2 (by rfl) ⟨1219866, by rfl⟩ : syracuseStep 3252977 = 2439733) B2439733
theorem B2168651 : Blo 2167435 2168651 := bstep (se 1 (by rfl) ⟨1626488, by rfl⟩ : syracuseStep 2168651 = 3252977) B3252977
theorem B2744705 : Blo 2167435 2744705 := bbase (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) (by norm_num)
theorem B7319213 : Blo 2167435 7319213 := bstep (se 3 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 7319213 = 2744705) B2744705
theorem B4879475 : Blo 2167435 4879475 := bstep (se 1 (by rfl) ⟨3659606, by rfl⟩ : syracuseStep 4879475 = 7319213) B7319213
theorem B3252983 : Blo 2167435 3252983 := bstep (se 1 (by rfl) ⟨2439737, by rfl⟩ : syracuseStep 3252983 = 4879475) B4879475
theorem B2168655 : Blo 2167435 2168655 := bstep (se 1 (by rfl) ⟨1626491, by rfl⟩ : syracuseStep 2168655 = 3252983) B3252983
theorem B3252989 : Blo 2167435 3252989 := bbase (se 3 (by rfl) ⟨609935, by rfl⟩ : syracuseStep 3252989 = 1219871) (by norm_num)
theorem B2168659 : Blo 2167435 2168659 := bstep (se 1 (by rfl) ⟨1626494, by rfl⟩ : syracuseStep 2168659 = 3252989) B3252989
theorem B4879493 : Blo 2167435 4879493 := bbase (se 4 (by rfl) ⟨457452, by rfl⟩ : syracuseStep 4879493 = 914905) (by norm_num)
theorem B3252995 : Blo 2167435 3252995 := bstep (se 1 (by rfl) ⟨2439746, by rfl⟩ : syracuseStep 3252995 = 4879493) B4879493
theorem B2168663 : Blo 2167435 2168663 := bstep (se 1 (by rfl) ⟨1626497, by rfl⟩ : syracuseStep 2168663 = 3252995) B3252995
theorem B4631717 : Blo 2167435 4631717 := bbase (se 4 (by rfl) ⟨434223, by rfl⟩ : syracuseStep 4631717 = 868447) (by norm_num)
theorem B3087811 : Blo 2167435 3087811 := bstep (se 1 (by rfl) ⟨2315858, by rfl⟩ : syracuseStep 3087811 = 4631717) B4631717
theorem B4117081 : Blo 2167435 4117081 := bstep (se 2 (by rfl) ⟨1543905, by rfl⟩ : syracuseStep 4117081 = 3087811) B3087811
theorem B5489441 : Blo 2167435 5489441 := bstep (se 2 (by rfl) ⟨2058540, by rfl⟩ : syracuseStep 5489441 = 4117081) B4117081
theorem B3659627 : Blo 2167435 3659627 := bstep (se 1 (by rfl) ⟨2744720, by rfl⟩ : syracuseStep 3659627 = 5489441) B5489441
theorem B2439751 : Blo 2167435 2439751 := bstep (se 1 (by rfl) ⟨1829813, by rfl⟩ : syracuseStep 2439751 = 3659627) B3659627
theorem B3253001 : Blo 2167435 3253001 := bstep (se 2 (by rfl) ⟨1219875, by rfl⟩ : syracuseStep 3253001 = 2439751) B2439751
theorem B2168667 : Blo 2167435 2168667 := bstep (se 1 (by rfl) ⟨1626500, by rfl⟩ : syracuseStep 2168667 = 3253001) B3253001
theorem B10978901 : Blo 2167435 10978901 := bbase (se 8 (by rfl) ⟨64329, by rfl⟩ : syracuseStep 10978901 = 128659) (by norm_num)
theorem B7319267 : Blo 2167435 7319267 := bstep (se 1 (by rfl) ⟨5489450, by rfl⟩ : syracuseStep 7319267 = 10978901) B10978901
theorem B4879511 : Blo 2167435 4879511 := bstep (se 1 (by rfl) ⟨3659633, by rfl⟩ : syracuseStep 4879511 = 7319267) B7319267
theorem B3253007 : Blo 2167435 3253007 := bstep (se 1 (by rfl) ⟨2439755, by rfl⟩ : syracuseStep 3253007 = 4879511) B4879511
theorem B2168671 : Blo 2167435 2168671 := bstep (se 1 (by rfl) ⟨1626503, by rfl⟩ : syracuseStep 2168671 = 3253007) B3253007
theorem B3253013 : Blo 2167435 3253013 := bbase (se 6 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 3253013 = 152485) (by norm_num)
theorem B2168675 : Blo 2167435 2168675 := bstep (se 1 (by rfl) ⟨1626506, by rfl⟩ : syracuseStep 2168675 = 3253013) B3253013
theorem B6594805 : Blo 2167435 6594805 := bbase (se 5 (by rfl) ⟨309131, by rfl⟩ : syracuseStep 6594805 = 618263) (by norm_num)
theorem B8793073 : Blo 2167435 8793073 := bstep (se 2 (by rfl) ⟨3297402, by rfl⟩ : syracuseStep 8793073 = 6594805) B6594805
theorem B11724097 : Blo 2167435 11724097 := bstep (se 2 (by rfl) ⟨4396536, by rfl⟩ : syracuseStep 11724097 = 8793073) B8793073
theorem B15632129 : Blo 2167435 15632129 := bstep (se 2 (by rfl) ⟨5862048, by rfl⟩ : syracuseStep 15632129 = 11724097) B11724097
theorem B41685677 : Blo 2167435 41685677 := bstep (se 3 (by rfl) ⟨7816064, by rfl⟩ : syracuseStep 41685677 = 15632129) B15632129
theorem B27790451 : Blo 2167435 27790451 := bstep (se 1 (by rfl) ⟨20842838, by rfl⟩ : syracuseStep 27790451 = 41685677) B41685677
theorem B18526967 : Blo 2167435 18526967 := bstep (se 1 (by rfl) ⟨13895225, by rfl⟩ : syracuseStep 18526967 = 27790451) B27790451
theorem B12351311 : Blo 2167435 12351311 := bstep (se 1 (by rfl) ⟨9263483, by rfl⟩ : syracuseStep 12351311 = 18526967) B18526967
theorem B8234207 : Blo 2167435 8234207 := bstep (se 1 (by rfl) ⟨6175655, by rfl⟩ : syracuseStep 8234207 = 12351311) B12351311
theorem B5489471 : Blo 2167435 5489471 := bstep (se 1 (by rfl) ⟨4117103, by rfl⟩ : syracuseStep 5489471 = 8234207) B8234207
theorem B3659647 : Blo 2167435 3659647 := bstep (se 1 (by rfl) ⟨2744735, by rfl⟩ : syracuseStep 3659647 = 5489471) B5489471
theorem B4879529 : Blo 2167435 4879529 := bstep (se 2 (by rfl) ⟨1829823, by rfl⟩ : syracuseStep 4879529 = 3659647) B3659647
theorem B3253019 : Blo 2167435 3253019 := bstep (se 1 (by rfl) ⟨2439764, by rfl⟩ : syracuseStep 3253019 = 4879529) B4879529
theorem B2168679 : Blo 2167435 2168679 := bstep (se 1 (by rfl) ⟨1626509, by rfl⟩ : syracuseStep 2168679 = 3253019) B3253019
theorem B2439769 : Blo 2167435 2439769 := bbase (se 2 (by rfl) ⟨914913, by rfl⟩ : syracuseStep 2439769 = 1829827) (by norm_num)
theorem B3253025 : Blo 2167435 3253025 := bstep (se 2 (by rfl) ⟨1219884, by rfl⟩ : syracuseStep 3253025 = 2439769) B2439769
theorem B2168683 : Blo 2167435 2168683 := bstep (se 1 (by rfl) ⟨1626512, by rfl⟩ : syracuseStep 2168683 = 3253025) B3253025
theorem B5564389 : Blo 2167435 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B7419185 : Blo 2167435 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B4946123 : Blo 2167435 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B13189661 : Blo 2167435 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B8793107 : Blo 2167435 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B5862071 : Blo 2167435 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B15632189 : Blo 2167435 15632189 := bstep (se 3 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 15632189 = 5862071) B5862071
theorem B10421459 : Blo 2167435 10421459 := bstep (se 1 (by rfl) ⟨7816094, by rfl⟩ : syracuseStep 10421459 = 15632189) B15632189
theorem B6947639 : Blo 2167435 6947639 := bstep (se 1 (by rfl) ⟨5210729, by rfl⟩ : syracuseStep 6947639 = 10421459) B10421459
theorem B4631759 : Blo 2167435 4631759 := bstep (se 1 (by rfl) ⟨3473819, by rfl⟩ : syracuseStep 4631759 = 6947639) B6947639
theorem B3087839 : Blo 2167435 3087839 := bstep (se 1 (by rfl) ⟨2315879, by rfl⟩ : syracuseStep 3087839 = 4631759) B4631759
theorem B8234237 : Blo 2167435 8234237 := bstep (se 3 (by rfl) ⟨1543919, by rfl⟩ : syracuseStep 8234237 = 3087839) B3087839
theorem B5489491 : Blo 2167435 5489491 := bstep (se 1 (by rfl) ⟨4117118, by rfl⟩ : syracuseStep 5489491 = 8234237) B8234237
theorem B7319321 : Blo 2167435 7319321 := bstep (se 2 (by rfl) ⟨2744745, by rfl⟩ : syracuseStep 7319321 = 5489491) B5489491
theorem B4879547 : Blo 2167435 4879547 := bstep (se 1 (by rfl) ⟨3659660, by rfl⟩ : syracuseStep 4879547 = 7319321) B7319321
theorem B3253031 : Blo 2167435 3253031 := bstep (se 1 (by rfl) ⟨2439773, by rfl⟩ : syracuseStep 3253031 = 4879547) B4879547
theorem B2168687 : Blo 2167435 2168687 := bstep (se 1 (by rfl) ⟨1626515, by rfl⟩ : syracuseStep 2168687 = 3253031) B3253031
theorem B3253037 : Blo 2167435 3253037 := bbase (se 3 (by rfl) ⟨609944, by rfl⟩ : syracuseStep 3253037 = 1219889) (by norm_num)
theorem B2168691 : Blo 2167435 2168691 := bstep (se 1 (by rfl) ⟨1626518, by rfl⟩ : syracuseStep 2168691 = 3253037) B3253037
theorem B4879565 : Blo 2167435 4879565 := bbase (se 3 (by rfl) ⟨914918, by rfl⟩ : syracuseStep 4879565 = 1829837) (by norm_num)
theorem B3253043 : Blo 2167435 3253043 := bstep (se 1 (by rfl) ⟨2439782, by rfl⟩ : syracuseStep 3253043 = 4879565) B4879565
theorem B2168695 : Blo 2167435 2168695 := bstep (se 1 (by rfl) ⟨1626521, by rfl⟩ : syracuseStep 2168695 = 3253043) B3253043
theorem B2744761 : Blo 2167435 2744761 := bbase (se 2 (by rfl) ⟨1029285, by rfl⟩ : syracuseStep 2744761 = 2058571) (by norm_num)
theorem B3659681 : Blo 2167435 3659681 := bstep (se 2 (by rfl) ⟨1372380, by rfl⟩ : syracuseStep 3659681 = 2744761) B2744761
theorem B2439787 : Blo 2167435 2439787 := bstep (se 1 (by rfl) ⟨1829840, by rfl⟩ : syracuseStep 2439787 = 3659681) B3659681
theorem B3253049 : Blo 2167435 3253049 := bstep (se 2 (by rfl) ⟨1219893, by rfl⟩ : syracuseStep 3253049 = 2439787) B2439787
theorem B2168699 : Blo 2167435 2168699 := bstep (se 1 (by rfl) ⟨1626524, by rfl⟩ : syracuseStep 2168699 = 3253049) B3253049
theorem B35652565 : Blo 2167435 35652565 := bbase (se 7 (by rfl) ⟨417803, by rfl⟩ : syracuseStep 35652565 = 835607) (by norm_num)
theorem B47536753 : Blo 2167435 47536753 := bstep (se 2 (by rfl) ⟨17826282, by rfl⟩ : syracuseStep 47536753 = 35652565) B35652565
theorem B63382337 : Blo 2167435 63382337 := bstep (se 2 (by rfl) ⟨23768376, by rfl⟩ : syracuseStep 63382337 = 47536753) B47536753
theorem B42254891 : Blo 2167435 42254891 := bstep (se 1 (by rfl) ⟨31691168, by rfl⟩ : syracuseStep 42254891 = 63382337) B63382337
theorem B28169927 : Blo 2167435 28169927 := bstep (se 1 (by rfl) ⟨21127445, by rfl⟩ : syracuseStep 28169927 = 42254891) B42254891
theorem B18779951 : Blo 2167435 18779951 := bstep (se 1 (by rfl) ⟨14084963, by rfl⟩ : syracuseStep 18779951 = 28169927) B28169927
theorem B12519967 : Blo 2167435 12519967 := bstep (se 1 (by rfl) ⟨9389975, by rfl⟩ : syracuseStep 12519967 = 18779951) B18779951
theorem B16693289 : Blo 2167435 16693289 := bstep (se 2 (by rfl) ⟨6259983, by rfl⟩ : syracuseStep 16693289 = 12519967) B12519967
theorem B11128859 : Blo 2167435 11128859 := bstep (se 1 (by rfl) ⟨8346644, by rfl⟩ : syracuseStep 11128859 = 16693289) B16693289
theorem B7419239 : Blo 2167435 7419239 := bstep (se 1 (by rfl) ⟨5564429, by rfl⟩ : syracuseStep 7419239 = 11128859) B11128859
theorem B4946159 : Blo 2167435 4946159 := bstep (se 1 (by rfl) ⟨3709619, by rfl⟩ : syracuseStep 4946159 = 7419239) B7419239
theorem B3297439 : Blo 2167435 3297439 := bstep (se 1 (by rfl) ⟨2473079, by rfl⟩ : syracuseStep 3297439 = 4946159) B4946159
theorem B17586341 : Blo 2167435 17586341 := bstep (se 4 (by rfl) ⟨1648719, by rfl⟩ : syracuseStep 17586341 = 3297439) B3297439
theorem B11724227 : Blo 2167435 11724227 := bstep (se 1 (by rfl) ⟨8793170, by rfl⟩ : syracuseStep 11724227 = 17586341) B17586341
theorem B7816151 : Blo 2167435 7816151 := bstep (se 1 (by rfl) ⟨5862113, by rfl⟩ : syracuseStep 7816151 = 11724227) B11724227
theorem B5210767 : Blo 2167435 5210767 := bstep (se 1 (by rfl) ⟨3908075, by rfl⟩ : syracuseStep 5210767 = 7816151) B7816151
theorem B6947689 : Blo 2167435 6947689 := bstep (se 2 (by rfl) ⟨2605383, by rfl⟩ : syracuseStep 6947689 = 5210767) B5210767
theorem B9263585 : Blo 2167435 9263585 := bstep (se 2 (by rfl) ⟨3473844, by rfl⟩ : syracuseStep 9263585 = 6947689) B6947689
theorem B24702893 : Blo 2167435 24702893 := bstep (se 3 (by rfl) ⟨4631792, by rfl⟩ : syracuseStep 24702893 = 9263585) B9263585
theorem B16468595 : Blo 2167435 16468595 := bstep (se 1 (by rfl) ⟨12351446, by rfl⟩ : syracuseStep 16468595 = 24702893) B24702893
theorem B10979063 : Blo 2167435 10979063 := bstep (se 1 (by rfl) ⟨8234297, by rfl⟩ : syracuseStep 10979063 = 16468595) B16468595
theorem B7319375 : Blo 2167435 7319375 := bstep (se 1 (by rfl) ⟨5489531, by rfl⟩ : syracuseStep 7319375 = 10979063) B10979063
theorem B4879583 : Blo 2167435 4879583 := bstep (se 1 (by rfl) ⟨3659687, by rfl⟩ : syracuseStep 4879583 = 7319375) B7319375
theorem B3253055 : Blo 2167435 3253055 := bstep (se 1 (by rfl) ⟨2439791, by rfl⟩ : syracuseStep 3253055 = 4879583) B4879583
theorem B2168703 : Blo 2167435 2168703 := bstep (se 1 (by rfl) ⟨1626527, by rfl⟩ : syracuseStep 2168703 = 3253055) B3253055
theorem B3253061 : Blo 2167435 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B2168707 : Blo 2167435 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B3659701 : Blo 2167435 3659701 := bbase (se 5 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 3659701 = 343097) (by norm_num)
theorem B4879601 : Blo 2167435 4879601 := bstep (se 2 (by rfl) ⟨1829850, by rfl⟩ : syracuseStep 4879601 = 3659701) B3659701
theorem B3253067 : Blo 2167435 3253067 := bstep (se 1 (by rfl) ⟨2439800, by rfl⟩ : syracuseStep 3253067 = 4879601) B4879601
theorem B2168711 : Blo 2167435 2168711 := bstep (se 1 (by rfl) ⟨1626533, by rfl⟩ : syracuseStep 2168711 = 3253067) B3253067
theorem B2439805 : Blo 2167435 2439805 := bbase (se 3 (by rfl) ⟨457463, by rfl⟩ : syracuseStep 2439805 = 914927) (by norm_num)
theorem B3253073 : Blo 2167435 3253073 := bstep (se 2 (by rfl) ⟨1219902, by rfl⟩ : syracuseStep 3253073 = 2439805) B2439805
theorem B2168715 : Blo 2167435 2168715 := bstep (se 1 (by rfl) ⟨1626536, by rfl⟩ : syracuseStep 2168715 = 3253073) B3253073
theorem B7319429 : Blo 2167435 7319429 := bbase (se 4 (by rfl) ⟨686196, by rfl⟩ : syracuseStep 7319429 = 1372393) (by norm_num)
theorem B4879619 : Blo 2167435 4879619 := bstep (se 1 (by rfl) ⟨3659714, by rfl⟩ : syracuseStep 4879619 = 7319429) B7319429
theorem B3253079 : Blo 2167435 3253079 := bstep (se 1 (by rfl) ⟨2439809, by rfl⟩ : syracuseStep 3253079 = 4879619) B4879619
theorem B2168719 : Blo 2167435 2168719 := bstep (se 1 (by rfl) ⟨1626539, by rfl⟩ : syracuseStep 2168719 = 3253079) B3253079
theorem B3253085 : Blo 2167435 3253085 := bbase (se 3 (by rfl) ⟨609953, by rfl⟩ : syracuseStep 3253085 = 1219907) (by norm_num)
theorem B2168723 : Blo 2167435 2168723 := bstep (se 1 (by rfl) ⟨1626542, by rfl⟩ : syracuseStep 2168723 = 3253085) B3253085
theorem B4879637 : Blo 2167435 4879637 := bbase (se 6 (by rfl) ⟨114366, by rfl⟩ : syracuseStep 4879637 = 228733) (by norm_num)
theorem B3253091 : Blo 2167435 3253091 := bstep (se 1 (by rfl) ⟨2439818, by rfl⟩ : syracuseStep 3253091 = 4879637) B4879637
theorem B2168727 : Blo 2167435 2168727 := bstep (se 1 (by rfl) ⟨1626545, by rfl⟩ : syracuseStep 2168727 = 3253091) B3253091
theorem B8234405 : Blo 2167435 8234405 := bbase (se 4 (by rfl) ⟨771975, by rfl⟩ : syracuseStep 8234405 = 1543951) (by norm_num)
theorem B5489603 : Blo 2167435 5489603 := bstep (se 1 (by rfl) ⟨4117202, by rfl⟩ : syracuseStep 5489603 = 8234405) B8234405
theorem B3659735 : Blo 2167435 3659735 := bstep (se 1 (by rfl) ⟨2744801, by rfl⟩ : syracuseStep 3659735 = 5489603) B5489603
theorem B2439823 : Blo 2167435 2439823 := bstep (se 1 (by rfl) ⟨1829867, by rfl⟩ : syracuseStep 2439823 = 3659735) B3659735
theorem B3253097 : Blo 2167435 3253097 := bstep (se 2 (by rfl) ⟨1219911, by rfl⟩ : syracuseStep 3253097 = 2439823) B2439823
theorem B2168731 : Blo 2167435 2168731 := bstep (se 1 (by rfl) ⟨1626548, by rfl⟩ : syracuseStep 2168731 = 3253097) B3253097
theorem B4631861 : Blo 2167435 4631861 := bbase (se 5 (by rfl) ⟨217118, by rfl⟩ : syracuseStep 4631861 = 434237) (by norm_num)
theorem B12351629 : Blo 2167435 12351629 := bstep (se 3 (by rfl) ⟨2315930, by rfl⟩ : syracuseStep 12351629 = 4631861) B4631861
theorem B8234419 : Blo 2167435 8234419 := bstep (se 1 (by rfl) ⟨6175814, by rfl⟩ : syracuseStep 8234419 = 12351629) B12351629
theorem B10979225 : Blo 2167435 10979225 := bstep (se 2 (by rfl) ⟨4117209, by rfl⟩ : syracuseStep 10979225 = 8234419) B8234419
theorem B7319483 : Blo 2167435 7319483 := bstep (se 1 (by rfl) ⟨5489612, by rfl⟩ : syracuseStep 7319483 = 10979225) B10979225
theorem B4879655 : Blo 2167435 4879655 := bstep (se 1 (by rfl) ⟨3659741, by rfl⟩ : syracuseStep 4879655 = 7319483) B7319483
theorem B3253103 : Blo 2167435 3253103 := bstep (se 1 (by rfl) ⟨2439827, by rfl⟩ : syracuseStep 3253103 = 4879655) B4879655
theorem B2168735 : Blo 2167435 2168735 := bstep (se 1 (by rfl) ⟨1626551, by rfl⟩ : syracuseStep 2168735 = 3253103) B3253103
theorem B3253109 : Blo 2167435 3253109 := bbase (se 5 (by rfl) ⟨152489, by rfl⟩ : syracuseStep 3253109 = 304979) (by norm_num)
theorem B2168739 : Blo 2167435 2168739 := bstep (se 1 (by rfl) ⟨1626554, by rfl⟩ : syracuseStep 2168739 = 3253109) B3253109
theorem B5564533 : Blo 2167435 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B7419377 : Blo 2167435 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B19785005 : Blo 2167435 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B13190003 : Blo 2167435 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B8793335 : Blo 2167435 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B5862223 : Blo 2167435 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B7816297 : Blo 2167435 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B10421729 : Blo 2167435 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B6947819 : Blo 2167435 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B4631879 : Blo 2167435 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B3087919 : Blo 2167435 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B4117225 : Blo 2167435 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B5489633 : Blo 2167435 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B3659755 : Blo 2167435 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B4879673 : Blo 2167435 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B3253115 : Blo 2167435 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B2168743 : Blo 2167435 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B2439841 : Blo 2167435 2439841 := bbase (se 2 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 2439841 = 1829881) (by norm_num)
theorem B3253121 : Blo 2167435 3253121 := bstep (se 2 (by rfl) ⟨1219920, by rfl⟩ : syracuseStep 3253121 = 2439841) B2439841
theorem B2168747 : Blo 2167435 2168747 := bstep (se 1 (by rfl) ⟨1626560, by rfl⟩ : syracuseStep 2168747 = 3253121) B3253121
theorem B5489653 : Blo 2167435 5489653 := bbase (se 5 (by rfl) ⟨257327, by rfl⟩ : syracuseStep 5489653 = 514655) (by norm_num)
theorem B7319537 : Blo 2167435 7319537 := bstep (se 2 (by rfl) ⟨2744826, by rfl⟩ : syracuseStep 7319537 = 5489653) B5489653
theorem B4879691 : Blo 2167435 4879691 := bstep (se 1 (by rfl) ⟨3659768, by rfl⟩ : syracuseStep 4879691 = 7319537) B7319537
theorem B3253127 : Blo 2167435 3253127 := bstep (se 1 (by rfl) ⟨2439845, by rfl⟩ : syracuseStep 3253127 = 4879691) B4879691
theorem B2168751 : Blo 2167435 2168751 := bstep (se 1 (by rfl) ⟨1626563, by rfl⟩ : syracuseStep 2168751 = 3253127) B3253127
theorem B3253133 : Blo 2167435 3253133 := bbase (se 3 (by rfl) ⟨609962, by rfl⟩ : syracuseStep 3253133 = 1219925) (by norm_num)
theorem B2168755 : Blo 2167435 2168755 := bstep (se 1 (by rfl) ⟨1626566, by rfl⟩ : syracuseStep 2168755 = 3253133) B3253133
theorem B4879709 : Blo 2167435 4879709 := bbase (se 3 (by rfl) ⟨914945, by rfl⟩ : syracuseStep 4879709 = 1829891) (by norm_num)
theorem B3253139 : Blo 2167435 3253139 := bstep (se 1 (by rfl) ⟨2439854, by rfl⟩ : syracuseStep 3253139 = 4879709) B4879709
theorem B2168759 : Blo 2167435 2168759 := bstep (se 1 (by rfl) ⟨1626569, by rfl⟩ : syracuseStep 2168759 = 3253139) B3253139
theorem B3659789 : Blo 2167435 3659789 := bbase (se 3 (by rfl) ⟨686210, by rfl⟩ : syracuseStep 3659789 = 1372421) (by norm_num)
theorem B2439859 : Blo 2167435 2439859 := bstep (se 1 (by rfl) ⟨1829894, by rfl⟩ : syracuseStep 2439859 = 3659789) B3659789
theorem B3253145 : Blo 2167435 3253145 := bstep (se 2 (by rfl) ⟨1219929, by rfl⟩ : syracuseStep 3253145 = 2439859) B2439859
theorem B2168763 : Blo 2167435 2168763 := bstep (se 1 (by rfl) ⟨1626572, by rfl⟩ : syracuseStep 2168763 = 3253145) B3253145
theorem B2782297 : Blo 2167435 2782297 := bbase (se 2 (by rfl) ⟨1043361, by rfl⟩ : syracuseStep 2782297 = 2086723) (by norm_num)
theorem B3709729 : Blo 2167435 3709729 := bstep (se 2 (by rfl) ⟨1391148, by rfl⟩ : syracuseStep 3709729 = 2782297) B2782297
theorem B19785221 : Blo 2167435 19785221 := bstep (se 4 (by rfl) ⟨1854864, by rfl⟩ : syracuseStep 19785221 = 3709729) B3709729
theorem B13190147 : Blo 2167435 13190147 := bstep (se 1 (by rfl) ⟨9892610, by rfl⟩ : syracuseStep 13190147 = 19785221) B19785221
theorem B8793431 : Blo 2167435 8793431 := bstep (se 1 (by rfl) ⟨6595073, by rfl⟩ : syracuseStep 8793431 = 13190147) B13190147
theorem B5862287 : Blo 2167435 5862287 := bstep (se 1 (by rfl) ⟨4396715, by rfl⟩ : syracuseStep 5862287 = 8793431) B8793431
theorem B3908191 : Blo 2167435 3908191 := bstep (se 1 (by rfl) ⟨2931143, by rfl⟩ : syracuseStep 3908191 = 5862287) B5862287
theorem B5210921 : Blo 2167435 5210921 := bstep (se 2 (by rfl) ⟨1954095, by rfl⟩ : syracuseStep 5210921 = 3908191) B3908191
theorem B3473947 : Blo 2167435 3473947 := bstep (se 1 (by rfl) ⟨2605460, by rfl⟩ : syracuseStep 3473947 = 5210921) B5210921
theorem B18527717 : Blo 2167435 18527717 := bstep (se 4 (by rfl) ⟨1736973, by rfl⟩ : syracuseStep 18527717 = 3473947) B3473947
theorem B12351811 : Blo 2167435 12351811 := bstep (se 1 (by rfl) ⟨9263858, by rfl⟩ : syracuseStep 12351811 = 18527717) B18527717
theorem B16469081 : Blo 2167435 16469081 := bstep (se 2 (by rfl) ⟨6175905, by rfl⟩ : syracuseStep 16469081 = 12351811) B12351811
theorem B10979387 : Blo 2167435 10979387 := bstep (se 1 (by rfl) ⟨8234540, by rfl⟩ : syracuseStep 10979387 = 16469081) B16469081
theorem B7319591 : Blo 2167435 7319591 := bstep (se 1 (by rfl) ⟨5489693, by rfl⟩ : syracuseStep 7319591 = 10979387) B10979387
theorem B4879727 : Blo 2167435 4879727 := bstep (se 1 (by rfl) ⟨3659795, by rfl⟩ : syracuseStep 4879727 = 7319591) B7319591
theorem B3253151 : Blo 2167435 3253151 := bstep (se 1 (by rfl) ⟨2439863, by rfl⟩ : syracuseStep 3253151 = 4879727) B4879727
theorem B2168767 : Blo 2167435 2168767 := bstep (se 1 (by rfl) ⟨1626575, by rfl⟩ : syracuseStep 2168767 = 3253151) B3253151
theorem B3253157 : Blo 2167435 3253157 := bbase (se 4 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 3253157 = 609967) (by norm_num)
theorem B2168771 : Blo 2167435 2168771 := bstep (se 1 (by rfl) ⟨1626578, by rfl⟩ : syracuseStep 2168771 = 3253157) B3253157
theorem B2744857 : Blo 2167435 2744857 := bbase (se 2 (by rfl) ⟨1029321, by rfl⟩ : syracuseStep 2744857 = 2058643) (by norm_num)
theorem B3659809 : Blo 2167435 3659809 := bstep (se 2 (by rfl) ⟨1372428, by rfl⟩ : syracuseStep 3659809 = 2744857) B2744857
theorem B4879745 : Blo 2167435 4879745 := bstep (se 2 (by rfl) ⟨1829904, by rfl⟩ : syracuseStep 4879745 = 3659809) B3659809
theorem B3253163 : Blo 2167435 3253163 := bstep (se 1 (by rfl) ⟨2439872, by rfl⟩ : syracuseStep 3253163 = 4879745) B4879745
theorem B2168775 : Blo 2167435 2168775 := bstep (se 1 (by rfl) ⟨1626581, by rfl⟩ : syracuseStep 2168775 = 3253163) B3253163
theorem B2439877 : Blo 2167435 2439877 := bbase (se 4 (by rfl) ⟨228738, by rfl⟩ : syracuseStep 2439877 = 457477) (by norm_num)
theorem B3253169 : Blo 2167435 3253169 := bstep (se 2 (by rfl) ⟨1219938, by rfl⟩ : syracuseStep 3253169 = 2439877) B2439877
theorem B2168779 : Blo 2167435 2168779 := bstep (se 1 (by rfl) ⟨1626584, by rfl⟩ : syracuseStep 2168779 = 3253169) B3253169
theorem B4117301 : Blo 2167435 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B2744867 : Blo 2167435 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B7319645 : Blo 2167435 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B4879763 : Blo 2167435 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B3253175 : Blo 2167435 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B2168783 : Blo 2167435 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B3253181 : Blo 2167435 3253181 := bbase (se 3 (by rfl) ⟨609971, by rfl⟩ : syracuseStep 3253181 = 1219943) (by norm_num)
theorem B2168787 : Blo 2167435 2168787 := bstep (se 1 (by rfl) ⟨1626590, by rfl⟩ : syracuseStep 2168787 = 3253181) B3253181
theorem B4879781 : Blo 2167435 4879781 := bbase (se 4 (by rfl) ⟨457479, by rfl⟩ : syracuseStep 4879781 = 914959) (by norm_num)
theorem B3253187 : Blo 2167435 3253187 := bstep (se 1 (by rfl) ⟨2439890, by rfl⟩ : syracuseStep 3253187 = 4879781) B4879781
theorem B2168791 : Blo 2167435 2168791 := bstep (se 1 (by rfl) ⟨1626593, by rfl⟩ : syracuseStep 2168791 = 3253187) B3253187
theorem B5489765 : Blo 2167435 5489765 := bbase (se 4 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 5489765 = 1029331) (by norm_num)
theorem B3659843 : Blo 2167435 3659843 := bstep (se 1 (by rfl) ⟨2744882, by rfl⟩ : syracuseStep 3659843 = 5489765) B5489765
theorem B2439895 : Blo 2167435 2439895 := bstep (se 1 (by rfl) ⟨1829921, by rfl⟩ : syracuseStep 2439895 = 3659843) B3659843
theorem B3253193 : Blo 2167435 3253193 := bstep (se 2 (by rfl) ⟨1219947, by rfl⟩ : syracuseStep 3253193 = 2439895) B2439895
theorem B2168795 : Blo 2167435 2168795 := bstep (se 1 (by rfl) ⟨1626596, by rfl⟩ : syracuseStep 2168795 = 3253193) B3253193
theorem B4396781 : Blo 2167435 4396781 := bbase (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) (by norm_num)
theorem B11724749 : Blo 2167435 11724749 := bstep (se 3 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 11724749 = 4396781) B4396781
theorem B7816499 : Blo 2167435 7816499 := bstep (se 1 (by rfl) ⟨5862374, by rfl⟩ : syracuseStep 7816499 = 11724749) B11724749
theorem B5210999 : Blo 2167435 5210999 := bstep (se 1 (by rfl) ⟨3908249, by rfl⟩ : syracuseStep 5210999 = 7816499) B7816499
theorem B3473999 : Blo 2167435 3473999 := bstep (se 1 (by rfl) ⟨2605499, by rfl⟩ : syracuseStep 3473999 = 5210999) B5210999
theorem B2315999 : Blo 2167435 2315999 := bstep (se 1 (by rfl) ⟨1736999, by rfl⟩ : syracuseStep 2315999 = 3473999) B3473999
theorem B6175997 : Blo 2167435 6175997 := bstep (se 3 (by rfl) ⟨1157999, by rfl⟩ : syracuseStep 6175997 = 2315999) B2315999
theorem B4117331 : Blo 2167435 4117331 := bstep (se 1 (by rfl) ⟨3087998, by rfl⟩ : syracuseStep 4117331 = 6175997) B6175997
theorem B10979549 : Blo 2167435 10979549 := bstep (se 3 (by rfl) ⟨2058665, by rfl⟩ : syracuseStep 10979549 = 4117331) B4117331
theorem B7319699 : Blo 2167435 7319699 := bstep (se 1 (by rfl) ⟨5489774, by rfl⟩ : syracuseStep 7319699 = 10979549) B10979549
theorem B4879799 : Blo 2167435 4879799 := bstep (se 1 (by rfl) ⟨3659849, by rfl⟩ : syracuseStep 4879799 = 7319699) B7319699
theorem B3253199 : Blo 2167435 3253199 := bstep (se 1 (by rfl) ⟨2439899, by rfl⟩ : syracuseStep 3253199 = 4879799) B4879799
theorem B2168799 : Blo 2167435 2168799 := bstep (se 1 (by rfl) ⟨1626599, by rfl⟩ : syracuseStep 2168799 = 3253199) B3253199
theorem B3253205 : Blo 2167435 3253205 := bbase (se 7 (by rfl) ⟨38123, by rfl⟩ : syracuseStep 3253205 = 76247) (by norm_num)
theorem B2168803 : Blo 2167435 2168803 := bstep (se 1 (by rfl) ⟨1626602, by rfl⟩ : syracuseStep 2168803 = 3253205) B3253205
theorem B8234693 : Blo 2167435 8234693 := bbase (se 4 (by rfl) ⟨772002, by rfl⟩ : syracuseStep 8234693 = 1544005) (by norm_num)
theorem B5489795 : Blo 2167435 5489795 := bstep (se 1 (by rfl) ⟨4117346, by rfl⟩ : syracuseStep 5489795 = 8234693) B8234693
theorem B3659863 : Blo 2167435 3659863 := bstep (se 1 (by rfl) ⟨2744897, by rfl⟩ : syracuseStep 3659863 = 5489795) B5489795
theorem B4879817 : Blo 2167435 4879817 := bstep (se 2 (by rfl) ⟨1829931, by rfl⟩ : syracuseStep 4879817 = 3659863) B3659863
theorem B3253211 : Blo 2167435 3253211 := bstep (se 1 (by rfl) ⟨2439908, by rfl⟩ : syracuseStep 3253211 = 4879817) B4879817
theorem B2168807 : Blo 2167435 2168807 := bstep (se 1 (by rfl) ⟨1626605, by rfl⟩ : syracuseStep 2168807 = 3253211) B3253211
theorem B2439913 : Blo 2167435 2439913 := bbase (se 2 (by rfl) ⟨914967, by rfl⟩ : syracuseStep 2439913 = 1829935) (by norm_num)
theorem B3253217 : Blo 2167435 3253217 := bstep (se 2 (by rfl) ⟨1219956, by rfl⟩ : syracuseStep 3253217 = 2439913) B2439913
theorem B2168811 : Blo 2167435 2168811 := bstep (se 1 (by rfl) ⟨1626608, by rfl⟩ : syracuseStep 2168811 = 3253217) B3253217
theorem B12352085 : Blo 2167435 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B8234723 : Blo 2167435 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B5489815 : Blo 2167435 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B7319753 : Blo 2167435 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B4879835 : Blo 2167435 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B3253223 : Blo 2167435 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B2168815 : Blo 2167435 2168815 := bstep (se 1 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 2168815 = 3253223) B3253223
theorem B3253229 : Blo 2167435 3253229 := bbase (se 3 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 3253229 = 1219961) (by norm_num)
theorem B2168819 : Blo 2167435 2168819 := bstep (se 1 (by rfl) ⟨1626614, by rfl⟩ : syracuseStep 2168819 = 3253229) B3253229
theorem B4879853 : Blo 2167435 4879853 := bbase (se 3 (by rfl) ⟨914972, by rfl⟩ : syracuseStep 4879853 = 1829945) (by norm_num)
theorem B3253235 : Blo 2167435 3253235 := bstep (se 1 (by rfl) ⟨2439926, by rfl⟩ : syracuseStep 3253235 = 4879853) B4879853
theorem B2168823 : Blo 2167435 2168823 := bstep (se 1 (by rfl) ⟨1626617, by rfl⟩ : syracuseStep 2168823 = 3253235) B3253235
theorem B3297629 : Blo 2167435 3297629 := bbase (se 3 (by rfl) ⟨618305, by rfl⟩ : syracuseStep 3297629 = 1236611) (by norm_num)
theorem B8793677 : Blo 2167435 8793677 := bstep (se 3 (by rfl) ⟨1648814, by rfl⟩ : syracuseStep 8793677 = 3297629) B3297629
theorem B5862451 : Blo 2167435 5862451 := bstep (se 1 (by rfl) ⟨4396838, by rfl⟩ : syracuseStep 5862451 = 8793677) B8793677
theorem B7816601 : Blo 2167435 7816601 := bstep (se 2 (by rfl) ⟨2931225, by rfl⟩ : syracuseStep 7816601 = 5862451) B5862451
theorem B5211067 : Blo 2167435 5211067 := bstep (se 1 (by rfl) ⟨3908300, by rfl⟩ : syracuseStep 5211067 = 7816601) B7816601
theorem B6948089 : Blo 2167435 6948089 := bstep (se 2 (by rfl) ⟨2605533, by rfl⟩ : syracuseStep 6948089 = 5211067) B5211067
theorem B4632059 : Blo 2167435 4632059 := bstep (se 1 (by rfl) ⟨3474044, by rfl⟩ : syracuseStep 4632059 = 6948089) B6948089
theorem B3088039 : Blo 2167435 3088039 := bstep (se 1 (by rfl) ⟨2316029, by rfl⟩ : syracuseStep 3088039 = 4632059) B4632059
theorem B4117385 : Blo 2167435 4117385 := bstep (se 2 (by rfl) ⟨1544019, by rfl⟩ : syracuseStep 4117385 = 3088039) B3088039
theorem B2744923 : Blo 2167435 2744923 := bstep (se 1 (by rfl) ⟨2058692, by rfl⟩ : syracuseStep 2744923 = 4117385) B4117385
theorem B3659897 : Blo 2167435 3659897 := bstep (se 2 (by rfl) ⟨1372461, by rfl⟩ : syracuseStep 3659897 = 2744923) B2744923
theorem B2439931 : Blo 2167435 2439931 := bstep (se 1 (by rfl) ⟨1829948, by rfl⟩ : syracuseStep 2439931 = 3659897) B3659897
theorem B3253241 : Blo 2167435 3253241 := bstep (se 2 (by rfl) ⟨1219965, by rfl⟩ : syracuseStep 3253241 = 2439931) B2439931
theorem B2168827 : Blo 2167435 2168827 := bstep (se 1 (by rfl) ⟨1626620, by rfl⟩ : syracuseStep 2168827 = 3253241) B3253241
theorem B11724917 : Blo 2167435 11724917 := bbase (se 5 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 11724917 = 1099211) (by norm_num)
theorem B125065781 : Blo 2167435 125065781 := bstep (se 5 (by rfl) ⟨5862458, by rfl⟩ : syracuseStep 125065781 = 11724917) B11724917
theorem B83377187 : Blo 2167435 83377187 := bstep (se 1 (by rfl) ⟨62532890, by rfl⟩ : syracuseStep 83377187 = 125065781) B125065781
theorem B55584791 : Blo 2167435 55584791 := bstep (se 1 (by rfl) ⟨41688593, by rfl⟩ : syracuseStep 55584791 = 83377187) B83377187
theorem B37056527 : Blo 2167435 37056527 := bstep (se 1 (by rfl) ⟨27792395, by rfl⟩ : syracuseStep 37056527 = 55584791) B55584791
theorem B24704351 : Blo 2167435 24704351 := bstep (se 1 (by rfl) ⟨18528263, by rfl⟩ : syracuseStep 24704351 = 37056527) B37056527
theorem B16469567 : Blo 2167435 16469567 := bstep (se 1 (by rfl) ⟨12352175, by rfl⟩ : syracuseStep 16469567 = 24704351) B24704351
theorem B10979711 : Blo 2167435 10979711 := bstep (se 1 (by rfl) ⟨8234783, by rfl⟩ : syracuseStep 10979711 = 16469567) B16469567
theorem B7319807 : Blo 2167435 7319807 := bstep (se 1 (by rfl) ⟨5489855, by rfl⟩ : syracuseStep 7319807 = 10979711) B10979711
theorem B4879871 : Blo 2167435 4879871 := bstep (se 1 (by rfl) ⟨3659903, by rfl⟩ : syracuseStep 4879871 = 7319807) B7319807
theorem B3253247 : Blo 2167435 3253247 := bstep (se 1 (by rfl) ⟨2439935, by rfl⟩ : syracuseStep 3253247 = 4879871) B4879871
theorem B2168831 : Blo 2167435 2168831 := bstep (se 1 (by rfl) ⟨1626623, by rfl⟩ : syracuseStep 2168831 = 3253247) B3253247
theorem B3253253 : Blo 2167435 3253253 := bbase (se 4 (by rfl) ⟨304992, by rfl⟩ : syracuseStep 3253253 = 609985) (by norm_num)
theorem B2168835 : Blo 2167435 2168835 := bstep (se 1 (by rfl) ⟨1626626, by rfl⟩ : syracuseStep 2168835 = 3253253) B3253253
theorem B3659917 : Blo 2167435 3659917 := bbase (se 3 (by rfl) ⟨686234, by rfl⟩ : syracuseStep 3659917 = 1372469) (by norm_num)
theorem B4879889 : Blo 2167435 4879889 := bstep (se 2 (by rfl) ⟨1829958, by rfl⟩ : syracuseStep 4879889 = 3659917) B3659917
theorem B3253259 : Blo 2167435 3253259 := bstep (se 1 (by rfl) ⟨2439944, by rfl⟩ : syracuseStep 3253259 = 4879889) B4879889
theorem B2168839 : Blo 2167435 2168839 := bstep (se 1 (by rfl) ⟨1626629, by rfl⟩ : syracuseStep 2168839 = 3253259) B3253259
theorem B2439949 : Blo 2167435 2439949 := bbase (se 3 (by rfl) ⟨457490, by rfl⟩ : syracuseStep 2439949 = 914981) (by norm_num)
theorem B3253265 : Blo 2167435 3253265 := bstep (se 2 (by rfl) ⟨1219974, by rfl⟩ : syracuseStep 3253265 = 2439949) B2439949
theorem B2168843 : Blo 2167435 2168843 := bstep (se 1 (by rfl) ⟨1626632, by rfl⟩ : syracuseStep 2168843 = 3253265) B3253265
theorem B7319861 : Blo 2167435 7319861 := bbase (se 5 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 7319861 = 686237) (by norm_num)
theorem B4879907 : Blo 2167435 4879907 := bstep (se 1 (by rfl) ⟨3659930, by rfl⟩ : syracuseStep 4879907 = 7319861) B7319861
theorem B3253271 : Blo 2167435 3253271 := bstep (se 1 (by rfl) ⟨2439953, by rfl⟩ : syracuseStep 3253271 = 4879907) B4879907
theorem B2168847 : Blo 2167435 2168847 := bstep (se 1 (by rfl) ⟨1626635, by rfl⟩ : syracuseStep 2168847 = 3253271) B3253271
theorem B3253277 : Blo 2167435 3253277 := bbase (se 3 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 3253277 = 1219979) (by norm_num)
theorem B2168851 : Blo 2167435 2168851 := bstep (se 1 (by rfl) ⟨1626638, by rfl⟩ : syracuseStep 2168851 = 3253277) B3253277
theorem B4879925 : Blo 2167435 4879925 := bbase (se 5 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 4879925 = 457493) (by norm_num)
theorem B3253283 : Blo 2167435 3253283 := bstep (se 1 (by rfl) ⟨2439962, by rfl⟩ : syracuseStep 3253283 = 4879925) B4879925
theorem B2168855 : Blo 2167435 2168855 := bstep (se 1 (by rfl) ⟨1626641, by rfl⟩ : syracuseStep 2168855 = 3253283) B3253283
theorem B3297677 : Blo 2167435 3297677 := bbase (se 3 (by rfl) ⟨618314, by rfl⟩ : syracuseStep 3297677 = 1236629) (by norm_num)
theorem B8793805 : Blo 2167435 8793805 := bstep (se 3 (by rfl) ⟨1648838, by rfl⟩ : syracuseStep 8793805 = 3297677) B3297677
theorem B11725073 : Blo 2167435 11725073 := bstep (se 2 (by rfl) ⟨4396902, by rfl⟩ : syracuseStep 11725073 = 8793805) B8793805
theorem B7816715 : Blo 2167435 7816715 := bstep (se 1 (by rfl) ⟨5862536, by rfl⟩ : syracuseStep 7816715 = 11725073) B11725073
theorem B5211143 : Blo 2167435 5211143 := bstep (se 1 (by rfl) ⟨3908357, by rfl⟩ : syracuseStep 5211143 = 7816715) B7816715
theorem B3474095 : Blo 2167435 3474095 := bstep (se 1 (by rfl) ⟨2605571, by rfl⟩ : syracuseStep 3474095 = 5211143) B5211143
theorem B9264253 : Blo 2167435 9264253 := bstep (se 3 (by rfl) ⟨1737047, by rfl⟩ : syracuseStep 9264253 = 3474095) B3474095
theorem B12352337 : Blo 2167435 12352337 := bstep (se 2 (by rfl) ⟨4632126, by rfl⟩ : syracuseStep 12352337 = 9264253) B9264253
theorem B8234891 : Blo 2167435 8234891 := bstep (se 1 (by rfl) ⟨6176168, by rfl⟩ : syracuseStep 8234891 = 12352337) B12352337
theorem B5489927 : Blo 2167435 5489927 := bstep (se 1 (by rfl) ⟨4117445, by rfl⟩ : syracuseStep 5489927 = 8234891) B8234891
theorem B3659951 : Blo 2167435 3659951 := bstep (se 1 (by rfl) ⟨2744963, by rfl⟩ : syracuseStep 3659951 = 5489927) B5489927
theorem B2439967 : Blo 2167435 2439967 := bstep (se 1 (by rfl) ⟨1829975, by rfl⟩ : syracuseStep 2439967 = 3659951) B3659951
theorem B3253289 : Blo 2167435 3253289 := bstep (se 2 (by rfl) ⟨1219983, by rfl⟩ : syracuseStep 3253289 = 2439967) B2439967
theorem B2168859 : Blo 2167435 2168859 := bstep (se 1 (by rfl) ⟨1626644, by rfl⟩ : syracuseStep 2168859 = 3253289) B3253289
theorem B3474101 : Blo 2167435 3474101 := bbase (se 5 (by rfl) ⟨162848, by rfl⟩ : syracuseStep 3474101 = 325697) (by norm_num)
theorem B9264269 : Blo 2167435 9264269 := bstep (se 3 (by rfl) ⟨1737050, by rfl⟩ : syracuseStep 9264269 = 3474101) B3474101
theorem B6176179 : Blo 2167435 6176179 := bstep (se 1 (by rfl) ⟨4632134, by rfl⟩ : syracuseStep 6176179 = 9264269) B9264269
theorem B8234905 : Blo 2167435 8234905 := bstep (se 2 (by rfl) ⟨3088089, by rfl⟩ : syracuseStep 8234905 = 6176179) B6176179
theorem B10979873 : Blo 2167435 10979873 := bstep (se 2 (by rfl) ⟨4117452, by rfl⟩ : syracuseStep 10979873 = 8234905) B8234905
theorem B7319915 : Blo 2167435 7319915 := bstep (se 1 (by rfl) ⟨5489936, by rfl⟩ : syracuseStep 7319915 = 10979873) B10979873
theorem B4879943 : Blo 2167435 4879943 := bstep (se 1 (by rfl) ⟨3659957, by rfl⟩ : syracuseStep 4879943 = 7319915) B7319915
theorem B3253295 : Blo 2167435 3253295 := bstep (se 1 (by rfl) ⟨2439971, by rfl⟩ : syracuseStep 3253295 = 4879943) B4879943
theorem B2168863 : Blo 2167435 2168863 := bstep (se 1 (by rfl) ⟨1626647, by rfl⟩ : syracuseStep 2168863 = 3253295) B3253295
theorem B3253301 : Blo 2167435 3253301 := bbase (se 5 (by rfl) ⟨152498, by rfl⟩ : syracuseStep 3253301 = 304997) (by norm_num)
theorem B2168867 : Blo 2167435 2168867 := bstep (se 1 (by rfl) ⟨1626650, by rfl⟩ : syracuseStep 2168867 = 3253301) B3253301
theorem B5489957 : Blo 2167435 5489957 := bbase (se 4 (by rfl) ⟨514683, by rfl⟩ : syracuseStep 5489957 = 1029367) (by norm_num)
theorem B3659971 : Blo 2167435 3659971 := bstep (se 1 (by rfl) ⟨2744978, by rfl⟩ : syracuseStep 3659971 = 5489957) B5489957
theorem B4879961 : Blo 2167435 4879961 := bstep (se 2 (by rfl) ⟨1829985, by rfl⟩ : syracuseStep 4879961 = 3659971) B3659971
theorem B3253307 : Blo 2167435 3253307 := bstep (se 1 (by rfl) ⟨2439980, by rfl⟩ : syracuseStep 3253307 = 4879961) B4879961
theorem B2168871 : Blo 2167435 2168871 := bstep (se 1 (by rfl) ⟨1626653, by rfl⟩ : syracuseStep 2168871 = 3253307) B3253307
theorem B2439985 : Blo 2167435 2439985 := bbase (se 2 (by rfl) ⟨914994, by rfl⟩ : syracuseStep 2439985 = 1829989) (by norm_num)
theorem B3253313 : Blo 2167435 3253313 := bstep (se 2 (by rfl) ⟨1219992, by rfl⟩ : syracuseStep 3253313 = 2439985) B2439985
theorem B2168875 : Blo 2167435 2168875 := bstep (se 1 (by rfl) ⟨1626656, by rfl⟩ : syracuseStep 2168875 = 3253313) B3253313
theorem B2782441 : Blo 2167435 2782441 := bbase (se 2 (by rfl) ⟨1043415, by rfl⟩ : syracuseStep 2782441 = 2086831) (by norm_num)
theorem B14839685 : Blo 2167435 14839685 := bstep (se 4 (by rfl) ⟨1391220, by rfl⟩ : syracuseStep 14839685 = 2782441) B2782441
theorem B9893123 : Blo 2167435 9893123 := bstep (se 1 (by rfl) ⟨7419842, by rfl⟩ : syracuseStep 9893123 = 14839685) B14839685
theorem B6595415 : Blo 2167435 6595415 := bstep (se 1 (by rfl) ⟨4946561, by rfl⟩ : syracuseStep 6595415 = 9893123) B9893123
theorem B4396943 : Blo 2167435 4396943 := bstep (se 1 (by rfl) ⟨3297707, by rfl⟩ : syracuseStep 4396943 = 6595415) B6595415
theorem B11725181 : Blo 2167435 11725181 := bstep (se 3 (by rfl) ⟨2198471, by rfl⟩ : syracuseStep 11725181 = 4396943) B4396943
theorem B7816787 : Blo 2167435 7816787 := bstep (se 1 (by rfl) ⟨5862590, by rfl⟩ : syracuseStep 7816787 = 11725181) B11725181
theorem B5211191 : Blo 2167435 5211191 := bstep (se 1 (by rfl) ⟨3908393, by rfl⟩ : syracuseStep 5211191 = 7816787) B7816787
theorem B3474127 : Blo 2167435 3474127 := bstep (se 1 (by rfl) ⟨2605595, by rfl⟩ : syracuseStep 3474127 = 5211191) B5211191
theorem B4632169 : Blo 2167435 4632169 := bstep (se 2 (by rfl) ⟨1737063, by rfl⟩ : syracuseStep 4632169 = 3474127) B3474127
theorem B6176225 : Blo 2167435 6176225 := bstep (se 2 (by rfl) ⟨2316084, by rfl⟩ : syracuseStep 6176225 = 4632169) B4632169
theorem B4117483 : Blo 2167435 4117483 := bstep (se 1 (by rfl) ⟨3088112, by rfl⟩ : syracuseStep 4117483 = 6176225) B6176225
theorem B5489977 : Blo 2167435 5489977 := bstep (se 2 (by rfl) ⟨2058741, by rfl⟩ : syracuseStep 5489977 = 4117483) B4117483
theorem B7319969 : Blo 2167435 7319969 := bstep (se 2 (by rfl) ⟨2744988, by rfl⟩ : syracuseStep 7319969 = 5489977) B5489977
theorem B4879979 : Blo 2167435 4879979 := bstep (se 1 (by rfl) ⟨3659984, by rfl⟩ : syracuseStep 4879979 = 7319969) B7319969
theorem B3253319 : Blo 2167435 3253319 := bstep (se 1 (by rfl) ⟨2439989, by rfl⟩ : syracuseStep 3253319 = 4879979) B4879979
theorem B2168879 : Blo 2167435 2168879 := bstep (se 1 (by rfl) ⟨1626659, by rfl⟩ : syracuseStep 2168879 = 3253319) B3253319
theorem B3253325 : Blo 2167435 3253325 := bbase (se 3 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 3253325 = 1219997) (by norm_num)
theorem B2168883 : Blo 2167435 2168883 := bstep (se 1 (by rfl) ⟨1626662, by rfl⟩ : syracuseStep 2168883 = 3253325) B3253325
theorem B4879997 : Blo 2167435 4879997 := bbase (se 3 (by rfl) ⟨914999, by rfl⟩ : syracuseStep 4879997 = 1829999) (by norm_num)
theorem B3253331 : Blo 2167435 3253331 := bstep (se 1 (by rfl) ⟨2439998, by rfl⟩ : syracuseStep 3253331 = 4879997) B4879997
theorem B2168887 : Blo 2167435 2168887 := bstep (se 1 (by rfl) ⟨1626665, by rfl⟩ : syracuseStep 2168887 = 3253331) B3253331
theorem B3660005 : Blo 2167435 3660005 := bbase (se 4 (by rfl) ⟨343125, by rfl⟩ : syracuseStep 3660005 = 686251) (by norm_num)
theorem B2440003 : Blo 2167435 2440003 := bstep (se 1 (by rfl) ⟨1830002, by rfl⟩ : syracuseStep 2440003 = 3660005) B3660005
theorem B3253337 : Blo 2167435 3253337 := bstep (se 2 (by rfl) ⟨1220001, by rfl⟩ : syracuseStep 3253337 = 2440003) B2440003
theorem B2168891 : Blo 2167435 2168891 := bstep (se 1 (by rfl) ⟨1626668, by rfl⟩ : syracuseStep 2168891 = 3253337) B3253337
theorem B5211229 : Blo 2167435 5211229 := bbase (se 3 (by rfl) ⟨977105, by rfl⟩ : syracuseStep 5211229 = 1954211) (by norm_num)
theorem B6948305 : Blo 2167435 6948305 := bstep (se 2 (by rfl) ⟨2605614, by rfl⟩ : syracuseStep 6948305 = 5211229) B5211229
theorem B4632203 : Blo 2167435 4632203 := bstep (se 1 (by rfl) ⟨3474152, by rfl⟩ : syracuseStep 4632203 = 6948305) B6948305
theorem B3088135 : Blo 2167435 3088135 := bstep (se 1 (by rfl) ⟨2316101, by rfl⟩ : syracuseStep 3088135 = 4632203) B4632203
theorem B16470053 : Blo 2167435 16470053 := bstep (se 4 (by rfl) ⟨1544067, by rfl⟩ : syracuseStep 16470053 = 3088135) B3088135
theorem B10980035 : Blo 2167435 10980035 := bstep (se 1 (by rfl) ⟨8235026, by rfl⟩ : syracuseStep 10980035 = 16470053) B16470053
theorem B7320023 : Blo 2167435 7320023 := bstep (se 1 (by rfl) ⟨5490017, by rfl⟩ : syracuseStep 7320023 = 10980035) B10980035
theorem B4880015 : Blo 2167435 4880015 := bstep (se 1 (by rfl) ⟨3660011, by rfl⟩ : syracuseStep 4880015 = 7320023) B7320023
theorem B3253343 : Blo 2167435 3253343 := bstep (se 1 (by rfl) ⟨2440007, by rfl⟩ : syracuseStep 3253343 = 4880015) B4880015
theorem B2168895 : Blo 2167435 2168895 := bstep (se 1 (by rfl) ⟨1626671, by rfl⟩ : syracuseStep 2168895 = 3253343) B3253343
theorem B3253349 : Blo 2167435 3253349 := bbase (se 4 (by rfl) ⟨305001, by rfl⟩ : syracuseStep 3253349 = 610003) (by norm_num)
theorem B2168899 : Blo 2167435 2168899 := bstep (se 1 (by rfl) ⟨1626674, by rfl⟩ : syracuseStep 2168899 = 3253349) B3253349
theorem B4632221 : Blo 2167435 4632221 := bbase (se 3 (by rfl) ⟨868541, by rfl⟩ : syracuseStep 4632221 = 1737083) (by norm_num)
theorem B3088147 : Blo 2167435 3088147 := bstep (se 1 (by rfl) ⟨2316110, by rfl⟩ : syracuseStep 3088147 = 4632221) B4632221
theorem B4117529 : Blo 2167435 4117529 := bstep (se 2 (by rfl) ⟨1544073, by rfl⟩ : syracuseStep 4117529 = 3088147) B3088147
theorem B2745019 : Blo 2167435 2745019 := bstep (se 1 (by rfl) ⟨2058764, by rfl⟩ : syracuseStep 2745019 = 4117529) B4117529
theorem B3660025 : Blo 2167435 3660025 := bstep (se 2 (by rfl) ⟨1372509, by rfl⟩ : syracuseStep 3660025 = 2745019) B2745019
theorem B4880033 : Blo 2167435 4880033 := bstep (se 2 (by rfl) ⟨1830012, by rfl⟩ : syracuseStep 4880033 = 3660025) B3660025
theorem B3253355 : Blo 2167435 3253355 := bstep (se 1 (by rfl) ⟨2440016, by rfl⟩ : syracuseStep 3253355 = 4880033) B4880033
theorem B2168903 : Blo 2167435 2168903 := bstep (se 1 (by rfl) ⟨1626677, by rfl⟩ : syracuseStep 2168903 = 3253355) B3253355
theorem B2440021 : Blo 2167435 2440021 := bbase (se 9 (by rfl) ⟨7148, by rfl⟩ : syracuseStep 2440021 = 14297) (by norm_num)
theorem B3253361 : Blo 2167435 3253361 := bstep (se 2 (by rfl) ⟨1220010, by rfl⟩ : syracuseStep 3253361 = 2440021) B2440021
theorem B2168907 : Blo 2167435 2168907 := bstep (se 1 (by rfl) ⟨1626680, by rfl⟩ : syracuseStep 2168907 = 3253361) B3253361
theorem B2745029 : Blo 2167435 2745029 := bbase (se 4 (by rfl) ⟨257346, by rfl⟩ : syracuseStep 2745029 = 514693) (by norm_num)
theorem B7320077 : Blo 2167435 7320077 := bstep (se 3 (by rfl) ⟨1372514, by rfl⟩ : syracuseStep 7320077 = 2745029) B2745029
theorem B4880051 : Blo 2167435 4880051 := bstep (se 1 (by rfl) ⟨3660038, by rfl⟩ : syracuseStep 4880051 = 7320077) B7320077
theorem B3253367 : Blo 2167435 3253367 := bstep (se 1 (by rfl) ⟨2440025, by rfl⟩ : syracuseStep 3253367 = 4880051) B4880051
theorem B2168911 : Blo 2167435 2168911 := bstep (se 1 (by rfl) ⟨1626683, by rfl⟩ : syracuseStep 2168911 = 3253367) B3253367
theorem B3253373 : Blo 2167435 3253373 := bbase (se 3 (by rfl) ⟨610007, by rfl⟩ : syracuseStep 3253373 = 1220015) (by norm_num)
theorem B2168915 : Blo 2167435 2168915 := bstep (se 1 (by rfl) ⟨1626686, by rfl⟩ : syracuseStep 2168915 = 3253373) B3253373
theorem B4880069 : Blo 2167435 4880069 := bbase (se 4 (by rfl) ⟨457506, by rfl⟩ : syracuseStep 4880069 = 915013) (by norm_num)
theorem B3253379 : Blo 2167435 3253379 := bstep (se 1 (by rfl) ⟨2440034, by rfl⟩ : syracuseStep 3253379 = 4880069) B4880069
theorem B2168919 : Blo 2167435 2168919 := bstep (se 1 (by rfl) ⟨1626689, by rfl⟩ : syracuseStep 2168919 = 3253379) B3253379
theorem B5862709 : Blo 2167435 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B31267781 : Blo 2167435 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B20845187 : Blo 2167435 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B13896791 : Blo 2167435 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B9264527 : Blo 2167435 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B6176351 : Blo 2167435 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B4117567 : Blo 2167435 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B5490089 : Blo 2167435 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B3660059 : Blo 2167435 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2440039 : Blo 2167435 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B3253385 : Blo 2167435 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B2168923 : Blo 2167435 2168923 := bstep (se 1 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 2168923 = 3253385) B3253385
theorem B10980197 : Blo 2167435 10980197 := bbase (se 4 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 10980197 = 2058787) (by norm_num)
theorem B7320131 : Blo 2167435 7320131 := bstep (se 1 (by rfl) ⟨5490098, by rfl⟩ : syracuseStep 7320131 = 10980197) B10980197
theorem B4880087 : Blo 2167435 4880087 := bstep (se 1 (by rfl) ⟨3660065, by rfl⟩ : syracuseStep 4880087 = 7320131) B7320131
theorem B3253391 : Blo 2167435 3253391 := bstep (se 1 (by rfl) ⟨2440043, by rfl⟩ : syracuseStep 3253391 = 4880087) B4880087
theorem B2168927 : Blo 2167435 2168927 := bstep (se 1 (by rfl) ⟨1626695, by rfl⟩ : syracuseStep 2168927 = 3253391) B3253391
theorem B3253397 : Blo 2167435 3253397 := bbase (se 6 (by rfl) ⟨76251, by rfl⟩ : syracuseStep 3253397 = 152503) (by norm_num)
theorem B2168931 : Blo 2167435 2168931 := bstep (se 1 (by rfl) ⟨1626698, by rfl⟩ : syracuseStep 2168931 = 3253397) B3253397
theorem B5211325 : Blo 2167435 5211325 := bbase (se 3 (by rfl) ⟨977123, by rfl⟩ : syracuseStep 5211325 = 1954247) (by norm_num)
theorem B6948433 : Blo 2167435 6948433 := bstep (se 2 (by rfl) ⟨2605662, by rfl⟩ : syracuseStep 6948433 = 5211325) B5211325
theorem B9264577 : Blo 2167435 9264577 := bstep (se 2 (by rfl) ⟨3474216, by rfl⟩ : syracuseStep 9264577 = 6948433) B6948433
theorem B12352769 : Blo 2167435 12352769 := bstep (se 2 (by rfl) ⟨4632288, by rfl⟩ : syracuseStep 12352769 = 9264577) B9264577
theorem B8235179 : Blo 2167435 8235179 := bstep (se 1 (by rfl) ⟨6176384, by rfl⟩ : syracuseStep 8235179 = 12352769) B12352769
theorem B5490119 : Blo 2167435 5490119 := bstep (se 1 (by rfl) ⟨4117589, by rfl⟩ : syracuseStep 5490119 = 8235179) B8235179
theorem B3660079 : Blo 2167435 3660079 := bstep (se 1 (by rfl) ⟨2745059, by rfl⟩ : syracuseStep 3660079 = 5490119) B5490119
theorem B4880105 : Blo 2167435 4880105 := bstep (se 2 (by rfl) ⟨1830039, by rfl⟩ : syracuseStep 4880105 = 3660079) B3660079
theorem B3253403 : Blo 2167435 3253403 := bstep (se 1 (by rfl) ⟨2440052, by rfl⟩ : syracuseStep 3253403 = 4880105) B4880105
theorem B2168935 : Blo 2167435 2168935 := bstep (se 1 (by rfl) ⟨1626701, by rfl⟩ : syracuseStep 2168935 = 3253403) B3253403
theorem B2440057 : Blo 2167435 2440057 := bbase (se 2 (by rfl) ⟨915021, by rfl⟩ : syracuseStep 2440057 = 1830043) (by norm_num)
theorem B3253409 : Blo 2167435 3253409 := bstep (se 2 (by rfl) ⟨1220028, by rfl⟩ : syracuseStep 3253409 = 2440057) B2440057
theorem B2168939 : Blo 2167435 2168939 := bstep (se 1 (by rfl) ⟨1626704, by rfl⟩ : syracuseStep 2168939 = 3253409) B3253409
theorem B13896917 : Blo 2167435 13896917 := bbase (se 7 (by rfl) ⟨162854, by rfl⟩ : syracuseStep 13896917 = 325709) (by norm_num)
theorem B9264611 : Blo 2167435 9264611 := bstep (se 1 (by rfl) ⟨6948458, by rfl⟩ : syracuseStep 9264611 = 13896917) B13896917
theorem B6176407 : Blo 2167435 6176407 := bstep (se 1 (by rfl) ⟨4632305, by rfl⟩ : syracuseStep 6176407 = 9264611) B9264611
theorem B8235209 : Blo 2167435 8235209 := bstep (se 2 (by rfl) ⟨3088203, by rfl⟩ : syracuseStep 8235209 = 6176407) B6176407
theorem B5490139 : Blo 2167435 5490139 := bstep (se 1 (by rfl) ⟨4117604, by rfl⟩ : syracuseStep 5490139 = 8235209) B8235209
theorem B7320185 : Blo 2167435 7320185 := bstep (se 2 (by rfl) ⟨2745069, by rfl⟩ : syracuseStep 7320185 = 5490139) B5490139
theorem B4880123 : Blo 2167435 4880123 := bstep (se 1 (by rfl) ⟨3660092, by rfl⟩ : syracuseStep 4880123 = 7320185) B7320185
theorem B3253415 : Blo 2167435 3253415 := bstep (se 1 (by rfl) ⟨2440061, by rfl⟩ : syracuseStep 3253415 = 4880123) B4880123
theorem B2168943 : Blo 2167435 2168943 := bstep (se 1 (by rfl) ⟨1626707, by rfl⟩ : syracuseStep 2168943 = 3253415) B3253415
theorem B3253421 : Blo 2167435 3253421 := bbase (se 3 (by rfl) ⟨610016, by rfl⟩ : syracuseStep 3253421 = 1220033) (by norm_num)
theorem B2168947 : Blo 2167435 2168947 := bstep (se 1 (by rfl) ⟨1626710, by rfl⟩ : syracuseStep 2168947 = 3253421) B3253421
theorem B4880141 : Blo 2167435 4880141 := bbase (se 3 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 4880141 = 1830053) (by norm_num)
theorem B3253427 : Blo 2167435 3253427 := bstep (se 1 (by rfl) ⟨2440070, by rfl⟩ : syracuseStep 3253427 = 4880141) B4880141
theorem B2168951 : Blo 2167435 2168951 := bstep (se 1 (by rfl) ⟨1626713, by rfl⟩ : syracuseStep 2168951 = 3253427) B3253427
theorem B2745085 : Blo 2167435 2745085 := bbase (se 3 (by rfl) ⟨514703, by rfl⟩ : syracuseStep 2745085 = 1029407) (by norm_num)
theorem B3660113 : Blo 2167435 3660113 := bstep (se 2 (by rfl) ⟨1372542, by rfl⟩ : syracuseStep 3660113 = 2745085) B2745085
theorem B2440075 : Blo 2167435 2440075 := bstep (se 1 (by rfl) ⟨1830056, by rfl⟩ : syracuseStep 2440075 = 3660113) B3660113
theorem B3253433 : Blo 2167435 3253433 := bstep (se 2 (by rfl) ⟨1220037, by rfl⟩ : syracuseStep 3253433 = 2440075) B2440075
theorem B2168955 : Blo 2167435 2168955 := bstep (se 1 (by rfl) ⟨1626716, by rfl⟩ : syracuseStep 2168955 = 3253433) B3253433
theorem B3297829 : Blo 2167435 3297829 := bbase (se 4 (by rfl) ⟨309171, by rfl⟩ : syracuseStep 3297829 = 618343) (by norm_num)
theorem B4397105 : Blo 2167435 4397105 := bstep (se 2 (by rfl) ⟨1648914, by rfl⟩ : syracuseStep 4397105 = 3297829) B3297829
theorem B2931403 : Blo 2167435 2931403 := bstep (se 1 (by rfl) ⟨2198552, by rfl⟩ : syracuseStep 2931403 = 4397105) B4397105
theorem B3908537 : Blo 2167435 3908537 := bstep (se 2 (by rfl) ⟨1465701, by rfl⟩ : syracuseStep 3908537 = 2931403) B2931403
theorem B2605691 : Blo 2167435 2605691 := bstep (se 1 (by rfl) ⟨1954268, by rfl⟩ : syracuseStep 2605691 = 3908537) B3908537
theorem B6948509 : Blo 2167435 6948509 := bstep (se 3 (by rfl) ⟨1302845, by rfl⟩ : syracuseStep 6948509 = 2605691) B2605691
theorem B18529357 : Blo 2167435 18529357 := bstep (se 3 (by rfl) ⟨3474254, by rfl⟩ : syracuseStep 18529357 = 6948509) B6948509
theorem B24705809 : Blo 2167435 24705809 := bstep (se 2 (by rfl) ⟨9264678, by rfl⟩ : syracuseStep 24705809 = 18529357) B18529357
theorem B16470539 : Blo 2167435 16470539 := bstep (se 1 (by rfl) ⟨12352904, by rfl⟩ : syracuseStep 16470539 = 24705809) B24705809
theorem B10980359 : Blo 2167435 10980359 := bstep (se 1 (by rfl) ⟨8235269, by rfl⟩ : syracuseStep 10980359 = 16470539) B16470539
theorem B7320239 : Blo 2167435 7320239 := bstep (se 1 (by rfl) ⟨5490179, by rfl⟩ : syracuseStep 7320239 = 10980359) B10980359
theorem B4880159 : Blo 2167435 4880159 := bstep (se 1 (by rfl) ⟨3660119, by rfl⟩ : syracuseStep 4880159 = 7320239) B7320239
theorem B3253439 : Blo 2167435 3253439 := bstep (se 1 (by rfl) ⟨2440079, by rfl⟩ : syracuseStep 3253439 = 4880159) B4880159
theorem B2168959 : Blo 2167435 2168959 := bstep (se 1 (by rfl) ⟨1626719, by rfl⟩ : syracuseStep 2168959 = 3253439) B3253439
theorem B3253445 : Blo 2167435 3253445 := bbase (se 4 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 3253445 = 610021) (by norm_num)
theorem B2168963 : Blo 2167435 2168963 := bstep (se 1 (by rfl) ⟨1626722, by rfl⟩ : syracuseStep 2168963 = 3253445) B3253445
theorem B3660133 : Blo 2167435 3660133 := bbase (se 4 (by rfl) ⟨343137, by rfl⟩ : syracuseStep 3660133 = 686275) (by norm_num)
theorem B4880177 : Blo 2167435 4880177 := bstep (se 2 (by rfl) ⟨1830066, by rfl⟩ : syracuseStep 4880177 = 3660133) B3660133
theorem B3253451 : Blo 2167435 3253451 := bstep (se 1 (by rfl) ⟨2440088, by rfl⟩ : syracuseStep 3253451 = 4880177) B4880177
theorem B2168967 : Blo 2167435 2168967 := bstep (se 1 (by rfl) ⟨1626725, by rfl⟩ : syracuseStep 2168967 = 3253451) B3253451
theorem B2440093 : Blo 2167435 2440093 := bbase (se 3 (by rfl) ⟨457517, by rfl⟩ : syracuseStep 2440093 = 915035) (by norm_num)
theorem B3253457 : Blo 2167435 3253457 := bstep (se 2 (by rfl) ⟨1220046, by rfl⟩ : syracuseStep 3253457 = 2440093) B2440093
theorem B2168971 : Blo 2167435 2168971 := bstep (se 1 (by rfl) ⟨1626728, by rfl⟩ : syracuseStep 2168971 = 3253457) B3253457
theorem B7320293 : Blo 2167435 7320293 := bbase (se 4 (by rfl) ⟨686277, by rfl⟩ : syracuseStep 7320293 = 1372555) (by norm_num)
theorem B4880195 : Blo 2167435 4880195 := bstep (se 1 (by rfl) ⟨3660146, by rfl⟩ : syracuseStep 4880195 = 7320293) B7320293
theorem B3253463 : Blo 2167435 3253463 := bstep (se 1 (by rfl) ⟨2440097, by rfl⟩ : syracuseStep 3253463 = 4880195) B4880195
theorem B2168975 : Blo 2167435 2168975 := bstep (se 1 (by rfl) ⟨1626731, by rfl⟩ : syracuseStep 2168975 = 3253463) B3253463
theorem B3253469 : Blo 2167435 3253469 := bbase (se 3 (by rfl) ⟨610025, by rfl⟩ : syracuseStep 3253469 = 1220051) (by norm_num)
theorem B2168979 : Blo 2167435 2168979 := bstep (se 1 (by rfl) ⟨1626734, by rfl⟩ : syracuseStep 2168979 = 3253469) B3253469
theorem B4880213 : Blo 2167435 4880213 := bbase (se 9 (by rfl) ⟨14297, by rfl⟩ : syracuseStep 4880213 = 28595) (by norm_num)
theorem B3253475 : Blo 2167435 3253475 := bstep (se 1 (by rfl) ⟨2440106, by rfl⟩ : syracuseStep 3253475 = 4880213) B4880213
theorem B2168983 : Blo 2167435 2168983 := bstep (se 1 (by rfl) ⟨1626737, by rfl⟩ : syracuseStep 2168983 = 3253475) B3253475
theorem B6176533 : Blo 2167435 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B8235377 : Blo 2167435 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B5490251 : Blo 2167435 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B3660167 : Blo 2167435 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B2440111 : Blo 2167435 2440111 := bstep (se 1 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 2440111 = 3660167) B3660167
theorem B3253481 : Blo 2167435 3253481 := bstep (se 2 (by rfl) ⟨1220055, by rfl⟩ : syracuseStep 3253481 = 2440111) B2440111
theorem B2168987 : Blo 2167435 2168987 := bstep (se 1 (by rfl) ⟨1626740, by rfl⟩ : syracuseStep 2168987 = 3253481) B3253481
theorem B7521461 : Blo 2167435 7521461 := bbase (se 5 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 7521461 = 705137) (by norm_num)
theorem B5014307 : Blo 2167435 5014307 := bstep (se 1 (by rfl) ⟨3760730, by rfl⟩ : syracuseStep 5014307 = 7521461) B7521461
theorem B13371485 : Blo 2167435 13371485 := bstep (se 3 (by rfl) ⟨2507153, by rfl⟩ : syracuseStep 13371485 = 5014307) B5014307
theorem B35657293 : Blo 2167435 35657293 := bstep (se 3 (by rfl) ⟨6685742, by rfl⟩ : syracuseStep 35657293 = 13371485) B13371485
theorem B47543057 : Blo 2167435 47543057 := bstep (se 2 (by rfl) ⟨17828646, by rfl⟩ : syracuseStep 47543057 = 35657293) B35657293
theorem B31695371 : Blo 2167435 31695371 := bstep (se 1 (by rfl) ⟨23771528, by rfl⟩ : syracuseStep 31695371 = 47543057) B47543057
theorem B21130247 : Blo 2167435 21130247 := bstep (se 1 (by rfl) ⟨15847685, by rfl⟩ : syracuseStep 21130247 = 31695371) B31695371
theorem B56347325 : Blo 2167435 56347325 := bstep (se 3 (by rfl) ⟨10565123, by rfl⟩ : syracuseStep 56347325 = 21130247) B21130247
theorem B37564883 : Blo 2167435 37564883 := bstep (se 1 (by rfl) ⟨28173662, by rfl⟩ : syracuseStep 37564883 = 56347325) B56347325
theorem B25043255 : Blo 2167435 25043255 := bstep (se 1 (by rfl) ⟨18782441, by rfl⟩ : syracuseStep 25043255 = 37564883) B37564883
theorem B16695503 : Blo 2167435 16695503 := bstep (se 1 (by rfl) ⟨12521627, by rfl⟩ : syracuseStep 16695503 = 25043255) B25043255
theorem B11130335 : Blo 2167435 11130335 := bstep (se 1 (by rfl) ⟨8347751, by rfl⟩ : syracuseStep 11130335 = 16695503) B16695503
theorem B7420223 : Blo 2167435 7420223 := bstep (se 1 (by rfl) ⟨5565167, by rfl⟩ : syracuseStep 7420223 = 11130335) B11130335
theorem B4946815 : Blo 2167435 4946815 := bstep (se 1 (by rfl) ⟨3710111, by rfl⟩ : syracuseStep 4946815 = 7420223) B7420223
theorem B6595753 : Blo 2167435 6595753 := bstep (se 2 (by rfl) ⟨2473407, by rfl⟩ : syracuseStep 6595753 = 4946815) B4946815
theorem B8794337 : Blo 2167435 8794337 := bstep (se 2 (by rfl) ⟨3297876, by rfl⟩ : syracuseStep 8794337 = 6595753) B6595753
theorem B93806261 : Blo 2167435 93806261 := bstep (se 5 (by rfl) ⟨4397168, by rfl⟩ : syracuseStep 93806261 = 8794337) B8794337
theorem B62537507 : Blo 2167435 62537507 := bstep (se 1 (by rfl) ⟨46903130, by rfl⟩ : syracuseStep 62537507 = 93806261) B93806261
theorem B41691671 : Blo 2167435 41691671 := bstep (se 1 (by rfl) ⟨31268753, by rfl⟩ : syracuseStep 41691671 = 62537507) B62537507
theorem B27794447 : Blo 2167435 27794447 := bstep (se 1 (by rfl) ⟨20845835, by rfl⟩ : syracuseStep 27794447 = 41691671) B41691671
theorem B18529631 : Blo 2167435 18529631 := bstep (se 1 (by rfl) ⟨13897223, by rfl⟩ : syracuseStep 18529631 = 27794447) B27794447
theorem B12353087 : Blo 2167435 12353087 := bstep (se 1 (by rfl) ⟨9264815, by rfl⟩ : syracuseStep 12353087 = 18529631) B18529631
theorem B8235391 : Blo 2167435 8235391 := bstep (se 1 (by rfl) ⟨6176543, by rfl⟩ : syracuseStep 8235391 = 12353087) B12353087
theorem B10980521 : Blo 2167435 10980521 := bstep (se 2 (by rfl) ⟨4117695, by rfl⟩ : syracuseStep 10980521 = 8235391) B8235391
theorem B7320347 : Blo 2167435 7320347 := bstep (se 1 (by rfl) ⟨5490260, by rfl⟩ : syracuseStep 7320347 = 10980521) B10980521
theorem B4880231 : Blo 2167435 4880231 := bstep (se 1 (by rfl) ⟨3660173, by rfl⟩ : syracuseStep 4880231 = 7320347) B7320347
theorem B3253487 : Blo 2167435 3253487 := bstep (se 1 (by rfl) ⟨2440115, by rfl⟩ : syracuseStep 3253487 = 4880231) B4880231
theorem B2168991 : Blo 2167435 2168991 := bstep (se 1 (by rfl) ⟨1626743, by rfl⟩ : syracuseStep 2168991 = 3253487) B3253487
theorem B3253493 : Blo 2167435 3253493 := bbase (se 5 (by rfl) ⟨152507, by rfl⟩ : syracuseStep 3253493 = 305015) (by norm_num)
theorem B2168995 : Blo 2167435 2168995 := bstep (se 1 (by rfl) ⟨1626746, by rfl⟩ : syracuseStep 2168995 = 3253493) B3253493
theorem B2198593 : Blo 2167435 2198593 := bbase (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) (by norm_num)
theorem B11725829 : Blo 2167435 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B7817219 : Blo 2167435 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B5211479 : Blo 2167435 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B13897277 : Blo 2167435 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B9264851 : Blo 2167435 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B6176567 : Blo 2167435 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B4117711 : Blo 2167435 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B5490281 : Blo 2167435 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B3660187 : Blo 2167435 3660187 := bstep (se 1 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 3660187 = 5490281) B5490281
theorem B4880249 : Blo 2167435 4880249 := bstep (se 2 (by rfl) ⟨1830093, by rfl⟩ : syracuseStep 4880249 = 3660187) B3660187
theorem B3253499 : Blo 2167435 3253499 := bstep (se 1 (by rfl) ⟨2440124, by rfl⟩ : syracuseStep 3253499 = 4880249) B4880249
theorem B2168999 : Blo 2167435 2168999 := bstep (se 1 (by rfl) ⟨1626749, by rfl⟩ : syracuseStep 2168999 = 3253499) B3253499
theorem B2440129 : Blo 2167435 2440129 := bbase (se 2 (by rfl) ⟨915048, by rfl⟩ : syracuseStep 2440129 = 1830097) (by norm_num)
theorem B3253505 : Blo 2167435 3253505 := bstep (se 2 (by rfl) ⟨1220064, by rfl⟩ : syracuseStep 3253505 = 2440129) B2440129
theorem B2169003 : Blo 2167435 2169003 := bstep (se 1 (by rfl) ⟨1626752, by rfl⟩ : syracuseStep 2169003 = 3253505) B3253505
theorem B5490301 : Blo 2167435 5490301 := bbase (se 3 (by rfl) ⟨1029431, by rfl⟩ : syracuseStep 5490301 = 2058863) (by norm_num)
theorem B7320401 : Blo 2167435 7320401 := bstep (se 2 (by rfl) ⟨2745150, by rfl⟩ : syracuseStep 7320401 = 5490301) B5490301
theorem B4880267 : Blo 2167435 4880267 := bstep (se 1 (by rfl) ⟨3660200, by rfl⟩ : syracuseStep 4880267 = 7320401) B7320401
theorem B3253511 : Blo 2167435 3253511 := bstep (se 1 (by rfl) ⟨2440133, by rfl⟩ : syracuseStep 3253511 = 4880267) B4880267
theorem B2169007 : Blo 2167435 2169007 := bstep (se 1 (by rfl) ⟨1626755, by rfl⟩ : syracuseStep 2169007 = 3253511) B3253511
theorem B3253517 : Blo 2167435 3253517 := bbase (se 3 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 3253517 = 1220069) (by norm_num)
theorem B2169011 : Blo 2167435 2169011 := bstep (se 1 (by rfl) ⟨1626758, by rfl⟩ : syracuseStep 2169011 = 3253517) B3253517
theorem B4880285 : Blo 2167435 4880285 := bbase (se 3 (by rfl) ⟨915053, by rfl⟩ : syracuseStep 4880285 = 1830107) (by norm_num)
theorem B3253523 : Blo 2167435 3253523 := bstep (se 1 (by rfl) ⟨2440142, by rfl⟩ : syracuseStep 3253523 = 4880285) B4880285
theorem B2169015 : Blo 2167435 2169015 := bstep (se 1 (by rfl) ⟨1626761, by rfl⟩ : syracuseStep 2169015 = 3253523) B3253523
theorem B3660221 : Blo 2167435 3660221 := bbase (se 3 (by rfl) ⟨686291, by rfl⟩ : syracuseStep 3660221 = 1372583) (by norm_num)
theorem B2440147 : Blo 2167435 2440147 := bstep (se 1 (by rfl) ⟨1830110, by rfl⟩ : syracuseStep 2440147 = 3660221) B3660221
theorem B3253529 : Blo 2167435 3253529 := bstep (se 2 (by rfl) ⟨1220073, by rfl⟩ : syracuseStep 3253529 = 2440147) B2440147
theorem B2169019 : Blo 2167435 2169019 := bstep (se 1 (by rfl) ⟨1626764, by rfl⟩ : syracuseStep 2169019 = 3253529) B3253529
theorem B12353269 : Blo 2167435 12353269 := bbase (se 5 (by rfl) ⟨579059, by rfl⟩ : syracuseStep 12353269 = 1158119) (by norm_num)
theorem B16471025 : Blo 2167435 16471025 := bstep (se 2 (by rfl) ⟨6176634, by rfl⟩ : syracuseStep 16471025 = 12353269) B12353269
theorem B10980683 : Blo 2167435 10980683 := bstep (se 1 (by rfl) ⟨8235512, by rfl⟩ : syracuseStep 10980683 = 16471025) B16471025
theorem B7320455 : Blo 2167435 7320455 := bstep (se 1 (by rfl) ⟨5490341, by rfl⟩ : syracuseStep 7320455 = 10980683) B10980683
theorem B4880303 : Blo 2167435 4880303 := bstep (se 1 (by rfl) ⟨3660227, by rfl⟩ : syracuseStep 4880303 = 7320455) B7320455
theorem B3253535 : Blo 2167435 3253535 := bstep (se 1 (by rfl) ⟨2440151, by rfl⟩ : syracuseStep 3253535 = 4880303) B4880303
theorem B2169023 : Blo 2167435 2169023 := bstep (se 1 (by rfl) ⟨1626767, by rfl⟩ : syracuseStep 2169023 = 3253535) B3253535
theorem B3253541 : Blo 2167435 3253541 := bbase (se 4 (by rfl) ⟨305019, by rfl⟩ : syracuseStep 3253541 = 610039) (by norm_num)
theorem B2169027 : Blo 2167435 2169027 := bstep (se 1 (by rfl) ⟨1626770, by rfl⟩ : syracuseStep 2169027 = 3253541) B3253541
theorem B2745181 : Blo 2167435 2745181 := bbase (se 3 (by rfl) ⟨514721, by rfl⟩ : syracuseStep 2745181 = 1029443) (by norm_num)
theorem B3660241 : Blo 2167435 3660241 := bstep (se 2 (by rfl) ⟨1372590, by rfl⟩ : syracuseStep 3660241 = 2745181) B2745181
theorem B4880321 : Blo 2167435 4880321 := bstep (se 2 (by rfl) ⟨1830120, by rfl⟩ : syracuseStep 4880321 = 3660241) B3660241
theorem B3253547 : Blo 2167435 3253547 := bstep (se 1 (by rfl) ⟨2440160, by rfl⟩ : syracuseStep 3253547 = 4880321) B4880321
theorem B2169031 : Blo 2167435 2169031 := bstep (se 1 (by rfl) ⟨1626773, by rfl⟩ : syracuseStep 2169031 = 3253547) B3253547
theorem B2440165 : Blo 2167435 2440165 := bbase (se 4 (by rfl) ⟨228765, by rfl⟩ : syracuseStep 2440165 = 457531) (by norm_num)
theorem B3253553 : Blo 2167435 3253553 := bstep (se 2 (by rfl) ⟨1220082, by rfl⟩ : syracuseStep 3253553 = 2440165) B2440165
theorem B2169035 : Blo 2167435 2169035 := bstep (se 1 (by rfl) ⟨1626776, by rfl⟩ : syracuseStep 2169035 = 3253553) B3253553
theorem B7043573 : Blo 2167435 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B4695715 : Blo 2167435 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B25043813 : Blo 2167435 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B16695875 : Blo 2167435 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B11130583 : Blo 2167435 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B14840777 : Blo 2167435 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B39575405 : Blo 2167435 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B26383603 : Blo 2167435 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B35178137 : Blo 2167435 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B23452091 : Blo 2167435 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B15634727 : Blo 2167435 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B10423151 : Blo 2167435 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B6948767 : Blo 2167435 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B4632511 : Blo 2167435 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B6176681 : Blo 2167435 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B4117787 : Blo 2167435 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B2745191 : Blo 2167435 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B7320509 : Blo 2167435 7320509 := bstep (se 3 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 7320509 = 2745191) B2745191
theorem B4880339 : Blo 2167435 4880339 := bstep (se 1 (by rfl) ⟨3660254, by rfl⟩ : syracuseStep 4880339 = 7320509) B7320509
theorem B3253559 : Blo 2167435 3253559 := bstep (se 1 (by rfl) ⟨2440169, by rfl⟩ : syracuseStep 3253559 = 4880339) B4880339
theorem B2169039 : Blo 2167435 2169039 := bstep (se 1 (by rfl) ⟨1626779, by rfl⟩ : syracuseStep 2169039 = 3253559) B3253559
theorem B3253565 : Blo 2167435 3253565 := bbase (se 3 (by rfl) ⟨610043, by rfl⟩ : syracuseStep 3253565 = 1220087) (by norm_num)
theorem B2169043 : Blo 2167435 2169043 := bstep (se 1 (by rfl) ⟨1626782, by rfl⟩ : syracuseStep 2169043 = 3253565) B3253565
theorem B4880357 : Blo 2167435 4880357 := bbase (se 4 (by rfl) ⟨457533, by rfl⟩ : syracuseStep 4880357 = 915067) (by norm_num)
theorem B3253571 : Blo 2167435 3253571 := bstep (se 1 (by rfl) ⟨2440178, by rfl⟩ : syracuseStep 3253571 = 4880357) B4880357
theorem B2169047 : Blo 2167435 2169047 := bstep (se 1 (by rfl) ⟨1626785, by rfl⟩ : syracuseStep 2169047 = 3253571) B3253571
theorem B5490413 : Blo 2167435 5490413 := bbase (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) (by norm_num)
theorem B3660275 : Blo 2167435 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B2440183 : Blo 2167435 2440183 := bstep (se 1 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 2440183 = 3660275) B3660275
theorem B3253577 : Blo 2167435 3253577 := bstep (se 2 (by rfl) ⟨1220091, by rfl⟩ : syracuseStep 3253577 = 2440183) B2440183
theorem B2169051 : Blo 2167435 2169051 := bstep (se 1 (by rfl) ⟨1626788, by rfl⟩ : syracuseStep 2169051 = 3253577) B3253577
theorem B5943061 : Blo 2167435 5943061 := bbase (se 6 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 5943061 = 278581) (by norm_num)
theorem B7924081 : Blo 2167435 7924081 := bstep (se 2 (by rfl) ⟨2971530, by rfl⟩ : syracuseStep 7924081 = 5943061) B5943061
theorem B10565441 : Blo 2167435 10565441 := bstep (se 2 (by rfl) ⟨3962040, by rfl⟩ : syracuseStep 10565441 = 7924081) B7924081
theorem B7043627 : Blo 2167435 7043627 := bstep (se 1 (by rfl) ⟨5282720, by rfl⟩ : syracuseStep 7043627 = 10565441) B10565441
theorem B4695751 : Blo 2167435 4695751 := bstep (se 1 (by rfl) ⟨3521813, by rfl⟩ : syracuseStep 4695751 = 7043627) B7043627
theorem B25044005 : Blo 2167435 25044005 := bstep (se 4 (by rfl) ⟨2347875, by rfl⟩ : syracuseStep 25044005 = 4695751) B4695751
theorem B16696003 : Blo 2167435 16696003 := bstep (se 1 (by rfl) ⟨12522002, by rfl⟩ : syracuseStep 16696003 = 25044005) B25044005
theorem B22261337 : Blo 2167435 22261337 := bstep (se 2 (by rfl) ⟨8348001, by rfl⟩ : syracuseStep 22261337 = 16696003) B16696003
theorem B14840891 : Blo 2167435 14840891 := bstep (se 1 (by rfl) ⟨11130668, by rfl⟩ : syracuseStep 14840891 = 22261337) B22261337
theorem B9893927 : Blo 2167435 9893927 := bstep (se 1 (by rfl) ⟨7420445, by rfl⟩ : syracuseStep 9893927 = 14840891) B14840891
theorem B6595951 : Blo 2167435 6595951 := bstep (se 1 (by rfl) ⟨4946963, by rfl⟩ : syracuseStep 6595951 = 9893927) B9893927
theorem B8794601 : Blo 2167435 8794601 := bstep (se 2 (by rfl) ⟨3297975, by rfl⟩ : syracuseStep 8794601 = 6595951) B6595951
theorem B5863067 : Blo 2167435 5863067 := bstep (se 1 (by rfl) ⟨4397300, by rfl⟩ : syracuseStep 5863067 = 8794601) B8794601
theorem B3908711 : Blo 2167435 3908711 := bstep (se 1 (by rfl) ⟨2931533, by rfl⟩ : syracuseStep 3908711 = 5863067) B5863067
theorem B2605807 : Blo 2167435 2605807 := bstep (se 1 (by rfl) ⟨1954355, by rfl⟩ : syracuseStep 2605807 = 3908711) B3908711
theorem B3474409 : Blo 2167435 3474409 := bstep (se 2 (by rfl) ⟨1302903, by rfl⟩ : syracuseStep 3474409 = 2605807) B2605807
theorem B4632545 : Blo 2167435 4632545 := bstep (se 2 (by rfl) ⟨1737204, by rfl⟩ : syracuseStep 4632545 = 3474409) B3474409
theorem B3088363 : Blo 2167435 3088363 := bstep (se 1 (by rfl) ⟨2316272, by rfl⟩ : syracuseStep 3088363 = 4632545) B4632545
theorem B4117817 : Blo 2167435 4117817 := bstep (se 2 (by rfl) ⟨1544181, by rfl⟩ : syracuseStep 4117817 = 3088363) B3088363
theorem B10980845 : Blo 2167435 10980845 := bstep (se 3 (by rfl) ⟨2058908, by rfl⟩ : syracuseStep 10980845 = 4117817) B4117817
theorem B7320563 : Blo 2167435 7320563 := bstep (se 1 (by rfl) ⟨5490422, by rfl⟩ : syracuseStep 7320563 = 10980845) B10980845
theorem B4880375 : Blo 2167435 4880375 := bstep (se 1 (by rfl) ⟨3660281, by rfl⟩ : syracuseStep 4880375 = 7320563) B7320563
theorem B3253583 : Blo 2167435 3253583 := bstep (se 1 (by rfl) ⟨2440187, by rfl⟩ : syracuseStep 3253583 = 4880375) B4880375
theorem B2169055 : Blo 2167435 2169055 := bstep (se 1 (by rfl) ⟨1626791, by rfl⟩ : syracuseStep 2169055 = 3253583) B3253583
theorem B3253589 : Blo 2167435 3253589 := bbase (se 12 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 3253589 = 2383) (by norm_num)
theorem B2169059 : Blo 2167435 2169059 := bstep (se 1 (by rfl) ⟨1626794, by rfl⟩ : syracuseStep 2169059 = 3253589) B3253589
theorem B2316281 : Blo 2167435 2316281 := bbase (se 2 (by rfl) ⟨868605, by rfl⟩ : syracuseStep 2316281 = 1737211) (by norm_num)
theorem B6176749 : Blo 2167435 6176749 := bstep (se 3 (by rfl) ⟨1158140, by rfl⟩ : syracuseStep 6176749 = 2316281) B2316281
theorem B8235665 : Blo 2167435 8235665 := bstep (se 2 (by rfl) ⟨3088374, by rfl⟩ : syracuseStep 8235665 = 6176749) B6176749
theorem B5490443 : Blo 2167435 5490443 := bstep (se 1 (by rfl) ⟨4117832, by rfl⟩ : syracuseStep 5490443 = 8235665) B8235665
theorem B3660295 : Blo 2167435 3660295 := bstep (se 1 (by rfl) ⟨2745221, by rfl⟩ : syracuseStep 3660295 = 5490443) B5490443
theorem B4880393 : Blo 2167435 4880393 := bstep (se 2 (by rfl) ⟨1830147, by rfl⟩ : syracuseStep 4880393 = 3660295) B3660295
theorem B3253595 : Blo 2167435 3253595 := bstep (se 1 (by rfl) ⟨2440196, by rfl⟩ : syracuseStep 3253595 = 4880393) B4880393
theorem B2169063 : Blo 2167435 2169063 := bstep (se 1 (by rfl) ⟨1626797, by rfl⟩ : syracuseStep 2169063 = 3253595) B3253595
theorem B2440201 : Blo 2167435 2440201 := bbase (se 2 (by rfl) ⟨915075, by rfl⟩ : syracuseStep 2440201 = 1830151) (by norm_num)
theorem B3253601 : Blo 2167435 3253601 := bstep (se 2 (by rfl) ⟨1220100, by rfl⟩ : syracuseStep 3253601 = 2440201) B2440201
theorem B2169067 : Blo 2167435 2169067 := bstep (se 1 (by rfl) ⟨1626800, by rfl⟩ : syracuseStep 2169067 = 3253601) B3253601
theorem B7817477 : Blo 2167435 7817477 := bbase (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) (by norm_num)
theorem B20846605 : Blo 2167435 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B27795473 : Blo 2167435 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B18530315 : Blo 2167435 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B12353543 : Blo 2167435 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B8235695 : Blo 2167435 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B5490463 : Blo 2167435 5490463 := bstep (se 1 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 5490463 = 8235695) B8235695
theorem B7320617 : Blo 2167435 7320617 := bstep (se 2 (by rfl) ⟨2745231, by rfl⟩ : syracuseStep 7320617 = 5490463) B5490463
theorem B4880411 : Blo 2167435 4880411 := bstep (se 1 (by rfl) ⟨3660308, by rfl⟩ : syracuseStep 4880411 = 7320617) B7320617
theorem B3253607 : Blo 2167435 3253607 := bstep (se 1 (by rfl) ⟨2440205, by rfl⟩ : syracuseStep 3253607 = 4880411) B4880411
theorem B2169071 : Blo 2167435 2169071 := bstep (se 1 (by rfl) ⟨1626803, by rfl⟩ : syracuseStep 2169071 = 3253607) B3253607
theorem B3253613 : Blo 2167435 3253613 := bbase (se 3 (by rfl) ⟨610052, by rfl⟩ : syracuseStep 3253613 = 1220105) (by norm_num)
theorem B2169075 : Blo 2167435 2169075 := bstep (se 1 (by rfl) ⟨1626806, by rfl⟩ : syracuseStep 2169075 = 3253613) B3253613
theorem B4880429 : Blo 2167435 4880429 := bbase (se 3 (by rfl) ⟨915080, by rfl⟩ : syracuseStep 4880429 = 1830161) (by norm_num)
theorem B3253619 : Blo 2167435 3253619 := bstep (se 1 (by rfl) ⟨2440214, by rfl⟩ : syracuseStep 3253619 = 4880429) B4880429
theorem B2169079 : Blo 2167435 2169079 := bstep (se 1 (by rfl) ⟨1626809, by rfl⟩ : syracuseStep 2169079 = 3253619) B3253619
theorem B4397357 : Blo 2167435 4397357 := bbase (se 3 (by rfl) ⟨824504, by rfl⟩ : syracuseStep 4397357 = 1649009) (by norm_num)
theorem B2931571 : Blo 2167435 2931571 := bstep (se 1 (by rfl) ⟨2198678, by rfl⟩ : syracuseStep 2931571 = 4397357) B4397357
theorem B15635045 : Blo 2167435 15635045 := bstep (se 4 (by rfl) ⟨1465785, by rfl⟩ : syracuseStep 15635045 = 2931571) B2931571
theorem B10423363 : Blo 2167435 10423363 := bstep (se 1 (by rfl) ⟨7817522, by rfl⟩ : syracuseStep 10423363 = 15635045) B15635045
theorem B13897817 : Blo 2167435 13897817 := bstep (se 2 (by rfl) ⟨5211681, by rfl⟩ : syracuseStep 13897817 = 10423363) B10423363
theorem B9265211 : Blo 2167435 9265211 := bstep (se 1 (by rfl) ⟨6948908, by rfl⟩ : syracuseStep 9265211 = 13897817) B13897817
theorem B6176807 : Blo 2167435 6176807 := bstep (se 1 (by rfl) ⟨4632605, by rfl⟩ : syracuseStep 6176807 = 9265211) B9265211
theorem B4117871 : Blo 2167435 4117871 := bstep (se 1 (by rfl) ⟨3088403, by rfl⟩ : syracuseStep 4117871 = 6176807) B6176807
theorem B2745247 : Blo 2167435 2745247 := bstep (se 1 (by rfl) ⟨2058935, by rfl⟩ : syracuseStep 2745247 = 4117871) B4117871
theorem B3660329 : Blo 2167435 3660329 := bstep (se 2 (by rfl) ⟨1372623, by rfl⟩ : syracuseStep 3660329 = 2745247) B2745247
theorem B2440219 : Blo 2167435 2440219 := bstep (se 1 (by rfl) ⟨1830164, by rfl⟩ : syracuseStep 2440219 = 3660329) B3660329
theorem B3253625 : Blo 2167435 3253625 := bstep (se 2 (by rfl) ⟨1220109, by rfl⟩ : syracuseStep 3253625 = 2440219) B2440219
theorem B2169083 : Blo 2167435 2169083 := bstep (se 1 (by rfl) ⟨1626812, by rfl⟩ : syracuseStep 2169083 = 3253625) B3253625
theorem B2347909 : Blo 2167435 2347909 := bbase (se 4 (by rfl) ⟨220116, by rfl⟩ : syracuseStep 2347909 = 440233) (by norm_num)
theorem B50088725 : Blo 2167435 50088725 := bstep (se 6 (by rfl) ⟨1173954, by rfl⟩ : syracuseStep 50088725 = 2347909) B2347909
theorem B33392483 : Blo 2167435 33392483 := bstep (se 1 (by rfl) ⟨25044362, by rfl⟩ : syracuseStep 33392483 = 50088725) B50088725
theorem B22261655 : Blo 2167435 22261655 := bstep (se 1 (by rfl) ⟨16696241, by rfl⟩ : syracuseStep 22261655 = 33392483) B33392483
theorem B14841103 : Blo 2167435 14841103 := bstep (se 1 (by rfl) ⟨11130827, by rfl⟩ : syracuseStep 14841103 = 22261655) B22261655
theorem B19788137 : Blo 2167435 19788137 := bstep (se 2 (by rfl) ⟨7420551, by rfl⟩ : syracuseStep 19788137 = 14841103) B14841103
theorem B13192091 : Blo 2167435 13192091 := bstep (se 1 (by rfl) ⟨9894068, by rfl⟩ : syracuseStep 13192091 = 19788137) B19788137
theorem B8794727 : Blo 2167435 8794727 := bstep (se 1 (by rfl) ⟨6596045, by rfl⟩ : syracuseStep 8794727 = 13192091) B13192091
theorem B5863151 : Blo 2167435 5863151 := bstep (se 1 (by rfl) ⟨4397363, by rfl⟩ : syracuseStep 5863151 = 8794727) B8794727
theorem B15635069 : Blo 2167435 15635069 := bstep (se 3 (by rfl) ⟨2931575, by rfl⟩ : syracuseStep 15635069 = 5863151) B5863151
theorem B10423379 : Blo 2167435 10423379 := bstep (se 1 (by rfl) ⟨7817534, by rfl⟩ : syracuseStep 10423379 = 15635069) B15635069
theorem B6948919 : Blo 2167435 6948919 := bstep (se 1 (by rfl) ⟨5211689, by rfl⟩ : syracuseStep 6948919 = 10423379) B10423379
theorem B37060901 : Blo 2167435 37060901 := bstep (se 4 (by rfl) ⟨3474459, by rfl⟩ : syracuseStep 37060901 = 6948919) B6948919
theorem B24707267 : Blo 2167435 24707267 := bstep (se 1 (by rfl) ⟨18530450, by rfl⟩ : syracuseStep 24707267 = 37060901) B37060901
theorem B16471511 : Blo 2167435 16471511 := bstep (se 1 (by rfl) ⟨12353633, by rfl⟩ : syracuseStep 16471511 = 24707267) B24707267
theorem B10981007 : Blo 2167435 10981007 := bstep (se 1 (by rfl) ⟨8235755, by rfl⟩ : syracuseStep 10981007 = 16471511) B16471511
theorem B7320671 : Blo 2167435 7320671 := bstep (se 1 (by rfl) ⟨5490503, by rfl⟩ : syracuseStep 7320671 = 10981007) B10981007
theorem B4880447 : Blo 2167435 4880447 := bstep (se 1 (by rfl) ⟨3660335, by rfl⟩ : syracuseStep 4880447 = 7320671) B7320671
theorem B3253631 : Blo 2167435 3253631 := bstep (se 1 (by rfl) ⟨2440223, by rfl⟩ : syracuseStep 3253631 = 4880447) B4880447
theorem B2169087 : Blo 2167435 2169087 := bstep (se 1 (by rfl) ⟨1626815, by rfl⟩ : syracuseStep 2169087 = 3253631) B3253631
theorem B3253637 : Blo 2167435 3253637 := bbase (se 4 (by rfl) ⟨305028, by rfl⟩ : syracuseStep 3253637 = 610057) (by norm_num)
theorem B2169091 : Blo 2167435 2169091 := bstep (se 1 (by rfl) ⟨1626818, by rfl⟩ : syracuseStep 2169091 = 3253637) B3253637
theorem B3660349 : Blo 2167435 3660349 := bbase (se 3 (by rfl) ⟨686315, by rfl⟩ : syracuseStep 3660349 = 1372631) (by norm_num)
theorem B4880465 : Blo 2167435 4880465 := bstep (se 2 (by rfl) ⟨1830174, by rfl⟩ : syracuseStep 4880465 = 3660349) B3660349
theorem B3253643 : Blo 2167435 3253643 := bstep (se 1 (by rfl) ⟨2440232, by rfl⟩ : syracuseStep 3253643 = 4880465) B4880465
theorem B2169095 : Blo 2167435 2169095 := bstep (se 1 (by rfl) ⟨1626821, by rfl⟩ : syracuseStep 2169095 = 3253643) B3253643
theorem B2440237 : Blo 2167435 2440237 := bbase (se 3 (by rfl) ⟨457544, by rfl⟩ : syracuseStep 2440237 = 915089) (by norm_num)
theorem B3253649 : Blo 2167435 3253649 := bstep (se 2 (by rfl) ⟨1220118, by rfl⟩ : syracuseStep 3253649 = 2440237) B2440237
theorem B2169099 : Blo 2167435 2169099 := bstep (se 1 (by rfl) ⟨1626824, by rfl⟩ : syracuseStep 2169099 = 3253649) B3253649
theorem B7320725 : Blo 2167435 7320725 := bbase (se 6 (by rfl) ⟨171579, by rfl⟩ : syracuseStep 7320725 = 343159) (by norm_num)
theorem B4880483 : Blo 2167435 4880483 := bstep (se 1 (by rfl) ⟨3660362, by rfl⟩ : syracuseStep 4880483 = 7320725) B7320725
theorem B3253655 : Blo 2167435 3253655 := bstep (se 1 (by rfl) ⟨2440241, by rfl⟩ : syracuseStep 3253655 = 4880483) B4880483
theorem B2169103 : Blo 2167435 2169103 := bstep (se 1 (by rfl) ⟨1626827, by rfl⟩ : syracuseStep 2169103 = 3253655) B3253655
theorem B3253661 : Blo 2167435 3253661 := bbase (se 3 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 3253661 = 1220123) (by norm_num)
theorem B2169107 : Blo 2167435 2169107 := bstep (se 1 (by rfl) ⟨1626830, by rfl⟩ : syracuseStep 2169107 = 3253661) B3253661
theorem B4880501 : Blo 2167435 4880501 := bbase (se 5 (by rfl) ⟨228773, by rfl⟩ : syracuseStep 4880501 = 457547) (by norm_num)
theorem B3253667 : Blo 2167435 3253667 := bstep (se 1 (by rfl) ⟨2440250, by rfl⟩ : syracuseStep 3253667 = 4880501) B4880501
theorem B2169111 : Blo 2167435 2169111 := bstep (se 1 (by rfl) ⟨1626833, by rfl⟩ : syracuseStep 2169111 = 3253667) B3253667
theorem B4947101 : Blo 2167435 4947101 := bbase (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) (by norm_num)
theorem B3298067 : Blo 2167435 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B2198711 : Blo 2167435 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B5863229 : Blo 2167435 5863229 := bstep (se 3 (by rfl) ⟨1099355, by rfl⟩ : syracuseStep 5863229 = 2198711) B2198711
theorem B3908819 : Blo 2167435 3908819 := bstep (se 1 (by rfl) ⟨2931614, by rfl⟩ : syracuseStep 3908819 = 5863229) B5863229
theorem B2605879 : Blo 2167435 2605879 := bstep (se 1 (by rfl) ⟨1954409, by rfl⟩ : syracuseStep 2605879 = 3908819) B3908819
theorem B3474505 : Blo 2167435 3474505 := bstep (se 2 (by rfl) ⟨1302939, by rfl⟩ : syracuseStep 3474505 = 2605879) B2605879
theorem B18530693 : Blo 2167435 18530693 := bstep (se 4 (by rfl) ⟨1737252, by rfl⟩ : syracuseStep 18530693 = 3474505) B3474505
theorem B12353795 : Blo 2167435 12353795 := bstep (se 1 (by rfl) ⟨9265346, by rfl⟩ : syracuseStep 12353795 = 18530693) B18530693
theorem B8235863 : Blo 2167435 8235863 := bstep (se 1 (by rfl) ⟨6176897, by rfl⟩ : syracuseStep 8235863 = 12353795) B12353795
theorem B5490575 : Blo 2167435 5490575 := bstep (se 1 (by rfl) ⟨4117931, by rfl⟩ : syracuseStep 5490575 = 8235863) B8235863
theorem B3660383 : Blo 2167435 3660383 := bstep (se 1 (by rfl) ⟨2745287, by rfl⟩ : syracuseStep 3660383 = 5490575) B5490575
theorem B2440255 : Blo 2167435 2440255 := bstep (se 1 (by rfl) ⟨1830191, by rfl⟩ : syracuseStep 2440255 = 3660383) B3660383
theorem B3253673 : Blo 2167435 3253673 := bstep (se 2 (by rfl) ⟨1220127, by rfl⟩ : syracuseStep 3253673 = 2440255) B2440255
theorem B2169115 : Blo 2167435 2169115 := bstep (se 1 (by rfl) ⟨1626836, by rfl⟩ : syracuseStep 2169115 = 3253673) B3253673
theorem B8235877 : Blo 2167435 8235877 := bbase (se 4 (by rfl) ⟨772113, by rfl⟩ : syracuseStep 8235877 = 1544227) (by norm_num)
theorem B10981169 : Blo 2167435 10981169 := bstep (se 2 (by rfl) ⟨4117938, by rfl⟩ : syracuseStep 10981169 = 8235877) B8235877
theorem B7320779 : Blo 2167435 7320779 := bstep (se 1 (by rfl) ⟨5490584, by rfl⟩ : syracuseStep 7320779 = 10981169) B10981169
theorem B4880519 : Blo 2167435 4880519 := bstep (se 1 (by rfl) ⟨3660389, by rfl⟩ : syracuseStep 4880519 = 7320779) B7320779
theorem B3253679 : Blo 2167435 3253679 := bstep (se 1 (by rfl) ⟨2440259, by rfl⟩ : syracuseStep 3253679 = 4880519) B4880519
theorem B2169119 : Blo 2167435 2169119 := bstep (se 1 (by rfl) ⟨1626839, by rfl⟩ : syracuseStep 2169119 = 3253679) B3253679
theorem B3253685 : Blo 2167435 3253685 := bbase (se 5 (by rfl) ⟨152516, by rfl⟩ : syracuseStep 3253685 = 305033) (by norm_num)
theorem B2169123 : Blo 2167435 2169123 := bstep (se 1 (by rfl) ⟨1626842, by rfl⟩ : syracuseStep 2169123 = 3253685) B3253685
theorem B5490605 : Blo 2167435 5490605 := bbase (se 3 (by rfl) ⟨1029488, by rfl⟩ : syracuseStep 5490605 = 2058977) (by norm_num)
theorem B3660403 : Blo 2167435 3660403 := bstep (se 1 (by rfl) ⟨2745302, by rfl⟩ : syracuseStep 3660403 = 5490605) B5490605
theorem B4880537 : Blo 2167435 4880537 := bstep (se 2 (by rfl) ⟨1830201, by rfl⟩ : syracuseStep 4880537 = 3660403) B3660403
theorem B3253691 : Blo 2167435 3253691 := bstep (se 1 (by rfl) ⟨2440268, by rfl⟩ : syracuseStep 3253691 = 4880537) B4880537
theorem B2169127 : Blo 2167435 2169127 := bstep (se 1 (by rfl) ⟨1626845, by rfl⟩ : syracuseStep 2169127 = 3253691) B3253691
theorem B2440273 : Blo 2167435 2440273 := bbase (se 2 (by rfl) ⟨915102, by rfl⟩ : syracuseStep 2440273 = 1830205) (by norm_num)
theorem B3253697 : Blo 2167435 3253697 := bstep (se 2 (by rfl) ⟨1220136, by rfl⟩ : syracuseStep 3253697 = 2440273) B2440273
theorem B2169131 : Blo 2167435 2169131 := bstep (se 1 (by rfl) ⟨1626848, by rfl⟩ : syracuseStep 2169131 = 3253697) B3253697
theorem B3088477 : Blo 2167435 3088477 := bbase (se 3 (by rfl) ⟨579089, by rfl⟩ : syracuseStep 3088477 = 1158179) (by norm_num)
theorem B4117969 : Blo 2167435 4117969 := bstep (se 2 (by rfl) ⟨1544238, by rfl⟩ : syracuseStep 4117969 = 3088477) B3088477
theorem B5490625 : Blo 2167435 5490625 := bstep (se 2 (by rfl) ⟨2058984, by rfl⟩ : syracuseStep 5490625 = 4117969) B4117969
theorem B7320833 : Blo 2167435 7320833 := bstep (se 2 (by rfl) ⟨2745312, by rfl⟩ : syracuseStep 7320833 = 5490625) B5490625
theorem B4880555 : Blo 2167435 4880555 := bstep (se 1 (by rfl) ⟨3660416, by rfl⟩ : syracuseStep 4880555 = 7320833) B7320833
theorem B3253703 : Blo 2167435 3253703 := bstep (se 1 (by rfl) ⟨2440277, by rfl⟩ : syracuseStep 3253703 = 4880555) B4880555
theorem B2169135 : Blo 2167435 2169135 := bstep (se 1 (by rfl) ⟨1626851, by rfl⟩ : syracuseStep 2169135 = 3253703) B3253703
theorem B3253709 : Blo 2167435 3253709 := bbase (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) (by norm_num)
theorem B2169139 : Blo 2167435 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B4880573 : Blo 2167435 4880573 := bbase (se 3 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 4880573 = 1830215) (by norm_num)
theorem B3253715 : Blo 2167435 3253715 := bstep (se 1 (by rfl) ⟨2440286, by rfl⟩ : syracuseStep 3253715 = 4880573) B4880573
theorem B2169143 : Blo 2167435 2169143 := bstep (se 1 (by rfl) ⟨1626857, by rfl⟩ : syracuseStep 2169143 = 3253715) B3253715
theorem B3660437 : Blo 2167435 3660437 := bbase (se 6 (by rfl) ⟨85791, by rfl⟩ : syracuseStep 3660437 = 171583) (by norm_num)
theorem B2440291 : Blo 2167435 2440291 := bstep (se 1 (by rfl) ⟨1830218, by rfl⟩ : syracuseStep 2440291 = 3660437) B3660437
theorem B3253721 : Blo 2167435 3253721 := bstep (se 2 (by rfl) ⟨1220145, by rfl⟩ : syracuseStep 3253721 = 2440291) B2440291
theorem B2169147 : Blo 2167435 2169147 := bstep (se 1 (by rfl) ⟨1626860, by rfl⟩ : syracuseStep 2169147 = 3253721) B3253721
theorem B17589973 : Blo 2167435 17589973 := bbase (se 7 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 17589973 = 412265) (by norm_num)
theorem B23453297 : Blo 2167435 23453297 := bstep (se 2 (by rfl) ⟨8794986, by rfl⟩ : syracuseStep 23453297 = 17589973) B17589973
theorem B15635531 : Blo 2167435 15635531 := bstep (se 1 (by rfl) ⟨11726648, by rfl⟩ : syracuseStep 15635531 = 23453297) B23453297
theorem B10423687 : Blo 2167435 10423687 := bstep (se 1 (by rfl) ⟨7817765, by rfl⟩ : syracuseStep 10423687 = 15635531) B15635531
theorem B13898249 : Blo 2167435 13898249 := bstep (se 2 (by rfl) ⟨5211843, by rfl⟩ : syracuseStep 13898249 = 10423687) B10423687
theorem B9265499 : Blo 2167435 9265499 := bstep (se 1 (by rfl) ⟨6949124, by rfl⟩ : syracuseStep 9265499 = 13898249) B13898249
theorem B6176999 : Blo 2167435 6176999 := bstep (se 1 (by rfl) ⟨4632749, by rfl⟩ : syracuseStep 6176999 = 9265499) B9265499
theorem B16471997 : Blo 2167435 16471997 := bstep (se 3 (by rfl) ⟨3088499, by rfl⟩ : syracuseStep 16471997 = 6176999) B6176999
theorem B10981331 : Blo 2167435 10981331 := bstep (se 1 (by rfl) ⟨8235998, by rfl⟩ : syracuseStep 10981331 = 16471997) B16471997
theorem B7320887 : Blo 2167435 7320887 := bstep (se 1 (by rfl) ⟨5490665, by rfl⟩ : syracuseStep 7320887 = 10981331) B10981331
theorem B4880591 : Blo 2167435 4880591 := bstep (se 1 (by rfl) ⟨3660443, by rfl⟩ : syracuseStep 4880591 = 7320887) B7320887
theorem B3253727 : Blo 2167435 3253727 := bstep (se 1 (by rfl) ⟨2440295, by rfl⟩ : syracuseStep 3253727 = 4880591) B4880591
theorem B2169151 : Blo 2167435 2169151 := bstep (se 1 (by rfl) ⟨1626863, by rfl⟩ : syracuseStep 2169151 = 3253727) B3253727
theorem B3253733 : Blo 2167435 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B2169155 : Blo 2167435 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B2576233 : Blo 2167435 2576233 := bbase (se 2 (by rfl) ⟨966087, by rfl⟩ : syracuseStep 2576233 = 1932175) (by norm_num)
theorem B3434977 : Blo 2167435 3434977 := bstep (se 2 (by rfl) ⟨1288116, by rfl⟩ : syracuseStep 3434977 = 2576233) B2576233
theorem B18319877 : Blo 2167435 18319877 := bstep (se 4 (by rfl) ⟨1717488, by rfl⟩ : syracuseStep 18319877 = 3434977) B3434977
theorem B12213251 : Blo 2167435 12213251 := bstep (se 1 (by rfl) ⟨9159938, by rfl⟩ : syracuseStep 12213251 = 18319877) B18319877
theorem B8142167 : Blo 2167435 8142167 := bstep (se 1 (by rfl) ⟨6106625, by rfl⟩ : syracuseStep 8142167 = 12213251) B12213251
theorem B21712445 : Blo 2167435 21712445 := bstep (se 3 (by rfl) ⟨4071083, by rfl⟩ : syracuseStep 21712445 = 8142167) B8142167
theorem B14474963 : Blo 2167435 14474963 := bstep (se 1 (by rfl) ⟨10856222, by rfl⟩ : syracuseStep 14474963 = 21712445) B21712445
theorem B9649975 : Blo 2167435 9649975 := bstep (se 1 (by rfl) ⟨7237481, by rfl⟩ : syracuseStep 9649975 = 14474963) B14474963
theorem B12866633 : Blo 2167435 12866633 := bstep (se 2 (by rfl) ⟨4824987, by rfl⟩ : syracuseStep 12866633 = 9649975) B9649975
theorem B8577755 : Blo 2167435 8577755 := bstep (se 1 (by rfl) ⟨6433316, by rfl⟩ : syracuseStep 8577755 = 12866633) B12866633
theorem B5718503 : Blo 2167435 5718503 := bstep (se 1 (by rfl) ⟨4288877, by rfl⟩ : syracuseStep 5718503 = 8577755) B8577755
theorem B3812335 : Blo 2167435 3812335 := bstep (se 1 (by rfl) ⟨2859251, by rfl⟩ : syracuseStep 3812335 = 5718503) B5718503
theorem B20332453 : Blo 2167435 20332453 := bstep (se 4 (by rfl) ⟨1906167, by rfl⟩ : syracuseStep 20332453 = 3812335) B3812335
theorem B27109937 : Blo 2167435 27109937 := bstep (se 2 (by rfl) ⟨10166226, by rfl⟩ : syracuseStep 27109937 = 20332453) B20332453
theorem B72293165 : Blo 2167435 72293165 := bstep (se 3 (by rfl) ⟨13554968, by rfl⟩ : syracuseStep 72293165 = 27109937) B27109937
theorem B48195443 : Blo 2167435 48195443 := bstep (se 1 (by rfl) ⟨36146582, by rfl⟩ : syracuseStep 48195443 = 72293165) B72293165
theorem B128521181 : Blo 2167435 128521181 := bstep (se 3 (by rfl) ⟨24097721, by rfl⟩ : syracuseStep 128521181 = 48195443) B48195443
theorem B85680787 : Blo 2167435 85680787 := bstep (se 1 (by rfl) ⟨64260590, by rfl⟩ : syracuseStep 85680787 = 128521181) B128521181
theorem B114241049 : Blo 2167435 114241049 := bstep (se 2 (by rfl) ⟨42840393, by rfl⟩ : syracuseStep 114241049 = 85680787) B85680787
theorem B76160699 : Blo 2167435 76160699 := bstep (se 1 (by rfl) ⟨57120524, by rfl⟩ : syracuseStep 76160699 = 114241049) B114241049
theorem B50773799 : Blo 2167435 50773799 := bstep (se 1 (by rfl) ⟨38080349, by rfl⟩ : syracuseStep 50773799 = 76160699) B76160699
theorem B33849199 : Blo 2167435 33849199 := bstep (se 1 (by rfl) ⟨25386899, by rfl⟩ : syracuseStep 33849199 = 50773799) B50773799
theorem B45132265 : Blo 2167435 45132265 := bstep (se 2 (by rfl) ⟨16924599, by rfl⟩ : syracuseStep 45132265 = 33849199) B33849199
theorem B60176353 : Blo 2167435 60176353 := bstep (se 2 (by rfl) ⟨22566132, by rfl⟩ : syracuseStep 60176353 = 45132265) B45132265
theorem B80235137 : Blo 2167435 80235137 := bstep (se 2 (by rfl) ⟨30088176, by rfl⟩ : syracuseStep 80235137 = 60176353) B60176353
theorem B53490091 : Blo 2167435 53490091 := bstep (se 1 (by rfl) ⟨40117568, by rfl⟩ : syracuseStep 53490091 = 80235137) B80235137
theorem B71320121 : Blo 2167435 71320121 := bstep (se 2 (by rfl) ⟨26745045, by rfl⟩ : syracuseStep 71320121 = 53490091) B53490091
theorem B47546747 : Blo 2167435 47546747 := bstep (se 1 (by rfl) ⟨35660060, by rfl⟩ : syracuseStep 47546747 = 71320121) B71320121
theorem B31697831 : Blo 2167435 31697831 := bstep (se 1 (by rfl) ⟨23773373, by rfl⟩ : syracuseStep 31697831 = 47546747) B47546747
theorem B84527549 : Blo 2167435 84527549 := bstep (se 3 (by rfl) ⟨15848915, by rfl⟩ : syracuseStep 84527549 = 31697831) B31697831
theorem B56351699 : Blo 2167435 56351699 := bstep (se 1 (by rfl) ⟨42263774, by rfl⟩ : syracuseStep 56351699 = 84527549) B84527549
theorem B37567799 : Blo 2167435 37567799 := bstep (se 1 (by rfl) ⟨28175849, by rfl⟩ : syracuseStep 37567799 = 56351699) B56351699
theorem B25045199 : Blo 2167435 25045199 := bstep (se 1 (by rfl) ⟨18783899, by rfl⟩ : syracuseStep 25045199 = 37567799) B37567799
theorem B16696799 : Blo 2167435 16696799 := bstep (se 1 (by rfl) ⟨12522599, by rfl⟩ : syracuseStep 16696799 = 25045199) B25045199
theorem B11131199 : Blo 2167435 11131199 := bstep (se 1 (by rfl) ⟨8348399, by rfl⟩ : syracuseStep 11131199 = 16696799) B16696799
theorem B7420799 : Blo 2167435 7420799 := bstep (se 1 (by rfl) ⟨5565599, by rfl⟩ : syracuseStep 7420799 = 11131199) B11131199
theorem B4947199 : Blo 2167435 4947199 := bstep (se 1 (by rfl) ⟨3710399, by rfl⟩ : syracuseStep 4947199 = 7420799) B7420799
theorem B105540245 : Blo 2167435 105540245 := bstep (se 6 (by rfl) ⟨2473599, by rfl⟩ : syracuseStep 105540245 = 4947199) B4947199
theorem B70360163 : Blo 2167435 70360163 := bstep (se 1 (by rfl) ⟨52770122, by rfl⟩ : syracuseStep 70360163 = 105540245) B105540245
theorem B46906775 : Blo 2167435 46906775 := bstep (se 1 (by rfl) ⟨35180081, by rfl⟩ : syracuseStep 46906775 = 70360163) B70360163
theorem B31271183 : Blo 2167435 31271183 := bstep (se 1 (by rfl) ⟨23453387, by rfl⟩ : syracuseStep 31271183 = 46906775) B46906775
theorem B20847455 : Blo 2167435 20847455 := bstep (se 1 (by rfl) ⟨15635591, by rfl⟩ : syracuseStep 20847455 = 31271183) B31271183
theorem B13898303 : Blo 2167435 13898303 := bstep (se 1 (by rfl) ⟨10423727, by rfl⟩ : syracuseStep 13898303 = 20847455) B20847455
theorem B9265535 : Blo 2167435 9265535 := bstep (se 1 (by rfl) ⟨6949151, by rfl⟩ : syracuseStep 9265535 = 13898303) B13898303
theorem B6177023 : Blo 2167435 6177023 := bstep (se 1 (by rfl) ⟨4632767, by rfl⟩ : syracuseStep 6177023 = 9265535) B9265535
theorem B4118015 : Blo 2167435 4118015 := bstep (se 1 (by rfl) ⟨3088511, by rfl⟩ : syracuseStep 4118015 = 6177023) B6177023
theorem B2745343 : Blo 2167435 2745343 := bstep (se 1 (by rfl) ⟨2059007, by rfl⟩ : syracuseStep 2745343 = 4118015) B4118015
theorem B3660457 : Blo 2167435 3660457 := bstep (se 2 (by rfl) ⟨1372671, by rfl⟩ : syracuseStep 3660457 = 2745343) B2745343
theorem B4880609 : Blo 2167435 4880609 := bstep (se 2 (by rfl) ⟨1830228, by rfl⟩ : syracuseStep 4880609 = 3660457) B3660457
theorem B3253739 : Blo 2167435 3253739 := bstep (se 1 (by rfl) ⟨2440304, by rfl⟩ : syracuseStep 3253739 = 4880609) B4880609
theorem B2169159 : Blo 2167435 2169159 := bstep (se 1 (by rfl) ⟨1626869, by rfl⟩ : syracuseStep 2169159 = 3253739) B3253739
theorem B2440309 : Blo 2167435 2440309 := bbase (se 5 (by rfl) ⟨114389, by rfl⟩ : syracuseStep 2440309 = 228779) (by norm_num)
theorem B3253745 : Blo 2167435 3253745 := bstep (se 2 (by rfl) ⟨1220154, by rfl⟩ : syracuseStep 3253745 = 2440309) B2440309
theorem B2169163 : Blo 2167435 2169163 := bstep (se 1 (by rfl) ⟨1626872, by rfl⟩ : syracuseStep 2169163 = 3253745) B3253745
theorem B2745353 : Blo 2167435 2745353 := bbase (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) (by norm_num)
theorem B7320941 : Blo 2167435 7320941 := bstep (se 3 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 7320941 = 2745353) B2745353
theorem B4880627 : Blo 2167435 4880627 := bstep (se 1 (by rfl) ⟨3660470, by rfl⟩ : syracuseStep 4880627 = 7320941) B7320941
theorem B3253751 : Blo 2167435 3253751 := bstep (se 1 (by rfl) ⟨2440313, by rfl⟩ : syracuseStep 3253751 = 4880627) B4880627
theorem B2169167 : Blo 2167435 2169167 := bstep (se 1 (by rfl) ⟨1626875, by rfl⟩ : syracuseStep 2169167 = 3253751) B3253751
theorem B3253757 : Blo 2167435 3253757 := bbase (se 3 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 3253757 = 1220159) (by norm_num)
theorem B2169171 : Blo 2167435 2169171 := bstep (se 1 (by rfl) ⟨1626878, by rfl⟩ : syracuseStep 2169171 = 3253757) B3253757
theorem B4880645 : Blo 2167435 4880645 := bbase (se 4 (by rfl) ⟨457560, by rfl⟩ : syracuseStep 4880645 = 915121) (by norm_num)
theorem B3253763 : Blo 2167435 3253763 := bstep (se 1 (by rfl) ⟨2440322, by rfl⟩ : syracuseStep 3253763 = 4880645) B4880645
theorem B2169175 : Blo 2167435 2169175 := bstep (se 1 (by rfl) ⟨1626881, by rfl⟩ : syracuseStep 2169175 = 3253763) B3253763
theorem B4118053 : Blo 2167435 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B5490737 : Blo 2167435 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B3660491 : Blo 2167435 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B2440327 : Blo 2167435 2440327 := bstep (se 1 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 2440327 = 3660491) B3660491
theorem B3253769 : Blo 2167435 3253769 := bstep (se 2 (by rfl) ⟨1220163, by rfl⟩ : syracuseStep 3253769 = 2440327) B2440327
theorem B2169179 : Blo 2167435 2169179 := bstep (se 1 (by rfl) ⟨1626884, by rfl⟩ : syracuseStep 2169179 = 3253769) B3253769
theorem B10981493 : Blo 2167435 10981493 := bbase (se 5 (by rfl) ⟨514757, by rfl⟩ : syracuseStep 10981493 = 1029515) (by norm_num)
theorem B7320995 : Blo 2167435 7320995 := bstep (se 1 (by rfl) ⟨5490746, by rfl⟩ : syracuseStep 7320995 = 10981493) B10981493
theorem B4880663 : Blo 2167435 4880663 := bstep (se 1 (by rfl) ⟨3660497, by rfl⟩ : syracuseStep 4880663 = 7320995) B7320995
theorem B3253775 : Blo 2167435 3253775 := bstep (se 1 (by rfl) ⟨2440331, by rfl⟩ : syracuseStep 3253775 = 4880663) B4880663
theorem B2169183 : Blo 2167435 2169183 := bstep (se 1 (by rfl) ⟨1626887, by rfl⟩ : syracuseStep 2169183 = 3253775) B3253775
theorem B3253781 : Blo 2167435 3253781 := bbase (se 6 (by rfl) ⟨76260, by rfl⟩ : syracuseStep 3253781 = 152521) (by norm_num)
theorem B2169187 : Blo 2167435 2169187 := bstep (se 1 (by rfl) ⟨1626890, by rfl⟩ : syracuseStep 2169187 = 3253781) B3253781
theorem B6949253 : Blo 2167435 6949253 := bbase (se 4 (by rfl) ⟨651492, by rfl⟩ : syracuseStep 6949253 = 1302985) (by norm_num)
theorem B18531341 : Blo 2167435 18531341 := bstep (se 3 (by rfl) ⟨3474626, by rfl⟩ : syracuseStep 18531341 = 6949253) B6949253
theorem B12354227 : Blo 2167435 12354227 := bstep (se 1 (by rfl) ⟨9265670, by rfl⟩ : syracuseStep 12354227 = 18531341) B18531341
theorem B8236151 : Blo 2167435 8236151 := bstep (se 1 (by rfl) ⟨6177113, by rfl⟩ : syracuseStep 8236151 = 12354227) B12354227
theorem B5490767 : Blo 2167435 5490767 := bstep (se 1 (by rfl) ⟨4118075, by rfl⟩ : syracuseStep 5490767 = 8236151) B8236151
theorem B3660511 : Blo 2167435 3660511 := bstep (se 1 (by rfl) ⟨2745383, by rfl⟩ : syracuseStep 3660511 = 5490767) B5490767
theorem B4880681 : Blo 2167435 4880681 := bstep (se 2 (by rfl) ⟨1830255, by rfl⟩ : syracuseStep 4880681 = 3660511) B3660511
theorem B3253787 : Blo 2167435 3253787 := bstep (se 1 (by rfl) ⟨2440340, by rfl⟩ : syracuseStep 3253787 = 4880681) B4880681
theorem B2169191 : Blo 2167435 2169191 := bstep (se 1 (by rfl) ⟨1626893, by rfl⟩ : syracuseStep 2169191 = 3253787) B3253787
theorem B2440345 : Blo 2167435 2440345 := bbase (se 2 (by rfl) ⟨915129, by rfl⟩ : syracuseStep 2440345 = 1830259) (by norm_num)
theorem B3253793 : Blo 2167435 3253793 := bstep (se 2 (by rfl) ⟨1220172, by rfl⟩ : syracuseStep 3253793 = 2440345) B2440345
theorem B2169195 : Blo 2167435 2169195 := bstep (se 1 (by rfl) ⟨1626896, by rfl⟩ : syracuseStep 2169195 = 3253793) B3253793
theorem B8236181 : Blo 2167435 8236181 := bbase (se 6 (by rfl) ⟨193035, by rfl⟩ : syracuseStep 8236181 = 386071) (by norm_num)
theorem B5490787 : Blo 2167435 5490787 := bstep (se 1 (by rfl) ⟨4118090, by rfl⟩ : syracuseStep 5490787 = 8236181) B8236181
theorem B7321049 : Blo 2167435 7321049 := bstep (se 2 (by rfl) ⟨2745393, by rfl⟩ : syracuseStep 7321049 = 5490787) B5490787
theorem B4880699 : Blo 2167435 4880699 := bstep (se 1 (by rfl) ⟨3660524, by rfl⟩ : syracuseStep 4880699 = 7321049) B7321049
theorem B3253799 : Blo 2167435 3253799 := bstep (se 1 (by rfl) ⟨2440349, by rfl⟩ : syracuseStep 3253799 = 4880699) B4880699
theorem B2169199 : Blo 2167435 2169199 := bstep (se 1 (by rfl) ⟨1626899, by rfl⟩ : syracuseStep 2169199 = 3253799) B3253799
theorem B3253805 : Blo 2167435 3253805 := bbase (se 3 (by rfl) ⟨610088, by rfl⟩ : syracuseStep 3253805 = 1220177) (by norm_num)
theorem B2169203 : Blo 2167435 2169203 := bstep (se 1 (by rfl) ⟨1626902, by rfl⟩ : syracuseStep 2169203 = 3253805) B3253805
theorem B4880717 : Blo 2167435 4880717 := bbase (se 3 (by rfl) ⟨915134, by rfl⟩ : syracuseStep 4880717 = 1830269) (by norm_num)
theorem B3253811 : Blo 2167435 3253811 := bstep (se 1 (by rfl) ⟨2440358, by rfl⟩ : syracuseStep 3253811 = 4880717) B4880717
theorem B2169207 : Blo 2167435 2169207 := bstep (se 1 (by rfl) ⟨1626905, by rfl⟩ : syracuseStep 2169207 = 3253811) B3253811
theorem B2745409 : Blo 2167435 2745409 := bbase (se 2 (by rfl) ⟨1029528, by rfl⟩ : syracuseStep 2745409 = 2059057) (by norm_num)
theorem B3660545 : Blo 2167435 3660545 := bstep (se 2 (by rfl) ⟨1372704, by rfl⟩ : syracuseStep 3660545 = 2745409) B2745409
theorem B2440363 : Blo 2167435 2440363 := bstep (se 1 (by rfl) ⟨1830272, by rfl⟩ : syracuseStep 2440363 = 3660545) B3660545
theorem B3253817 : Blo 2167435 3253817 := bstep (se 2 (by rfl) ⟨1220181, by rfl⟩ : syracuseStep 3253817 = 2440363) B2440363
theorem B2169211 : Blo 2167435 2169211 := bstep (se 1 (by rfl) ⟨1626908, by rfl⟩ : syracuseStep 2169211 = 3253817) B3253817
theorem B6596437 : Blo 2167435 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B8795249 : Blo 2167435 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B5863499 : Blo 2167435 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B3908999 : Blo 2167435 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B2605999 : Blo 2167435 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B3474665 : Blo 2167435 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B2316443 : Blo 2167435 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B24708725 : Blo 2167435 24708725 := bstep (se 5 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 24708725 = 2316443) B2316443
theorem B16472483 : Blo 2167435 16472483 := bstep (se 1 (by rfl) ⟨12354362, by rfl⟩ : syracuseStep 16472483 = 24708725) B24708725
theorem B10981655 : Blo 2167435 10981655 := bstep (se 1 (by rfl) ⟨8236241, by rfl⟩ : syracuseStep 10981655 = 16472483) B16472483
theorem B7321103 : Blo 2167435 7321103 := bstep (se 1 (by rfl) ⟨5490827, by rfl⟩ : syracuseStep 7321103 = 10981655) B10981655
theorem B4880735 : Blo 2167435 4880735 := bstep (se 1 (by rfl) ⟨3660551, by rfl⟩ : syracuseStep 4880735 = 7321103) B7321103
theorem B3253823 : Blo 2167435 3253823 := bstep (se 1 (by rfl) ⟨2440367, by rfl⟩ : syracuseStep 3253823 = 4880735) B4880735
theorem B2169215 : Blo 2167435 2169215 := bstep (se 1 (by rfl) ⟨1626911, by rfl⟩ : syracuseStep 2169215 = 3253823) B3253823
theorem B3253829 : Blo 2167435 3253829 := bbase (se 4 (by rfl) ⟨305046, by rfl⟩ : syracuseStep 3253829 = 610093) (by norm_num)
theorem B2169219 : Blo 2167435 2169219 := bstep (se 1 (by rfl) ⟨1626914, by rfl⟩ : syracuseStep 2169219 = 3253829) B3253829
theorem B3660565 : Blo 2167435 3660565 := bbase (se 6 (by rfl) ⟨85794, by rfl⟩ : syracuseStep 3660565 = 171589) (by norm_num)
theorem B4880753 : Blo 2167435 4880753 := bstep (se 2 (by rfl) ⟨1830282, by rfl⟩ : syracuseStep 4880753 = 3660565) B3660565
theorem B3253835 : Blo 2167435 3253835 := bstep (se 1 (by rfl) ⟨2440376, by rfl⟩ : syracuseStep 3253835 = 4880753) B4880753
theorem B2169223 : Blo 2167435 2169223 := bstep (se 1 (by rfl) ⟨1626917, by rfl⟩ : syracuseStep 2169223 = 3253835) B3253835
theorem B2440381 : Blo 2167435 2440381 := bbase (se 3 (by rfl) ⟨457571, by rfl⟩ : syracuseStep 2440381 = 915143) (by norm_num)
theorem B3253841 : Blo 2167435 3253841 := bstep (se 2 (by rfl) ⟨1220190, by rfl⟩ : syracuseStep 3253841 = 2440381) B2440381
theorem B2169227 : Blo 2167435 2169227 := bstep (se 1 (by rfl) ⟨1626920, by rfl⟩ : syracuseStep 2169227 = 3253841) B3253841
theorem B7321157 : Blo 2167435 7321157 := bbase (se 4 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 7321157 = 1372717) (by norm_num)
theorem B4880771 : Blo 2167435 4880771 := bstep (se 1 (by rfl) ⟨3660578, by rfl⟩ : syracuseStep 4880771 = 7321157) B7321157
theorem B3253847 : Blo 2167435 3253847 := bstep (se 1 (by rfl) ⟨2440385, by rfl⟩ : syracuseStep 3253847 = 4880771) B4880771
theorem B2169231 : Blo 2167435 2169231 := bstep (se 1 (by rfl) ⟨1626923, by rfl⟩ : syracuseStep 2169231 = 3253847) B3253847
theorem B3253853 : Blo 2167435 3253853 := bbase (se 3 (by rfl) ⟨610097, by rfl⟩ : syracuseStep 3253853 = 1220195) (by norm_num)
theorem B2169235 : Blo 2167435 2169235 := bstep (se 1 (by rfl) ⟨1626926, by rfl⟩ : syracuseStep 2169235 = 3253853) B3253853
theorem B4880789 : Blo 2167435 4880789 := bbase (se 6 (by rfl) ⟨114393, by rfl⟩ : syracuseStep 4880789 = 228787) (by norm_num)
theorem B3253859 : Blo 2167435 3253859 := bstep (se 1 (by rfl) ⟨2440394, by rfl⟩ : syracuseStep 3253859 = 4880789) B4880789
theorem B2169239 : Blo 2167435 2169239 := bstep (se 1 (by rfl) ⟨1626929, by rfl⟩ : syracuseStep 2169239 = 3253859) B3253859
theorem B2606033 : Blo 2167435 2606033 := bbase (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) (by norm_num)
theorem B6949421 : Blo 2167435 6949421 := bstep (se 3 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 6949421 = 2606033) B2606033
theorem B4632947 : Blo 2167435 4632947 := bstep (se 1 (by rfl) ⟨3474710, by rfl⟩ : syracuseStep 4632947 = 6949421) B6949421
theorem B3088631 : Blo 2167435 3088631 := bstep (se 1 (by rfl) ⟨2316473, by rfl⟩ : syracuseStep 3088631 = 4632947) B4632947
theorem B8236349 : Blo 2167435 8236349 := bstep (se 3 (by rfl) ⟨1544315, by rfl⟩ : syracuseStep 8236349 = 3088631) B3088631
theorem B5490899 : Blo 2167435 5490899 := bstep (se 1 (by rfl) ⟨4118174, by rfl⟩ : syracuseStep 5490899 = 8236349) B8236349
theorem B3660599 : Blo 2167435 3660599 := bstep (se 1 (by rfl) ⟨2745449, by rfl⟩ : syracuseStep 3660599 = 5490899) B5490899
theorem B2440399 : Blo 2167435 2440399 := bstep (se 1 (by rfl) ⟨1830299, by rfl⟩ : syracuseStep 2440399 = 3660599) B3660599
theorem B3253865 : Blo 2167435 3253865 := bstep (se 2 (by rfl) ⟨1220199, by rfl⟩ : syracuseStep 3253865 = 2440399) B2440399
theorem B2169243 : Blo 2167435 2169243 := bstep (se 1 (by rfl) ⟨1626932, by rfl⟩ : syracuseStep 2169243 = 3253865) B3253865
theorem B9265909 : Blo 2167435 9265909 := bbase (se 5 (by rfl) ⟨434339, by rfl⟩ : syracuseStep 9265909 = 868679) (by norm_num)
theorem B12354545 : Blo 2167435 12354545 := bstep (se 2 (by rfl) ⟨4632954, by rfl⟩ : syracuseStep 12354545 = 9265909) B9265909
theorem B8236363 : Blo 2167435 8236363 := bstep (se 1 (by rfl) ⟨6177272, by rfl⟩ : syracuseStep 8236363 = 12354545) B12354545
theorem B10981817 : Blo 2167435 10981817 := bstep (se 2 (by rfl) ⟨4118181, by rfl⟩ : syracuseStep 10981817 = 8236363) B8236363
theorem B7321211 : Blo 2167435 7321211 := bstep (se 1 (by rfl) ⟨5490908, by rfl⟩ : syracuseStep 7321211 = 10981817) B10981817
theorem B4880807 : Blo 2167435 4880807 := bstep (se 1 (by rfl) ⟨3660605, by rfl⟩ : syracuseStep 4880807 = 7321211) B7321211
theorem B3253871 : Blo 2167435 3253871 := bstep (se 1 (by rfl) ⟨2440403, by rfl⟩ : syracuseStep 3253871 = 4880807) B4880807
theorem B2169247 : Blo 2167435 2169247 := bstep (se 1 (by rfl) ⟨1626935, by rfl⟩ : syracuseStep 2169247 = 3253871) B3253871
theorem B3253877 : Blo 2167435 3253877 := bbase (se 5 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 3253877 = 305051) (by norm_num)
theorem B2169251 : Blo 2167435 2169251 := bstep (se 1 (by rfl) ⟨1626938, by rfl⟩ : syracuseStep 2169251 = 3253877) B3253877
theorem B4118197 : Blo 2167435 4118197 := bbase (se 5 (by rfl) ⟨193040, by rfl⟩ : syracuseStep 4118197 = 386081) (by norm_num)
theorem B5490929 : Blo 2167435 5490929 := bstep (se 2 (by rfl) ⟨2059098, by rfl⟩ : syracuseStep 5490929 = 4118197) B4118197
theorem B3660619 : Blo 2167435 3660619 := bstep (se 1 (by rfl) ⟨2745464, by rfl⟩ : syracuseStep 3660619 = 5490929) B5490929
theorem B4880825 : Blo 2167435 4880825 := bstep (se 2 (by rfl) ⟨1830309, by rfl⟩ : syracuseStep 4880825 = 3660619) B3660619
theorem B3253883 : Blo 2167435 3253883 := bstep (se 1 (by rfl) ⟨2440412, by rfl⟩ : syracuseStep 3253883 = 4880825) B4880825
theorem B2169255 : Blo 2167435 2169255 := bstep (se 1 (by rfl) ⟨1626941, by rfl⟩ : syracuseStep 2169255 = 3253883) B3253883
theorem B2440417 : Blo 2167435 2440417 := bbase (se 2 (by rfl) ⟨915156, by rfl⟩ : syracuseStep 2440417 = 1830313) (by norm_num)
theorem B3253889 : Blo 2167435 3253889 := bstep (se 2 (by rfl) ⟨1220208, by rfl⟩ : syracuseStep 3253889 = 2440417) B2440417
theorem B2169259 : Blo 2167435 2169259 := bstep (se 1 (by rfl) ⟨1626944, by rfl⟩ : syracuseStep 2169259 = 3253889) B3253889
theorem B5490949 : Blo 2167435 5490949 := bbase (se 4 (by rfl) ⟨514776, by rfl⟩ : syracuseStep 5490949 = 1029553) (by norm_num)
theorem B7321265 : Blo 2167435 7321265 := bstep (se 2 (by rfl) ⟨2745474, by rfl⟩ : syracuseStep 7321265 = 5490949) B5490949
theorem B4880843 : Blo 2167435 4880843 := bstep (se 1 (by rfl) ⟨3660632, by rfl⟩ : syracuseStep 4880843 = 7321265) B7321265
theorem B3253895 : Blo 2167435 3253895 := bstep (se 1 (by rfl) ⟨2440421, by rfl⟩ : syracuseStep 3253895 = 4880843) B4880843
theorem B2169263 : Blo 2167435 2169263 := bstep (se 1 (by rfl) ⟨1626947, by rfl⟩ : syracuseStep 2169263 = 3253895) B3253895
theorem B3253901 : Blo 2167435 3253901 := bbase (se 3 (by rfl) ⟨610106, by rfl⟩ : syracuseStep 3253901 = 1220213) (by norm_num)
theorem B2169267 : Blo 2167435 2169267 := bstep (se 1 (by rfl) ⟨1626950, by rfl⟩ : syracuseStep 2169267 = 3253901) B3253901
theorem B4880861 : Blo 2167435 4880861 := bbase (se 3 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 4880861 = 1830323) (by norm_num)
theorem B3253907 : Blo 2167435 3253907 := bstep (se 1 (by rfl) ⟨2440430, by rfl⟩ : syracuseStep 3253907 = 4880861) B4880861
theorem B2169271 : Blo 2167435 2169271 := bstep (se 1 (by rfl) ⟨1626953, by rfl⟩ : syracuseStep 2169271 = 3253907) B3253907
theorem B3660653 : Blo 2167435 3660653 := bbase (se 3 (by rfl) ⟨686372, by rfl⟩ : syracuseStep 3660653 = 1372745) (by norm_num)
theorem B2440435 : Blo 2167435 2440435 := bstep (se 1 (by rfl) ⟨1830326, by rfl⟩ : syracuseStep 2440435 = 3660653) B3660653
theorem B3253913 : Blo 2167435 3253913 := bstep (se 2 (by rfl) ⟨1220217, by rfl⟩ : syracuseStep 3253913 = 2440435) B2440435
theorem B2169275 : Blo 2167435 2169275 := bstep (se 1 (by rfl) ⟨1626956, by rfl⟩ : syracuseStep 2169275 = 3253913) B3253913
theorem B26746517 : Blo 2167435 26746517 := bbase (se 6 (by rfl) ⟨626871, by rfl⟩ : syracuseStep 26746517 = 1253743) (by norm_num)
theorem B17831011 : Blo 2167435 17831011 := bstep (se 1 (by rfl) ⟨13373258, by rfl⟩ : syracuseStep 17831011 = 26746517) B26746517
theorem B23774681 : Blo 2167435 23774681 := bstep (se 2 (by rfl) ⟨8915505, by rfl⟩ : syracuseStep 23774681 = 17831011) B17831011
theorem B63399149 : Blo 2167435 63399149 := bstep (se 3 (by rfl) ⟨11887340, by rfl⟩ : syracuseStep 63399149 = 23774681) B23774681
theorem B42266099 : Blo 2167435 42266099 := bstep (se 1 (by rfl) ⟨31699574, by rfl⟩ : syracuseStep 42266099 = 63399149) B63399149
theorem B28177399 : Blo 2167435 28177399 := bstep (se 1 (by rfl) ⟨21133049, by rfl⟩ : syracuseStep 28177399 = 42266099) B42266099
theorem B37569865 : Blo 2167435 37569865 := bstep (se 2 (by rfl) ⟨14088699, by rfl⟩ : syracuseStep 37569865 = 28177399) B28177399
theorem B50093153 : Blo 2167435 50093153 := bstep (se 2 (by rfl) ⟨18784932, by rfl⟩ : syracuseStep 50093153 = 37569865) B37569865
theorem B33395435 : Blo 2167435 33395435 := bstep (se 1 (by rfl) ⟨25046576, by rfl⟩ : syracuseStep 33395435 = 50093153) B50093153
theorem B22263623 : Blo 2167435 22263623 := bstep (se 1 (by rfl) ⟨16697717, by rfl⟩ : syracuseStep 22263623 = 33395435) B33395435
theorem B14842415 : Blo 2167435 14842415 := bstep (se 1 (by rfl) ⟨11131811, by rfl⟩ : syracuseStep 14842415 = 22263623) B22263623
theorem B9894943 : Blo 2167435 9894943 := bstep (se 1 (by rfl) ⟨7421207, by rfl⟩ : syracuseStep 9894943 = 14842415) B14842415
theorem B52773029 : Blo 2167435 52773029 := bstep (se 4 (by rfl) ⟨4947471, by rfl⟩ : syracuseStep 52773029 = 9894943) B9894943
theorem B35182019 : Blo 2167435 35182019 := bstep (se 1 (by rfl) ⟨26386514, by rfl⟩ : syracuseStep 35182019 = 52773029) B52773029
theorem B23454679 : Blo 2167435 23454679 := bstep (se 1 (by rfl) ⟨17591009, by rfl⟩ : syracuseStep 23454679 = 35182019) B35182019
theorem B31272905 : Blo 2167435 31272905 := bstep (se 2 (by rfl) ⟨11727339, by rfl⟩ : syracuseStep 31272905 = 23454679) B23454679
theorem B20848603 : Blo 2167435 20848603 := bstep (se 1 (by rfl) ⟨15636452, by rfl⟩ : syracuseStep 20848603 = 31272905) B31272905
theorem B27798137 : Blo 2167435 27798137 := bstep (se 2 (by rfl) ⟨10424301, by rfl⟩ : syracuseStep 27798137 = 20848603) B20848603
theorem B18532091 : Blo 2167435 18532091 := bstep (se 1 (by rfl) ⟨13899068, by rfl⟩ : syracuseStep 18532091 = 27798137) B27798137
theorem B12354727 : Blo 2167435 12354727 := bstep (se 1 (by rfl) ⟨9266045, by rfl⟩ : syracuseStep 12354727 = 18532091) B18532091
theorem B16472969 : Blo 2167435 16472969 := bstep (se 2 (by rfl) ⟨6177363, by rfl⟩ : syracuseStep 16472969 = 12354727) B12354727
theorem B10981979 : Blo 2167435 10981979 := bstep (se 1 (by rfl) ⟨8236484, by rfl⟩ : syracuseStep 10981979 = 16472969) B16472969
theorem B7321319 : Blo 2167435 7321319 := bstep (se 1 (by rfl) ⟨5490989, by rfl⟩ : syracuseStep 7321319 = 10981979) B10981979
theorem B4880879 : Blo 2167435 4880879 := bstep (se 1 (by rfl) ⟨3660659, by rfl⟩ : syracuseStep 4880879 = 7321319) B7321319
theorem B3253919 : Blo 2167435 3253919 := bstep (se 1 (by rfl) ⟨2440439, by rfl⟩ : syracuseStep 3253919 = 4880879) B4880879
theorem B2169279 : Blo 2167435 2169279 := bstep (se 1 (by rfl) ⟨1626959, by rfl⟩ : syracuseStep 2169279 = 3253919) B3253919
theorem B3253925 : Blo 2167435 3253925 := bbase (se 4 (by rfl) ⟨305055, by rfl⟩ : syracuseStep 3253925 = 610111) (by norm_num)
theorem B2169283 : Blo 2167435 2169283 := bstep (se 1 (by rfl) ⟨1626962, by rfl⟩ : syracuseStep 2169283 = 3253925) B3253925
theorem B2745505 : Blo 2167435 2745505 := bbase (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) (by norm_num)
theorem B3660673 : Blo 2167435 3660673 := bstep (se 2 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 3660673 = 2745505) B2745505
theorem B4880897 : Blo 2167435 4880897 := bstep (se 2 (by rfl) ⟨1830336, by rfl⟩ : syracuseStep 4880897 = 3660673) B3660673
theorem B3253931 : Blo 2167435 3253931 := bstep (se 1 (by rfl) ⟨2440448, by rfl⟩ : syracuseStep 3253931 = 4880897) B4880897
theorem B2169287 : Blo 2167435 2169287 := bstep (se 1 (by rfl) ⟨1626965, by rfl⟩ : syracuseStep 2169287 = 3253931) B3253931
theorem B2440453 : Blo 2167435 2440453 := bbase (se 4 (by rfl) ⟨228792, by rfl⟩ : syracuseStep 2440453 = 457585) (by norm_num)
theorem B3253937 : Blo 2167435 3253937 := bstep (se 2 (by rfl) ⟨1220226, by rfl⟩ : syracuseStep 3253937 = 2440453) B2440453
theorem B2169291 : Blo 2167435 2169291 := bstep (se 1 (by rfl) ⟨1626968, by rfl⟩ : syracuseStep 2169291 = 3253937) B3253937
theorem B2316529 : Blo 2167435 2316529 := bbase (se 2 (by rfl) ⟨868698, by rfl⟩ : syracuseStep 2316529 = 1737397) (by norm_num)
theorem B3088705 : Blo 2167435 3088705 := bstep (se 2 (by rfl) ⟨1158264, by rfl⟩ : syracuseStep 3088705 = 2316529) B2316529
theorem B4118273 : Blo 2167435 4118273 := bstep (se 2 (by rfl) ⟨1544352, by rfl⟩ : syracuseStep 4118273 = 3088705) B3088705
theorem B2745515 : Blo 2167435 2745515 := bstep (se 1 (by rfl) ⟨2059136, by rfl⟩ : syracuseStep 2745515 = 4118273) B4118273
theorem B7321373 : Blo 2167435 7321373 := bstep (se 3 (by rfl) ⟨1372757, by rfl⟩ : syracuseStep 7321373 = 2745515) B2745515
theorem B4880915 : Blo 2167435 4880915 := bstep (se 1 (by rfl) ⟨3660686, by rfl⟩ : syracuseStep 4880915 = 7321373) B7321373
theorem B3253943 : Blo 2167435 3253943 := bstep (se 1 (by rfl) ⟨2440457, by rfl⟩ : syracuseStep 3253943 = 4880915) B4880915
theorem B2169295 : Blo 2167435 2169295 := bstep (se 1 (by rfl) ⟨1626971, by rfl⟩ : syracuseStep 2169295 = 3253943) B3253943
theorem B3253949 : Blo 2167435 3253949 := bbase (se 3 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 3253949 = 1220231) (by norm_num)
theorem B2169299 : Blo 2167435 2169299 := bstep (se 1 (by rfl) ⟨1626974, by rfl⟩ : syracuseStep 2169299 = 3253949) B3253949
theorem B4880933 : Blo 2167435 4880933 := bbase (se 4 (by rfl) ⟨457587, by rfl⟩ : syracuseStep 4880933 = 915175) (by norm_num)
theorem B3253955 : Blo 2167435 3253955 := bstep (se 1 (by rfl) ⟨2440466, by rfl⟩ : syracuseStep 3253955 = 4880933) B4880933
theorem B2169303 : Blo 2167435 2169303 := bstep (se 1 (by rfl) ⟨1626977, by rfl⟩ : syracuseStep 2169303 = 3253955) B3253955
theorem B5491061 : Blo 2167435 5491061 := bbase (se 5 (by rfl) ⟨257393, by rfl⟩ : syracuseStep 5491061 = 514787) (by norm_num)
theorem B3660707 : Blo 2167435 3660707 := bstep (se 1 (by rfl) ⟨2745530, by rfl⟩ : syracuseStep 3660707 = 5491061) B5491061
theorem B2440471 : Blo 2167435 2440471 := bstep (se 1 (by rfl) ⟨1830353, by rfl⟩ : syracuseStep 2440471 = 3660707) B3660707
theorem B3253961 : Blo 2167435 3253961 := bstep (se 2 (by rfl) ⟨1220235, by rfl⟩ : syracuseStep 3253961 = 2440471) B2440471
theorem B2169307 : Blo 2167435 2169307 := bstep (se 1 (by rfl) ⟨1626980, by rfl⟩ : syracuseStep 2169307 = 3253961) B3253961
theorem B2198909 : Blo 2167435 2198909 := bbase (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) (by norm_num)
theorem B5863757 : Blo 2167435 5863757 := bstep (se 3 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 5863757 = 2198909) B2198909
theorem B15636685 : Blo 2167435 15636685 := bstep (se 3 (by rfl) ⟨2931878, by rfl⟩ : syracuseStep 15636685 = 5863757) B5863757
theorem B20848913 : Blo 2167435 20848913 := bstep (se 2 (by rfl) ⟨7818342, by rfl⟩ : syracuseStep 20848913 = 15636685) B15636685
theorem B13899275 : Blo 2167435 13899275 := bstep (se 1 (by rfl) ⟨10424456, by rfl⟩ : syracuseStep 13899275 = 20848913) B20848913
theorem B9266183 : Blo 2167435 9266183 := bstep (se 1 (by rfl) ⟨6949637, by rfl⟩ : syracuseStep 9266183 = 13899275) B13899275
theorem B6177455 : Blo 2167435 6177455 := bstep (se 1 (by rfl) ⟨4633091, by rfl⟩ : syracuseStep 6177455 = 9266183) B9266183
theorem B4118303 : Blo 2167435 4118303 := bstep (se 1 (by rfl) ⟨3088727, by rfl⟩ : syracuseStep 4118303 = 6177455) B6177455
theorem B10982141 : Blo 2167435 10982141 := bstep (se 3 (by rfl) ⟨2059151, by rfl⟩ : syracuseStep 10982141 = 4118303) B4118303
theorem B7321427 : Blo 2167435 7321427 := bstep (se 1 (by rfl) ⟨5491070, by rfl⟩ : syracuseStep 7321427 = 10982141) B10982141
theorem B4880951 : Blo 2167435 4880951 := bstep (se 1 (by rfl) ⟨3660713, by rfl⟩ : syracuseStep 4880951 = 7321427) B7321427
theorem B3253967 : Blo 2167435 3253967 := bstep (se 1 (by rfl) ⟨2440475, by rfl⟩ : syracuseStep 3253967 = 4880951) B4880951
theorem B2169311 : Blo 2167435 2169311 := bstep (se 1 (by rfl) ⟨1626983, by rfl⟩ : syracuseStep 2169311 = 3253967) B3253967
theorem B3253973 : Blo 2167435 3253973 := bbase (se 7 (by rfl) ⟨38132, by rfl⟩ : syracuseStep 3253973 = 76265) (by norm_num)
theorem B2169315 : Blo 2167435 2169315 := bstep (se 1 (by rfl) ⟨1626986, by rfl⟩ : syracuseStep 2169315 = 3253973) B3253973
theorem B4633109 : Blo 2167435 4633109 := bbase (se 6 (by rfl) ⟨108588, by rfl⟩ : syracuseStep 4633109 = 217177) (by norm_num)
theorem B3088739 : Blo 2167435 3088739 := bstep (se 1 (by rfl) ⟨2316554, by rfl⟩ : syracuseStep 3088739 = 4633109) B4633109
theorem B8236637 : Blo 2167435 8236637 := bstep (se 3 (by rfl) ⟨1544369, by rfl⟩ : syracuseStep 8236637 = 3088739) B3088739
theorem B5491091 : Blo 2167435 5491091 := bstep (se 1 (by rfl) ⟨4118318, by rfl⟩ : syracuseStep 5491091 = 8236637) B8236637
theorem B3660727 : Blo 2167435 3660727 := bstep (se 1 (by rfl) ⟨2745545, by rfl⟩ : syracuseStep 3660727 = 5491091) B5491091
theorem B4880969 : Blo 2167435 4880969 := bstep (se 2 (by rfl) ⟨1830363, by rfl⟩ : syracuseStep 4880969 = 3660727) B3660727
theorem B3253979 : Blo 2167435 3253979 := bstep (se 1 (by rfl) ⟨2440484, by rfl⟩ : syracuseStep 3253979 = 4880969) B4880969
theorem B2169319 : Blo 2167435 2169319 := bstep (se 1 (by rfl) ⟨1626989, by rfl⟩ : syracuseStep 2169319 = 3253979) B3253979
theorem B2440489 : Blo 2167435 2440489 := bbase (se 2 (by rfl) ⟨915183, by rfl⟩ : syracuseStep 2440489 = 1830367) (by norm_num)
theorem B3253985 : Blo 2167435 3253985 := bstep (se 2 (by rfl) ⟨1220244, by rfl⟩ : syracuseStep 3253985 = 2440489) B2440489
theorem B2169323 : Blo 2167435 2169323 := bstep (se 1 (by rfl) ⟨1626992, by rfl⟩ : syracuseStep 2169323 = 3253985) B3253985
theorem B10424533 : Blo 2167435 10424533 := bbase (se 7 (by rfl) ⟨122162, by rfl⟩ : syracuseStep 10424533 = 244325) (by norm_num)
theorem B13899377 : Blo 2167435 13899377 := bstep (se 2 (by rfl) ⟨5212266, by rfl⟩ : syracuseStep 13899377 = 10424533) B10424533
theorem B9266251 : Blo 2167435 9266251 := bstep (se 1 (by rfl) ⟨6949688, by rfl⟩ : syracuseStep 9266251 = 13899377) B13899377
theorem B12355001 : Blo 2167435 12355001 := bstep (se 2 (by rfl) ⟨4633125, by rfl⟩ : syracuseStep 12355001 = 9266251) B9266251
theorem B8236667 : Blo 2167435 8236667 := bstep (se 1 (by rfl) ⟨6177500, by rfl⟩ : syracuseStep 8236667 = 12355001) B12355001
theorem B5491111 : Blo 2167435 5491111 := bstep (se 1 (by rfl) ⟨4118333, by rfl⟩ : syracuseStep 5491111 = 8236667) B8236667
theorem B7321481 : Blo 2167435 7321481 := bstep (se 2 (by rfl) ⟨2745555, by rfl⟩ : syracuseStep 7321481 = 5491111) B5491111
theorem B4880987 : Blo 2167435 4880987 := bstep (se 1 (by rfl) ⟨3660740, by rfl⟩ : syracuseStep 4880987 = 7321481) B7321481
theorem B3253991 : Blo 2167435 3253991 := bstep (se 1 (by rfl) ⟨2440493, by rfl⟩ : syracuseStep 3253991 = 4880987) B4880987
theorem B2169327 : Blo 2167435 2169327 := bstep (se 1 (by rfl) ⟨1626995, by rfl⟩ : syracuseStep 2169327 = 3253991) B3253991
theorem B3253997 : Blo 2167435 3253997 := bbase (se 3 (by rfl) ⟨610124, by rfl⟩ : syracuseStep 3253997 = 1220249) (by norm_num)
theorem B2169331 : Blo 2167435 2169331 := bstep (se 1 (by rfl) ⟨1626998, by rfl⟩ : syracuseStep 2169331 = 3253997) B3253997
theorem B4881005 : Blo 2167435 4881005 := bbase (se 3 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 4881005 = 1830377) (by norm_num)
theorem B3254003 : Blo 2167435 3254003 := bstep (se 1 (by rfl) ⟨2440502, by rfl⟩ : syracuseStep 3254003 = 4881005) B4881005
theorem B2169335 : Blo 2167435 2169335 := bstep (se 1 (by rfl) ⟨1627001, by rfl⟩ : syracuseStep 2169335 = 3254003) B3254003
theorem B4118357 : Blo 2167435 4118357 := bbase (se 9 (by rfl) ⟨12065, by rfl⟩ : syracuseStep 4118357 = 24131) (by norm_num)
theorem B2745571 : Blo 2167435 2745571 := bstep (se 1 (by rfl) ⟨2059178, by rfl⟩ : syracuseStep 2745571 = 4118357) B4118357
theorem B3660761 : Blo 2167435 3660761 := bstep (se 2 (by rfl) ⟨1372785, by rfl⟩ : syracuseStep 3660761 = 2745571) B2745571
theorem B2440507 : Blo 2167435 2440507 := bstep (se 1 (by rfl) ⟨1830380, by rfl⟩ : syracuseStep 2440507 = 3660761) B3660761
theorem B3254009 : Blo 2167435 3254009 := bstep (se 2 (by rfl) ⟨1220253, by rfl⟩ : syracuseStep 3254009 = 2440507) B2440507
theorem B2169339 : Blo 2167435 2169339 := bstep (se 1 (by rfl) ⟨1627004, by rfl⟩ : syracuseStep 2169339 = 3254009) B3254009
theorem B2198941 : Blo 2167435 2198941 := bbase (se 3 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 2198941 = 824603) (by norm_num)
theorem B11727685 : Blo 2167435 11727685 := bstep (se 4 (by rfl) ⟨1099470, by rfl⟩ : syracuseStep 11727685 = 2198941) B2198941
theorem B62547653 : Blo 2167435 62547653 := bstep (se 4 (by rfl) ⟨5863842, by rfl⟩ : syracuseStep 62547653 = 11727685) B11727685
theorem B41698435 : Blo 2167435 41698435 := bstep (se 1 (by rfl) ⟨31273826, by rfl⟩ : syracuseStep 41698435 = 62547653) B62547653
theorem B55597913 : Blo 2167435 55597913 := bstep (se 2 (by rfl) ⟨20849217, by rfl⟩ : syracuseStep 55597913 = 41698435) B41698435
theorem B37065275 : Blo 2167435 37065275 := bstep (se 1 (by rfl) ⟨27798956, by rfl⟩ : syracuseStep 37065275 = 55597913) B55597913
theorem B24710183 : Blo 2167435 24710183 := bstep (se 1 (by rfl) ⟨18532637, by rfl⟩ : syracuseStep 24710183 = 37065275) B37065275
theorem B16473455 : Blo 2167435 16473455 := bstep (se 1 (by rfl) ⟨12355091, by rfl⟩ : syracuseStep 16473455 = 24710183) B24710183
theorem B10982303 : Blo 2167435 10982303 := bstep (se 1 (by rfl) ⟨8236727, by rfl⟩ : syracuseStep 10982303 = 16473455) B16473455
theorem B7321535 : Blo 2167435 7321535 := bstep (se 1 (by rfl) ⟨5491151, by rfl⟩ : syracuseStep 7321535 = 10982303) B10982303
theorem B4881023 : Blo 2167435 4881023 := bstep (se 1 (by rfl) ⟨3660767, by rfl⟩ : syracuseStep 4881023 = 7321535) B7321535
theorem B3254015 : Blo 2167435 3254015 := bstep (se 1 (by rfl) ⟨2440511, by rfl⟩ : syracuseStep 3254015 = 4881023) B4881023
theorem B2169343 : Blo 2167435 2169343 := bstep (se 1 (by rfl) ⟨1627007, by rfl⟩ : syracuseStep 2169343 = 3254015) B3254015
theorem B3254021 : Blo 2167435 3254021 := bbase (se 4 (by rfl) ⟨305064, by rfl⟩ : syracuseStep 3254021 = 610129) (by norm_num)
theorem B2169347 : Blo 2167435 2169347 := bstep (se 1 (by rfl) ⟨1627010, by rfl⟩ : syracuseStep 2169347 = 3254021) B3254021
theorem B3660781 : Blo 2167435 3660781 := bbase (se 3 (by rfl) ⟨686396, by rfl⟩ : syracuseStep 3660781 = 1372793) (by norm_num)
theorem B4881041 : Blo 2167435 4881041 := bstep (se 2 (by rfl) ⟨1830390, by rfl⟩ : syracuseStep 4881041 = 3660781) B3660781
theorem B3254027 : Blo 2167435 3254027 := bstep (se 1 (by rfl) ⟨2440520, by rfl⟩ : syracuseStep 3254027 = 4881041) B4881041
theorem B2169351 : Blo 2167435 2169351 := bstep (se 1 (by rfl) ⟨1627013, by rfl⟩ : syracuseStep 2169351 = 3254027) B3254027
theorem B2440525 : Blo 2167435 2440525 := bbase (se 3 (by rfl) ⟨457598, by rfl⟩ : syracuseStep 2440525 = 915197) (by norm_num)
theorem B3254033 : Blo 2167435 3254033 := bstep (se 2 (by rfl) ⟨1220262, by rfl⟩ : syracuseStep 3254033 = 2440525) B2440525
theorem B2169355 : Blo 2167435 2169355 := bstep (se 1 (by rfl) ⟨1627016, by rfl⟩ : syracuseStep 2169355 = 3254033) B3254033
theorem B7321589 : Blo 2167435 7321589 := bbase (se 5 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 7321589 = 686399) (by norm_num)
theorem B4881059 : Blo 2167435 4881059 := bstep (se 1 (by rfl) ⟨3660794, by rfl⟩ : syracuseStep 4881059 = 7321589) B7321589
theorem B3254039 : Blo 2167435 3254039 := bstep (se 1 (by rfl) ⟨2440529, by rfl⟩ : syracuseStep 3254039 = 4881059) B4881059
theorem B2169359 : Blo 2167435 2169359 := bstep (se 1 (by rfl) ⟨1627019, by rfl⟩ : syracuseStep 2169359 = 3254039) B3254039
theorem B3254045 : Blo 2167435 3254045 := bbase (se 3 (by rfl) ⟨610133, by rfl⟩ : syracuseStep 3254045 = 1220267) (by norm_num)
theorem B2169363 : Blo 2167435 2169363 := bstep (se 1 (by rfl) ⟨1627022, by rfl⟩ : syracuseStep 2169363 = 3254045) B3254045
theorem B4881077 : Blo 2167435 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B3254051 : Blo 2167435 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B2169367 : Blo 2167435 2169367 := bstep (se 1 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 2169367 = 3254051) B3254051
theorem B12355253 : Blo 2167435 12355253 := bbase (se 5 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 12355253 = 1158305) (by norm_num)
theorem B8236835 : Blo 2167435 8236835 := bstep (se 1 (by rfl) ⟨6177626, by rfl⟩ : syracuseStep 8236835 = 12355253) B12355253
theorem B5491223 : Blo 2167435 5491223 := bstep (se 1 (by rfl) ⟨4118417, by rfl⟩ : syracuseStep 5491223 = 8236835) B8236835
theorem B3660815 : Blo 2167435 3660815 := bstep (se 1 (by rfl) ⟨2745611, by rfl⟩ : syracuseStep 3660815 = 5491223) B5491223
theorem B2440543 : Blo 2167435 2440543 := bstep (se 1 (by rfl) ⟨1830407, by rfl⟩ : syracuseStep 2440543 = 3660815) B3660815
theorem B3254057 : Blo 2167435 3254057 := bstep (se 2 (by rfl) ⟨1220271, by rfl⟩ : syracuseStep 3254057 = 2440543) B2440543
theorem B2169371 : Blo 2167435 2169371 := bstep (se 1 (by rfl) ⟨1627028, by rfl⟩ : syracuseStep 2169371 = 3254057) B3254057
theorem B6177637 : Blo 2167435 6177637 := bbase (se 4 (by rfl) ⟨579153, by rfl⟩ : syracuseStep 6177637 = 1158307) (by norm_num)
theorem B8236849 : Blo 2167435 8236849 := bstep (se 2 (by rfl) ⟨3088818, by rfl⟩ : syracuseStep 8236849 = 6177637) B6177637
theorem B10982465 : Blo 2167435 10982465 := bstep (se 2 (by rfl) ⟨4118424, by rfl⟩ : syracuseStep 10982465 = 8236849) B8236849
theorem B7321643 : Blo 2167435 7321643 := bstep (se 1 (by rfl) ⟨5491232, by rfl⟩ : syracuseStep 7321643 = 10982465) B10982465
theorem B4881095 : Blo 2167435 4881095 := bstep (se 1 (by rfl) ⟨3660821, by rfl⟩ : syracuseStep 4881095 = 7321643) B7321643
theorem B3254063 : Blo 2167435 3254063 := bstep (se 1 (by rfl) ⟨2440547, by rfl⟩ : syracuseStep 3254063 = 4881095) B4881095
theorem B2169375 : Blo 2167435 2169375 := bstep (se 1 (by rfl) ⟨1627031, by rfl⟩ : syracuseStep 2169375 = 3254063) B3254063
theorem B3254069 : Blo 2167435 3254069 := bbase (se 5 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 3254069 = 305069) (by norm_num)
theorem B2169379 : Blo 2167435 2169379 := bstep (se 1 (by rfl) ⟨1627034, by rfl⟩ : syracuseStep 2169379 = 3254069) B3254069
theorem B5491253 : Blo 2167435 5491253 := bbase (se 5 (by rfl) ⟨257402, by rfl⟩ : syracuseStep 5491253 = 514805) (by norm_num)
theorem B3660835 : Blo 2167435 3660835 := bstep (se 1 (by rfl) ⟨2745626, by rfl⟩ : syracuseStep 3660835 = 5491253) B5491253
theorem B4881113 : Blo 2167435 4881113 := bstep (se 2 (by rfl) ⟨1830417, by rfl⟩ : syracuseStep 4881113 = 3660835) B3660835
theorem B3254075 : Blo 2167435 3254075 := bstep (se 1 (by rfl) ⟨2440556, by rfl⟩ : syracuseStep 3254075 = 4881113) B4881113
theorem B2169383 : Blo 2167435 2169383 := bstep (se 1 (by rfl) ⟨1627037, by rfl⟩ : syracuseStep 2169383 = 3254075) B3254075
theorem B2440561 : Blo 2167435 2440561 := bbase (se 2 (by rfl) ⟨915210, by rfl⟩ : syracuseStep 2440561 = 1830421) (by norm_num)
theorem B3254081 : Blo 2167435 3254081 := bstep (se 2 (by rfl) ⟨1220280, by rfl⟩ : syracuseStep 3254081 = 2440561) B2440561
theorem B2169387 : Blo 2167435 2169387 := bstep (se 1 (by rfl) ⟨1627040, by rfl⟩ : syracuseStep 2169387 = 3254081) B3254081
theorem B5212421 : Blo 2167435 5212421 := bbase (se 4 (by rfl) ⟨488664, by rfl⟩ : syracuseStep 5212421 = 977329) (by norm_num)
theorem B3474947 : Blo 2167435 3474947 := bstep (se 1 (by rfl) ⟨2606210, by rfl⟩ : syracuseStep 3474947 = 5212421) B5212421
theorem B9266525 : Blo 2167435 9266525 := bstep (se 3 (by rfl) ⟨1737473, by rfl⟩ : syracuseStep 9266525 = 3474947) B3474947
theorem B6177683 : Blo 2167435 6177683 := bstep (se 1 (by rfl) ⟨4633262, by rfl⟩ : syracuseStep 6177683 = 9266525) B9266525
theorem B4118455 : Blo 2167435 4118455 := bstep (se 1 (by rfl) ⟨3088841, by rfl⟩ : syracuseStep 4118455 = 6177683) B6177683
theorem B5491273 : Blo 2167435 5491273 := bstep (se 2 (by rfl) ⟨2059227, by rfl⟩ : syracuseStep 5491273 = 4118455) B4118455
theorem B7321697 : Blo 2167435 7321697 := bstep (se 2 (by rfl) ⟨2745636, by rfl⟩ : syracuseStep 7321697 = 5491273) B5491273
theorem B4881131 : Blo 2167435 4881131 := bstep (se 1 (by rfl) ⟨3660848, by rfl⟩ : syracuseStep 4881131 = 7321697) B7321697
theorem B3254087 : Blo 2167435 3254087 := bstep (se 1 (by rfl) ⟨2440565, by rfl⟩ : syracuseStep 3254087 = 4881131) B4881131
theorem B2169391 : Blo 2167435 2169391 := bstep (se 1 (by rfl) ⟨1627043, by rfl⟩ : syracuseStep 2169391 = 3254087) B3254087
theorem B3254093 : Blo 2167435 3254093 := bbase (se 3 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 3254093 = 1220285) (by norm_num)
theorem B2169395 : Blo 2167435 2169395 := bstep (se 1 (by rfl) ⟨1627046, by rfl⟩ : syracuseStep 2169395 = 3254093) B3254093
theorem B4881149 : Blo 2167435 4881149 := bbase (se 3 (by rfl) ⟨915215, by rfl⟩ : syracuseStep 4881149 = 1830431) (by norm_num)
theorem B3254099 : Blo 2167435 3254099 := bstep (se 1 (by rfl) ⟨2440574, by rfl⟩ : syracuseStep 3254099 = 4881149) B4881149
theorem B2169399 : Blo 2167435 2169399 := bstep (se 1 (by rfl) ⟨1627049, by rfl⟩ : syracuseStep 2169399 = 3254099) B3254099
theorem B3660869 : Blo 2167435 3660869 := bbase (se 4 (by rfl) ⟨343206, by rfl⟩ : syracuseStep 3660869 = 686413) (by norm_num)
theorem B2440579 : Blo 2167435 2440579 := bstep (se 1 (by rfl) ⟨1830434, by rfl⟩ : syracuseStep 2440579 = 3660869) B3660869
theorem B3254105 : Blo 2167435 3254105 := bstep (se 2 (by rfl) ⟨1220289, by rfl⟩ : syracuseStep 3254105 = 2440579) B2440579
theorem B2169403 : Blo 2167435 2169403 := bstep (se 1 (by rfl) ⟨1627052, by rfl⟩ : syracuseStep 2169403 = 3254105) B3254105
theorem B16473941 : Blo 2167435 16473941 := bbase (se 9 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 16473941 = 96527) (by norm_num)
theorem B10982627 : Blo 2167435 10982627 := bstep (se 1 (by rfl) ⟨8236970, by rfl⟩ : syracuseStep 10982627 = 16473941) B16473941
theorem B7321751 : Blo 2167435 7321751 := bstep (se 1 (by rfl) ⟨5491313, by rfl⟩ : syracuseStep 7321751 = 10982627) B10982627
theorem B4881167 : Blo 2167435 4881167 := bstep (se 1 (by rfl) ⟨3660875, by rfl⟩ : syracuseStep 4881167 = 7321751) B7321751
theorem B3254111 : Blo 2167435 3254111 := bstep (se 1 (by rfl) ⟨2440583, by rfl⟩ : syracuseStep 3254111 = 4881167) B4881167
theorem B2169407 : Blo 2167435 2169407 := bstep (se 1 (by rfl) ⟨1627055, by rfl⟩ : syracuseStep 2169407 = 3254111) B3254111
theorem B3254117 : Blo 2167435 3254117 := bbase (se 4 (by rfl) ⟨305073, by rfl⟩ : syracuseStep 3254117 = 610147) (by norm_num)
theorem B2169411 : Blo 2167435 2169411 := bstep (se 1 (by rfl) ⟨1627058, by rfl⟩ : syracuseStep 2169411 = 3254117) B3254117
theorem B4118501 : Blo 2167435 4118501 := bbase (se 4 (by rfl) ⟨386109, by rfl⟩ : syracuseStep 4118501 = 772219) (by norm_num)
theorem B2745667 : Blo 2167435 2745667 := bstep (se 1 (by rfl) ⟨2059250, by rfl⟩ : syracuseStep 2745667 = 4118501) B4118501
theorem B3660889 : Blo 2167435 3660889 := bstep (se 2 (by rfl) ⟨1372833, by rfl⟩ : syracuseStep 3660889 = 2745667) B2745667
theorem B4881185 : Blo 2167435 4881185 := bstep (se 2 (by rfl) ⟨1830444, by rfl⟩ : syracuseStep 4881185 = 3660889) B3660889
theorem B3254123 : Blo 2167435 3254123 := bstep (se 1 (by rfl) ⟨2440592, by rfl⟩ : syracuseStep 3254123 = 4881185) B4881185
theorem B2169415 : Blo 2167435 2169415 := bstep (se 1 (by rfl) ⟨1627061, by rfl⟩ : syracuseStep 2169415 = 3254123) B3254123
theorem B2440597 : Blo 2167435 2440597 := bbase (se 6 (by rfl) ⟨57201, by rfl⟩ : syracuseStep 2440597 = 114403) (by norm_num)
theorem B3254129 : Blo 2167435 3254129 := bstep (se 2 (by rfl) ⟨1220298, by rfl⟩ : syracuseStep 3254129 = 2440597) B2440597
theorem B2169419 : Blo 2167435 2169419 := bstep (se 1 (by rfl) ⟨1627064, by rfl⟩ : syracuseStep 2169419 = 3254129) B3254129
theorem B2745677 : Blo 2167435 2745677 := bbase (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) (by norm_num)
theorem B7321805 : Blo 2167435 7321805 := bstep (se 3 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 7321805 = 2745677) B2745677
theorem B4881203 : Blo 2167435 4881203 := bstep (se 1 (by rfl) ⟨3660902, by rfl⟩ : syracuseStep 4881203 = 7321805) B7321805
theorem B3254135 : Blo 2167435 3254135 := bstep (se 1 (by rfl) ⟨2440601, by rfl⟩ : syracuseStep 3254135 = 4881203) B4881203
theorem B2169423 : Blo 2167435 2169423 := bstep (se 1 (by rfl) ⟨1627067, by rfl⟩ : syracuseStep 2169423 = 3254135) B3254135
theorem B3254141 : Blo 2167435 3254141 := bbase (se 3 (by rfl) ⟨610151, by rfl⟩ : syracuseStep 3254141 = 1220303) (by norm_num)
theorem B2169427 : Blo 2167435 2169427 := bstep (se 1 (by rfl) ⟨1627070, by rfl⟩ : syracuseStep 2169427 = 3254141) B3254141
theorem B4881221 : Blo 2167435 4881221 := bbase (se 4 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 4881221 = 915229) (by norm_num)
theorem B3254147 : Blo 2167435 3254147 := bstep (se 1 (by rfl) ⟨2440610, by rfl⟩ : syracuseStep 3254147 = 4881221) B4881221
theorem B2169431 : Blo 2167435 2169431 := bstep (se 1 (by rfl) ⟨1627073, by rfl⟩ : syracuseStep 2169431 = 3254147) B3254147
theorem B4633357 : Blo 2167435 4633357 := bbase (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) (by norm_num)
theorem B6177809 : Blo 2167435 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B4118539 : Blo 2167435 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B5491385 : Blo 2167435 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B3660923 : Blo 2167435 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B2440615 : Blo 2167435 2440615 := bstep (se 1 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 2440615 = 3660923) B3660923
theorem B3254153 : Blo 2167435 3254153 := bstep (se 2 (by rfl) ⟨1220307, by rfl⟩ : syracuseStep 3254153 = 2440615) B2440615
theorem B2169435 : Blo 2167435 2169435 := bstep (se 1 (by rfl) ⟨1627076, by rfl⟩ : syracuseStep 2169435 = 3254153) B3254153
theorem C0 (j : ℕ) (h1 : 541858 ≤ j) (h2 : j ≤ 542358) : Blo 2167435 (4 * j + 3) := by
  interval_cases j
  · exact B2167435
  · exact B2167439
  · exact B2167443
  · exact B2167447
  · exact B2167451
  · exact B2167455
  · exact B2167459
  · exact B2167463
  · exact B2167467
  · exact B2167471
  · exact B2167475
  · exact B2167479
  · exact B2167483
  · exact B2167487
  · exact B2167491
  · exact B2167495
  · exact B2167499
  · exact B2167503
  · exact B2167507
  · exact B2167511
  · exact B2167515
  · exact B2167519
  · exact B2167523
  · exact B2167527
  · exact B2167531
  · exact B2167535
  · exact B2167539
  · exact B2167543
  · exact B2167547
  · exact B2167551
  · exact B2167555
  · exact B2167559
  · exact B2167563
  · exact B2167567
  · exact B2167571
  · exact B2167575
  · exact B2167579
  · exact B2167583
  · exact B2167587
  · exact B2167591
  · exact B2167595
  · exact B2167599
  · exact B2167603
  · exact B2167607
  · exact B2167611
  · exact B2167615
  · exact B2167619
  · exact B2167623
  · exact B2167627
  · exact B2167631
  · exact B2167635
  · exact B2167639
  · exact B2167643
  · exact B2167647
  · exact B2167651
  · exact B2167655
  · exact B2167659
  · exact B2167663
  · exact B2167667
  · exact B2167671
  · exact B2167675
  · exact B2167679
  · exact B2167683
  · exact B2167687
  · exact B2167691
  · exact B2167695
  · exact B2167699
  · exact B2167703
  · exact B2167707
  · exact B2167711
  · exact B2167715
  · exact B2167719
  · exact B2167723
  · exact B2167727
  · exact B2167731
  · exact B2167735
  · exact B2167739
  · exact B2167743
  · exact B2167747
  · exact B2167751
  · exact B2167755
  · exact B2167759
  · exact B2167763
  · exact B2167767
  · exact B2167771
  · exact B2167775
  · exact B2167779
  · exact B2167783
  · exact B2167787
  · exact B2167791
  · exact B2167795
  · exact B2167799
  · exact B2167803
  · exact B2167807
  · exact B2167811
  · exact B2167815
  · exact B2167819
  · exact B2167823
  · exact B2167827
  · exact B2167831
  · exact B2167835
  · exact B2167839
  · exact B2167843
  · exact B2167847
  · exact B2167851
  · exact B2167855
  · exact B2167859
  · exact B2167863
  · exact B2167867
  · exact B2167871
  · exact B2167875
  · exact B2167879
  · exact B2167883
  · exact B2167887
  · exact B2167891
  · exact B2167895
  · exact B2167899
  · exact B2167903
  · exact B2167907
  · exact B2167911
  · exact B2167915
  · exact B2167919
  · exact B2167923
  · exact B2167927
  · exact B2167931
  · exact B2167935
  · exact B2167939
  · exact B2167943
  · exact B2167947
  · exact B2167951
  · exact B2167955
  · exact B2167959
  · exact B2167963
  · exact B2167967
  · exact B2167971
  · exact B2167975
  · exact B2167979
  · exact B2167983
  · exact B2167987
  · exact B2167991
  · exact B2167995
  · exact B2167999
  · exact B2168003
  · exact B2168007
  · exact B2168011
  · exact B2168015
  · exact B2168019
  · exact B2168023
  · exact B2168027
  · exact B2168031
  · exact B2168035
  · exact B2168039
  · exact B2168043
  · exact B2168047
  · exact B2168051
  · exact B2168055
  · exact B2168059
  · exact B2168063
  · exact B2168067
  · exact B2168071
  · exact B2168075
  · exact B2168079
  · exact B2168083
  · exact B2168087
  · exact B2168091
  · exact B2168095
  · exact B2168099
  · exact B2168103
  · exact B2168107
  · exact B2168111
  · exact B2168115
  · exact B2168119
  · exact B2168123
  · exact B2168127
  · exact B2168131
  · exact B2168135
  · exact B2168139
  · exact B2168143
  · exact B2168147
  · exact B2168151
  · exact B2168155
  · exact B2168159
  · exact B2168163
  · exact B2168167
  · exact B2168171
  · exact B2168175
  · exact B2168179
  · exact B2168183
  · exact B2168187
  · exact B2168191
  · exact B2168195
  · exact B2168199
  · exact B2168203
  · exact B2168207
  · exact B2168211
  · exact B2168215
  · exact B2168219
  · exact B2168223
  · exact B2168227
  · exact B2168231
  · exact B2168235
  · exact B2168239
  · exact B2168243
  · exact B2168247
  · exact B2168251
  · exact B2168255
  · exact B2168259
  · exact B2168263
  · exact B2168267
  · exact B2168271
  · exact B2168275
  · exact B2168279
  · exact B2168283
  · exact B2168287
  · exact B2168291
  · exact B2168295
  · exact B2168299
  · exact B2168303
  · exact B2168307
  · exact B2168311
  · exact B2168315
  · exact B2168319
  · exact B2168323
  · exact B2168327
  · exact B2168331
  · exact B2168335
  · exact B2168339
  · exact B2168343
  · exact B2168347
  · exact B2168351
  · exact B2168355
  · exact B2168359
  · exact B2168363
  · exact B2168367
  · exact B2168371
  · exact B2168375
  · exact B2168379
  · exact B2168383
  · exact B2168387
  · exact B2168391
  · exact B2168395
  · exact B2168399
  · exact B2168403
  · exact B2168407
  · exact B2168411
  · exact B2168415
  · exact B2168419
  · exact B2168423
  · exact B2168427
  · exact B2168431
  · exact B2168435
  · exact B2168439
  · exact B2168443
  · exact B2168447
  · exact B2168451
  · exact B2168455
  · exact B2168459
  · exact B2168463
  · exact B2168467
  · exact B2168471
  · exact B2168475
  · exact B2168479
  · exact B2168483
  · exact B2168487
  · exact B2168491
  · exact B2168495
  · exact B2168499
  · exact B2168503
  · exact B2168507
  · exact B2168511
  · exact B2168515
  · exact B2168519
  · exact B2168523
  · exact B2168527
  · exact B2168531
  · exact B2168535
  · exact B2168539
  · exact B2168543
  · exact B2168547
  · exact B2168551
  · exact B2168555
  · exact B2168559
  · exact B2168563
  · exact B2168567
  · exact B2168571
  · exact B2168575
  · exact B2168579
  · exact B2168583
  · exact B2168587
  · exact B2168591
  · exact B2168595
  · exact B2168599
  · exact B2168603
  · exact B2168607
  · exact B2168611
  · exact B2168615
  · exact B2168619
  · exact B2168623
  · exact B2168627
  · exact B2168631
  · exact B2168635
  · exact B2168639
  · exact B2168643
  · exact B2168647
  · exact B2168651
  · exact B2168655
  · exact B2168659
  · exact B2168663
  · exact B2168667
  · exact B2168671
  · exact B2168675
  · exact B2168679
  · exact B2168683
  · exact B2168687
  · exact B2168691
  · exact B2168695
  · exact B2168699
  · exact B2168703
  · exact B2168707
  · exact B2168711
  · exact B2168715
  · exact B2168719
  · exact B2168723
  · exact B2168727
  · exact B2168731
  · exact B2168735
  · exact B2168739
  · exact B2168743
  · exact B2168747
  · exact B2168751
  · exact B2168755
  · exact B2168759
  · exact B2168763
  · exact B2168767
  · exact B2168771
  · exact B2168775
  · exact B2168779
  · exact B2168783
  · exact B2168787
  · exact B2168791
  · exact B2168795
  · exact B2168799
  · exact B2168803
  · exact B2168807
  · exact B2168811
  · exact B2168815
  · exact B2168819
  · exact B2168823
  · exact B2168827
  · exact B2168831
  · exact B2168835
  · exact B2168839
  · exact B2168843
  · exact B2168847
  · exact B2168851
  · exact B2168855
  · exact B2168859
  · exact B2168863
  · exact B2168867
  · exact B2168871
  · exact B2168875
  · exact B2168879
  · exact B2168883
  · exact B2168887
  · exact B2168891
  · exact B2168895
  · exact B2168899
  · exact B2168903
  · exact B2168907
  · exact B2168911
  · exact B2168915
  · exact B2168919
  · exact B2168923
  · exact B2168927
  · exact B2168931
  · exact B2168935
  · exact B2168939
  · exact B2168943
  · exact B2168947
  · exact B2168951
  · exact B2168955
  · exact B2168959
  · exact B2168963
  · exact B2168967
  · exact B2168971
  · exact B2168975
  · exact B2168979
  · exact B2168983
  · exact B2168987
  · exact B2168991
  · exact B2168995
  · exact B2168999
  · exact B2169003
  · exact B2169007
  · exact B2169011
  · exact B2169015
  · exact B2169019
  · exact B2169023
  · exact B2169027
  · exact B2169031
  · exact B2169035
  · exact B2169039
  · exact B2169043
  · exact B2169047
  · exact B2169051
  · exact B2169055
  · exact B2169059
  · exact B2169063
  · exact B2169067
  · exact B2169071
  · exact B2169075
  · exact B2169079
  · exact B2169083
  · exact B2169087
  · exact B2169091
  · exact B2169095
  · exact B2169099
  · exact B2169103
  · exact B2169107
  · exact B2169111
  · exact B2169115
  · exact B2169119
  · exact B2169123
  · exact B2169127
  · exact B2169131
  · exact B2169135
  · exact B2169139
  · exact B2169143
  · exact B2169147
  · exact B2169151
  · exact B2169155
  · exact B2169159
  · exact B2169163
  · exact B2169167
  · exact B2169171
  · exact B2169175
  · exact B2169179
  · exact B2169183
  · exact B2169187
  · exact B2169191
  · exact B2169195
  · exact B2169199
  · exact B2169203
  · exact B2169207
  · exact B2169211
  · exact B2169215
  · exact B2169219
  · exact B2169223
  · exact B2169227
  · exact B2169231
  · exact B2169235
  · exact B2169239
  · exact B2169243
  · exact B2169247
  · exact B2169251
  · exact B2169255
  · exact B2169259
  · exact B2169263
  · exact B2169267
  · exact B2169271
  · exact B2169275
  · exact B2169279
  · exact B2169283
  · exact B2169287
  · exact B2169291
  · exact B2169295
  · exact B2169299
  · exact B2169303
  · exact B2169307
  · exact B2169311
  · exact B2169315
  · exact B2169319
  · exact B2169323
  · exact B2169327
  · exact B2169331
  · exact B2169335
  · exact B2169339
  · exact B2169343
  · exact B2169347
  · exact B2169351
  · exact B2169355
  · exact B2169359
  · exact B2169363
  · exact B2169367
  · exact B2169371
  · exact B2169375
  · exact B2169379
  · exact B2169383
  · exact B2169387
  · exact B2169391
  · exact B2169395
  · exact B2169399
  · exact B2169403
  · exact B2169407
  · exact B2169411
  · exact B2169415
  · exact B2169419
  · exact B2169423
  · exact B2169427
  · exact B2169431
  · exact B2169435
theorem solution (m : ℕ) (hlo : 2167435 ≤ m) (hhi : m ≤ 2169435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 541858 ≤ j := by omega
    have hj2 : j ≤ 542358 := by omega
    have hb : Blo 2167435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
