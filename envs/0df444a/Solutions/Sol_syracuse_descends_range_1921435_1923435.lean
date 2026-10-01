-- Prove2me | solution 1 for syracuse_descends_range_1921435_1923435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:12.410496+00:00
-- url     : https://prove2.me/submissions/65cfc1ea-a055-40bd-9203-33f918a192ab

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

theorem B4103693 : Blo 1921435 4103693 := bbase (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) (by norm_num)
theorem B2735795 : Blo 1921435 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B7295453 : Blo 1921435 7295453 := bstep (se 3 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 7295453 = 2735795) B2735795
theorem B4863635 : Blo 1921435 4863635 := bstep (se 1 (by rfl) ⟨3647726, by rfl⟩ : syracuseStep 4863635 = 7295453) B7295453
theorem B3242423 : Blo 1921435 3242423 := bstep (se 1 (by rfl) ⟨2431817, by rfl⟩ : syracuseStep 3242423 = 4863635) B4863635
theorem B2161615 : Blo 1921435 2161615 := bstep (se 1 (by rfl) ⟨1621211, by rfl⟩ : syracuseStep 2161615 = 3242423) B3242423
theorem B2882153 : Blo 1921435 2882153 := bstep (se 2 (by rfl) ⟨1080807, by rfl⟩ : syracuseStep 2882153 = 2161615) B2161615
theorem B1921435 : Blo 1921435 1921435 := bstep (se 1 (by rfl) ⟨1441076, by rfl⟩ : syracuseStep 1921435 = 2882153) B2882153
theorem B23371861 : Blo 1921435 23371861 := bbase (se 8 (by rfl) ⟨136944, by rfl⟩ : syracuseStep 23371861 = 273889) (by norm_num)
theorem B31162481 : Blo 1921435 31162481 := bstep (se 2 (by rfl) ⟨11685930, by rfl⟩ : syracuseStep 31162481 = 23371861) B23371861
theorem B20774987 : Blo 1921435 20774987 := bstep (se 1 (by rfl) ⟨15581240, by rfl⟩ : syracuseStep 20774987 = 31162481) B31162481
theorem B13849991 : Blo 1921435 13849991 := bstep (se 1 (by rfl) ⟨10387493, by rfl⟩ : syracuseStep 13849991 = 20774987) B20774987
theorem B9233327 : Blo 1921435 9233327 := bstep (se 1 (by rfl) ⟨6924995, by rfl⟩ : syracuseStep 9233327 = 13849991) B13849991
theorem B6155551 : Blo 1921435 6155551 := bstep (se 1 (by rfl) ⟨4616663, by rfl⟩ : syracuseStep 6155551 = 9233327) B9233327
theorem B8207401 : Blo 1921435 8207401 := bstep (se 2 (by rfl) ⟨3077775, by rfl⟩ : syracuseStep 8207401 = 6155551) B6155551
theorem B10943201 : Blo 1921435 10943201 := bstep (se 2 (by rfl) ⟨4103700, by rfl⟩ : syracuseStep 10943201 = 8207401) B8207401
theorem B7295467 : Blo 1921435 7295467 := bstep (se 1 (by rfl) ⟨5471600, by rfl⟩ : syracuseStep 7295467 = 10943201) B10943201
theorem B9727289 : Blo 1921435 9727289 := bstep (se 2 (by rfl) ⟨3647733, by rfl⟩ : syracuseStep 9727289 = 7295467) B7295467
theorem B6484859 : Blo 1921435 6484859 := bstep (se 1 (by rfl) ⟨4863644, by rfl⟩ : syracuseStep 6484859 = 9727289) B9727289
theorem B4323239 : Blo 1921435 4323239 := bstep (se 1 (by rfl) ⟨3242429, by rfl⟩ : syracuseStep 4323239 = 6484859) B6484859
theorem B2882159 : Blo 1921435 2882159 := bstep (se 1 (by rfl) ⟨2161619, by rfl⟩ : syracuseStep 2882159 = 4323239) B4323239
theorem B1921439 : Blo 1921435 1921439 := bstep (se 1 (by rfl) ⟨1441079, by rfl⟩ : syracuseStep 1921439 = 2882159) B2882159
theorem B2882165 : Blo 1921435 2882165 := bbase (se 5 (by rfl) ⟨135101, by rfl⟩ : syracuseStep 2882165 = 270203) (by norm_num)
theorem B1921443 : Blo 1921435 1921443 := bstep (se 1 (by rfl) ⟨1441082, by rfl⟩ : syracuseStep 1921443 = 2882165) B2882165
theorem B3647749 : Blo 1921435 3647749 := bbase (se 4 (by rfl) ⟨341976, by rfl⟩ : syracuseStep 3647749 = 683953) (by norm_num)
theorem B4863665 : Blo 1921435 4863665 := bstep (se 2 (by rfl) ⟨1823874, by rfl⟩ : syracuseStep 4863665 = 3647749) B3647749
theorem B3242443 : Blo 1921435 3242443 := bstep (se 1 (by rfl) ⟨2431832, by rfl⟩ : syracuseStep 3242443 = 4863665) B4863665
theorem B4323257 : Blo 1921435 4323257 := bstep (se 2 (by rfl) ⟨1621221, by rfl⟩ : syracuseStep 4323257 = 3242443) B3242443
theorem B2882171 : Blo 1921435 2882171 := bstep (se 1 (by rfl) ⟨2161628, by rfl⟩ : syracuseStep 2882171 = 4323257) B4323257
theorem B1921447 : Blo 1921435 1921447 := bstep (se 1 (by rfl) ⟨1441085, by rfl⟩ : syracuseStep 1921447 = 2882171) B2882171
theorem B2161633 : Blo 1921435 2161633 := bbase (se 2 (by rfl) ⟨810612, by rfl⟩ : syracuseStep 2161633 = 1621225) (by norm_num)
theorem B2882177 : Blo 1921435 2882177 := bstep (se 2 (by rfl) ⟨1080816, by rfl⟩ : syracuseStep 2882177 = 2161633) B2161633
theorem B1921451 : Blo 1921435 1921451 := bstep (se 1 (by rfl) ⟨1441088, by rfl⟩ : syracuseStep 1921451 = 2882177) B2882177
theorem B4863685 : Blo 1921435 4863685 := bbase (se 4 (by rfl) ⟨455970, by rfl⟩ : syracuseStep 4863685 = 911941) (by norm_num)
theorem B6484913 : Blo 1921435 6484913 := bstep (se 2 (by rfl) ⟨2431842, by rfl⟩ : syracuseStep 6484913 = 4863685) B4863685
theorem B4323275 : Blo 1921435 4323275 := bstep (se 1 (by rfl) ⟨3242456, by rfl⟩ : syracuseStep 4323275 = 6484913) B6484913
theorem B2882183 : Blo 1921435 2882183 := bstep (se 1 (by rfl) ⟨2161637, by rfl⟩ : syracuseStep 2882183 = 4323275) B4323275
theorem B1921455 : Blo 1921435 1921455 := bstep (se 1 (by rfl) ⟨1441091, by rfl⟩ : syracuseStep 1921455 = 2882183) B2882183
theorem B2882189 : Blo 1921435 2882189 := bbase (se 3 (by rfl) ⟨540410, by rfl⟩ : syracuseStep 2882189 = 1080821) (by norm_num)
theorem B1921459 : Blo 1921435 1921459 := bstep (se 1 (by rfl) ⟨1441094, by rfl⟩ : syracuseStep 1921459 = 2882189) B2882189
theorem B4323293 : Blo 1921435 4323293 := bbase (se 3 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 4323293 = 1621235) (by norm_num)
theorem B2882195 : Blo 1921435 2882195 := bstep (se 1 (by rfl) ⟨2161646, by rfl⟩ : syracuseStep 2882195 = 4323293) B4323293
theorem B1921463 : Blo 1921435 1921463 := bstep (se 1 (by rfl) ⟨1441097, by rfl⟩ : syracuseStep 1921463 = 2882195) B2882195
theorem B3242477 : Blo 1921435 3242477 := bbase (se 3 (by rfl) ⟨607964, by rfl⟩ : syracuseStep 3242477 = 1215929) (by norm_num)
theorem B2161651 : Blo 1921435 2161651 := bstep (se 1 (by rfl) ⟨1621238, by rfl⟩ : syracuseStep 2161651 = 3242477) B3242477
theorem B2882201 : Blo 1921435 2882201 := bstep (se 2 (by rfl) ⟨1080825, by rfl⟩ : syracuseStep 2882201 = 2161651) B2161651
theorem B1921467 : Blo 1921435 1921467 := bstep (se 1 (by rfl) ⟨1441100, by rfl⟩ : syracuseStep 1921467 = 2882201) B2882201
theorem B24622613 : Blo 1921435 24622613 := bbase (se 6 (by rfl) ⟨577092, by rfl⟩ : syracuseStep 24622613 = 1154185) (by norm_num)
theorem B16415075 : Blo 1921435 16415075 := bstep (se 1 (by rfl) ⟨12311306, by rfl⟩ : syracuseStep 16415075 = 24622613) B24622613
theorem B10943383 : Blo 1921435 10943383 := bstep (se 1 (by rfl) ⟨8207537, by rfl⟩ : syracuseStep 10943383 = 16415075) B16415075
theorem B14591177 : Blo 1921435 14591177 := bstep (se 2 (by rfl) ⟨5471691, by rfl⟩ : syracuseStep 14591177 = 10943383) B10943383
theorem B9727451 : Blo 1921435 9727451 := bstep (se 1 (by rfl) ⟨7295588, by rfl⟩ : syracuseStep 9727451 = 14591177) B14591177
theorem B6484967 : Blo 1921435 6484967 := bstep (se 1 (by rfl) ⟨4863725, by rfl⟩ : syracuseStep 6484967 = 9727451) B9727451
theorem B4323311 : Blo 1921435 4323311 := bstep (se 1 (by rfl) ⟨3242483, by rfl⟩ : syracuseStep 4323311 = 6484967) B6484967
theorem B2882207 : Blo 1921435 2882207 := bstep (se 1 (by rfl) ⟨2161655, by rfl⟩ : syracuseStep 2882207 = 4323311) B4323311
theorem B1921471 : Blo 1921435 1921471 := bstep (se 1 (by rfl) ⟨1441103, by rfl⟩ : syracuseStep 1921471 = 2882207) B2882207
theorem B2882213 : Blo 1921435 2882213 := bbase (se 4 (by rfl) ⟨270207, by rfl⟩ : syracuseStep 2882213 = 540415) (by norm_num)
theorem B1921475 : Blo 1921435 1921475 := bstep (se 1 (by rfl) ⟨1441106, by rfl⟩ : syracuseStep 1921475 = 2882213) B2882213
theorem B2431873 : Blo 1921435 2431873 := bbase (se 2 (by rfl) ⟨911952, by rfl⟩ : syracuseStep 2431873 = 1823905) (by norm_num)
theorem B3242497 : Blo 1921435 3242497 := bstep (se 2 (by rfl) ⟨1215936, by rfl⟩ : syracuseStep 3242497 = 2431873) B2431873
theorem B4323329 : Blo 1921435 4323329 := bstep (se 2 (by rfl) ⟨1621248, by rfl⟩ : syracuseStep 4323329 = 3242497) B3242497
theorem B2882219 : Blo 1921435 2882219 := bstep (se 1 (by rfl) ⟨2161664, by rfl⟩ : syracuseStep 2882219 = 4323329) B4323329
theorem B1921479 : Blo 1921435 1921479 := bstep (se 1 (by rfl) ⟨1441109, by rfl⟩ : syracuseStep 1921479 = 2882219) B2882219
theorem B2161669 : Blo 1921435 2161669 := bbase (se 4 (by rfl) ⟨202656, by rfl⟩ : syracuseStep 2161669 = 405313) (by norm_num)
theorem B2882225 : Blo 1921435 2882225 := bstep (se 2 (by rfl) ⟨1080834, by rfl⟩ : syracuseStep 2882225 = 2161669) B2161669
theorem B1921483 : Blo 1921435 1921483 := bstep (se 1 (by rfl) ⟨1441112, by rfl⟩ : syracuseStep 1921483 = 2882225) B2882225
theorem B2735869 : Blo 1921435 2735869 := bbase (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) (by norm_num)
theorem B3647825 : Blo 1921435 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B2431883 : Blo 1921435 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B6485021 : Blo 1921435 6485021 := bstep (se 3 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 6485021 = 2431883) B2431883
theorem B4323347 : Blo 1921435 4323347 := bstep (se 1 (by rfl) ⟨3242510, by rfl⟩ : syracuseStep 4323347 = 6485021) B6485021
theorem B2882231 : Blo 1921435 2882231 := bstep (se 1 (by rfl) ⟨2161673, by rfl⟩ : syracuseStep 2882231 = 4323347) B4323347
theorem B1921487 : Blo 1921435 1921487 := bstep (se 1 (by rfl) ⟨1441115, by rfl⟩ : syracuseStep 1921487 = 2882231) B2882231
theorem B2882237 : Blo 1921435 2882237 := bbase (se 3 (by rfl) ⟨540419, by rfl⟩ : syracuseStep 2882237 = 1080839) (by norm_num)
theorem B1921491 : Blo 1921435 1921491 := bstep (se 1 (by rfl) ⟨1441118, by rfl⟩ : syracuseStep 1921491 = 2882237) B2882237
theorem B4323365 : Blo 1921435 4323365 := bbase (se 4 (by rfl) ⟨405315, by rfl⟩ : syracuseStep 4323365 = 810631) (by norm_num)
theorem B2882243 : Blo 1921435 2882243 := bstep (se 1 (by rfl) ⟨2161682, by rfl⟩ : syracuseStep 2882243 = 4323365) B4323365
theorem B1921495 : Blo 1921435 1921495 := bstep (se 1 (by rfl) ⟨1441121, by rfl⟩ : syracuseStep 1921495 = 2882243) B2882243
theorem B4863797 : Blo 1921435 4863797 := bbase (se 5 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 4863797 = 455981) (by norm_num)
theorem B3242531 : Blo 1921435 3242531 := bstep (se 1 (by rfl) ⟨2431898, by rfl⟩ : syracuseStep 3242531 = 4863797) B4863797
theorem B2161687 : Blo 1921435 2161687 := bstep (se 1 (by rfl) ⟨1621265, by rfl⟩ : syracuseStep 2161687 = 3242531) B3242531
theorem B2882249 : Blo 1921435 2882249 := bstep (se 2 (by rfl) ⟨1080843, by rfl⟩ : syracuseStep 2882249 = 2161687) B2161687
theorem B1921499 : Blo 1921435 1921499 := bstep (se 1 (by rfl) ⟨1441124, by rfl⟩ : syracuseStep 1921499 = 2882249) B2882249
theorem B13850453 : Blo 1921435 13850453 := bbase (se 9 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 13850453 = 81155) (by norm_num)
theorem B9233635 : Blo 1921435 9233635 := bstep (se 1 (by rfl) ⟨6925226, by rfl⟩ : syracuseStep 9233635 = 13850453) B13850453
theorem B12311513 : Blo 1921435 12311513 := bstep (se 2 (by rfl) ⟨4616817, by rfl⟩ : syracuseStep 12311513 = 9233635) B9233635
theorem B8207675 : Blo 1921435 8207675 := bstep (se 1 (by rfl) ⟨6155756, by rfl⟩ : syracuseStep 8207675 = 12311513) B12311513
theorem B5471783 : Blo 1921435 5471783 := bstep (se 1 (by rfl) ⟨4103837, by rfl⟩ : syracuseStep 5471783 = 8207675) B8207675
theorem B3647855 : Blo 1921435 3647855 := bstep (se 1 (by rfl) ⟨2735891, by rfl⟩ : syracuseStep 3647855 = 5471783) B5471783
theorem B9727613 : Blo 1921435 9727613 := bstep (se 3 (by rfl) ⟨1823927, by rfl⟩ : syracuseStep 9727613 = 3647855) B3647855
theorem B6485075 : Blo 1921435 6485075 := bstep (se 1 (by rfl) ⟨4863806, by rfl⟩ : syracuseStep 6485075 = 9727613) B9727613
theorem B4323383 : Blo 1921435 4323383 := bstep (se 1 (by rfl) ⟨3242537, by rfl⟩ : syracuseStep 4323383 = 6485075) B6485075
theorem B2882255 : Blo 1921435 2882255 := bstep (se 1 (by rfl) ⟨2161691, by rfl⟩ : syracuseStep 2882255 = 4323383) B4323383
theorem B1921503 : Blo 1921435 1921503 := bstep (se 1 (by rfl) ⟨1441127, by rfl⟩ : syracuseStep 1921503 = 2882255) B2882255
theorem B2882261 : Blo 1921435 2882261 := bbase (se 7 (by rfl) ⟨33776, by rfl⟩ : syracuseStep 2882261 = 67553) (by norm_num)
theorem B1921507 : Blo 1921435 1921507 := bstep (se 1 (by rfl) ⟨1441130, by rfl⟩ : syracuseStep 1921507 = 2882261) B2882261
theorem B10529621 : Blo 1921435 10529621 := bbase (se 9 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 10529621 = 61697) (by norm_num)
theorem B7019747 : Blo 1921435 7019747 := bstep (se 1 (by rfl) ⟨5264810, by rfl⟩ : syracuseStep 7019747 = 10529621) B10529621
theorem B4679831 : Blo 1921435 4679831 := bstep (se 1 (by rfl) ⟨3509873, by rfl⟩ : syracuseStep 4679831 = 7019747) B7019747
theorem B3119887 : Blo 1921435 3119887 := bstep (se 1 (by rfl) ⟨2339915, by rfl⟩ : syracuseStep 3119887 = 4679831) B4679831
theorem B4159849 : Blo 1921435 4159849 := bstep (se 2 (by rfl) ⟨1559943, by rfl⟩ : syracuseStep 4159849 = 3119887) B3119887
theorem B5546465 : Blo 1921435 5546465 := bstep (se 2 (by rfl) ⟨2079924, by rfl⟩ : syracuseStep 5546465 = 4159849) B4159849
theorem B3697643 : Blo 1921435 3697643 := bstep (se 1 (by rfl) ⟨2773232, by rfl⟩ : syracuseStep 3697643 = 5546465) B5546465
theorem B2465095 : Blo 1921435 2465095 := bstep (se 1 (by rfl) ⟨1848821, by rfl⟩ : syracuseStep 2465095 = 3697643) B3697643
theorem B3286793 : Blo 1921435 3286793 := bstep (se 2 (by rfl) ⟨1232547, by rfl⟩ : syracuseStep 3286793 = 2465095) B2465095
theorem B2191195 : Blo 1921435 2191195 := bstep (se 1 (by rfl) ⟨1643396, by rfl⟩ : syracuseStep 2191195 = 3286793) B3286793
theorem B2921593 : Blo 1921435 2921593 := bstep (se 2 (by rfl) ⟨1095597, by rfl⟩ : syracuseStep 2921593 = 2191195) B2191195
theorem B3895457 : Blo 1921435 3895457 := bstep (se 2 (by rfl) ⟨1460796, by rfl⟩ : syracuseStep 3895457 = 2921593) B2921593
theorem B10387885 : Blo 1921435 10387885 := bstep (se 3 (by rfl) ⟨1947728, by rfl⟩ : syracuseStep 10387885 = 3895457) B3895457
theorem B13850513 : Blo 1921435 13850513 := bstep (se 2 (by rfl) ⟨5193942, by rfl⟩ : syracuseStep 13850513 = 10387885) B10387885
theorem B9233675 : Blo 1921435 9233675 := bstep (se 1 (by rfl) ⟨6925256, by rfl⟩ : syracuseStep 9233675 = 13850513) B13850513
theorem B6155783 : Blo 1921435 6155783 := bstep (se 1 (by rfl) ⟨4616837, by rfl⟩ : syracuseStep 6155783 = 9233675) B9233675
theorem B4103855 : Blo 1921435 4103855 := bstep (se 1 (by rfl) ⟨3077891, by rfl⟩ : syracuseStep 4103855 = 6155783) B6155783
theorem B2735903 : Blo 1921435 2735903 := bstep (se 1 (by rfl) ⟨2051927, by rfl⟩ : syracuseStep 2735903 = 4103855) B4103855
theorem B7295741 : Blo 1921435 7295741 := bstep (se 3 (by rfl) ⟨1367951, by rfl⟩ : syracuseStep 7295741 = 2735903) B2735903
theorem B4863827 : Blo 1921435 4863827 := bstep (se 1 (by rfl) ⟨3647870, by rfl⟩ : syracuseStep 4863827 = 7295741) B7295741
theorem B3242551 : Blo 1921435 3242551 := bstep (se 1 (by rfl) ⟨2431913, by rfl⟩ : syracuseStep 3242551 = 4863827) B4863827
theorem B4323401 : Blo 1921435 4323401 := bstep (se 2 (by rfl) ⟨1621275, by rfl⟩ : syracuseStep 4323401 = 3242551) B3242551
theorem B2882267 : Blo 1921435 2882267 := bstep (se 1 (by rfl) ⟨2161700, by rfl⟩ : syracuseStep 2882267 = 4323401) B4323401
theorem B1921511 : Blo 1921435 1921511 := bstep (se 1 (by rfl) ⟨1441133, by rfl⟩ : syracuseStep 1921511 = 2882267) B2882267
theorem B2161705 : Blo 1921435 2161705 := bbase (se 2 (by rfl) ⟨810639, by rfl⟩ : syracuseStep 2161705 = 1621279) (by norm_num)
theorem B2882273 : Blo 1921435 2882273 := bstep (se 2 (by rfl) ⟨1080852, by rfl⟩ : syracuseStep 2882273 = 2161705) B2161705
theorem B1921515 : Blo 1921435 1921515 := bstep (se 1 (by rfl) ⟨1441136, by rfl⟩ : syracuseStep 1921515 = 2882273) B2882273
theorem B42118613 : Blo 1921435 42118613 := bbase (se 7 (by rfl) ⟨493577, by rfl⟩ : syracuseStep 42118613 = 987155) (by norm_num)
theorem B28079075 : Blo 1921435 28079075 := bstep (se 1 (by rfl) ⟨21059306, by rfl⟩ : syracuseStep 28079075 = 42118613) B42118613
theorem B18719383 : Blo 1921435 18719383 := bstep (se 1 (by rfl) ⟨14039537, by rfl⟩ : syracuseStep 18719383 = 28079075) B28079075
theorem B24959177 : Blo 1921435 24959177 := bstep (se 2 (by rfl) ⟨9359691, by rfl⟩ : syracuseStep 24959177 = 18719383) B18719383
theorem B16639451 : Blo 1921435 16639451 := bstep (se 1 (by rfl) ⟨12479588, by rfl⟩ : syracuseStep 16639451 = 24959177) B24959177
theorem B11092967 : Blo 1921435 11092967 := bstep (se 1 (by rfl) ⟨8319725, by rfl⟩ : syracuseStep 11092967 = 16639451) B16639451
theorem B7395311 : Blo 1921435 7395311 := bstep (se 1 (by rfl) ⟨5546483, by rfl⟩ : syracuseStep 7395311 = 11092967) B11092967
theorem B19720829 : Blo 1921435 19720829 := bstep (se 3 (by rfl) ⟨3697655, by rfl⟩ : syracuseStep 19720829 = 7395311) B7395311
theorem B13147219 : Blo 1921435 13147219 := bstep (se 1 (by rfl) ⟨9860414, by rfl⟩ : syracuseStep 13147219 = 19720829) B19720829
theorem B17529625 : Blo 1921435 17529625 := bstep (se 2 (by rfl) ⟨6573609, by rfl⟩ : syracuseStep 17529625 = 13147219) B13147219
theorem B93491333 : Blo 1921435 93491333 := bstep (se 4 (by rfl) ⟨8764812, by rfl⟩ : syracuseStep 93491333 = 17529625) B17529625
theorem B62327555 : Blo 1921435 62327555 := bstep (se 1 (by rfl) ⟨46745666, by rfl⟩ : syracuseStep 62327555 = 93491333) B93491333
theorem B41551703 : Blo 1921435 41551703 := bstep (se 1 (by rfl) ⟨31163777, by rfl⟩ : syracuseStep 41551703 = 62327555) B62327555
theorem B27701135 : Blo 1921435 27701135 := bstep (se 1 (by rfl) ⟨20775851, by rfl⟩ : syracuseStep 27701135 = 41551703) B41551703
theorem B18467423 : Blo 1921435 18467423 := bstep (se 1 (by rfl) ⟨13850567, by rfl⟩ : syracuseStep 18467423 = 27701135) B27701135
theorem B12311615 : Blo 1921435 12311615 := bstep (se 1 (by rfl) ⟨9233711, by rfl⟩ : syracuseStep 12311615 = 18467423) B18467423
theorem B8207743 : Blo 1921435 8207743 := bstep (se 1 (by rfl) ⟨6155807, by rfl⟩ : syracuseStep 8207743 = 12311615) B12311615
theorem B10943657 : Blo 1921435 10943657 := bstep (se 2 (by rfl) ⟨4103871, by rfl⟩ : syracuseStep 10943657 = 8207743) B8207743
theorem B7295771 : Blo 1921435 7295771 := bstep (se 1 (by rfl) ⟨5471828, by rfl⟩ : syracuseStep 7295771 = 10943657) B10943657
theorem B4863847 : Blo 1921435 4863847 := bstep (se 1 (by rfl) ⟨3647885, by rfl⟩ : syracuseStep 4863847 = 7295771) B7295771
theorem B6485129 : Blo 1921435 6485129 := bstep (se 2 (by rfl) ⟨2431923, by rfl⟩ : syracuseStep 6485129 = 4863847) B4863847
theorem B4323419 : Blo 1921435 4323419 := bstep (se 1 (by rfl) ⟨3242564, by rfl⟩ : syracuseStep 4323419 = 6485129) B6485129
theorem B2882279 : Blo 1921435 2882279 := bstep (se 1 (by rfl) ⟨2161709, by rfl⟩ : syracuseStep 2882279 = 4323419) B4323419
theorem B1921519 : Blo 1921435 1921519 := bstep (se 1 (by rfl) ⟨1441139, by rfl⟩ : syracuseStep 1921519 = 2882279) B2882279
theorem B2882285 : Blo 1921435 2882285 := bbase (se 3 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 2882285 = 1080857) (by norm_num)
theorem B1921523 : Blo 1921435 1921523 := bstep (se 1 (by rfl) ⟨1441142, by rfl⟩ : syracuseStep 1921523 = 2882285) B2882285
theorem B4323437 : Blo 1921435 4323437 := bbase (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) (by norm_num)
theorem B2882291 : Blo 1921435 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B1921527 : Blo 1921435 1921527 := bstep (se 1 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 1921527 = 2882291) B2882291
theorem B3647909 : Blo 1921435 3647909 := bbase (se 4 (by rfl) ⟨341991, by rfl⟩ : syracuseStep 3647909 = 683983) (by norm_num)
theorem B2431939 : Blo 1921435 2431939 := bstep (se 1 (by rfl) ⟨1823954, by rfl⟩ : syracuseStep 2431939 = 3647909) B3647909
theorem B3242585 : Blo 1921435 3242585 := bstep (se 2 (by rfl) ⟨1215969, by rfl⟩ : syracuseStep 3242585 = 2431939) B2431939
theorem B2161723 : Blo 1921435 2161723 := bstep (se 1 (by rfl) ⟨1621292, by rfl⟩ : syracuseStep 2161723 = 3242585) B3242585
theorem B2882297 : Blo 1921435 2882297 := bstep (se 2 (by rfl) ⟨1080861, by rfl⟩ : syracuseStep 2882297 = 2161723) B2161723
theorem B1921531 : Blo 1921435 1921531 := bstep (se 1 (by rfl) ⟨1441148, by rfl⟩ : syracuseStep 1921531 = 2882297) B2882297
theorem B8764885 : Blo 1921435 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B11686513 : Blo 1921435 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B15582017 : Blo 1921435 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B10388011 : Blo 1921435 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B13850681 : Blo 1921435 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B36935149 : Blo 1921435 36935149 := bstep (se 3 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 36935149 = 13850681) B13850681
theorem B49246865 : Blo 1921435 49246865 := bstep (se 2 (by rfl) ⟨18467574, by rfl⟩ : syracuseStep 49246865 = 36935149) B36935149
theorem B32831243 : Blo 1921435 32831243 := bstep (se 1 (by rfl) ⟨24623432, by rfl⟩ : syracuseStep 32831243 = 49246865) B49246865
theorem B21887495 : Blo 1921435 21887495 := bstep (se 1 (by rfl) ⟨16415621, by rfl⟩ : syracuseStep 21887495 = 32831243) B32831243
theorem B14591663 : Blo 1921435 14591663 := bstep (se 1 (by rfl) ⟨10943747, by rfl⟩ : syracuseStep 14591663 = 21887495) B21887495
theorem B9727775 : Blo 1921435 9727775 := bstep (se 1 (by rfl) ⟨7295831, by rfl⟩ : syracuseStep 9727775 = 14591663) B14591663
theorem B6485183 : Blo 1921435 6485183 := bstep (se 1 (by rfl) ⟨4863887, by rfl⟩ : syracuseStep 6485183 = 9727775) B9727775
theorem B4323455 : Blo 1921435 4323455 := bstep (se 1 (by rfl) ⟨3242591, by rfl⟩ : syracuseStep 4323455 = 6485183) B6485183
theorem B2882303 : Blo 1921435 2882303 := bstep (se 1 (by rfl) ⟨2161727, by rfl⟩ : syracuseStep 2882303 = 4323455) B4323455
theorem B1921535 : Blo 1921435 1921535 := bstep (se 1 (by rfl) ⟨1441151, by rfl⟩ : syracuseStep 1921535 = 2882303) B2882303
theorem B2882309 : Blo 1921435 2882309 := bbase (se 4 (by rfl) ⟨270216, by rfl⟩ : syracuseStep 2882309 = 540433) (by norm_num)
theorem B1921539 : Blo 1921435 1921539 := bstep (se 1 (by rfl) ⟨1441154, by rfl⟩ : syracuseStep 1921539 = 2882309) B2882309
theorem B3242605 : Blo 1921435 3242605 := bbase (se 3 (by rfl) ⟨607988, by rfl⟩ : syracuseStep 3242605 = 1215977) (by norm_num)
theorem B4323473 : Blo 1921435 4323473 := bstep (se 2 (by rfl) ⟨1621302, by rfl⟩ : syracuseStep 4323473 = 3242605) B3242605
theorem B2882315 : Blo 1921435 2882315 := bstep (se 1 (by rfl) ⟨2161736, by rfl⟩ : syracuseStep 2882315 = 4323473) B4323473
theorem B1921543 : Blo 1921435 1921543 := bstep (se 1 (by rfl) ⟨1441157, by rfl⟩ : syracuseStep 1921543 = 2882315) B2882315
theorem B2161741 : Blo 1921435 2161741 := bbase (se 3 (by rfl) ⟨405326, by rfl⟩ : syracuseStep 2161741 = 810653) (by norm_num)
theorem B2882321 : Blo 1921435 2882321 := bstep (se 2 (by rfl) ⟨1080870, by rfl⟩ : syracuseStep 2882321 = 2161741) B2161741
theorem B1921547 : Blo 1921435 1921547 := bstep (se 1 (by rfl) ⟨1441160, by rfl⟩ : syracuseStep 1921547 = 2882321) B2882321
theorem B6485237 : Blo 1921435 6485237 := bbase (se 5 (by rfl) ⟨303995, by rfl⟩ : syracuseStep 6485237 = 607991) (by norm_num)
theorem B4323491 : Blo 1921435 4323491 := bstep (se 1 (by rfl) ⟨3242618, by rfl⟩ : syracuseStep 4323491 = 6485237) B6485237
theorem B2882327 : Blo 1921435 2882327 := bstep (se 1 (by rfl) ⟨2161745, by rfl⟩ : syracuseStep 2882327 = 4323491) B4323491
theorem B1921551 : Blo 1921435 1921551 := bstep (se 1 (by rfl) ⟨1441163, by rfl⟩ : syracuseStep 1921551 = 2882327) B2882327
theorem B2882333 : Blo 1921435 2882333 := bbase (se 3 (by rfl) ⟨540437, by rfl⟩ : syracuseStep 2882333 = 1080875) (by norm_num)
theorem B1921555 : Blo 1921435 1921555 := bstep (se 1 (by rfl) ⟨1441166, by rfl⟩ : syracuseStep 1921555 = 2882333) B2882333
theorem B4323509 : Blo 1921435 4323509 := bbase (se 5 (by rfl) ⟨202664, by rfl⟩ : syracuseStep 4323509 = 405329) (by norm_num)
theorem B2882339 : Blo 1921435 2882339 := bstep (se 1 (by rfl) ⟨2161754, by rfl⟩ : syracuseStep 2882339 = 4323509) B4323509
theorem B1921559 : Blo 1921435 1921559 := bstep (se 1 (by rfl) ⟨1441169, by rfl⟩ : syracuseStep 1921559 = 2882339) B2882339
theorem B6925445 : Blo 1921435 6925445 := bbase (se 4 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 6925445 = 1298521) (by norm_num)
theorem B4616963 : Blo 1921435 4616963 := bstep (se 1 (by rfl) ⟨3462722, by rfl⟩ : syracuseStep 4616963 = 6925445) B6925445
theorem B3077975 : Blo 1921435 3077975 := bstep (se 1 (by rfl) ⟨2308481, by rfl⟩ : syracuseStep 3077975 = 4616963) B4616963
theorem B2051983 : Blo 1921435 2051983 := bstep (se 1 (by rfl) ⟨1538987, by rfl⟩ : syracuseStep 2051983 = 3077975) B3077975
theorem B10943909 : Blo 1921435 10943909 := bstep (se 4 (by rfl) ⟨1025991, by rfl⟩ : syracuseStep 10943909 = 2051983) B2051983
theorem B7295939 : Blo 1921435 7295939 := bstep (se 1 (by rfl) ⟨5471954, by rfl⟩ : syracuseStep 7295939 = 10943909) B10943909
theorem B4863959 : Blo 1921435 4863959 := bstep (se 1 (by rfl) ⟨3647969, by rfl⟩ : syracuseStep 4863959 = 7295939) B7295939
theorem B3242639 : Blo 1921435 3242639 := bstep (se 1 (by rfl) ⟨2431979, by rfl⟩ : syracuseStep 3242639 = 4863959) B4863959
theorem B2161759 : Blo 1921435 2161759 := bstep (se 1 (by rfl) ⟨1621319, by rfl⟩ : syracuseStep 2161759 = 3242639) B3242639
theorem B2882345 : Blo 1921435 2882345 := bstep (se 2 (by rfl) ⟨1080879, by rfl⟩ : syracuseStep 2882345 = 2161759) B2161759
theorem B1921563 : Blo 1921435 1921563 := bstep (se 1 (by rfl) ⟨1441172, by rfl⟩ : syracuseStep 1921563 = 2882345) B2882345
theorem B3077981 : Blo 1921435 3077981 := bbase (se 3 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 3077981 = 1154243) (by norm_num)
theorem B2051987 : Blo 1921435 2051987 := bstep (se 1 (by rfl) ⟨1538990, by rfl⟩ : syracuseStep 2051987 = 3077981) B3077981
theorem B5471965 : Blo 1921435 5471965 := bstep (se 3 (by rfl) ⟨1025993, by rfl⟩ : syracuseStep 5471965 = 2051987) B2051987
theorem B7295953 : Blo 1921435 7295953 := bstep (se 2 (by rfl) ⟨2735982, by rfl⟩ : syracuseStep 7295953 = 5471965) B5471965
theorem B9727937 : Blo 1921435 9727937 := bstep (se 2 (by rfl) ⟨3647976, by rfl⟩ : syracuseStep 9727937 = 7295953) B7295953
theorem B6485291 : Blo 1921435 6485291 := bstep (se 1 (by rfl) ⟨4863968, by rfl⟩ : syracuseStep 6485291 = 9727937) B9727937
theorem B4323527 : Blo 1921435 4323527 := bstep (se 1 (by rfl) ⟨3242645, by rfl⟩ : syracuseStep 4323527 = 6485291) B6485291
theorem B2882351 : Blo 1921435 2882351 := bstep (se 1 (by rfl) ⟨2161763, by rfl⟩ : syracuseStep 2882351 = 4323527) B4323527
theorem B1921567 : Blo 1921435 1921567 := bstep (se 1 (by rfl) ⟨1441175, by rfl⟩ : syracuseStep 1921567 = 2882351) B2882351
theorem B2882357 : Blo 1921435 2882357 := bbase (se 5 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 2882357 = 270221) (by norm_num)
theorem B1921571 : Blo 1921435 1921571 := bstep (se 1 (by rfl) ⟨1441178, by rfl⟩ : syracuseStep 1921571 = 2882357) B2882357
theorem B4863989 : Blo 1921435 4863989 := bbase (se 5 (by rfl) ⟨227999, by rfl⟩ : syracuseStep 4863989 = 455999) (by norm_num)
theorem B3242659 : Blo 1921435 3242659 := bstep (se 1 (by rfl) ⟨2431994, by rfl⟩ : syracuseStep 3242659 = 4863989) B4863989
theorem B4323545 : Blo 1921435 4323545 := bstep (se 2 (by rfl) ⟨1621329, by rfl⟩ : syracuseStep 4323545 = 3242659) B3242659
theorem B2882363 : Blo 1921435 2882363 := bstep (se 1 (by rfl) ⟨2161772, by rfl⟩ : syracuseStep 2882363 = 4323545) B4323545
theorem B1921575 : Blo 1921435 1921575 := bstep (se 1 (by rfl) ⟨1441181, by rfl⟩ : syracuseStep 1921575 = 2882363) B2882363
theorem B2161777 : Blo 1921435 2161777 := bbase (se 2 (by rfl) ⟨810666, by rfl⟩ : syracuseStep 2161777 = 1621333) (by norm_num)
theorem B2882369 : Blo 1921435 2882369 := bstep (se 2 (by rfl) ⟨1080888, by rfl⟩ : syracuseStep 2882369 = 2161777) B2161777
theorem B1921579 : Blo 1921435 1921579 := bstep (se 1 (by rfl) ⟨1441184, by rfl⟩ : syracuseStep 1921579 = 2882369) B2882369
theorem B2308505 : Blo 1921435 2308505 := bbase (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) (by norm_num)
theorem B6156013 : Blo 1921435 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B8208017 : Blo 1921435 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B5472011 : Blo 1921435 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B3648007 : Blo 1921435 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B4864009 : Blo 1921435 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B6485345 : Blo 1921435 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B4323563 : Blo 1921435 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B2882375 : Blo 1921435 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B1921583 : Blo 1921435 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B2882381 : Blo 1921435 2882381 := bbase (se 3 (by rfl) ⟨540446, by rfl⟩ : syracuseStep 2882381 = 1080893) (by norm_num)
theorem B1921587 : Blo 1921435 1921587 := bstep (se 1 (by rfl) ⟨1441190, by rfl⟩ : syracuseStep 1921587 = 2882381) B2882381
theorem B4323581 : Blo 1921435 4323581 := bbase (se 3 (by rfl) ⟨810671, by rfl⟩ : syracuseStep 4323581 = 1621343) (by norm_num)
theorem B2882387 : Blo 1921435 2882387 := bstep (se 1 (by rfl) ⟨2161790, by rfl⟩ : syracuseStep 2882387 = 4323581) B4323581
theorem B1921591 : Blo 1921435 1921591 := bstep (se 1 (by rfl) ⟨1441193, by rfl⟩ : syracuseStep 1921591 = 2882387) B2882387
theorem B3242693 : Blo 1921435 3242693 := bbase (se 4 (by rfl) ⟨304002, by rfl⟩ : syracuseStep 3242693 = 608005) (by norm_num)
theorem B2161795 : Blo 1921435 2161795 := bstep (se 1 (by rfl) ⟨1621346, by rfl⟩ : syracuseStep 2161795 = 3242693) B3242693
theorem B2882393 : Blo 1921435 2882393 := bstep (se 2 (by rfl) ⟨1080897, by rfl⟩ : syracuseStep 2882393 = 2161795) B2161795
theorem B1921595 : Blo 1921435 1921595 := bstep (se 1 (by rfl) ⟨1441196, by rfl⟩ : syracuseStep 1921595 = 2882393) B2882393
theorem B14592149 : Blo 1921435 14592149 := bbase (se 6 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 14592149 = 684007) (by norm_num)
theorem B9728099 : Blo 1921435 9728099 := bstep (se 1 (by rfl) ⟨7296074, by rfl⟩ : syracuseStep 9728099 = 14592149) B14592149
theorem B6485399 : Blo 1921435 6485399 := bstep (se 1 (by rfl) ⟨4864049, by rfl⟩ : syracuseStep 6485399 = 9728099) B9728099
theorem B4323599 : Blo 1921435 4323599 := bstep (se 1 (by rfl) ⟨3242699, by rfl⟩ : syracuseStep 4323599 = 6485399) B6485399
theorem B2882399 : Blo 1921435 2882399 := bstep (se 1 (by rfl) ⟨2161799, by rfl⟩ : syracuseStep 2882399 = 4323599) B4323599
theorem B1921599 : Blo 1921435 1921599 := bstep (se 1 (by rfl) ⟨1441199, by rfl⟩ : syracuseStep 1921599 = 2882399) B2882399
theorem B2882405 : Blo 1921435 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B1921603 : Blo 1921435 1921603 := bstep (se 1 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 1921603 = 2882405) B2882405
theorem B3648053 : Blo 1921435 3648053 := bbase (se 5 (by rfl) ⟨171002, by rfl⟩ : syracuseStep 3648053 = 342005) (by norm_num)
theorem B2432035 : Blo 1921435 2432035 := bstep (se 1 (by rfl) ⟨1824026, by rfl⟩ : syracuseStep 2432035 = 3648053) B3648053
theorem B3242713 : Blo 1921435 3242713 := bstep (se 2 (by rfl) ⟨1216017, by rfl⟩ : syracuseStep 3242713 = 2432035) B2432035
theorem B4323617 : Blo 1921435 4323617 := bstep (se 2 (by rfl) ⟨1621356, by rfl⟩ : syracuseStep 4323617 = 3242713) B3242713
theorem B2882411 : Blo 1921435 2882411 := bstep (se 1 (by rfl) ⟨2161808, by rfl⟩ : syracuseStep 2882411 = 4323617) B4323617
theorem B1921607 : Blo 1921435 1921607 := bstep (se 1 (by rfl) ⟨1441205, by rfl⟩ : syracuseStep 1921607 = 2882411) B2882411
theorem B2161813 : Blo 1921435 2161813 := bbase (se 6 (by rfl) ⟨50667, by rfl⟩ : syracuseStep 2161813 = 101335) (by norm_num)
theorem B2882417 : Blo 1921435 2882417 := bstep (se 2 (by rfl) ⟨1080906, by rfl⟩ : syracuseStep 2882417 = 2161813) B2161813
theorem B1921611 : Blo 1921435 1921611 := bstep (se 1 (by rfl) ⟨1441208, by rfl⟩ : syracuseStep 1921611 = 2882417) B2882417
theorem B2432045 : Blo 1921435 2432045 := bbase (se 3 (by rfl) ⟨456008, by rfl⟩ : syracuseStep 2432045 = 912017) (by norm_num)
theorem B6485453 : Blo 1921435 6485453 := bstep (se 3 (by rfl) ⟨1216022, by rfl⟩ : syracuseStep 6485453 = 2432045) B2432045
theorem B4323635 : Blo 1921435 4323635 := bstep (se 1 (by rfl) ⟨3242726, by rfl⟩ : syracuseStep 4323635 = 6485453) B6485453
theorem B2882423 : Blo 1921435 2882423 := bstep (se 1 (by rfl) ⟨2161817, by rfl⟩ : syracuseStep 2882423 = 4323635) B4323635
theorem B1921615 : Blo 1921435 1921615 := bstep (se 1 (by rfl) ⟨1441211, by rfl⟩ : syracuseStep 1921615 = 2882423) B2882423
theorem B2882429 : Blo 1921435 2882429 := bbase (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) (by norm_num)
theorem B1921619 : Blo 1921435 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B4323653 : Blo 1921435 4323653 := bbase (se 4 (by rfl) ⟨405342, by rfl⟩ : syracuseStep 4323653 = 810685) (by norm_num)
theorem B2882435 : Blo 1921435 2882435 := bstep (se 1 (by rfl) ⟨2161826, by rfl⟩ : syracuseStep 2882435 = 4323653) B4323653
theorem B1921623 : Blo 1921435 1921623 := bstep (se 1 (by rfl) ⟨1441217, by rfl⟩ : syracuseStep 1921623 = 2882435) B2882435
theorem B6240149 : Blo 1921435 6240149 := bbase (se 6 (by rfl) ⟨146253, by rfl⟩ : syracuseStep 6240149 = 292507) (by norm_num)
theorem B4160099 : Blo 1921435 4160099 := bstep (se 1 (by rfl) ⟨3120074, by rfl⟩ : syracuseStep 4160099 = 6240149) B6240149
theorem B11093597 : Blo 1921435 11093597 := bstep (se 3 (by rfl) ⟨2080049, by rfl⟩ : syracuseStep 11093597 = 4160099) B4160099
theorem B7395731 : Blo 1921435 7395731 := bstep (se 1 (by rfl) ⟨5546798, by rfl⟩ : syracuseStep 7395731 = 11093597) B11093597
theorem B4930487 : Blo 1921435 4930487 := bstep (se 1 (by rfl) ⟨3697865, by rfl⟩ : syracuseStep 4930487 = 7395731) B7395731
theorem B3286991 : Blo 1921435 3286991 := bstep (se 1 (by rfl) ⟨2465243, by rfl⟩ : syracuseStep 3286991 = 4930487) B4930487
theorem B8765309 : Blo 1921435 8765309 := bstep (se 3 (by rfl) ⟨1643495, by rfl⟩ : syracuseStep 8765309 = 3286991) B3286991
theorem B5843539 : Blo 1921435 5843539 := bstep (se 1 (by rfl) ⟨4382654, by rfl⟩ : syracuseStep 5843539 = 8765309) B8765309
theorem B7791385 : Blo 1921435 7791385 := bstep (se 2 (by rfl) ⟨2921769, by rfl⟩ : syracuseStep 7791385 = 5843539) B5843539
theorem B10388513 : Blo 1921435 10388513 := bstep (se 2 (by rfl) ⟨3895692, by rfl⟩ : syracuseStep 10388513 = 7791385) B7791385
theorem B6925675 : Blo 1921435 6925675 := bstep (se 1 (by rfl) ⟨5194256, by rfl⟩ : syracuseStep 6925675 = 10388513) B10388513
theorem B9234233 : Blo 1921435 9234233 := bstep (se 2 (by rfl) ⟨3462837, by rfl⟩ : syracuseStep 9234233 = 6925675) B6925675
theorem B6156155 : Blo 1921435 6156155 := bstep (se 1 (by rfl) ⟨4617116, by rfl⟩ : syracuseStep 6156155 = 9234233) B9234233
theorem B4104103 : Blo 1921435 4104103 := bstep (se 1 (by rfl) ⟨3078077, by rfl⟩ : syracuseStep 4104103 = 6156155) B6156155
theorem B5472137 : Blo 1921435 5472137 := bstep (se 2 (by rfl) ⟨2052051, by rfl⟩ : syracuseStep 5472137 = 4104103) B4104103
theorem B3648091 : Blo 1921435 3648091 := bstep (se 1 (by rfl) ⟨2736068, by rfl⟩ : syracuseStep 3648091 = 5472137) B5472137
theorem B4864121 : Blo 1921435 4864121 := bstep (se 2 (by rfl) ⟨1824045, by rfl⟩ : syracuseStep 4864121 = 3648091) B3648091
theorem B3242747 : Blo 1921435 3242747 := bstep (se 1 (by rfl) ⟨2432060, by rfl⟩ : syracuseStep 3242747 = 4864121) B4864121
theorem B2161831 : Blo 1921435 2161831 := bstep (se 1 (by rfl) ⟨1621373, by rfl⟩ : syracuseStep 2161831 = 3242747) B3242747
theorem B2882441 : Blo 1921435 2882441 := bstep (se 2 (by rfl) ⟨1080915, by rfl⟩ : syracuseStep 2882441 = 2161831) B2161831
theorem B1921627 : Blo 1921435 1921627 := bstep (se 1 (by rfl) ⟨1441220, by rfl⟩ : syracuseStep 1921627 = 2882441) B2882441
theorem B9728261 : Blo 1921435 9728261 := bbase (se 4 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 9728261 = 1824049) (by norm_num)
theorem B6485507 : Blo 1921435 6485507 := bstep (se 1 (by rfl) ⟨4864130, by rfl⟩ : syracuseStep 6485507 = 9728261) B9728261
theorem B4323671 : Blo 1921435 4323671 := bstep (se 1 (by rfl) ⟨3242753, by rfl⟩ : syracuseStep 4323671 = 6485507) B6485507
theorem B2882447 : Blo 1921435 2882447 := bstep (se 1 (by rfl) ⟨2161835, by rfl⟩ : syracuseStep 2882447 = 4323671) B4323671
theorem B1921631 : Blo 1921435 1921631 := bstep (se 1 (by rfl) ⟨1441223, by rfl⟩ : syracuseStep 1921631 = 2882447) B2882447
theorem B2882453 : Blo 1921435 2882453 := bbase (se 6 (by rfl) ⟨67557, by rfl⟩ : syracuseStep 2882453 = 135115) (by norm_num)
theorem B1921635 : Blo 1921435 1921635 := bstep (se 1 (by rfl) ⟨1441226, by rfl⟩ : syracuseStep 1921635 = 2882453) B2882453
theorem B10944341 : Blo 1921435 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B7296227 : Blo 1921435 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B4864151 : Blo 1921435 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B3242767 : Blo 1921435 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B4323689 : Blo 1921435 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2882459 : Blo 1921435 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B1921639 : Blo 1921435 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B2161849 : Blo 1921435 2161849 := bbase (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) (by norm_num)
theorem B2882465 : Blo 1921435 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B1921643 : Blo 1921435 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B3078109 : Blo 1921435 3078109 := bbase (se 3 (by rfl) ⟨577145, by rfl⟩ : syracuseStep 3078109 = 1154291) (by norm_num)
theorem B4104145 : Blo 1921435 4104145 := bstep (se 2 (by rfl) ⟨1539054, by rfl⟩ : syracuseStep 4104145 = 3078109) B3078109
theorem B5472193 : Blo 1921435 5472193 := bstep (se 2 (by rfl) ⟨2052072, by rfl⟩ : syracuseStep 5472193 = 4104145) B4104145
theorem B7296257 : Blo 1921435 7296257 := bstep (se 2 (by rfl) ⟨2736096, by rfl⟩ : syracuseStep 7296257 = 5472193) B5472193
theorem B4864171 : Blo 1921435 4864171 := bstep (se 1 (by rfl) ⟨3648128, by rfl⟩ : syracuseStep 4864171 = 7296257) B7296257
theorem B6485561 : Blo 1921435 6485561 := bstep (se 2 (by rfl) ⟨2432085, by rfl⟩ : syracuseStep 6485561 = 4864171) B4864171
theorem B4323707 : Blo 1921435 4323707 := bstep (se 1 (by rfl) ⟨3242780, by rfl⟩ : syracuseStep 4323707 = 6485561) B6485561
theorem B2882471 : Blo 1921435 2882471 := bstep (se 1 (by rfl) ⟨2161853, by rfl⟩ : syracuseStep 2882471 = 4323707) B4323707
theorem B1921647 : Blo 1921435 1921647 := bstep (se 1 (by rfl) ⟨1441235, by rfl⟩ : syracuseStep 1921647 = 2882471) B2882471
theorem B2882477 : Blo 1921435 2882477 := bbase (se 3 (by rfl) ⟨540464, by rfl⟩ : syracuseStep 2882477 = 1080929) (by norm_num)
theorem B1921651 : Blo 1921435 1921651 := bstep (se 1 (by rfl) ⟨1441238, by rfl⟩ : syracuseStep 1921651 = 2882477) B2882477
theorem B4323725 : Blo 1921435 4323725 := bbase (se 3 (by rfl) ⟨810698, by rfl⟩ : syracuseStep 4323725 = 1621397) (by norm_num)
theorem B2882483 : Blo 1921435 2882483 := bstep (se 1 (by rfl) ⟨2161862, by rfl⟩ : syracuseStep 2882483 = 4323725) B4323725
theorem B1921655 : Blo 1921435 1921655 := bstep (se 1 (by rfl) ⟨1441241, by rfl⟩ : syracuseStep 1921655 = 2882483) B2882483
theorem B2432101 : Blo 1921435 2432101 := bbase (se 4 (by rfl) ⟨228009, by rfl⟩ : syracuseStep 2432101 = 456019) (by norm_num)
theorem B3242801 : Blo 1921435 3242801 := bstep (se 2 (by rfl) ⟨1216050, by rfl⟩ : syracuseStep 3242801 = 2432101) B2432101
theorem B2161867 : Blo 1921435 2161867 := bstep (se 1 (by rfl) ⟨1621400, by rfl⟩ : syracuseStep 2161867 = 3242801) B3242801
theorem B2882489 : Blo 1921435 2882489 := bstep (se 2 (by rfl) ⟨1080933, by rfl⟩ : syracuseStep 2882489 = 2161867) B2161867
theorem B1921659 : Blo 1921435 1921659 := bstep (se 1 (by rfl) ⟨1441244, by rfl⟩ : syracuseStep 1921659 = 2882489) B2882489
theorem B3462901 : Blo 1921435 3462901 := bbase (se 5 (by rfl) ⟨162323, by rfl⟩ : syracuseStep 3462901 = 324647) (by norm_num)
theorem B18468805 : Blo 1921435 18468805 := bstep (se 4 (by rfl) ⟨1731450, by rfl⟩ : syracuseStep 18468805 = 3462901) B3462901
theorem B24625073 : Blo 1921435 24625073 := bstep (se 2 (by rfl) ⟨9234402, by rfl⟩ : syracuseStep 24625073 = 18468805) B18468805
theorem B16416715 : Blo 1921435 16416715 := bstep (se 1 (by rfl) ⟨12312536, by rfl⟩ : syracuseStep 16416715 = 24625073) B24625073
theorem B21888953 : Blo 1921435 21888953 := bstep (se 2 (by rfl) ⟨8208357, by rfl⟩ : syracuseStep 21888953 = 16416715) B16416715
theorem B14592635 : Blo 1921435 14592635 := bstep (se 1 (by rfl) ⟨10944476, by rfl⟩ : syracuseStep 14592635 = 21888953) B21888953
theorem B9728423 : Blo 1921435 9728423 := bstep (se 1 (by rfl) ⟨7296317, by rfl⟩ : syracuseStep 9728423 = 14592635) B14592635
theorem B6485615 : Blo 1921435 6485615 := bstep (se 1 (by rfl) ⟨4864211, by rfl⟩ : syracuseStep 6485615 = 9728423) B9728423
theorem B4323743 : Blo 1921435 4323743 := bstep (se 1 (by rfl) ⟨3242807, by rfl⟩ : syracuseStep 4323743 = 6485615) B6485615
theorem B2882495 : Blo 1921435 2882495 := bstep (se 1 (by rfl) ⟨2161871, by rfl⟩ : syracuseStep 2882495 = 4323743) B4323743
theorem B1921663 : Blo 1921435 1921663 := bstep (se 1 (by rfl) ⟨1441247, by rfl⟩ : syracuseStep 1921663 = 2882495) B2882495
theorem B2882501 : Blo 1921435 2882501 := bbase (se 4 (by rfl) ⟨270234, by rfl⟩ : syracuseStep 2882501 = 540469) (by norm_num)
theorem B1921667 : Blo 1921435 1921667 := bstep (se 1 (by rfl) ⟨1441250, by rfl⟩ : syracuseStep 1921667 = 2882501) B2882501
theorem B3242821 : Blo 1921435 3242821 := bbase (se 4 (by rfl) ⟨304014, by rfl⟩ : syracuseStep 3242821 = 608029) (by norm_num)
theorem B4323761 : Blo 1921435 4323761 := bstep (se 2 (by rfl) ⟨1621410, by rfl⟩ : syracuseStep 4323761 = 3242821) B3242821
theorem B2882507 : Blo 1921435 2882507 := bstep (se 1 (by rfl) ⟨2161880, by rfl⟩ : syracuseStep 2882507 = 4323761) B4323761
theorem B1921671 : Blo 1921435 1921671 := bstep (se 1 (by rfl) ⟨1441253, by rfl⟩ : syracuseStep 1921671 = 2882507) B2882507
theorem B2161885 : Blo 1921435 2161885 := bbase (se 3 (by rfl) ⟨405353, by rfl⟩ : syracuseStep 2161885 = 810707) (by norm_num)
theorem B2882513 : Blo 1921435 2882513 := bstep (se 2 (by rfl) ⟨1080942, by rfl⟩ : syracuseStep 2882513 = 2161885) B2161885
theorem B1921675 : Blo 1921435 1921675 := bstep (se 1 (by rfl) ⟨1441256, by rfl⟩ : syracuseStep 1921675 = 2882513) B2882513
theorem B6485669 : Blo 1921435 6485669 := bbase (se 4 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 6485669 = 1216063) (by norm_num)
theorem B4323779 : Blo 1921435 4323779 := bstep (se 1 (by rfl) ⟨3242834, by rfl⟩ : syracuseStep 4323779 = 6485669) B6485669
theorem B2882519 : Blo 1921435 2882519 := bstep (se 1 (by rfl) ⟨2161889, by rfl⟩ : syracuseStep 2882519 = 4323779) B4323779
theorem B1921679 : Blo 1921435 1921679 := bstep (se 1 (by rfl) ⟨1441259, by rfl⟩ : syracuseStep 1921679 = 2882519) B2882519
theorem B2882525 : Blo 1921435 2882525 := bbase (se 3 (by rfl) ⟨540473, by rfl⟩ : syracuseStep 2882525 = 1080947) (by norm_num)
theorem B1921683 : Blo 1921435 1921683 := bstep (se 1 (by rfl) ⟨1441262, by rfl⟩ : syracuseStep 1921683 = 2882525) B2882525
theorem B4323797 : Blo 1921435 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B2882531 : Blo 1921435 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B1921687 : Blo 1921435 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B4442597 : Blo 1921435 4442597 := bbase (se 4 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 4442597 = 832987) (by norm_num)
theorem B2961731 : Blo 1921435 2961731 := bstep (se 1 (by rfl) ⟨2221298, by rfl⟩ : syracuseStep 2961731 = 4442597) B4442597
theorem B1974487 : Blo 1921435 1974487 := bstep (se 1 (by rfl) ⟨1480865, by rfl⟩ : syracuseStep 1974487 = 2961731) B2961731
theorem B168489557 : Blo 1921435 168489557 := bstep (se 8 (by rfl) ⟨987243, by rfl⟩ : syracuseStep 168489557 = 1974487) B1974487
theorem B112326371 : Blo 1921435 112326371 := bstep (se 1 (by rfl) ⟨84244778, by rfl⟩ : syracuseStep 112326371 = 168489557) B168489557
theorem B74884247 : Blo 1921435 74884247 := bstep (se 1 (by rfl) ⟨56163185, by rfl⟩ : syracuseStep 74884247 = 112326371) B112326371
theorem B49922831 : Blo 1921435 49922831 := bstep (se 1 (by rfl) ⟨37442123, by rfl⟩ : syracuseStep 49922831 = 74884247) B74884247
theorem B33281887 : Blo 1921435 33281887 := bstep (se 1 (by rfl) ⟨24961415, by rfl⟩ : syracuseStep 33281887 = 49922831) B49922831
theorem B44375849 : Blo 1921435 44375849 := bstep (se 2 (by rfl) ⟨16640943, by rfl⟩ : syracuseStep 44375849 = 33281887) B33281887
theorem B29583899 : Blo 1921435 29583899 := bstep (se 1 (by rfl) ⟨22187924, by rfl⟩ : syracuseStep 29583899 = 44375849) B44375849
theorem B19722599 : Blo 1921435 19722599 := bstep (se 1 (by rfl) ⟨14791949, by rfl⟩ : syracuseStep 19722599 = 29583899) B29583899
theorem B13148399 : Blo 1921435 13148399 := bstep (se 1 (by rfl) ⟨9861299, by rfl⟩ : syracuseStep 13148399 = 19722599) B19722599
theorem B8765599 : Blo 1921435 8765599 := bstep (se 1 (by rfl) ⟨6574199, by rfl⟩ : syracuseStep 8765599 = 13148399) B13148399
theorem B11687465 : Blo 1921435 11687465 := bstep (se 2 (by rfl) ⟨4382799, by rfl⟩ : syracuseStep 11687465 = 8765599) B8765599
theorem B7791643 : Blo 1921435 7791643 := bstep (se 1 (by rfl) ⟨5843732, by rfl⟩ : syracuseStep 7791643 = 11687465) B11687465
theorem B41555429 : Blo 1921435 41555429 := bstep (se 4 (by rfl) ⟨3895821, by rfl⟩ : syracuseStep 41555429 = 7791643) B7791643
theorem B27703619 : Blo 1921435 27703619 := bstep (se 1 (by rfl) ⟨20777714, by rfl⟩ : syracuseStep 27703619 = 41555429) B41555429
theorem B18469079 : Blo 1921435 18469079 := bstep (se 1 (by rfl) ⟨13851809, by rfl⟩ : syracuseStep 18469079 = 27703619) B27703619
theorem B12312719 : Blo 1921435 12312719 := bstep (se 1 (by rfl) ⟨9234539, by rfl⟩ : syracuseStep 12312719 = 18469079) B18469079
theorem B8208479 : Blo 1921435 8208479 := bstep (se 1 (by rfl) ⟨6156359, by rfl⟩ : syracuseStep 8208479 = 12312719) B12312719
theorem B5472319 : Blo 1921435 5472319 := bstep (se 1 (by rfl) ⟨4104239, by rfl⟩ : syracuseStep 5472319 = 8208479) B8208479
theorem B7296425 : Blo 1921435 7296425 := bstep (se 2 (by rfl) ⟨2736159, by rfl⟩ : syracuseStep 7296425 = 5472319) B5472319
theorem B4864283 : Blo 1921435 4864283 := bstep (se 1 (by rfl) ⟨3648212, by rfl⟩ : syracuseStep 4864283 = 7296425) B7296425
theorem B3242855 : Blo 1921435 3242855 := bstep (se 1 (by rfl) ⟨2432141, by rfl⟩ : syracuseStep 3242855 = 4864283) B4864283
theorem B2161903 : Blo 1921435 2161903 := bstep (se 1 (by rfl) ⟨1621427, by rfl⟩ : syracuseStep 2161903 = 3242855) B3242855
theorem B2882537 : Blo 1921435 2882537 := bstep (se 2 (by rfl) ⟨1080951, by rfl⟩ : syracuseStep 2882537 = 2161903) B2161903
theorem B1921691 : Blo 1921435 1921691 := bstep (se 1 (by rfl) ⟨1441268, by rfl⟩ : syracuseStep 1921691 = 2882537) B2882537
theorem B6574213 : Blo 1921435 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B8765617 : Blo 1921435 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B11687489 : Blo 1921435 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B7791659 : Blo 1921435 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B5194439 : Blo 1921435 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B3462959 : Blo 1921435 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B9234557 : Blo 1921435 9234557 := bstep (se 3 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 9234557 = 3462959) B3462959
theorem B6156371 : Blo 1921435 6156371 := bstep (se 1 (by rfl) ⟨4617278, by rfl⟩ : syracuseStep 6156371 = 9234557) B9234557
theorem B16416989 : Blo 1921435 16416989 := bstep (se 3 (by rfl) ⟨3078185, by rfl⟩ : syracuseStep 16416989 = 6156371) B6156371
theorem B10944659 : Blo 1921435 10944659 := bstep (se 1 (by rfl) ⟨8208494, by rfl⟩ : syracuseStep 10944659 = 16416989) B16416989
theorem B7296439 : Blo 1921435 7296439 := bstep (se 1 (by rfl) ⟨5472329, by rfl⟩ : syracuseStep 7296439 = 10944659) B10944659
theorem B9728585 : Blo 1921435 9728585 := bstep (se 2 (by rfl) ⟨3648219, by rfl⟩ : syracuseStep 9728585 = 7296439) B7296439
theorem B6485723 : Blo 1921435 6485723 := bstep (se 1 (by rfl) ⟨4864292, by rfl⟩ : syracuseStep 6485723 = 9728585) B9728585
theorem B4323815 : Blo 1921435 4323815 := bstep (se 1 (by rfl) ⟨3242861, by rfl⟩ : syracuseStep 4323815 = 6485723) B6485723
theorem B2882543 : Blo 1921435 2882543 := bstep (se 1 (by rfl) ⟨2161907, by rfl⟩ : syracuseStep 2882543 = 4323815) B4323815
theorem B1921695 : Blo 1921435 1921695 := bstep (se 1 (by rfl) ⟨1441271, by rfl⟩ : syracuseStep 1921695 = 2882543) B2882543
theorem B2882549 : Blo 1921435 2882549 := bbase (se 5 (by rfl) ⟨135119, by rfl⟩ : syracuseStep 2882549 = 270239) (by norm_num)
theorem B1921699 : Blo 1921435 1921699 := bstep (se 1 (by rfl) ⟨1441274, by rfl⟩ : syracuseStep 1921699 = 2882549) B2882549
theorem B9861365 : Blo 1921435 9861365 := bbase (se 5 (by rfl) ⟨462251, by rfl⟩ : syracuseStep 9861365 = 924503) (by norm_num)
theorem B6574243 : Blo 1921435 6574243 := bstep (se 1 (by rfl) ⟨4930682, by rfl⟩ : syracuseStep 6574243 = 9861365) B9861365
theorem B8765657 : Blo 1921435 8765657 := bstep (se 2 (by rfl) ⟨3287121, by rfl⟩ : syracuseStep 8765657 = 6574243) B6574243
theorem B5843771 : Blo 1921435 5843771 := bstep (se 1 (by rfl) ⟨4382828, by rfl⟩ : syracuseStep 5843771 = 8765657) B8765657
theorem B3895847 : Blo 1921435 3895847 := bstep (se 1 (by rfl) ⟨2921885, by rfl⟩ : syracuseStep 3895847 = 5843771) B5843771
theorem B2597231 : Blo 1921435 2597231 := bstep (se 1 (by rfl) ⟨1947923, by rfl⟩ : syracuseStep 2597231 = 3895847) B3895847
theorem B6925949 : Blo 1921435 6925949 := bstep (se 3 (by rfl) ⟨1298615, by rfl⟩ : syracuseStep 6925949 = 2597231) B2597231
theorem B4617299 : Blo 1921435 4617299 := bstep (se 1 (by rfl) ⟨3462974, by rfl⟩ : syracuseStep 4617299 = 6925949) B6925949
theorem B3078199 : Blo 1921435 3078199 := bstep (se 1 (by rfl) ⟨2308649, by rfl⟩ : syracuseStep 3078199 = 4617299) B4617299
theorem B4104265 : Blo 1921435 4104265 := bstep (se 2 (by rfl) ⟨1539099, by rfl⟩ : syracuseStep 4104265 = 3078199) B3078199
theorem B5472353 : Blo 1921435 5472353 := bstep (se 2 (by rfl) ⟨2052132, by rfl⟩ : syracuseStep 5472353 = 4104265) B4104265
theorem B3648235 : Blo 1921435 3648235 := bstep (se 1 (by rfl) ⟨2736176, by rfl⟩ : syracuseStep 3648235 = 5472353) B5472353
theorem B4864313 : Blo 1921435 4864313 := bstep (se 2 (by rfl) ⟨1824117, by rfl⟩ : syracuseStep 4864313 = 3648235) B3648235
theorem B3242875 : Blo 1921435 3242875 := bstep (se 1 (by rfl) ⟨2432156, by rfl⟩ : syracuseStep 3242875 = 4864313) B4864313
theorem B4323833 : Blo 1921435 4323833 := bstep (se 2 (by rfl) ⟨1621437, by rfl⟩ : syracuseStep 4323833 = 3242875) B3242875
theorem B2882555 : Blo 1921435 2882555 := bstep (se 1 (by rfl) ⟨2161916, by rfl⟩ : syracuseStep 2882555 = 4323833) B4323833
theorem B1921703 : Blo 1921435 1921703 := bstep (se 1 (by rfl) ⟨1441277, by rfl⟩ : syracuseStep 1921703 = 2882555) B2882555
theorem B2161921 : Blo 1921435 2161921 := bbase (se 2 (by rfl) ⟨810720, by rfl⟩ : syracuseStep 2161921 = 1621441) (by norm_num)
theorem B2882561 : Blo 1921435 2882561 := bstep (se 2 (by rfl) ⟨1080960, by rfl⟩ : syracuseStep 2882561 = 2161921) B2161921
theorem B1921707 : Blo 1921435 1921707 := bstep (se 1 (by rfl) ⟨1441280, by rfl⟩ : syracuseStep 1921707 = 2882561) B2882561
theorem B4864333 : Blo 1921435 4864333 := bbase (se 3 (by rfl) ⟨912062, by rfl⟩ : syracuseStep 4864333 = 1824125) (by norm_num)
theorem B6485777 : Blo 1921435 6485777 := bstep (se 2 (by rfl) ⟨2432166, by rfl⟩ : syracuseStep 6485777 = 4864333) B4864333
theorem B4323851 : Blo 1921435 4323851 := bstep (se 1 (by rfl) ⟨3242888, by rfl⟩ : syracuseStep 4323851 = 6485777) B6485777
theorem B2882567 : Blo 1921435 2882567 := bstep (se 1 (by rfl) ⟨2161925, by rfl⟩ : syracuseStep 2882567 = 4323851) B4323851
theorem B1921711 : Blo 1921435 1921711 := bstep (se 1 (by rfl) ⟨1441283, by rfl⟩ : syracuseStep 1921711 = 2882567) B2882567
theorem B2882573 : Blo 1921435 2882573 := bbase (se 3 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 2882573 = 1080965) (by norm_num)
theorem B1921715 : Blo 1921435 1921715 := bstep (se 1 (by rfl) ⟨1441286, by rfl⟩ : syracuseStep 1921715 = 2882573) B2882573
theorem B4323869 : Blo 1921435 4323869 := bbase (se 3 (by rfl) ⟨810725, by rfl⟩ : syracuseStep 4323869 = 1621451) (by norm_num)
theorem B2882579 : Blo 1921435 2882579 := bstep (se 1 (by rfl) ⟨2161934, by rfl⟩ : syracuseStep 2882579 = 4323869) B4323869
theorem B1921719 : Blo 1921435 1921719 := bstep (se 1 (by rfl) ⟨1441289, by rfl⟩ : syracuseStep 1921719 = 2882579) B2882579
theorem B3242909 : Blo 1921435 3242909 := bbase (se 3 (by rfl) ⟨608045, by rfl⟩ : syracuseStep 3242909 = 1216091) (by norm_num)
theorem B2161939 : Blo 1921435 2161939 := bstep (se 1 (by rfl) ⟨1621454, by rfl⟩ : syracuseStep 2161939 = 3242909) B3242909
theorem B2882585 : Blo 1921435 2882585 := bstep (se 2 (by rfl) ⟨1080969, by rfl⟩ : syracuseStep 2882585 = 2161939) B2161939
theorem B1921723 : Blo 1921435 1921723 := bstep (se 1 (by rfl) ⟨1441292, by rfl⟩ : syracuseStep 1921723 = 2882585) B2882585
theorem B2191441 : Blo 1921435 2191441 := bbase (se 2 (by rfl) ⟨821790, by rfl⟩ : syracuseStep 2191441 = 1643581) (by norm_num)
theorem B2921921 : Blo 1921435 2921921 := bstep (se 2 (by rfl) ⟨1095720, by rfl⟩ : syracuseStep 2921921 = 2191441) B2191441
theorem B1947947 : Blo 1921435 1947947 := bstep (se 1 (by rfl) ⟨1460960, by rfl⟩ : syracuseStep 1947947 = 2921921) B2921921
theorem B5194525 : Blo 1921435 5194525 := bstep (se 3 (by rfl) ⟨973973, by rfl⟩ : syracuseStep 5194525 = 1947947) B1947947
theorem B6926033 : Blo 1921435 6926033 := bstep (se 2 (by rfl) ⟨2597262, by rfl⟩ : syracuseStep 6926033 = 5194525) B5194525
theorem B18469421 : Blo 1921435 18469421 := bstep (se 3 (by rfl) ⟨3463016, by rfl⟩ : syracuseStep 18469421 = 6926033) B6926033
theorem B12312947 : Blo 1921435 12312947 := bstep (se 1 (by rfl) ⟨9234710, by rfl⟩ : syracuseStep 12312947 = 18469421) B18469421
theorem B8208631 : Blo 1921435 8208631 := bstep (se 1 (by rfl) ⟨6156473, by rfl⟩ : syracuseStep 8208631 = 12312947) B12312947
theorem B10944841 : Blo 1921435 10944841 := bstep (se 2 (by rfl) ⟨4104315, by rfl⟩ : syracuseStep 10944841 = 8208631) B8208631
theorem B14593121 : Blo 1921435 14593121 := bstep (se 2 (by rfl) ⟨5472420, by rfl⟩ : syracuseStep 14593121 = 10944841) B10944841
theorem B9728747 : Blo 1921435 9728747 := bstep (se 1 (by rfl) ⟨7296560, by rfl⟩ : syracuseStep 9728747 = 14593121) B14593121
theorem B6485831 : Blo 1921435 6485831 := bstep (se 1 (by rfl) ⟨4864373, by rfl⟩ : syracuseStep 6485831 = 9728747) B9728747
theorem B4323887 : Blo 1921435 4323887 := bstep (se 1 (by rfl) ⟨3242915, by rfl⟩ : syracuseStep 4323887 = 6485831) B6485831
theorem B2882591 : Blo 1921435 2882591 := bstep (se 1 (by rfl) ⟨2161943, by rfl⟩ : syracuseStep 2882591 = 4323887) B4323887
theorem B1921727 : Blo 1921435 1921727 := bstep (se 1 (by rfl) ⟨1441295, by rfl⟩ : syracuseStep 1921727 = 2882591) B2882591
theorem B2882597 : Blo 1921435 2882597 := bbase (se 4 (by rfl) ⟨270243, by rfl⟩ : syracuseStep 2882597 = 540487) (by norm_num)
theorem B1921731 : Blo 1921435 1921731 := bstep (se 1 (by rfl) ⟨1441298, by rfl⟩ : syracuseStep 1921731 = 2882597) B2882597
theorem B2432197 : Blo 1921435 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B3242929 : Blo 1921435 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B4323905 : Blo 1921435 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B2882603 : Blo 1921435 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B1921735 : Blo 1921435 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B2161957 : Blo 1921435 2161957 := bbase (se 4 (by rfl) ⟨202683, by rfl⟩ : syracuseStep 2161957 = 405367) (by norm_num)
theorem B2882609 : Blo 1921435 2882609 := bstep (se 2 (by rfl) ⟨1080978, by rfl⟩ : syracuseStep 2882609 = 2161957) B2161957
theorem B1921739 : Blo 1921435 1921739 := bstep (se 1 (by rfl) ⟨1441304, by rfl⟩ : syracuseStep 1921739 = 2882609) B2882609
theorem B2597285 : Blo 1921435 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B6926093 : Blo 1921435 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B4617395 : Blo 1921435 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B3078263 : Blo 1921435 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B8208701 : Blo 1921435 8208701 := bstep (se 3 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 8208701 = 3078263) B3078263
theorem B5472467 : Blo 1921435 5472467 := bstep (se 1 (by rfl) ⟨4104350, by rfl⟩ : syracuseStep 5472467 = 8208701) B8208701
theorem B3648311 : Blo 1921435 3648311 := bstep (se 1 (by rfl) ⟨2736233, by rfl⟩ : syracuseStep 3648311 = 5472467) B5472467
theorem B2432207 : Blo 1921435 2432207 := bstep (se 1 (by rfl) ⟨1824155, by rfl⟩ : syracuseStep 2432207 = 3648311) B3648311
theorem B6485885 : Blo 1921435 6485885 := bstep (se 3 (by rfl) ⟨1216103, by rfl⟩ : syracuseStep 6485885 = 2432207) B2432207
theorem B4323923 : Blo 1921435 4323923 := bstep (se 1 (by rfl) ⟨3242942, by rfl⟩ : syracuseStep 4323923 = 6485885) B6485885
theorem B2882615 : Blo 1921435 2882615 := bstep (se 1 (by rfl) ⟨2161961, by rfl⟩ : syracuseStep 2882615 = 4323923) B4323923
theorem B1921743 : Blo 1921435 1921743 := bstep (se 1 (by rfl) ⟨1441307, by rfl⟩ : syracuseStep 1921743 = 2882615) B2882615
theorem B2882621 : Blo 1921435 2882621 := bbase (se 3 (by rfl) ⟨540491, by rfl⟩ : syracuseStep 2882621 = 1080983) (by norm_num)
theorem B1921747 : Blo 1921435 1921747 := bstep (se 1 (by rfl) ⟨1441310, by rfl⟩ : syracuseStep 1921747 = 2882621) B2882621
theorem B4323941 : Blo 1921435 4323941 := bbase (se 4 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 4323941 = 810739) (by norm_num)
theorem B2882627 : Blo 1921435 2882627 := bstep (se 1 (by rfl) ⟨2161970, by rfl⟩ : syracuseStep 2882627 = 4323941) B4323941
theorem B1921751 : Blo 1921435 1921751 := bstep (se 1 (by rfl) ⟨1441313, by rfl⟩ : syracuseStep 1921751 = 2882627) B2882627
theorem B4864445 : Blo 1921435 4864445 := bbase (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) (by norm_num)
theorem B3242963 : Blo 1921435 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B2161975 : Blo 1921435 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B2882633 : Blo 1921435 2882633 := bstep (se 2 (by rfl) ⟨1080987, by rfl⟩ : syracuseStep 2882633 = 2161975) B2161975
theorem B1921755 : Blo 1921435 1921755 := bstep (se 1 (by rfl) ⟨1441316, by rfl⟩ : syracuseStep 1921755 = 2882633) B2882633
theorem B3648341 : Blo 1921435 3648341 := bbase (se 9 (by rfl) ⟨10688, by rfl⟩ : syracuseStep 3648341 = 21377) (by norm_num)
theorem B9728909 : Blo 1921435 9728909 := bstep (se 3 (by rfl) ⟨1824170, by rfl⟩ : syracuseStep 9728909 = 3648341) B3648341
theorem B6485939 : Blo 1921435 6485939 := bstep (se 1 (by rfl) ⟨4864454, by rfl⟩ : syracuseStep 6485939 = 9728909) B9728909
theorem B4323959 : Blo 1921435 4323959 := bstep (se 1 (by rfl) ⟨3242969, by rfl⟩ : syracuseStep 4323959 = 6485939) B6485939
theorem B2882639 : Blo 1921435 2882639 := bstep (se 1 (by rfl) ⟨2161979, by rfl⟩ : syracuseStep 2882639 = 4323959) B4323959
theorem B1921759 : Blo 1921435 1921759 := bstep (se 1 (by rfl) ⟨1441319, by rfl⟩ : syracuseStep 1921759 = 2882639) B2882639
theorem B2882645 : Blo 1921435 2882645 := bbase (se 8 (by rfl) ⟨16890, by rfl⟩ : syracuseStep 2882645 = 33781) (by norm_num)
theorem B1921763 : Blo 1921435 1921763 := bstep (se 1 (by rfl) ⟨1441322, by rfl⟩ : syracuseStep 1921763 = 2882645) B2882645
theorem B12313205 : Blo 1921435 12313205 := bbase (se 5 (by rfl) ⟨577181, by rfl⟩ : syracuseStep 12313205 = 1154363) (by norm_num)
theorem B8208803 : Blo 1921435 8208803 := bstep (se 1 (by rfl) ⟨6156602, by rfl⟩ : syracuseStep 8208803 = 12313205) B12313205
theorem B5472535 : Blo 1921435 5472535 := bstep (se 1 (by rfl) ⟨4104401, by rfl⟩ : syracuseStep 5472535 = 8208803) B8208803
theorem B7296713 : Blo 1921435 7296713 := bstep (se 2 (by rfl) ⟨2736267, by rfl⟩ : syracuseStep 7296713 = 5472535) B5472535
theorem B4864475 : Blo 1921435 4864475 := bstep (se 1 (by rfl) ⟨3648356, by rfl⟩ : syracuseStep 4864475 = 7296713) B7296713
theorem B3242983 : Blo 1921435 3242983 := bstep (se 1 (by rfl) ⟨2432237, by rfl⟩ : syracuseStep 3242983 = 4864475) B4864475
theorem B4323977 : Blo 1921435 4323977 := bstep (se 2 (by rfl) ⟨1621491, by rfl⟩ : syracuseStep 4323977 = 3242983) B3242983
theorem B2882651 : Blo 1921435 2882651 := bstep (se 1 (by rfl) ⟨2161988, by rfl⟩ : syracuseStep 2882651 = 4323977) B4323977
theorem B1921767 : Blo 1921435 1921767 := bstep (se 1 (by rfl) ⟨1441325, by rfl⟩ : syracuseStep 1921767 = 2882651) B2882651
theorem B2161993 : Blo 1921435 2161993 := bbase (se 2 (by rfl) ⟨810747, by rfl⟩ : syracuseStep 2161993 = 1621495) (by norm_num)
theorem B2882657 : Blo 1921435 2882657 := bstep (se 2 (by rfl) ⟨1080996, by rfl⟩ : syracuseStep 2882657 = 2161993) B2161993
theorem B1921771 : Blo 1921435 1921771 := bstep (se 1 (by rfl) ⟨1441328, by rfl⟩ : syracuseStep 1921771 = 2882657) B2882657
theorem B26297941 : Blo 1921435 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B35063921 : Blo 1921435 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B23375947 : Blo 1921435 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B31167929 : Blo 1921435 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B20778619 : Blo 1921435 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B27704825 : Blo 1921435 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B18469883 : Blo 1921435 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B12313255 : Blo 1921435 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B16417673 : Blo 1921435 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B10945115 : Blo 1921435 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B7296743 : Blo 1921435 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B4864495 : Blo 1921435 4864495 := bstep (se 1 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 4864495 = 7296743) B7296743
theorem B6485993 : Blo 1921435 6485993 := bstep (se 2 (by rfl) ⟨2432247, by rfl⟩ : syracuseStep 6485993 = 4864495) B4864495
theorem B4323995 : Blo 1921435 4323995 := bstep (se 1 (by rfl) ⟨3242996, by rfl⟩ : syracuseStep 4323995 = 6485993) B6485993
theorem B2882663 : Blo 1921435 2882663 := bstep (se 1 (by rfl) ⟨2161997, by rfl⟩ : syracuseStep 2882663 = 4323995) B4323995
theorem B1921775 : Blo 1921435 1921775 := bstep (se 1 (by rfl) ⟨1441331, by rfl⟩ : syracuseStep 1921775 = 2882663) B2882663
theorem B2882669 : Blo 1921435 2882669 := bbase (se 3 (by rfl) ⟨540500, by rfl⟩ : syracuseStep 2882669 = 1081001) (by norm_num)
theorem B1921779 : Blo 1921435 1921779 := bstep (se 1 (by rfl) ⟨1441334, by rfl⟩ : syracuseStep 1921779 = 2882669) B2882669
theorem B4324013 : Blo 1921435 4324013 := bbase (se 3 (by rfl) ⟨810752, by rfl⟩ : syracuseStep 4324013 = 1621505) (by norm_num)
theorem B2882675 : Blo 1921435 2882675 := bstep (se 1 (by rfl) ⟨2162006, by rfl⟩ : syracuseStep 2882675 = 4324013) B4324013
theorem B1921783 : Blo 1921435 1921783 := bstep (se 1 (by rfl) ⟨1441337, by rfl⟩ : syracuseStep 1921783 = 2882675) B2882675
theorem B4104445 : Blo 1921435 4104445 := bbase (se 3 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 4104445 = 1539167) (by norm_num)
theorem B5472593 : Blo 1921435 5472593 := bstep (se 2 (by rfl) ⟨2052222, by rfl⟩ : syracuseStep 5472593 = 4104445) B4104445
theorem B3648395 : Blo 1921435 3648395 := bstep (se 1 (by rfl) ⟨2736296, by rfl⟩ : syracuseStep 3648395 = 5472593) B5472593
theorem B2432263 : Blo 1921435 2432263 := bstep (se 1 (by rfl) ⟨1824197, by rfl⟩ : syracuseStep 2432263 = 3648395) B3648395
theorem B3243017 : Blo 1921435 3243017 := bstep (se 2 (by rfl) ⟨1216131, by rfl⟩ : syracuseStep 3243017 = 2432263) B2432263
theorem B2162011 : Blo 1921435 2162011 := bstep (se 1 (by rfl) ⟨1621508, by rfl⟩ : syracuseStep 2162011 = 3243017) B3243017
theorem B2882681 : Blo 1921435 2882681 := bstep (se 2 (by rfl) ⟨1081005, by rfl⟩ : syracuseStep 2882681 = 2162011) B2162011
theorem B1921787 : Blo 1921435 1921787 := bstep (se 1 (by rfl) ⟨1441340, by rfl⟩ : syracuseStep 1921787 = 2882681) B2882681
theorem B8766053 : Blo 1921435 8766053 := bbase (se 4 (by rfl) ⟨821817, by rfl⟩ : syracuseStep 8766053 = 1643635) (by norm_num)
theorem B5844035 : Blo 1921435 5844035 := bstep (se 1 (by rfl) ⟨4383026, by rfl⟩ : syracuseStep 5844035 = 8766053) B8766053
theorem B15584093 : Blo 1921435 15584093 := bstep (se 3 (by rfl) ⟨2922017, by rfl⟩ : syracuseStep 15584093 = 5844035) B5844035
theorem B10389395 : Blo 1921435 10389395 := bstep (se 1 (by rfl) ⟨7792046, by rfl⟩ : syracuseStep 10389395 = 15584093) B15584093
theorem B27705053 : Blo 1921435 27705053 := bstep (se 3 (by rfl) ⟨5194697, by rfl⟩ : syracuseStep 27705053 = 10389395) B10389395
theorem B18470035 : Blo 1921435 18470035 := bstep (se 1 (by rfl) ⟨13852526, by rfl⟩ : syracuseStep 18470035 = 27705053) B27705053
theorem B24626713 : Blo 1921435 24626713 := bstep (se 2 (by rfl) ⟨9235017, by rfl⟩ : syracuseStep 24626713 = 18470035) B18470035
theorem B32835617 : Blo 1921435 32835617 := bstep (se 2 (by rfl) ⟨12313356, by rfl⟩ : syracuseStep 32835617 = 24626713) B24626713
theorem B21890411 : Blo 1921435 21890411 := bstep (se 1 (by rfl) ⟨16417808, by rfl⟩ : syracuseStep 21890411 = 32835617) B32835617
theorem B14593607 : Blo 1921435 14593607 := bstep (se 1 (by rfl) ⟨10945205, by rfl⟩ : syracuseStep 14593607 = 21890411) B21890411
theorem B9729071 : Blo 1921435 9729071 := bstep (se 1 (by rfl) ⟨7296803, by rfl⟩ : syracuseStep 9729071 = 14593607) B14593607
theorem B6486047 : Blo 1921435 6486047 := bstep (se 1 (by rfl) ⟨4864535, by rfl⟩ : syracuseStep 6486047 = 9729071) B9729071
theorem B4324031 : Blo 1921435 4324031 := bstep (se 1 (by rfl) ⟨3243023, by rfl⟩ : syracuseStep 4324031 = 6486047) B6486047
theorem B2882687 : Blo 1921435 2882687 := bstep (se 1 (by rfl) ⟨2162015, by rfl⟩ : syracuseStep 2882687 = 4324031) B4324031
theorem B1921791 : Blo 1921435 1921791 := bstep (se 1 (by rfl) ⟨1441343, by rfl⟩ : syracuseStep 1921791 = 2882687) B2882687
theorem B2882693 : Blo 1921435 2882693 := bbase (se 4 (by rfl) ⟨270252, by rfl⟩ : syracuseStep 2882693 = 540505) (by norm_num)
theorem B1921795 : Blo 1921435 1921795 := bstep (se 1 (by rfl) ⟨1441346, by rfl⟩ : syracuseStep 1921795 = 2882693) B2882693
theorem B3243037 : Blo 1921435 3243037 := bbase (se 3 (by rfl) ⟨608069, by rfl⟩ : syracuseStep 3243037 = 1216139) (by norm_num)
theorem B4324049 : Blo 1921435 4324049 := bstep (se 2 (by rfl) ⟨1621518, by rfl⟩ : syracuseStep 4324049 = 3243037) B3243037
theorem B2882699 : Blo 1921435 2882699 := bstep (se 1 (by rfl) ⟨2162024, by rfl⟩ : syracuseStep 2882699 = 4324049) B4324049
theorem B1921799 : Blo 1921435 1921799 := bstep (se 1 (by rfl) ⟨1441349, by rfl⟩ : syracuseStep 1921799 = 2882699) B2882699
theorem B2162029 : Blo 1921435 2162029 := bbase (se 3 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 2162029 = 810761) (by norm_num)
theorem B2882705 : Blo 1921435 2882705 := bstep (se 2 (by rfl) ⟨1081014, by rfl⟩ : syracuseStep 2882705 = 2162029) B2162029
theorem B1921803 : Blo 1921435 1921803 := bstep (se 1 (by rfl) ⟨1441352, by rfl⟩ : syracuseStep 1921803 = 2882705) B2882705
theorem B6486101 : Blo 1921435 6486101 := bbase (se 8 (by rfl) ⟨38004, by rfl⟩ : syracuseStep 6486101 = 76009) (by norm_num)
theorem B4324067 : Blo 1921435 4324067 := bstep (se 1 (by rfl) ⟨3243050, by rfl⟩ : syracuseStep 4324067 = 6486101) B6486101
theorem B2882711 : Blo 1921435 2882711 := bstep (se 1 (by rfl) ⟨2162033, by rfl⟩ : syracuseStep 2882711 = 4324067) B4324067
theorem B1921807 : Blo 1921435 1921807 := bstep (se 1 (by rfl) ⟨1441355, by rfl⟩ : syracuseStep 1921807 = 2882711) B2882711
theorem B2882717 : Blo 1921435 2882717 := bbase (se 3 (by rfl) ⟨540509, by rfl⟩ : syracuseStep 2882717 = 1081019) (by norm_num)
theorem B1921811 : Blo 1921435 1921811 := bstep (se 1 (by rfl) ⟨1441358, by rfl⟩ : syracuseStep 1921811 = 2882717) B2882717
theorem B4324085 : Blo 1921435 4324085 := bbase (se 5 (by rfl) ⟨202691, by rfl⟩ : syracuseStep 4324085 = 405383) (by norm_num)
theorem B2882723 : Blo 1921435 2882723 := bstep (se 1 (by rfl) ⟨2162042, by rfl⟩ : syracuseStep 2882723 = 4324085) B4324085
theorem B1921815 : Blo 1921435 1921815 := bstep (se 1 (by rfl) ⟨1441361, by rfl⟩ : syracuseStep 1921815 = 2882723) B2882723
theorem B11688245 : Blo 1921435 11688245 := bbase (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) (by norm_num)
theorem B7792163 : Blo 1921435 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B5194775 : Blo 1921435 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B3463183 : Blo 1921435 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B4617577 : Blo 1921435 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B24627077 : Blo 1921435 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B16418051 : Blo 1921435 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B10945367 : Blo 1921435 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B7296911 : Blo 1921435 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B4864607 : Blo 1921435 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B3243071 : Blo 1921435 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B2162047 : Blo 1921435 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B2882729 : Blo 1921435 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B1921819 : Blo 1921435 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B1948045 : Blo 1921435 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B2597393 : Blo 1921435 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B6926381 : Blo 1921435 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B4617587 : Blo 1921435 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B3078391 : Blo 1921435 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B4104521 : Blo 1921435 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B2736347 : Blo 1921435 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B7296925 : Blo 1921435 7296925 := bstep (se 3 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 7296925 = 2736347) B2736347
theorem B9729233 : Blo 1921435 9729233 := bstep (se 2 (by rfl) ⟨3648462, by rfl⟩ : syracuseStep 9729233 = 7296925) B7296925
theorem B6486155 : Blo 1921435 6486155 := bstep (se 1 (by rfl) ⟨4864616, by rfl⟩ : syracuseStep 6486155 = 9729233) B9729233
theorem B4324103 : Blo 1921435 4324103 := bstep (se 1 (by rfl) ⟨3243077, by rfl⟩ : syracuseStep 4324103 = 6486155) B6486155
theorem B2882735 : Blo 1921435 2882735 := bstep (se 1 (by rfl) ⟨2162051, by rfl⟩ : syracuseStep 2882735 = 4324103) B4324103
theorem B1921823 : Blo 1921435 1921823 := bstep (se 1 (by rfl) ⟨1441367, by rfl⟩ : syracuseStep 1921823 = 2882735) B2882735
theorem B2882741 : Blo 1921435 2882741 := bbase (se 5 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 2882741 = 270257) (by norm_num)
theorem B1921827 : Blo 1921435 1921827 := bstep (se 1 (by rfl) ⟨1441370, by rfl⟩ : syracuseStep 1921827 = 2882741) B2882741
theorem B4864637 : Blo 1921435 4864637 := bbase (se 3 (by rfl) ⟨912119, by rfl⟩ : syracuseStep 4864637 = 1824239) (by norm_num)
theorem B3243091 : Blo 1921435 3243091 := bstep (se 1 (by rfl) ⟨2432318, by rfl⟩ : syracuseStep 3243091 = 4864637) B4864637
theorem B4324121 : Blo 1921435 4324121 := bstep (se 2 (by rfl) ⟨1621545, by rfl⟩ : syracuseStep 4324121 = 3243091) B3243091
theorem B2882747 : Blo 1921435 2882747 := bstep (se 1 (by rfl) ⟨2162060, by rfl⟩ : syracuseStep 2882747 = 4324121) B4324121
theorem B1921831 : Blo 1921435 1921831 := bstep (se 1 (by rfl) ⟨1441373, by rfl⟩ : syracuseStep 1921831 = 2882747) B2882747
theorem B2162065 : Blo 1921435 2162065 := bbase (se 2 (by rfl) ⟨810774, by rfl⟩ : syracuseStep 2162065 = 1621549) (by norm_num)
theorem B2882753 : Blo 1921435 2882753 := bstep (se 2 (by rfl) ⟨1081032, by rfl⟩ : syracuseStep 2882753 = 2162065) B2162065
theorem B1921835 : Blo 1921435 1921835 := bstep (se 1 (by rfl) ⟨1441376, by rfl⟩ : syracuseStep 1921835 = 2882753) B2882753
theorem B3648493 : Blo 1921435 3648493 := bbase (se 3 (by rfl) ⟨684092, by rfl⟩ : syracuseStep 3648493 = 1368185) (by norm_num)
theorem B4864657 : Blo 1921435 4864657 := bstep (se 2 (by rfl) ⟨1824246, by rfl⟩ : syracuseStep 4864657 = 3648493) B3648493
theorem B6486209 : Blo 1921435 6486209 := bstep (se 2 (by rfl) ⟨2432328, by rfl⟩ : syracuseStep 6486209 = 4864657) B4864657
theorem B4324139 : Blo 1921435 4324139 := bstep (se 1 (by rfl) ⟨3243104, by rfl⟩ : syracuseStep 4324139 = 6486209) B6486209
theorem B2882759 : Blo 1921435 2882759 := bstep (se 1 (by rfl) ⟨2162069, by rfl⟩ : syracuseStep 2882759 = 4324139) B4324139
theorem B1921839 : Blo 1921435 1921839 := bstep (se 1 (by rfl) ⟨1441379, by rfl⟩ : syracuseStep 1921839 = 2882759) B2882759
theorem B2882765 : Blo 1921435 2882765 := bbase (se 3 (by rfl) ⟨540518, by rfl⟩ : syracuseStep 2882765 = 1081037) (by norm_num)
theorem B1921843 : Blo 1921435 1921843 := bstep (se 1 (by rfl) ⟨1441382, by rfl⟩ : syracuseStep 1921843 = 2882765) B2882765
theorem B4324157 : Blo 1921435 4324157 := bbase (se 3 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 4324157 = 1621559) (by norm_num)
theorem B2882771 : Blo 1921435 2882771 := bstep (se 1 (by rfl) ⟨2162078, by rfl⟩ : syracuseStep 2882771 = 4324157) B4324157
theorem B1921847 : Blo 1921435 1921847 := bstep (se 1 (by rfl) ⟨1441385, by rfl⟩ : syracuseStep 1921847 = 2882771) B2882771
theorem B3243125 : Blo 1921435 3243125 := bbase (se 5 (by rfl) ⟨152021, by rfl⟩ : syracuseStep 3243125 = 304043) (by norm_num)
theorem B2162083 : Blo 1921435 2162083 := bstep (se 1 (by rfl) ⟨1621562, by rfl⟩ : syracuseStep 2162083 = 3243125) B3243125
theorem B2882777 : Blo 1921435 2882777 := bstep (se 2 (by rfl) ⟨1081041, by rfl⟩ : syracuseStep 2882777 = 2162083) B2162083
theorem B1921851 : Blo 1921435 1921851 := bstep (se 1 (by rfl) ⟨1441388, by rfl⟩ : syracuseStep 1921851 = 2882777) B2882777
theorem B4104589 : Blo 1921435 4104589 := bbase (se 3 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 4104589 = 1539221) (by norm_num)
theorem B5472785 : Blo 1921435 5472785 := bstep (se 2 (by rfl) ⟨2052294, by rfl⟩ : syracuseStep 5472785 = 4104589) B4104589
theorem B14594093 : Blo 1921435 14594093 := bstep (se 3 (by rfl) ⟨2736392, by rfl⟩ : syracuseStep 14594093 = 5472785) B5472785
theorem B9729395 : Blo 1921435 9729395 := bstep (se 1 (by rfl) ⟨7297046, by rfl⟩ : syracuseStep 9729395 = 14594093) B14594093
theorem B6486263 : Blo 1921435 6486263 := bstep (se 1 (by rfl) ⟨4864697, by rfl⟩ : syracuseStep 6486263 = 9729395) B9729395
theorem B4324175 : Blo 1921435 4324175 := bstep (se 1 (by rfl) ⟨3243131, by rfl⟩ : syracuseStep 4324175 = 6486263) B6486263
theorem B2882783 : Blo 1921435 2882783 := bstep (se 1 (by rfl) ⟨2162087, by rfl⟩ : syracuseStep 2882783 = 4324175) B4324175
theorem B1921855 : Blo 1921435 1921855 := bstep (se 1 (by rfl) ⟨1441391, by rfl⟩ : syracuseStep 1921855 = 2882783) B2882783
theorem B2882789 : Blo 1921435 2882789 := bbase (se 4 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 2882789 = 540523) (by norm_num)
theorem B1921859 : Blo 1921435 1921859 := bstep (se 1 (by rfl) ⟨1441394, by rfl⟩ : syracuseStep 1921859 = 2882789) B2882789
theorem B4680685 : Blo 1921435 4680685 := bbase (se 3 (by rfl) ⟨877628, by rfl⟩ : syracuseStep 4680685 = 1755257) (by norm_num)
theorem B24963653 : Blo 1921435 24963653 := bstep (se 4 (by rfl) ⟨2340342, by rfl⟩ : syracuseStep 24963653 = 4680685) B4680685
theorem B16642435 : Blo 1921435 16642435 := bstep (se 1 (by rfl) ⟨12481826, by rfl⟩ : syracuseStep 16642435 = 24963653) B24963653
theorem B22189913 : Blo 1921435 22189913 := bstep (se 2 (by rfl) ⟨8321217, by rfl⟩ : syracuseStep 22189913 = 16642435) B16642435
theorem B14793275 : Blo 1921435 14793275 := bstep (se 1 (by rfl) ⟨11094956, by rfl⟩ : syracuseStep 14793275 = 22189913) B22189913
theorem B9862183 : Blo 1921435 9862183 := bstep (se 1 (by rfl) ⟨7396637, by rfl⟩ : syracuseStep 9862183 = 14793275) B14793275
theorem B13149577 : Blo 1921435 13149577 := bstep (se 2 (by rfl) ⟨4931091, by rfl⟩ : syracuseStep 13149577 = 9862183) B9862183
theorem B17532769 : Blo 1921435 17532769 := bstep (se 2 (by rfl) ⟨6574788, by rfl⟩ : syracuseStep 17532769 = 13149577) B13149577
theorem B23377025 : Blo 1921435 23377025 := bstep (se 2 (by rfl) ⟨8766384, by rfl⟩ : syracuseStep 23377025 = 17532769) B17532769
theorem B15584683 : Blo 1921435 15584683 := bstep (se 1 (by rfl) ⟨11688512, by rfl⟩ : syracuseStep 15584683 = 23377025) B23377025
theorem B20779577 : Blo 1921435 20779577 := bstep (se 2 (by rfl) ⟨7792341, by rfl⟩ : syracuseStep 20779577 = 15584683) B15584683
theorem B13853051 : Blo 1921435 13853051 := bstep (se 1 (by rfl) ⟨10389788, by rfl⟩ : syracuseStep 13853051 = 20779577) B20779577
theorem B9235367 : Blo 1921435 9235367 := bstep (se 1 (by rfl) ⟨6926525, by rfl⟩ : syracuseStep 9235367 = 13853051) B13853051
theorem B6156911 : Blo 1921435 6156911 := bstep (se 1 (by rfl) ⟨4617683, by rfl⟩ : syracuseStep 6156911 = 9235367) B9235367
theorem B4104607 : Blo 1921435 4104607 := bstep (se 1 (by rfl) ⟨3078455, by rfl⟩ : syracuseStep 4104607 = 6156911) B6156911
theorem B5472809 : Blo 1921435 5472809 := bstep (se 2 (by rfl) ⟨2052303, by rfl⟩ : syracuseStep 5472809 = 4104607) B4104607
theorem B3648539 : Blo 1921435 3648539 := bstep (se 1 (by rfl) ⟨2736404, by rfl⟩ : syracuseStep 3648539 = 5472809) B5472809
theorem B2432359 : Blo 1921435 2432359 := bstep (se 1 (by rfl) ⟨1824269, by rfl⟩ : syracuseStep 2432359 = 3648539) B3648539
theorem B3243145 : Blo 1921435 3243145 := bstep (se 2 (by rfl) ⟨1216179, by rfl⟩ : syracuseStep 3243145 = 2432359) B2432359
theorem B4324193 : Blo 1921435 4324193 := bstep (se 2 (by rfl) ⟨1621572, by rfl⟩ : syracuseStep 4324193 = 3243145) B3243145
theorem B2882795 : Blo 1921435 2882795 := bstep (se 1 (by rfl) ⟨2162096, by rfl⟩ : syracuseStep 2882795 = 4324193) B4324193
theorem B1921863 : Blo 1921435 1921863 := bstep (se 1 (by rfl) ⟨1441397, by rfl⟩ : syracuseStep 1921863 = 2882795) B2882795
theorem B2162101 : Blo 1921435 2162101 := bbase (se 5 (by rfl) ⟨101348, by rfl⟩ : syracuseStep 2162101 = 202697) (by norm_num)
theorem B2882801 : Blo 1921435 2882801 := bstep (se 2 (by rfl) ⟨1081050, by rfl⟩ : syracuseStep 2882801 = 2162101) B2162101
theorem B1921867 : Blo 1921435 1921867 := bstep (se 1 (by rfl) ⟨1441400, by rfl⟩ : syracuseStep 1921867 = 2882801) B2882801
theorem B2432369 : Blo 1921435 2432369 := bbase (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) (by norm_num)
theorem B6486317 : Blo 1921435 6486317 := bstep (se 3 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 6486317 = 2432369) B2432369
theorem B4324211 : Blo 1921435 4324211 := bstep (se 1 (by rfl) ⟨3243158, by rfl⟩ : syracuseStep 4324211 = 6486317) B6486317
theorem B2882807 : Blo 1921435 2882807 := bstep (se 1 (by rfl) ⟨2162105, by rfl⟩ : syracuseStep 2882807 = 4324211) B4324211
theorem B1921871 : Blo 1921435 1921871 := bstep (se 1 (by rfl) ⟨1441403, by rfl⟩ : syracuseStep 1921871 = 2882807) B2882807
theorem B2882813 : Blo 1921435 2882813 := bbase (se 3 (by rfl) ⟨540527, by rfl⟩ : syracuseStep 2882813 = 1081055) (by norm_num)
theorem B1921875 : Blo 1921435 1921875 := bstep (se 1 (by rfl) ⟨1441406, by rfl⟩ : syracuseStep 1921875 = 2882813) B2882813
theorem B4324229 : Blo 1921435 4324229 := bbase (se 4 (by rfl) ⟨405396, by rfl⟩ : syracuseStep 4324229 = 810793) (by norm_num)
theorem B2882819 : Blo 1921435 2882819 := bstep (se 1 (by rfl) ⟨2162114, by rfl⟩ : syracuseStep 2882819 = 4324229) B4324229
theorem B1921879 : Blo 1921435 1921879 := bstep (se 1 (by rfl) ⟨1441409, by rfl⟩ : syracuseStep 1921879 = 2882819) B2882819
theorem B2052325 : Blo 1921435 2052325 := bbase (se 4 (by rfl) ⟨192405, by rfl⟩ : syracuseStep 2052325 = 384811) (by norm_num)
theorem B2736433 : Blo 1921435 2736433 := bstep (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) B2052325
theorem B3648577 : Blo 1921435 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B4864769 : Blo 1921435 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B3243179 : Blo 1921435 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B2162119 : Blo 1921435 2162119 := bstep (se 1 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 2162119 = 3243179) B3243179
theorem B2882825 : Blo 1921435 2882825 := bstep (se 2 (by rfl) ⟨1081059, by rfl⟩ : syracuseStep 2882825 = 2162119) B2162119
theorem B1921883 : Blo 1921435 1921883 := bstep (se 1 (by rfl) ⟨1441412, by rfl⟩ : syracuseStep 1921883 = 2882825) B2882825
theorem B9729557 : Blo 1921435 9729557 := bbase (se 6 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 9729557 = 456073) (by norm_num)
theorem B6486371 : Blo 1921435 6486371 := bstep (se 1 (by rfl) ⟨4864778, by rfl⟩ : syracuseStep 6486371 = 9729557) B9729557
theorem B4324247 : Blo 1921435 4324247 := bstep (se 1 (by rfl) ⟨3243185, by rfl⟩ : syracuseStep 4324247 = 6486371) B6486371
theorem B2882831 : Blo 1921435 2882831 := bstep (se 1 (by rfl) ⟨2162123, by rfl⟩ : syracuseStep 2882831 = 4324247) B4324247
theorem B1921887 : Blo 1921435 1921887 := bstep (se 1 (by rfl) ⟨1441415, by rfl⟩ : syracuseStep 1921887 = 2882831) B2882831
theorem B2882837 : Blo 1921435 2882837 := bbase (se 6 (by rfl) ⟨67566, by rfl⟩ : syracuseStep 2882837 = 135133) (by norm_num)
theorem B1921891 : Blo 1921435 1921891 := bstep (se 1 (by rfl) ⟨1441418, by rfl⟩ : syracuseStep 1921891 = 2882837) B2882837
theorem B16642709 : Blo 1921435 16642709 := bbase (se 6 (by rfl) ⟨390063, by rfl⟩ : syracuseStep 16642709 = 780127) (by norm_num)
theorem B11095139 : Blo 1921435 11095139 := bstep (se 1 (by rfl) ⟨8321354, by rfl⟩ : syracuseStep 11095139 = 16642709) B16642709
theorem B7396759 : Blo 1921435 7396759 := bstep (se 1 (by rfl) ⟨5547569, by rfl⟩ : syracuseStep 7396759 = 11095139) B11095139
theorem B9862345 : Blo 1921435 9862345 := bstep (se 2 (by rfl) ⟨3698379, by rfl⟩ : syracuseStep 9862345 = 7396759) B7396759
theorem B13149793 : Blo 1921435 13149793 := bstep (se 2 (by rfl) ⟨4931172, by rfl⟩ : syracuseStep 13149793 = 9862345) B9862345
theorem B17533057 : Blo 1921435 17533057 := bstep (se 2 (by rfl) ⟨6574896, by rfl⟩ : syracuseStep 17533057 = 13149793) B13149793
theorem B23377409 : Blo 1921435 23377409 := bstep (se 2 (by rfl) ⟨8766528, by rfl⟩ : syracuseStep 23377409 = 17533057) B17533057
theorem B15584939 : Blo 1921435 15584939 := bstep (se 1 (by rfl) ⟨11688704, by rfl⟩ : syracuseStep 15584939 = 23377409) B23377409
theorem B10389959 : Blo 1921435 10389959 := bstep (se 1 (by rfl) ⟨7792469, by rfl⟩ : syracuseStep 10389959 = 15584939) B15584939
theorem B6926639 : Blo 1921435 6926639 := bstep (se 1 (by rfl) ⟨5194979, by rfl⟩ : syracuseStep 6926639 = 10389959) B10389959
theorem B18471037 : Blo 1921435 18471037 := bstep (se 3 (by rfl) ⟨3463319, by rfl⟩ : syracuseStep 18471037 = 6926639) B6926639
theorem B24628049 : Blo 1921435 24628049 := bstep (se 2 (by rfl) ⟨9235518, by rfl⟩ : syracuseStep 24628049 = 18471037) B18471037
theorem B16418699 : Blo 1921435 16418699 := bstep (se 1 (by rfl) ⟨12314024, by rfl⟩ : syracuseStep 16418699 = 24628049) B24628049
theorem B10945799 : Blo 1921435 10945799 := bstep (se 1 (by rfl) ⟨8209349, by rfl⟩ : syracuseStep 10945799 = 16418699) B16418699
theorem B7297199 : Blo 1921435 7297199 := bstep (se 1 (by rfl) ⟨5472899, by rfl⟩ : syracuseStep 7297199 = 10945799) B10945799
theorem B4864799 : Blo 1921435 4864799 := bstep (se 1 (by rfl) ⟨3648599, by rfl⟩ : syracuseStep 4864799 = 7297199) B7297199
theorem B3243199 : Blo 1921435 3243199 := bstep (se 1 (by rfl) ⟨2432399, by rfl⟩ : syracuseStep 3243199 = 4864799) B4864799
theorem B4324265 : Blo 1921435 4324265 := bstep (se 2 (by rfl) ⟨1621599, by rfl⟩ : syracuseStep 4324265 = 3243199) B3243199
theorem B2882843 : Blo 1921435 2882843 := bstep (se 1 (by rfl) ⟨2162132, by rfl⟩ : syracuseStep 2882843 = 4324265) B4324265
theorem B1921895 : Blo 1921435 1921895 := bstep (se 1 (by rfl) ⟨1441421, by rfl⟩ : syracuseStep 1921895 = 2882843) B2882843
theorem B2162137 : Blo 1921435 2162137 := bbase (se 2 (by rfl) ⟨810801, by rfl⟩ : syracuseStep 2162137 = 1621603) (by norm_num)
theorem B2882849 : Blo 1921435 2882849 := bstep (se 2 (by rfl) ⟨1081068, by rfl⟩ : syracuseStep 2882849 = 2162137) B2162137
theorem B1921899 : Blo 1921435 1921899 := bstep (se 1 (by rfl) ⟨1441424, by rfl⟩ : syracuseStep 1921899 = 2882849) B2882849
theorem B2736461 : Blo 1921435 2736461 := bbase (se 3 (by rfl) ⟨513086, by rfl⟩ : syracuseStep 2736461 = 1026173) (by norm_num)
theorem B7297229 : Blo 1921435 7297229 := bstep (se 3 (by rfl) ⟨1368230, by rfl⟩ : syracuseStep 7297229 = 2736461) B2736461
theorem B4864819 : Blo 1921435 4864819 := bstep (se 1 (by rfl) ⟨3648614, by rfl⟩ : syracuseStep 4864819 = 7297229) B7297229
theorem B6486425 : Blo 1921435 6486425 := bstep (se 2 (by rfl) ⟨2432409, by rfl⟩ : syracuseStep 6486425 = 4864819) B4864819
theorem B4324283 : Blo 1921435 4324283 := bstep (se 1 (by rfl) ⟨3243212, by rfl⟩ : syracuseStep 4324283 = 6486425) B6486425
theorem B2882855 : Blo 1921435 2882855 := bstep (se 1 (by rfl) ⟨2162141, by rfl⟩ : syracuseStep 2882855 = 4324283) B4324283
theorem B1921903 : Blo 1921435 1921903 := bstep (se 1 (by rfl) ⟨1441427, by rfl⟩ : syracuseStep 1921903 = 2882855) B2882855
theorem B2882861 : Blo 1921435 2882861 := bbase (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) (by norm_num)
theorem B1921907 : Blo 1921435 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B4324301 : Blo 1921435 4324301 := bbase (se 3 (by rfl) ⟨810806, by rfl⟩ : syracuseStep 4324301 = 1621613) (by norm_num)
theorem B2882867 : Blo 1921435 2882867 := bstep (se 1 (by rfl) ⟨2162150, by rfl⟩ : syracuseStep 2882867 = 4324301) B4324301
theorem B1921911 : Blo 1921435 1921911 := bstep (se 1 (by rfl) ⟨1441433, by rfl⟩ : syracuseStep 1921911 = 2882867) B2882867
theorem B2432425 : Blo 1921435 2432425 := bbase (se 2 (by rfl) ⟨912159, by rfl⟩ : syracuseStep 2432425 = 1824319) (by norm_num)
theorem B3243233 : Blo 1921435 3243233 := bstep (se 2 (by rfl) ⟨1216212, by rfl⟩ : syracuseStep 3243233 = 2432425) B2432425
theorem B2162155 : Blo 1921435 2162155 := bstep (se 1 (by rfl) ⟨1621616, by rfl⟩ : syracuseStep 2162155 = 3243233) B3243233
theorem B2882873 : Blo 1921435 2882873 := bstep (se 2 (by rfl) ⟨1081077, by rfl⟩ : syracuseStep 2882873 = 2162155) B2162155
theorem B1921915 : Blo 1921435 1921915 := bstep (se 1 (by rfl) ⟨1441436, by rfl⟩ : syracuseStep 1921915 = 2882873) B2882873
theorem B6926725 : Blo 1921435 6926725 := bbase (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) (by norm_num)
theorem B9235633 : Blo 1921435 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B12314177 : Blo 1921435 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B8209451 : Blo 1921435 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B21891869 : Blo 1921435 21891869 := bstep (se 3 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 21891869 = 8209451) B8209451
theorem B14594579 : Blo 1921435 14594579 := bstep (se 1 (by rfl) ⟨10945934, by rfl⟩ : syracuseStep 14594579 = 21891869) B21891869
theorem B9729719 : Blo 1921435 9729719 := bstep (se 1 (by rfl) ⟨7297289, by rfl⟩ : syracuseStep 9729719 = 14594579) B14594579
theorem B6486479 : Blo 1921435 6486479 := bstep (se 1 (by rfl) ⟨4864859, by rfl⟩ : syracuseStep 6486479 = 9729719) B9729719
theorem B4324319 : Blo 1921435 4324319 := bstep (se 1 (by rfl) ⟨3243239, by rfl⟩ : syracuseStep 4324319 = 6486479) B6486479
theorem B2882879 : Blo 1921435 2882879 := bstep (se 1 (by rfl) ⟨2162159, by rfl⟩ : syracuseStep 2882879 = 4324319) B4324319
theorem B1921919 : Blo 1921435 1921919 := bstep (se 1 (by rfl) ⟨1441439, by rfl⟩ : syracuseStep 1921919 = 2882879) B2882879
theorem B2882885 : Blo 1921435 2882885 := bbase (se 4 (by rfl) ⟨270270, by rfl⟩ : syracuseStep 2882885 = 540541) (by norm_num)
theorem B1921923 : Blo 1921435 1921923 := bstep (se 1 (by rfl) ⟨1441442, by rfl⟩ : syracuseStep 1921923 = 2882885) B2882885
theorem B3243253 : Blo 1921435 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B4324337 : Blo 1921435 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2882891 : Blo 1921435 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B1921927 : Blo 1921435 1921927 := bstep (se 1 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 1921927 = 2882891) B2882891
theorem B2162173 : Blo 1921435 2162173 := bbase (se 3 (by rfl) ⟨405407, by rfl⟩ : syracuseStep 2162173 = 810815) (by norm_num)
theorem B2882897 : Blo 1921435 2882897 := bstep (se 2 (by rfl) ⟨1081086, by rfl⟩ : syracuseStep 2882897 = 2162173) B2162173
theorem B1921931 : Blo 1921435 1921931 := bstep (se 1 (by rfl) ⟨1441448, by rfl⟩ : syracuseStep 1921931 = 2882897) B2882897
theorem B6486533 : Blo 1921435 6486533 := bbase (se 4 (by rfl) ⟨608112, by rfl⟩ : syracuseStep 6486533 = 1216225) (by norm_num)
theorem B4324355 : Blo 1921435 4324355 := bstep (se 1 (by rfl) ⟨3243266, by rfl⟩ : syracuseStep 4324355 = 6486533) B6486533
theorem B2882903 : Blo 1921435 2882903 := bstep (se 1 (by rfl) ⟨2162177, by rfl⟩ : syracuseStep 2882903 = 4324355) B4324355
theorem B1921935 : Blo 1921435 1921935 := bstep (se 1 (by rfl) ⟨1441451, by rfl⟩ : syracuseStep 1921935 = 2882903) B2882903
theorem B2882909 : Blo 1921435 2882909 := bbase (se 3 (by rfl) ⟨540545, by rfl⟩ : syracuseStep 2882909 = 1081091) (by norm_num)
theorem B1921939 : Blo 1921435 1921939 := bstep (se 1 (by rfl) ⟨1441454, by rfl⟩ : syracuseStep 1921939 = 2882909) B2882909
theorem B4324373 : Blo 1921435 4324373 := bbase (se 6 (by rfl) ⟨101352, by rfl⟩ : syracuseStep 4324373 = 202705) (by norm_num)
theorem B2882915 : Blo 1921435 2882915 := bstep (se 1 (by rfl) ⟨2162186, by rfl⟩ : syracuseStep 2882915 = 4324373) B4324373
theorem B1921943 : Blo 1921435 1921943 := bstep (se 1 (by rfl) ⟨1441457, by rfl⟩ : syracuseStep 1921943 = 2882915) B2882915
theorem B7297397 : Blo 1921435 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B4864931 : Blo 1921435 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B3243287 : Blo 1921435 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B2162191 : Blo 1921435 2162191 := bstep (se 1 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 2162191 = 3243287) B3243287
theorem B2882921 : Blo 1921435 2882921 := bstep (se 2 (by rfl) ⟨1081095, by rfl⟩ : syracuseStep 2882921 = 2162191) B2162191
theorem B1921947 : Blo 1921435 1921947 := bstep (se 1 (by rfl) ⟨1441460, by rfl⟩ : syracuseStep 1921947 = 2882921) B2882921
theorem B2052397 : Blo 1921435 2052397 := bbase (se 3 (by rfl) ⟨384824, by rfl⟩ : syracuseStep 2052397 = 769649) (by norm_num)
theorem B10946117 : Blo 1921435 10946117 := bstep (se 4 (by rfl) ⟨1026198, by rfl⟩ : syracuseStep 10946117 = 2052397) B2052397
theorem B7297411 : Blo 1921435 7297411 := bstep (se 1 (by rfl) ⟨5473058, by rfl⟩ : syracuseStep 7297411 = 10946117) B10946117
theorem B9729881 : Blo 1921435 9729881 := bstep (se 2 (by rfl) ⟨3648705, by rfl⟩ : syracuseStep 9729881 = 7297411) B7297411
theorem B6486587 : Blo 1921435 6486587 := bstep (se 1 (by rfl) ⟨4864940, by rfl⟩ : syracuseStep 6486587 = 9729881) B9729881
theorem B4324391 : Blo 1921435 4324391 := bstep (se 1 (by rfl) ⟨3243293, by rfl⟩ : syracuseStep 4324391 = 6486587) B6486587
theorem B2882927 : Blo 1921435 2882927 := bstep (se 1 (by rfl) ⟨2162195, by rfl⟩ : syracuseStep 2882927 = 4324391) B4324391
theorem B1921951 : Blo 1921435 1921951 := bstep (se 1 (by rfl) ⟨1441463, by rfl⟩ : syracuseStep 1921951 = 2882927) B2882927
theorem B2882933 : Blo 1921435 2882933 := bbase (se 5 (by rfl) ⟨135137, by rfl⟩ : syracuseStep 2882933 = 270275) (by norm_num)
theorem B1921955 : Blo 1921435 1921955 := bstep (se 1 (by rfl) ⟨1441466, by rfl⟩ : syracuseStep 1921955 = 2882933) B2882933
theorem B2736541 : Blo 1921435 2736541 := bbase (se 3 (by rfl) ⟨513101, by rfl⟩ : syracuseStep 2736541 = 1026203) (by norm_num)
theorem B3648721 : Blo 1921435 3648721 := bstep (se 2 (by rfl) ⟨1368270, by rfl⟩ : syracuseStep 3648721 = 2736541) B2736541
theorem B4864961 : Blo 1921435 4864961 := bstep (se 2 (by rfl) ⟨1824360, by rfl⟩ : syracuseStep 4864961 = 3648721) B3648721
theorem B3243307 : Blo 1921435 3243307 := bstep (se 1 (by rfl) ⟨2432480, by rfl⟩ : syracuseStep 3243307 = 4864961) B4864961
theorem B4324409 : Blo 1921435 4324409 := bstep (se 2 (by rfl) ⟨1621653, by rfl⟩ : syracuseStep 4324409 = 3243307) B3243307
theorem B2882939 : Blo 1921435 2882939 := bstep (se 1 (by rfl) ⟨2162204, by rfl⟩ : syracuseStep 2882939 = 4324409) B4324409
theorem B1921959 : Blo 1921435 1921959 := bstep (se 1 (by rfl) ⟨1441469, by rfl⟩ : syracuseStep 1921959 = 2882939) B2882939
theorem B2162209 : Blo 1921435 2162209 := bbase (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) (by norm_num)
theorem B2882945 : Blo 1921435 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B1921963 : Blo 1921435 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B4864981 : Blo 1921435 4864981 := bbase (se 7 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 4864981 = 114023) (by norm_num)
theorem B6486641 : Blo 1921435 6486641 := bstep (se 2 (by rfl) ⟨2432490, by rfl⟩ : syracuseStep 6486641 = 4864981) B4864981
theorem B4324427 : Blo 1921435 4324427 := bstep (se 1 (by rfl) ⟨3243320, by rfl⟩ : syracuseStep 4324427 = 6486641) B6486641
theorem B2882951 : Blo 1921435 2882951 := bstep (se 1 (by rfl) ⟨2162213, by rfl⟩ : syracuseStep 2882951 = 4324427) B4324427
theorem B1921967 : Blo 1921435 1921967 := bstep (se 1 (by rfl) ⟨1441475, by rfl⟩ : syracuseStep 1921967 = 2882951) B2882951
theorem B2882957 : Blo 1921435 2882957 := bbase (se 3 (by rfl) ⟨540554, by rfl⟩ : syracuseStep 2882957 = 1081109) (by norm_num)
theorem B1921971 : Blo 1921435 1921971 := bstep (se 1 (by rfl) ⟨1441478, by rfl⟩ : syracuseStep 1921971 = 2882957) B2882957
theorem B4324445 : Blo 1921435 4324445 := bbase (se 3 (by rfl) ⟨810833, by rfl⟩ : syracuseStep 4324445 = 1621667) (by norm_num)
theorem B2882963 : Blo 1921435 2882963 := bstep (se 1 (by rfl) ⟨2162222, by rfl⟩ : syracuseStep 2882963 = 4324445) B4324445
theorem B1921975 : Blo 1921435 1921975 := bstep (se 1 (by rfl) ⟨1441481, by rfl⟩ : syracuseStep 1921975 = 2882963) B2882963
theorem B3243341 : Blo 1921435 3243341 := bbase (se 3 (by rfl) ⟨608126, by rfl⟩ : syracuseStep 3243341 = 1216253) (by norm_num)
theorem B2162227 : Blo 1921435 2162227 := bstep (se 1 (by rfl) ⟨1621670, by rfl⟩ : syracuseStep 2162227 = 3243341) B3243341
theorem B2882969 : Blo 1921435 2882969 := bstep (se 2 (by rfl) ⟨1081113, by rfl⟩ : syracuseStep 2882969 = 2162227) B2162227
theorem B1921979 : Blo 1921435 1921979 := bstep (se 1 (by rfl) ⟨1441484, by rfl⟩ : syracuseStep 1921979 = 2882969) B2882969
theorem B3698549 : Blo 1921435 3698549 := bbase (se 5 (by rfl) ⟨173369, by rfl⟩ : syracuseStep 3698549 = 346739) (by norm_num)
theorem B2465699 : Blo 1921435 2465699 := bstep (se 1 (by rfl) ⟨1849274, by rfl⟩ : syracuseStep 2465699 = 3698549) B3698549
theorem B6575197 : Blo 1921435 6575197 := bstep (se 3 (by rfl) ⟨1232849, by rfl⟩ : syracuseStep 6575197 = 2465699) B2465699
theorem B8766929 : Blo 1921435 8766929 := bstep (se 2 (by rfl) ⟨3287598, by rfl⟩ : syracuseStep 8766929 = 6575197) B6575197
theorem B5844619 : Blo 1921435 5844619 := bstep (se 1 (by rfl) ⟨4383464, by rfl⟩ : syracuseStep 5844619 = 8766929) B8766929
theorem B31171301 : Blo 1921435 31171301 := bstep (se 4 (by rfl) ⟨2922309, by rfl⟩ : syracuseStep 31171301 = 5844619) B5844619
theorem B20780867 : Blo 1921435 20780867 := bstep (se 1 (by rfl) ⟨15585650, by rfl⟩ : syracuseStep 20780867 = 31171301) B31171301
theorem B13853911 : Blo 1921435 13853911 := bstep (se 1 (by rfl) ⟨10390433, by rfl⟩ : syracuseStep 13853911 = 20780867) B20780867
theorem B18471881 : Blo 1921435 18471881 := bstep (se 2 (by rfl) ⟨6926955, by rfl⟩ : syracuseStep 18471881 = 13853911) B13853911
theorem B12314587 : Blo 1921435 12314587 := bstep (se 1 (by rfl) ⟨9235940, by rfl⟩ : syracuseStep 12314587 = 18471881) B18471881
theorem B16419449 : Blo 1921435 16419449 := bstep (se 2 (by rfl) ⟨6157293, by rfl⟩ : syracuseStep 16419449 = 12314587) B12314587
theorem B10946299 : Blo 1921435 10946299 := bstep (se 1 (by rfl) ⟨8209724, by rfl⟩ : syracuseStep 10946299 = 16419449) B16419449
theorem B14595065 : Blo 1921435 14595065 := bstep (se 2 (by rfl) ⟨5473149, by rfl⟩ : syracuseStep 14595065 = 10946299) B10946299
theorem B9730043 : Blo 1921435 9730043 := bstep (se 1 (by rfl) ⟨7297532, by rfl⟩ : syracuseStep 9730043 = 14595065) B14595065
theorem B6486695 : Blo 1921435 6486695 := bstep (se 1 (by rfl) ⟨4865021, by rfl⟩ : syracuseStep 6486695 = 9730043) B9730043
theorem B4324463 : Blo 1921435 4324463 := bstep (se 1 (by rfl) ⟨3243347, by rfl⟩ : syracuseStep 4324463 = 6486695) B6486695
theorem B2882975 : Blo 1921435 2882975 := bstep (se 1 (by rfl) ⟨2162231, by rfl⟩ : syracuseStep 2882975 = 4324463) B4324463
theorem B1921983 : Blo 1921435 1921983 := bstep (se 1 (by rfl) ⟨1441487, by rfl⟩ : syracuseStep 1921983 = 2882975) B2882975
theorem B2882981 : Blo 1921435 2882981 := bbase (se 4 (by rfl) ⟨270279, by rfl⟩ : syracuseStep 2882981 = 540559) (by norm_num)
theorem B1921987 : Blo 1921435 1921987 := bstep (se 1 (by rfl) ⟨1441490, by rfl⟩ : syracuseStep 1921987 = 2882981) B2882981
theorem B2432521 : Blo 1921435 2432521 := bbase (se 2 (by rfl) ⟨912195, by rfl⟩ : syracuseStep 2432521 = 1824391) (by norm_num)
theorem B3243361 : Blo 1921435 3243361 := bstep (se 2 (by rfl) ⟨1216260, by rfl⟩ : syracuseStep 3243361 = 2432521) B2432521
theorem B4324481 : Blo 1921435 4324481 := bstep (se 2 (by rfl) ⟨1621680, by rfl⟩ : syracuseStep 4324481 = 3243361) B3243361
theorem B2882987 : Blo 1921435 2882987 := bstep (se 1 (by rfl) ⟨2162240, by rfl⟩ : syracuseStep 2882987 = 4324481) B4324481
theorem B1921991 : Blo 1921435 1921991 := bstep (se 1 (by rfl) ⟨1441493, by rfl⟩ : syracuseStep 1921991 = 2882987) B2882987
theorem B2162245 : Blo 1921435 2162245 := bbase (se 4 (by rfl) ⟨202710, by rfl⟩ : syracuseStep 2162245 = 405421) (by norm_num)
theorem B2882993 : Blo 1921435 2882993 := bstep (se 2 (by rfl) ⟨1081122, by rfl⟩ : syracuseStep 2882993 = 2162245) B2162245
theorem B1921995 : Blo 1921435 1921995 := bstep (se 1 (by rfl) ⟨1441496, by rfl⟩ : syracuseStep 1921995 = 2882993) B2882993
theorem B3648797 : Blo 1921435 3648797 := bbase (se 3 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 3648797 = 1368299) (by norm_num)
theorem B2432531 : Blo 1921435 2432531 := bstep (se 1 (by rfl) ⟨1824398, by rfl⟩ : syracuseStep 2432531 = 3648797) B3648797
theorem B6486749 : Blo 1921435 6486749 := bstep (se 3 (by rfl) ⟨1216265, by rfl⟩ : syracuseStep 6486749 = 2432531) B2432531
theorem B4324499 : Blo 1921435 4324499 := bstep (se 1 (by rfl) ⟨3243374, by rfl⟩ : syracuseStep 4324499 = 6486749) B6486749
theorem B2882999 : Blo 1921435 2882999 := bstep (se 1 (by rfl) ⟨2162249, by rfl⟩ : syracuseStep 2882999 = 4324499) B4324499
theorem B1921999 : Blo 1921435 1921999 := bstep (se 1 (by rfl) ⟨1441499, by rfl⟩ : syracuseStep 1921999 = 2882999) B2882999
theorem B2883005 : Blo 1921435 2883005 := bbase (se 3 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 2883005 = 1081127) (by norm_num)
theorem B1922003 : Blo 1921435 1922003 := bstep (se 1 (by rfl) ⟨1441502, by rfl⟩ : syracuseStep 1922003 = 2883005) B2883005
theorem B4324517 : Blo 1921435 4324517 := bbase (se 4 (by rfl) ⟨405423, by rfl⟩ : syracuseStep 4324517 = 810847) (by norm_num)
theorem B2883011 : Blo 1921435 2883011 := bstep (se 1 (by rfl) ⟨2162258, by rfl⟩ : syracuseStep 2883011 = 4324517) B4324517
theorem B1922007 : Blo 1921435 1922007 := bstep (se 1 (by rfl) ⟨1441505, by rfl⟩ : syracuseStep 1922007 = 2883011) B2883011
theorem B4865093 : Blo 1921435 4865093 := bbase (se 4 (by rfl) ⟨456102, by rfl⟩ : syracuseStep 4865093 = 912205) (by norm_num)
theorem B3243395 : Blo 1921435 3243395 := bstep (se 1 (by rfl) ⟨2432546, by rfl⟩ : syracuseStep 3243395 = 4865093) B4865093
theorem B2162263 : Blo 1921435 2162263 := bstep (se 1 (by rfl) ⟨1621697, by rfl⟩ : syracuseStep 2162263 = 3243395) B3243395
theorem B2883017 : Blo 1921435 2883017 := bstep (se 2 (by rfl) ⟨1081131, by rfl⟩ : syracuseStep 2883017 = 2162263) B2162263
theorem B1922011 : Blo 1921435 1922011 := bstep (se 1 (by rfl) ⟨1441508, by rfl⟩ : syracuseStep 1922011 = 2883017) B2883017
theorem B6157397 : Blo 1921435 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B4104931 : Blo 1921435 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B5473241 : Blo 1921435 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B3648827 : Blo 1921435 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B9730205 : Blo 1921435 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B6486803 : Blo 1921435 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B4324535 : Blo 1921435 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B2883023 : Blo 1921435 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B1922015 : Blo 1921435 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B2883029 : Blo 1921435 2883029 := bbase (se 7 (by rfl) ⟨33785, by rfl⟩ : syracuseStep 2883029 = 67571) (by norm_num)
theorem B1922019 : Blo 1921435 1922019 := bstep (se 1 (by rfl) ⟨1441514, by rfl⟩ : syracuseStep 1922019 = 2883029) B2883029
theorem B7297685 : Blo 1921435 7297685 := bbase (se 6 (by rfl) ⟨171039, by rfl⟩ : syracuseStep 7297685 = 342079) (by norm_num)
theorem B4865123 : Blo 1921435 4865123 := bstep (se 1 (by rfl) ⟨3648842, by rfl⟩ : syracuseStep 4865123 = 7297685) B7297685
theorem B3243415 : Blo 1921435 3243415 := bstep (se 1 (by rfl) ⟨2432561, by rfl⟩ : syracuseStep 3243415 = 4865123) B4865123
theorem B4324553 : Blo 1921435 4324553 := bstep (se 2 (by rfl) ⟨1621707, by rfl⟩ : syracuseStep 4324553 = 3243415) B3243415
theorem B2883035 : Blo 1921435 2883035 := bstep (se 1 (by rfl) ⟨2162276, by rfl⟩ : syracuseStep 2883035 = 4324553) B4324553
theorem B1922023 : Blo 1921435 1922023 := bstep (se 1 (by rfl) ⟨1441517, by rfl⟩ : syracuseStep 1922023 = 2883035) B2883035
theorem B2162281 : Blo 1921435 2162281 := bbase (se 2 (by rfl) ⟨810855, by rfl⟩ : syracuseStep 2162281 = 1621711) (by norm_num)
theorem B2883041 : Blo 1921435 2883041 := bstep (se 2 (by rfl) ⟨1081140, by rfl⟩ : syracuseStep 2883041 = 2162281) B2162281
theorem B1922027 : Blo 1921435 1922027 := bstep (se 1 (by rfl) ⟨1441520, by rfl⟩ : syracuseStep 1922027 = 2883041) B2883041
theorem B4104965 : Blo 1921435 4104965 := bbase (se 4 (by rfl) ⟨384840, by rfl⟩ : syracuseStep 4104965 = 769681) (by norm_num)
theorem B10946573 : Blo 1921435 10946573 := bstep (se 3 (by rfl) ⟨2052482, by rfl⟩ : syracuseStep 10946573 = 4104965) B4104965
theorem B7297715 : Blo 1921435 7297715 := bstep (se 1 (by rfl) ⟨5473286, by rfl⟩ : syracuseStep 7297715 = 10946573) B10946573
theorem B4865143 : Blo 1921435 4865143 := bstep (se 1 (by rfl) ⟨3648857, by rfl⟩ : syracuseStep 4865143 = 7297715) B7297715
theorem B6486857 : Blo 1921435 6486857 := bstep (se 2 (by rfl) ⟨2432571, by rfl⟩ : syracuseStep 6486857 = 4865143) B4865143
theorem B4324571 : Blo 1921435 4324571 := bstep (se 1 (by rfl) ⟨3243428, by rfl⟩ : syracuseStep 4324571 = 6486857) B6486857
theorem B2883047 : Blo 1921435 2883047 := bstep (se 1 (by rfl) ⟨2162285, by rfl⟩ : syracuseStep 2883047 = 4324571) B4324571
theorem B1922031 : Blo 1921435 1922031 := bstep (se 1 (by rfl) ⟨1441523, by rfl⟩ : syracuseStep 1922031 = 2883047) B2883047
theorem B2883053 : Blo 1921435 2883053 := bbase (se 3 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 2883053 = 1081145) (by norm_num)
theorem B1922035 : Blo 1921435 1922035 := bstep (se 1 (by rfl) ⟨1441526, by rfl⟩ : syracuseStep 1922035 = 2883053) B2883053
theorem B4324589 : Blo 1921435 4324589 := bbase (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) (by norm_num)
theorem B2883059 : Blo 1921435 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B1922039 : Blo 1921435 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B2736661 : Blo 1921435 2736661 := bbase (se 6 (by rfl) ⟨64140, by rfl⟩ : syracuseStep 2736661 = 128281) (by norm_num)
theorem B3648881 : Blo 1921435 3648881 := bstep (se 2 (by rfl) ⟨1368330, by rfl⟩ : syracuseStep 3648881 = 2736661) B2736661
theorem B2432587 : Blo 1921435 2432587 := bstep (se 1 (by rfl) ⟨1824440, by rfl⟩ : syracuseStep 2432587 = 3648881) B3648881
theorem B3243449 : Blo 1921435 3243449 := bstep (se 2 (by rfl) ⟨1216293, by rfl⟩ : syracuseStep 3243449 = 2432587) B2432587
theorem B2162299 : Blo 1921435 2162299 := bstep (se 1 (by rfl) ⟨1621724, by rfl⟩ : syracuseStep 2162299 = 3243449) B3243449
theorem B2883065 : Blo 1921435 2883065 := bstep (se 2 (by rfl) ⟨1081149, by rfl⟩ : syracuseStep 2883065 = 2162299) B2162299
theorem B1922043 : Blo 1921435 1922043 := bstep (se 1 (by rfl) ⟨1441532, by rfl⟩ : syracuseStep 1922043 = 2883065) B2883065
theorem B9362261 : Blo 1921435 9362261 := bbase (se 9 (by rfl) ⟨27428, by rfl⟩ : syracuseStep 9362261 = 54857) (by norm_num)
theorem B24966029 : Blo 1921435 24966029 := bstep (se 3 (by rfl) ⟨4681130, by rfl⟩ : syracuseStep 24966029 = 9362261) B9362261
theorem B66576077 : Blo 1921435 66576077 := bstep (se 3 (by rfl) ⟨12483014, by rfl⟩ : syracuseStep 66576077 = 24966029) B24966029
theorem B44384051 : Blo 1921435 44384051 := bstep (se 1 (by rfl) ⟨33288038, by rfl⟩ : syracuseStep 44384051 = 66576077) B66576077
theorem B118357469 : Blo 1921435 118357469 := bstep (se 3 (by rfl) ⟨22192025, by rfl⟩ : syracuseStep 118357469 = 44384051) B44384051
theorem B78904979 : Blo 1921435 78904979 := bstep (se 1 (by rfl) ⟨59178734, by rfl⟩ : syracuseStep 78904979 = 118357469) B118357469
theorem B52603319 : Blo 1921435 52603319 := bstep (se 1 (by rfl) ⟨39452489, by rfl⟩ : syracuseStep 52603319 = 78904979) B78904979
theorem B35068879 : Blo 1921435 35068879 := bstep (se 1 (by rfl) ⟨26301659, by rfl⟩ : syracuseStep 35068879 = 52603319) B52603319
theorem B46758505 : Blo 1921435 46758505 := bstep (se 2 (by rfl) ⟨17534439, by rfl⟩ : syracuseStep 46758505 = 35068879) B35068879
theorem B62344673 : Blo 1921435 62344673 := bstep (se 2 (by rfl) ⟨23379252, by rfl⟩ : syracuseStep 62344673 = 46758505) B46758505
theorem B41563115 : Blo 1921435 41563115 := bstep (se 1 (by rfl) ⟨31172336, by rfl⟩ : syracuseStep 41563115 = 62344673) B62344673
theorem B27708743 : Blo 1921435 27708743 := bstep (se 1 (by rfl) ⟨20781557, by rfl⟩ : syracuseStep 27708743 = 41563115) B41563115
theorem B73889981 : Blo 1921435 73889981 := bstep (se 3 (by rfl) ⟨13854371, by rfl⟩ : syracuseStep 73889981 = 27708743) B27708743
theorem B49259987 : Blo 1921435 49259987 := bstep (se 1 (by rfl) ⟨36944990, by rfl⟩ : syracuseStep 49259987 = 73889981) B73889981
theorem B32839991 : Blo 1921435 32839991 := bstep (se 1 (by rfl) ⟨24629993, by rfl⟩ : syracuseStep 32839991 = 49259987) B49259987
theorem B21893327 : Blo 1921435 21893327 := bstep (se 1 (by rfl) ⟨16419995, by rfl⟩ : syracuseStep 21893327 = 32839991) B32839991
theorem B14595551 : Blo 1921435 14595551 := bstep (se 1 (by rfl) ⟨10946663, by rfl⟩ : syracuseStep 14595551 = 21893327) B21893327
theorem B9730367 : Blo 1921435 9730367 := bstep (se 1 (by rfl) ⟨7297775, by rfl⟩ : syracuseStep 9730367 = 14595551) B14595551
theorem B6486911 : Blo 1921435 6486911 := bstep (se 1 (by rfl) ⟨4865183, by rfl⟩ : syracuseStep 6486911 = 9730367) B9730367
theorem B4324607 : Blo 1921435 4324607 := bstep (se 1 (by rfl) ⟨3243455, by rfl⟩ : syracuseStep 4324607 = 6486911) B6486911
theorem B2883071 : Blo 1921435 2883071 := bstep (se 1 (by rfl) ⟨2162303, by rfl⟩ : syracuseStep 2883071 = 4324607) B4324607
theorem B1922047 : Blo 1921435 1922047 := bstep (se 1 (by rfl) ⟨1441535, by rfl⟩ : syracuseStep 1922047 = 2883071) B2883071
theorem B2883077 : Blo 1921435 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B1922051 : Blo 1921435 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B3243469 : Blo 1921435 3243469 := bbase (se 3 (by rfl) ⟨608150, by rfl⟩ : syracuseStep 3243469 = 1216301) (by norm_num)
theorem B4324625 : Blo 1921435 4324625 := bstep (se 2 (by rfl) ⟨1621734, by rfl⟩ : syracuseStep 4324625 = 3243469) B3243469
theorem B2883083 : Blo 1921435 2883083 := bstep (se 1 (by rfl) ⟨2162312, by rfl⟩ : syracuseStep 2883083 = 4324625) B4324625
theorem B1922055 : Blo 1921435 1922055 := bstep (se 1 (by rfl) ⟨1441541, by rfl⟩ : syracuseStep 1922055 = 2883083) B2883083
theorem B2162317 : Blo 1921435 2162317 := bbase (se 3 (by rfl) ⟨405434, by rfl⟩ : syracuseStep 2162317 = 810869) (by norm_num)
theorem B2883089 : Blo 1921435 2883089 := bstep (se 2 (by rfl) ⟨1081158, by rfl⟩ : syracuseStep 2883089 = 2162317) B2162317
theorem B1922059 : Blo 1921435 1922059 := bstep (se 1 (by rfl) ⟨1441544, by rfl⟩ : syracuseStep 1922059 = 2883089) B2883089
theorem B6486965 : Blo 1921435 6486965 := bbase (se 5 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 6486965 = 608153) (by norm_num)
theorem B4324643 : Blo 1921435 4324643 := bstep (se 1 (by rfl) ⟨3243482, by rfl⟩ : syracuseStep 4324643 = 6486965) B6486965
theorem B2883095 : Blo 1921435 2883095 := bstep (se 1 (by rfl) ⟨2162321, by rfl⟩ : syracuseStep 2883095 = 4324643) B4324643
theorem B1922063 : Blo 1921435 1922063 := bstep (se 1 (by rfl) ⟨1441547, by rfl⟩ : syracuseStep 1922063 = 2883095) B2883095
theorem B2883101 : Blo 1921435 2883101 := bbase (se 3 (by rfl) ⟨540581, by rfl⟩ : syracuseStep 2883101 = 1081163) (by norm_num)
theorem B1922067 : Blo 1921435 1922067 := bstep (se 1 (by rfl) ⟨1441550, by rfl⟩ : syracuseStep 1922067 = 2883101) B2883101
theorem B4324661 : Blo 1921435 4324661 := bbase (se 5 (by rfl) ⟨202718, by rfl⟩ : syracuseStep 4324661 = 405437) (by norm_num)
theorem B2883107 : Blo 1921435 2883107 := bstep (se 1 (by rfl) ⟨2162330, by rfl⟩ : syracuseStep 2883107 = 4324661) B4324661
theorem B1922071 : Blo 1921435 1922071 := bstep (se 1 (by rfl) ⟨1441553, by rfl⟩ : syracuseStep 1922071 = 2883107) B2883107
theorem B10390933 : Blo 1921435 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B13854577 : Blo 1921435 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B18472769 : Blo 1921435 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B12315179 : Blo 1921435 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B8210119 : Blo 1921435 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B10946825 : Blo 1921435 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B7297883 : Blo 1921435 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B4865255 : Blo 1921435 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B3243503 : Blo 1921435 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B2162335 : Blo 1921435 2162335 := bstep (se 1 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 2162335 = 3243503) B3243503
theorem B2883113 : Blo 1921435 2883113 := bstep (se 2 (by rfl) ⟨1081167, by rfl⟩ : syracuseStep 2883113 = 2162335) B2162335
theorem B1922075 : Blo 1921435 1922075 := bstep (se 1 (by rfl) ⟨1441556, by rfl⟩ : syracuseStep 1922075 = 2883113) B2883113
theorem B5195477 : Blo 1921435 5195477 := bbase (se 7 (by rfl) ⟨60884, by rfl⟩ : syracuseStep 5195477 = 121769) (by norm_num)
theorem B3463651 : Blo 1921435 3463651 := bstep (se 1 (by rfl) ⟨2597738, by rfl⟩ : syracuseStep 3463651 = 5195477) B5195477
theorem B18472805 : Blo 1921435 18472805 := bstep (se 4 (by rfl) ⟨1731825, by rfl⟩ : syracuseStep 18472805 = 3463651) B3463651
theorem B12315203 : Blo 1921435 12315203 := bstep (se 1 (by rfl) ⟨9236402, by rfl⟩ : syracuseStep 12315203 = 18472805) B18472805
theorem B8210135 : Blo 1921435 8210135 := bstep (se 1 (by rfl) ⟨6157601, by rfl⟩ : syracuseStep 8210135 = 12315203) B12315203
theorem B5473423 : Blo 1921435 5473423 := bstep (se 1 (by rfl) ⟨4105067, by rfl⟩ : syracuseStep 5473423 = 8210135) B8210135
theorem B7297897 : Blo 1921435 7297897 := bstep (se 2 (by rfl) ⟨2736711, by rfl⟩ : syracuseStep 7297897 = 5473423) B5473423
theorem B9730529 : Blo 1921435 9730529 := bstep (se 2 (by rfl) ⟨3648948, by rfl⟩ : syracuseStep 9730529 = 7297897) B7297897
theorem B6487019 : Blo 1921435 6487019 := bstep (se 1 (by rfl) ⟨4865264, by rfl⟩ : syracuseStep 6487019 = 9730529) B9730529
theorem B4324679 : Blo 1921435 4324679 := bstep (se 1 (by rfl) ⟨3243509, by rfl⟩ : syracuseStep 4324679 = 6487019) B6487019
theorem B2883119 : Blo 1921435 2883119 := bstep (se 1 (by rfl) ⟨2162339, by rfl⟩ : syracuseStep 2883119 = 4324679) B4324679
theorem B1922079 : Blo 1921435 1922079 := bstep (se 1 (by rfl) ⟨1441559, by rfl⟩ : syracuseStep 1922079 = 2883119) B2883119
theorem B2883125 : Blo 1921435 2883125 := bbase (se 5 (by rfl) ⟨135146, by rfl⟩ : syracuseStep 2883125 = 270293) (by norm_num)
theorem B1922083 : Blo 1921435 1922083 := bstep (se 1 (by rfl) ⟨1441562, by rfl⟩ : syracuseStep 1922083 = 2883125) B2883125
theorem B4865285 : Blo 1921435 4865285 := bbase (se 4 (by rfl) ⟨456120, by rfl⟩ : syracuseStep 4865285 = 912241) (by norm_num)
theorem B3243523 : Blo 1921435 3243523 := bstep (se 1 (by rfl) ⟨2432642, by rfl⟩ : syracuseStep 3243523 = 4865285) B4865285
theorem B4324697 : Blo 1921435 4324697 := bstep (se 2 (by rfl) ⟨1621761, by rfl⟩ : syracuseStep 4324697 = 3243523) B3243523
theorem B2883131 : Blo 1921435 2883131 := bstep (se 1 (by rfl) ⟨2162348, by rfl⟩ : syracuseStep 2883131 = 4324697) B4324697
theorem B1922087 : Blo 1921435 1922087 := bstep (se 1 (by rfl) ⟨1441565, by rfl⟩ : syracuseStep 1922087 = 2883131) B2883131
theorem B2162353 : Blo 1921435 2162353 := bbase (se 2 (by rfl) ⟨810882, by rfl⟩ : syracuseStep 2162353 = 1621765) (by norm_num)
theorem B2883137 : Blo 1921435 2883137 := bstep (se 2 (by rfl) ⟨1081176, by rfl⟩ : syracuseStep 2883137 = 2162353) B2162353
theorem B1922091 : Blo 1921435 1922091 := bstep (se 1 (by rfl) ⟨1441568, by rfl⟩ : syracuseStep 1922091 = 2883137) B2883137
theorem B1948321 : Blo 1921435 1948321 := bbase (se 2 (by rfl) ⟨730620, by rfl⟩ : syracuseStep 1948321 = 1461241) (by norm_num)
theorem B2597761 : Blo 1921435 2597761 := bstep (se 2 (by rfl) ⟨974160, by rfl⟩ : syracuseStep 2597761 = 1948321) B1948321
theorem B3463681 : Blo 1921435 3463681 := bstep (se 2 (by rfl) ⟨1298880, by rfl⟩ : syracuseStep 3463681 = 2597761) B2597761
theorem B4618241 : Blo 1921435 4618241 := bstep (se 2 (by rfl) ⟨1731840, by rfl⟩ : syracuseStep 4618241 = 3463681) B3463681
theorem B3078827 : Blo 1921435 3078827 := bstep (se 1 (by rfl) ⟨2309120, by rfl⟩ : syracuseStep 3078827 = 4618241) B4618241
theorem B2052551 : Blo 1921435 2052551 := bstep (se 1 (by rfl) ⟨1539413, by rfl⟩ : syracuseStep 2052551 = 3078827) B3078827
theorem B5473469 : Blo 1921435 5473469 := bstep (se 3 (by rfl) ⟨1026275, by rfl⟩ : syracuseStep 5473469 = 2052551) B2052551
theorem B3648979 : Blo 1921435 3648979 := bstep (se 1 (by rfl) ⟨2736734, by rfl⟩ : syracuseStep 3648979 = 5473469) B5473469
theorem B4865305 : Blo 1921435 4865305 := bstep (se 2 (by rfl) ⟨1824489, by rfl⟩ : syracuseStep 4865305 = 3648979) B3648979
theorem B6487073 : Blo 1921435 6487073 := bstep (se 2 (by rfl) ⟨2432652, by rfl⟩ : syracuseStep 6487073 = 4865305) B4865305
theorem B4324715 : Blo 1921435 4324715 := bstep (se 1 (by rfl) ⟨3243536, by rfl⟩ : syracuseStep 4324715 = 6487073) B6487073
theorem B2883143 : Blo 1921435 2883143 := bstep (se 1 (by rfl) ⟨2162357, by rfl⟩ : syracuseStep 2883143 = 4324715) B4324715
theorem B1922095 : Blo 1921435 1922095 := bstep (se 1 (by rfl) ⟨1441571, by rfl⟩ : syracuseStep 1922095 = 2883143) B2883143
theorem B2883149 : Blo 1921435 2883149 := bbase (se 3 (by rfl) ⟨540590, by rfl⟩ : syracuseStep 2883149 = 1081181) (by norm_num)
theorem B1922099 : Blo 1921435 1922099 := bstep (se 1 (by rfl) ⟨1441574, by rfl⟩ : syracuseStep 1922099 = 2883149) B2883149
theorem B4324733 : Blo 1921435 4324733 := bbase (se 3 (by rfl) ⟨810887, by rfl⟩ : syracuseStep 4324733 = 1621775) (by norm_num)
theorem B2883155 : Blo 1921435 2883155 := bstep (se 1 (by rfl) ⟨2162366, by rfl⟩ : syracuseStep 2883155 = 4324733) B4324733
theorem B1922103 : Blo 1921435 1922103 := bstep (se 1 (by rfl) ⟨1441577, by rfl⟩ : syracuseStep 1922103 = 2883155) B2883155
theorem B3243557 : Blo 1921435 3243557 := bbase (se 4 (by rfl) ⟨304083, by rfl⟩ : syracuseStep 3243557 = 608167) (by norm_num)
theorem B2162371 : Blo 1921435 2162371 := bstep (se 1 (by rfl) ⟨1621778, by rfl⟩ : syracuseStep 2162371 = 3243557) B3243557
theorem B2883161 : Blo 1921435 2883161 := bstep (se 2 (by rfl) ⟨1081185, by rfl⟩ : syracuseStep 2883161 = 2162371) B2162371
theorem B1922107 : Blo 1921435 1922107 := bstep (se 1 (by rfl) ⟨1441580, by rfl⟩ : syracuseStep 1922107 = 2883161) B2883161
theorem B2736757 : Blo 1921435 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B14596037 : Blo 1921435 14596037 := bstep (se 4 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 14596037 = 2736757) B2736757
theorem B9730691 : Blo 1921435 9730691 := bstep (se 1 (by rfl) ⟨7298018, by rfl⟩ : syracuseStep 9730691 = 14596037) B14596037
theorem B6487127 : Blo 1921435 6487127 := bstep (se 1 (by rfl) ⟨4865345, by rfl⟩ : syracuseStep 6487127 = 9730691) B9730691
theorem B4324751 : Blo 1921435 4324751 := bstep (se 1 (by rfl) ⟨3243563, by rfl⟩ : syracuseStep 4324751 = 6487127) B6487127
theorem B2883167 : Blo 1921435 2883167 := bstep (se 1 (by rfl) ⟨2162375, by rfl⟩ : syracuseStep 2883167 = 4324751) B4324751
theorem B1922111 : Blo 1921435 1922111 := bstep (se 1 (by rfl) ⟨1441583, by rfl⟩ : syracuseStep 1922111 = 2883167) B2883167
theorem B2883173 : Blo 1921435 2883173 := bbase (se 4 (by rfl) ⟨270297, by rfl⟩ : syracuseStep 2883173 = 540595) (by norm_num)
theorem B1922115 : Blo 1921435 1922115 := bstep (se 1 (by rfl) ⟨1441586, by rfl⟩ : syracuseStep 1922115 = 2883173) B2883173
theorem B2052577 : Blo 1921435 2052577 := bbase (se 2 (by rfl) ⟨769716, by rfl⟩ : syracuseStep 2052577 = 1539433) (by norm_num)
theorem B2736769 : Blo 1921435 2736769 := bstep (se 2 (by rfl) ⟨1026288, by rfl⟩ : syracuseStep 2736769 = 2052577) B2052577
theorem B3649025 : Blo 1921435 3649025 := bstep (se 2 (by rfl) ⟨1368384, by rfl⟩ : syracuseStep 3649025 = 2736769) B2736769
theorem B2432683 : Blo 1921435 2432683 := bstep (se 1 (by rfl) ⟨1824512, by rfl⟩ : syracuseStep 2432683 = 3649025) B3649025
theorem B3243577 : Blo 1921435 3243577 := bstep (se 2 (by rfl) ⟨1216341, by rfl⟩ : syracuseStep 3243577 = 2432683) B2432683
theorem B4324769 : Blo 1921435 4324769 := bstep (se 2 (by rfl) ⟨1621788, by rfl⟩ : syracuseStep 4324769 = 3243577) B3243577
theorem B2883179 : Blo 1921435 2883179 := bstep (se 1 (by rfl) ⟨2162384, by rfl⟩ : syracuseStep 2883179 = 4324769) B4324769
theorem B1922119 : Blo 1921435 1922119 := bstep (se 1 (by rfl) ⟨1441589, by rfl⟩ : syracuseStep 1922119 = 2883179) B2883179
theorem B2162389 : Blo 1921435 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B2883185 : Blo 1921435 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B1922123 : Blo 1921435 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B2432693 : Blo 1921435 2432693 := bbase (se 5 (by rfl) ⟨114032, by rfl⟩ : syracuseStep 2432693 = 228065) (by norm_num)
theorem B6487181 : Blo 1921435 6487181 := bstep (se 3 (by rfl) ⟨1216346, by rfl⟩ : syracuseStep 6487181 = 2432693) B2432693
theorem B4324787 : Blo 1921435 4324787 := bstep (se 1 (by rfl) ⟨3243590, by rfl⟩ : syracuseStep 4324787 = 6487181) B6487181
theorem B2883191 : Blo 1921435 2883191 := bstep (se 1 (by rfl) ⟨2162393, by rfl⟩ : syracuseStep 2883191 = 4324787) B4324787
theorem B1922127 : Blo 1921435 1922127 := bstep (se 1 (by rfl) ⟨1441595, by rfl⟩ : syracuseStep 1922127 = 2883191) B2883191
theorem B2883197 : Blo 1921435 2883197 := bbase (se 3 (by rfl) ⟨540599, by rfl⟩ : syracuseStep 2883197 = 1081199) (by norm_num)
theorem B1922131 : Blo 1921435 1922131 := bstep (se 1 (by rfl) ⟨1441598, by rfl⟩ : syracuseStep 1922131 = 2883197) B2883197
theorem B4324805 : Blo 1921435 4324805 := bbase (se 4 (by rfl) ⟨405450, by rfl⟩ : syracuseStep 4324805 = 810901) (by norm_num)
theorem B2883203 : Blo 1921435 2883203 := bstep (se 1 (by rfl) ⟨2162402, by rfl⟩ : syracuseStep 2883203 = 4324805) B4324805
theorem B1922135 : Blo 1921435 1922135 := bstep (se 1 (by rfl) ⟨1441601, by rfl⟩ : syracuseStep 1922135 = 2883203) B2883203
theorem B9236693 : Blo 1921435 9236693 := bbase (se 7 (by rfl) ⟨108242, by rfl⟩ : syracuseStep 9236693 = 216485) (by norm_num)
theorem B6157795 : Blo 1921435 6157795 := bstep (se 1 (by rfl) ⟨4618346, by rfl⟩ : syracuseStep 6157795 = 9236693) B9236693
theorem B8210393 : Blo 1921435 8210393 := bstep (se 2 (by rfl) ⟨3078897, by rfl⟩ : syracuseStep 8210393 = 6157795) B6157795
theorem B5473595 : Blo 1921435 5473595 := bstep (se 1 (by rfl) ⟨4105196, by rfl⟩ : syracuseStep 5473595 = 8210393) B8210393
theorem B3649063 : Blo 1921435 3649063 := bstep (se 1 (by rfl) ⟨2736797, by rfl⟩ : syracuseStep 3649063 = 5473595) B5473595
theorem B4865417 : Blo 1921435 4865417 := bstep (se 2 (by rfl) ⟨1824531, by rfl⟩ : syracuseStep 4865417 = 3649063) B3649063
theorem B3243611 : Blo 1921435 3243611 := bstep (se 1 (by rfl) ⟨2432708, by rfl⟩ : syracuseStep 3243611 = 4865417) B4865417
theorem B2162407 : Blo 1921435 2162407 := bstep (se 1 (by rfl) ⟨1621805, by rfl⟩ : syracuseStep 2162407 = 3243611) B3243611
theorem B2883209 : Blo 1921435 2883209 := bstep (se 2 (by rfl) ⟨1081203, by rfl⟩ : syracuseStep 2883209 = 2162407) B2162407
theorem B1922139 : Blo 1921435 1922139 := bstep (se 1 (by rfl) ⟨1441604, by rfl⟩ : syracuseStep 1922139 = 2883209) B2883209
theorem B9730853 : Blo 1921435 9730853 := bbase (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) (by norm_num)
theorem B6487235 : Blo 1921435 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B4324823 : Blo 1921435 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B2883215 : Blo 1921435 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B1922143 : Blo 1921435 1922143 := bstep (se 1 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 1922143 = 2883215) B2883215
theorem B2883221 : Blo 1921435 2883221 := bbase (se 6 (by rfl) ⟨67575, by rfl⟩ : syracuseStep 2883221 = 135151) (by norm_num)
theorem B1922147 : Blo 1921435 1922147 := bstep (se 1 (by rfl) ⟨1441610, by rfl⟩ : syracuseStep 1922147 = 2883221) B2883221
theorem B3463781 : Blo 1921435 3463781 := bbase (se 4 (by rfl) ⟨324729, by rfl⟩ : syracuseStep 3463781 = 649459) (by norm_num)
theorem B9236749 : Blo 1921435 9236749 := bstep (se 3 (by rfl) ⟨1731890, by rfl⟩ : syracuseStep 9236749 = 3463781) B3463781
theorem B12315665 : Blo 1921435 12315665 := bstep (se 2 (by rfl) ⟨4618374, by rfl⟩ : syracuseStep 12315665 = 9236749) B9236749
theorem B8210443 : Blo 1921435 8210443 := bstep (se 1 (by rfl) ⟨6157832, by rfl⟩ : syracuseStep 8210443 = 12315665) B12315665
theorem B10947257 : Blo 1921435 10947257 := bstep (se 2 (by rfl) ⟨4105221, by rfl⟩ : syracuseStep 10947257 = 8210443) B8210443
theorem B7298171 : Blo 1921435 7298171 := bstep (se 1 (by rfl) ⟨5473628, by rfl⟩ : syracuseStep 7298171 = 10947257) B10947257
theorem B4865447 : Blo 1921435 4865447 := bstep (se 1 (by rfl) ⟨3649085, by rfl⟩ : syracuseStep 4865447 = 7298171) B7298171
theorem B3243631 : Blo 1921435 3243631 := bstep (se 1 (by rfl) ⟨2432723, by rfl⟩ : syracuseStep 3243631 = 4865447) B4865447
theorem B4324841 : Blo 1921435 4324841 := bstep (se 2 (by rfl) ⟨1621815, by rfl⟩ : syracuseStep 4324841 = 3243631) B3243631
theorem B2883227 : Blo 1921435 2883227 := bstep (se 1 (by rfl) ⟨2162420, by rfl⟩ : syracuseStep 2883227 = 4324841) B4324841
theorem B1922151 : Blo 1921435 1922151 := bstep (se 1 (by rfl) ⟨1441613, by rfl⟩ : syracuseStep 1922151 = 2883227) B2883227
theorem B2162425 : Blo 1921435 2162425 := bbase (se 2 (by rfl) ⟨810909, by rfl⟩ : syracuseStep 2162425 = 1621819) (by norm_num)
theorem B2883233 : Blo 1921435 2883233 := bstep (se 2 (by rfl) ⟨1081212, by rfl⟩ : syracuseStep 2883233 = 2162425) B2162425
theorem B1922155 : Blo 1921435 1922155 := bstep (se 1 (by rfl) ⟨1441616, by rfl⟩ : syracuseStep 1922155 = 2883233) B2883233
theorem B2309197 : Blo 1921435 2309197 := bbase (se 3 (by rfl) ⟨432974, by rfl⟩ : syracuseStep 2309197 = 865949) (by norm_num)
theorem B3078929 : Blo 1921435 3078929 := bstep (se 2 (by rfl) ⟨1154598, by rfl⟩ : syracuseStep 3078929 = 2309197) B2309197
theorem B8210477 : Blo 1921435 8210477 := bstep (se 3 (by rfl) ⟨1539464, by rfl⟩ : syracuseStep 8210477 = 3078929) B3078929
theorem B5473651 : Blo 1921435 5473651 := bstep (se 1 (by rfl) ⟨4105238, by rfl⟩ : syracuseStep 5473651 = 8210477) B8210477
theorem B7298201 : Blo 1921435 7298201 := bstep (se 2 (by rfl) ⟨2736825, by rfl⟩ : syracuseStep 7298201 = 5473651) B5473651
theorem B4865467 : Blo 1921435 4865467 := bstep (se 1 (by rfl) ⟨3649100, by rfl⟩ : syracuseStep 4865467 = 7298201) B7298201
theorem B6487289 : Blo 1921435 6487289 := bstep (se 2 (by rfl) ⟨2432733, by rfl⟩ : syracuseStep 6487289 = 4865467) B4865467
theorem B4324859 : Blo 1921435 4324859 := bstep (se 1 (by rfl) ⟨3243644, by rfl⟩ : syracuseStep 4324859 = 6487289) B6487289
theorem B2883239 : Blo 1921435 2883239 := bstep (se 1 (by rfl) ⟨2162429, by rfl⟩ : syracuseStep 2883239 = 4324859) B4324859
theorem B1922159 : Blo 1921435 1922159 := bstep (se 1 (by rfl) ⟨1441619, by rfl⟩ : syracuseStep 1922159 = 2883239) B2883239
theorem B2883245 : Blo 1921435 2883245 := bbase (se 3 (by rfl) ⟨540608, by rfl⟩ : syracuseStep 2883245 = 1081217) (by norm_num)
theorem B1922163 : Blo 1921435 1922163 := bstep (se 1 (by rfl) ⟨1441622, by rfl⟩ : syracuseStep 1922163 = 2883245) B2883245
theorem B4324877 : Blo 1921435 4324877 := bbase (se 3 (by rfl) ⟨810914, by rfl⟩ : syracuseStep 4324877 = 1621829) (by norm_num)
theorem B2883251 : Blo 1921435 2883251 := bstep (se 1 (by rfl) ⟨2162438, by rfl⟩ : syracuseStep 2883251 = 4324877) B4324877
theorem B1922167 : Blo 1921435 1922167 := bstep (se 1 (by rfl) ⟨1441625, by rfl⟩ : syracuseStep 1922167 = 2883251) B2883251
theorem B2432749 : Blo 1921435 2432749 := bbase (se 3 (by rfl) ⟨456140, by rfl⟩ : syracuseStep 2432749 = 912281) (by norm_num)
theorem B3243665 : Blo 1921435 3243665 := bstep (se 2 (by rfl) ⟨1216374, by rfl⟩ : syracuseStep 3243665 = 2432749) B2432749
theorem B2162443 : Blo 1921435 2162443 := bstep (se 1 (by rfl) ⟨1621832, by rfl⟩ : syracuseStep 2162443 = 3243665) B3243665
theorem B2883257 : Blo 1921435 2883257 := bstep (se 2 (by rfl) ⟨1081221, by rfl⟩ : syracuseStep 2883257 = 2162443) B2162443
theorem B1922171 : Blo 1921435 1922171 := bstep (se 1 (by rfl) ⟨1441628, by rfl⟩ : syracuseStep 1922171 = 2883257) B2883257
theorem B2465945 : Blo 1921435 2465945 := bbase (se 2 (by rfl) ⟨924729, by rfl⟩ : syracuseStep 2465945 = 1849459) (by norm_num)
theorem B105213653 : Blo 1921435 105213653 := bstep (se 7 (by rfl) ⟨1232972, by rfl⟩ : syracuseStep 105213653 = 2465945) B2465945
theorem B70142435 : Blo 1921435 70142435 := bstep (se 1 (by rfl) ⟨52606826, by rfl⟩ : syracuseStep 70142435 = 105213653) B105213653
theorem B46761623 : Blo 1921435 46761623 := bstep (se 1 (by rfl) ⟨35071217, by rfl⟩ : syracuseStep 46761623 = 70142435) B70142435
theorem B31174415 : Blo 1921435 31174415 := bstep (se 1 (by rfl) ⟨23380811, by rfl⟩ : syracuseStep 31174415 = 46761623) B46761623
theorem B20782943 : Blo 1921435 20782943 := bstep (se 1 (by rfl) ⟨15587207, by rfl⟩ : syracuseStep 20782943 = 31174415) B31174415
theorem B13855295 : Blo 1921435 13855295 := bstep (se 1 (by rfl) ⟨10391471, by rfl⟩ : syracuseStep 13855295 = 20782943) B20782943
theorem B9236863 : Blo 1921435 9236863 := bstep (se 1 (by rfl) ⟨6927647, by rfl⟩ : syracuseStep 9236863 = 13855295) B13855295
theorem B12315817 : Blo 1921435 12315817 := bstep (se 2 (by rfl) ⟨4618431, by rfl⟩ : syracuseStep 12315817 = 9236863) B9236863
theorem B16421089 : Blo 1921435 16421089 := bstep (se 2 (by rfl) ⟨6157908, by rfl⟩ : syracuseStep 16421089 = 12315817) B12315817
theorem B21894785 : Blo 1921435 21894785 := bstep (se 2 (by rfl) ⟨8210544, by rfl⟩ : syracuseStep 21894785 = 16421089) B16421089
theorem B14596523 : Blo 1921435 14596523 := bstep (se 1 (by rfl) ⟨10947392, by rfl⟩ : syracuseStep 14596523 = 21894785) B21894785
theorem B9731015 : Blo 1921435 9731015 := bstep (se 1 (by rfl) ⟨7298261, by rfl⟩ : syracuseStep 9731015 = 14596523) B14596523
theorem B6487343 : Blo 1921435 6487343 := bstep (se 1 (by rfl) ⟨4865507, by rfl⟩ : syracuseStep 6487343 = 9731015) B9731015
theorem B4324895 : Blo 1921435 4324895 := bstep (se 1 (by rfl) ⟨3243671, by rfl⟩ : syracuseStep 4324895 = 6487343) B6487343
theorem B2883263 : Blo 1921435 2883263 := bstep (se 1 (by rfl) ⟨2162447, by rfl⟩ : syracuseStep 2883263 = 4324895) B4324895
theorem B1922175 : Blo 1921435 1922175 := bstep (se 1 (by rfl) ⟨1441631, by rfl⟩ : syracuseStep 1922175 = 2883263) B2883263
theorem B2883269 : Blo 1921435 2883269 := bbase (se 4 (by rfl) ⟨270306, by rfl⟩ : syracuseStep 2883269 = 540613) (by norm_num)
theorem B1922179 : Blo 1921435 1922179 := bstep (se 1 (by rfl) ⟨1441634, by rfl⟩ : syracuseStep 1922179 = 2883269) B2883269
theorem B3243685 : Blo 1921435 3243685 := bbase (se 4 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 3243685 = 608191) (by norm_num)
theorem B4324913 : Blo 1921435 4324913 := bstep (se 2 (by rfl) ⟨1621842, by rfl⟩ : syracuseStep 4324913 = 3243685) B3243685
theorem B2883275 : Blo 1921435 2883275 := bstep (se 1 (by rfl) ⟨2162456, by rfl⟩ : syracuseStep 2883275 = 4324913) B4324913
theorem B1922183 : Blo 1921435 1922183 := bstep (se 1 (by rfl) ⟨1441637, by rfl⟩ : syracuseStep 1922183 = 2883275) B2883275
theorem B2162461 : Blo 1921435 2162461 := bbase (se 3 (by rfl) ⟨405461, by rfl⟩ : syracuseStep 2162461 = 810923) (by norm_num)
theorem B2883281 : Blo 1921435 2883281 := bstep (se 2 (by rfl) ⟨1081230, by rfl⟩ : syracuseStep 2883281 = 2162461) B2162461
theorem B1922187 : Blo 1921435 1922187 := bstep (se 1 (by rfl) ⟨1441640, by rfl⟩ : syracuseStep 1922187 = 2883281) B2883281
theorem B6487397 : Blo 1921435 6487397 := bbase (se 4 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 6487397 = 1216387) (by norm_num)
theorem B4324931 : Blo 1921435 4324931 := bstep (se 1 (by rfl) ⟨3243698, by rfl⟩ : syracuseStep 4324931 = 6487397) B6487397
theorem B2883287 : Blo 1921435 2883287 := bstep (se 1 (by rfl) ⟨2162465, by rfl⟩ : syracuseStep 2883287 = 4324931) B4324931
theorem B1922191 : Blo 1921435 1922191 := bstep (se 1 (by rfl) ⟨1441643, by rfl⟩ : syracuseStep 1922191 = 2883287) B2883287
theorem B2883293 : Blo 1921435 2883293 := bbase (se 3 (by rfl) ⟨540617, by rfl⟩ : syracuseStep 2883293 = 1081235) (by norm_num)
theorem B1922195 : Blo 1921435 1922195 := bstep (se 1 (by rfl) ⟨1441646, by rfl⟩ : syracuseStep 1922195 = 2883293) B2883293
theorem B4324949 : Blo 1921435 4324949 := bbase (se 8 (by rfl) ⟨25341, by rfl⟩ : syracuseStep 4324949 = 50683) (by norm_num)
theorem B2883299 : Blo 1921435 2883299 := bstep (se 1 (by rfl) ⟨2162474, by rfl⟩ : syracuseStep 2883299 = 4324949) B4324949
theorem B1922199 : Blo 1921435 1922199 := bstep (se 1 (by rfl) ⟨1441649, by rfl⟩ : syracuseStep 1922199 = 2883299) B2883299
theorem B4105333 : Blo 1921435 4105333 := bbase (se 5 (by rfl) ⟨192437, by rfl⟩ : syracuseStep 4105333 = 384875) (by norm_num)
theorem B5473777 : Blo 1921435 5473777 := bstep (se 2 (by rfl) ⟨2052666, by rfl⟩ : syracuseStep 5473777 = 4105333) B4105333
theorem B7298369 : Blo 1921435 7298369 := bstep (se 2 (by rfl) ⟨2736888, by rfl⟩ : syracuseStep 7298369 = 5473777) B5473777
theorem B4865579 : Blo 1921435 4865579 := bstep (se 1 (by rfl) ⟨3649184, by rfl⟩ : syracuseStep 4865579 = 7298369) B7298369
theorem B3243719 : Blo 1921435 3243719 := bstep (se 1 (by rfl) ⟨2432789, by rfl⟩ : syracuseStep 3243719 = 4865579) B4865579
theorem B2162479 : Blo 1921435 2162479 := bstep (se 1 (by rfl) ⟨1621859, by rfl⟩ : syracuseStep 2162479 = 3243719) B3243719
theorem B2883305 : Blo 1921435 2883305 := bstep (se 2 (by rfl) ⟨1081239, by rfl⟩ : syracuseStep 2883305 = 2162479) B2162479
theorem B1922203 : Blo 1921435 1922203 := bstep (se 1 (by rfl) ⟨1441652, by rfl⟩ : syracuseStep 1922203 = 2883305) B2883305
theorem B5845301 : Blo 1921435 5845301 := bbase (se 5 (by rfl) ⟨273998, by rfl⟩ : syracuseStep 5845301 = 547997) (by norm_num)
theorem B3896867 : Blo 1921435 3896867 := bstep (se 1 (by rfl) ⟨2922650, by rfl⟩ : syracuseStep 3896867 = 5845301) B5845301
theorem B10391645 : Blo 1921435 10391645 := bstep (se 3 (by rfl) ⟨1948433, by rfl⟩ : syracuseStep 10391645 = 3896867) B3896867
theorem B6927763 : Blo 1921435 6927763 := bstep (se 1 (by rfl) ⟨5195822, by rfl⟩ : syracuseStep 6927763 = 10391645) B10391645
theorem B9237017 : Blo 1921435 9237017 := bstep (se 2 (by rfl) ⟨3463881, by rfl⟩ : syracuseStep 9237017 = 6927763) B6927763
theorem B24632045 : Blo 1921435 24632045 := bstep (se 3 (by rfl) ⟨4618508, by rfl⟩ : syracuseStep 24632045 = 9237017) B9237017
theorem B16421363 : Blo 1921435 16421363 := bstep (se 1 (by rfl) ⟨12316022, by rfl⟩ : syracuseStep 16421363 = 24632045) B24632045
theorem B10947575 : Blo 1921435 10947575 := bstep (se 1 (by rfl) ⟨8210681, by rfl⟩ : syracuseStep 10947575 = 16421363) B16421363
theorem B7298383 : Blo 1921435 7298383 := bstep (se 1 (by rfl) ⟨5473787, by rfl⟩ : syracuseStep 7298383 = 10947575) B10947575
theorem B9731177 : Blo 1921435 9731177 := bstep (se 2 (by rfl) ⟨3649191, by rfl⟩ : syracuseStep 9731177 = 7298383) B7298383
theorem B6487451 : Blo 1921435 6487451 := bstep (se 1 (by rfl) ⟨4865588, by rfl⟩ : syracuseStep 6487451 = 9731177) B9731177
theorem B4324967 : Blo 1921435 4324967 := bstep (se 1 (by rfl) ⟨3243725, by rfl⟩ : syracuseStep 4324967 = 6487451) B6487451
theorem B2883311 : Blo 1921435 2883311 := bstep (se 1 (by rfl) ⟨2162483, by rfl⟩ : syracuseStep 2883311 = 4324967) B4324967
theorem B1922207 : Blo 1921435 1922207 := bstep (se 1 (by rfl) ⟨1441655, by rfl⟩ : syracuseStep 1922207 = 2883311) B2883311
theorem B2883317 : Blo 1921435 2883317 := bbase (se 5 (by rfl) ⟨135155, by rfl⟩ : syracuseStep 2883317 = 270311) (by norm_num)
theorem B1922211 : Blo 1921435 1922211 := bstep (se 1 (by rfl) ⟨1441658, by rfl⟩ : syracuseStep 1922211 = 2883317) B2883317
theorem B3896885 : Blo 1921435 3896885 := bbase (se 5 (by rfl) ⟨182666, by rfl⟩ : syracuseStep 3896885 = 365333) (by norm_num)
theorem B2597923 : Blo 1921435 2597923 := bstep (se 1 (by rfl) ⟨1948442, by rfl⟩ : syracuseStep 2597923 = 3896885) B3896885
theorem B3463897 : Blo 1921435 3463897 := bstep (se 2 (by rfl) ⟨1298961, by rfl⟩ : syracuseStep 3463897 = 2597923) B2597923
theorem B4618529 : Blo 1921435 4618529 := bstep (se 2 (by rfl) ⟨1731948, by rfl⟩ : syracuseStep 4618529 = 3463897) B3463897
theorem B3079019 : Blo 1921435 3079019 := bstep (se 1 (by rfl) ⟨2309264, by rfl⟩ : syracuseStep 3079019 = 4618529) B4618529
theorem B8210717 : Blo 1921435 8210717 := bstep (se 3 (by rfl) ⟨1539509, by rfl⟩ : syracuseStep 8210717 = 3079019) B3079019
theorem B5473811 : Blo 1921435 5473811 := bstep (se 1 (by rfl) ⟨4105358, by rfl⟩ : syracuseStep 5473811 = 8210717) B8210717
theorem B3649207 : Blo 1921435 3649207 := bstep (se 1 (by rfl) ⟨2736905, by rfl⟩ : syracuseStep 3649207 = 5473811) B5473811
theorem B4865609 : Blo 1921435 4865609 := bstep (se 2 (by rfl) ⟨1824603, by rfl⟩ : syracuseStep 4865609 = 3649207) B3649207
theorem B3243739 : Blo 1921435 3243739 := bstep (se 1 (by rfl) ⟨2432804, by rfl⟩ : syracuseStep 3243739 = 4865609) B4865609
theorem B4324985 : Blo 1921435 4324985 := bstep (se 2 (by rfl) ⟨1621869, by rfl⟩ : syracuseStep 4324985 = 3243739) B3243739
theorem B2883323 : Blo 1921435 2883323 := bstep (se 1 (by rfl) ⟨2162492, by rfl⟩ : syracuseStep 2883323 = 4324985) B4324985
theorem B1922215 : Blo 1921435 1922215 := bstep (se 1 (by rfl) ⟨1441661, by rfl⟩ : syracuseStep 1922215 = 2883323) B2883323
theorem B2162497 : Blo 1921435 2162497 := bbase (se 2 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 2162497 = 1621873) (by norm_num)
theorem B2883329 : Blo 1921435 2883329 := bstep (se 2 (by rfl) ⟨1081248, by rfl⟩ : syracuseStep 2883329 = 2162497) B2162497
theorem B1922219 : Blo 1921435 1922219 := bstep (se 1 (by rfl) ⟨1441664, by rfl⟩ : syracuseStep 1922219 = 2883329) B2883329
theorem B4865629 : Blo 1921435 4865629 := bbase (se 3 (by rfl) ⟨912305, by rfl⟩ : syracuseStep 4865629 = 1824611) (by norm_num)
theorem B6487505 : Blo 1921435 6487505 := bstep (se 2 (by rfl) ⟨2432814, by rfl⟩ : syracuseStep 6487505 = 4865629) B4865629
theorem B4325003 : Blo 1921435 4325003 := bstep (se 1 (by rfl) ⟨3243752, by rfl⟩ : syracuseStep 4325003 = 6487505) B6487505
theorem B2883335 : Blo 1921435 2883335 := bstep (se 1 (by rfl) ⟨2162501, by rfl⟩ : syracuseStep 2883335 = 4325003) B4325003
theorem B1922223 : Blo 1921435 1922223 := bstep (se 1 (by rfl) ⟨1441667, by rfl⟩ : syracuseStep 1922223 = 2883335) B2883335
theorem B2883341 : Blo 1921435 2883341 := bbase (se 3 (by rfl) ⟨540626, by rfl⟩ : syracuseStep 2883341 = 1081253) (by norm_num)
theorem B1922227 : Blo 1921435 1922227 := bstep (se 1 (by rfl) ⟨1441670, by rfl⟩ : syracuseStep 1922227 = 2883341) B2883341
theorem B4325021 : Blo 1921435 4325021 := bbase (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) (by norm_num)
theorem B2883347 : Blo 1921435 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B1922231 : Blo 1921435 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B3243773 : Blo 1921435 3243773 := bbase (se 3 (by rfl) ⟨608207, by rfl⟩ : syracuseStep 3243773 = 1216415) (by norm_num)
theorem B2162515 : Blo 1921435 2162515 := bstep (se 1 (by rfl) ⟨1621886, by rfl⟩ : syracuseStep 2162515 = 3243773) B3243773
theorem B2883353 : Blo 1921435 2883353 := bstep (se 2 (by rfl) ⟨1081257, by rfl⟩ : syracuseStep 2883353 = 2162515) B2162515
theorem B1922235 : Blo 1921435 1922235 := bstep (se 1 (by rfl) ⟨1441676, by rfl⟩ : syracuseStep 1922235 = 2883353) B2883353
theorem B2309293 : Blo 1921435 2309293 := bbase (se 3 (by rfl) ⟨432992, by rfl⟩ : syracuseStep 2309293 = 865985) (by norm_num)
theorem B3079057 : Blo 1921435 3079057 := bstep (se 2 (by rfl) ⟨1154646, by rfl⟩ : syracuseStep 3079057 = 2309293) B2309293
theorem B4105409 : Blo 1921435 4105409 := bstep (se 2 (by rfl) ⟨1539528, by rfl⟩ : syracuseStep 4105409 = 3079057) B3079057
theorem B10947757 : Blo 1921435 10947757 := bstep (se 3 (by rfl) ⟨2052704, by rfl⟩ : syracuseStep 10947757 = 4105409) B4105409
theorem B14597009 : Blo 1921435 14597009 := bstep (se 2 (by rfl) ⟨5473878, by rfl⟩ : syracuseStep 14597009 = 10947757) B10947757
theorem B9731339 : Blo 1921435 9731339 := bstep (se 1 (by rfl) ⟨7298504, by rfl⟩ : syracuseStep 9731339 = 14597009) B14597009
theorem B6487559 : Blo 1921435 6487559 := bstep (se 1 (by rfl) ⟨4865669, by rfl⟩ : syracuseStep 6487559 = 9731339) B9731339
theorem B4325039 : Blo 1921435 4325039 := bstep (se 1 (by rfl) ⟨3243779, by rfl⟩ : syracuseStep 4325039 = 6487559) B6487559
theorem B2883359 : Blo 1921435 2883359 := bstep (se 1 (by rfl) ⟨2162519, by rfl⟩ : syracuseStep 2883359 = 4325039) B4325039
theorem B1922239 : Blo 1921435 1922239 := bstep (se 1 (by rfl) ⟨1441679, by rfl⟩ : syracuseStep 1922239 = 2883359) B2883359
theorem B2883365 : Blo 1921435 2883365 := bbase (se 4 (by rfl) ⟨270315, by rfl⟩ : syracuseStep 2883365 = 540631) (by norm_num)
theorem B1922243 : Blo 1921435 1922243 := bstep (se 1 (by rfl) ⟨1441682, by rfl⟩ : syracuseStep 1922243 = 2883365) B2883365
theorem B2432845 : Blo 1921435 2432845 := bbase (se 3 (by rfl) ⟨456158, by rfl⟩ : syracuseStep 2432845 = 912317) (by norm_num)
theorem B3243793 : Blo 1921435 3243793 := bstep (se 2 (by rfl) ⟨1216422, by rfl⟩ : syracuseStep 3243793 = 2432845) B2432845
theorem B4325057 : Blo 1921435 4325057 := bstep (se 2 (by rfl) ⟨1621896, by rfl⟩ : syracuseStep 4325057 = 3243793) B3243793
theorem B2883371 : Blo 1921435 2883371 := bstep (se 1 (by rfl) ⟨2162528, by rfl⟩ : syracuseStep 2883371 = 4325057) B4325057
theorem B1922247 : Blo 1921435 1922247 := bstep (se 1 (by rfl) ⟨1441685, by rfl⟩ : syracuseStep 1922247 = 2883371) B2883371
theorem B2162533 : Blo 1921435 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B2883377 : Blo 1921435 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B1922251 : Blo 1921435 1922251 := bstep (se 1 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 1922251 = 2883377) B2883377
theorem B5473925 : Blo 1921435 5473925 := bbase (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) (by norm_num)
theorem B3649283 : Blo 1921435 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B2432855 : Blo 1921435 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B6487613 : Blo 1921435 6487613 := bstep (se 3 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 6487613 = 2432855) B2432855
theorem B4325075 : Blo 1921435 4325075 := bstep (se 1 (by rfl) ⟨3243806, by rfl⟩ : syracuseStep 4325075 = 6487613) B6487613
theorem B2883383 : Blo 1921435 2883383 := bstep (se 1 (by rfl) ⟨2162537, by rfl⟩ : syracuseStep 2883383 = 4325075) B4325075
theorem B1922255 : Blo 1921435 1922255 := bstep (se 1 (by rfl) ⟨1441691, by rfl⟩ : syracuseStep 1922255 = 2883383) B2883383
theorem B2883389 : Blo 1921435 2883389 := bbase (se 3 (by rfl) ⟨540635, by rfl⟩ : syracuseStep 2883389 = 1081271) (by norm_num)
theorem B1922259 : Blo 1921435 1922259 := bstep (se 1 (by rfl) ⟨1441694, by rfl⟩ : syracuseStep 1922259 = 2883389) B2883389
theorem B4325093 : Blo 1921435 4325093 := bbase (se 4 (by rfl) ⟨405477, by rfl⟩ : syracuseStep 4325093 = 810955) (by norm_num)
theorem B2883395 : Blo 1921435 2883395 := bstep (se 1 (by rfl) ⟨2162546, by rfl⟩ : syracuseStep 2883395 = 4325093) B4325093
theorem B1922263 : Blo 1921435 1922263 := bstep (se 1 (by rfl) ⟨1441697, by rfl⟩ : syracuseStep 1922263 = 2883395) B2883395
theorem B4865741 : Blo 1921435 4865741 := bbase (se 3 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 4865741 = 1824653) (by norm_num)
theorem B3243827 : Blo 1921435 3243827 := bstep (se 1 (by rfl) ⟨2432870, by rfl⟩ : syracuseStep 3243827 = 4865741) B4865741
theorem B2162551 : Blo 1921435 2162551 := bstep (se 1 (by rfl) ⟨1621913, by rfl⟩ : syracuseStep 2162551 = 3243827) B3243827
theorem B2883401 : Blo 1921435 2883401 := bstep (se 2 (by rfl) ⟨1081275, by rfl⟩ : syracuseStep 2883401 = 2162551) B2162551
theorem B1922267 : Blo 1921435 1922267 := bstep (se 1 (by rfl) ⟨1441700, by rfl⟩ : syracuseStep 1922267 = 2883401) B2883401
theorem B3079109 : Blo 1921435 3079109 := bbase (se 4 (by rfl) ⟨288666, by rfl⟩ : syracuseStep 3079109 = 577333) (by norm_num)
theorem B2052739 : Blo 1921435 2052739 := bstep (se 1 (by rfl) ⟨1539554, by rfl⟩ : syracuseStep 2052739 = 3079109) B3079109
theorem B2736985 : Blo 1921435 2736985 := bstep (se 2 (by rfl) ⟨1026369, by rfl⟩ : syracuseStep 2736985 = 2052739) B2052739
theorem B3649313 : Blo 1921435 3649313 := bstep (se 2 (by rfl) ⟨1368492, by rfl⟩ : syracuseStep 3649313 = 2736985) B2736985
theorem B9731501 : Blo 1921435 9731501 := bstep (se 3 (by rfl) ⟨1824656, by rfl⟩ : syracuseStep 9731501 = 3649313) B3649313
theorem B6487667 : Blo 1921435 6487667 := bstep (se 1 (by rfl) ⟨4865750, by rfl⟩ : syracuseStep 6487667 = 9731501) B9731501
theorem B4325111 : Blo 1921435 4325111 := bstep (se 1 (by rfl) ⟨3243833, by rfl⟩ : syracuseStep 4325111 = 6487667) B6487667
theorem B2883407 : Blo 1921435 2883407 := bstep (se 1 (by rfl) ⟨2162555, by rfl⟩ : syracuseStep 2883407 = 4325111) B4325111
theorem B1922271 : Blo 1921435 1922271 := bstep (se 1 (by rfl) ⟨1441703, by rfl⟩ : syracuseStep 1922271 = 2883407) B2883407
theorem B2883413 : Blo 1921435 2883413 := bbase (se 9 (by rfl) ⟨8447, by rfl⟩ : syracuseStep 2883413 = 16895) (by norm_num)
theorem B1922275 : Blo 1921435 1922275 := bstep (se 1 (by rfl) ⟨1441706, by rfl⟩ : syracuseStep 1922275 = 2883413) B2883413
theorem B9237365 : Blo 1921435 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B6158243 : Blo 1921435 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B4105495 : Blo 1921435 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B5473993 : Blo 1921435 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B7298657 : Blo 1921435 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B4865771 : Blo 1921435 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B3243847 : Blo 1921435 3243847 := bstep (se 1 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 3243847 = 4865771) B4865771
theorem B4325129 : Blo 1921435 4325129 := bstep (se 2 (by rfl) ⟨1621923, by rfl⟩ : syracuseStep 4325129 = 3243847) B3243847
theorem B2883419 : Blo 1921435 2883419 := bstep (se 1 (by rfl) ⟨2162564, by rfl⟩ : syracuseStep 2883419 = 4325129) B4325129
theorem B1922279 : Blo 1921435 1922279 := bstep (se 1 (by rfl) ⟨1441709, by rfl⟩ : syracuseStep 1922279 = 2883419) B2883419
theorem B2162569 : Blo 1921435 2162569 := bbase (se 2 (by rfl) ⟨810963, by rfl⟩ : syracuseStep 2162569 = 1621927) (by norm_num)
theorem B2883425 : Blo 1921435 2883425 := bstep (se 2 (by rfl) ⟨1081284, by rfl⟩ : syracuseStep 2883425 = 2162569) B2162569
theorem B1922283 : Blo 1921435 1922283 := bstep (se 1 (by rfl) ⟨1441712, by rfl⟩ : syracuseStep 1922283 = 2883425) B2883425
theorem B3699133 : Blo 1921435 3699133 := bbase (se 3 (by rfl) ⟨693587, by rfl⟩ : syracuseStep 3699133 = 1387175) (by norm_num)
theorem B78914837 : Blo 1921435 78914837 := bstep (se 6 (by rfl) ⟨1849566, by rfl⟩ : syracuseStep 78914837 = 3699133) B3699133
theorem B210439565 : Blo 1921435 210439565 := bstep (se 3 (by rfl) ⟨39457418, by rfl⟩ : syracuseStep 210439565 = 78914837) B78914837
theorem B140293043 : Blo 1921435 140293043 := bstep (se 1 (by rfl) ⟨105219782, by rfl⟩ : syracuseStep 140293043 = 210439565) B210439565
theorem B93528695 : Blo 1921435 93528695 := bstep (se 1 (by rfl) ⟨70146521, by rfl⟩ : syracuseStep 93528695 = 140293043) B140293043
theorem B62352463 : Blo 1921435 62352463 := bstep (se 1 (by rfl) ⟨46764347, by rfl⟩ : syracuseStep 62352463 = 93528695) B93528695
theorem B83136617 : Blo 1921435 83136617 := bstep (se 2 (by rfl) ⟨31176231, by rfl⟩ : syracuseStep 83136617 = 62352463) B62352463
theorem B55424411 : Blo 1921435 55424411 := bstep (se 1 (by rfl) ⟨41568308, by rfl⟩ : syracuseStep 55424411 = 83136617) B83136617
theorem B36949607 : Blo 1921435 36949607 := bstep (se 1 (by rfl) ⟨27712205, by rfl⟩ : syracuseStep 36949607 = 55424411) B55424411
theorem B24633071 : Blo 1921435 24633071 := bstep (se 1 (by rfl) ⟨18474803, by rfl⟩ : syracuseStep 24633071 = 36949607) B36949607
theorem B16422047 : Blo 1921435 16422047 := bstep (se 1 (by rfl) ⟨12316535, by rfl⟩ : syracuseStep 16422047 = 24633071) B24633071
theorem B10948031 : Blo 1921435 10948031 := bstep (se 1 (by rfl) ⟨8211023, by rfl⟩ : syracuseStep 10948031 = 16422047) B16422047
theorem B7298687 : Blo 1921435 7298687 := bstep (se 1 (by rfl) ⟨5474015, by rfl⟩ : syracuseStep 7298687 = 10948031) B10948031
theorem B4865791 : Blo 1921435 4865791 := bstep (se 1 (by rfl) ⟨3649343, by rfl⟩ : syracuseStep 4865791 = 7298687) B7298687
theorem B6487721 : Blo 1921435 6487721 := bstep (se 2 (by rfl) ⟨2432895, by rfl⟩ : syracuseStep 6487721 = 4865791) B4865791
theorem B4325147 : Blo 1921435 4325147 := bstep (se 1 (by rfl) ⟨3243860, by rfl⟩ : syracuseStep 4325147 = 6487721) B6487721
theorem B2883431 : Blo 1921435 2883431 := bstep (se 1 (by rfl) ⟨2162573, by rfl⟩ : syracuseStep 2883431 = 4325147) B4325147
theorem B1922287 : Blo 1921435 1922287 := bstep (se 1 (by rfl) ⟨1441715, by rfl⟩ : syracuseStep 1922287 = 2883431) B2883431
theorem B2883437 : Blo 1921435 2883437 := bbase (se 3 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 2883437 = 1081289) (by norm_num)
theorem B1922291 : Blo 1921435 1922291 := bstep (se 1 (by rfl) ⟨1441718, by rfl⟩ : syracuseStep 1922291 = 2883437) B2883437
theorem B4325165 : Blo 1921435 4325165 := bbase (se 3 (by rfl) ⟨810968, by rfl⟩ : syracuseStep 4325165 = 1621937) (by norm_num)
theorem B2883443 : Blo 1921435 2883443 := bstep (se 1 (by rfl) ⟨2162582, by rfl⟩ : syracuseStep 2883443 = 4325165) B4325165
theorem B1922295 : Blo 1921435 1922295 := bstep (se 1 (by rfl) ⟨1441721, by rfl⟩ : syracuseStep 1922295 = 2883443) B2883443
theorem B8211077 : Blo 1921435 8211077 := bbase (se 4 (by rfl) ⟨769788, by rfl⟩ : syracuseStep 8211077 = 1539577) (by norm_num)
theorem B5474051 : Blo 1921435 5474051 := bstep (se 1 (by rfl) ⟨4105538, by rfl⟩ : syracuseStep 5474051 = 8211077) B8211077
theorem B3649367 : Blo 1921435 3649367 := bstep (se 1 (by rfl) ⟨2737025, by rfl⟩ : syracuseStep 3649367 = 5474051) B5474051
theorem B2432911 : Blo 1921435 2432911 := bstep (se 1 (by rfl) ⟨1824683, by rfl⟩ : syracuseStep 2432911 = 3649367) B3649367
theorem B3243881 : Blo 1921435 3243881 := bstep (se 2 (by rfl) ⟨1216455, by rfl⟩ : syracuseStep 3243881 = 2432911) B2432911
theorem B2162587 : Blo 1921435 2162587 := bstep (se 1 (by rfl) ⟨1621940, by rfl⟩ : syracuseStep 2162587 = 3243881) B3243881
theorem B2883449 : Blo 1921435 2883449 := bstep (se 2 (by rfl) ⟨1081293, by rfl⟩ : syracuseStep 2883449 = 2162587) B2162587
theorem B1922299 : Blo 1921435 1922299 := bstep (se 1 (by rfl) ⟨1441724, by rfl⟩ : syracuseStep 1922299 = 2883449) B2883449
theorem B2922797 : Blo 1921435 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B1948531 : Blo 1921435 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B2598041 : Blo 1921435 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B6928109 : Blo 1921435 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B4618739 : Blo 1921435 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B12316637 : Blo 1921435 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B32844365 : Blo 1921435 32844365 := bstep (se 3 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 32844365 = 12316637) B12316637
theorem B21896243 : Blo 1921435 21896243 := bstep (se 1 (by rfl) ⟨16422182, by rfl⟩ : syracuseStep 21896243 = 32844365) B32844365
theorem B14597495 : Blo 1921435 14597495 := bstep (se 1 (by rfl) ⟨10948121, by rfl⟩ : syracuseStep 14597495 = 21896243) B21896243
theorem B9731663 : Blo 1921435 9731663 := bstep (se 1 (by rfl) ⟨7298747, by rfl⟩ : syracuseStep 9731663 = 14597495) B14597495
theorem B6487775 : Blo 1921435 6487775 := bstep (se 1 (by rfl) ⟨4865831, by rfl⟩ : syracuseStep 6487775 = 9731663) B9731663
theorem B4325183 : Blo 1921435 4325183 := bstep (se 1 (by rfl) ⟨3243887, by rfl⟩ : syracuseStep 4325183 = 6487775) B6487775
theorem B2883455 : Blo 1921435 2883455 := bstep (se 1 (by rfl) ⟨2162591, by rfl⟩ : syracuseStep 2883455 = 4325183) B4325183
theorem B1922303 : Blo 1921435 1922303 := bstep (se 1 (by rfl) ⟨1441727, by rfl⟩ : syracuseStep 1922303 = 2883455) B2883455
theorem B2883461 : Blo 1921435 2883461 := bbase (se 4 (by rfl) ⟨270324, by rfl⟩ : syracuseStep 2883461 = 540649) (by norm_num)
theorem B1922307 : Blo 1921435 1922307 := bstep (se 1 (by rfl) ⟨1441730, by rfl⟩ : syracuseStep 1922307 = 2883461) B2883461
theorem B3243901 : Blo 1921435 3243901 := bbase (se 3 (by rfl) ⟨608231, by rfl⟩ : syracuseStep 3243901 = 1216463) (by norm_num)
theorem B4325201 : Blo 1921435 4325201 := bstep (se 2 (by rfl) ⟨1621950, by rfl⟩ : syracuseStep 4325201 = 3243901) B3243901
theorem B2883467 : Blo 1921435 2883467 := bstep (se 1 (by rfl) ⟨2162600, by rfl⟩ : syracuseStep 2883467 = 4325201) B4325201
theorem B1922311 : Blo 1921435 1922311 := bstep (se 1 (by rfl) ⟨1441733, by rfl⟩ : syracuseStep 1922311 = 2883467) B2883467
theorem B2162605 : Blo 1921435 2162605 := bbase (se 3 (by rfl) ⟨405488, by rfl⟩ : syracuseStep 2162605 = 810977) (by norm_num)
theorem B2883473 : Blo 1921435 2883473 := bstep (se 2 (by rfl) ⟨1081302, by rfl⟩ : syracuseStep 2883473 = 2162605) B2162605
theorem B1922315 : Blo 1921435 1922315 := bstep (se 1 (by rfl) ⟨1441736, by rfl⟩ : syracuseStep 1922315 = 2883473) B2883473
theorem B6487829 : Blo 1921435 6487829 := bbase (se 6 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 6487829 = 304117) (by norm_num)
theorem B4325219 : Blo 1921435 4325219 := bstep (se 1 (by rfl) ⟨3243914, by rfl⟩ : syracuseStep 4325219 = 6487829) B6487829
theorem B2883479 : Blo 1921435 2883479 := bstep (se 1 (by rfl) ⟨2162609, by rfl⟩ : syracuseStep 2883479 = 4325219) B4325219
theorem B1922319 : Blo 1921435 1922319 := bstep (se 1 (by rfl) ⟨1441739, by rfl⟩ : syracuseStep 1922319 = 2883479) B2883479
theorem B2883485 : Blo 1921435 2883485 := bbase (se 3 (by rfl) ⟨540653, by rfl⟩ : syracuseStep 2883485 = 1081307) (by norm_num)
theorem B1922323 : Blo 1921435 1922323 := bstep (se 1 (by rfl) ⟨1441742, by rfl⟩ : syracuseStep 1922323 = 2883485) B2883485
theorem B4325237 : Blo 1921435 4325237 := bbase (se 5 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 4325237 = 405491) (by norm_num)
theorem B2883491 : Blo 1921435 2883491 := bstep (se 1 (by rfl) ⟨2162618, by rfl⟩ : syracuseStep 2883491 = 4325237) B4325237
theorem B1922327 : Blo 1921435 1922327 := bstep (se 1 (by rfl) ⟨1441745, by rfl⟩ : syracuseStep 1922327 = 2883491) B2883491
theorem B2340913 : Blo 1921435 2340913 := bbase (se 2 (by rfl) ⟨877842, by rfl⟩ : syracuseStep 2340913 = 1755685) (by norm_num)
theorem B3121217 : Blo 1921435 3121217 := bstep (se 2 (by rfl) ⟨1170456, by rfl⟩ : syracuseStep 3121217 = 2340913) B2340913
theorem B2080811 : Blo 1921435 2080811 := bstep (se 1 (by rfl) ⟨1560608, by rfl⟩ : syracuseStep 2080811 = 3121217) B3121217
theorem B5548829 : Blo 1921435 5548829 := bstep (se 3 (by rfl) ⟨1040405, by rfl⟩ : syracuseStep 5548829 = 2080811) B2080811
theorem B14796877 : Blo 1921435 14796877 := bstep (se 3 (by rfl) ⟨2774414, by rfl⟩ : syracuseStep 14796877 = 5548829) B5548829
theorem B19729169 : Blo 1921435 19729169 := bstep (se 2 (by rfl) ⟨7398438, by rfl⟩ : syracuseStep 19729169 = 14796877) B14796877
theorem B13152779 : Blo 1921435 13152779 := bstep (se 1 (by rfl) ⟨9864584, by rfl⟩ : syracuseStep 13152779 = 19729169) B19729169
theorem B8768519 : Blo 1921435 8768519 := bstep (se 1 (by rfl) ⟨6576389, by rfl⟩ : syracuseStep 8768519 = 13152779) B13152779
theorem B5845679 : Blo 1921435 5845679 := bstep (se 1 (by rfl) ⟨4384259, by rfl⟩ : syracuseStep 5845679 = 8768519) B8768519
theorem B3897119 : Blo 1921435 3897119 := bstep (se 1 (by rfl) ⟨2922839, by rfl⟩ : syracuseStep 3897119 = 5845679) B5845679
theorem B10392317 : Blo 1921435 10392317 := bstep (se 3 (by rfl) ⟨1948559, by rfl⟩ : syracuseStep 10392317 = 3897119) B3897119
theorem B6928211 : Blo 1921435 6928211 := bstep (se 1 (by rfl) ⟨5196158, by rfl⟩ : syracuseStep 6928211 = 10392317) B10392317
theorem B18475229 : Blo 1921435 18475229 := bstep (se 3 (by rfl) ⟨3464105, by rfl⟩ : syracuseStep 18475229 = 6928211) B6928211
theorem B12316819 : Blo 1921435 12316819 := bstep (se 1 (by rfl) ⟨9237614, by rfl⟩ : syracuseStep 12316819 = 18475229) B18475229
theorem B16422425 : Blo 1921435 16422425 := bstep (se 2 (by rfl) ⟨6158409, by rfl⟩ : syracuseStep 16422425 = 12316819) B12316819
theorem B10948283 : Blo 1921435 10948283 := bstep (se 1 (by rfl) ⟨8211212, by rfl⟩ : syracuseStep 10948283 = 16422425) B16422425
theorem B7298855 : Blo 1921435 7298855 := bstep (se 1 (by rfl) ⟨5474141, by rfl⟩ : syracuseStep 7298855 = 10948283) B10948283
theorem B4865903 : Blo 1921435 4865903 := bstep (se 1 (by rfl) ⟨3649427, by rfl⟩ : syracuseStep 4865903 = 7298855) B7298855
theorem B3243935 : Blo 1921435 3243935 := bstep (se 1 (by rfl) ⟨2432951, by rfl⟩ : syracuseStep 3243935 = 4865903) B4865903
theorem B2162623 : Blo 1921435 2162623 := bstep (se 1 (by rfl) ⟨1621967, by rfl⟩ : syracuseStep 2162623 = 3243935) B3243935
theorem B2883497 : Blo 1921435 2883497 := bstep (se 2 (by rfl) ⟨1081311, by rfl⟩ : syracuseStep 2883497 = 2162623) B2162623
theorem B1922331 : Blo 1921435 1922331 := bstep (se 1 (by rfl) ⟨1441748, by rfl⟩ : syracuseStep 1922331 = 2883497) B2883497
theorem B7298869 : Blo 1921435 7298869 := bbase (se 5 (by rfl) ⟨342134, by rfl⟩ : syracuseStep 7298869 = 684269) (by norm_num)
theorem B9731825 : Blo 1921435 9731825 := bstep (se 2 (by rfl) ⟨3649434, by rfl⟩ : syracuseStep 9731825 = 7298869) B7298869
theorem B6487883 : Blo 1921435 6487883 := bstep (se 1 (by rfl) ⟨4865912, by rfl⟩ : syracuseStep 6487883 = 9731825) B9731825
theorem B4325255 : Blo 1921435 4325255 := bstep (se 1 (by rfl) ⟨3243941, by rfl⟩ : syracuseStep 4325255 = 6487883) B6487883
theorem B2883503 : Blo 1921435 2883503 := bstep (se 1 (by rfl) ⟨2162627, by rfl⟩ : syracuseStep 2883503 = 4325255) B4325255
theorem B1922335 : Blo 1921435 1922335 := bstep (se 1 (by rfl) ⟨1441751, by rfl⟩ : syracuseStep 1922335 = 2883503) B2883503
theorem B2883509 : Blo 1921435 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B1922339 : Blo 1921435 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B4865933 : Blo 1921435 4865933 := bbase (se 3 (by rfl) ⟨912362, by rfl⟩ : syracuseStep 4865933 = 1824725) (by norm_num)
theorem B3243955 : Blo 1921435 3243955 := bstep (se 1 (by rfl) ⟨2432966, by rfl⟩ : syracuseStep 3243955 = 4865933) B4865933
theorem B4325273 : Blo 1921435 4325273 := bstep (se 2 (by rfl) ⟨1621977, by rfl⟩ : syracuseStep 4325273 = 3243955) B3243955
theorem B2883515 : Blo 1921435 2883515 := bstep (se 1 (by rfl) ⟨2162636, by rfl⟩ : syracuseStep 2883515 = 4325273) B4325273
theorem B1922343 : Blo 1921435 1922343 := bstep (se 1 (by rfl) ⟨1441757, by rfl⟩ : syracuseStep 1922343 = 2883515) B2883515
theorem B2162641 : Blo 1921435 2162641 := bbase (se 2 (by rfl) ⟨810990, by rfl⟩ : syracuseStep 2162641 = 1621981) (by norm_num)
theorem B2883521 : Blo 1921435 2883521 := bstep (se 2 (by rfl) ⟨1081320, by rfl⟩ : syracuseStep 2883521 = 2162641) B2162641
theorem B1922347 : Blo 1921435 1922347 := bstep (se 1 (by rfl) ⟨1441760, by rfl⟩ : syracuseStep 1922347 = 2883521) B2883521
theorem B3079237 : Blo 1921435 3079237 := bbase (se 4 (by rfl) ⟨288678, by rfl⟩ : syracuseStep 3079237 = 577357) (by norm_num)
theorem B4105649 : Blo 1921435 4105649 := bstep (se 2 (by rfl) ⟨1539618, by rfl⟩ : syracuseStep 4105649 = 3079237) B3079237
theorem B2737099 : Blo 1921435 2737099 := bstep (se 1 (by rfl) ⟨2052824, by rfl⟩ : syracuseStep 2737099 = 4105649) B4105649
theorem B3649465 : Blo 1921435 3649465 := bstep (se 2 (by rfl) ⟨1368549, by rfl⟩ : syracuseStep 3649465 = 2737099) B2737099
theorem B4865953 : Blo 1921435 4865953 := bstep (se 2 (by rfl) ⟨1824732, by rfl⟩ : syracuseStep 4865953 = 3649465) B3649465
theorem B6487937 : Blo 1921435 6487937 := bstep (se 2 (by rfl) ⟨2432976, by rfl⟩ : syracuseStep 6487937 = 4865953) B4865953
theorem B4325291 : Blo 1921435 4325291 := bstep (se 1 (by rfl) ⟨3243968, by rfl⟩ : syracuseStep 4325291 = 6487937) B6487937
theorem B2883527 : Blo 1921435 2883527 := bstep (se 1 (by rfl) ⟨2162645, by rfl⟩ : syracuseStep 2883527 = 4325291) B4325291
theorem B1922351 : Blo 1921435 1922351 := bstep (se 1 (by rfl) ⟨1441763, by rfl⟩ : syracuseStep 1922351 = 2883527) B2883527
theorem B2883533 : Blo 1921435 2883533 := bbase (se 3 (by rfl) ⟨540662, by rfl⟩ : syracuseStep 2883533 = 1081325) (by norm_num)
theorem B1922355 : Blo 1921435 1922355 := bstep (se 1 (by rfl) ⟨1441766, by rfl⟩ : syracuseStep 1922355 = 2883533) B2883533
theorem B4325309 : Blo 1921435 4325309 := bbase (se 3 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 4325309 = 1621991) (by norm_num)
theorem B2883539 : Blo 1921435 2883539 := bstep (se 1 (by rfl) ⟨2162654, by rfl⟩ : syracuseStep 2883539 = 4325309) B4325309
theorem B1922359 : Blo 1921435 1922359 := bstep (se 1 (by rfl) ⟨1441769, by rfl⟩ : syracuseStep 1922359 = 2883539) B2883539
theorem B3243989 : Blo 1921435 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B2162659 : Blo 1921435 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B2883545 : Blo 1921435 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B1922363 : Blo 1921435 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B8211365 : Blo 1921435 8211365 := bbase (se 4 (by rfl) ⟨769815, by rfl⟩ : syracuseStep 8211365 = 1539631) (by norm_num)
theorem B5474243 : Blo 1921435 5474243 := bstep (se 1 (by rfl) ⟨4105682, by rfl⟩ : syracuseStep 5474243 = 8211365) B8211365
theorem B14597981 : Blo 1921435 14597981 := bstep (se 3 (by rfl) ⟨2737121, by rfl⟩ : syracuseStep 14597981 = 5474243) B5474243
theorem B9731987 : Blo 1921435 9731987 := bstep (se 1 (by rfl) ⟨7298990, by rfl⟩ : syracuseStep 9731987 = 14597981) B14597981
theorem B6487991 : Blo 1921435 6487991 := bstep (se 1 (by rfl) ⟨4865993, by rfl⟩ : syracuseStep 6487991 = 9731987) B9731987
theorem B4325327 : Blo 1921435 4325327 := bstep (se 1 (by rfl) ⟨3243995, by rfl⟩ : syracuseStep 4325327 = 6487991) B6487991
theorem B2883551 : Blo 1921435 2883551 := bstep (se 1 (by rfl) ⟨2162663, by rfl⟩ : syracuseStep 2883551 = 4325327) B4325327
theorem B1922367 : Blo 1921435 1922367 := bstep (se 1 (by rfl) ⟨1441775, by rfl⟩ : syracuseStep 1922367 = 2883551) B2883551
theorem B2883557 : Blo 1921435 2883557 := bbase (se 4 (by rfl) ⟨270333, by rfl⟩ : syracuseStep 2883557 = 540667) (by norm_num)
theorem B1922371 : Blo 1921435 1922371 := bstep (se 1 (by rfl) ⟨1441778, by rfl⟩ : syracuseStep 1922371 = 2883557) B2883557
theorem B7499557 : Blo 1921435 7499557 := bbase (se 4 (by rfl) ⟨703083, by rfl⟩ : syracuseStep 7499557 = 1406167) (by norm_num)
theorem B9999409 : Blo 1921435 9999409 := bstep (se 2 (by rfl) ⟨3749778, by rfl⟩ : syracuseStep 9999409 = 7499557) B7499557
theorem B13332545 : Blo 1921435 13332545 := bstep (se 2 (by rfl) ⟨4999704, by rfl⟩ : syracuseStep 13332545 = 9999409) B9999409
theorem B8888363 : Blo 1921435 8888363 := bstep (se 1 (by rfl) ⟨6666272, by rfl⟩ : syracuseStep 8888363 = 13332545) B13332545
theorem B5925575 : Blo 1921435 5925575 := bstep (se 1 (by rfl) ⟨4444181, by rfl⟩ : syracuseStep 5925575 = 8888363) B8888363
theorem B3950383 : Blo 1921435 3950383 := bstep (se 1 (by rfl) ⟨2962787, by rfl⟩ : syracuseStep 3950383 = 5925575) B5925575
theorem B5267177 : Blo 1921435 5267177 := bstep (se 2 (by rfl) ⟨1975191, by rfl⟩ : syracuseStep 5267177 = 3950383) B3950383
theorem B3511451 : Blo 1921435 3511451 := bstep (se 1 (by rfl) ⟨2633588, by rfl⟩ : syracuseStep 3511451 = 5267177) B5267177
theorem B9363869 : Blo 1921435 9363869 := bstep (se 3 (by rfl) ⟨1755725, by rfl⟩ : syracuseStep 9363869 = 3511451) B3511451
theorem B6242579 : Blo 1921435 6242579 := bstep (se 1 (by rfl) ⟨4681934, by rfl⟩ : syracuseStep 6242579 = 9363869) B9363869
theorem B4161719 : Blo 1921435 4161719 := bstep (se 1 (by rfl) ⟨3121289, by rfl⟩ : syracuseStep 4161719 = 6242579) B6242579
theorem B11097917 : Blo 1921435 11097917 := bstep (se 3 (by rfl) ⟨2080859, by rfl⟩ : syracuseStep 11097917 = 4161719) B4161719
theorem B7398611 : Blo 1921435 7398611 := bstep (se 1 (by rfl) ⟨5548958, by rfl⟩ : syracuseStep 7398611 = 11097917) B11097917
theorem B4932407 : Blo 1921435 4932407 := bstep (se 1 (by rfl) ⟨3699305, by rfl⟩ : syracuseStep 4932407 = 7398611) B7398611
theorem B3288271 : Blo 1921435 3288271 := bstep (se 1 (by rfl) ⟨2466203, by rfl⟩ : syracuseStep 3288271 = 4932407) B4932407
theorem B4384361 : Blo 1921435 4384361 := bstep (se 2 (by rfl) ⟨1644135, by rfl⟩ : syracuseStep 4384361 = 3288271) B3288271
theorem B2922907 : Blo 1921435 2922907 := bstep (se 1 (by rfl) ⟨2192180, by rfl⟩ : syracuseStep 2922907 = 4384361) B4384361
theorem B3897209 : Blo 1921435 3897209 := bstep (se 2 (by rfl) ⟨1461453, by rfl⟩ : syracuseStep 3897209 = 2922907) B2922907
theorem B2598139 : Blo 1921435 2598139 := bstep (se 1 (by rfl) ⟨1948604, by rfl⟩ : syracuseStep 2598139 = 3897209) B3897209
theorem B13856741 : Blo 1921435 13856741 := bstep (se 4 (by rfl) ⟨1299069, by rfl⟩ : syracuseStep 13856741 = 2598139) B2598139
theorem B9237827 : Blo 1921435 9237827 := bstep (se 1 (by rfl) ⟨6928370, by rfl⟩ : syracuseStep 9237827 = 13856741) B13856741
theorem B6158551 : Blo 1921435 6158551 := bstep (se 1 (by rfl) ⟨4618913, by rfl⟩ : syracuseStep 6158551 = 9237827) B9237827
theorem B8211401 : Blo 1921435 8211401 := bstep (se 2 (by rfl) ⟨3079275, by rfl⟩ : syracuseStep 8211401 = 6158551) B6158551
theorem B5474267 : Blo 1921435 5474267 := bstep (se 1 (by rfl) ⟨4105700, by rfl⟩ : syracuseStep 5474267 = 8211401) B8211401
theorem B3649511 : Blo 1921435 3649511 := bstep (se 1 (by rfl) ⟨2737133, by rfl⟩ : syracuseStep 3649511 = 5474267) B5474267
theorem B2433007 : Blo 1921435 2433007 := bstep (se 1 (by rfl) ⟨1824755, by rfl⟩ : syracuseStep 2433007 = 3649511) B3649511
theorem B3244009 : Blo 1921435 3244009 := bstep (se 2 (by rfl) ⟨1216503, by rfl⟩ : syracuseStep 3244009 = 2433007) B2433007
theorem B4325345 : Blo 1921435 4325345 := bstep (se 2 (by rfl) ⟨1622004, by rfl⟩ : syracuseStep 4325345 = 3244009) B3244009
theorem B2883563 : Blo 1921435 2883563 := bstep (se 1 (by rfl) ⟨2162672, by rfl⟩ : syracuseStep 2883563 = 4325345) B4325345
theorem B1922375 : Blo 1921435 1922375 := bstep (se 1 (by rfl) ⟨1441781, by rfl⟩ : syracuseStep 1922375 = 2883563) B2883563
theorem B2162677 : Blo 1921435 2162677 := bbase (se 5 (by rfl) ⟨101375, by rfl⟩ : syracuseStep 2162677 = 202751) (by norm_num)
theorem B2883569 : Blo 1921435 2883569 := bstep (se 2 (by rfl) ⟨1081338, by rfl⟩ : syracuseStep 2883569 = 2162677) B2162677
theorem B1922379 : Blo 1921435 1922379 := bstep (se 1 (by rfl) ⟨1441784, by rfl⟩ : syracuseStep 1922379 = 2883569) B2883569
theorem B2433017 : Blo 1921435 2433017 := bbase (se 2 (by rfl) ⟨912381, by rfl⟩ : syracuseStep 2433017 = 1824763) (by norm_num)
theorem B6488045 : Blo 1921435 6488045 := bstep (se 3 (by rfl) ⟨1216508, by rfl⟩ : syracuseStep 6488045 = 2433017) B2433017
theorem B4325363 : Blo 1921435 4325363 := bstep (se 1 (by rfl) ⟨3244022, by rfl⟩ : syracuseStep 4325363 = 6488045) B6488045
theorem B2883575 : Blo 1921435 2883575 := bstep (se 1 (by rfl) ⟨2162681, by rfl⟩ : syracuseStep 2883575 = 4325363) B4325363
theorem B1922383 : Blo 1921435 1922383 := bstep (se 1 (by rfl) ⟨1441787, by rfl⟩ : syracuseStep 1922383 = 2883575) B2883575
theorem B2883581 : Blo 1921435 2883581 := bbase (se 3 (by rfl) ⟨540671, by rfl⟩ : syracuseStep 2883581 = 1081343) (by norm_num)
theorem B1922387 : Blo 1921435 1922387 := bstep (se 1 (by rfl) ⟨1441790, by rfl⟩ : syracuseStep 1922387 = 2883581) B2883581
theorem B4325381 : Blo 1921435 4325381 := bbase (se 4 (by rfl) ⟨405504, by rfl⟩ : syracuseStep 4325381 = 811009) (by norm_num)
theorem B2883587 : Blo 1921435 2883587 := bstep (se 1 (by rfl) ⟨2162690, by rfl⟩ : syracuseStep 2883587 = 4325381) B4325381
theorem B1922391 : Blo 1921435 1922391 := bstep (se 1 (by rfl) ⟨1441793, by rfl⟩ : syracuseStep 1922391 = 2883587) B2883587
theorem B3649549 : Blo 1921435 3649549 := bbase (se 3 (by rfl) ⟨684290, by rfl⟩ : syracuseStep 3649549 = 1368581) (by norm_num)
theorem B4866065 : Blo 1921435 4866065 := bstep (se 2 (by rfl) ⟨1824774, by rfl⟩ : syracuseStep 4866065 = 3649549) B3649549
theorem B3244043 : Blo 1921435 3244043 := bstep (se 1 (by rfl) ⟨2433032, by rfl⟩ : syracuseStep 3244043 = 4866065) B4866065
theorem B2162695 : Blo 1921435 2162695 := bstep (se 1 (by rfl) ⟨1622021, by rfl⟩ : syracuseStep 2162695 = 3244043) B3244043
theorem B2883593 : Blo 1921435 2883593 := bstep (se 2 (by rfl) ⟨1081347, by rfl⟩ : syracuseStep 2883593 = 2162695) B2162695
theorem B1922395 : Blo 1921435 1922395 := bstep (se 1 (by rfl) ⟨1441796, by rfl⟩ : syracuseStep 1922395 = 2883593) B2883593
theorem B9732149 : Blo 1921435 9732149 := bbase (se 5 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 9732149 = 912389) (by norm_num)
theorem B6488099 : Blo 1921435 6488099 := bstep (se 1 (by rfl) ⟨4866074, by rfl⟩ : syracuseStep 6488099 = 9732149) B9732149
theorem B4325399 : Blo 1921435 4325399 := bstep (se 1 (by rfl) ⟨3244049, by rfl⟩ : syracuseStep 4325399 = 6488099) B6488099
theorem B2883599 : Blo 1921435 2883599 := bstep (se 1 (by rfl) ⟨2162699, by rfl⟩ : syracuseStep 2883599 = 4325399) B4325399
theorem B1922399 : Blo 1921435 1922399 := bstep (se 1 (by rfl) ⟨1441799, by rfl⟩ : syracuseStep 1922399 = 2883599) B2883599
theorem B2883605 : Blo 1921435 2883605 := bbase (se 6 (by rfl) ⟨67584, by rfl⟩ : syracuseStep 2883605 = 135169) (by norm_num)
theorem B1922403 : Blo 1921435 1922403 := bstep (se 1 (by rfl) ⟨1441802, by rfl⟩ : syracuseStep 1922403 = 2883605) B2883605
theorem B23383637 : Blo 1921435 23383637 := bbase (se 8 (by rfl) ⟨137013, by rfl⟩ : syracuseStep 23383637 = 274027) (by norm_num)
theorem B15589091 : Blo 1921435 15589091 := bstep (se 1 (by rfl) ⟨11691818, by rfl⟩ : syracuseStep 15589091 = 23383637) B23383637
theorem B10392727 : Blo 1921435 10392727 := bstep (se 1 (by rfl) ⟨7794545, by rfl⟩ : syracuseStep 10392727 = 15589091) B15589091
theorem B13856969 : Blo 1921435 13856969 := bstep (se 2 (by rfl) ⟨5196363, by rfl⟩ : syracuseStep 13856969 = 10392727) B10392727
theorem B9237979 : Blo 1921435 9237979 := bstep (se 1 (by rfl) ⟨6928484, by rfl⟩ : syracuseStep 9237979 = 13856969) B13856969
theorem B12317305 : Blo 1921435 12317305 := bstep (se 2 (by rfl) ⟨4618989, by rfl⟩ : syracuseStep 12317305 = 9237979) B9237979
theorem B16423073 : Blo 1921435 16423073 := bstep (se 2 (by rfl) ⟨6158652, by rfl⟩ : syracuseStep 16423073 = 12317305) B12317305
theorem B10948715 : Blo 1921435 10948715 := bstep (se 1 (by rfl) ⟨8211536, by rfl⟩ : syracuseStep 10948715 = 16423073) B16423073
theorem B7299143 : Blo 1921435 7299143 := bstep (se 1 (by rfl) ⟨5474357, by rfl⟩ : syracuseStep 7299143 = 10948715) B10948715
theorem B4866095 : Blo 1921435 4866095 := bstep (se 1 (by rfl) ⟨3649571, by rfl⟩ : syracuseStep 4866095 = 7299143) B7299143
theorem B3244063 : Blo 1921435 3244063 := bstep (se 1 (by rfl) ⟨2433047, by rfl⟩ : syracuseStep 3244063 = 4866095) B4866095
theorem B4325417 : Blo 1921435 4325417 := bstep (se 2 (by rfl) ⟨1622031, by rfl⟩ : syracuseStep 4325417 = 3244063) B3244063
theorem B2883611 : Blo 1921435 2883611 := bstep (se 1 (by rfl) ⟨2162708, by rfl⟩ : syracuseStep 2883611 = 4325417) B4325417
theorem B1922407 : Blo 1921435 1922407 := bstep (se 1 (by rfl) ⟨1441805, by rfl⟩ : syracuseStep 1922407 = 2883611) B2883611
theorem B2162713 : Blo 1921435 2162713 := bbase (se 2 (by rfl) ⟨811017, by rfl⟩ : syracuseStep 2162713 = 1622035) (by norm_num)
theorem B2883617 : Blo 1921435 2883617 := bstep (se 2 (by rfl) ⟨1081356, by rfl⟩ : syracuseStep 2883617 = 2162713) B2162713
theorem B1922411 : Blo 1921435 1922411 := bstep (se 1 (by rfl) ⟨1441808, by rfl⟩ : syracuseStep 1922411 = 2883617) B2883617
theorem B7299173 : Blo 1921435 7299173 := bbase (se 4 (by rfl) ⟨684297, by rfl⟩ : syracuseStep 7299173 = 1368595) (by norm_num)
theorem B4866115 : Blo 1921435 4866115 := bstep (se 1 (by rfl) ⟨3649586, by rfl⟩ : syracuseStep 4866115 = 7299173) B7299173
theorem B6488153 : Blo 1921435 6488153 := bstep (se 2 (by rfl) ⟨2433057, by rfl⟩ : syracuseStep 6488153 = 4866115) B4866115
theorem B4325435 : Blo 1921435 4325435 := bstep (se 1 (by rfl) ⟨3244076, by rfl⟩ : syracuseStep 4325435 = 6488153) B6488153
theorem B2883623 : Blo 1921435 2883623 := bstep (se 1 (by rfl) ⟨2162717, by rfl⟩ : syracuseStep 2883623 = 4325435) B4325435
theorem B1922415 : Blo 1921435 1922415 := bstep (se 1 (by rfl) ⟨1441811, by rfl⟩ : syracuseStep 1922415 = 2883623) B2883623
theorem B2883629 : Blo 1921435 2883629 := bbase (se 3 (by rfl) ⟨540680, by rfl⟩ : syracuseStep 2883629 = 1081361) (by norm_num)
theorem B1922419 : Blo 1921435 1922419 := bstep (se 1 (by rfl) ⟨1441814, by rfl⟩ : syracuseStep 1922419 = 2883629) B2883629
theorem B4325453 : Blo 1921435 4325453 := bbase (se 3 (by rfl) ⟨811022, by rfl⟩ : syracuseStep 4325453 = 1622045) (by norm_num)
theorem B2883635 : Blo 1921435 2883635 := bstep (se 1 (by rfl) ⟨2162726, by rfl⟩ : syracuseStep 2883635 = 4325453) B4325453
theorem B1922423 : Blo 1921435 1922423 := bstep (se 1 (by rfl) ⟨1441817, by rfl⟩ : syracuseStep 1922423 = 2883635) B2883635
theorem B2433073 : Blo 1921435 2433073 := bbase (se 2 (by rfl) ⟨912402, by rfl⟩ : syracuseStep 2433073 = 1824805) (by norm_num)
theorem B3244097 : Blo 1921435 3244097 := bstep (se 2 (by rfl) ⟨1216536, by rfl⟩ : syracuseStep 3244097 = 2433073) B2433073
theorem B2162731 : Blo 1921435 2162731 := bstep (se 1 (by rfl) ⟨1622048, by rfl⟩ : syracuseStep 2162731 = 3244097) B3244097
theorem B2883641 : Blo 1921435 2883641 := bstep (se 2 (by rfl) ⟨1081365, by rfl⟩ : syracuseStep 2883641 = 2162731) B2162731
theorem B1922427 : Blo 1921435 1922427 := bstep (se 1 (by rfl) ⟨1441820, by rfl⟩ : syracuseStep 1922427 = 2883641) B2883641
theorem B8008789 : Blo 1921435 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B10678385 : Blo 1921435 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B7118923 : Blo 1921435 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B9491897 : Blo 1921435 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B6327931 : Blo 1921435 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B8437241 : Blo 1921435 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B22499309 : Blo 1921435 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B59998157 : Blo 1921435 59998157 := bstep (se 3 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 59998157 = 22499309) B22499309
theorem B39998771 : Blo 1921435 39998771 := bstep (se 1 (by rfl) ⟨29999078, by rfl⟩ : syracuseStep 39998771 = 59998157) B59998157
theorem B26665847 : Blo 1921435 26665847 := bstep (se 1 (by rfl) ⟨19999385, by rfl⟩ : syracuseStep 26665847 = 39998771) B39998771
theorem B17777231 : Blo 1921435 17777231 := bstep (se 1 (by rfl) ⟨13332923, by rfl⟩ : syracuseStep 17777231 = 26665847) B26665847
theorem B11851487 : Blo 1921435 11851487 := bstep (se 1 (by rfl) ⟨8888615, by rfl⟩ : syracuseStep 11851487 = 17777231) B17777231
theorem B7900991 : Blo 1921435 7900991 := bstep (se 1 (by rfl) ⟨5925743, by rfl⟩ : syracuseStep 7900991 = 11851487) B11851487
theorem B5267327 : Blo 1921435 5267327 := bstep (se 1 (by rfl) ⟨3950495, by rfl⟩ : syracuseStep 5267327 = 7900991) B7900991
theorem B14046205 : Blo 1921435 14046205 := bstep (se 3 (by rfl) ⟨2633663, by rfl⟩ : syracuseStep 14046205 = 5267327) B5267327
theorem B18728273 : Blo 1921435 18728273 := bstep (se 2 (by rfl) ⟨7023102, by rfl⟩ : syracuseStep 18728273 = 14046205) B14046205
theorem B12485515 : Blo 1921435 12485515 := bstep (se 1 (by rfl) ⟨9364136, by rfl⟩ : syracuseStep 12485515 = 18728273) B18728273
theorem B16647353 : Blo 1921435 16647353 := bstep (se 2 (by rfl) ⟨6242757, by rfl⟩ : syracuseStep 16647353 = 12485515) B12485515
theorem B11098235 : Blo 1921435 11098235 := bstep (se 1 (by rfl) ⟨8323676, by rfl⟩ : syracuseStep 11098235 = 16647353) B16647353
theorem B7398823 : Blo 1921435 7398823 := bstep (se 1 (by rfl) ⟨5549117, by rfl⟩ : syracuseStep 7398823 = 11098235) B11098235
theorem B9865097 : Blo 1921435 9865097 := bstep (se 2 (by rfl) ⟨3699411, by rfl⟩ : syracuseStep 9865097 = 7398823) B7398823
theorem B6576731 : Blo 1921435 6576731 := bstep (se 1 (by rfl) ⟨4932548, by rfl⟩ : syracuseStep 6576731 = 9865097) B9865097
theorem B4384487 : Blo 1921435 4384487 := bstep (se 1 (by rfl) ⟨3288365, by rfl⟩ : syracuseStep 4384487 = 6576731) B6576731
theorem B11691965 : Blo 1921435 11691965 := bstep (se 3 (by rfl) ⟨2192243, by rfl⟩ : syracuseStep 11691965 = 4384487) B4384487
theorem B7794643 : Blo 1921435 7794643 := bstep (se 1 (by rfl) ⟨5845982, by rfl⟩ : syracuseStep 7794643 = 11691965) B11691965
theorem B10392857 : Blo 1921435 10392857 := bstep (se 2 (by rfl) ⟨3897321, by rfl⟩ : syracuseStep 10392857 = 7794643) B7794643
theorem B6928571 : Blo 1921435 6928571 := bstep (se 1 (by rfl) ⟨5196428, by rfl⟩ : syracuseStep 6928571 = 10392857) B10392857
theorem B4619047 : Blo 1921435 4619047 := bstep (se 1 (by rfl) ⟨3464285, by rfl⟩ : syracuseStep 4619047 = 6928571) B6928571
theorem B6158729 : Blo 1921435 6158729 := bstep (se 2 (by rfl) ⟨2309523, by rfl⟩ : syracuseStep 6158729 = 4619047) B4619047
theorem B4105819 : Blo 1921435 4105819 := bstep (se 1 (by rfl) ⟨3079364, by rfl⟩ : syracuseStep 4105819 = 6158729) B6158729
theorem B21897701 : Blo 1921435 21897701 := bstep (se 4 (by rfl) ⟨2052909, by rfl⟩ : syracuseStep 21897701 = 4105819) B4105819
theorem B14598467 : Blo 1921435 14598467 := bstep (se 1 (by rfl) ⟨10948850, by rfl⟩ : syracuseStep 14598467 = 21897701) B21897701
theorem B9732311 : Blo 1921435 9732311 := bstep (se 1 (by rfl) ⟨7299233, by rfl⟩ : syracuseStep 9732311 = 14598467) B14598467
theorem B6488207 : Blo 1921435 6488207 := bstep (se 1 (by rfl) ⟨4866155, by rfl⟩ : syracuseStep 6488207 = 9732311) B9732311
theorem B4325471 : Blo 1921435 4325471 := bstep (se 1 (by rfl) ⟨3244103, by rfl⟩ : syracuseStep 4325471 = 6488207) B6488207
theorem B2883647 : Blo 1921435 2883647 := bstep (se 1 (by rfl) ⟨2162735, by rfl⟩ : syracuseStep 2883647 = 4325471) B4325471
theorem B1922431 : Blo 1921435 1922431 := bstep (se 1 (by rfl) ⟨1441823, by rfl⟩ : syracuseStep 1922431 = 2883647) B2883647
theorem B2883653 : Blo 1921435 2883653 := bbase (se 4 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 2883653 = 540685) (by norm_num)
theorem B1922435 : Blo 1921435 1922435 := bstep (se 1 (by rfl) ⟨1441826, by rfl⟩ : syracuseStep 1922435 = 2883653) B2883653
theorem B3244117 : Blo 1921435 3244117 := bbase (se 8 (by rfl) ⟨19008, by rfl⟩ : syracuseStep 3244117 = 38017) (by norm_num)
theorem B4325489 : Blo 1921435 4325489 := bstep (se 2 (by rfl) ⟨1622058, by rfl⟩ : syracuseStep 4325489 = 3244117) B3244117
theorem B2883659 : Blo 1921435 2883659 := bstep (se 1 (by rfl) ⟨2162744, by rfl⟩ : syracuseStep 2883659 = 4325489) B4325489
theorem B1922439 : Blo 1921435 1922439 := bstep (se 1 (by rfl) ⟨1441829, by rfl⟩ : syracuseStep 1922439 = 2883659) B2883659
theorem B2162749 : Blo 1921435 2162749 := bbase (se 3 (by rfl) ⟨405515, by rfl⟩ : syracuseStep 2162749 = 811031) (by norm_num)
theorem B2883665 : Blo 1921435 2883665 := bstep (se 2 (by rfl) ⟨1081374, by rfl⟩ : syracuseStep 2883665 = 2162749) B2162749
theorem B1922443 : Blo 1921435 1922443 := bstep (se 1 (by rfl) ⟨1441832, by rfl⟩ : syracuseStep 1922443 = 2883665) B2883665
theorem B6488261 : Blo 1921435 6488261 := bbase (se 4 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 6488261 = 1216549) (by norm_num)
theorem B4325507 : Blo 1921435 4325507 := bstep (se 1 (by rfl) ⟨3244130, by rfl⟩ : syracuseStep 4325507 = 6488261) B6488261
theorem B2883671 : Blo 1921435 2883671 := bstep (se 1 (by rfl) ⟨2162753, by rfl⟩ : syracuseStep 2883671 = 4325507) B4325507
theorem B1922447 : Blo 1921435 1922447 := bstep (se 1 (by rfl) ⟨1441835, by rfl⟩ : syracuseStep 1922447 = 2883671) B2883671
theorem B2883677 : Blo 1921435 2883677 := bbase (se 3 (by rfl) ⟨540689, by rfl⟩ : syracuseStep 2883677 = 1081379) (by norm_num)
theorem B1922451 : Blo 1921435 1922451 := bstep (se 1 (by rfl) ⟨1441838, by rfl⟩ : syracuseStep 1922451 = 2883677) B2883677
theorem B4325525 : Blo 1921435 4325525 := bbase (se 6 (by rfl) ⟨101379, by rfl⟩ : syracuseStep 4325525 = 202759) (by norm_num)
theorem B2883683 : Blo 1921435 2883683 := bstep (se 1 (by rfl) ⟨2162762, by rfl⟩ : syracuseStep 2883683 = 4325525) B4325525
theorem B1922455 : Blo 1921435 1922455 := bstep (se 1 (by rfl) ⟨1441841, by rfl⟩ : syracuseStep 1922455 = 2883683) B2883683
theorem B2737253 : Blo 1921435 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B7299341 : Blo 1921435 7299341 := bstep (se 3 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 7299341 = 2737253) B2737253
theorem B4866227 : Blo 1921435 4866227 := bstep (se 1 (by rfl) ⟨3649670, by rfl⟩ : syracuseStep 4866227 = 7299341) B7299341
theorem B3244151 : Blo 1921435 3244151 := bstep (se 1 (by rfl) ⟨2433113, by rfl⟩ : syracuseStep 3244151 = 4866227) B4866227
theorem B2162767 : Blo 1921435 2162767 := bstep (se 1 (by rfl) ⟨1622075, by rfl⟩ : syracuseStep 2162767 = 3244151) B3244151
theorem B2883689 : Blo 1921435 2883689 := bstep (se 2 (by rfl) ⟨1081383, by rfl⟩ : syracuseStep 2883689 = 2162767) B2162767
theorem B1922459 : Blo 1921435 1922459 := bstep (se 1 (by rfl) ⟨1441844, by rfl⟩ : syracuseStep 1922459 = 2883689) B2883689
theorem B2373013 : Blo 1921435 2373013 := bbase (se 6 (by rfl) ⟨55617, by rfl⟩ : syracuseStep 2373013 = 111235) (by norm_num)
theorem B3164017 : Blo 1921435 3164017 := bstep (se 2 (by rfl) ⟨1186506, by rfl⟩ : syracuseStep 3164017 = 2373013) B2373013
theorem B4218689 : Blo 1921435 4218689 := bstep (se 2 (by rfl) ⟨1582008, by rfl⟩ : syracuseStep 4218689 = 3164017) B3164017
theorem B2812459 : Blo 1921435 2812459 := bstep (se 1 (by rfl) ⟨2109344, by rfl⟩ : syracuseStep 2812459 = 4218689) B4218689
theorem B3749945 : Blo 1921435 3749945 := bstep (se 2 (by rfl) ⟨1406229, by rfl⟩ : syracuseStep 3749945 = 2812459) B2812459
theorem B39999413 : Blo 1921435 39999413 := bstep (se 5 (by rfl) ⟨1874972, by rfl⟩ : syracuseStep 39999413 = 3749945) B3749945
theorem B26666275 : Blo 1921435 26666275 := bstep (se 1 (by rfl) ⟨19999706, by rfl⟩ : syracuseStep 26666275 = 39999413) B39999413
theorem B35555033 : Blo 1921435 35555033 := bstep (se 2 (by rfl) ⟨13333137, by rfl⟩ : syracuseStep 35555033 = 26666275) B26666275
theorem B94813421 : Blo 1921435 94813421 := bstep (se 3 (by rfl) ⟨17777516, by rfl⟩ : syracuseStep 94813421 = 35555033) B35555033
theorem B252835789 : Blo 1921435 252835789 := bstep (se 3 (by rfl) ⟨47406710, by rfl⟩ : syracuseStep 252835789 = 94813421) B94813421
theorem B337114385 : Blo 1921435 337114385 := bstep (se 2 (by rfl) ⟨126417894, by rfl⟩ : syracuseStep 337114385 = 252835789) B252835789
theorem B224742923 : Blo 1921435 224742923 := bstep (se 1 (by rfl) ⟨168557192, by rfl⟩ : syracuseStep 224742923 = 337114385) B337114385
theorem B149828615 : Blo 1921435 149828615 := bstep (se 1 (by rfl) ⟨112371461, by rfl⟩ : syracuseStep 149828615 = 224742923) B224742923
theorem B99885743 : Blo 1921435 99885743 := bstep (se 1 (by rfl) ⟨74914307, by rfl⟩ : syracuseStep 99885743 = 149828615) B149828615
theorem B66590495 : Blo 1921435 66590495 := bstep (se 1 (by rfl) ⟨49942871, by rfl⟩ : syracuseStep 66590495 = 99885743) B99885743
theorem B44393663 : Blo 1921435 44393663 := bstep (se 1 (by rfl) ⟨33295247, by rfl⟩ : syracuseStep 44393663 = 66590495) B66590495
theorem B29595775 : Blo 1921435 29595775 := bstep (se 1 (by rfl) ⟨22196831, by rfl⟩ : syracuseStep 29595775 = 44393663) B44393663
theorem B39461033 : Blo 1921435 39461033 := bstep (se 2 (by rfl) ⟨14797887, by rfl⟩ : syracuseStep 39461033 = 29595775) B29595775
theorem B26307355 : Blo 1921435 26307355 := bstep (se 1 (by rfl) ⟨19730516, by rfl⟩ : syracuseStep 26307355 = 39461033) B39461033
theorem B35076473 : Blo 1921435 35076473 := bstep (se 2 (by rfl) ⟨13153677, by rfl⟩ : syracuseStep 35076473 = 26307355) B26307355
theorem B23384315 : Blo 1921435 23384315 := bstep (se 1 (by rfl) ⟨17538236, by rfl⟩ : syracuseStep 23384315 = 35076473) B35076473
theorem B62358173 : Blo 1921435 62358173 := bstep (se 3 (by rfl) ⟨11692157, by rfl⟩ : syracuseStep 62358173 = 23384315) B23384315
theorem B41572115 : Blo 1921435 41572115 := bstep (se 1 (by rfl) ⟨31179086, by rfl⟩ : syracuseStep 41572115 = 62358173) B62358173
theorem B27714743 : Blo 1921435 27714743 := bstep (se 1 (by rfl) ⟨20786057, by rfl⟩ : syracuseStep 27714743 = 41572115) B41572115
theorem B18476495 : Blo 1921435 18476495 := bstep (se 1 (by rfl) ⟨13857371, by rfl⟩ : syracuseStep 18476495 = 27714743) B27714743
theorem B12317663 : Blo 1921435 12317663 := bstep (se 1 (by rfl) ⟨9238247, by rfl⟩ : syracuseStep 12317663 = 18476495) B18476495
theorem B8211775 : Blo 1921435 8211775 := bstep (se 1 (by rfl) ⟨6158831, by rfl⟩ : syracuseStep 8211775 = 12317663) B12317663
theorem B10949033 : Blo 1921435 10949033 := bstep (se 2 (by rfl) ⟨4105887, by rfl⟩ : syracuseStep 10949033 = 8211775) B8211775
theorem B7299355 : Blo 1921435 7299355 := bstep (se 1 (by rfl) ⟨5474516, by rfl⟩ : syracuseStep 7299355 = 10949033) B10949033
theorem B9732473 : Blo 1921435 9732473 := bstep (se 2 (by rfl) ⟨3649677, by rfl⟩ : syracuseStep 9732473 = 7299355) B7299355
theorem B6488315 : Blo 1921435 6488315 := bstep (se 1 (by rfl) ⟨4866236, by rfl⟩ : syracuseStep 6488315 = 9732473) B9732473
theorem B4325543 : Blo 1921435 4325543 := bstep (se 1 (by rfl) ⟨3244157, by rfl⟩ : syracuseStep 4325543 = 6488315) B6488315
theorem B2883695 : Blo 1921435 2883695 := bstep (se 1 (by rfl) ⟨2162771, by rfl⟩ : syracuseStep 2883695 = 4325543) B4325543
theorem B1922463 : Blo 1921435 1922463 := bstep (se 1 (by rfl) ⟨1441847, by rfl⟩ : syracuseStep 1922463 = 2883695) B2883695
theorem B2883701 : Blo 1921435 2883701 := bbase (se 5 (by rfl) ⟨135173, by rfl⟩ : syracuseStep 2883701 = 270347) (by norm_num)
theorem B1922467 : Blo 1921435 1922467 := bstep (se 1 (by rfl) ⟨1441850, by rfl⟩ : syracuseStep 1922467 = 2883701) B2883701
theorem B3649693 : Blo 1921435 3649693 := bbase (se 3 (by rfl) ⟨684317, by rfl⟩ : syracuseStep 3649693 = 1368635) (by norm_num)
theorem B4866257 : Blo 1921435 4866257 := bstep (se 2 (by rfl) ⟨1824846, by rfl⟩ : syracuseStep 4866257 = 3649693) B3649693
theorem B3244171 : Blo 1921435 3244171 := bstep (se 1 (by rfl) ⟨2433128, by rfl⟩ : syracuseStep 3244171 = 4866257) B4866257
theorem B4325561 : Blo 1921435 4325561 := bstep (se 2 (by rfl) ⟨1622085, by rfl⟩ : syracuseStep 4325561 = 3244171) B3244171
theorem B2883707 : Blo 1921435 2883707 := bstep (se 1 (by rfl) ⟨2162780, by rfl⟩ : syracuseStep 2883707 = 4325561) B4325561
theorem B1922471 : Blo 1921435 1922471 := bstep (se 1 (by rfl) ⟨1441853, by rfl⟩ : syracuseStep 1922471 = 2883707) B2883707
theorem B2162785 : Blo 1921435 2162785 := bbase (se 2 (by rfl) ⟨811044, by rfl⟩ : syracuseStep 2162785 = 1622089) (by norm_num)
theorem B2883713 : Blo 1921435 2883713 := bstep (se 2 (by rfl) ⟨1081392, by rfl⟩ : syracuseStep 2883713 = 2162785) B2162785
theorem B1922475 : Blo 1921435 1922475 := bstep (se 1 (by rfl) ⟨1441856, by rfl⟩ : syracuseStep 1922475 = 2883713) B2883713
theorem B4866277 : Blo 1921435 4866277 := bbase (se 4 (by rfl) ⟨456213, by rfl⟩ : syracuseStep 4866277 = 912427) (by norm_num)
theorem B6488369 : Blo 1921435 6488369 := bstep (se 2 (by rfl) ⟨2433138, by rfl⟩ : syracuseStep 6488369 = 4866277) B4866277
theorem B4325579 : Blo 1921435 4325579 := bstep (se 1 (by rfl) ⟨3244184, by rfl⟩ : syracuseStep 4325579 = 6488369) B6488369
theorem B2883719 : Blo 1921435 2883719 := bstep (se 1 (by rfl) ⟨2162789, by rfl⟩ : syracuseStep 2883719 = 4325579) B4325579
theorem B1922479 : Blo 1921435 1922479 := bstep (se 1 (by rfl) ⟨1441859, by rfl⟩ : syracuseStep 1922479 = 2883719) B2883719
theorem B2883725 : Blo 1921435 2883725 := bbase (se 3 (by rfl) ⟨540698, by rfl⟩ : syracuseStep 2883725 = 1081397) (by norm_num)
theorem B1922483 : Blo 1921435 1922483 := bstep (se 1 (by rfl) ⟨1441862, by rfl⟩ : syracuseStep 1922483 = 2883725) B2883725
theorem B4325597 : Blo 1921435 4325597 := bbase (se 3 (by rfl) ⟨811049, by rfl⟩ : syracuseStep 4325597 = 1622099) (by norm_num)
theorem B2883731 : Blo 1921435 2883731 := bstep (se 1 (by rfl) ⟨2162798, by rfl⟩ : syracuseStep 2883731 = 4325597) B4325597
theorem B1922487 : Blo 1921435 1922487 := bstep (se 1 (by rfl) ⟨1441865, by rfl⟩ : syracuseStep 1922487 = 2883731) B2883731
theorem B3244205 : Blo 1921435 3244205 := bbase (se 3 (by rfl) ⟨608288, by rfl⟩ : syracuseStep 3244205 = 1216577) (by norm_num)
theorem B2162803 : Blo 1921435 2162803 := bstep (se 1 (by rfl) ⟨1622102, by rfl⟩ : syracuseStep 2162803 = 3244205) B3244205
theorem B2883737 : Blo 1921435 2883737 := bstep (se 2 (by rfl) ⟨1081401, by rfl⟩ : syracuseStep 2883737 = 2162803) B2162803
theorem B1922491 : Blo 1921435 1922491 := bstep (se 1 (by rfl) ⟨1441868, by rfl⟩ : syracuseStep 1922491 = 2883737) B2883737
theorem B7794901 : Blo 1921435 7794901 := bbase (se 7 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 7794901 = 182693) (by norm_num)
theorem B10393201 : Blo 1921435 10393201 := bstep (se 2 (by rfl) ⟨3897450, by rfl⟩ : syracuseStep 10393201 = 7794901) B7794901
theorem B55430405 : Blo 1921435 55430405 := bstep (se 4 (by rfl) ⟨5196600, by rfl⟩ : syracuseStep 55430405 = 10393201) B10393201
theorem B36953603 : Blo 1921435 36953603 := bstep (se 1 (by rfl) ⟨27715202, by rfl⟩ : syracuseStep 36953603 = 55430405) B55430405
theorem B24635735 : Blo 1921435 24635735 := bstep (se 1 (by rfl) ⟨18476801, by rfl⟩ : syracuseStep 24635735 = 36953603) B36953603
theorem B16423823 : Blo 1921435 16423823 := bstep (se 1 (by rfl) ⟨12317867, by rfl⟩ : syracuseStep 16423823 = 24635735) B24635735
theorem B10949215 : Blo 1921435 10949215 := bstep (se 1 (by rfl) ⟨8211911, by rfl⟩ : syracuseStep 10949215 = 16423823) B16423823
theorem B14598953 : Blo 1921435 14598953 := bstep (se 2 (by rfl) ⟨5474607, by rfl⟩ : syracuseStep 14598953 = 10949215) B10949215
theorem B9732635 : Blo 1921435 9732635 := bstep (se 1 (by rfl) ⟨7299476, by rfl⟩ : syracuseStep 9732635 = 14598953) B14598953
theorem B6488423 : Blo 1921435 6488423 := bstep (se 1 (by rfl) ⟨4866317, by rfl⟩ : syracuseStep 6488423 = 9732635) B9732635
theorem B4325615 : Blo 1921435 4325615 := bstep (se 1 (by rfl) ⟨3244211, by rfl⟩ : syracuseStep 4325615 = 6488423) B6488423
theorem B2883743 : Blo 1921435 2883743 := bstep (se 1 (by rfl) ⟨2162807, by rfl⟩ : syracuseStep 2883743 = 4325615) B4325615
theorem B1922495 : Blo 1921435 1922495 := bstep (se 1 (by rfl) ⟨1441871, by rfl⟩ : syracuseStep 1922495 = 2883743) B2883743
theorem B2883749 : Blo 1921435 2883749 := bbase (se 4 (by rfl) ⟨270351, by rfl⟩ : syracuseStep 2883749 = 540703) (by norm_num)
theorem B1922499 : Blo 1921435 1922499 := bstep (se 1 (by rfl) ⟨1441874, by rfl⟩ : syracuseStep 1922499 = 2883749) B2883749
theorem B2433169 : Blo 1921435 2433169 := bbase (se 2 (by rfl) ⟨912438, by rfl⟩ : syracuseStep 2433169 = 1824877) (by norm_num)
theorem B3244225 : Blo 1921435 3244225 := bstep (se 2 (by rfl) ⟨1216584, by rfl⟩ : syracuseStep 3244225 = 2433169) B2433169
theorem B4325633 : Blo 1921435 4325633 := bstep (se 2 (by rfl) ⟨1622112, by rfl⟩ : syracuseStep 4325633 = 3244225) B3244225
theorem B2883755 : Blo 1921435 2883755 := bstep (se 1 (by rfl) ⟨2162816, by rfl⟩ : syracuseStep 2883755 = 4325633) B4325633
theorem B1922503 : Blo 1921435 1922503 := bstep (se 1 (by rfl) ⟨1441877, by rfl⟩ : syracuseStep 1922503 = 2883755) B2883755
theorem B2162821 : Blo 1921435 2162821 := bbase (se 4 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 2162821 = 405529) (by norm_num)
theorem B2883761 : Blo 1921435 2883761 := bstep (se 2 (by rfl) ⟨1081410, by rfl⟩ : syracuseStep 2883761 = 2162821) B2162821
theorem B1922507 : Blo 1921435 1922507 := bstep (se 1 (by rfl) ⟨1441880, by rfl⟩ : syracuseStep 1922507 = 2883761) B2883761
theorem B3897485 : Blo 1921435 3897485 := bbase (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) (by norm_num)
theorem B2598323 : Blo 1921435 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B6928861 : Blo 1921435 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B9238481 : Blo 1921435 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B6158987 : Blo 1921435 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B4105991 : Blo 1921435 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B2737327 : Blo 1921435 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B3649769 : Blo 1921435 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B2433179 : Blo 1921435 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B6488477 : Blo 1921435 6488477 := bstep (se 3 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 6488477 = 2433179) B2433179
theorem B4325651 : Blo 1921435 4325651 := bstep (se 1 (by rfl) ⟨3244238, by rfl⟩ : syracuseStep 4325651 = 6488477) B6488477
theorem B2883767 : Blo 1921435 2883767 := bstep (se 1 (by rfl) ⟨2162825, by rfl⟩ : syracuseStep 2883767 = 4325651) B4325651
theorem B1922511 : Blo 1921435 1922511 := bstep (se 1 (by rfl) ⟨1441883, by rfl⟩ : syracuseStep 1922511 = 2883767) B2883767
theorem B2883773 : Blo 1921435 2883773 := bbase (se 3 (by rfl) ⟨540707, by rfl⟩ : syracuseStep 2883773 = 1081415) (by norm_num)
theorem B1922515 : Blo 1921435 1922515 := bstep (se 1 (by rfl) ⟨1441886, by rfl⟩ : syracuseStep 1922515 = 2883773) B2883773
theorem B4325669 : Blo 1921435 4325669 := bbase (se 4 (by rfl) ⟨405531, by rfl⟩ : syracuseStep 4325669 = 811063) (by norm_num)
theorem B2883779 : Blo 1921435 2883779 := bstep (se 1 (by rfl) ⟨2162834, by rfl⟩ : syracuseStep 2883779 = 4325669) B4325669
theorem B1922519 : Blo 1921435 1922519 := bstep (se 1 (by rfl) ⟨1441889, by rfl⟩ : syracuseStep 1922519 = 2883779) B2883779
theorem B4866389 : Blo 1921435 4866389 := bbase (se 10 (by rfl) ⟨7128, by rfl⟩ : syracuseStep 4866389 = 14257) (by norm_num)
theorem B3244259 : Blo 1921435 3244259 := bstep (se 1 (by rfl) ⟨2433194, by rfl⟩ : syracuseStep 3244259 = 4866389) B4866389
theorem B2162839 : Blo 1921435 2162839 := bstep (se 1 (by rfl) ⟨1622129, by rfl⟩ : syracuseStep 2162839 = 3244259) B3244259
theorem B2883785 : Blo 1921435 2883785 := bstep (se 2 (by rfl) ⟨1081419, by rfl⟩ : syracuseStep 2883785 = 2162839) B2162839
theorem B1922523 : Blo 1921435 1922523 := bstep (se 1 (by rfl) ⟨1441892, by rfl⟩ : syracuseStep 1922523 = 2883785) B2883785
theorem B3897517 : Blo 1921435 3897517 := bbase (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) (by norm_num)
theorem B5196689 : Blo 1921435 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B3464459 : Blo 1921435 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B2309639 : Blo 1921435 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B6159037 : Blo 1921435 6159037 := bstep (se 3 (by rfl) ⟨1154819, by rfl⟩ : syracuseStep 6159037 = 2309639) B2309639
theorem B8212049 : Blo 1921435 8212049 := bstep (se 2 (by rfl) ⟨3079518, by rfl⟩ : syracuseStep 8212049 = 6159037) B6159037
theorem B5474699 : Blo 1921435 5474699 := bstep (se 1 (by rfl) ⟨4106024, by rfl⟩ : syracuseStep 5474699 = 8212049) B8212049
theorem B3649799 : Blo 1921435 3649799 := bstep (se 1 (by rfl) ⟨2737349, by rfl⟩ : syracuseStep 3649799 = 5474699) B5474699
theorem B9732797 : Blo 1921435 9732797 := bstep (se 3 (by rfl) ⟨1824899, by rfl⟩ : syracuseStep 9732797 = 3649799) B3649799
theorem B6488531 : Blo 1921435 6488531 := bstep (se 1 (by rfl) ⟨4866398, by rfl⟩ : syracuseStep 6488531 = 9732797) B9732797
theorem B4325687 : Blo 1921435 4325687 := bstep (se 1 (by rfl) ⟨3244265, by rfl⟩ : syracuseStep 4325687 = 6488531) B6488531
theorem B2883791 : Blo 1921435 2883791 := bstep (se 1 (by rfl) ⟨2162843, by rfl⟩ : syracuseStep 2883791 = 4325687) B4325687
theorem B1922527 : Blo 1921435 1922527 := bstep (se 1 (by rfl) ⟨1441895, by rfl⟩ : syracuseStep 1922527 = 2883791) B2883791
theorem B2883797 : Blo 1921435 2883797 := bbase (se 7 (by rfl) ⟨33794, by rfl⟩ : syracuseStep 2883797 = 67589) (by norm_num)
theorem B1922531 : Blo 1921435 1922531 := bstep (se 1 (by rfl) ⟨1441898, by rfl⟩ : syracuseStep 1922531 = 2883797) B2883797
theorem B2053021 : Blo 1921435 2053021 := bbase (se 3 (by rfl) ⟨384941, by rfl⟩ : syracuseStep 2053021 = 769883) (by norm_num)
theorem B2737361 : Blo 1921435 2737361 := bstep (se 2 (by rfl) ⟨1026510, by rfl⟩ : syracuseStep 2737361 = 2053021) B2053021
theorem B7299629 : Blo 1921435 7299629 := bstep (se 3 (by rfl) ⟨1368680, by rfl⟩ : syracuseStep 7299629 = 2737361) B2737361
theorem B4866419 : Blo 1921435 4866419 := bstep (se 1 (by rfl) ⟨3649814, by rfl⟩ : syracuseStep 4866419 = 7299629) B7299629
theorem B3244279 : Blo 1921435 3244279 := bstep (se 1 (by rfl) ⟨2433209, by rfl⟩ : syracuseStep 3244279 = 4866419) B4866419
theorem B4325705 : Blo 1921435 4325705 := bstep (se 2 (by rfl) ⟨1622139, by rfl⟩ : syracuseStep 4325705 = 3244279) B3244279
theorem B2883803 : Blo 1921435 2883803 := bstep (se 1 (by rfl) ⟨2162852, by rfl⟩ : syracuseStep 2883803 = 4325705) B4325705
theorem B1922535 : Blo 1921435 1922535 := bstep (se 1 (by rfl) ⟨1441901, by rfl⟩ : syracuseStep 1922535 = 2883803) B2883803
theorem B2162857 : Blo 1921435 2162857 := bbase (se 2 (by rfl) ⟨811071, by rfl⟩ : syracuseStep 2162857 = 1622143) (by norm_num)
theorem B2883809 : Blo 1921435 2883809 := bstep (se 2 (by rfl) ⟨1081428, by rfl⟩ : syracuseStep 2883809 = 2162857) B2162857
theorem B1922539 : Blo 1921435 1922539 := bstep (se 1 (by rfl) ⟨1441904, by rfl⟩ : syracuseStep 1922539 = 2883809) B2883809
theorem B8212117 : Blo 1921435 8212117 := bbase (se 6 (by rfl) ⟨192471, by rfl⟩ : syracuseStep 8212117 = 384943) (by norm_num)
theorem B10949489 : Blo 1921435 10949489 := bstep (se 2 (by rfl) ⟨4106058, by rfl⟩ : syracuseStep 10949489 = 8212117) B8212117
theorem B7299659 : Blo 1921435 7299659 := bstep (se 1 (by rfl) ⟨5474744, by rfl⟩ : syracuseStep 7299659 = 10949489) B10949489
theorem B4866439 : Blo 1921435 4866439 := bstep (se 1 (by rfl) ⟨3649829, by rfl⟩ : syracuseStep 4866439 = 7299659) B7299659
theorem B6488585 : Blo 1921435 6488585 := bstep (se 2 (by rfl) ⟨2433219, by rfl⟩ : syracuseStep 6488585 = 4866439) B4866439
theorem B4325723 : Blo 1921435 4325723 := bstep (se 1 (by rfl) ⟨3244292, by rfl⟩ : syracuseStep 4325723 = 6488585) B6488585
theorem B2883815 : Blo 1921435 2883815 := bstep (se 1 (by rfl) ⟨2162861, by rfl⟩ : syracuseStep 2883815 = 4325723) B4325723
theorem B1922543 : Blo 1921435 1922543 := bstep (se 1 (by rfl) ⟨1441907, by rfl⟩ : syracuseStep 1922543 = 2883815) B2883815
theorem B2883821 : Blo 1921435 2883821 := bbase (se 3 (by rfl) ⟨540716, by rfl⟩ : syracuseStep 2883821 = 1081433) (by norm_num)
theorem B1922547 : Blo 1921435 1922547 := bstep (se 1 (by rfl) ⟨1441910, by rfl⟩ : syracuseStep 1922547 = 2883821) B2883821
theorem B4325741 : Blo 1921435 4325741 := bbase (se 3 (by rfl) ⟨811076, by rfl⟩ : syracuseStep 4325741 = 1622153) (by norm_num)
theorem B2883827 : Blo 1921435 2883827 := bstep (se 1 (by rfl) ⟨2162870, by rfl⟩ : syracuseStep 2883827 = 4325741) B4325741
theorem B1922551 : Blo 1921435 1922551 := bstep (se 1 (by rfl) ⟨1441913, by rfl⟩ : syracuseStep 1922551 = 2883827) B2883827
theorem B3649853 : Blo 1921435 3649853 := bbase (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) (by norm_num)
theorem B2433235 : Blo 1921435 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B3244313 : Blo 1921435 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B2162875 : Blo 1921435 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2883833 : Blo 1921435 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1922555 : Blo 1921435 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B2309677 : Blo 1921435 2309677 := bbase (se 3 (by rfl) ⟨433064, by rfl⟩ : syracuseStep 2309677 = 866129) (by norm_num)
theorem B49273109 : Blo 1921435 49273109 := bstep (se 6 (by rfl) ⟨1154838, by rfl⟩ : syracuseStep 49273109 = 2309677) B2309677
theorem B32848739 : Blo 1921435 32848739 := bstep (se 1 (by rfl) ⟨24636554, by rfl⟩ : syracuseStep 32848739 = 49273109) B49273109
theorem B21899159 : Blo 1921435 21899159 := bstep (se 1 (by rfl) ⟨16424369, by rfl⟩ : syracuseStep 21899159 = 32848739) B32848739
theorem B14599439 : Blo 1921435 14599439 := bstep (se 1 (by rfl) ⟨10949579, by rfl⟩ : syracuseStep 14599439 = 21899159) B21899159
theorem B9732959 : Blo 1921435 9732959 := bstep (se 1 (by rfl) ⟨7299719, by rfl⟩ : syracuseStep 9732959 = 14599439) B14599439
theorem B6488639 : Blo 1921435 6488639 := bstep (se 1 (by rfl) ⟨4866479, by rfl⟩ : syracuseStep 6488639 = 9732959) B9732959
theorem B4325759 : Blo 1921435 4325759 := bstep (se 1 (by rfl) ⟨3244319, by rfl⟩ : syracuseStep 4325759 = 6488639) B6488639
theorem B2883839 : Blo 1921435 2883839 := bstep (se 1 (by rfl) ⟨2162879, by rfl⟩ : syracuseStep 2883839 = 4325759) B4325759
theorem B1922559 : Blo 1921435 1922559 := bstep (se 1 (by rfl) ⟨1441919, by rfl⟩ : syracuseStep 1922559 = 2883839) B2883839
theorem B2883845 : Blo 1921435 2883845 := bbase (se 4 (by rfl) ⟨270360, by rfl⟩ : syracuseStep 2883845 = 540721) (by norm_num)
theorem B1922563 : Blo 1921435 1922563 := bstep (se 1 (by rfl) ⟨1441922, by rfl⟩ : syracuseStep 1922563 = 2883845) B2883845
theorem B3244333 : Blo 1921435 3244333 := bbase (se 3 (by rfl) ⟨608312, by rfl⟩ : syracuseStep 3244333 = 1216625) (by norm_num)
theorem B4325777 : Blo 1921435 4325777 := bstep (se 2 (by rfl) ⟨1622166, by rfl⟩ : syracuseStep 4325777 = 3244333) B3244333
theorem B2883851 : Blo 1921435 2883851 := bstep (se 1 (by rfl) ⟨2162888, by rfl⟩ : syracuseStep 2883851 = 4325777) B4325777
theorem B1922567 : Blo 1921435 1922567 := bstep (se 1 (by rfl) ⟨1441925, by rfl⟩ : syracuseStep 1922567 = 2883851) B2883851
theorem B2162893 : Blo 1921435 2162893 := bbase (se 3 (by rfl) ⟨405542, by rfl⟩ : syracuseStep 2162893 = 811085) (by norm_num)
theorem B2883857 : Blo 1921435 2883857 := bstep (se 2 (by rfl) ⟨1081446, by rfl⟩ : syracuseStep 2883857 = 2162893) B2162893
theorem B1922571 : Blo 1921435 1922571 := bstep (se 1 (by rfl) ⟨1441928, by rfl⟩ : syracuseStep 1922571 = 2883857) B2883857
theorem B6488693 : Blo 1921435 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B4325795 : Blo 1921435 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B2883863 : Blo 1921435 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B1922575 : Blo 1921435 1922575 := bstep (se 1 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 1922575 = 2883863) B2883863
theorem B2883869 : Blo 1921435 2883869 := bbase (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) (by norm_num)
theorem B1922579 : Blo 1921435 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B4325813 : Blo 1921435 4325813 := bbase (se 5 (by rfl) ⟨202772, by rfl⟩ : syracuseStep 4325813 = 405545) (by norm_num)
theorem B2883875 : Blo 1921435 2883875 := bstep (se 1 (by rfl) ⟨2162906, by rfl⟩ : syracuseStep 2883875 = 4325813) B4325813
theorem B1922583 : Blo 1921435 1922583 := bstep (se 1 (by rfl) ⟨1441937, by rfl⟩ : syracuseStep 1922583 = 2883875) B2883875
theorem B10535509 : Blo 1921435 10535509 := bbase (se 8 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 10535509 = 123463) (by norm_num)
theorem B14047345 : Blo 1921435 14047345 := bstep (se 2 (by rfl) ⟨5267754, by rfl⟩ : syracuseStep 14047345 = 10535509) B10535509
theorem B18729793 : Blo 1921435 18729793 := bstep (se 2 (by rfl) ⟨7023672, by rfl⟩ : syracuseStep 18729793 = 14047345) B14047345
theorem B24973057 : Blo 1921435 24973057 := bstep (se 2 (by rfl) ⟨9364896, by rfl⟩ : syracuseStep 24973057 = 18729793) B18729793
theorem B33297409 : Blo 1921435 33297409 := bstep (se 2 (by rfl) ⟨12486528, by rfl⟩ : syracuseStep 33297409 = 24973057) B24973057
theorem B44396545 : Blo 1921435 44396545 := bstep (se 2 (by rfl) ⟨16648704, by rfl⟩ : syracuseStep 44396545 = 33297409) B33297409
theorem B59195393 : Blo 1921435 59195393 := bstep (se 2 (by rfl) ⟨22198272, by rfl⟩ : syracuseStep 59195393 = 44396545) B44396545
theorem B39463595 : Blo 1921435 39463595 := bstep (se 1 (by rfl) ⟨29597696, by rfl⟩ : syracuseStep 39463595 = 59195393) B59195393
theorem B26309063 : Blo 1921435 26309063 := bstep (se 1 (by rfl) ⟨19731797, by rfl⟩ : syracuseStep 26309063 = 39463595) B39463595
theorem B17539375 : Blo 1921435 17539375 := bstep (se 1 (by rfl) ⟨13154531, by rfl⟩ : syracuseStep 17539375 = 26309063) B26309063
theorem B23385833 : Blo 1921435 23385833 := bstep (se 2 (by rfl) ⟨8769687, by rfl⟩ : syracuseStep 23385833 = 17539375) B17539375
theorem B15590555 : Blo 1921435 15590555 := bstep (se 1 (by rfl) ⟨11692916, by rfl⟩ : syracuseStep 15590555 = 23385833) B23385833
theorem B10393703 : Blo 1921435 10393703 := bstep (se 1 (by rfl) ⟨7795277, by rfl⟩ : syracuseStep 10393703 = 15590555) B15590555
theorem B6929135 : Blo 1921435 6929135 := bstep (se 1 (by rfl) ⟨5196851, by rfl⟩ : syracuseStep 6929135 = 10393703) B10393703
theorem B4619423 : Blo 1921435 4619423 := bstep (se 1 (by rfl) ⟨3464567, by rfl⟩ : syracuseStep 4619423 = 6929135) B6929135
theorem B3079615 : Blo 1921435 3079615 := bstep (se 1 (by rfl) ⟨2309711, by rfl⟩ : syracuseStep 3079615 = 4619423) B4619423
theorem B4106153 : Blo 1921435 4106153 := bstep (se 2 (by rfl) ⟨1539807, by rfl⟩ : syracuseStep 4106153 = 3079615) B3079615
theorem B10949741 : Blo 1921435 10949741 := bstep (se 3 (by rfl) ⟨2053076, by rfl⟩ : syracuseStep 10949741 = 4106153) B4106153
theorem B7299827 : Blo 1921435 7299827 := bstep (se 1 (by rfl) ⟨5474870, by rfl⟩ : syracuseStep 7299827 = 10949741) B10949741
theorem B4866551 : Blo 1921435 4866551 := bstep (se 1 (by rfl) ⟨3649913, by rfl⟩ : syracuseStep 4866551 = 7299827) B7299827
theorem B3244367 : Blo 1921435 3244367 := bstep (se 1 (by rfl) ⟨2433275, by rfl⟩ : syracuseStep 3244367 = 4866551) B4866551
theorem B2162911 : Blo 1921435 2162911 := bstep (se 1 (by rfl) ⟨1622183, by rfl⟩ : syracuseStep 2162911 = 3244367) B3244367
theorem B2883881 : Blo 1921435 2883881 := bstep (se 2 (by rfl) ⟨1081455, by rfl⟩ : syracuseStep 2883881 = 2162911) B2162911
theorem B1922587 : Blo 1921435 1922587 := bstep (se 1 (by rfl) ⟨1441940, by rfl⟩ : syracuseStep 1922587 = 2883881) B2883881
theorem B3079621 : Blo 1921435 3079621 := bbase (se 4 (by rfl) ⟨288714, by rfl⟩ : syracuseStep 3079621 = 577429) (by norm_num)
theorem B4106161 : Blo 1921435 4106161 := bstep (se 2 (by rfl) ⟨1539810, by rfl⟩ : syracuseStep 4106161 = 3079621) B3079621
theorem B5474881 : Blo 1921435 5474881 := bstep (se 2 (by rfl) ⟨2053080, by rfl⟩ : syracuseStep 5474881 = 4106161) B4106161
theorem B7299841 : Blo 1921435 7299841 := bstep (se 2 (by rfl) ⟨2737440, by rfl⟩ : syracuseStep 7299841 = 5474881) B5474881
theorem B9733121 : Blo 1921435 9733121 := bstep (se 2 (by rfl) ⟨3649920, by rfl⟩ : syracuseStep 9733121 = 7299841) B7299841
theorem B6488747 : Blo 1921435 6488747 := bstep (se 1 (by rfl) ⟨4866560, by rfl⟩ : syracuseStep 6488747 = 9733121) B9733121
theorem B4325831 : Blo 1921435 4325831 := bstep (se 1 (by rfl) ⟨3244373, by rfl⟩ : syracuseStep 4325831 = 6488747) B6488747
theorem B2883887 : Blo 1921435 2883887 := bstep (se 1 (by rfl) ⟨2162915, by rfl⟩ : syracuseStep 2883887 = 4325831) B4325831
theorem B1922591 : Blo 1921435 1922591 := bstep (se 1 (by rfl) ⟨1441943, by rfl⟩ : syracuseStep 1922591 = 2883887) B2883887
theorem B2883893 : Blo 1921435 2883893 := bbase (se 5 (by rfl) ⟨135182, by rfl⟩ : syracuseStep 2883893 = 270365) (by norm_num)
theorem B1922595 : Blo 1921435 1922595 := bstep (se 1 (by rfl) ⟨1441946, by rfl⟩ : syracuseStep 1922595 = 2883893) B2883893
theorem B4866581 : Blo 1921435 4866581 := bbase (se 6 (by rfl) ⟨114060, by rfl⟩ : syracuseStep 4866581 = 228121) (by norm_num)
theorem B3244387 : Blo 1921435 3244387 := bstep (se 1 (by rfl) ⟨2433290, by rfl⟩ : syracuseStep 3244387 = 4866581) B4866581
theorem B4325849 : Blo 1921435 4325849 := bstep (se 2 (by rfl) ⟨1622193, by rfl⟩ : syracuseStep 4325849 = 3244387) B3244387
theorem B2883899 : Blo 1921435 2883899 := bstep (se 1 (by rfl) ⟨2162924, by rfl⟩ : syracuseStep 2883899 = 4325849) B4325849
theorem B1922599 : Blo 1921435 1922599 := bstep (se 1 (by rfl) ⟨1441949, by rfl⟩ : syracuseStep 1922599 = 2883899) B2883899
theorem B2162929 : Blo 1921435 2162929 := bbase (se 2 (by rfl) ⟨811098, by rfl⟩ : syracuseStep 2162929 = 1622197) (by norm_num)
theorem B2883905 : Blo 1921435 2883905 := bstep (se 2 (by rfl) ⟨1081464, by rfl⟩ : syracuseStep 2883905 = 2162929) B2162929
theorem B1922603 : Blo 1921435 1922603 := bstep (se 1 (by rfl) ⟨1441952, by rfl⟩ : syracuseStep 1922603 = 2883905) B2883905
theorem B33297749 : Blo 1921435 33297749 := bbase (se 14 (by rfl) ⟨3048, by rfl⟩ : syracuseStep 33297749 = 6097) (by norm_num)
theorem B22198499 : Blo 1921435 22198499 := bstep (se 1 (by rfl) ⟨16648874, by rfl⟩ : syracuseStep 22198499 = 33297749) B33297749
theorem B14798999 : Blo 1921435 14798999 := bstep (se 1 (by rfl) ⟨11099249, by rfl⟩ : syracuseStep 14798999 = 22198499) B22198499
theorem B9865999 : Blo 1921435 9865999 := bstep (se 1 (by rfl) ⟨7399499, by rfl⟩ : syracuseStep 9865999 = 14798999) B14798999
theorem B13154665 : Blo 1921435 13154665 := bstep (se 2 (by rfl) ⟨4932999, by rfl⟩ : syracuseStep 13154665 = 9865999) B9865999
theorem B17539553 : Blo 1921435 17539553 := bstep (se 2 (by rfl) ⟨6577332, by rfl⟩ : syracuseStep 17539553 = 13154665) B13154665
theorem B11693035 : Blo 1921435 11693035 := bstep (se 1 (by rfl) ⟨8769776, by rfl⟩ : syracuseStep 11693035 = 17539553) B17539553
theorem B15590713 : Blo 1921435 15590713 := bstep (se 2 (by rfl) ⟨5846517, by rfl⟩ : syracuseStep 15590713 = 11693035) B11693035
theorem B20787617 : Blo 1921435 20787617 := bstep (se 2 (by rfl) ⟨7795356, by rfl⟩ : syracuseStep 20787617 = 15590713) B15590713
theorem B13858411 : Blo 1921435 13858411 := bstep (se 1 (by rfl) ⟨10393808, by rfl⟩ : syracuseStep 13858411 = 20787617) B20787617
theorem B18477881 : Blo 1921435 18477881 := bstep (se 2 (by rfl) ⟨6929205, by rfl⟩ : syracuseStep 18477881 = 13858411) B13858411
theorem B12318587 : Blo 1921435 12318587 := bstep (se 1 (by rfl) ⟨9238940, by rfl⟩ : syracuseStep 12318587 = 18477881) B18477881
theorem B8212391 : Blo 1921435 8212391 := bstep (se 1 (by rfl) ⟨6159293, by rfl⟩ : syracuseStep 8212391 = 12318587) B12318587
theorem B5474927 : Blo 1921435 5474927 := bstep (se 1 (by rfl) ⟨4106195, by rfl⟩ : syracuseStep 5474927 = 8212391) B8212391
theorem B3649951 : Blo 1921435 3649951 := bstep (se 1 (by rfl) ⟨2737463, by rfl⟩ : syracuseStep 3649951 = 5474927) B5474927
theorem B4866601 : Blo 1921435 4866601 := bstep (se 2 (by rfl) ⟨1824975, by rfl⟩ : syracuseStep 4866601 = 3649951) B3649951
theorem B6488801 : Blo 1921435 6488801 := bstep (se 2 (by rfl) ⟨2433300, by rfl⟩ : syracuseStep 6488801 = 4866601) B4866601
theorem B4325867 : Blo 1921435 4325867 := bstep (se 1 (by rfl) ⟨3244400, by rfl⟩ : syracuseStep 4325867 = 6488801) B6488801
theorem B2883911 : Blo 1921435 2883911 := bstep (se 1 (by rfl) ⟨2162933, by rfl⟩ : syracuseStep 2883911 = 4325867) B4325867
theorem B1922607 : Blo 1921435 1922607 := bstep (se 1 (by rfl) ⟨1441955, by rfl⟩ : syracuseStep 1922607 = 2883911) B2883911
theorem B2883917 : Blo 1921435 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B1922611 : Blo 1921435 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B4325885 : Blo 1921435 4325885 := bbase (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) (by norm_num)
theorem B2883923 : Blo 1921435 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B1922615 : Blo 1921435 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B3244421 : Blo 1921435 3244421 := bbase (se 4 (by rfl) ⟨304164, by rfl⟩ : syracuseStep 3244421 = 608329) (by norm_num)
theorem B2162947 : Blo 1921435 2162947 := bstep (se 1 (by rfl) ⟨1622210, by rfl⟩ : syracuseStep 2162947 = 3244421) B3244421
theorem B2883929 : Blo 1921435 2883929 := bstep (se 2 (by rfl) ⟨1081473, by rfl⟩ : syracuseStep 2883929 = 2162947) B2162947
theorem B1922619 : Blo 1921435 1922619 := bstep (se 1 (by rfl) ⟨1441964, by rfl⟩ : syracuseStep 1922619 = 2883929) B2883929
theorem B14599925 : Blo 1921435 14599925 := bbase (se 5 (by rfl) ⟨684371, by rfl⟩ : syracuseStep 14599925 = 1368743) (by norm_num)
theorem B9733283 : Blo 1921435 9733283 := bstep (se 1 (by rfl) ⟨7299962, by rfl⟩ : syracuseStep 9733283 = 14599925) B14599925
theorem B6488855 : Blo 1921435 6488855 := bstep (se 1 (by rfl) ⟨4866641, by rfl⟩ : syracuseStep 6488855 = 9733283) B9733283
theorem B4325903 : Blo 1921435 4325903 := bstep (se 1 (by rfl) ⟨3244427, by rfl⟩ : syracuseStep 4325903 = 6488855) B6488855
theorem B2883935 : Blo 1921435 2883935 := bstep (se 1 (by rfl) ⟨2162951, by rfl⟩ : syracuseStep 2883935 = 4325903) B4325903
theorem B1922623 : Blo 1921435 1922623 := bstep (se 1 (by rfl) ⟨1441967, by rfl⟩ : syracuseStep 1922623 = 2883935) B2883935
theorem B2883941 : Blo 1921435 2883941 := bbase (se 4 (by rfl) ⟨270369, by rfl⟩ : syracuseStep 2883941 = 540739) (by norm_num)
theorem B1922627 : Blo 1921435 1922627 := bstep (se 1 (by rfl) ⟨1441970, by rfl⟩ : syracuseStep 1922627 = 2883941) B2883941
theorem B3649997 : Blo 1921435 3649997 := bbase (se 3 (by rfl) ⟨684374, by rfl⟩ : syracuseStep 3649997 = 1368749) (by norm_num)
theorem B2433331 : Blo 1921435 2433331 := bstep (se 1 (by rfl) ⟨1824998, by rfl⟩ : syracuseStep 2433331 = 3649997) B3649997
theorem B3244441 : Blo 1921435 3244441 := bstep (se 2 (by rfl) ⟨1216665, by rfl⟩ : syracuseStep 3244441 = 2433331) B2433331
theorem B4325921 : Blo 1921435 4325921 := bstep (se 2 (by rfl) ⟨1622220, by rfl⟩ : syracuseStep 4325921 = 3244441) B3244441
theorem B2883947 : Blo 1921435 2883947 := bstep (se 1 (by rfl) ⟨2162960, by rfl⟩ : syracuseStep 2883947 = 4325921) B4325921
theorem B1922631 : Blo 1921435 1922631 := bstep (se 1 (by rfl) ⟨1441973, by rfl⟩ : syracuseStep 1922631 = 2883947) B2883947
theorem B2162965 : Blo 1921435 2162965 := bbase (se 6 (by rfl) ⟨50694, by rfl⟩ : syracuseStep 2162965 = 101389) (by norm_num)
theorem B2883953 : Blo 1921435 2883953 := bstep (se 2 (by rfl) ⟨1081482, by rfl⟩ : syracuseStep 2883953 = 2162965) B2162965
theorem B1922635 : Blo 1921435 1922635 := bstep (se 1 (by rfl) ⟨1441976, by rfl⟩ : syracuseStep 1922635 = 2883953) B2883953
theorem B2433341 : Blo 1921435 2433341 := bbase (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) (by norm_num)
theorem B6488909 : Blo 1921435 6488909 := bstep (se 3 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 6488909 = 2433341) B2433341
theorem B4325939 : Blo 1921435 4325939 := bstep (se 1 (by rfl) ⟨3244454, by rfl⟩ : syracuseStep 4325939 = 6488909) B6488909
theorem B2883959 : Blo 1921435 2883959 := bstep (se 1 (by rfl) ⟨2162969, by rfl⟩ : syracuseStep 2883959 = 4325939) B4325939
theorem B1922639 : Blo 1921435 1922639 := bstep (se 1 (by rfl) ⟨1441979, by rfl⟩ : syracuseStep 1922639 = 2883959) B2883959
theorem B2883965 : Blo 1921435 2883965 := bbase (se 3 (by rfl) ⟨540743, by rfl⟩ : syracuseStep 2883965 = 1081487) (by norm_num)
theorem B1922643 : Blo 1921435 1922643 := bstep (se 1 (by rfl) ⟨1441982, by rfl⟩ : syracuseStep 1922643 = 2883965) B2883965
theorem B4325957 : Blo 1921435 4325957 := bbase (se 4 (by rfl) ⟨405558, by rfl⟩ : syracuseStep 4325957 = 811117) (by norm_num)
theorem B2883971 : Blo 1921435 2883971 := bstep (se 1 (by rfl) ⟨2162978, by rfl⟩ : syracuseStep 2883971 = 4325957) B4325957
theorem B1922647 : Blo 1921435 1922647 := bstep (se 1 (by rfl) ⟨1441985, by rfl⟩ : syracuseStep 1922647 = 2883971) B2883971
theorem B2053145 : Blo 1921435 2053145 := bbase (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) (by norm_num)
theorem B5475053 : Blo 1921435 5475053 := bstep (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) B2053145
theorem B3650035 : Blo 1921435 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B4866713 : Blo 1921435 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B3244475 : Blo 1921435 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B2162983 : Blo 1921435 2162983 := bstep (se 1 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 2162983 = 3244475) B3244475
theorem B2883977 : Blo 1921435 2883977 := bstep (se 2 (by rfl) ⟨1081491, by rfl⟩ : syracuseStep 2883977 = 2162983) B2162983
theorem B1922651 : Blo 1921435 1922651 := bstep (se 1 (by rfl) ⟨1441988, by rfl⟩ : syracuseStep 1922651 = 2883977) B2883977
theorem B9733445 : Blo 1921435 9733445 := bbase (se 4 (by rfl) ⟨912510, by rfl⟩ : syracuseStep 9733445 = 1825021) (by norm_num)
theorem B6488963 : Blo 1921435 6488963 := bstep (se 1 (by rfl) ⟨4866722, by rfl⟩ : syracuseStep 6488963 = 9733445) B9733445
theorem B4325975 : Blo 1921435 4325975 := bstep (se 1 (by rfl) ⟨3244481, by rfl⟩ : syracuseStep 4325975 = 6488963) B6488963
theorem B2883983 : Blo 1921435 2883983 := bstep (se 1 (by rfl) ⟨2162987, by rfl⟩ : syracuseStep 2883983 = 4325975) B4325975
theorem B1922655 : Blo 1921435 1922655 := bstep (se 1 (by rfl) ⟨1441991, by rfl⟩ : syracuseStep 1922655 = 2883983) B2883983
theorem B2883989 : Blo 1921435 2883989 := bbase (se 6 (by rfl) ⟨67593, by rfl⟩ : syracuseStep 2883989 = 135187) (by norm_num)
theorem B1922659 : Blo 1921435 1922659 := bstep (se 1 (by rfl) ⟨1441994, by rfl⟩ : syracuseStep 1922659 = 2883989) B2883989
theorem B4619605 : Blo 1921435 4619605 := bbase (se 11 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 4619605 = 6767) (by norm_num)
theorem B6159473 : Blo 1921435 6159473 := bstep (se 2 (by rfl) ⟨2309802, by rfl⟩ : syracuseStep 6159473 = 4619605) B4619605
theorem B4106315 : Blo 1921435 4106315 := bstep (se 1 (by rfl) ⟨3079736, by rfl⟩ : syracuseStep 4106315 = 6159473) B6159473
theorem B10950173 : Blo 1921435 10950173 := bstep (se 3 (by rfl) ⟨2053157, by rfl⟩ : syracuseStep 10950173 = 4106315) B4106315
theorem B7300115 : Blo 1921435 7300115 := bstep (se 1 (by rfl) ⟨5475086, by rfl⟩ : syracuseStep 7300115 = 10950173) B10950173
theorem B4866743 : Blo 1921435 4866743 := bstep (se 1 (by rfl) ⟨3650057, by rfl⟩ : syracuseStep 4866743 = 7300115) B7300115
theorem B3244495 : Blo 1921435 3244495 := bstep (se 1 (by rfl) ⟨2433371, by rfl⟩ : syracuseStep 3244495 = 4866743) B4866743
theorem B4325993 : Blo 1921435 4325993 := bstep (se 2 (by rfl) ⟨1622247, by rfl⟩ : syracuseStep 4325993 = 3244495) B3244495
theorem B2883995 : Blo 1921435 2883995 := bstep (se 1 (by rfl) ⟨2162996, by rfl⟩ : syracuseStep 2883995 = 4325993) B4325993
theorem B1922663 : Blo 1921435 1922663 := bstep (se 1 (by rfl) ⟨1441997, by rfl⟩ : syracuseStep 1922663 = 2883995) B2883995
theorem B2163001 : Blo 1921435 2163001 := bbase (se 2 (by rfl) ⟨811125, by rfl⟩ : syracuseStep 2163001 = 1622251) (by norm_num)
theorem B2884001 : Blo 1921435 2884001 := bstep (se 2 (by rfl) ⟨1081500, by rfl⟩ : syracuseStep 2884001 = 2163001) B2163001
theorem B1922667 : Blo 1921435 1922667 := bstep (se 1 (by rfl) ⟨1442000, by rfl⟩ : syracuseStep 1922667 = 2884001) B2884001
theorem B5475109 : Blo 1921435 5475109 := bbase (se 4 (by rfl) ⟨513291, by rfl⟩ : syracuseStep 5475109 = 1026583) (by norm_num)
theorem B7300145 : Blo 1921435 7300145 := bstep (se 2 (by rfl) ⟨2737554, by rfl⟩ : syracuseStep 7300145 = 5475109) B5475109
theorem B4866763 : Blo 1921435 4866763 := bstep (se 1 (by rfl) ⟨3650072, by rfl⟩ : syracuseStep 4866763 = 7300145) B7300145
theorem B6489017 : Blo 1921435 6489017 := bstep (se 2 (by rfl) ⟨2433381, by rfl⟩ : syracuseStep 6489017 = 4866763) B4866763
theorem B4326011 : Blo 1921435 4326011 := bstep (se 1 (by rfl) ⟨3244508, by rfl⟩ : syracuseStep 4326011 = 6489017) B6489017
theorem B2884007 : Blo 1921435 2884007 := bstep (se 1 (by rfl) ⟨2163005, by rfl⟩ : syracuseStep 2884007 = 4326011) B4326011
theorem B1922671 : Blo 1921435 1922671 := bstep (se 1 (by rfl) ⟨1442003, by rfl⟩ : syracuseStep 1922671 = 2884007) B2884007
theorem B2884013 : Blo 1921435 2884013 := bbase (se 3 (by rfl) ⟨540752, by rfl⟩ : syracuseStep 2884013 = 1081505) (by norm_num)
theorem B1922675 : Blo 1921435 1922675 := bstep (se 1 (by rfl) ⟨1442006, by rfl⟩ : syracuseStep 1922675 = 2884013) B2884013
theorem B4326029 : Blo 1921435 4326029 := bbase (se 3 (by rfl) ⟨811130, by rfl⟩ : syracuseStep 4326029 = 1622261) (by norm_num)
theorem B2884019 : Blo 1921435 2884019 := bstep (se 1 (by rfl) ⟨2163014, by rfl⟩ : syracuseStep 2884019 = 4326029) B4326029
theorem B1922679 : Blo 1921435 1922679 := bstep (se 1 (by rfl) ⟨1442009, by rfl⟩ : syracuseStep 1922679 = 2884019) B2884019
theorem B2433397 : Blo 1921435 2433397 := bbase (se 5 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 2433397 = 228131) (by norm_num)
theorem B3244529 : Blo 1921435 3244529 := bstep (se 2 (by rfl) ⟨1216698, by rfl⟩ : syracuseStep 3244529 = 2433397) B2433397
theorem B2163019 : Blo 1921435 2163019 := bstep (se 1 (by rfl) ⟨1622264, by rfl⟩ : syracuseStep 2163019 = 3244529) B3244529
theorem B2884025 : Blo 1921435 2884025 := bstep (se 2 (by rfl) ⟨1081509, by rfl⟩ : syracuseStep 2884025 = 2163019) B2163019
theorem B1922683 : Blo 1921435 1922683 := bstep (se 1 (by rfl) ⟨1442012, by rfl⟩ : syracuseStep 1922683 = 2884025) B2884025
theorem B2341345 : Blo 1921435 2341345 := bbase (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) (by norm_num)
theorem B3121793 : Blo 1921435 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B133196501 : Blo 1921435 133196501 := bstep (se 7 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 133196501 = 3121793) B3121793
theorem B88797667 : Blo 1921435 88797667 := bstep (se 1 (by rfl) ⟨66598250, by rfl⟩ : syracuseStep 88797667 = 133196501) B133196501
theorem B118396889 : Blo 1921435 118396889 := bstep (se 2 (by rfl) ⟨44398833, by rfl⟩ : syracuseStep 118396889 = 88797667) B88797667
theorem B78931259 : Blo 1921435 78931259 := bstep (se 1 (by rfl) ⟨59198444, by rfl⟩ : syracuseStep 78931259 = 118396889) B118396889
theorem B52620839 : Blo 1921435 52620839 := bstep (se 1 (by rfl) ⟨39465629, by rfl⟩ : syracuseStep 52620839 = 78931259) B78931259
theorem B35080559 : Blo 1921435 35080559 := bstep (se 1 (by rfl) ⟨26310419, by rfl⟩ : syracuseStep 35080559 = 52620839) B52620839
theorem B23387039 : Blo 1921435 23387039 := bstep (se 1 (by rfl) ⟨17540279, by rfl⟩ : syracuseStep 23387039 = 35080559) B35080559
theorem B15591359 : Blo 1921435 15591359 := bstep (se 1 (by rfl) ⟨11693519, by rfl⟩ : syracuseStep 15591359 = 23387039) B23387039
theorem B10394239 : Blo 1921435 10394239 := bstep (se 1 (by rfl) ⟨7795679, by rfl⟩ : syracuseStep 10394239 = 15591359) B15591359
theorem B13858985 : Blo 1921435 13858985 := bstep (se 2 (by rfl) ⟨5197119, by rfl⟩ : syracuseStep 13858985 = 10394239) B10394239
theorem B36957293 : Blo 1921435 36957293 := bstep (se 3 (by rfl) ⟨6929492, by rfl⟩ : syracuseStep 36957293 = 13858985) B13858985
theorem B24638195 : Blo 1921435 24638195 := bstep (se 1 (by rfl) ⟨18478646, by rfl⟩ : syracuseStep 24638195 = 36957293) B36957293
theorem B16425463 : Blo 1921435 16425463 := bstep (se 1 (by rfl) ⟨12319097, by rfl⟩ : syracuseStep 16425463 = 24638195) B24638195
theorem B21900617 : Blo 1921435 21900617 := bstep (se 2 (by rfl) ⟨8212731, by rfl⟩ : syracuseStep 21900617 = 16425463) B16425463
theorem B14600411 : Blo 1921435 14600411 := bstep (se 1 (by rfl) ⟨10950308, by rfl⟩ : syracuseStep 14600411 = 21900617) B21900617
theorem B9733607 : Blo 1921435 9733607 := bstep (se 1 (by rfl) ⟨7300205, by rfl⟩ : syracuseStep 9733607 = 14600411) B14600411
theorem B6489071 : Blo 1921435 6489071 := bstep (se 1 (by rfl) ⟨4866803, by rfl⟩ : syracuseStep 6489071 = 9733607) B9733607
theorem B4326047 : Blo 1921435 4326047 := bstep (se 1 (by rfl) ⟨3244535, by rfl⟩ : syracuseStep 4326047 = 6489071) B6489071
theorem B2884031 : Blo 1921435 2884031 := bstep (se 1 (by rfl) ⟨2163023, by rfl⟩ : syracuseStep 2884031 = 4326047) B4326047
theorem B1922687 : Blo 1921435 1922687 := bstep (se 1 (by rfl) ⟨1442015, by rfl⟩ : syracuseStep 1922687 = 2884031) B2884031
theorem B2884037 : Blo 1921435 2884037 := bbase (se 4 (by rfl) ⟨270378, by rfl⟩ : syracuseStep 2884037 = 540757) (by norm_num)
theorem B1922691 : Blo 1921435 1922691 := bstep (se 1 (by rfl) ⟨1442018, by rfl⟩ : syracuseStep 1922691 = 2884037) B2884037
theorem B3244549 : Blo 1921435 3244549 := bbase (se 4 (by rfl) ⟨304176, by rfl⟩ : syracuseStep 3244549 = 608353) (by norm_num)
theorem B4326065 : Blo 1921435 4326065 := bstep (se 2 (by rfl) ⟨1622274, by rfl⟩ : syracuseStep 4326065 = 3244549) B3244549
theorem B2884043 : Blo 1921435 2884043 := bstep (se 1 (by rfl) ⟨2163032, by rfl⟩ : syracuseStep 2884043 = 4326065) B4326065
theorem B1922695 : Blo 1921435 1922695 := bstep (se 1 (by rfl) ⟨1442021, by rfl⟩ : syracuseStep 1922695 = 2884043) B2884043
theorem B2163037 : Blo 1921435 2163037 := bbase (se 3 (by rfl) ⟨405569, by rfl⟩ : syracuseStep 2163037 = 811139) (by norm_num)
theorem B2884049 : Blo 1921435 2884049 := bstep (se 2 (by rfl) ⟨1081518, by rfl⟩ : syracuseStep 2884049 = 2163037) B2163037
theorem B1922699 : Blo 1921435 1922699 := bstep (se 1 (by rfl) ⟨1442024, by rfl⟩ : syracuseStep 1922699 = 2884049) B2884049
theorem B6489125 : Blo 1921435 6489125 := bbase (se 4 (by rfl) ⟨608355, by rfl⟩ : syracuseStep 6489125 = 1216711) (by norm_num)
theorem B4326083 : Blo 1921435 4326083 := bstep (se 1 (by rfl) ⟨3244562, by rfl⟩ : syracuseStep 4326083 = 6489125) B6489125
theorem B2884055 : Blo 1921435 2884055 := bstep (se 1 (by rfl) ⟨2163041, by rfl⟩ : syracuseStep 2884055 = 4326083) B4326083
theorem B1922703 : Blo 1921435 1922703 := bstep (se 1 (by rfl) ⟨1442027, by rfl⟩ : syracuseStep 1922703 = 2884055) B2884055
theorem B2884061 : Blo 1921435 2884061 := bbase (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) (by norm_num)
theorem B1922707 : Blo 1921435 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B4326101 : Blo 1921435 4326101 := bbase (se 7 (by rfl) ⟨50696, by rfl⟩ : syracuseStep 4326101 = 101393) (by norm_num)
theorem B2884067 : Blo 1921435 2884067 := bstep (se 1 (by rfl) ⟨2163050, by rfl⟩ : syracuseStep 2884067 = 4326101) B4326101
theorem B1922711 : Blo 1921435 1922711 := bstep (se 1 (by rfl) ⟨1442033, by rfl⟩ : syracuseStep 1922711 = 2884067) B2884067
theorem B8212853 : Blo 1921435 8212853 := bbase (se 5 (by rfl) ⟨384977, by rfl⟩ : syracuseStep 8212853 = 769955) (by norm_num)
theorem B5475235 : Blo 1921435 5475235 := bstep (se 1 (by rfl) ⟨4106426, by rfl⟩ : syracuseStep 5475235 = 8212853) B8212853
theorem B7300313 : Blo 1921435 7300313 := bstep (se 2 (by rfl) ⟨2737617, by rfl⟩ : syracuseStep 7300313 = 5475235) B5475235
theorem B4866875 : Blo 1921435 4866875 := bstep (se 1 (by rfl) ⟨3650156, by rfl⟩ : syracuseStep 4866875 = 7300313) B7300313
theorem B3244583 : Blo 1921435 3244583 := bstep (se 1 (by rfl) ⟨2433437, by rfl⟩ : syracuseStep 3244583 = 4866875) B4866875
theorem B2163055 : Blo 1921435 2163055 := bstep (se 1 (by rfl) ⟨1622291, by rfl⟩ : syracuseStep 2163055 = 3244583) B3244583
theorem B2884073 : Blo 1921435 2884073 := bstep (se 2 (by rfl) ⟨1081527, by rfl⟩ : syracuseStep 2884073 = 2163055) B2163055
theorem B1922715 : Blo 1921435 1922715 := bstep (se 1 (by rfl) ⟨1442036, by rfl⟩ : syracuseStep 1922715 = 2884073) B2884073
theorem B3699965 : Blo 1921435 3699965 := bbase (se 3 (by rfl) ⟨693743, by rfl⟩ : syracuseStep 3699965 = 1387487) (by norm_num)
theorem B9866573 : Blo 1921435 9866573 := bstep (se 3 (by rfl) ⟨1849982, by rfl⟩ : syracuseStep 9866573 = 3699965) B3699965
theorem B6577715 : Blo 1921435 6577715 := bstep (se 1 (by rfl) ⟨4933286, by rfl⟩ : syracuseStep 6577715 = 9866573) B9866573
theorem B4385143 : Blo 1921435 4385143 := bstep (se 1 (by rfl) ⟨3288857, by rfl⟩ : syracuseStep 4385143 = 6577715) B6577715
theorem B23387429 : Blo 1921435 23387429 := bstep (se 4 (by rfl) ⟨2192571, by rfl⟩ : syracuseStep 23387429 = 4385143) B4385143
theorem B15591619 : Blo 1921435 15591619 := bstep (se 1 (by rfl) ⟨11693714, by rfl⟩ : syracuseStep 15591619 = 23387429) B23387429
theorem B20788825 : Blo 1921435 20788825 := bstep (se 2 (by rfl) ⟨7795809, by rfl⟩ : syracuseStep 20788825 = 15591619) B15591619
theorem B27718433 : Blo 1921435 27718433 := bstep (se 2 (by rfl) ⟨10394412, by rfl⟩ : syracuseStep 27718433 = 20788825) B20788825
theorem B18478955 : Blo 1921435 18478955 := bstep (se 1 (by rfl) ⟨13859216, by rfl⟩ : syracuseStep 18478955 = 27718433) B27718433
theorem B12319303 : Blo 1921435 12319303 := bstep (se 1 (by rfl) ⟨9239477, by rfl⟩ : syracuseStep 12319303 = 18478955) B18478955
theorem B16425737 : Blo 1921435 16425737 := bstep (se 2 (by rfl) ⟨6159651, by rfl⟩ : syracuseStep 16425737 = 12319303) B12319303
theorem B10950491 : Blo 1921435 10950491 := bstep (se 1 (by rfl) ⟨8212868, by rfl⟩ : syracuseStep 10950491 = 16425737) B16425737
theorem B7300327 : Blo 1921435 7300327 := bstep (se 1 (by rfl) ⟨5475245, by rfl⟩ : syracuseStep 7300327 = 10950491) B10950491
theorem B9733769 : Blo 1921435 9733769 := bstep (se 2 (by rfl) ⟨3650163, by rfl⟩ : syracuseStep 9733769 = 7300327) B7300327
theorem B6489179 : Blo 1921435 6489179 := bstep (se 1 (by rfl) ⟨4866884, by rfl⟩ : syracuseStep 6489179 = 9733769) B9733769
theorem B4326119 : Blo 1921435 4326119 := bstep (se 1 (by rfl) ⟨3244589, by rfl⟩ : syracuseStep 4326119 = 6489179) B6489179
theorem B2884079 : Blo 1921435 2884079 := bstep (se 1 (by rfl) ⟨2163059, by rfl⟩ : syracuseStep 2884079 = 4326119) B4326119
theorem B1922719 : Blo 1921435 1922719 := bstep (se 1 (by rfl) ⟨1442039, by rfl⟩ : syracuseStep 1922719 = 2884079) B2884079
theorem B2884085 : Blo 1921435 2884085 := bbase (se 5 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 2884085 = 270383) (by norm_num)
theorem B1922723 : Blo 1921435 1922723 := bstep (se 1 (by rfl) ⟨1442042, by rfl⟩ : syracuseStep 1922723 = 2884085) B2884085
theorem B5475269 : Blo 1921435 5475269 := bbase (se 4 (by rfl) ⟨513306, by rfl⟩ : syracuseStep 5475269 = 1026613) (by norm_num)
theorem B3650179 : Blo 1921435 3650179 := bstep (se 1 (by rfl) ⟨2737634, by rfl⟩ : syracuseStep 3650179 = 5475269) B5475269
theorem B4866905 : Blo 1921435 4866905 := bstep (se 2 (by rfl) ⟨1825089, by rfl⟩ : syracuseStep 4866905 = 3650179) B3650179
theorem B3244603 : Blo 1921435 3244603 := bstep (se 1 (by rfl) ⟨2433452, by rfl⟩ : syracuseStep 3244603 = 4866905) B4866905
theorem B4326137 : Blo 1921435 4326137 := bstep (se 2 (by rfl) ⟨1622301, by rfl⟩ : syracuseStep 4326137 = 3244603) B3244603
theorem B2884091 : Blo 1921435 2884091 := bstep (se 1 (by rfl) ⟨2163068, by rfl⟩ : syracuseStep 2884091 = 4326137) B4326137
theorem B1922727 : Blo 1921435 1922727 := bstep (se 1 (by rfl) ⟨1442045, by rfl⟩ : syracuseStep 1922727 = 2884091) B2884091
theorem B2163073 : Blo 1921435 2163073 := bbase (se 2 (by rfl) ⟨811152, by rfl⟩ : syracuseStep 2163073 = 1622305) (by norm_num)
theorem B2884097 : Blo 1921435 2884097 := bstep (se 2 (by rfl) ⟨1081536, by rfl⟩ : syracuseStep 2884097 = 2163073) B2163073
theorem B1922731 : Blo 1921435 1922731 := bstep (se 1 (by rfl) ⟨1442048, by rfl⟩ : syracuseStep 1922731 = 2884097) B2884097
theorem B4866925 : Blo 1921435 4866925 := bbase (se 3 (by rfl) ⟨912548, by rfl⟩ : syracuseStep 4866925 = 1825097) (by norm_num)
theorem B6489233 : Blo 1921435 6489233 := bstep (se 2 (by rfl) ⟨2433462, by rfl⟩ : syracuseStep 6489233 = 4866925) B4866925
theorem B4326155 : Blo 1921435 4326155 := bstep (se 1 (by rfl) ⟨3244616, by rfl⟩ : syracuseStep 4326155 = 6489233) B6489233
theorem B2884103 : Blo 1921435 2884103 := bstep (se 1 (by rfl) ⟨2163077, by rfl⟩ : syracuseStep 2884103 = 4326155) B4326155
theorem B1922735 : Blo 1921435 1922735 := bstep (se 1 (by rfl) ⟨1442051, by rfl⟩ : syracuseStep 1922735 = 2884103) B2884103
theorem B2884109 : Blo 1921435 2884109 := bbase (se 3 (by rfl) ⟨540770, by rfl⟩ : syracuseStep 2884109 = 1081541) (by norm_num)
theorem B1922739 : Blo 1921435 1922739 := bstep (se 1 (by rfl) ⟨1442054, by rfl⟩ : syracuseStep 1922739 = 2884109) B2884109
theorem B4326173 : Blo 1921435 4326173 := bbase (se 3 (by rfl) ⟨811157, by rfl⟩ : syracuseStep 4326173 = 1622315) (by norm_num)
theorem B2884115 : Blo 1921435 2884115 := bstep (se 1 (by rfl) ⟨2163086, by rfl⟩ : syracuseStep 2884115 = 4326173) B4326173
theorem B1922743 : Blo 1921435 1922743 := bstep (se 1 (by rfl) ⟨1442057, by rfl⟩ : syracuseStep 1922743 = 2884115) B2884115
theorem B3244637 : Blo 1921435 3244637 := bbase (se 3 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 3244637 = 1216739) (by norm_num)
theorem B2163091 : Blo 1921435 2163091 := bstep (se 1 (by rfl) ⟨1622318, by rfl⟩ : syracuseStep 2163091 = 3244637) B3244637
theorem B2884121 : Blo 1921435 2884121 := bstep (se 2 (by rfl) ⟨1081545, by rfl⟩ : syracuseStep 2884121 = 2163091) B2163091
theorem B1922747 : Blo 1921435 1922747 := bstep (se 1 (by rfl) ⟨1442060, by rfl⟩ : syracuseStep 1922747 = 2884121) B2884121
theorem B3079877 : Blo 1921435 3079877 := bbase (se 4 (by rfl) ⟨288738, by rfl⟩ : syracuseStep 3079877 = 577477) (by norm_num)
theorem B8213005 : Blo 1921435 8213005 := bstep (se 3 (by rfl) ⟨1539938, by rfl⟩ : syracuseStep 8213005 = 3079877) B3079877
theorem B10950673 : Blo 1921435 10950673 := bstep (se 2 (by rfl) ⟨4106502, by rfl⟩ : syracuseStep 10950673 = 8213005) B8213005
theorem B14600897 : Blo 1921435 14600897 := bstep (se 2 (by rfl) ⟨5475336, by rfl⟩ : syracuseStep 14600897 = 10950673) B10950673
theorem B9733931 : Blo 1921435 9733931 := bstep (se 1 (by rfl) ⟨7300448, by rfl⟩ : syracuseStep 9733931 = 14600897) B14600897
theorem B6489287 : Blo 1921435 6489287 := bstep (se 1 (by rfl) ⟨4866965, by rfl⟩ : syracuseStep 6489287 = 9733931) B9733931
theorem B4326191 : Blo 1921435 4326191 := bstep (se 1 (by rfl) ⟨3244643, by rfl⟩ : syracuseStep 4326191 = 6489287) B6489287
theorem B2884127 : Blo 1921435 2884127 := bstep (se 1 (by rfl) ⟨2163095, by rfl⟩ : syracuseStep 2884127 = 4326191) B4326191
theorem B1922751 : Blo 1921435 1922751 := bstep (se 1 (by rfl) ⟨1442063, by rfl⟩ : syracuseStep 1922751 = 2884127) B2884127
theorem B2884133 : Blo 1921435 2884133 := bbase (se 4 (by rfl) ⟨270387, by rfl⟩ : syracuseStep 2884133 = 540775) (by norm_num)
theorem B1922755 : Blo 1921435 1922755 := bstep (se 1 (by rfl) ⟨1442066, by rfl⟩ : syracuseStep 1922755 = 2884133) B2884133
theorem B2433493 : Blo 1921435 2433493 := bbase (se 7 (by rfl) ⟨28517, by rfl⟩ : syracuseStep 2433493 = 57035) (by norm_num)
theorem B3244657 : Blo 1921435 3244657 := bstep (se 2 (by rfl) ⟨1216746, by rfl⟩ : syracuseStep 3244657 = 2433493) B2433493
theorem B4326209 : Blo 1921435 4326209 := bstep (se 2 (by rfl) ⟨1622328, by rfl⟩ : syracuseStep 4326209 = 3244657) B3244657
theorem B2884139 : Blo 1921435 2884139 := bstep (se 1 (by rfl) ⟨2163104, by rfl⟩ : syracuseStep 2884139 = 4326209) B4326209
theorem B1922759 : Blo 1921435 1922759 := bstep (se 1 (by rfl) ⟨1442069, by rfl⟩ : syracuseStep 1922759 = 2884139) B2884139
theorem B2163109 : Blo 1921435 2163109 := bbase (se 4 (by rfl) ⟨202791, by rfl⟩ : syracuseStep 2163109 = 405583) (by norm_num)
theorem B2884145 : Blo 1921435 2884145 := bstep (se 2 (by rfl) ⟨1081554, by rfl⟩ : syracuseStep 2884145 = 2163109) B2163109
theorem B1922763 : Blo 1921435 1922763 := bstep (se 1 (by rfl) ⟨1442072, by rfl⟩ : syracuseStep 1922763 = 2884145) B2884145
theorem B3288941 : Blo 1921435 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B2192627 : Blo 1921435 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B5847005 : Blo 1921435 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B15592013 : Blo 1921435 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B10394675 : Blo 1921435 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B6929783 : Blo 1921435 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B4619855 : Blo 1921435 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B12319613 : Blo 1921435 12319613 := bstep (se 3 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 12319613 = 4619855) B4619855
theorem B8213075 : Blo 1921435 8213075 := bstep (se 1 (by rfl) ⟨6159806, by rfl⟩ : syracuseStep 8213075 = 12319613) B12319613
theorem B5475383 : Blo 1921435 5475383 := bstep (se 1 (by rfl) ⟨4106537, by rfl⟩ : syracuseStep 5475383 = 8213075) B8213075
theorem B3650255 : Blo 1921435 3650255 := bstep (se 1 (by rfl) ⟨2737691, by rfl⟩ : syracuseStep 3650255 = 5475383) B5475383
theorem B2433503 : Blo 1921435 2433503 := bstep (se 1 (by rfl) ⟨1825127, by rfl⟩ : syracuseStep 2433503 = 3650255) B3650255
theorem B6489341 : Blo 1921435 6489341 := bstep (se 3 (by rfl) ⟨1216751, by rfl⟩ : syracuseStep 6489341 = 2433503) B2433503
theorem B4326227 : Blo 1921435 4326227 := bstep (se 1 (by rfl) ⟨3244670, by rfl⟩ : syracuseStep 4326227 = 6489341) B6489341
theorem B2884151 : Blo 1921435 2884151 := bstep (se 1 (by rfl) ⟨2163113, by rfl⟩ : syracuseStep 2884151 = 4326227) B4326227
theorem B1922767 : Blo 1921435 1922767 := bstep (se 1 (by rfl) ⟨1442075, by rfl⟩ : syracuseStep 1922767 = 2884151) B2884151
theorem B2884157 : Blo 1921435 2884157 := bbase (se 3 (by rfl) ⟨540779, by rfl⟩ : syracuseStep 2884157 = 1081559) (by norm_num)
theorem B1922771 : Blo 1921435 1922771 := bstep (se 1 (by rfl) ⟨1442078, by rfl⟩ : syracuseStep 1922771 = 2884157) B2884157
theorem B4326245 : Blo 1921435 4326245 := bbase (se 4 (by rfl) ⟨405585, by rfl⟩ : syracuseStep 4326245 = 811171) (by norm_num)
theorem B2884163 : Blo 1921435 2884163 := bstep (se 1 (by rfl) ⟨2163122, by rfl⟩ : syracuseStep 2884163 = 4326245) B4326245
theorem B1922775 : Blo 1921435 1922775 := bstep (se 1 (by rfl) ⟨1442081, by rfl⟩ : syracuseStep 1922775 = 2884163) B2884163
theorem B4867037 : Blo 1921435 4867037 := bbase (se 3 (by rfl) ⟨912569, by rfl⟩ : syracuseStep 4867037 = 1825139) (by norm_num)
theorem B3244691 : Blo 1921435 3244691 := bstep (se 1 (by rfl) ⟨2433518, by rfl⟩ : syracuseStep 3244691 = 4867037) B4867037
theorem B2163127 : Blo 1921435 2163127 := bstep (se 1 (by rfl) ⟨1622345, by rfl⟩ : syracuseStep 2163127 = 3244691) B3244691
theorem B2884169 : Blo 1921435 2884169 := bstep (se 2 (by rfl) ⟨1081563, by rfl⟩ : syracuseStep 2884169 = 2163127) B2163127
theorem B1922779 : Blo 1921435 1922779 := bstep (se 1 (by rfl) ⟨1442084, by rfl⟩ : syracuseStep 1922779 = 2884169) B2884169
theorem B3650285 : Blo 1921435 3650285 := bbase (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) (by norm_num)
theorem B9734093 : Blo 1921435 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B6489395 : Blo 1921435 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B4326263 : Blo 1921435 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B2884175 : Blo 1921435 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B1922783 : Blo 1921435 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B2884181 : Blo 1921435 2884181 := bbase (se 8 (by rfl) ⟨16899, by rfl⟩ : syracuseStep 2884181 = 33799) (by norm_num)
theorem B1922787 : Blo 1921435 1922787 := bstep (se 1 (by rfl) ⟨1442090, by rfl⟩ : syracuseStep 1922787 = 2884181) B2884181
theorem B2598701 : Blo 1921435 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B6929869 : Blo 1921435 6929869 := bstep (se 3 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 6929869 = 2598701) B2598701
theorem B9239825 : Blo 1921435 9239825 := bstep (se 2 (by rfl) ⟨3464934, by rfl⟩ : syracuseStep 9239825 = 6929869) B6929869
theorem B6159883 : Blo 1921435 6159883 := bstep (se 1 (by rfl) ⟨4619912, by rfl⟩ : syracuseStep 6159883 = 9239825) B9239825
theorem B8213177 : Blo 1921435 8213177 := bstep (se 2 (by rfl) ⟨3079941, by rfl⟩ : syracuseStep 8213177 = 6159883) B6159883
theorem B5475451 : Blo 1921435 5475451 := bstep (se 1 (by rfl) ⟨4106588, by rfl⟩ : syracuseStep 5475451 = 8213177) B8213177
theorem B7300601 : Blo 1921435 7300601 := bstep (se 2 (by rfl) ⟨2737725, by rfl⟩ : syracuseStep 7300601 = 5475451) B5475451
theorem B4867067 : Blo 1921435 4867067 := bstep (se 1 (by rfl) ⟨3650300, by rfl⟩ : syracuseStep 4867067 = 7300601) B7300601
theorem B3244711 : Blo 1921435 3244711 := bstep (se 1 (by rfl) ⟨2433533, by rfl⟩ : syracuseStep 3244711 = 4867067) B4867067
theorem B4326281 : Blo 1921435 4326281 := bstep (se 2 (by rfl) ⟨1622355, by rfl⟩ : syracuseStep 4326281 = 3244711) B3244711
theorem B2884187 : Blo 1921435 2884187 := bstep (se 1 (by rfl) ⟨2163140, by rfl⟩ : syracuseStep 2884187 = 4326281) B4326281
theorem B1922791 : Blo 1921435 1922791 := bstep (se 1 (by rfl) ⟨1442093, by rfl⟩ : syracuseStep 1922791 = 2884187) B2884187
theorem B2163145 : Blo 1921435 2163145 := bbase (se 2 (by rfl) ⟨811179, by rfl⟩ : syracuseStep 2163145 = 1622359) (by norm_num)
theorem B2884193 : Blo 1921435 2884193 := bstep (se 2 (by rfl) ⟨1081572, by rfl⟩ : syracuseStep 2884193 = 2163145) B2163145
theorem B1922795 : Blo 1921435 1922795 := bstep (se 1 (by rfl) ⟨1442096, by rfl⟩ : syracuseStep 1922795 = 2884193) B2884193
theorem B16426421 : Blo 1921435 16426421 := bbase (se 5 (by rfl) ⟨769988, by rfl⟩ : syracuseStep 16426421 = 1539977) (by norm_num)
theorem B10950947 : Blo 1921435 10950947 := bstep (se 1 (by rfl) ⟨8213210, by rfl⟩ : syracuseStep 10950947 = 16426421) B16426421
theorem B7300631 : Blo 1921435 7300631 := bstep (se 1 (by rfl) ⟨5475473, by rfl⟩ : syracuseStep 7300631 = 10950947) B10950947
theorem B4867087 : Blo 1921435 4867087 := bstep (se 1 (by rfl) ⟨3650315, by rfl⟩ : syracuseStep 4867087 = 7300631) B7300631
theorem B6489449 : Blo 1921435 6489449 := bstep (se 2 (by rfl) ⟨2433543, by rfl⟩ : syracuseStep 6489449 = 4867087) B4867087
theorem B4326299 : Blo 1921435 4326299 := bstep (se 1 (by rfl) ⟨3244724, by rfl⟩ : syracuseStep 4326299 = 6489449) B6489449
theorem B2884199 : Blo 1921435 2884199 := bstep (se 1 (by rfl) ⟨2163149, by rfl⟩ : syracuseStep 2884199 = 4326299) B4326299
theorem B1922799 : Blo 1921435 1922799 := bstep (se 1 (by rfl) ⟨1442099, by rfl⟩ : syracuseStep 1922799 = 2884199) B2884199
theorem B2884205 : Blo 1921435 2884205 := bbase (se 3 (by rfl) ⟨540788, by rfl⟩ : syracuseStep 2884205 = 1081577) (by norm_num)
theorem B1922803 : Blo 1921435 1922803 := bstep (se 1 (by rfl) ⟨1442102, by rfl⟩ : syracuseStep 1922803 = 2884205) B2884205
theorem B4326317 : Blo 1921435 4326317 := bbase (se 3 (by rfl) ⟨811184, by rfl⟩ : syracuseStep 4326317 = 1622369) (by norm_num)
theorem B2884211 : Blo 1921435 2884211 := bstep (se 1 (by rfl) ⟨2163158, by rfl⟩ : syracuseStep 2884211 = 4326317) B4326317
theorem B1922807 : Blo 1921435 1922807 := bstep (se 1 (by rfl) ⟨1442105, by rfl⟩ : syracuseStep 1922807 = 2884211) B2884211
theorem B5475509 : Blo 1921435 5475509 := bbase (se 5 (by rfl) ⟨256664, by rfl⟩ : syracuseStep 5475509 = 513329) (by norm_num)
theorem B3650339 : Blo 1921435 3650339 := bstep (se 1 (by rfl) ⟨2737754, by rfl⟩ : syracuseStep 3650339 = 5475509) B5475509
theorem B2433559 : Blo 1921435 2433559 := bstep (se 1 (by rfl) ⟨1825169, by rfl⟩ : syracuseStep 2433559 = 3650339) B3650339
theorem B3244745 : Blo 1921435 3244745 := bstep (se 2 (by rfl) ⟨1216779, by rfl⟩ : syracuseStep 3244745 = 2433559) B2433559
theorem B2163163 : Blo 1921435 2163163 := bstep (se 1 (by rfl) ⟨1622372, by rfl⟩ : syracuseStep 2163163 = 3244745) B3244745
theorem B2884217 : Blo 1921435 2884217 := bstep (se 2 (by rfl) ⟨1081581, by rfl⟩ : syracuseStep 2884217 = 2163163) B2163163
theorem B1922811 : Blo 1921435 1922811 := bstep (se 1 (by rfl) ⟨1442108, by rfl⟩ : syracuseStep 1922811 = 2884217) B2884217
theorem B13156085 : Blo 1921435 13156085 := bbase (se 5 (by rfl) ⟨616691, by rfl⟩ : syracuseStep 13156085 = 1233383) (by norm_num)
theorem B8770723 : Blo 1921435 8770723 := bstep (se 1 (by rfl) ⟨6578042, by rfl⟩ : syracuseStep 8770723 = 13156085) B13156085
theorem B46777189 : Blo 1921435 46777189 := bstep (se 4 (by rfl) ⟨4385361, by rfl⟩ : syracuseStep 46777189 = 8770723) B8770723
theorem B62369585 : Blo 1921435 62369585 := bstep (se 2 (by rfl) ⟨23388594, by rfl⟩ : syracuseStep 62369585 = 46777189) B46777189
theorem B41579723 : Blo 1921435 41579723 := bstep (se 1 (by rfl) ⟨31184792, by rfl⟩ : syracuseStep 41579723 = 62369585) B62369585
theorem B27719815 : Blo 1921435 27719815 := bstep (se 1 (by rfl) ⟨20789861, by rfl⟩ : syracuseStep 27719815 = 41579723) B41579723
theorem B36959753 : Blo 1921435 36959753 := bstep (se 2 (by rfl) ⟨13859907, by rfl⟩ : syracuseStep 36959753 = 27719815) B27719815
theorem B24639835 : Blo 1921435 24639835 := bstep (se 1 (by rfl) ⟨18479876, by rfl⟩ : syracuseStep 24639835 = 36959753) B36959753
theorem B32853113 : Blo 1921435 32853113 := bstep (se 2 (by rfl) ⟨12319917, by rfl⟩ : syracuseStep 32853113 = 24639835) B24639835
theorem B21902075 : Blo 1921435 21902075 := bstep (se 1 (by rfl) ⟨16426556, by rfl⟩ : syracuseStep 21902075 = 32853113) B32853113
theorem B14601383 : Blo 1921435 14601383 := bstep (se 1 (by rfl) ⟨10951037, by rfl⟩ : syracuseStep 14601383 = 21902075) B21902075
theorem B9734255 : Blo 1921435 9734255 := bstep (se 1 (by rfl) ⟨7300691, by rfl⟩ : syracuseStep 9734255 = 14601383) B14601383
theorem B6489503 : Blo 1921435 6489503 := bstep (se 1 (by rfl) ⟨4867127, by rfl⟩ : syracuseStep 6489503 = 9734255) B9734255
theorem B4326335 : Blo 1921435 4326335 := bstep (se 1 (by rfl) ⟨3244751, by rfl⟩ : syracuseStep 4326335 = 6489503) B6489503
theorem B2884223 : Blo 1921435 2884223 := bstep (se 1 (by rfl) ⟨2163167, by rfl⟩ : syracuseStep 2884223 = 4326335) B4326335
theorem B1922815 : Blo 1921435 1922815 := bstep (se 1 (by rfl) ⟨1442111, by rfl⟩ : syracuseStep 1922815 = 2884223) B2884223
theorem B2884229 : Blo 1921435 2884229 := bbase (se 4 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 2884229 = 540793) (by norm_num)
theorem B1922819 : Blo 1921435 1922819 := bstep (se 1 (by rfl) ⟨1442114, by rfl⟩ : syracuseStep 1922819 = 2884229) B2884229
theorem B3244765 : Blo 1921435 3244765 := bbase (se 3 (by rfl) ⟨608393, by rfl⟩ : syracuseStep 3244765 = 1216787) (by norm_num)
theorem B4326353 : Blo 1921435 4326353 := bstep (se 2 (by rfl) ⟨1622382, by rfl⟩ : syracuseStep 4326353 = 3244765) B3244765
theorem B2884235 : Blo 1921435 2884235 := bstep (se 1 (by rfl) ⟨2163176, by rfl⟩ : syracuseStep 2884235 = 4326353) B4326353
theorem B1922823 : Blo 1921435 1922823 := bstep (se 1 (by rfl) ⟨1442117, by rfl⟩ : syracuseStep 1922823 = 2884235) B2884235
theorem B2163181 : Blo 1921435 2163181 := bbase (se 3 (by rfl) ⟨405596, by rfl⟩ : syracuseStep 2163181 = 811193) (by norm_num)
theorem B2884241 : Blo 1921435 2884241 := bstep (se 2 (by rfl) ⟨1081590, by rfl⟩ : syracuseStep 2884241 = 2163181) B2163181
theorem B1922827 : Blo 1921435 1922827 := bstep (se 1 (by rfl) ⟨1442120, by rfl⟩ : syracuseStep 1922827 = 2884241) B2884241
theorem B6489557 : Blo 1921435 6489557 := bbase (se 7 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 6489557 = 152099) (by norm_num)
theorem B4326371 : Blo 1921435 4326371 := bstep (se 1 (by rfl) ⟨3244778, by rfl⟩ : syracuseStep 4326371 = 6489557) B6489557
theorem B2884247 : Blo 1921435 2884247 := bstep (se 1 (by rfl) ⟨2163185, by rfl⟩ : syracuseStep 2884247 = 4326371) B4326371
theorem B1922831 : Blo 1921435 1922831 := bstep (se 1 (by rfl) ⟨1442123, by rfl⟩ : syracuseStep 1922831 = 2884247) B2884247
theorem B2884253 : Blo 1921435 2884253 := bbase (se 3 (by rfl) ⟨540797, by rfl⟩ : syracuseStep 2884253 = 1081595) (by norm_num)
theorem B1922835 : Blo 1921435 1922835 := bstep (se 1 (by rfl) ⟨1442126, by rfl⟩ : syracuseStep 1922835 = 2884253) B2884253
theorem B4326389 : Blo 1921435 4326389 := bbase (se 5 (by rfl) ⟨202799, by rfl⟩ : syracuseStep 4326389 = 405599) (by norm_num)
theorem B2884259 : Blo 1921435 2884259 := bstep (se 1 (by rfl) ⟨2163194, by rfl⟩ : syracuseStep 2884259 = 4326389) B4326389
theorem B1922839 : Blo 1921435 1922839 := bstep (se 1 (by rfl) ⟨1442129, by rfl⟩ : syracuseStep 1922839 = 2884259) B2884259
theorem B8770853 : Blo 1921435 8770853 := bbase (se 4 (by rfl) ⟨822267, by rfl⟩ : syracuseStep 8770853 = 1644535) (by norm_num)
theorem B5847235 : Blo 1921435 5847235 := bstep (se 1 (by rfl) ⟨4385426, by rfl⟩ : syracuseStep 5847235 = 8770853) B8770853
theorem B31185253 : Blo 1921435 31185253 := bstep (se 4 (by rfl) ⟨2923617, by rfl⟩ : syracuseStep 31185253 = 5847235) B5847235
theorem B41580337 : Blo 1921435 41580337 := bstep (se 2 (by rfl) ⟨15592626, by rfl⟩ : syracuseStep 41580337 = 31185253) B31185253
theorem B55440449 : Blo 1921435 55440449 := bstep (se 2 (by rfl) ⟨20790168, by rfl⟩ : syracuseStep 55440449 = 41580337) B41580337
theorem B36960299 : Blo 1921435 36960299 := bstep (se 1 (by rfl) ⟨27720224, by rfl⟩ : syracuseStep 36960299 = 55440449) B55440449
theorem B24640199 : Blo 1921435 24640199 := bstep (se 1 (by rfl) ⟨18480149, by rfl⟩ : syracuseStep 24640199 = 36960299) B36960299
theorem B16426799 : Blo 1921435 16426799 := bstep (se 1 (by rfl) ⟨12320099, by rfl⟩ : syracuseStep 16426799 = 24640199) B24640199
theorem B10951199 : Blo 1921435 10951199 := bstep (se 1 (by rfl) ⟨8213399, by rfl⟩ : syracuseStep 10951199 = 16426799) B16426799
theorem B7300799 : Blo 1921435 7300799 := bstep (se 1 (by rfl) ⟨5475599, by rfl⟩ : syracuseStep 7300799 = 10951199) B10951199
theorem B4867199 : Blo 1921435 4867199 := bstep (se 1 (by rfl) ⟨3650399, by rfl⟩ : syracuseStep 4867199 = 7300799) B7300799
theorem B3244799 : Blo 1921435 3244799 := bstep (se 1 (by rfl) ⟨2433599, by rfl⟩ : syracuseStep 3244799 = 4867199) B4867199
theorem B2163199 : Blo 1921435 2163199 := bstep (se 1 (by rfl) ⟨1622399, by rfl⟩ : syracuseStep 2163199 = 3244799) B3244799
theorem B2884265 : Blo 1921435 2884265 := bstep (se 2 (by rfl) ⟨1081599, by rfl⟩ : syracuseStep 2884265 = 2163199) B2163199
theorem B1922843 : Blo 1921435 1922843 := bstep (se 1 (by rfl) ⟨1442132, by rfl⟩ : syracuseStep 1922843 = 2884265) B2884265
theorem B2737805 : Blo 1921435 2737805 := bbase (se 3 (by rfl) ⟨513338, by rfl⟩ : syracuseStep 2737805 = 1026677) (by norm_num)
theorem B7300813 : Blo 1921435 7300813 := bstep (se 3 (by rfl) ⟨1368902, by rfl⟩ : syracuseStep 7300813 = 2737805) B2737805
theorem B9734417 : Blo 1921435 9734417 := bstep (se 2 (by rfl) ⟨3650406, by rfl⟩ : syracuseStep 9734417 = 7300813) B7300813
theorem B6489611 : Blo 1921435 6489611 := bstep (se 1 (by rfl) ⟨4867208, by rfl⟩ : syracuseStep 6489611 = 9734417) B9734417
theorem B4326407 : Blo 1921435 4326407 := bstep (se 1 (by rfl) ⟨3244805, by rfl⟩ : syracuseStep 4326407 = 6489611) B6489611
theorem B2884271 : Blo 1921435 2884271 := bstep (se 1 (by rfl) ⟨2163203, by rfl⟩ : syracuseStep 2884271 = 4326407) B4326407
theorem B1922847 : Blo 1921435 1922847 := bstep (se 1 (by rfl) ⟨1442135, by rfl⟩ : syracuseStep 1922847 = 2884271) B2884271
theorem B2884277 : Blo 1921435 2884277 := bbase (se 5 (by rfl) ⟨135200, by rfl⟩ : syracuseStep 2884277 = 270401) (by norm_num)
theorem B1922851 : Blo 1921435 1922851 := bstep (se 1 (by rfl) ⟨1442138, by rfl⟩ : syracuseStep 1922851 = 2884277) B2884277
theorem B4867229 : Blo 1921435 4867229 := bbase (se 3 (by rfl) ⟨912605, by rfl⟩ : syracuseStep 4867229 = 1825211) (by norm_num)
theorem B3244819 : Blo 1921435 3244819 := bstep (se 1 (by rfl) ⟨2433614, by rfl⟩ : syracuseStep 3244819 = 4867229) B4867229
theorem B4326425 : Blo 1921435 4326425 := bstep (se 2 (by rfl) ⟨1622409, by rfl⟩ : syracuseStep 4326425 = 3244819) B3244819
theorem B2884283 : Blo 1921435 2884283 := bstep (se 1 (by rfl) ⟨2163212, by rfl⟩ : syracuseStep 2884283 = 4326425) B4326425
theorem B1922855 : Blo 1921435 1922855 := bstep (se 1 (by rfl) ⟨1442141, by rfl⟩ : syracuseStep 1922855 = 2884283) B2884283
theorem B2163217 : Blo 1921435 2163217 := bbase (se 2 (by rfl) ⟨811206, by rfl⟩ : syracuseStep 2163217 = 1622413) (by norm_num)
theorem B2884289 : Blo 1921435 2884289 := bstep (se 2 (by rfl) ⟨1081608, by rfl⟩ : syracuseStep 2884289 = 2163217) B2163217
theorem B1922859 : Blo 1921435 1922859 := bstep (se 1 (by rfl) ⟨1442144, by rfl⟩ : syracuseStep 1922859 = 2884289) B2884289
theorem B3650437 : Blo 1921435 3650437 := bbase (se 4 (by rfl) ⟨342228, by rfl⟩ : syracuseStep 3650437 = 684457) (by norm_num)
theorem B4867249 : Blo 1921435 4867249 := bstep (se 2 (by rfl) ⟨1825218, by rfl⟩ : syracuseStep 4867249 = 3650437) B3650437
theorem B6489665 : Blo 1921435 6489665 := bstep (se 2 (by rfl) ⟨2433624, by rfl⟩ : syracuseStep 6489665 = 4867249) B4867249
theorem B4326443 : Blo 1921435 4326443 := bstep (se 1 (by rfl) ⟨3244832, by rfl⟩ : syracuseStep 4326443 = 6489665) B6489665
theorem B2884295 : Blo 1921435 2884295 := bstep (se 1 (by rfl) ⟨2163221, by rfl⟩ : syracuseStep 2884295 = 4326443) B4326443
theorem B1922863 : Blo 1921435 1922863 := bstep (se 1 (by rfl) ⟨1442147, by rfl⟩ : syracuseStep 1922863 = 2884295) B2884295
theorem B2884301 : Blo 1921435 2884301 := bbase (se 3 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 2884301 = 1081613) (by norm_num)
theorem B1922867 : Blo 1921435 1922867 := bstep (se 1 (by rfl) ⟨1442150, by rfl⟩ : syracuseStep 1922867 = 2884301) B2884301
theorem B4326461 : Blo 1921435 4326461 := bbase (se 3 (by rfl) ⟨811211, by rfl⟩ : syracuseStep 4326461 = 1622423) (by norm_num)
theorem B2884307 : Blo 1921435 2884307 := bstep (se 1 (by rfl) ⟨2163230, by rfl⟩ : syracuseStep 2884307 = 4326461) B4326461
theorem B1922871 : Blo 1921435 1922871 := bstep (se 1 (by rfl) ⟨1442153, by rfl⟩ : syracuseStep 1922871 = 2884307) B2884307
theorem B3244853 : Blo 1921435 3244853 := bbase (se 5 (by rfl) ⟨152102, by rfl⟩ : syracuseStep 3244853 = 304205) (by norm_num)
theorem B2163235 : Blo 1921435 2163235 := bstep (se 1 (by rfl) ⟨1622426, by rfl⟩ : syracuseStep 2163235 = 3244853) B3244853
theorem B2884313 : Blo 1921435 2884313 := bstep (se 2 (by rfl) ⟨1081617, by rfl⟩ : syracuseStep 2884313 = 2163235) B2163235
theorem B1922875 : Blo 1921435 1922875 := bstep (se 1 (by rfl) ⟨1442156, by rfl⟩ : syracuseStep 1922875 = 2884313) B2884313
theorem B5475701 : Blo 1921435 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B14601869 : Blo 1921435 14601869 := bstep (se 3 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 14601869 = 5475701) B5475701
theorem B9734579 : Blo 1921435 9734579 := bstep (se 1 (by rfl) ⟨7300934, by rfl⟩ : syracuseStep 9734579 = 14601869) B14601869
theorem B6489719 : Blo 1921435 6489719 := bstep (se 1 (by rfl) ⟨4867289, by rfl⟩ : syracuseStep 6489719 = 9734579) B9734579
theorem B4326479 : Blo 1921435 4326479 := bstep (se 1 (by rfl) ⟨3244859, by rfl⟩ : syracuseStep 4326479 = 6489719) B6489719
theorem B2884319 : Blo 1921435 2884319 := bstep (se 1 (by rfl) ⟨2163239, by rfl⟩ : syracuseStep 2884319 = 4326479) B4326479
theorem B1922879 : Blo 1921435 1922879 := bstep (se 1 (by rfl) ⟨1442159, by rfl⟩ : syracuseStep 1922879 = 2884319) B2884319
theorem B2884325 : Blo 1921435 2884325 := bbase (se 4 (by rfl) ⟨270405, by rfl⟩ : syracuseStep 2884325 = 540811) (by norm_num)
theorem B1922883 : Blo 1921435 1922883 := bstep (se 1 (by rfl) ⟨1442162, by rfl⟩ : syracuseStep 1922883 = 2884325) B2884325
theorem B2053397 : Blo 1921435 2053397 := bbase (se 6 (by rfl) ⟨48126, by rfl⟩ : syracuseStep 2053397 = 96253) (by norm_num)
theorem B5475725 : Blo 1921435 5475725 := bstep (se 3 (by rfl) ⟨1026698, by rfl⟩ : syracuseStep 5475725 = 2053397) B2053397
theorem B3650483 : Blo 1921435 3650483 := bstep (se 1 (by rfl) ⟨2737862, by rfl⟩ : syracuseStep 3650483 = 5475725) B5475725
theorem B2433655 : Blo 1921435 2433655 := bstep (se 1 (by rfl) ⟨1825241, by rfl⟩ : syracuseStep 2433655 = 3650483) B3650483
theorem B3244873 : Blo 1921435 3244873 := bstep (se 2 (by rfl) ⟨1216827, by rfl⟩ : syracuseStep 3244873 = 2433655) B2433655
theorem B4326497 : Blo 1921435 4326497 := bstep (se 2 (by rfl) ⟨1622436, by rfl⟩ : syracuseStep 4326497 = 3244873) B3244873
theorem B2884331 : Blo 1921435 2884331 := bstep (se 1 (by rfl) ⟨2163248, by rfl⟩ : syracuseStep 2884331 = 4326497) B4326497
theorem B1922887 : Blo 1921435 1922887 := bstep (se 1 (by rfl) ⟨1442165, by rfl⟩ : syracuseStep 1922887 = 2884331) B2884331
theorem B2163253 : Blo 1921435 2163253 := bbase (se 5 (by rfl) ⟨101402, by rfl⟩ : syracuseStep 2163253 = 202805) (by norm_num)
theorem B2884337 : Blo 1921435 2884337 := bstep (se 2 (by rfl) ⟨1081626, by rfl⟩ : syracuseStep 2884337 = 2163253) B2163253
theorem B1922891 : Blo 1921435 1922891 := bstep (se 1 (by rfl) ⟨1442168, by rfl⟩ : syracuseStep 1922891 = 2884337) B2884337
theorem B2433665 : Blo 1921435 2433665 := bbase (se 2 (by rfl) ⟨912624, by rfl⟩ : syracuseStep 2433665 = 1825249) (by norm_num)
theorem B6489773 : Blo 1921435 6489773 := bstep (se 3 (by rfl) ⟨1216832, by rfl⟩ : syracuseStep 6489773 = 2433665) B2433665
theorem B4326515 : Blo 1921435 4326515 := bstep (se 1 (by rfl) ⟨3244886, by rfl⟩ : syracuseStep 4326515 = 6489773) B6489773
theorem B2884343 : Blo 1921435 2884343 := bstep (se 1 (by rfl) ⟨2163257, by rfl⟩ : syracuseStep 2884343 = 4326515) B4326515
theorem B1922895 : Blo 1921435 1922895 := bstep (se 1 (by rfl) ⟨1442171, by rfl⟩ : syracuseStep 1922895 = 2884343) B2884343
theorem B2884349 : Blo 1921435 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B1922899 : Blo 1921435 1922899 := bstep (se 1 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 1922899 = 2884349) B2884349
theorem B4326533 : Blo 1921435 4326533 := bbase (se 4 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 4326533 = 811225) (by norm_num)
theorem B2884355 : Blo 1921435 2884355 := bstep (se 1 (by rfl) ⟨2163266, by rfl⟩ : syracuseStep 2884355 = 4326533) B4326533
theorem B1922903 : Blo 1921435 1922903 := bstep (se 1 (by rfl) ⟨1442177, by rfl⟩ : syracuseStep 1922903 = 2884355) B2884355
theorem B4106837 : Blo 1921435 4106837 := bbase (se 8 (by rfl) ⟨24063, by rfl⟩ : syracuseStep 4106837 = 48127) (by norm_num)
theorem B2737891 : Blo 1921435 2737891 := bstep (se 1 (by rfl) ⟨2053418, by rfl⟩ : syracuseStep 2737891 = 4106837) B4106837
theorem B3650521 : Blo 1921435 3650521 := bstep (se 2 (by rfl) ⟨1368945, by rfl⟩ : syracuseStep 3650521 = 2737891) B2737891
theorem B4867361 : Blo 1921435 4867361 := bstep (se 2 (by rfl) ⟨1825260, by rfl⟩ : syracuseStep 4867361 = 3650521) B3650521
theorem B3244907 : Blo 1921435 3244907 := bstep (se 1 (by rfl) ⟨2433680, by rfl⟩ : syracuseStep 3244907 = 4867361) B4867361
theorem B2163271 : Blo 1921435 2163271 := bstep (se 1 (by rfl) ⟨1622453, by rfl⟩ : syracuseStep 2163271 = 3244907) B3244907
theorem B2884361 : Blo 1921435 2884361 := bstep (se 2 (by rfl) ⟨1081635, by rfl⟩ : syracuseStep 2884361 = 2163271) B2163271
theorem B1922907 : Blo 1921435 1922907 := bstep (se 1 (by rfl) ⟨1442180, by rfl⟩ : syracuseStep 1922907 = 2884361) B2884361
theorem B9734741 : Blo 1921435 9734741 := bbase (se 8 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 9734741 = 114079) (by norm_num)
theorem B6489827 : Blo 1921435 6489827 := bstep (se 1 (by rfl) ⟨4867370, by rfl⟩ : syracuseStep 6489827 = 9734741) B9734741
theorem B4326551 : Blo 1921435 4326551 := bstep (se 1 (by rfl) ⟨3244913, by rfl⟩ : syracuseStep 4326551 = 6489827) B6489827
theorem B2884367 : Blo 1921435 2884367 := bstep (se 1 (by rfl) ⟨2163275, by rfl⟩ : syracuseStep 2884367 = 4326551) B4326551
theorem B1922911 : Blo 1921435 1922911 := bstep (se 1 (by rfl) ⟨1442183, by rfl⟩ : syracuseStep 1922911 = 2884367) B2884367
theorem B2884373 : Blo 1921435 2884373 := bbase (se 6 (by rfl) ⟨67602, by rfl⟩ : syracuseStep 2884373 = 135205) (by norm_num)
theorem B1922915 : Blo 1921435 1922915 := bstep (se 1 (by rfl) ⟨1442186, by rfl⟩ : syracuseStep 1922915 = 2884373) B2884373
theorem B2923733 : Blo 1921435 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B7796621 : Blo 1921435 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B20790989 : Blo 1921435 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B13860659 : Blo 1921435 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B36961757 : Blo 1921435 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B24641171 : Blo 1921435 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B16427447 : Blo 1921435 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B10951631 : Blo 1921435 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B7301087 : Blo 1921435 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B4867391 : Blo 1921435 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B3244927 : Blo 1921435 3244927 := bstep (se 1 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 3244927 = 4867391) B4867391
theorem B4326569 : Blo 1921435 4326569 := bstep (se 2 (by rfl) ⟨1622463, by rfl⟩ : syracuseStep 4326569 = 3244927) B3244927
theorem B2884379 : Blo 1921435 2884379 := bstep (se 1 (by rfl) ⟨2163284, by rfl⟩ : syracuseStep 2884379 = 4326569) B4326569
theorem B1922919 : Blo 1921435 1922919 := bstep (se 1 (by rfl) ⟨1442189, by rfl⟩ : syracuseStep 1922919 = 2884379) B2884379
theorem B2163289 : Blo 1921435 2163289 := bbase (se 2 (by rfl) ⟨811233, by rfl⟩ : syracuseStep 2163289 = 1622467) (by norm_num)
theorem B2884385 : Blo 1921435 2884385 := bstep (se 2 (by rfl) ⟨1081644, by rfl⟩ : syracuseStep 2884385 = 2163289) B2163289
theorem B1922923 : Blo 1921435 1922923 := bstep (se 1 (by rfl) ⟨1442192, by rfl⟩ : syracuseStep 1922923 = 2884385) B2884385
theorem B7217909 : Blo 1921435 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B4811939 : Blo 1921435 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B3207959 : Blo 1921435 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B136872917 : Blo 1921435 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B91248611 : Blo 1921435 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B243329629 : Blo 1921435 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B324439505 : Blo 1921435 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B216293003 : Blo 1921435 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B144195335 : Blo 1921435 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B96130223 : Blo 1921435 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B64086815 : Blo 1921435 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B170898173 : Blo 1921435 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B113932115 : Blo 1921435 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B75954743 : Blo 1921435 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B50636495 : Blo 1921435 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B33757663 : Blo 1921435 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B45010217 : Blo 1921435 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B30006811 : Blo 1921435 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B40009081 : Blo 1921435 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B53345441 : Blo 1921435 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B35563627 : Blo 1921435 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B47418169 : Blo 1921435 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B63224225 : Blo 1921435 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B42149483 : Blo 1921435 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B28099655 : Blo 1921435 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B18733103 : Blo 1921435 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B12488735 : Blo 1921435 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B8325823 : Blo 1921435 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B11101097 : Blo 1921435 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B29602925 : Blo 1921435 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B19735283 : Blo 1921435 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B52627421 : Blo 1921435 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B35084947 : Blo 1921435 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B46779929 : Blo 1921435 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B31186619 : Blo 1921435 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B20791079 : Blo 1921435 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B13860719 : Blo 1921435 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B9240479 : Blo 1921435 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B6160319 : Blo 1921435 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B4106879 : Blo 1921435 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B2737919 : Blo 1921435 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B7301117 : Blo 1921435 7301117 := bstep (se 3 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 7301117 = 2737919) B2737919
theorem B4867411 : Blo 1921435 4867411 := bstep (se 1 (by rfl) ⟨3650558, by rfl⟩ : syracuseStep 4867411 = 7301117) B7301117
theorem B6489881 : Blo 1921435 6489881 := bstep (se 2 (by rfl) ⟨2433705, by rfl⟩ : syracuseStep 6489881 = 4867411) B4867411
theorem B4326587 : Blo 1921435 4326587 := bstep (se 1 (by rfl) ⟨3244940, by rfl⟩ : syracuseStep 4326587 = 6489881) B6489881
theorem B2884391 : Blo 1921435 2884391 := bstep (se 1 (by rfl) ⟨2163293, by rfl⟩ : syracuseStep 2884391 = 4326587) B4326587
theorem B1922927 : Blo 1921435 1922927 := bstep (se 1 (by rfl) ⟨1442195, by rfl⟩ : syracuseStep 1922927 = 2884391) B2884391
theorem B2884397 : Blo 1921435 2884397 := bbase (se 3 (by rfl) ⟨540824, by rfl⟩ : syracuseStep 2884397 = 1081649) (by norm_num)
theorem B1922931 : Blo 1921435 1922931 := bstep (se 1 (by rfl) ⟨1442198, by rfl⟩ : syracuseStep 1922931 = 2884397) B2884397
theorem B4326605 : Blo 1921435 4326605 := bbase (se 3 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 4326605 = 1622477) (by norm_num)
theorem B2884403 : Blo 1921435 2884403 := bstep (se 1 (by rfl) ⟨2163302, by rfl⟩ : syracuseStep 2884403 = 4326605) B4326605
theorem B1922935 : Blo 1921435 1922935 := bstep (se 1 (by rfl) ⟨1442201, by rfl⟩ : syracuseStep 1922935 = 2884403) B2884403
theorem B2433721 : Blo 1921435 2433721 := bbase (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) (by norm_num)
theorem B3244961 : Blo 1921435 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2163307 : Blo 1921435 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B2884409 : Blo 1921435 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B1922939 : Blo 1921435 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B4620277 : Blo 1921435 4620277 := bbase (se 5 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 4620277 = 433151) (by norm_num)
theorem B6160369 : Blo 1921435 6160369 := bstep (se 2 (by rfl) ⟨2310138, by rfl⟩ : syracuseStep 6160369 = 4620277) B4620277
theorem B8213825 : Blo 1921435 8213825 := bstep (se 2 (by rfl) ⟨3080184, by rfl⟩ : syracuseStep 8213825 = 6160369) B6160369
theorem B21903533 : Blo 1921435 21903533 := bstep (se 3 (by rfl) ⟨4106912, by rfl⟩ : syracuseStep 21903533 = 8213825) B8213825
theorem B14602355 : Blo 1921435 14602355 := bstep (se 1 (by rfl) ⟨10951766, by rfl⟩ : syracuseStep 14602355 = 21903533) B21903533
theorem B9734903 : Blo 1921435 9734903 := bstep (se 1 (by rfl) ⟨7301177, by rfl⟩ : syracuseStep 9734903 = 14602355) B14602355
theorem B6489935 : Blo 1921435 6489935 := bstep (se 1 (by rfl) ⟨4867451, by rfl⟩ : syracuseStep 6489935 = 9734903) B9734903
theorem B4326623 : Blo 1921435 4326623 := bstep (se 1 (by rfl) ⟨3244967, by rfl⟩ : syracuseStep 4326623 = 6489935) B6489935
theorem B2884415 : Blo 1921435 2884415 := bstep (se 1 (by rfl) ⟨2163311, by rfl⟩ : syracuseStep 2884415 = 4326623) B4326623
theorem B1922943 : Blo 1921435 1922943 := bstep (se 1 (by rfl) ⟨1442207, by rfl⟩ : syracuseStep 1922943 = 2884415) B2884415
theorem B2884421 : Blo 1921435 2884421 := bbase (se 4 (by rfl) ⟨270414, by rfl⟩ : syracuseStep 2884421 = 540829) (by norm_num)
theorem B1922947 : Blo 1921435 1922947 := bstep (se 1 (by rfl) ⟨1442210, by rfl⟩ : syracuseStep 1922947 = 2884421) B2884421
theorem B3244981 : Blo 1921435 3244981 := bbase (se 5 (by rfl) ⟨152108, by rfl⟩ : syracuseStep 3244981 = 304217) (by norm_num)
theorem B4326641 : Blo 1921435 4326641 := bstep (se 2 (by rfl) ⟨1622490, by rfl⟩ : syracuseStep 4326641 = 3244981) B3244981
theorem B2884427 : Blo 1921435 2884427 := bstep (se 1 (by rfl) ⟨2163320, by rfl⟩ : syracuseStep 2884427 = 4326641) B4326641
theorem B1922951 : Blo 1921435 1922951 := bstep (se 1 (by rfl) ⟨1442213, by rfl⟩ : syracuseStep 1922951 = 2884427) B2884427
theorem B2163325 : Blo 1921435 2163325 := bbase (se 3 (by rfl) ⟨405623, by rfl⟩ : syracuseStep 2163325 = 811247) (by norm_num)
theorem B2884433 : Blo 1921435 2884433 := bstep (se 2 (by rfl) ⟨1081662, by rfl⟩ : syracuseStep 2884433 = 2163325) B2163325
theorem B1922955 : Blo 1921435 1922955 := bstep (se 1 (by rfl) ⟨1442216, by rfl⟩ : syracuseStep 1922955 = 2884433) B2884433
theorem B6489989 : Blo 1921435 6489989 := bbase (se 4 (by rfl) ⟨608436, by rfl⟩ : syracuseStep 6489989 = 1216873) (by norm_num)
theorem B4326659 : Blo 1921435 4326659 := bstep (se 1 (by rfl) ⟨3244994, by rfl⟩ : syracuseStep 4326659 = 6489989) B6489989
theorem B2884439 : Blo 1921435 2884439 := bstep (se 1 (by rfl) ⟨2163329, by rfl⟩ : syracuseStep 2884439 = 4326659) B4326659
theorem B1922959 : Blo 1921435 1922959 := bstep (se 1 (by rfl) ⟨1442219, by rfl⟩ : syracuseStep 1922959 = 2884439) B2884439
theorem B2884445 : Blo 1921435 2884445 := bbase (se 3 (by rfl) ⟨540833, by rfl⟩ : syracuseStep 2884445 = 1081667) (by norm_num)
theorem B1922963 : Blo 1921435 1922963 := bstep (se 1 (by rfl) ⟨1442222, by rfl⟩ : syracuseStep 1922963 = 2884445) B2884445
theorem B4326677 : Blo 1921435 4326677 := bbase (se 6 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 4326677 = 202813) (by norm_num)
theorem B2884451 : Blo 1921435 2884451 := bstep (se 1 (by rfl) ⟨2163338, by rfl⟩ : syracuseStep 2884451 = 4326677) B4326677
theorem B1922967 : Blo 1921435 1922967 := bstep (se 1 (by rfl) ⟨1442225, by rfl⟩ : syracuseStep 1922967 = 2884451) B2884451
theorem B7301285 : Blo 1921435 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B4867523 : Blo 1921435 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B3245015 : Blo 1921435 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B2163343 : Blo 1921435 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B2884457 : Blo 1921435 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B1922971 : Blo 1921435 1922971 := bstep (se 1 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 1922971 = 2884457) B2884457
theorem B4106981 : Blo 1921435 4106981 := bbase (se 4 (by rfl) ⟨385029, by rfl⟩ : syracuseStep 4106981 = 770059) (by norm_num)
theorem B10951949 : Blo 1921435 10951949 := bstep (se 3 (by rfl) ⟨2053490, by rfl⟩ : syracuseStep 10951949 = 4106981) B4106981
theorem B7301299 : Blo 1921435 7301299 := bstep (se 1 (by rfl) ⟨5475974, by rfl⟩ : syracuseStep 7301299 = 10951949) B10951949
theorem B9735065 : Blo 1921435 9735065 := bstep (se 2 (by rfl) ⟨3650649, by rfl⟩ : syracuseStep 9735065 = 7301299) B7301299
theorem B6490043 : Blo 1921435 6490043 := bstep (se 1 (by rfl) ⟨4867532, by rfl⟩ : syracuseStep 6490043 = 9735065) B9735065
theorem B4326695 : Blo 1921435 4326695 := bstep (se 1 (by rfl) ⟨3245021, by rfl⟩ : syracuseStep 4326695 = 6490043) B6490043
theorem B2884463 : Blo 1921435 2884463 := bstep (se 1 (by rfl) ⟨2163347, by rfl⟩ : syracuseStep 2884463 = 4326695) B4326695
theorem B1922975 : Blo 1921435 1922975 := bstep (se 1 (by rfl) ⟨1442231, by rfl⟩ : syracuseStep 1922975 = 2884463) B2884463
theorem B2884469 : Blo 1921435 2884469 := bbase (se 5 (by rfl) ⟨135209, by rfl⟩ : syracuseStep 2884469 = 270419) (by norm_num)
theorem B1922979 : Blo 1921435 1922979 := bstep (se 1 (by rfl) ⟨1442234, by rfl⟩ : syracuseStep 1922979 = 2884469) B2884469
theorem B1949221 : Blo 1921435 1949221 := bbase (se 4 (by rfl) ⟨182739, by rfl⟩ : syracuseStep 1949221 = 365479) (by norm_num)
theorem B2598961 : Blo 1921435 2598961 := bstep (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) B1949221
theorem B3465281 : Blo 1921435 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B9240749 : Blo 1921435 9240749 := bstep (se 3 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 9240749 = 3465281) B3465281
theorem B6160499 : Blo 1921435 6160499 := bstep (se 1 (by rfl) ⟨4620374, by rfl⟩ : syracuseStep 6160499 = 9240749) B9240749
theorem B4106999 : Blo 1921435 4106999 := bstep (se 1 (by rfl) ⟨3080249, by rfl⟩ : syracuseStep 4106999 = 6160499) B6160499
theorem B2737999 : Blo 1921435 2737999 := bstep (se 1 (by rfl) ⟨2053499, by rfl⟩ : syracuseStep 2737999 = 4106999) B4106999
theorem B3650665 : Blo 1921435 3650665 := bstep (se 2 (by rfl) ⟨1368999, by rfl⟩ : syracuseStep 3650665 = 2737999) B2737999
theorem B4867553 : Blo 1921435 4867553 := bstep (se 2 (by rfl) ⟨1825332, by rfl⟩ : syracuseStep 4867553 = 3650665) B3650665
theorem B3245035 : Blo 1921435 3245035 := bstep (se 1 (by rfl) ⟨2433776, by rfl⟩ : syracuseStep 3245035 = 4867553) B4867553
theorem B4326713 : Blo 1921435 4326713 := bstep (se 2 (by rfl) ⟨1622517, by rfl⟩ : syracuseStep 4326713 = 3245035) B3245035
theorem B2884475 : Blo 1921435 2884475 := bstep (se 1 (by rfl) ⟨2163356, by rfl⟩ : syracuseStep 2884475 = 4326713) B4326713
theorem B1922983 : Blo 1921435 1922983 := bstep (se 1 (by rfl) ⟨1442237, by rfl⟩ : syracuseStep 1922983 = 2884475) B2884475
theorem B2163361 : Blo 1921435 2163361 := bbase (se 2 (by rfl) ⟨811260, by rfl⟩ : syracuseStep 2163361 = 1622521) (by norm_num)
theorem B2884481 : Blo 1921435 2884481 := bstep (se 2 (by rfl) ⟨1081680, by rfl⟩ : syracuseStep 2884481 = 2163361) B2163361
theorem B1922987 : Blo 1921435 1922987 := bstep (se 1 (by rfl) ⟨1442240, by rfl⟩ : syracuseStep 1922987 = 2884481) B2884481
theorem B4867573 : Blo 1921435 4867573 := bbase (se 5 (by rfl) ⟨228167, by rfl⟩ : syracuseStep 4867573 = 456335) (by norm_num)
theorem B6490097 : Blo 1921435 6490097 := bstep (se 2 (by rfl) ⟨2433786, by rfl⟩ : syracuseStep 6490097 = 4867573) B4867573
theorem B4326731 : Blo 1921435 4326731 := bstep (se 1 (by rfl) ⟨3245048, by rfl⟩ : syracuseStep 4326731 = 6490097) B6490097
theorem B2884487 : Blo 1921435 2884487 := bstep (se 1 (by rfl) ⟨2163365, by rfl⟩ : syracuseStep 2884487 = 4326731) B4326731
theorem B1922991 : Blo 1921435 1922991 := bstep (se 1 (by rfl) ⟨1442243, by rfl⟩ : syracuseStep 1922991 = 2884487) B2884487
theorem B2884493 : Blo 1921435 2884493 := bbase (se 3 (by rfl) ⟨540842, by rfl⟩ : syracuseStep 2884493 = 1081685) (by norm_num)
theorem B1922995 : Blo 1921435 1922995 := bstep (se 1 (by rfl) ⟨1442246, by rfl⟩ : syracuseStep 1922995 = 2884493) B2884493
theorem B4326749 : Blo 1921435 4326749 := bbase (se 3 (by rfl) ⟨811265, by rfl⟩ : syracuseStep 4326749 = 1622531) (by norm_num)
theorem B2884499 : Blo 1921435 2884499 := bstep (se 1 (by rfl) ⟨2163374, by rfl⟩ : syracuseStep 2884499 = 4326749) B4326749
theorem B1922999 : Blo 1921435 1922999 := bstep (se 1 (by rfl) ⟨1442249, by rfl⟩ : syracuseStep 1922999 = 2884499) B2884499
theorem B3245069 : Blo 1921435 3245069 := bbase (se 3 (by rfl) ⟨608450, by rfl⟩ : syracuseStep 3245069 = 1216901) (by norm_num)
theorem B2163379 : Blo 1921435 2163379 := bstep (se 1 (by rfl) ⟨1622534, by rfl⟩ : syracuseStep 2163379 = 3245069) B3245069
theorem B2884505 : Blo 1921435 2884505 := bstep (se 2 (by rfl) ⟨1081689, by rfl⟩ : syracuseStep 2884505 = 2163379) B2163379
theorem B1923003 : Blo 1921435 1923003 := bstep (se 1 (by rfl) ⟨1442252, by rfl⟩ : syracuseStep 1923003 = 2884505) B2884505
theorem B3512605 : Blo 1921435 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B4683473 : Blo 1921435 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B3122315 : Blo 1921435 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2081543 : Blo 1921435 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B5550781 : Blo 1921435 5550781 := bstep (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) B2081543
theorem B7401041 : Blo 1921435 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B4934027 : Blo 1921435 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B3289351 : Blo 1921435 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B4385801 : Blo 1921435 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B2923867 : Blo 1921435 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B15593957 : Blo 1921435 15593957 := bstep (se 4 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 15593957 = 2923867) B2923867
theorem B10395971 : Blo 1921435 10395971 := bstep (se 1 (by rfl) ⟨7796978, by rfl⟩ : syracuseStep 10395971 = 15593957) B15593957
theorem B6930647 : Blo 1921435 6930647 := bstep (se 1 (by rfl) ⟨5197985, by rfl⟩ : syracuseStep 6930647 = 10395971) B10395971
theorem B4620431 : Blo 1921435 4620431 := bstep (se 1 (by rfl) ⟨3465323, by rfl⟩ : syracuseStep 4620431 = 6930647) B6930647
theorem B3080287 : Blo 1921435 3080287 := bstep (se 1 (by rfl) ⟨2310215, by rfl⟩ : syracuseStep 3080287 = 4620431) B4620431
theorem B16428197 : Blo 1921435 16428197 := bstep (se 4 (by rfl) ⟨1540143, by rfl⟩ : syracuseStep 16428197 = 3080287) B3080287
theorem B10952131 : Blo 1921435 10952131 := bstep (se 1 (by rfl) ⟨8214098, by rfl⟩ : syracuseStep 10952131 = 16428197) B16428197
theorem B14602841 : Blo 1921435 14602841 := bstep (se 2 (by rfl) ⟨5476065, by rfl⟩ : syracuseStep 14602841 = 10952131) B10952131
theorem B9735227 : Blo 1921435 9735227 := bstep (se 1 (by rfl) ⟨7301420, by rfl⟩ : syracuseStep 9735227 = 14602841) B14602841
theorem B6490151 : Blo 1921435 6490151 := bstep (se 1 (by rfl) ⟨4867613, by rfl⟩ : syracuseStep 6490151 = 9735227) B9735227
theorem B4326767 : Blo 1921435 4326767 := bstep (se 1 (by rfl) ⟨3245075, by rfl⟩ : syracuseStep 4326767 = 6490151) B6490151
theorem B2884511 : Blo 1921435 2884511 := bstep (se 1 (by rfl) ⟨2163383, by rfl⟩ : syracuseStep 2884511 = 4326767) B4326767
theorem B1923007 : Blo 1921435 1923007 := bstep (se 1 (by rfl) ⟨1442255, by rfl⟩ : syracuseStep 1923007 = 2884511) B2884511
theorem B2884517 : Blo 1921435 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B1923011 : Blo 1921435 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B2433817 : Blo 1921435 2433817 := bbase (se 2 (by rfl) ⟨912681, by rfl⟩ : syracuseStep 2433817 = 1825363) (by norm_num)
theorem B3245089 : Blo 1921435 3245089 := bstep (se 2 (by rfl) ⟨1216908, by rfl⟩ : syracuseStep 3245089 = 2433817) B2433817
theorem B4326785 : Blo 1921435 4326785 := bstep (se 2 (by rfl) ⟨1622544, by rfl⟩ : syracuseStep 4326785 = 3245089) B3245089
theorem B2884523 : Blo 1921435 2884523 := bstep (se 1 (by rfl) ⟨2163392, by rfl⟩ : syracuseStep 2884523 = 4326785) B4326785
theorem B1923015 : Blo 1921435 1923015 := bstep (se 1 (by rfl) ⟨1442261, by rfl⟩ : syracuseStep 1923015 = 2884523) B2884523
theorem B2163397 : Blo 1921435 2163397 := bbase (se 4 (by rfl) ⟨202818, by rfl⟩ : syracuseStep 2163397 = 405637) (by norm_num)
theorem B2884529 : Blo 1921435 2884529 := bstep (se 2 (by rfl) ⟨1081698, by rfl⟩ : syracuseStep 2884529 = 2163397) B2163397
theorem B1923019 : Blo 1921435 1923019 := bstep (se 1 (by rfl) ⟨1442264, by rfl⟩ : syracuseStep 1923019 = 2884529) B2884529
theorem B3650741 : Blo 1921435 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B2433827 : Blo 1921435 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B6490205 : Blo 1921435 6490205 := bstep (se 3 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 6490205 = 2433827) B2433827
theorem B4326803 : Blo 1921435 4326803 := bstep (se 1 (by rfl) ⟨3245102, by rfl⟩ : syracuseStep 4326803 = 6490205) B6490205
theorem B2884535 : Blo 1921435 2884535 := bstep (se 1 (by rfl) ⟨2163401, by rfl⟩ : syracuseStep 2884535 = 4326803) B4326803
theorem B1923023 : Blo 1921435 1923023 := bstep (se 1 (by rfl) ⟨1442267, by rfl⟩ : syracuseStep 1923023 = 2884535) B2884535
theorem B2884541 : Blo 1921435 2884541 := bbase (se 3 (by rfl) ⟨540851, by rfl⟩ : syracuseStep 2884541 = 1081703) (by norm_num)
theorem B1923027 : Blo 1921435 1923027 := bstep (se 1 (by rfl) ⟨1442270, by rfl⟩ : syracuseStep 1923027 = 2884541) B2884541
theorem B4326821 : Blo 1921435 4326821 := bbase (se 4 (by rfl) ⟨405639, by rfl⟩ : syracuseStep 4326821 = 811279) (by norm_num)
theorem B2884547 : Blo 1921435 2884547 := bstep (se 1 (by rfl) ⟨2163410, by rfl⟩ : syracuseStep 2884547 = 4326821) B4326821
theorem B1923031 : Blo 1921435 1923031 := bstep (se 1 (by rfl) ⟨1442273, by rfl⟩ : syracuseStep 1923031 = 2884547) B2884547
theorem B4867685 : Blo 1921435 4867685 := bbase (se 4 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 4867685 = 912691) (by norm_num)
theorem B3245123 : Blo 1921435 3245123 := bstep (se 1 (by rfl) ⟨2433842, by rfl⟩ : syracuseStep 3245123 = 4867685) B4867685
theorem B2163415 : Blo 1921435 2163415 := bstep (se 1 (by rfl) ⟨1622561, by rfl⟩ : syracuseStep 2163415 = 3245123) B3245123
theorem B2884553 : Blo 1921435 2884553 := bstep (se 2 (by rfl) ⟨1081707, by rfl⟩ : syracuseStep 2884553 = 2163415) B2163415
theorem B1923035 : Blo 1921435 1923035 := bstep (se 1 (by rfl) ⟨1442276, by rfl⟩ : syracuseStep 1923035 = 2884553) B2884553
theorem B4620509 : Blo 1921435 4620509 := bbase (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) (by norm_num)
theorem B3080339 : Blo 1921435 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B2053559 : Blo 1921435 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B5476157 : Blo 1921435 5476157 := bstep (se 3 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 5476157 = 2053559) B2053559
theorem B3650771 : Blo 1921435 3650771 := bstep (se 1 (by rfl) ⟨2738078, by rfl⟩ : syracuseStep 3650771 = 5476157) B5476157
theorem B9735389 : Blo 1921435 9735389 := bstep (se 3 (by rfl) ⟨1825385, by rfl⟩ : syracuseStep 9735389 = 3650771) B3650771
theorem B6490259 : Blo 1921435 6490259 := bstep (se 1 (by rfl) ⟨4867694, by rfl⟩ : syracuseStep 6490259 = 9735389) B9735389
theorem B4326839 : Blo 1921435 4326839 := bstep (se 1 (by rfl) ⟨3245129, by rfl⟩ : syracuseStep 4326839 = 6490259) B6490259
theorem B2884559 : Blo 1921435 2884559 := bstep (se 1 (by rfl) ⟨2163419, by rfl⟩ : syracuseStep 2884559 = 4326839) B4326839
theorem B1923039 : Blo 1921435 1923039 := bstep (se 1 (by rfl) ⟨1442279, by rfl⟩ : syracuseStep 1923039 = 2884559) B2884559
theorem B2884565 : Blo 1921435 2884565 := bbase (se 7 (by rfl) ⟨33803, by rfl⟩ : syracuseStep 2884565 = 67607) (by norm_num)
theorem B1923043 : Blo 1921435 1923043 := bstep (se 1 (by rfl) ⟨1442282, by rfl⟩ : syracuseStep 1923043 = 2884565) B2884565
theorem B7301573 : Blo 1921435 7301573 := bbase (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) (by norm_num)
theorem B4867715 : Blo 1921435 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B3245143 : Blo 1921435 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B4326857 : Blo 1921435 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B2884571 : Blo 1921435 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B1923047 : Blo 1921435 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B2163433 : Blo 1921435 2163433 := bbase (se 2 (by rfl) ⟨811287, by rfl⟩ : syracuseStep 2163433 = 1622575) (by norm_num)
theorem B2884577 : Blo 1921435 2884577 := bstep (se 2 (by rfl) ⟨1081716, by rfl⟩ : syracuseStep 2884577 = 2163433) B2163433
theorem B1923051 : Blo 1921435 1923051 := bstep (se 1 (by rfl) ⟨1442288, by rfl⟩ : syracuseStep 1923051 = 2884577) B2884577
theorem B10952405 : Blo 1921435 10952405 := bbase (se 7 (by rfl) ⟨128348, by rfl⟩ : syracuseStep 10952405 = 256697) (by norm_num)
theorem B7301603 : Blo 1921435 7301603 := bstep (se 1 (by rfl) ⟨5476202, by rfl⟩ : syracuseStep 7301603 = 10952405) B10952405
theorem B4867735 : Blo 1921435 4867735 := bstep (se 1 (by rfl) ⟨3650801, by rfl⟩ : syracuseStep 4867735 = 7301603) B7301603
theorem B6490313 : Blo 1921435 6490313 := bstep (se 2 (by rfl) ⟨2433867, by rfl⟩ : syracuseStep 6490313 = 4867735) B4867735
theorem B4326875 : Blo 1921435 4326875 := bstep (se 1 (by rfl) ⟨3245156, by rfl⟩ : syracuseStep 4326875 = 6490313) B6490313
theorem B2884583 : Blo 1921435 2884583 := bstep (se 1 (by rfl) ⟨2163437, by rfl⟩ : syracuseStep 2884583 = 4326875) B4326875
theorem B1923055 : Blo 1921435 1923055 := bstep (se 1 (by rfl) ⟨1442291, by rfl⟩ : syracuseStep 1923055 = 2884583) B2884583
theorem B2884589 : Blo 1921435 2884589 := bbase (se 3 (by rfl) ⟨540860, by rfl⟩ : syracuseStep 2884589 = 1081721) (by norm_num)
theorem B1923059 : Blo 1921435 1923059 := bstep (se 1 (by rfl) ⟨1442294, by rfl⟩ : syracuseStep 1923059 = 2884589) B2884589
theorem B4326893 : Blo 1921435 4326893 := bbase (se 3 (by rfl) ⟨811292, by rfl⟩ : syracuseStep 4326893 = 1622585) (by norm_num)
theorem B2884595 : Blo 1921435 2884595 := bstep (se 1 (by rfl) ⟨2163446, by rfl⟩ : syracuseStep 2884595 = 4326893) B4326893
theorem B1923063 : Blo 1921435 1923063 := bstep (se 1 (by rfl) ⟨1442297, by rfl⟩ : syracuseStep 1923063 = 2884595) B2884595
theorem B3898613 : Blo 1921435 3898613 := bbase (se 5 (by rfl) ⟨182747, by rfl⟩ : syracuseStep 3898613 = 365495) (by norm_num)
theorem B2599075 : Blo 1921435 2599075 := bstep (se 1 (by rfl) ⟨1949306, by rfl⟩ : syracuseStep 2599075 = 3898613) B3898613
theorem B3465433 : Blo 1921435 3465433 := bstep (se 2 (by rfl) ⟨1299537, by rfl⟩ : syracuseStep 3465433 = 2599075) B2599075
theorem B4620577 : Blo 1921435 4620577 := bstep (se 2 (by rfl) ⟨1732716, by rfl⟩ : syracuseStep 4620577 = 3465433) B3465433
theorem B6160769 : Blo 1921435 6160769 := bstep (se 2 (by rfl) ⟨2310288, by rfl⟩ : syracuseStep 6160769 = 4620577) B4620577
theorem B4107179 : Blo 1921435 4107179 := bstep (se 1 (by rfl) ⟨3080384, by rfl⟩ : syracuseStep 4107179 = 6160769) B6160769
theorem B2738119 : Blo 1921435 2738119 := bstep (se 1 (by rfl) ⟨2053589, by rfl⟩ : syracuseStep 2738119 = 4107179) B4107179
theorem B3650825 : Blo 1921435 3650825 := bstep (se 2 (by rfl) ⟨1369059, by rfl⟩ : syracuseStep 3650825 = 2738119) B2738119
theorem B2433883 : Blo 1921435 2433883 := bstep (se 1 (by rfl) ⟨1825412, by rfl⟩ : syracuseStep 2433883 = 3650825) B3650825
theorem B3245177 : Blo 1921435 3245177 := bstep (se 2 (by rfl) ⟨1216941, by rfl⟩ : syracuseStep 3245177 = 2433883) B2433883
theorem B2163451 : Blo 1921435 2163451 := bstep (se 1 (by rfl) ⟨1622588, by rfl⟩ : syracuseStep 2163451 = 3245177) B3245177
theorem B2884601 : Blo 1921435 2884601 := bstep (se 2 (by rfl) ⟨1081725, by rfl⟩ : syracuseStep 2884601 = 2163451) B2163451
theorem B1923067 : Blo 1921435 1923067 := bstep (se 1 (by rfl) ⟨1442300, by rfl⟩ : syracuseStep 1923067 = 2884601) B2884601
theorem B1949309 : Blo 1921435 1949309 := bbase (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) (by norm_num)
theorem B20792629 : Blo 1921435 20792629 := bstep (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) B1949309
theorem B110894021 : Blo 1921435 110894021 := bstep (se 4 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 110894021 = 20792629) B20792629
theorem B73929347 : Blo 1921435 73929347 := bstep (se 1 (by rfl) ⟨55447010, by rfl⟩ : syracuseStep 73929347 = 110894021) B110894021
theorem B49286231 : Blo 1921435 49286231 := bstep (se 1 (by rfl) ⟨36964673, by rfl⟩ : syracuseStep 49286231 = 73929347) B73929347
theorem B32857487 : Blo 1921435 32857487 := bstep (se 1 (by rfl) ⟨24643115, by rfl⟩ : syracuseStep 32857487 = 49286231) B49286231
theorem B21904991 : Blo 1921435 21904991 := bstep (se 1 (by rfl) ⟨16428743, by rfl⟩ : syracuseStep 21904991 = 32857487) B32857487
theorem B14603327 : Blo 1921435 14603327 := bstep (se 1 (by rfl) ⟨10952495, by rfl⟩ : syracuseStep 14603327 = 21904991) B21904991
theorem B9735551 : Blo 1921435 9735551 := bstep (se 1 (by rfl) ⟨7301663, by rfl⟩ : syracuseStep 9735551 = 14603327) B14603327
theorem B6490367 : Blo 1921435 6490367 := bstep (se 1 (by rfl) ⟨4867775, by rfl⟩ : syracuseStep 6490367 = 9735551) B9735551
theorem B4326911 : Blo 1921435 4326911 := bstep (se 1 (by rfl) ⟨3245183, by rfl⟩ : syracuseStep 4326911 = 6490367) B6490367
theorem B2884607 : Blo 1921435 2884607 := bstep (se 1 (by rfl) ⟨2163455, by rfl⟩ : syracuseStep 2884607 = 4326911) B4326911
theorem B1923071 : Blo 1921435 1923071 := bstep (se 1 (by rfl) ⟨1442303, by rfl⟩ : syracuseStep 1923071 = 2884607) B2884607
theorem B2884613 : Blo 1921435 2884613 := bbase (se 4 (by rfl) ⟨270432, by rfl⟩ : syracuseStep 2884613 = 540865) (by norm_num)
theorem B1923075 : Blo 1921435 1923075 := bstep (se 1 (by rfl) ⟨1442306, by rfl⟩ : syracuseStep 1923075 = 2884613) B2884613
theorem B3245197 : Blo 1921435 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B4326929 : Blo 1921435 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2884619 : Blo 1921435 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B1923079 : Blo 1921435 1923079 := bstep (se 1 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 1923079 = 2884619) B2884619
theorem B2163469 : Blo 1921435 2163469 := bbase (se 3 (by rfl) ⟨405650, by rfl⟩ : syracuseStep 2163469 = 811301) (by norm_num)
theorem B2884625 : Blo 1921435 2884625 := bstep (se 2 (by rfl) ⟨1081734, by rfl⟩ : syracuseStep 2884625 = 2163469) B2163469
theorem B1923083 : Blo 1921435 1923083 := bstep (se 1 (by rfl) ⟨1442312, by rfl⟩ : syracuseStep 1923083 = 2884625) B2884625
theorem B6490421 : Blo 1921435 6490421 := bbase (se 5 (by rfl) ⟨304238, by rfl⟩ : syracuseStep 6490421 = 608477) (by norm_num)
theorem B4326947 : Blo 1921435 4326947 := bstep (se 1 (by rfl) ⟨3245210, by rfl⟩ : syracuseStep 4326947 = 6490421) B6490421
theorem B2884631 : Blo 1921435 2884631 := bstep (se 1 (by rfl) ⟨2163473, by rfl⟩ : syracuseStep 2884631 = 4326947) B4326947
theorem B1923087 : Blo 1921435 1923087 := bstep (se 1 (by rfl) ⟨1442315, by rfl⟩ : syracuseStep 1923087 = 2884631) B2884631
theorem B2884637 : Blo 1921435 2884637 := bbase (se 3 (by rfl) ⟨540869, by rfl⟩ : syracuseStep 2884637 = 1081739) (by norm_num)
theorem B1923091 : Blo 1921435 1923091 := bstep (se 1 (by rfl) ⟨1442318, by rfl⟩ : syracuseStep 1923091 = 2884637) B2884637
theorem B4326965 : Blo 1921435 4326965 := bbase (se 5 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 4326965 = 405653) (by norm_num)
theorem B2884643 : Blo 1921435 2884643 := bstep (se 1 (by rfl) ⟨2163482, by rfl⟩ : syracuseStep 2884643 = 4326965) B4326965
theorem B1923095 : Blo 1921435 1923095 := bstep (se 1 (by rfl) ⟨1442321, by rfl⟩ : syracuseStep 1923095 = 2884643) B2884643
theorem B4620653 : Blo 1921435 4620653 := bbase (se 3 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 4620653 = 1732745) (by norm_num)
theorem B3080435 : Blo 1921435 3080435 := bstep (se 1 (by rfl) ⟨2310326, by rfl⟩ : syracuseStep 3080435 = 4620653) B4620653
theorem B8214493 : Blo 1921435 8214493 := bstep (se 3 (by rfl) ⟨1540217, by rfl⟩ : syracuseStep 8214493 = 3080435) B3080435
theorem B10952657 : Blo 1921435 10952657 := bstep (se 2 (by rfl) ⟨4107246, by rfl⟩ : syracuseStep 10952657 = 8214493) B8214493
theorem B7301771 : Blo 1921435 7301771 := bstep (se 1 (by rfl) ⟨5476328, by rfl⟩ : syracuseStep 7301771 = 10952657) B10952657
theorem B4867847 : Blo 1921435 4867847 := bstep (se 1 (by rfl) ⟨3650885, by rfl⟩ : syracuseStep 4867847 = 7301771) B7301771
theorem B3245231 : Blo 1921435 3245231 := bstep (se 1 (by rfl) ⟨2433923, by rfl⟩ : syracuseStep 3245231 = 4867847) B4867847
theorem B2163487 : Blo 1921435 2163487 := bstep (se 1 (by rfl) ⟨1622615, by rfl⟩ : syracuseStep 2163487 = 3245231) B3245231
theorem B2884649 : Blo 1921435 2884649 := bstep (se 2 (by rfl) ⟨1081743, by rfl⟩ : syracuseStep 2884649 = 2163487) B2163487
theorem B1923099 : Blo 1921435 1923099 := bstep (se 1 (by rfl) ⟨1442324, by rfl⟩ : syracuseStep 1923099 = 2884649) B2884649
theorem B3898685 : Blo 1921435 3898685 := bbase (se 3 (by rfl) ⟨731003, by rfl⟩ : syracuseStep 3898685 = 1462007) (by norm_num)
theorem B2599123 : Blo 1921435 2599123 := bstep (se 1 (by rfl) ⟨1949342, by rfl⟩ : syracuseStep 2599123 = 3898685) B3898685
theorem B3465497 : Blo 1921435 3465497 := bstep (se 2 (by rfl) ⟨1299561, by rfl⟩ : syracuseStep 3465497 = 2599123) B2599123
theorem B2310331 : Blo 1921435 2310331 := bstep (se 1 (by rfl) ⟨1732748, by rfl⟩ : syracuseStep 2310331 = 3465497) B3465497
theorem B3080441 : Blo 1921435 3080441 := bstep (se 2 (by rfl) ⟨1155165, by rfl⟩ : syracuseStep 3080441 = 2310331) B2310331
theorem B8214509 : Blo 1921435 8214509 := bstep (se 3 (by rfl) ⟨1540220, by rfl⟩ : syracuseStep 8214509 = 3080441) B3080441
theorem B5476339 : Blo 1921435 5476339 := bstep (se 1 (by rfl) ⟨4107254, by rfl⟩ : syracuseStep 5476339 = 8214509) B8214509
theorem B7301785 : Blo 1921435 7301785 := bstep (se 2 (by rfl) ⟨2738169, by rfl⟩ : syracuseStep 7301785 = 5476339) B5476339
theorem B9735713 : Blo 1921435 9735713 := bstep (se 2 (by rfl) ⟨3650892, by rfl⟩ : syracuseStep 9735713 = 7301785) B7301785
theorem B6490475 : Blo 1921435 6490475 := bstep (se 1 (by rfl) ⟨4867856, by rfl⟩ : syracuseStep 6490475 = 9735713) B9735713
theorem B4326983 : Blo 1921435 4326983 := bstep (se 1 (by rfl) ⟨3245237, by rfl⟩ : syracuseStep 4326983 = 6490475) B6490475
theorem B2884655 : Blo 1921435 2884655 := bstep (se 1 (by rfl) ⟨2163491, by rfl⟩ : syracuseStep 2884655 = 4326983) B4326983
theorem B1923103 : Blo 1921435 1923103 := bstep (se 1 (by rfl) ⟨1442327, by rfl⟩ : syracuseStep 1923103 = 2884655) B2884655
theorem B2884661 : Blo 1921435 2884661 := bbase (se 5 (by rfl) ⟨135218, by rfl⟩ : syracuseStep 2884661 = 270437) (by norm_num)
theorem B1923107 : Blo 1921435 1923107 := bstep (se 1 (by rfl) ⟨1442330, by rfl⟩ : syracuseStep 1923107 = 2884661) B2884661
theorem B4867877 : Blo 1921435 4867877 := bbase (se 4 (by rfl) ⟨456363, by rfl⟩ : syracuseStep 4867877 = 912727) (by norm_num)
theorem B3245251 : Blo 1921435 3245251 := bstep (se 1 (by rfl) ⟨2433938, by rfl⟩ : syracuseStep 3245251 = 4867877) B4867877
theorem B4327001 : Blo 1921435 4327001 := bstep (se 2 (by rfl) ⟨1622625, by rfl⟩ : syracuseStep 4327001 = 3245251) B3245251
theorem B2884667 : Blo 1921435 2884667 := bstep (se 1 (by rfl) ⟨2163500, by rfl⟩ : syracuseStep 2884667 = 4327001) B4327001
theorem B1923111 : Blo 1921435 1923111 := bstep (se 1 (by rfl) ⟨1442333, by rfl⟩ : syracuseStep 1923111 = 2884667) B2884667
theorem B2163505 : Blo 1921435 2163505 := bbase (se 2 (by rfl) ⟨811314, by rfl⟩ : syracuseStep 2163505 = 1622629) (by norm_num)
theorem B2884673 : Blo 1921435 2884673 := bstep (se 2 (by rfl) ⟨1081752, by rfl⟩ : syracuseStep 2884673 = 2163505) B2163505
theorem B1923115 : Blo 1921435 1923115 := bstep (se 1 (by rfl) ⟨1442336, by rfl⟩ : syracuseStep 1923115 = 2884673) B2884673
theorem B4620701 : Blo 1921435 4620701 := bbase (se 3 (by rfl) ⟨866381, by rfl⟩ : syracuseStep 4620701 = 1732763) (by norm_num)
theorem B3080467 : Blo 1921435 3080467 := bstep (se 1 (by rfl) ⟨2310350, by rfl⟩ : syracuseStep 3080467 = 4620701) B4620701
theorem B4107289 : Blo 1921435 4107289 := bstep (se 2 (by rfl) ⟨1540233, by rfl⟩ : syracuseStep 4107289 = 3080467) B3080467
theorem B5476385 : Blo 1921435 5476385 := bstep (se 2 (by rfl) ⟨2053644, by rfl⟩ : syracuseStep 5476385 = 4107289) B4107289
theorem B3650923 : Blo 1921435 3650923 := bstep (se 1 (by rfl) ⟨2738192, by rfl⟩ : syracuseStep 3650923 = 5476385) B5476385
theorem B4867897 : Blo 1921435 4867897 := bstep (se 2 (by rfl) ⟨1825461, by rfl⟩ : syracuseStep 4867897 = 3650923) B3650923
theorem B6490529 : Blo 1921435 6490529 := bstep (se 2 (by rfl) ⟨2433948, by rfl⟩ : syracuseStep 6490529 = 4867897) B4867897
theorem B4327019 : Blo 1921435 4327019 := bstep (se 1 (by rfl) ⟨3245264, by rfl⟩ : syracuseStep 4327019 = 6490529) B6490529
theorem B2884679 : Blo 1921435 2884679 := bstep (se 1 (by rfl) ⟨2163509, by rfl⟩ : syracuseStep 2884679 = 4327019) B4327019
theorem B1923119 : Blo 1921435 1923119 := bstep (se 1 (by rfl) ⟨1442339, by rfl⟩ : syracuseStep 1923119 = 2884679) B2884679
theorem B2884685 : Blo 1921435 2884685 := bbase (se 3 (by rfl) ⟨540878, by rfl⟩ : syracuseStep 2884685 = 1081757) (by norm_num)
theorem B1923123 : Blo 1921435 1923123 := bstep (se 1 (by rfl) ⟨1442342, by rfl⟩ : syracuseStep 1923123 = 2884685) B2884685
theorem B4327037 : Blo 1921435 4327037 := bbase (se 3 (by rfl) ⟨811319, by rfl⟩ : syracuseStep 4327037 = 1622639) (by norm_num)
theorem B2884691 : Blo 1921435 2884691 := bstep (se 1 (by rfl) ⟨2163518, by rfl⟩ : syracuseStep 2884691 = 4327037) B4327037
theorem B1923127 : Blo 1921435 1923127 := bstep (se 1 (by rfl) ⟨1442345, by rfl⟩ : syracuseStep 1923127 = 2884691) B2884691
theorem B3245285 : Blo 1921435 3245285 := bbase (se 4 (by rfl) ⟨304245, by rfl⟩ : syracuseStep 3245285 = 608491) (by norm_num)
theorem B2163523 : Blo 1921435 2163523 := bstep (se 1 (by rfl) ⟨1622642, by rfl⟩ : syracuseStep 2163523 = 3245285) B3245285
theorem B2884697 : Blo 1921435 2884697 := bstep (se 2 (by rfl) ⟨1081761, by rfl⟩ : syracuseStep 2884697 = 2163523) B2163523
theorem B1923131 : Blo 1921435 1923131 := bstep (se 1 (by rfl) ⟨1442348, by rfl⟩ : syracuseStep 1923131 = 2884697) B2884697
theorem B6931109 : Blo 1921435 6931109 := bbase (se 4 (by rfl) ⟨649791, by rfl⟩ : syracuseStep 6931109 = 1299583) (by norm_num)
theorem B4620739 : Blo 1921435 4620739 := bstep (se 1 (by rfl) ⟨3465554, by rfl⟩ : syracuseStep 4620739 = 6931109) B6931109
theorem B6160985 : Blo 1921435 6160985 := bstep (se 2 (by rfl) ⟨2310369, by rfl⟩ : syracuseStep 6160985 = 4620739) B4620739
theorem B4107323 : Blo 1921435 4107323 := bstep (se 1 (by rfl) ⟨3080492, by rfl⟩ : syracuseStep 4107323 = 6160985) B6160985
theorem B2738215 : Blo 1921435 2738215 := bstep (se 1 (by rfl) ⟨2053661, by rfl⟩ : syracuseStep 2738215 = 4107323) B4107323
theorem B14603813 : Blo 1921435 14603813 := bstep (se 4 (by rfl) ⟨1369107, by rfl⟩ : syracuseStep 14603813 = 2738215) B2738215
theorem B9735875 : Blo 1921435 9735875 := bstep (se 1 (by rfl) ⟨7301906, by rfl⟩ : syracuseStep 9735875 = 14603813) B14603813
theorem B6490583 : Blo 1921435 6490583 := bstep (se 1 (by rfl) ⟨4867937, by rfl⟩ : syracuseStep 6490583 = 9735875) B9735875
theorem B4327055 : Blo 1921435 4327055 := bstep (se 1 (by rfl) ⟨3245291, by rfl⟩ : syracuseStep 4327055 = 6490583) B6490583
theorem B2884703 : Blo 1921435 2884703 := bstep (se 1 (by rfl) ⟨2163527, by rfl⟩ : syracuseStep 2884703 = 4327055) B4327055
theorem B1923135 : Blo 1921435 1923135 := bstep (se 1 (by rfl) ⟨1442351, by rfl⟩ : syracuseStep 1923135 = 2884703) B2884703
theorem B2884709 : Blo 1921435 2884709 := bbase (se 4 (by rfl) ⟨270441, by rfl⟩ : syracuseStep 2884709 = 540883) (by norm_num)
theorem B1923139 : Blo 1921435 1923139 := bstep (se 1 (by rfl) ⟨1442354, by rfl⟩ : syracuseStep 1923139 = 2884709) B2884709
theorem B4107341 : Blo 1921435 4107341 := bbase (se 3 (by rfl) ⟨770126, by rfl⟩ : syracuseStep 4107341 = 1540253) (by norm_num)
theorem B2738227 : Blo 1921435 2738227 := bstep (se 1 (by rfl) ⟨2053670, by rfl⟩ : syracuseStep 2738227 = 4107341) B4107341
theorem B3650969 : Blo 1921435 3650969 := bstep (se 2 (by rfl) ⟨1369113, by rfl⟩ : syracuseStep 3650969 = 2738227) B2738227
theorem B2433979 : Blo 1921435 2433979 := bstep (se 1 (by rfl) ⟨1825484, by rfl⟩ : syracuseStep 2433979 = 3650969) B3650969
theorem B3245305 : Blo 1921435 3245305 := bstep (se 2 (by rfl) ⟨1216989, by rfl⟩ : syracuseStep 3245305 = 2433979) B2433979
theorem B4327073 : Blo 1921435 4327073 := bstep (se 2 (by rfl) ⟨1622652, by rfl⟩ : syracuseStep 4327073 = 3245305) B3245305
theorem B2884715 : Blo 1921435 2884715 := bstep (se 1 (by rfl) ⟨2163536, by rfl⟩ : syracuseStep 2884715 = 4327073) B4327073
theorem B1923143 : Blo 1921435 1923143 := bstep (se 1 (by rfl) ⟨1442357, by rfl⟩ : syracuseStep 1923143 = 2884715) B2884715
theorem B2163541 : Blo 1921435 2163541 := bbase (se 9 (by rfl) ⟨6338, by rfl⟩ : syracuseStep 2163541 = 12677) (by norm_num)
theorem B2884721 : Blo 1921435 2884721 := bstep (se 2 (by rfl) ⟨1081770, by rfl⟩ : syracuseStep 2884721 = 2163541) B2163541
theorem B1923147 : Blo 1921435 1923147 := bstep (se 1 (by rfl) ⟨1442360, by rfl⟩ : syracuseStep 1923147 = 2884721) B2884721
theorem B2433989 : Blo 1921435 2433989 := bbase (se 4 (by rfl) ⟨228186, by rfl⟩ : syracuseStep 2433989 = 456373) (by norm_num)
theorem B6490637 : Blo 1921435 6490637 := bstep (se 3 (by rfl) ⟨1216994, by rfl⟩ : syracuseStep 6490637 = 2433989) B2433989
theorem B4327091 : Blo 1921435 4327091 := bstep (se 1 (by rfl) ⟨3245318, by rfl⟩ : syracuseStep 4327091 = 6490637) B6490637
theorem B2884727 : Blo 1921435 2884727 := bstep (se 1 (by rfl) ⟨2163545, by rfl⟩ : syracuseStep 2884727 = 4327091) B4327091
theorem B1923151 : Blo 1921435 1923151 := bstep (se 1 (by rfl) ⟨1442363, by rfl⟩ : syracuseStep 1923151 = 2884727) B2884727
theorem B2884733 : Blo 1921435 2884733 := bbase (se 3 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 2884733 = 1081775) (by norm_num)
theorem B1923155 : Blo 1921435 1923155 := bstep (se 1 (by rfl) ⟨1442366, by rfl⟩ : syracuseStep 1923155 = 2884733) B2884733
theorem B4327109 : Blo 1921435 4327109 := bbase (se 4 (by rfl) ⟨405666, by rfl⟩ : syracuseStep 4327109 = 811333) (by norm_num)
theorem B2884739 : Blo 1921435 2884739 := bstep (se 1 (by rfl) ⟨2163554, by rfl⟩ : syracuseStep 2884739 = 4327109) B4327109
theorem B1923159 : Blo 1921435 1923159 := bstep (se 1 (by rfl) ⟨1442369, by rfl⟩ : syracuseStep 1923159 = 2884739) B2884739
theorem B3802493 : Blo 1921435 3802493 := bbase (se 3 (by rfl) ⟨712967, by rfl⟩ : syracuseStep 3802493 = 1425935) (by norm_num)
theorem B2534995 : Blo 1921435 2534995 := bstep (se 1 (by rfl) ⟨1901246, by rfl⟩ : syracuseStep 2534995 = 3802493) B3802493
theorem B13519973 : Blo 1921435 13519973 := bstep (se 4 (by rfl) ⟨1267497, by rfl⟩ : syracuseStep 13519973 = 2534995) B2534995
theorem B36053261 : Blo 1921435 36053261 := bstep (se 3 (by rfl) ⟨6759986, by rfl⟩ : syracuseStep 36053261 = 13519973) B13519973
theorem B24035507 : Blo 1921435 24035507 := bstep (se 1 (by rfl) ⟨18026630, by rfl⟩ : syracuseStep 24035507 = 36053261) B36053261
theorem B16023671 : Blo 1921435 16023671 := bstep (se 1 (by rfl) ⟨12017753, by rfl⟩ : syracuseStep 16023671 = 24035507) B24035507
theorem B10682447 : Blo 1921435 10682447 := bstep (se 1 (by rfl) ⟨8011835, by rfl⟩ : syracuseStep 10682447 = 16023671) B16023671
theorem B28486525 : Blo 1921435 28486525 := bstep (se 3 (by rfl) ⟨5341223, by rfl⟩ : syracuseStep 28486525 = 10682447) B10682447
theorem B37982033 : Blo 1921435 37982033 := bstep (se 2 (by rfl) ⟨14243262, by rfl⟩ : syracuseStep 37982033 = 28486525) B28486525
theorem B25321355 : Blo 1921435 25321355 := bstep (se 1 (by rfl) ⟨18991016, by rfl⟩ : syracuseStep 25321355 = 37982033) B37982033
theorem B16880903 : Blo 1921435 16880903 := bstep (se 1 (by rfl) ⟨12660677, by rfl⟩ : syracuseStep 16880903 = 25321355) B25321355
theorem B11253935 : Blo 1921435 11253935 := bstep (se 1 (by rfl) ⟨8440451, by rfl⟩ : syracuseStep 11253935 = 16880903) B16880903
theorem B30010493 : Blo 1921435 30010493 := bstep (se 3 (by rfl) ⟨5626967, by rfl⟩ : syracuseStep 30010493 = 11253935) B11253935
theorem B20006995 : Blo 1921435 20006995 := bstep (se 1 (by rfl) ⟨15005246, by rfl⟩ : syracuseStep 20006995 = 30010493) B30010493
theorem B26675993 : Blo 1921435 26675993 := bstep (se 2 (by rfl) ⟨10003497, by rfl⟩ : syracuseStep 26675993 = 20006995) B20006995
theorem B71135981 : Blo 1921435 71135981 := bstep (se 3 (by rfl) ⟨13337996, by rfl⟩ : syracuseStep 71135981 = 26675993) B26675993
theorem B47423987 : Blo 1921435 47423987 := bstep (se 1 (by rfl) ⟨35567990, by rfl⟩ : syracuseStep 47423987 = 71135981) B71135981
theorem B31615991 : Blo 1921435 31615991 := bstep (se 1 (by rfl) ⟨23711993, by rfl⟩ : syracuseStep 31615991 = 47423987) B47423987
theorem B21077327 : Blo 1921435 21077327 := bstep (se 1 (by rfl) ⟨15807995, by rfl⟩ : syracuseStep 21077327 = 31615991) B31615991
theorem B14051551 : Blo 1921435 14051551 := bstep (se 1 (by rfl) ⟨10538663, by rfl⟩ : syracuseStep 14051551 = 21077327) B21077327
theorem B18735401 : Blo 1921435 18735401 := bstep (se 2 (by rfl) ⟨7025775, by rfl⟩ : syracuseStep 18735401 = 14051551) B14051551
theorem B49961069 : Blo 1921435 49961069 := bstep (se 3 (by rfl) ⟨9367700, by rfl⟩ : syracuseStep 49961069 = 18735401) B18735401
theorem B33307379 : Blo 1921435 33307379 := bstep (se 1 (by rfl) ⟨24980534, by rfl⟩ : syracuseStep 33307379 = 49961069) B49961069
theorem B22204919 : Blo 1921435 22204919 := bstep (se 1 (by rfl) ⟨16653689, by rfl⟩ : syracuseStep 22204919 = 33307379) B33307379
theorem B14803279 : Blo 1921435 14803279 := bstep (se 1 (by rfl) ⟨11102459, by rfl⟩ : syracuseStep 14803279 = 22204919) B22204919
theorem B78950821 : Blo 1921435 78950821 := bstep (se 4 (by rfl) ⟨7401639, by rfl⟩ : syracuseStep 78950821 = 14803279) B14803279
theorem B105267761 : Blo 1921435 105267761 := bstep (se 2 (by rfl) ⟨39475410, by rfl⟩ : syracuseStep 105267761 = 78950821) B78950821
theorem B70178507 : Blo 1921435 70178507 := bstep (se 1 (by rfl) ⟨52633880, by rfl⟩ : syracuseStep 70178507 = 105267761) B105267761
theorem B46785671 : Blo 1921435 46785671 := bstep (se 1 (by rfl) ⟨35089253, by rfl⟩ : syracuseStep 46785671 = 70178507) B70178507
theorem B31190447 : Blo 1921435 31190447 := bstep (se 1 (by rfl) ⟨23392835, by rfl⟩ : syracuseStep 31190447 = 46785671) B46785671
theorem B20793631 : Blo 1921435 20793631 := bstep (se 1 (by rfl) ⟨15595223, by rfl⟩ : syracuseStep 20793631 = 31190447) B31190447
theorem B27724841 : Blo 1921435 27724841 := bstep (se 2 (by rfl) ⟨10396815, by rfl⟩ : syracuseStep 27724841 = 20793631) B20793631
theorem B18483227 : Blo 1921435 18483227 := bstep (se 1 (by rfl) ⟨13862420, by rfl⟩ : syracuseStep 18483227 = 27724841) B27724841
theorem B12322151 : Blo 1921435 12322151 := bstep (se 1 (by rfl) ⟨9241613, by rfl⟩ : syracuseStep 12322151 = 18483227) B18483227
theorem B8214767 : Blo 1921435 8214767 := bstep (se 1 (by rfl) ⟨6161075, by rfl⟩ : syracuseStep 8214767 = 12322151) B12322151
theorem B5476511 : Blo 1921435 5476511 := bstep (se 1 (by rfl) ⟨4107383, by rfl⟩ : syracuseStep 5476511 = 8214767) B8214767
theorem B3651007 : Blo 1921435 3651007 := bstep (se 1 (by rfl) ⟨2738255, by rfl⟩ : syracuseStep 3651007 = 5476511) B5476511
theorem B4868009 : Blo 1921435 4868009 := bstep (se 2 (by rfl) ⟨1825503, by rfl⟩ : syracuseStep 4868009 = 3651007) B3651007
theorem B3245339 : Blo 1921435 3245339 := bstep (se 1 (by rfl) ⟨2434004, by rfl⟩ : syracuseStep 3245339 = 4868009) B4868009
theorem B2163559 : Blo 1921435 2163559 := bstep (se 1 (by rfl) ⟨1622669, by rfl⟩ : syracuseStep 2163559 = 3245339) B3245339
theorem B2884745 : Blo 1921435 2884745 := bstep (se 2 (by rfl) ⟨1081779, by rfl⟩ : syracuseStep 2884745 = 2163559) B2163559
theorem B1923163 : Blo 1921435 1923163 := bstep (se 1 (by rfl) ⟨1442372, by rfl⟩ : syracuseStep 1923163 = 2884745) B2884745
theorem B9736037 : Blo 1921435 9736037 := bbase (se 4 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 9736037 = 1825507) (by norm_num)
theorem B6490691 : Blo 1921435 6490691 := bstep (se 1 (by rfl) ⟨4868018, by rfl⟩ : syracuseStep 6490691 = 9736037) B9736037
theorem B4327127 : Blo 1921435 4327127 := bstep (se 1 (by rfl) ⟨3245345, by rfl⟩ : syracuseStep 4327127 = 6490691) B6490691
theorem B2884751 : Blo 1921435 2884751 := bstep (se 1 (by rfl) ⟨2163563, by rfl⟩ : syracuseStep 2884751 = 4327127) B4327127
theorem B1923167 : Blo 1921435 1923167 := bstep (se 1 (by rfl) ⟨1442375, by rfl⟩ : syracuseStep 1923167 = 2884751) B2884751
theorem B2884757 : Blo 1921435 2884757 := bbase (se 6 (by rfl) ⟨67611, by rfl⟩ : syracuseStep 2884757 = 135223) (by norm_num)
theorem B1923171 : Blo 1921435 1923171 := bstep (se 1 (by rfl) ⟨1442378, by rfl⟩ : syracuseStep 1923171 = 2884757) B2884757
theorem B6931253 : Blo 1921435 6931253 := bbase (se 5 (by rfl) ⟨324902, by rfl⟩ : syracuseStep 6931253 = 649805) (by norm_num)
theorem B4620835 : Blo 1921435 4620835 := bstep (se 1 (by rfl) ⟨3465626, by rfl⟩ : syracuseStep 4620835 = 6931253) B6931253
theorem B6161113 : Blo 1921435 6161113 := bstep (se 2 (by rfl) ⟨2310417, by rfl⟩ : syracuseStep 6161113 = 4620835) B4620835
theorem B8214817 : Blo 1921435 8214817 := bstep (se 2 (by rfl) ⟨3080556, by rfl⟩ : syracuseStep 8214817 = 6161113) B6161113
theorem B10953089 : Blo 1921435 10953089 := bstep (se 2 (by rfl) ⟨4107408, by rfl⟩ : syracuseStep 10953089 = 8214817) B8214817
theorem B7302059 : Blo 1921435 7302059 := bstep (se 1 (by rfl) ⟨5476544, by rfl⟩ : syracuseStep 7302059 = 10953089) B10953089
theorem B4868039 : Blo 1921435 4868039 := bstep (se 1 (by rfl) ⟨3651029, by rfl⟩ : syracuseStep 4868039 = 7302059) B7302059
theorem B3245359 : Blo 1921435 3245359 := bstep (se 1 (by rfl) ⟨2434019, by rfl⟩ : syracuseStep 3245359 = 4868039) B4868039
theorem B4327145 : Blo 1921435 4327145 := bstep (se 2 (by rfl) ⟨1622679, by rfl⟩ : syracuseStep 4327145 = 3245359) B3245359
theorem B2884763 : Blo 1921435 2884763 := bstep (se 1 (by rfl) ⟨2163572, by rfl⟩ : syracuseStep 2884763 = 4327145) B4327145
theorem B1923175 : Blo 1921435 1923175 := bstep (se 1 (by rfl) ⟨1442381, by rfl⟩ : syracuseStep 1923175 = 2884763) B2884763
theorem B2163577 : Blo 1921435 2163577 := bbase (se 2 (by rfl) ⟨811341, by rfl⟩ : syracuseStep 2163577 = 1622683) (by norm_num)
theorem B2884769 : Blo 1921435 2884769 := bstep (se 2 (by rfl) ⟨1081788, by rfl⟩ : syracuseStep 2884769 = 2163577) B2163577
theorem B1923179 : Blo 1921435 1923179 := bstep (se 1 (by rfl) ⟨1442384, by rfl⟩ : syracuseStep 1923179 = 2884769) B2884769
theorem B4683901 : Blo 1921435 4683901 := bbase (se 3 (by rfl) ⟨878231, by rfl⟩ : syracuseStep 4683901 = 1756463) (by norm_num)
theorem B6245201 : Blo 1921435 6245201 := bstep (se 2 (by rfl) ⟨2341950, by rfl⟩ : syracuseStep 6245201 = 4683901) B4683901
theorem B16653869 : Blo 1921435 16653869 := bstep (se 3 (by rfl) ⟨3122600, by rfl⟩ : syracuseStep 16653869 = 6245201) B6245201
theorem B11102579 : Blo 1921435 11102579 := bstep (se 1 (by rfl) ⟨8326934, by rfl⟩ : syracuseStep 11102579 = 16653869) B16653869
theorem B7401719 : Blo 1921435 7401719 := bstep (se 1 (by rfl) ⟨5551289, by rfl⟩ : syracuseStep 7401719 = 11102579) B11102579
theorem B19737917 : Blo 1921435 19737917 := bstep (se 3 (by rfl) ⟨3700859, by rfl⟩ : syracuseStep 19737917 = 7401719) B7401719
theorem B13158611 : Blo 1921435 13158611 := bstep (se 1 (by rfl) ⟨9868958, by rfl⟩ : syracuseStep 13158611 = 19737917) B19737917
theorem B8772407 : Blo 1921435 8772407 := bstep (se 1 (by rfl) ⟨6579305, by rfl⟩ : syracuseStep 8772407 = 13158611) B13158611
theorem B5848271 : Blo 1921435 5848271 := bstep (se 1 (by rfl) ⟨4386203, by rfl⟩ : syracuseStep 5848271 = 8772407) B8772407
theorem B3898847 : Blo 1921435 3898847 := bstep (se 1 (by rfl) ⟨2924135, by rfl⟩ : syracuseStep 3898847 = 5848271) B5848271
theorem B2599231 : Blo 1921435 2599231 := bstep (se 1 (by rfl) ⟨1949423, by rfl⟩ : syracuseStep 2599231 = 3898847) B3898847
theorem B3465641 : Blo 1921435 3465641 := bstep (se 2 (by rfl) ⟨1299615, by rfl⟩ : syracuseStep 3465641 = 2599231) B2599231
theorem B2310427 : Blo 1921435 2310427 := bstep (se 1 (by rfl) ⟨1732820, by rfl⟩ : syracuseStep 2310427 = 3465641) B3465641
theorem B12322277 : Blo 1921435 12322277 := bstep (se 4 (by rfl) ⟨1155213, by rfl⟩ : syracuseStep 12322277 = 2310427) B2310427
theorem B8214851 : Blo 1921435 8214851 := bstep (se 1 (by rfl) ⟨6161138, by rfl⟩ : syracuseStep 8214851 = 12322277) B12322277
theorem B5476567 : Blo 1921435 5476567 := bstep (se 1 (by rfl) ⟨4107425, by rfl⟩ : syracuseStep 5476567 = 8214851) B8214851
theorem B7302089 : Blo 1921435 7302089 := bstep (se 2 (by rfl) ⟨2738283, by rfl⟩ : syracuseStep 7302089 = 5476567) B5476567
theorem B4868059 : Blo 1921435 4868059 := bstep (se 1 (by rfl) ⟨3651044, by rfl⟩ : syracuseStep 4868059 = 7302089) B7302089
theorem B6490745 : Blo 1921435 6490745 := bstep (se 2 (by rfl) ⟨2434029, by rfl⟩ : syracuseStep 6490745 = 4868059) B4868059
theorem B4327163 : Blo 1921435 4327163 := bstep (se 1 (by rfl) ⟨3245372, by rfl⟩ : syracuseStep 4327163 = 6490745) B6490745
theorem B2884775 : Blo 1921435 2884775 := bstep (se 1 (by rfl) ⟨2163581, by rfl⟩ : syracuseStep 2884775 = 4327163) B4327163
theorem B1923183 : Blo 1921435 1923183 := bstep (se 1 (by rfl) ⟨1442387, by rfl⟩ : syracuseStep 1923183 = 2884775) B2884775
theorem B2884781 : Blo 1921435 2884781 := bbase (se 3 (by rfl) ⟨540896, by rfl⟩ : syracuseStep 2884781 = 1081793) (by norm_num)
theorem B1923187 : Blo 1921435 1923187 := bstep (se 1 (by rfl) ⟨1442390, by rfl⟩ : syracuseStep 1923187 = 2884781) B2884781
theorem B4327181 : Blo 1921435 4327181 := bbase (se 3 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 4327181 = 1622693) (by norm_num)
theorem B2884787 : Blo 1921435 2884787 := bstep (se 1 (by rfl) ⟨2163590, by rfl⟩ : syracuseStep 2884787 = 4327181) B4327181
theorem B1923191 : Blo 1921435 1923191 := bstep (se 1 (by rfl) ⟨1442393, by rfl⟩ : syracuseStep 1923191 = 2884787) B2884787
theorem B2434045 : Blo 1921435 2434045 := bbase (se 3 (by rfl) ⟨456383, by rfl⟩ : syracuseStep 2434045 = 912767) (by norm_num)
theorem B3245393 : Blo 1921435 3245393 := bstep (se 2 (by rfl) ⟨1217022, by rfl⟩ : syracuseStep 3245393 = 2434045) B2434045
theorem B2163595 : Blo 1921435 2163595 := bstep (se 1 (by rfl) ⟨1622696, by rfl⟩ : syracuseStep 2163595 = 3245393) B3245393
theorem B2884793 : Blo 1921435 2884793 := bstep (se 2 (by rfl) ⟨1081797, by rfl⟩ : syracuseStep 2884793 = 2163595) B2163595
theorem B1923195 : Blo 1921435 1923195 := bstep (se 1 (by rfl) ⟨1442396, by rfl⟩ : syracuseStep 1923195 = 2884793) B2884793
theorem B6161189 : Blo 1921435 6161189 := bbase (se 4 (by rfl) ⟨577611, by rfl⟩ : syracuseStep 6161189 = 1155223) (by norm_num)
theorem B16429837 : Blo 1921435 16429837 := bstep (se 3 (by rfl) ⟨3080594, by rfl⟩ : syracuseStep 16429837 = 6161189) B6161189
theorem B21906449 : Blo 1921435 21906449 := bstep (se 2 (by rfl) ⟨8214918, by rfl⟩ : syracuseStep 21906449 = 16429837) B16429837
theorem B14604299 : Blo 1921435 14604299 := bstep (se 1 (by rfl) ⟨10953224, by rfl⟩ : syracuseStep 14604299 = 21906449) B21906449
theorem B9736199 : Blo 1921435 9736199 := bstep (se 1 (by rfl) ⟨7302149, by rfl⟩ : syracuseStep 9736199 = 14604299) B14604299
theorem B6490799 : Blo 1921435 6490799 := bstep (se 1 (by rfl) ⟨4868099, by rfl⟩ : syracuseStep 6490799 = 9736199) B9736199
theorem B4327199 : Blo 1921435 4327199 := bstep (se 1 (by rfl) ⟨3245399, by rfl⟩ : syracuseStep 4327199 = 6490799) B6490799
theorem B2884799 : Blo 1921435 2884799 := bstep (se 1 (by rfl) ⟨2163599, by rfl⟩ : syracuseStep 2884799 = 4327199) B4327199
theorem B1923199 : Blo 1921435 1923199 := bstep (se 1 (by rfl) ⟨1442399, by rfl⟩ : syracuseStep 1923199 = 2884799) B2884799
theorem B2884805 : Blo 1921435 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B1923203 : Blo 1921435 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B3245413 : Blo 1921435 3245413 := bbase (se 4 (by rfl) ⟨304257, by rfl⟩ : syracuseStep 3245413 = 608515) (by norm_num)
theorem B4327217 : Blo 1921435 4327217 := bstep (se 2 (by rfl) ⟨1622706, by rfl⟩ : syracuseStep 4327217 = 3245413) B3245413
theorem B2884811 : Blo 1921435 2884811 := bstep (se 1 (by rfl) ⟨2163608, by rfl⟩ : syracuseStep 2884811 = 4327217) B4327217
theorem B1923207 : Blo 1921435 1923207 := bstep (se 1 (by rfl) ⟨1442405, by rfl⟩ : syracuseStep 1923207 = 2884811) B2884811
theorem B2163613 : Blo 1921435 2163613 := bbase (se 3 (by rfl) ⟨405677, by rfl⟩ : syracuseStep 2163613 = 811355) (by norm_num)
theorem B2884817 : Blo 1921435 2884817 := bstep (se 2 (by rfl) ⟨1081806, by rfl⟩ : syracuseStep 2884817 = 2163613) B2163613
theorem B1923211 : Blo 1921435 1923211 := bstep (se 1 (by rfl) ⟨1442408, by rfl⟩ : syracuseStep 1923211 = 2884817) B2884817
theorem B6490853 : Blo 1921435 6490853 := bbase (se 4 (by rfl) ⟨608517, by rfl⟩ : syracuseStep 6490853 = 1217035) (by norm_num)
theorem B4327235 : Blo 1921435 4327235 := bstep (se 1 (by rfl) ⟨3245426, by rfl⟩ : syracuseStep 4327235 = 6490853) B6490853
theorem B2884823 : Blo 1921435 2884823 := bstep (se 1 (by rfl) ⟨2163617, by rfl⟩ : syracuseStep 2884823 = 4327235) B4327235
theorem B1923215 : Blo 1921435 1923215 := bstep (se 1 (by rfl) ⟨1442411, by rfl⟩ : syracuseStep 1923215 = 2884823) B2884823
theorem B2884829 : Blo 1921435 2884829 := bbase (se 3 (by rfl) ⟨540905, by rfl⟩ : syracuseStep 2884829 = 1081811) (by norm_num)
theorem B1923219 : Blo 1921435 1923219 := bstep (se 1 (by rfl) ⟨1442414, by rfl⟩ : syracuseStep 1923219 = 2884829) B2884829
theorem B4327253 : Blo 1921435 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B2884835 : Blo 1921435 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B1923223 : Blo 1921435 1923223 := bstep (se 1 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 1923223 = 2884835) B2884835
theorem B5476693 : Blo 1921435 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B7302257 : Blo 1921435 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B4868171 : Blo 1921435 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B3245447 : Blo 1921435 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B2163631 : Blo 1921435 2163631 := bstep (se 1 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 2163631 = 3245447) B3245447
theorem B2884841 : Blo 1921435 2884841 := bstep (se 2 (by rfl) ⟨1081815, by rfl⟩ : syracuseStep 2884841 = 2163631) B2163631
theorem B1923227 : Blo 1921435 1923227 := bstep (se 1 (by rfl) ⟨1442420, by rfl⟩ : syracuseStep 1923227 = 2884841) B2884841
theorem B112416341 : Blo 1921435 112416341 := bbase (se 8 (by rfl) ⟨658689, by rfl⟩ : syracuseStep 112416341 = 1317379) (by norm_num)
theorem B299776909 : Blo 1921435 299776909 := bstep (se 3 (by rfl) ⟨56208170, by rfl⟩ : syracuseStep 299776909 = 112416341) B112416341
theorem B399702545 : Blo 1921435 399702545 := bstep (se 2 (by rfl) ⟨149888454, by rfl⟩ : syracuseStep 399702545 = 299776909) B299776909
theorem B266468363 : Blo 1921435 266468363 := bstep (se 1 (by rfl) ⟨199851272, by rfl⟩ : syracuseStep 266468363 = 399702545) B399702545
theorem B177645575 : Blo 1921435 177645575 := bstep (se 1 (by rfl) ⟨133234181, by rfl⟩ : syracuseStep 177645575 = 266468363) B266468363
theorem B118430383 : Blo 1921435 118430383 := bstep (se 1 (by rfl) ⟨88822787, by rfl⟩ : syracuseStep 118430383 = 177645575) B177645575
theorem B157907177 : Blo 1921435 157907177 := bstep (se 2 (by rfl) ⟨59215191, by rfl⟩ : syracuseStep 157907177 = 118430383) B118430383
theorem B105271451 : Blo 1921435 105271451 := bstep (se 1 (by rfl) ⟨78953588, by rfl⟩ : syracuseStep 105271451 = 157907177) B157907177
theorem B70180967 : Blo 1921435 70180967 := bstep (se 1 (by rfl) ⟨52635725, by rfl⟩ : syracuseStep 70180967 = 105271451) B105271451
theorem B46787311 : Blo 1921435 46787311 := bstep (se 1 (by rfl) ⟨35090483, by rfl⟩ : syracuseStep 46787311 = 70180967) B70180967
theorem B62383081 : Blo 1921435 62383081 := bstep (se 2 (by rfl) ⟨23393655, by rfl⟩ : syracuseStep 62383081 = 46787311) B46787311
theorem B83177441 : Blo 1921435 83177441 := bstep (se 2 (by rfl) ⟨31191540, by rfl⟩ : syracuseStep 83177441 = 62383081) B62383081
theorem B55451627 : Blo 1921435 55451627 := bstep (se 1 (by rfl) ⟨41588720, by rfl⟩ : syracuseStep 55451627 = 83177441) B83177441
theorem B36967751 : Blo 1921435 36967751 := bstep (se 1 (by rfl) ⟨27725813, by rfl⟩ : syracuseStep 36967751 = 55451627) B55451627
theorem B24645167 : Blo 1921435 24645167 := bstep (se 1 (by rfl) ⟨18483875, by rfl⟩ : syracuseStep 24645167 = 36967751) B36967751
theorem B16430111 : Blo 1921435 16430111 := bstep (se 1 (by rfl) ⟨12322583, by rfl⟩ : syracuseStep 16430111 = 24645167) B24645167
theorem B10953407 : Blo 1921435 10953407 := bstep (se 1 (by rfl) ⟨8215055, by rfl⟩ : syracuseStep 10953407 = 16430111) B16430111
theorem B7302271 : Blo 1921435 7302271 := bstep (se 1 (by rfl) ⟨5476703, by rfl⟩ : syracuseStep 7302271 = 10953407) B10953407
theorem B9736361 : Blo 1921435 9736361 := bstep (se 2 (by rfl) ⟨3651135, by rfl⟩ : syracuseStep 9736361 = 7302271) B7302271
theorem B6490907 : Blo 1921435 6490907 := bstep (se 1 (by rfl) ⟨4868180, by rfl⟩ : syracuseStep 6490907 = 9736361) B9736361
theorem B4327271 : Blo 1921435 4327271 := bstep (se 1 (by rfl) ⟨3245453, by rfl⟩ : syracuseStep 4327271 = 6490907) B6490907
theorem B2884847 : Blo 1921435 2884847 := bstep (se 1 (by rfl) ⟨2163635, by rfl⟩ : syracuseStep 2884847 = 4327271) B4327271
theorem B1923231 : Blo 1921435 1923231 := bstep (se 1 (by rfl) ⟨1442423, by rfl⟩ : syracuseStep 1923231 = 2884847) B2884847
theorem B2884853 : Blo 1921435 2884853 := bbase (se 5 (by rfl) ⟨135227, by rfl⟩ : syracuseStep 2884853 = 270455) (by norm_num)
theorem B1923235 : Blo 1921435 1923235 := bstep (se 1 (by rfl) ⟨1442426, by rfl⟩ : syracuseStep 1923235 = 2884853) B2884853
theorem B4620989 : Blo 1921435 4620989 := bbase (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) (by norm_num)
theorem B12322637 : Blo 1921435 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B8215091 : Blo 1921435 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B5476727 : Blo 1921435 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B3651151 : Blo 1921435 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B4868201 : Blo 1921435 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B3245467 : Blo 1921435 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B4327289 : Blo 1921435 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B2884859 : Blo 1921435 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B1923239 : Blo 1921435 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B2163649 : Blo 1921435 2163649 := bbase (se 2 (by rfl) ⟨811368, by rfl⟩ : syracuseStep 2163649 = 1622737) (by norm_num)
theorem B2884865 : Blo 1921435 2884865 := bstep (se 2 (by rfl) ⟨1081824, by rfl⟩ : syracuseStep 2884865 = 2163649) B2163649
theorem B1923243 : Blo 1921435 1923243 := bstep (se 1 (by rfl) ⟨1442432, by rfl⟩ : syracuseStep 1923243 = 2884865) B2884865
theorem B4868221 : Blo 1921435 4868221 := bbase (se 3 (by rfl) ⟨912791, by rfl⟩ : syracuseStep 4868221 = 1825583) (by norm_num)
theorem B6490961 : Blo 1921435 6490961 := bstep (se 2 (by rfl) ⟨2434110, by rfl⟩ : syracuseStep 6490961 = 4868221) B4868221
theorem B4327307 : Blo 1921435 4327307 := bstep (se 1 (by rfl) ⟨3245480, by rfl⟩ : syracuseStep 4327307 = 6490961) B6490961
theorem B2884871 : Blo 1921435 2884871 := bstep (se 1 (by rfl) ⟨2163653, by rfl⟩ : syracuseStep 2884871 = 4327307) B4327307
theorem B1923247 : Blo 1921435 1923247 := bstep (se 1 (by rfl) ⟨1442435, by rfl⟩ : syracuseStep 1923247 = 2884871) B2884871
theorem B2884877 : Blo 1921435 2884877 := bbase (se 3 (by rfl) ⟨540914, by rfl⟩ : syracuseStep 2884877 = 1081829) (by norm_num)
theorem B1923251 : Blo 1921435 1923251 := bstep (se 1 (by rfl) ⟨1442438, by rfl⟩ : syracuseStep 1923251 = 2884877) B2884877
theorem B4327325 : Blo 1921435 4327325 := bbase (se 3 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 4327325 = 1622747) (by norm_num)
theorem B2884883 : Blo 1921435 2884883 := bstep (se 1 (by rfl) ⟨2163662, by rfl⟩ : syracuseStep 2884883 = 4327325) B4327325
theorem B1923255 : Blo 1921435 1923255 := bstep (se 1 (by rfl) ⟨1442441, by rfl⟩ : syracuseStep 1923255 = 2884883) B2884883
theorem B3245501 : Blo 1921435 3245501 := bbase (se 3 (by rfl) ⟨608531, by rfl⟩ : syracuseStep 3245501 = 1217063) (by norm_num)
theorem B2163667 : Blo 1921435 2163667 := bstep (se 1 (by rfl) ⟨1622750, by rfl⟩ : syracuseStep 2163667 = 3245501) B3245501
theorem B2884889 : Blo 1921435 2884889 := bstep (se 2 (by rfl) ⟨1081833, by rfl⟩ : syracuseStep 2884889 = 2163667) B2163667
theorem B1923259 : Blo 1921435 1923259 := bstep (se 1 (by rfl) ⟨1442444, by rfl⟩ : syracuseStep 1923259 = 2884889) B2884889
theorem B10953589 : Blo 1921435 10953589 := bbase (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) (by norm_num)
theorem B14604785 : Blo 1921435 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B9736523 : Blo 1921435 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B6491015 : Blo 1921435 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B4327343 : Blo 1921435 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B2884895 : Blo 1921435 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B1923263 : Blo 1921435 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B2884901 : Blo 1921435 2884901 := bbase (se 4 (by rfl) ⟨270459, by rfl⟩ : syracuseStep 2884901 = 540919) (by norm_num)
theorem B1923267 : Blo 1921435 1923267 := bstep (se 1 (by rfl) ⟨1442450, by rfl⟩ : syracuseStep 1923267 = 2884901) B2884901
theorem B2434141 : Blo 1921435 2434141 := bbase (se 3 (by rfl) ⟨456401, by rfl⟩ : syracuseStep 2434141 = 912803) (by norm_num)
theorem B3245521 : Blo 1921435 3245521 := bstep (se 2 (by rfl) ⟨1217070, by rfl⟩ : syracuseStep 3245521 = 2434141) B2434141
theorem B4327361 : Blo 1921435 4327361 := bstep (se 2 (by rfl) ⟨1622760, by rfl⟩ : syracuseStep 4327361 = 3245521) B3245521
theorem B2884907 : Blo 1921435 2884907 := bstep (se 1 (by rfl) ⟨2163680, by rfl⟩ : syracuseStep 2884907 = 4327361) B4327361
theorem B1923271 : Blo 1921435 1923271 := bstep (se 1 (by rfl) ⟨1442453, by rfl⟩ : syracuseStep 1923271 = 2884907) B2884907
theorem B2163685 : Blo 1921435 2163685 := bbase (se 4 (by rfl) ⟨202845, by rfl⟩ : syracuseStep 2163685 = 405691) (by norm_num)
theorem B2884913 : Blo 1921435 2884913 := bstep (se 2 (by rfl) ⟨1081842, by rfl⟩ : syracuseStep 2884913 = 2163685) B2163685
theorem B1923275 : Blo 1921435 1923275 := bstep (se 1 (by rfl) ⟨1442456, by rfl⟩ : syracuseStep 1923275 = 2884913) B2884913
theorem B3701045 : Blo 1921435 3701045 := bbase (se 5 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 3701045 = 346973) (by norm_num)
theorem B2467363 : Blo 1921435 2467363 := bstep (se 1 (by rfl) ⟨1850522, by rfl⟩ : syracuseStep 2467363 = 3701045) B3701045
theorem B3289817 : Blo 1921435 3289817 := bstep (se 2 (by rfl) ⟨1233681, by rfl⟩ : syracuseStep 3289817 = 2467363) B2467363
theorem B2193211 : Blo 1921435 2193211 := bstep (se 1 (by rfl) ⟨1644908, by rfl⟩ : syracuseStep 2193211 = 3289817) B3289817
theorem B2924281 : Blo 1921435 2924281 := bstep (se 2 (by rfl) ⟨1096605, by rfl⟩ : syracuseStep 2924281 = 2193211) B2193211
theorem B15596165 : Blo 1921435 15596165 := bstep (se 4 (by rfl) ⟨1462140, by rfl⟩ : syracuseStep 15596165 = 2924281) B2924281
theorem B10397443 : Blo 1921435 10397443 := bstep (se 1 (by rfl) ⟨7798082, by rfl⟩ : syracuseStep 10397443 = 15596165) B15596165
theorem B13863257 : Blo 1921435 13863257 := bstep (se 2 (by rfl) ⟨5198721, by rfl⟩ : syracuseStep 13863257 = 10397443) B10397443
theorem B9242171 : Blo 1921435 9242171 := bstep (se 1 (by rfl) ⟨6931628, by rfl⟩ : syracuseStep 9242171 = 13863257) B13863257
theorem B6161447 : Blo 1921435 6161447 := bstep (se 1 (by rfl) ⟨4621085, by rfl⟩ : syracuseStep 6161447 = 9242171) B9242171
theorem B4107631 : Blo 1921435 4107631 := bstep (se 1 (by rfl) ⟨3080723, by rfl⟩ : syracuseStep 4107631 = 6161447) B6161447
theorem B5476841 : Blo 1921435 5476841 := bstep (se 2 (by rfl) ⟨2053815, by rfl⟩ : syracuseStep 5476841 = 4107631) B4107631
theorem B3651227 : Blo 1921435 3651227 := bstep (se 1 (by rfl) ⟨2738420, by rfl⟩ : syracuseStep 3651227 = 5476841) B5476841
theorem B2434151 : Blo 1921435 2434151 := bstep (se 1 (by rfl) ⟨1825613, by rfl⟩ : syracuseStep 2434151 = 3651227) B3651227
theorem B6491069 : Blo 1921435 6491069 := bstep (se 3 (by rfl) ⟨1217075, by rfl⟩ : syracuseStep 6491069 = 2434151) B2434151
theorem B4327379 : Blo 1921435 4327379 := bstep (se 1 (by rfl) ⟨3245534, by rfl⟩ : syracuseStep 4327379 = 6491069) B6491069
theorem B2884919 : Blo 1921435 2884919 := bstep (se 1 (by rfl) ⟨2163689, by rfl⟩ : syracuseStep 2884919 = 4327379) B4327379
theorem B1923279 : Blo 1921435 1923279 := bstep (se 1 (by rfl) ⟨1442459, by rfl⟩ : syracuseStep 1923279 = 2884919) B2884919
theorem B2884925 : Blo 1921435 2884925 := bbase (se 3 (by rfl) ⟨540923, by rfl⟩ : syracuseStep 2884925 = 1081847) (by norm_num)
theorem B1923283 : Blo 1921435 1923283 := bstep (se 1 (by rfl) ⟨1442462, by rfl⟩ : syracuseStep 1923283 = 2884925) B2884925
theorem B4327397 : Blo 1921435 4327397 := bbase (se 4 (by rfl) ⟨405693, by rfl⟩ : syracuseStep 4327397 = 811387) (by norm_num)
theorem B2884931 : Blo 1921435 2884931 := bstep (se 1 (by rfl) ⟨2163698, by rfl⟩ : syracuseStep 2884931 = 4327397) B4327397
theorem B1923287 : Blo 1921435 1923287 := bstep (se 1 (by rfl) ⟨1442465, by rfl⟩ : syracuseStep 1923287 = 2884931) B2884931
theorem B4868333 : Blo 1921435 4868333 := bbase (se 3 (by rfl) ⟨912812, by rfl⟩ : syracuseStep 4868333 = 1825625) (by norm_num)
theorem B3245555 : Blo 1921435 3245555 := bstep (se 1 (by rfl) ⟨2434166, by rfl⟩ : syracuseStep 3245555 = 4868333) B4868333
theorem B2163703 : Blo 1921435 2163703 := bstep (se 1 (by rfl) ⟨1622777, by rfl⟩ : syracuseStep 2163703 = 3245555) B3245555
theorem B2884937 : Blo 1921435 2884937 := bstep (se 2 (by rfl) ⟨1081851, by rfl⟩ : syracuseStep 2884937 = 2163703) B2163703
theorem B1923291 : Blo 1921435 1923291 := bstep (se 1 (by rfl) ⟨1442468, by rfl⟩ : syracuseStep 1923291 = 2884937) B2884937
theorem B3080749 : Blo 1921435 3080749 := bbase (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) (by norm_num)
theorem B4107665 : Blo 1921435 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B2738443 : Blo 1921435 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B3651257 : Blo 1921435 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B9736685 : Blo 1921435 9736685 := bstep (se 3 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 9736685 = 3651257) B3651257
theorem B6491123 : Blo 1921435 6491123 := bstep (se 1 (by rfl) ⟨4868342, by rfl⟩ : syracuseStep 6491123 = 9736685) B9736685
theorem B4327415 : Blo 1921435 4327415 := bstep (se 1 (by rfl) ⟨3245561, by rfl⟩ : syracuseStep 4327415 = 6491123) B6491123
theorem B2884943 : Blo 1921435 2884943 := bstep (se 1 (by rfl) ⟨2163707, by rfl⟩ : syracuseStep 2884943 = 4327415) B4327415
theorem B1923295 : Blo 1921435 1923295 := bstep (se 1 (by rfl) ⟨1442471, by rfl⟩ : syracuseStep 1923295 = 2884943) B2884943
theorem B2884949 : Blo 1921435 2884949 := bbase (se 12 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 2884949 = 2113) (by norm_num)
theorem B1923299 : Blo 1921435 1923299 := bstep (se 1 (by rfl) ⟨1442474, by rfl⟩ : syracuseStep 1923299 = 2884949) B2884949
theorem B2053841 : Blo 1921435 2053841 := bbase (se 2 (by rfl) ⟨770190, by rfl⟩ : syracuseStep 2053841 = 1540381) (by norm_num)
theorem B5476909 : Blo 1921435 5476909 := bstep (se 3 (by rfl) ⟨1026920, by rfl⟩ : syracuseStep 5476909 = 2053841) B2053841
theorem B7302545 : Blo 1921435 7302545 := bstep (se 2 (by rfl) ⟨2738454, by rfl⟩ : syracuseStep 7302545 = 5476909) B5476909
theorem B4868363 : Blo 1921435 4868363 := bstep (se 1 (by rfl) ⟨3651272, by rfl⟩ : syracuseStep 4868363 = 7302545) B7302545
theorem B3245575 : Blo 1921435 3245575 := bstep (se 1 (by rfl) ⟨2434181, by rfl⟩ : syracuseStep 3245575 = 4868363) B4868363
theorem B4327433 : Blo 1921435 4327433 := bstep (se 2 (by rfl) ⟨1622787, by rfl⟩ : syracuseStep 4327433 = 3245575) B3245575
theorem B2884955 : Blo 1921435 2884955 := bstep (se 1 (by rfl) ⟨2163716, by rfl⟩ : syracuseStep 2884955 = 4327433) B4327433
theorem B1923303 : Blo 1921435 1923303 := bstep (se 1 (by rfl) ⟨1442477, by rfl⟩ : syracuseStep 1923303 = 2884955) B2884955
theorem B2163721 : Blo 1921435 2163721 := bbase (se 2 (by rfl) ⟨811395, by rfl⟩ : syracuseStep 2163721 = 1622791) (by norm_num)
theorem B2884961 : Blo 1921435 2884961 := bstep (se 2 (by rfl) ⟨1081860, by rfl⟩ : syracuseStep 2884961 = 2163721) B2163721
theorem B1923307 : Blo 1921435 1923307 := bstep (se 1 (by rfl) ⟨1442480, by rfl⟩ : syracuseStep 1923307 = 2884961) B2884961
theorem B11103317 : Blo 1921435 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B7402211 : Blo 1921435 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B4934807 : Blo 1921435 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B3289871 : Blo 1921435 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B2193247 : Blo 1921435 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B11697317 : Blo 1921435 11697317 := bstep (se 4 (by rfl) ⟨1096623, by rfl⟩ : syracuseStep 11697317 = 2193247) B2193247
theorem B7798211 : Blo 1921435 7798211 := bstep (se 1 (by rfl) ⟨5848658, by rfl⟩ : syracuseStep 7798211 = 11697317) B11697317
theorem B5198807 : Blo 1921435 5198807 := bstep (se 1 (by rfl) ⟨3899105, by rfl⟩ : syracuseStep 5198807 = 7798211) B7798211
theorem B3465871 : Blo 1921435 3465871 := bstep (se 1 (by rfl) ⟨2599403, by rfl⟩ : syracuseStep 3465871 = 5198807) B5198807
theorem B18484645 : Blo 1921435 18484645 := bstep (se 4 (by rfl) ⟨1732935, by rfl⟩ : syracuseStep 18484645 = 3465871) B3465871
theorem B24646193 : Blo 1921435 24646193 := bstep (se 2 (by rfl) ⟨9242322, by rfl⟩ : syracuseStep 24646193 = 18484645) B18484645
theorem B16430795 : Blo 1921435 16430795 := bstep (se 1 (by rfl) ⟨12323096, by rfl⟩ : syracuseStep 16430795 = 24646193) B24646193
theorem B10953863 : Blo 1921435 10953863 := bstep (se 1 (by rfl) ⟨8215397, by rfl⟩ : syracuseStep 10953863 = 16430795) B16430795
theorem B7302575 : Blo 1921435 7302575 := bstep (se 1 (by rfl) ⟨5476931, by rfl⟩ : syracuseStep 7302575 = 10953863) B10953863
theorem B4868383 : Blo 1921435 4868383 := bstep (se 1 (by rfl) ⟨3651287, by rfl⟩ : syracuseStep 4868383 = 7302575) B7302575
theorem B6491177 : Blo 1921435 6491177 := bstep (se 2 (by rfl) ⟨2434191, by rfl⟩ : syracuseStep 6491177 = 4868383) B4868383
theorem B4327451 : Blo 1921435 4327451 := bstep (se 1 (by rfl) ⟨3245588, by rfl⟩ : syracuseStep 4327451 = 6491177) B6491177
theorem B2884967 : Blo 1921435 2884967 := bstep (se 1 (by rfl) ⟨2163725, by rfl⟩ : syracuseStep 2884967 = 4327451) B4327451
theorem B1923311 : Blo 1921435 1923311 := bstep (se 1 (by rfl) ⟨1442483, by rfl⟩ : syracuseStep 1923311 = 2884967) B2884967
theorem B2884973 : Blo 1921435 2884973 := bbase (se 3 (by rfl) ⟨540932, by rfl⟩ : syracuseStep 2884973 = 1081865) (by norm_num)
theorem B1923315 : Blo 1921435 1923315 := bstep (se 1 (by rfl) ⟨1442486, by rfl⟩ : syracuseStep 1923315 = 2884973) B2884973
theorem B4327469 : Blo 1921435 4327469 := bbase (se 3 (by rfl) ⟨811400, by rfl⟩ : syracuseStep 4327469 = 1622801) (by norm_num)
theorem B2884979 : Blo 1921435 2884979 := bstep (se 1 (by rfl) ⟨2163734, by rfl⟩ : syracuseStep 2884979 = 4327469) B4327469
theorem B1923319 : Blo 1921435 1923319 := bstep (se 1 (by rfl) ⟨1442489, by rfl⟩ : syracuseStep 1923319 = 2884979) B2884979
theorem B31193045 : Blo 1921435 31193045 := bbase (se 7 (by rfl) ⟨365543, by rfl⟩ : syracuseStep 31193045 = 731087) (by norm_num)
theorem B20795363 : Blo 1921435 20795363 := bstep (se 1 (by rfl) ⟨15596522, by rfl⟩ : syracuseStep 20795363 = 31193045) B31193045
theorem B13863575 : Blo 1921435 13863575 := bstep (se 1 (by rfl) ⟨10397681, by rfl⟩ : syracuseStep 13863575 = 20795363) B20795363
theorem B9242383 : Blo 1921435 9242383 := bstep (se 1 (by rfl) ⟨6931787, by rfl⟩ : syracuseStep 9242383 = 13863575) B13863575
theorem B12323177 : Blo 1921435 12323177 := bstep (se 2 (by rfl) ⟨4621191, by rfl⟩ : syracuseStep 12323177 = 9242383) B9242383
theorem B8215451 : Blo 1921435 8215451 := bstep (se 1 (by rfl) ⟨6161588, by rfl⟩ : syracuseStep 8215451 = 12323177) B12323177
theorem B5476967 : Blo 1921435 5476967 := bstep (se 1 (by rfl) ⟨4107725, by rfl⟩ : syracuseStep 5476967 = 8215451) B8215451
theorem B3651311 : Blo 1921435 3651311 := bstep (se 1 (by rfl) ⟨2738483, by rfl⟩ : syracuseStep 3651311 = 5476967) B5476967
theorem B2434207 : Blo 1921435 2434207 := bstep (se 1 (by rfl) ⟨1825655, by rfl⟩ : syracuseStep 2434207 = 3651311) B3651311
theorem B3245609 : Blo 1921435 3245609 := bstep (se 2 (by rfl) ⟨1217103, by rfl⟩ : syracuseStep 3245609 = 2434207) B2434207
theorem B2163739 : Blo 1921435 2163739 := bstep (se 1 (by rfl) ⟨1622804, by rfl⟩ : syracuseStep 2163739 = 3245609) B3245609
theorem B2884985 : Blo 1921435 2884985 := bstep (se 2 (by rfl) ⟨1081869, by rfl⟩ : syracuseStep 2884985 = 2163739) B2163739
theorem B1923323 : Blo 1921435 1923323 := bstep (se 1 (by rfl) ⟨1442492, by rfl⟩ : syracuseStep 1923323 = 2884985) B2884985
theorem B2342125 : Blo 1921435 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B12491333 : Blo 1921435 12491333 := bstep (se 4 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 12491333 = 2342125) B2342125
theorem B8327555 : Blo 1921435 8327555 := bstep (se 1 (by rfl) ⟨6245666, by rfl⟩ : syracuseStep 8327555 = 12491333) B12491333
theorem B5551703 : Blo 1921435 5551703 := bstep (se 1 (by rfl) ⟨4163777, by rfl⟩ : syracuseStep 5551703 = 8327555) B8327555
theorem B3701135 : Blo 1921435 3701135 := bstep (se 1 (by rfl) ⟨2775851, by rfl⟩ : syracuseStep 3701135 = 5551703) B5551703
theorem B2467423 : Blo 1921435 2467423 := bstep (se 1 (by rfl) ⟨1850567, by rfl⟩ : syracuseStep 2467423 = 3701135) B3701135
theorem B13159589 : Blo 1921435 13159589 := bstep (se 4 (by rfl) ⟨1233711, by rfl⟩ : syracuseStep 13159589 = 2467423) B2467423
theorem B35092237 : Blo 1921435 35092237 := bstep (se 3 (by rfl) ⟨6579794, by rfl⟩ : syracuseStep 35092237 = 13159589) B13159589
theorem B46789649 : Blo 1921435 46789649 := bstep (se 2 (by rfl) ⟨17546118, by rfl⟩ : syracuseStep 46789649 = 35092237) B35092237
theorem B31193099 : Blo 1921435 31193099 := bstep (se 1 (by rfl) ⟨23394824, by rfl⟩ : syracuseStep 31193099 = 46789649) B46789649
theorem B20795399 : Blo 1921435 20795399 := bstep (se 1 (by rfl) ⟨15596549, by rfl⟩ : syracuseStep 20795399 = 31193099) B31193099
theorem B13863599 : Blo 1921435 13863599 := bstep (se 1 (by rfl) ⟨10397699, by rfl⟩ : syracuseStep 13863599 = 20795399) B20795399
theorem B9242399 : Blo 1921435 9242399 := bstep (se 1 (by rfl) ⟨6931799, by rfl⟩ : syracuseStep 9242399 = 13863599) B13863599
theorem B6161599 : Blo 1921435 6161599 := bstep (se 1 (by rfl) ⟨4621199, by rfl⟩ : syracuseStep 6161599 = 9242399) B9242399
theorem B32861861 : Blo 1921435 32861861 := bstep (se 4 (by rfl) ⟨3080799, by rfl⟩ : syracuseStep 32861861 = 6161599) B6161599
theorem B21907907 : Blo 1921435 21907907 := bstep (se 1 (by rfl) ⟨16430930, by rfl⟩ : syracuseStep 21907907 = 32861861) B32861861
theorem B14605271 : Blo 1921435 14605271 := bstep (se 1 (by rfl) ⟨10953953, by rfl⟩ : syracuseStep 14605271 = 21907907) B21907907
theorem B9736847 : Blo 1921435 9736847 := bstep (se 1 (by rfl) ⟨7302635, by rfl⟩ : syracuseStep 9736847 = 14605271) B14605271
theorem B6491231 : Blo 1921435 6491231 := bstep (se 1 (by rfl) ⟨4868423, by rfl⟩ : syracuseStep 6491231 = 9736847) B9736847
theorem B4327487 : Blo 1921435 4327487 := bstep (se 1 (by rfl) ⟨3245615, by rfl⟩ : syracuseStep 4327487 = 6491231) B6491231
theorem B2884991 : Blo 1921435 2884991 := bstep (se 1 (by rfl) ⟨2163743, by rfl⟩ : syracuseStep 2884991 = 4327487) B4327487
theorem B1923327 : Blo 1921435 1923327 := bstep (se 1 (by rfl) ⟨1442495, by rfl⟩ : syracuseStep 1923327 = 2884991) B2884991
theorem B2884997 : Blo 1921435 2884997 := bbase (se 4 (by rfl) ⟨270468, by rfl⟩ : syracuseStep 2884997 = 540937) (by norm_num)
theorem B1923331 : Blo 1921435 1923331 := bstep (se 1 (by rfl) ⟨1442498, by rfl⟩ : syracuseStep 1923331 = 2884997) B2884997
theorem B3245629 : Blo 1921435 3245629 := bbase (se 3 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 3245629 = 1217111) (by norm_num)
theorem B4327505 : Blo 1921435 4327505 := bstep (se 2 (by rfl) ⟨1622814, by rfl⟩ : syracuseStep 4327505 = 3245629) B3245629
theorem B2885003 : Blo 1921435 2885003 := bstep (se 1 (by rfl) ⟨2163752, by rfl⟩ : syracuseStep 2885003 = 4327505) B4327505
theorem B1923335 : Blo 1921435 1923335 := bstep (se 1 (by rfl) ⟨1442501, by rfl⟩ : syracuseStep 1923335 = 2885003) B2885003
theorem B2163757 : Blo 1921435 2163757 := bbase (se 3 (by rfl) ⟨405704, by rfl⟩ : syracuseStep 2163757 = 811409) (by norm_num)
theorem B2885009 : Blo 1921435 2885009 := bstep (se 2 (by rfl) ⟨1081878, by rfl⟩ : syracuseStep 2885009 = 2163757) B2163757
theorem B1923339 : Blo 1921435 1923339 := bstep (se 1 (by rfl) ⟨1442504, by rfl⟩ : syracuseStep 1923339 = 2885009) B2885009
theorem B6491285 : Blo 1921435 6491285 := bbase (se 6 (by rfl) ⟨152139, by rfl⟩ : syracuseStep 6491285 = 304279) (by norm_num)
theorem B4327523 : Blo 1921435 4327523 := bstep (se 1 (by rfl) ⟨3245642, by rfl⟩ : syracuseStep 4327523 = 6491285) B6491285
theorem B2885015 : Blo 1921435 2885015 := bstep (se 1 (by rfl) ⟨2163761, by rfl⟩ : syracuseStep 2885015 = 4327523) B4327523
theorem B1923343 : Blo 1921435 1923343 := bstep (se 1 (by rfl) ⟨1442507, by rfl⟩ : syracuseStep 1923343 = 2885015) B2885015
theorem B2885021 : Blo 1921435 2885021 := bbase (se 3 (by rfl) ⟨540941, by rfl⟩ : syracuseStep 2885021 = 1081883) (by norm_num)
theorem B1923347 : Blo 1921435 1923347 := bstep (se 1 (by rfl) ⟨1442510, by rfl⟩ : syracuseStep 1923347 = 2885021) B2885021
theorem B4327541 : Blo 1921435 4327541 := bbase (se 5 (by rfl) ⟨202853, by rfl⟩ : syracuseStep 4327541 = 405707) (by norm_num)
theorem B2885027 : Blo 1921435 2885027 := bstep (se 1 (by rfl) ⟨2163770, by rfl⟩ : syracuseStep 2885027 = 4327541) B4327541
theorem B1923351 : Blo 1921435 1923351 := bstep (se 1 (by rfl) ⟨1442513, by rfl⟩ : syracuseStep 1923351 = 2885027) B2885027
theorem B3080845 : Blo 1921435 3080845 := bbase (se 3 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 3080845 = 1155317) (by norm_num)
theorem B16431173 : Blo 1921435 16431173 := bstep (se 4 (by rfl) ⟨1540422, by rfl⟩ : syracuseStep 16431173 = 3080845) B3080845
theorem B10954115 : Blo 1921435 10954115 := bstep (se 1 (by rfl) ⟨8215586, by rfl⟩ : syracuseStep 10954115 = 16431173) B16431173
theorem B7302743 : Blo 1921435 7302743 := bstep (se 1 (by rfl) ⟨5477057, by rfl⟩ : syracuseStep 7302743 = 10954115) B10954115
theorem B4868495 : Blo 1921435 4868495 := bstep (se 1 (by rfl) ⟨3651371, by rfl⟩ : syracuseStep 4868495 = 7302743) B7302743
theorem B3245663 : Blo 1921435 3245663 := bstep (se 1 (by rfl) ⟨2434247, by rfl⟩ : syracuseStep 3245663 = 4868495) B4868495
theorem B2163775 : Blo 1921435 2163775 := bstep (se 1 (by rfl) ⟨1622831, by rfl⟩ : syracuseStep 2163775 = 3245663) B3245663
theorem B2885033 : Blo 1921435 2885033 := bstep (se 2 (by rfl) ⟨1081887, by rfl⟩ : syracuseStep 2885033 = 2163775) B2163775
theorem B1923355 : Blo 1921435 1923355 := bstep (se 1 (by rfl) ⟨1442516, by rfl⟩ : syracuseStep 1923355 = 2885033) B2885033
theorem B7302757 : Blo 1921435 7302757 := bbase (se 4 (by rfl) ⟨684633, by rfl⟩ : syracuseStep 7302757 = 1369267) (by norm_num)
theorem B9737009 : Blo 1921435 9737009 := bstep (se 2 (by rfl) ⟨3651378, by rfl⟩ : syracuseStep 9737009 = 7302757) B7302757
theorem B6491339 : Blo 1921435 6491339 := bstep (se 1 (by rfl) ⟨4868504, by rfl⟩ : syracuseStep 6491339 = 9737009) B9737009
theorem B4327559 : Blo 1921435 4327559 := bstep (se 1 (by rfl) ⟨3245669, by rfl⟩ : syracuseStep 4327559 = 6491339) B6491339
theorem B2885039 : Blo 1921435 2885039 := bstep (se 1 (by rfl) ⟨2163779, by rfl⟩ : syracuseStep 2885039 = 4327559) B4327559
theorem B1923359 : Blo 1921435 1923359 := bstep (se 1 (by rfl) ⟨1442519, by rfl⟩ : syracuseStep 1923359 = 2885039) B2885039
theorem B2885045 : Blo 1921435 2885045 := bbase (se 5 (by rfl) ⟨135236, by rfl⟩ : syracuseStep 2885045 = 270473) (by norm_num)
theorem B1923363 : Blo 1921435 1923363 := bstep (se 1 (by rfl) ⟨1442522, by rfl⟩ : syracuseStep 1923363 = 2885045) B2885045
theorem B4868525 : Blo 1921435 4868525 := bbase (se 3 (by rfl) ⟨912848, by rfl⟩ : syracuseStep 4868525 = 1825697) (by norm_num)
theorem B3245683 : Blo 1921435 3245683 := bstep (se 1 (by rfl) ⟨2434262, by rfl⟩ : syracuseStep 3245683 = 4868525) B4868525
theorem B4327577 : Blo 1921435 4327577 := bstep (se 2 (by rfl) ⟨1622841, by rfl⟩ : syracuseStep 4327577 = 3245683) B3245683
theorem B2885051 : Blo 1921435 2885051 := bstep (se 1 (by rfl) ⟨2163788, by rfl⟩ : syracuseStep 2885051 = 4327577) B4327577
theorem B1923367 : Blo 1921435 1923367 := bstep (se 1 (by rfl) ⟨1442525, by rfl⟩ : syracuseStep 1923367 = 2885051) B2885051
theorem B2163793 : Blo 1921435 2163793 := bbase (se 2 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 2163793 = 1622845) (by norm_num)
theorem B2885057 : Blo 1921435 2885057 := bstep (se 2 (by rfl) ⟨1081896, by rfl⟩ : syracuseStep 2885057 = 2163793) B2163793
theorem B1923371 : Blo 1921435 1923371 := bstep (se 1 (by rfl) ⟨1442528, by rfl⟩ : syracuseStep 1923371 = 2885057) B2885057
theorem B2738557 : Blo 1921435 2738557 := bbase (se 3 (by rfl) ⟨513479, by rfl⟩ : syracuseStep 2738557 = 1026959) (by norm_num)
theorem B3651409 : Blo 1921435 3651409 := bstep (se 2 (by rfl) ⟨1369278, by rfl⟩ : syracuseStep 3651409 = 2738557) B2738557
theorem B4868545 : Blo 1921435 4868545 := bstep (se 2 (by rfl) ⟨1825704, by rfl⟩ : syracuseStep 4868545 = 3651409) B3651409
theorem B6491393 : Blo 1921435 6491393 := bstep (se 2 (by rfl) ⟨2434272, by rfl⟩ : syracuseStep 6491393 = 4868545) B4868545
theorem B4327595 : Blo 1921435 4327595 := bstep (se 1 (by rfl) ⟨3245696, by rfl⟩ : syracuseStep 4327595 = 6491393) B6491393
theorem B2885063 : Blo 1921435 2885063 := bstep (se 1 (by rfl) ⟨2163797, by rfl⟩ : syracuseStep 2885063 = 4327595) B4327595
theorem B1923375 : Blo 1921435 1923375 := bstep (se 1 (by rfl) ⟨1442531, by rfl⟩ : syracuseStep 1923375 = 2885063) B2885063
theorem B2885069 : Blo 1921435 2885069 := bbase (se 3 (by rfl) ⟨540950, by rfl⟩ : syracuseStep 2885069 = 1081901) (by norm_num)
theorem B1923379 : Blo 1921435 1923379 := bstep (se 1 (by rfl) ⟨1442534, by rfl⟩ : syracuseStep 1923379 = 2885069) B2885069
theorem B4327613 : Blo 1921435 4327613 := bbase (se 3 (by rfl) ⟨811427, by rfl⟩ : syracuseStep 4327613 = 1622855) (by norm_num)
theorem B2885075 : Blo 1921435 2885075 := bstep (se 1 (by rfl) ⟨2163806, by rfl⟩ : syracuseStep 2885075 = 4327613) B4327613
theorem B1923383 : Blo 1921435 1923383 := bstep (se 1 (by rfl) ⟨1442537, by rfl⟩ : syracuseStep 1923383 = 2885075) B2885075
theorem B3245717 : Blo 1921435 3245717 := bbase (se 6 (by rfl) ⟨76071, by rfl⟩ : syracuseStep 3245717 = 152143) (by norm_num)
theorem B2163811 : Blo 1921435 2163811 := bstep (se 1 (by rfl) ⟨1622858, by rfl⟩ : syracuseStep 2163811 = 3245717) B3245717
theorem B2885081 : Blo 1921435 2885081 := bstep (se 2 (by rfl) ⟨1081905, by rfl⟩ : syracuseStep 2885081 = 2163811) B2163811
theorem B1923387 : Blo 1921435 1923387 := bstep (se 1 (by rfl) ⟨1442540, by rfl⟩ : syracuseStep 1923387 = 2885081) B2885081
theorem B7402517 : Blo 1921435 7402517 := bbase (se 6 (by rfl) ⟨173496, by rfl⟩ : syracuseStep 7402517 = 346993) (by norm_num)
theorem B4935011 : Blo 1921435 4935011 := bstep (se 1 (by rfl) ⟨3701258, by rfl⟩ : syracuseStep 4935011 = 7402517) B7402517
theorem B13160029 : Blo 1921435 13160029 := bstep (se 3 (by rfl) ⟨2467505, by rfl⟩ : syracuseStep 13160029 = 4935011) B4935011
theorem B17546705 : Blo 1921435 17546705 := bstep (se 2 (by rfl) ⟨6580014, by rfl⟩ : syracuseStep 17546705 = 13160029) B13160029
theorem B11697803 : Blo 1921435 11697803 := bstep (se 1 (by rfl) ⟨8773352, by rfl⟩ : syracuseStep 11697803 = 17546705) B17546705
theorem B7798535 : Blo 1921435 7798535 := bstep (se 1 (by rfl) ⟨5848901, by rfl⟩ : syracuseStep 7798535 = 11697803) B11697803
theorem B5199023 : Blo 1921435 5199023 := bstep (se 1 (by rfl) ⟨3899267, by rfl⟩ : syracuseStep 5199023 = 7798535) B7798535
theorem B13864061 : Blo 1921435 13864061 := bstep (se 3 (by rfl) ⟨2599511, by rfl⟩ : syracuseStep 13864061 = 5199023) B5199023
theorem B9242707 : Blo 1921435 9242707 := bstep (se 1 (by rfl) ⟨6932030, by rfl⟩ : syracuseStep 9242707 = 13864061) B13864061
theorem B12323609 : Blo 1921435 12323609 := bstep (se 2 (by rfl) ⟨4621353, by rfl⟩ : syracuseStep 12323609 = 9242707) B9242707
theorem B8215739 : Blo 1921435 8215739 := bstep (se 1 (by rfl) ⟨6161804, by rfl⟩ : syracuseStep 8215739 = 12323609) B12323609
theorem B5477159 : Blo 1921435 5477159 := bstep (se 1 (by rfl) ⟨4107869, by rfl⟩ : syracuseStep 5477159 = 8215739) B8215739
theorem B14605757 : Blo 1921435 14605757 := bstep (se 3 (by rfl) ⟨2738579, by rfl⟩ : syracuseStep 14605757 = 5477159) B5477159
theorem B9737171 : Blo 1921435 9737171 := bstep (se 1 (by rfl) ⟨7302878, by rfl⟩ : syracuseStep 9737171 = 14605757) B14605757
theorem B6491447 : Blo 1921435 6491447 := bstep (se 1 (by rfl) ⟨4868585, by rfl⟩ : syracuseStep 6491447 = 9737171) B9737171
theorem B4327631 : Blo 1921435 4327631 := bstep (se 1 (by rfl) ⟨3245723, by rfl⟩ : syracuseStep 4327631 = 6491447) B6491447
theorem B2885087 : Blo 1921435 2885087 := bstep (se 1 (by rfl) ⟨2163815, by rfl⟩ : syracuseStep 2885087 = 4327631) B4327631
theorem B1923391 : Blo 1921435 1923391 := bstep (se 1 (by rfl) ⟨1442543, by rfl⟩ : syracuseStep 1923391 = 2885087) B2885087
theorem B2885093 : Blo 1921435 2885093 := bbase (se 4 (by rfl) ⟨270477, by rfl⟩ : syracuseStep 2885093 = 540955) (by norm_num)
theorem B1923395 : Blo 1921435 1923395 := bstep (se 1 (by rfl) ⟨1442546, by rfl⟩ : syracuseStep 1923395 = 2885093) B2885093
theorem B7402549 : Blo 1921435 7402549 := bbase (se 5 (by rfl) ⟨346994, by rfl⟩ : syracuseStep 7402549 = 693989) (by norm_num)
theorem B9870065 : Blo 1921435 9870065 := bstep (se 2 (by rfl) ⟨3701274, by rfl⟩ : syracuseStep 9870065 = 7402549) B7402549
theorem B6580043 : Blo 1921435 6580043 := bstep (se 1 (by rfl) ⟨4935032, by rfl⟩ : syracuseStep 6580043 = 9870065) B9870065
theorem B4386695 : Blo 1921435 4386695 := bstep (se 1 (by rfl) ⟨3290021, by rfl⟩ : syracuseStep 4386695 = 6580043) B6580043
theorem B11697853 : Blo 1921435 11697853 := bstep (se 3 (by rfl) ⟨2193347, by rfl⟩ : syracuseStep 11697853 = 4386695) B4386695
theorem B15597137 : Blo 1921435 15597137 := bstep (se 2 (by rfl) ⟨5848926, by rfl⟩ : syracuseStep 15597137 = 11697853) B11697853
theorem B41592365 : Blo 1921435 41592365 := bstep (se 3 (by rfl) ⟨7798568, by rfl⟩ : syracuseStep 41592365 = 15597137) B15597137
theorem B27728243 : Blo 1921435 27728243 := bstep (se 1 (by rfl) ⟨20796182, by rfl⟩ : syracuseStep 27728243 = 41592365) B41592365
theorem B18485495 : Blo 1921435 18485495 := bstep (se 1 (by rfl) ⟨13864121, by rfl⟩ : syracuseStep 18485495 = 27728243) B27728243
theorem B12323663 : Blo 1921435 12323663 := bstep (se 1 (by rfl) ⟨9242747, by rfl⟩ : syracuseStep 12323663 = 18485495) B18485495
theorem B8215775 : Blo 1921435 8215775 := bstep (se 1 (by rfl) ⟨6161831, by rfl⟩ : syracuseStep 8215775 = 12323663) B12323663
theorem B5477183 : Blo 1921435 5477183 := bstep (se 1 (by rfl) ⟨4107887, by rfl⟩ : syracuseStep 5477183 = 8215775) B8215775
theorem B3651455 : Blo 1921435 3651455 := bstep (se 1 (by rfl) ⟨2738591, by rfl⟩ : syracuseStep 3651455 = 5477183) B5477183
theorem B2434303 : Blo 1921435 2434303 := bstep (se 1 (by rfl) ⟨1825727, by rfl⟩ : syracuseStep 2434303 = 3651455) B3651455
theorem B3245737 : Blo 1921435 3245737 := bstep (se 2 (by rfl) ⟨1217151, by rfl⟩ : syracuseStep 3245737 = 2434303) B2434303
theorem B4327649 : Blo 1921435 4327649 := bstep (se 2 (by rfl) ⟨1622868, by rfl⟩ : syracuseStep 4327649 = 3245737) B3245737
theorem B2885099 : Blo 1921435 2885099 := bstep (se 1 (by rfl) ⟨2163824, by rfl⟩ : syracuseStep 2885099 = 4327649) B4327649
theorem B1923399 : Blo 1921435 1923399 := bstep (se 1 (by rfl) ⟨1442549, by rfl⟩ : syracuseStep 1923399 = 2885099) B2885099
theorem B2163829 : Blo 1921435 2163829 := bbase (se 5 (by rfl) ⟨101429, by rfl⟩ : syracuseStep 2163829 = 202859) (by norm_num)
theorem B2885105 : Blo 1921435 2885105 := bstep (se 2 (by rfl) ⟨1081914, by rfl⟩ : syracuseStep 2885105 = 2163829) B2163829
theorem B1923403 : Blo 1921435 1923403 := bstep (se 1 (by rfl) ⟨1442552, by rfl⟩ : syracuseStep 1923403 = 2885105) B2885105
theorem B2434313 : Blo 1921435 2434313 := bbase (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) (by norm_num)
theorem B6491501 : Blo 1921435 6491501 := bstep (se 3 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 6491501 = 2434313) B2434313
theorem B4327667 : Blo 1921435 4327667 := bstep (se 1 (by rfl) ⟨3245750, by rfl⟩ : syracuseStep 4327667 = 6491501) B6491501
theorem B2885111 : Blo 1921435 2885111 := bstep (se 1 (by rfl) ⟨2163833, by rfl⟩ : syracuseStep 2885111 = 4327667) B4327667
theorem B1923407 : Blo 1921435 1923407 := bstep (se 1 (by rfl) ⟨1442555, by rfl⟩ : syracuseStep 1923407 = 2885111) B2885111
theorem B2885117 : Blo 1921435 2885117 := bbase (se 3 (by rfl) ⟨540959, by rfl⟩ : syracuseStep 2885117 = 1081919) (by norm_num)
theorem B1923411 : Blo 1921435 1923411 := bstep (se 1 (by rfl) ⟨1442558, by rfl⟩ : syracuseStep 1923411 = 2885117) B2885117
theorem B4327685 : Blo 1921435 4327685 := bbase (se 4 (by rfl) ⟨405720, by rfl⟩ : syracuseStep 4327685 = 811441) (by norm_num)
theorem B2885123 : Blo 1921435 2885123 := bstep (se 1 (by rfl) ⟨2163842, by rfl⟩ : syracuseStep 2885123 = 4327685) B4327685
theorem B1923415 : Blo 1921435 1923415 := bstep (se 1 (by rfl) ⟨1442561, by rfl⟩ : syracuseStep 1923415 = 2885123) B2885123
theorem B3651493 : Blo 1921435 3651493 := bbase (se 4 (by rfl) ⟨342327, by rfl⟩ : syracuseStep 3651493 = 684655) (by norm_num)
theorem B4868657 : Blo 1921435 4868657 := bstep (se 2 (by rfl) ⟨1825746, by rfl⟩ : syracuseStep 4868657 = 3651493) B3651493
theorem B3245771 : Blo 1921435 3245771 := bstep (se 1 (by rfl) ⟨2434328, by rfl⟩ : syracuseStep 3245771 = 4868657) B4868657
theorem B2163847 : Blo 1921435 2163847 := bstep (se 1 (by rfl) ⟨1622885, by rfl⟩ : syracuseStep 2163847 = 3245771) B3245771
theorem B2885129 : Blo 1921435 2885129 := bstep (se 2 (by rfl) ⟨1081923, by rfl⟩ : syracuseStep 2885129 = 2163847) B2163847
theorem B1923419 : Blo 1921435 1923419 := bstep (se 1 (by rfl) ⟨1442564, by rfl⟩ : syracuseStep 1923419 = 2885129) B2885129
theorem B9737333 : Blo 1921435 9737333 := bbase (se 5 (by rfl) ⟨456437, by rfl⟩ : syracuseStep 9737333 = 912875) (by norm_num)
theorem B6491555 : Blo 1921435 6491555 := bstep (se 1 (by rfl) ⟨4868666, by rfl⟩ : syracuseStep 6491555 = 9737333) B9737333
theorem B4327703 : Blo 1921435 4327703 := bstep (se 1 (by rfl) ⟨3245777, by rfl⟩ : syracuseStep 4327703 = 6491555) B6491555
theorem B2885135 : Blo 1921435 2885135 := bstep (se 1 (by rfl) ⟨2163851, by rfl⟩ : syracuseStep 2885135 = 4327703) B4327703
theorem B1923423 : Blo 1921435 1923423 := bstep (se 1 (by rfl) ⟨1442567, by rfl⟩ : syracuseStep 1923423 = 2885135) B2885135
theorem B2885141 : Blo 1921435 2885141 := bbase (se 6 (by rfl) ⟨67620, by rfl⟩ : syracuseStep 2885141 = 135241) (by norm_num)
theorem B1923427 : Blo 1921435 1923427 := bstep (se 1 (by rfl) ⟨1442570, by rfl⟩ : syracuseStep 1923427 = 2885141) B2885141
theorem B2310725 : Blo 1921435 2310725 := bbase (se 4 (by rfl) ⟨216630, by rfl⟩ : syracuseStep 2310725 = 433261) (by norm_num)
theorem B6161933 : Blo 1921435 6161933 := bstep (se 3 (by rfl) ⟨1155362, by rfl⟩ : syracuseStep 6161933 = 2310725) B2310725
theorem B16431821 : Blo 1921435 16431821 := bstep (se 3 (by rfl) ⟨3080966, by rfl⟩ : syracuseStep 16431821 = 6161933) B6161933
theorem B10954547 : Blo 1921435 10954547 := bstep (se 1 (by rfl) ⟨8215910, by rfl⟩ : syracuseStep 10954547 = 16431821) B16431821
theorem B7303031 : Blo 1921435 7303031 := bstep (se 1 (by rfl) ⟨5477273, by rfl⟩ : syracuseStep 7303031 = 10954547) B10954547
theorem B4868687 : Blo 1921435 4868687 := bstep (se 1 (by rfl) ⟨3651515, by rfl⟩ : syracuseStep 4868687 = 7303031) B7303031
theorem B3245791 : Blo 1921435 3245791 := bstep (se 1 (by rfl) ⟨2434343, by rfl⟩ : syracuseStep 3245791 = 4868687) B4868687
theorem B4327721 : Blo 1921435 4327721 := bstep (se 2 (by rfl) ⟨1622895, by rfl⟩ : syracuseStep 4327721 = 3245791) B3245791
theorem B2885147 : Blo 1921435 2885147 := bstep (se 1 (by rfl) ⟨2163860, by rfl⟩ : syracuseStep 2885147 = 4327721) B4327721
theorem B1923431 : Blo 1921435 1923431 := bstep (se 1 (by rfl) ⟨1442573, by rfl⟩ : syracuseStep 1923431 = 2885147) B2885147
theorem B2163865 : Blo 1921435 2163865 := bbase (se 2 (by rfl) ⟨811449, by rfl⟩ : syracuseStep 2163865 = 1622899) (by norm_num)
theorem B2885153 : Blo 1921435 2885153 := bstep (se 2 (by rfl) ⟨1081932, by rfl⟩ : syracuseStep 2885153 = 2163865) B2163865
theorem B1923435 : Blo 1921435 1923435 := bstep (se 1 (by rfl) ⟨1442576, by rfl⟩ : syracuseStep 1923435 = 2885153) B2885153
theorem C0 (j : ℕ) (h1 : 480358 ≤ j) (h2 : j ≤ 480858) : Blo 1921435 (4 * j + 3) := by
  interval_cases j
  · exact B1921435
  · exact B1921439
  · exact B1921443
  · exact B1921447
  · exact B1921451
  · exact B1921455
  · exact B1921459
  · exact B1921463
  · exact B1921467
  · exact B1921471
  · exact B1921475
  · exact B1921479
  · exact B1921483
  · exact B1921487
  · exact B1921491
  · exact B1921495
  · exact B1921499
  · exact B1921503
  · exact B1921507
  · exact B1921511
  · exact B1921515
  · exact B1921519
  · exact B1921523
  · exact B1921527
  · exact B1921531
  · exact B1921535
  · exact B1921539
  · exact B1921543
  · exact B1921547
  · exact B1921551
  · exact B1921555
  · exact B1921559
  · exact B1921563
  · exact B1921567
  · exact B1921571
  · exact B1921575
  · exact B1921579
  · exact B1921583
  · exact B1921587
  · exact B1921591
  · exact B1921595
  · exact B1921599
  · exact B1921603
  · exact B1921607
  · exact B1921611
  · exact B1921615
  · exact B1921619
  · exact B1921623
  · exact B1921627
  · exact B1921631
  · exact B1921635
  · exact B1921639
  · exact B1921643
  · exact B1921647
  · exact B1921651
  · exact B1921655
  · exact B1921659
  · exact B1921663
  · exact B1921667
  · exact B1921671
  · exact B1921675
  · exact B1921679
  · exact B1921683
  · exact B1921687
  · exact B1921691
  · exact B1921695
  · exact B1921699
  · exact B1921703
  · exact B1921707
  · exact B1921711
  · exact B1921715
  · exact B1921719
  · exact B1921723
  · exact B1921727
  · exact B1921731
  · exact B1921735
  · exact B1921739
  · exact B1921743
  · exact B1921747
  · exact B1921751
  · exact B1921755
  · exact B1921759
  · exact B1921763
  · exact B1921767
  · exact B1921771
  · exact B1921775
  · exact B1921779
  · exact B1921783
  · exact B1921787
  · exact B1921791
  · exact B1921795
  · exact B1921799
  · exact B1921803
  · exact B1921807
  · exact B1921811
  · exact B1921815
  · exact B1921819
  · exact B1921823
  · exact B1921827
  · exact B1921831
  · exact B1921835
  · exact B1921839
  · exact B1921843
  · exact B1921847
  · exact B1921851
  · exact B1921855
  · exact B1921859
  · exact B1921863
  · exact B1921867
  · exact B1921871
  · exact B1921875
  · exact B1921879
  · exact B1921883
  · exact B1921887
  · exact B1921891
  · exact B1921895
  · exact B1921899
  · exact B1921903
  · exact B1921907
  · exact B1921911
  · exact B1921915
  · exact B1921919
  · exact B1921923
  · exact B1921927
  · exact B1921931
  · exact B1921935
  · exact B1921939
  · exact B1921943
  · exact B1921947
  · exact B1921951
  · exact B1921955
  · exact B1921959
  · exact B1921963
  · exact B1921967
  · exact B1921971
  · exact B1921975
  · exact B1921979
  · exact B1921983
  · exact B1921987
  · exact B1921991
  · exact B1921995
  · exact B1921999
  · exact B1922003
  · exact B1922007
  · exact B1922011
  · exact B1922015
  · exact B1922019
  · exact B1922023
  · exact B1922027
  · exact B1922031
  · exact B1922035
  · exact B1922039
  · exact B1922043
  · exact B1922047
  · exact B1922051
  · exact B1922055
  · exact B1922059
  · exact B1922063
  · exact B1922067
  · exact B1922071
  · exact B1922075
  · exact B1922079
  · exact B1922083
  · exact B1922087
  · exact B1922091
  · exact B1922095
  · exact B1922099
  · exact B1922103
  · exact B1922107
  · exact B1922111
  · exact B1922115
  · exact B1922119
  · exact B1922123
  · exact B1922127
  · exact B1922131
  · exact B1922135
  · exact B1922139
  · exact B1922143
  · exact B1922147
  · exact B1922151
  · exact B1922155
  · exact B1922159
  · exact B1922163
  · exact B1922167
  · exact B1922171
  · exact B1922175
  · exact B1922179
  · exact B1922183
  · exact B1922187
  · exact B1922191
  · exact B1922195
  · exact B1922199
  · exact B1922203
  · exact B1922207
  · exact B1922211
  · exact B1922215
  · exact B1922219
  · exact B1922223
  · exact B1922227
  · exact B1922231
  · exact B1922235
  · exact B1922239
  · exact B1922243
  · exact B1922247
  · exact B1922251
  · exact B1922255
  · exact B1922259
  · exact B1922263
  · exact B1922267
  · exact B1922271
  · exact B1922275
  · exact B1922279
  · exact B1922283
  · exact B1922287
  · exact B1922291
  · exact B1922295
  · exact B1922299
  · exact B1922303
  · exact B1922307
  · exact B1922311
  · exact B1922315
  · exact B1922319
  · exact B1922323
  · exact B1922327
  · exact B1922331
  · exact B1922335
  · exact B1922339
  · exact B1922343
  · exact B1922347
  · exact B1922351
  · exact B1922355
  · exact B1922359
  · exact B1922363
  · exact B1922367
  · exact B1922371
  · exact B1922375
  · exact B1922379
  · exact B1922383
  · exact B1922387
  · exact B1922391
  · exact B1922395
  · exact B1922399
  · exact B1922403
  · exact B1922407
  · exact B1922411
  · exact B1922415
  · exact B1922419
  · exact B1922423
  · exact B1922427
  · exact B1922431
  · exact B1922435
  · exact B1922439
  · exact B1922443
  · exact B1922447
  · exact B1922451
  · exact B1922455
  · exact B1922459
  · exact B1922463
  · exact B1922467
  · exact B1922471
  · exact B1922475
  · exact B1922479
  · exact B1922483
  · exact B1922487
  · exact B1922491
  · exact B1922495
  · exact B1922499
  · exact B1922503
  · exact B1922507
  · exact B1922511
  · exact B1922515
  · exact B1922519
  · exact B1922523
  · exact B1922527
  · exact B1922531
  · exact B1922535
  · exact B1922539
  · exact B1922543
  · exact B1922547
  · exact B1922551
  · exact B1922555
  · exact B1922559
  · exact B1922563
  · exact B1922567
  · exact B1922571
  · exact B1922575
  · exact B1922579
  · exact B1922583
  · exact B1922587
  · exact B1922591
  · exact B1922595
  · exact B1922599
  · exact B1922603
  · exact B1922607
  · exact B1922611
  · exact B1922615
  · exact B1922619
  · exact B1922623
  · exact B1922627
  · exact B1922631
  · exact B1922635
  · exact B1922639
  · exact B1922643
  · exact B1922647
  · exact B1922651
  · exact B1922655
  · exact B1922659
  · exact B1922663
  · exact B1922667
  · exact B1922671
  · exact B1922675
  · exact B1922679
  · exact B1922683
  · exact B1922687
  · exact B1922691
  · exact B1922695
  · exact B1922699
  · exact B1922703
  · exact B1922707
  · exact B1922711
  · exact B1922715
  · exact B1922719
  · exact B1922723
  · exact B1922727
  · exact B1922731
  · exact B1922735
  · exact B1922739
  · exact B1922743
  · exact B1922747
  · exact B1922751
  · exact B1922755
  · exact B1922759
  · exact B1922763
  · exact B1922767
  · exact B1922771
  · exact B1922775
  · exact B1922779
  · exact B1922783
  · exact B1922787
  · exact B1922791
  · exact B1922795
  · exact B1922799
  · exact B1922803
  · exact B1922807
  · exact B1922811
  · exact B1922815
  · exact B1922819
  · exact B1922823
  · exact B1922827
  · exact B1922831
  · exact B1922835
  · exact B1922839
  · exact B1922843
  · exact B1922847
  · exact B1922851
  · exact B1922855
  · exact B1922859
  · exact B1922863
  · exact B1922867
  · exact B1922871
  · exact B1922875
  · exact B1922879
  · exact B1922883
  · exact B1922887
  · exact B1922891
  · exact B1922895
  · exact B1922899
  · exact B1922903
  · exact B1922907
  · exact B1922911
  · exact B1922915
  · exact B1922919
  · exact B1922923
  · exact B1922927
  · exact B1922931
  · exact B1922935
  · exact B1922939
  · exact B1922943
  · exact B1922947
  · exact B1922951
  · exact B1922955
  · exact B1922959
  · exact B1922963
  · exact B1922967
  · exact B1922971
  · exact B1922975
  · exact B1922979
  · exact B1922983
  · exact B1922987
  · exact B1922991
  · exact B1922995
  · exact B1922999
  · exact B1923003
  · exact B1923007
  · exact B1923011
  · exact B1923015
  · exact B1923019
  · exact B1923023
  · exact B1923027
  · exact B1923031
  · exact B1923035
  · exact B1923039
  · exact B1923043
  · exact B1923047
  · exact B1923051
  · exact B1923055
  · exact B1923059
  · exact B1923063
  · exact B1923067
  · exact B1923071
  · exact B1923075
  · exact B1923079
  · exact B1923083
  · exact B1923087
  · exact B1923091
  · exact B1923095
  · exact B1923099
  · exact B1923103
  · exact B1923107
  · exact B1923111
  · exact B1923115
  · exact B1923119
  · exact B1923123
  · exact B1923127
  · exact B1923131
  · exact B1923135
  · exact B1923139
  · exact B1923143
  · exact B1923147
  · exact B1923151
  · exact B1923155
  · exact B1923159
  · exact B1923163
  · exact B1923167
  · exact B1923171
  · exact B1923175
  · exact B1923179
  · exact B1923183
  · exact B1923187
  · exact B1923191
  · exact B1923195
  · exact B1923199
  · exact B1923203
  · exact B1923207
  · exact B1923211
  · exact B1923215
  · exact B1923219
  · exact B1923223
  · exact B1923227
  · exact B1923231
  · exact B1923235
  · exact B1923239
  · exact B1923243
  · exact B1923247
  · exact B1923251
  · exact B1923255
  · exact B1923259
  · exact B1923263
  · exact B1923267
  · exact B1923271
  · exact B1923275
  · exact B1923279
  · exact B1923283
  · exact B1923287
  · exact B1923291
  · exact B1923295
  · exact B1923299
  · exact B1923303
  · exact B1923307
  · exact B1923311
  · exact B1923315
  · exact B1923319
  · exact B1923323
  · exact B1923327
  · exact B1923331
  · exact B1923335
  · exact B1923339
  · exact B1923343
  · exact B1923347
  · exact B1923351
  · exact B1923355
  · exact B1923359
  · exact B1923363
  · exact B1923367
  · exact B1923371
  · exact B1923375
  · exact B1923379
  · exact B1923383
  · exact B1923387
  · exact B1923391
  · exact B1923395
  · exact B1923399
  · exact B1923403
  · exact B1923407
  · exact B1923411
  · exact B1923415
  · exact B1923419
  · exact B1923423
  · exact B1923427
  · exact B1923431
  · exact B1923435
theorem solution (m : ℕ) (hlo : 1921435 ≤ m) (hhi : m ≤ 1923435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 480358 ≤ j := by omega
    have hj2 : j ≤ 480858 := by omega
    have hb : Blo 1921435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
