-- Prove2me | solution 1 for syracuse_descends_range_2261435_2263435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:18.585998+00:00
-- url     : https://prove2.me/submissions/72f46a52-d36f-46db-add0-8ac70418ba17

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

theorem B3816173 : Blo 2261435 3816173 := bbase (se 3 (by rfl) ⟨715532, by rfl⟩ : syracuseStep 3816173 = 1431065) (by norm_num)
theorem B2544115 : Blo 2261435 2544115 := bstep (se 1 (by rfl) ⟨1908086, by rfl⟩ : syracuseStep 2544115 = 3816173) B3816173
theorem B3392153 : Blo 2261435 3392153 := bstep (se 2 (by rfl) ⟨1272057, by rfl⟩ : syracuseStep 3392153 = 2544115) B2544115
theorem B2261435 : Blo 2261435 2261435 := bstep (se 1 (by rfl) ⟨1696076, by rfl⟩ : syracuseStep 2261435 = 3392153) B3392153
theorem B20630645 : Blo 2261435 20630645 := bbase (se 5 (by rfl) ⟨967061, by rfl⟩ : syracuseStep 20630645 = 1934123) (by norm_num)
theorem B13753763 : Blo 2261435 13753763 := bstep (se 1 (by rfl) ⟨10315322, by rfl⟩ : syracuseStep 13753763 = 20630645) B20630645
theorem B9169175 : Blo 2261435 9169175 := bstep (se 1 (by rfl) ⟨6876881, by rfl⟩ : syracuseStep 9169175 = 13753763) B13753763
theorem B6112783 : Blo 2261435 6112783 := bstep (se 1 (by rfl) ⟨4584587, by rfl⟩ : syracuseStep 6112783 = 9169175) B9169175
theorem B8150377 : Blo 2261435 8150377 := bstep (se 2 (by rfl) ⟨3056391, by rfl⟩ : syracuseStep 8150377 = 6112783) B6112783
theorem B10867169 : Blo 2261435 10867169 := bstep (se 2 (by rfl) ⟨4075188, by rfl⟩ : syracuseStep 10867169 = 8150377) B8150377
theorem B28979117 : Blo 2261435 28979117 := bstep (se 3 (by rfl) ⟨5433584, by rfl⟩ : syracuseStep 28979117 = 10867169) B10867169
theorem B19319411 : Blo 2261435 19319411 := bstep (se 1 (by rfl) ⟨14489558, by rfl⟩ : syracuseStep 19319411 = 28979117) B28979117
theorem B12879607 : Blo 2261435 12879607 := bstep (se 1 (by rfl) ⟨9659705, by rfl⟩ : syracuseStep 12879607 = 19319411) B19319411
theorem B17172809 : Blo 2261435 17172809 := bstep (se 2 (by rfl) ⟨6439803, by rfl⟩ : syracuseStep 17172809 = 12879607) B12879607
theorem B11448539 : Blo 2261435 11448539 := bstep (se 1 (by rfl) ⟨8586404, by rfl⟩ : syracuseStep 11448539 = 17172809) B17172809
theorem B7632359 : Blo 2261435 7632359 := bstep (se 1 (by rfl) ⟨5724269, by rfl⟩ : syracuseStep 7632359 = 11448539) B11448539
theorem B5088239 : Blo 2261435 5088239 := bstep (se 1 (by rfl) ⟨3816179, by rfl⟩ : syracuseStep 5088239 = 7632359) B7632359
theorem B3392159 : Blo 2261435 3392159 := bstep (se 1 (by rfl) ⟨2544119, by rfl⟩ : syracuseStep 3392159 = 5088239) B5088239
theorem B2261439 : Blo 2261435 2261439 := bstep (se 1 (by rfl) ⟨1696079, by rfl⟩ : syracuseStep 2261439 = 3392159) B3392159
theorem B3392165 : Blo 2261435 3392165 := bbase (se 4 (by rfl) ⟨318015, by rfl⟩ : syracuseStep 3392165 = 636031) (by norm_num)
theorem B2261443 : Blo 2261435 2261443 := bstep (se 1 (by rfl) ⟨1696082, by rfl⟩ : syracuseStep 2261443 = 3392165) B3392165
theorem B2862145 : Blo 2261435 2862145 := bbase (se 2 (by rfl) ⟨1073304, by rfl⟩ : syracuseStep 2862145 = 2146609) (by norm_num)
theorem B3816193 : Blo 2261435 3816193 := bstep (se 2 (by rfl) ⟨1431072, by rfl⟩ : syracuseStep 3816193 = 2862145) B2862145
theorem B5088257 : Blo 2261435 5088257 := bstep (se 2 (by rfl) ⟨1908096, by rfl⟩ : syracuseStep 5088257 = 3816193) B3816193
theorem B3392171 : Blo 2261435 3392171 := bstep (se 1 (by rfl) ⟨2544128, by rfl⟩ : syracuseStep 3392171 = 5088257) B5088257
theorem B2261447 : Blo 2261435 2261447 := bstep (se 1 (by rfl) ⟨1696085, by rfl⟩ : syracuseStep 2261447 = 3392171) B3392171
theorem B2544133 : Blo 2261435 2544133 := bbase (se 4 (by rfl) ⟨238512, by rfl⟩ : syracuseStep 2544133 = 477025) (by norm_num)
theorem B3392177 : Blo 2261435 3392177 := bstep (se 2 (by rfl) ⟨1272066, by rfl⟩ : syracuseStep 3392177 = 2544133) B2544133
theorem B2261451 : Blo 2261435 2261451 := bstep (se 1 (by rfl) ⟨1696088, by rfl⟩ : syracuseStep 2261451 = 3392177) B3392177
theorem B3219925 : Blo 2261435 3219925 := bbase (se 7 (by rfl) ⟨37733, by rfl⟩ : syracuseStep 3219925 = 75467) (by norm_num)
theorem B4293233 : Blo 2261435 4293233 := bstep (se 2 (by rfl) ⟨1609962, by rfl⟩ : syracuseStep 4293233 = 3219925) B3219925
theorem B2862155 : Blo 2261435 2862155 := bstep (se 1 (by rfl) ⟨2146616, by rfl⟩ : syracuseStep 2862155 = 4293233) B4293233
theorem B7632413 : Blo 2261435 7632413 := bstep (se 3 (by rfl) ⟨1431077, by rfl⟩ : syracuseStep 7632413 = 2862155) B2862155
theorem B5088275 : Blo 2261435 5088275 := bstep (se 1 (by rfl) ⟨3816206, by rfl⟩ : syracuseStep 5088275 = 7632413) B7632413
theorem B3392183 : Blo 2261435 3392183 := bstep (se 1 (by rfl) ⟨2544137, by rfl⟩ : syracuseStep 3392183 = 5088275) B5088275
theorem B2261455 : Blo 2261435 2261455 := bstep (se 1 (by rfl) ⟨1696091, by rfl⟩ : syracuseStep 2261455 = 3392183) B3392183
theorem B3392189 : Blo 2261435 3392189 := bbase (se 3 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 3392189 = 1272071) (by norm_num)
theorem B2261459 : Blo 2261435 2261459 := bstep (se 1 (by rfl) ⟨1696094, by rfl⟩ : syracuseStep 2261459 = 3392189) B3392189
theorem B5088293 : Blo 2261435 5088293 := bbase (se 4 (by rfl) ⟨477027, by rfl⟩ : syracuseStep 5088293 = 954055) (by norm_num)
theorem B3392195 : Blo 2261435 3392195 := bstep (se 1 (by rfl) ⟨2544146, by rfl⟩ : syracuseStep 3392195 = 5088293) B5088293
theorem B2261463 : Blo 2261435 2261463 := bstep (se 1 (by rfl) ⟨1696097, by rfl⟩ : syracuseStep 2261463 = 3392195) B3392195
theorem B5724341 : Blo 2261435 5724341 := bbase (se 5 (by rfl) ⟨268328, by rfl⟩ : syracuseStep 5724341 = 536657) (by norm_num)
theorem B3816227 : Blo 2261435 3816227 := bstep (se 1 (by rfl) ⟨2862170, by rfl⟩ : syracuseStep 3816227 = 5724341) B5724341
theorem B2544151 : Blo 2261435 2544151 := bstep (se 1 (by rfl) ⟨1908113, by rfl⟩ : syracuseStep 2544151 = 3816227) B3816227
theorem B3392201 : Blo 2261435 3392201 := bstep (se 2 (by rfl) ⟨1272075, by rfl⟩ : syracuseStep 3392201 = 2544151) B2544151
theorem B2261467 : Blo 2261435 2261467 := bstep (se 1 (by rfl) ⟨1696100, by rfl⟩ : syracuseStep 2261467 = 3392201) B3392201
theorem B2940809 : Blo 2261435 2940809 := bbase (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) (by norm_num)
theorem B31368629 : Blo 2261435 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B20912419 : Blo 2261435 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B27883225 : Blo 2261435 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B37177633 : Blo 2261435 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B49570177 : Blo 2261435 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B66093569 : Blo 2261435 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B44062379 : Blo 2261435 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B29374919 : Blo 2261435 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B19583279 : Blo 2261435 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B13055519 : Blo 2261435 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B34814717 : Blo 2261435 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B23209811 : Blo 2261435 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B15473207 : Blo 2261435 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B10315471 : Blo 2261435 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B13753961 : Blo 2261435 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B9169307 : Blo 2261435 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B6112871 : Blo 2261435 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B4075247 : Blo 2261435 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B2716831 : Blo 2261435 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B14489765 : Blo 2261435 14489765 := bstep (se 4 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 14489765 = 2716831) B2716831
theorem B9659843 : Blo 2261435 9659843 := bstep (se 1 (by rfl) ⟨7244882, by rfl⟩ : syracuseStep 9659843 = 14489765) B14489765
theorem B6439895 : Blo 2261435 6439895 := bstep (se 1 (by rfl) ⟨4829921, by rfl⟩ : syracuseStep 6439895 = 9659843) B9659843
theorem B4293263 : Blo 2261435 4293263 := bstep (se 1 (by rfl) ⟨3219947, by rfl⟩ : syracuseStep 4293263 = 6439895) B6439895
theorem B11448701 : Blo 2261435 11448701 := bstep (se 3 (by rfl) ⟨2146631, by rfl⟩ : syracuseStep 11448701 = 4293263) B4293263
theorem B7632467 : Blo 2261435 7632467 := bstep (se 1 (by rfl) ⟨5724350, by rfl⟩ : syracuseStep 7632467 = 11448701) B11448701
theorem B5088311 : Blo 2261435 5088311 := bstep (se 1 (by rfl) ⟨3816233, by rfl⟩ : syracuseStep 5088311 = 7632467) B7632467
theorem B3392207 : Blo 2261435 3392207 := bstep (se 1 (by rfl) ⟨2544155, by rfl⟩ : syracuseStep 3392207 = 5088311) B5088311
theorem B2261471 : Blo 2261435 2261471 := bstep (se 1 (by rfl) ⟨1696103, by rfl⟩ : syracuseStep 2261471 = 3392207) B3392207
theorem B3392213 : Blo 2261435 3392213 := bbase (se 7 (by rfl) ⟨39752, by rfl⟩ : syracuseStep 3392213 = 79505) (by norm_num)
theorem B2261475 : Blo 2261435 2261475 := bstep (se 1 (by rfl) ⟨1696106, by rfl⟩ : syracuseStep 2261475 = 3392213) B3392213
theorem B2716841 : Blo 2261435 2716841 := bbase (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) (by norm_num)
theorem B7244909 : Blo 2261435 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4829939 : Blo 2261435 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3219959 : Blo 2261435 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B8586557 : Blo 2261435 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B5724371 : Blo 2261435 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3816247 : Blo 2261435 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B5088329 : Blo 2261435 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B3392219 : Blo 2261435 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B2261479 : Blo 2261435 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B2544169 : Blo 2261435 2544169 := bbase (se 2 (by rfl) ⟨954063, by rfl⟩ : syracuseStep 2544169 = 1908127) (by norm_num)
theorem B3392225 : Blo 2261435 3392225 := bstep (se 2 (by rfl) ⟨1272084, by rfl⟩ : syracuseStep 3392225 = 2544169) B2544169
theorem B2261483 : Blo 2261435 2261483 := bstep (se 1 (by rfl) ⟨1696112, by rfl⟩ : syracuseStep 2261483 = 3392225) B3392225
theorem B4584685 : Blo 2261435 4584685 := bbase (se 3 (by rfl) ⟨859628, by rfl⟩ : syracuseStep 4584685 = 1719257) (by norm_num)
theorem B6112913 : Blo 2261435 6112913 := bstep (se 2 (by rfl) ⟨2292342, by rfl⟩ : syracuseStep 6112913 = 4584685) B4584685
theorem B16301101 : Blo 2261435 16301101 := bstep (se 3 (by rfl) ⟨3056456, by rfl⟩ : syracuseStep 16301101 = 6112913) B6112913
theorem B21734801 : Blo 2261435 21734801 := bstep (se 2 (by rfl) ⟨8150550, by rfl⟩ : syracuseStep 21734801 = 16301101) B16301101
theorem B14489867 : Blo 2261435 14489867 := bstep (se 1 (by rfl) ⟨10867400, by rfl⟩ : syracuseStep 14489867 = 21734801) B21734801
theorem B9659911 : Blo 2261435 9659911 := bstep (se 1 (by rfl) ⟨7244933, by rfl⟩ : syracuseStep 9659911 = 14489867) B14489867
theorem B12879881 : Blo 2261435 12879881 := bstep (se 2 (by rfl) ⟨4829955, by rfl⟩ : syracuseStep 12879881 = 9659911) B9659911
theorem B8586587 : Blo 2261435 8586587 := bstep (se 1 (by rfl) ⟨6439940, by rfl⟩ : syracuseStep 8586587 = 12879881) B12879881
theorem B5724391 : Blo 2261435 5724391 := bstep (se 1 (by rfl) ⟨4293293, by rfl⟩ : syracuseStep 5724391 = 8586587) B8586587
theorem B7632521 : Blo 2261435 7632521 := bstep (se 2 (by rfl) ⟨2862195, by rfl⟩ : syracuseStep 7632521 = 5724391) B5724391
theorem B5088347 : Blo 2261435 5088347 := bstep (se 1 (by rfl) ⟨3816260, by rfl⟩ : syracuseStep 5088347 = 7632521) B7632521
theorem B3392231 : Blo 2261435 3392231 := bstep (se 1 (by rfl) ⟨2544173, by rfl⟩ : syracuseStep 3392231 = 5088347) B5088347
theorem B2261487 : Blo 2261435 2261487 := bstep (se 1 (by rfl) ⟨1696115, by rfl⟩ : syracuseStep 2261487 = 3392231) B3392231
theorem B3392237 : Blo 2261435 3392237 := bbase (se 3 (by rfl) ⟨636044, by rfl⟩ : syracuseStep 3392237 = 1272089) (by norm_num)
theorem B2261491 : Blo 2261435 2261491 := bstep (se 1 (by rfl) ⟨1696118, by rfl⟩ : syracuseStep 2261491 = 3392237) B3392237
theorem B5088365 : Blo 2261435 5088365 := bbase (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) (by norm_num)
theorem B3392243 : Blo 2261435 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B2261495 : Blo 2261435 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B4293317 : Blo 2261435 4293317 := bbase (se 4 (by rfl) ⟨402498, by rfl⟩ : syracuseStep 4293317 = 804997) (by norm_num)
theorem B2862211 : Blo 2261435 2862211 := bstep (se 1 (by rfl) ⟨2146658, by rfl⟩ : syracuseStep 2862211 = 4293317) B4293317
theorem B3816281 : Blo 2261435 3816281 := bstep (se 2 (by rfl) ⟨1431105, by rfl⟩ : syracuseStep 3816281 = 2862211) B2862211
theorem B2544187 : Blo 2261435 2544187 := bstep (se 1 (by rfl) ⟨1908140, by rfl⟩ : syracuseStep 2544187 = 3816281) B3816281
theorem B3392249 : Blo 2261435 3392249 := bstep (se 2 (by rfl) ⟨1272093, by rfl⟩ : syracuseStep 3392249 = 2544187) B2544187
theorem B2261499 : Blo 2261435 2261499 := bstep (se 1 (by rfl) ⟨1696124, by rfl⟩ : syracuseStep 2261499 = 3392249) B3392249
theorem B5802533 : Blo 2261435 5802533 := bbase (se 4 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 5802533 = 1087975) (by norm_num)
theorem B3868355 : Blo 2261435 3868355 := bstep (se 1 (by rfl) ⟨2901266, by rfl⟩ : syracuseStep 3868355 = 5802533) B5802533
theorem B10315613 : Blo 2261435 10315613 := bstep (se 3 (by rfl) ⟨1934177, by rfl⟩ : syracuseStep 10315613 = 3868355) B3868355
theorem B27508301 : Blo 2261435 27508301 := bstep (se 3 (by rfl) ⟨5157806, by rfl⟩ : syracuseStep 27508301 = 10315613) B10315613
theorem B18338867 : Blo 2261435 18338867 := bstep (se 1 (by rfl) ⟨13754150, by rfl⟩ : syracuseStep 18338867 = 27508301) B27508301
theorem B12225911 : Blo 2261435 12225911 := bstep (se 1 (by rfl) ⟨9169433, by rfl⟩ : syracuseStep 12225911 = 18338867) B18338867
theorem B32602429 : Blo 2261435 32602429 := bstep (se 3 (by rfl) ⟨6112955, by rfl⟩ : syracuseStep 32602429 = 12225911) B12225911
theorem B43469905 : Blo 2261435 43469905 := bstep (se 2 (by rfl) ⟨16301214, by rfl⟩ : syracuseStep 43469905 = 32602429) B32602429
theorem B57959873 : Blo 2261435 57959873 := bstep (se 2 (by rfl) ⟨21734952, by rfl⟩ : syracuseStep 57959873 = 43469905) B43469905
theorem B38639915 : Blo 2261435 38639915 := bstep (se 1 (by rfl) ⟨28979936, by rfl⟩ : syracuseStep 38639915 = 57959873) B57959873
theorem B25759943 : Blo 2261435 25759943 := bstep (se 1 (by rfl) ⟨19319957, by rfl⟩ : syracuseStep 25759943 = 38639915) B38639915
theorem B17173295 : Blo 2261435 17173295 := bstep (se 1 (by rfl) ⟨12879971, by rfl⟩ : syracuseStep 17173295 = 25759943) B25759943
theorem B11448863 : Blo 2261435 11448863 := bstep (se 1 (by rfl) ⟨8586647, by rfl⟩ : syracuseStep 11448863 = 17173295) B17173295
theorem B7632575 : Blo 2261435 7632575 := bstep (se 1 (by rfl) ⟨5724431, by rfl⟩ : syracuseStep 7632575 = 11448863) B11448863
theorem B5088383 : Blo 2261435 5088383 := bstep (se 1 (by rfl) ⟨3816287, by rfl⟩ : syracuseStep 5088383 = 7632575) B7632575
theorem B3392255 : Blo 2261435 3392255 := bstep (se 1 (by rfl) ⟨2544191, by rfl⟩ : syracuseStep 3392255 = 5088383) B5088383
theorem B2261503 : Blo 2261435 2261503 := bstep (se 1 (by rfl) ⟨1696127, by rfl⟩ : syracuseStep 2261503 = 3392255) B3392255
theorem B3392261 : Blo 2261435 3392261 := bbase (se 4 (by rfl) ⟨318024, by rfl⟩ : syracuseStep 3392261 = 636049) (by norm_num)
theorem B2261507 : Blo 2261435 2261507 := bstep (se 1 (by rfl) ⟨1696130, by rfl⟩ : syracuseStep 2261507 = 3392261) B3392261
theorem B3816301 : Blo 2261435 3816301 := bbase (se 3 (by rfl) ⟨715556, by rfl⟩ : syracuseStep 3816301 = 1431113) (by norm_num)
theorem B5088401 : Blo 2261435 5088401 := bstep (se 2 (by rfl) ⟨1908150, by rfl⟩ : syracuseStep 5088401 = 3816301) B3816301
theorem B3392267 : Blo 2261435 3392267 := bstep (se 1 (by rfl) ⟨2544200, by rfl⟩ : syracuseStep 3392267 = 5088401) B5088401
theorem B2261511 : Blo 2261435 2261511 := bstep (se 1 (by rfl) ⟨1696133, by rfl⟩ : syracuseStep 2261511 = 3392267) B3392267
theorem B2544205 : Blo 2261435 2544205 := bbase (se 3 (by rfl) ⟨477038, by rfl⟩ : syracuseStep 2544205 = 954077) (by norm_num)
theorem B3392273 : Blo 2261435 3392273 := bstep (se 2 (by rfl) ⟨1272102, by rfl⟩ : syracuseStep 3392273 = 2544205) B2544205
theorem B2261515 : Blo 2261435 2261515 := bstep (se 1 (by rfl) ⟨1696136, by rfl⟩ : syracuseStep 2261515 = 3392273) B3392273
theorem B7632629 : Blo 2261435 7632629 := bbase (se 5 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 7632629 = 715559) (by norm_num)
theorem B5088419 : Blo 2261435 5088419 := bstep (se 1 (by rfl) ⟨3816314, by rfl⟩ : syracuseStep 5088419 = 7632629) B7632629
theorem B3392279 : Blo 2261435 3392279 := bstep (se 1 (by rfl) ⟨2544209, by rfl⟩ : syracuseStep 3392279 = 5088419) B5088419
theorem B2261519 : Blo 2261435 2261519 := bstep (se 1 (by rfl) ⟨1696139, by rfl⟩ : syracuseStep 2261519 = 3392279) B3392279
theorem B3392285 : Blo 2261435 3392285 := bbase (se 3 (by rfl) ⟨636053, by rfl⟩ : syracuseStep 3392285 = 1272107) (by norm_num)
theorem B2261523 : Blo 2261435 2261523 := bstep (se 1 (by rfl) ⟨1696142, by rfl⟩ : syracuseStep 2261523 = 3392285) B3392285
theorem B5088437 : Blo 2261435 5088437 := bbase (se 5 (by rfl) ⟨238520, by rfl⟩ : syracuseStep 5088437 = 477041) (by norm_num)
theorem B3392291 : Blo 2261435 3392291 := bstep (se 1 (by rfl) ⟨2544218, by rfl⟩ : syracuseStep 3392291 = 5088437) B5088437
theorem B2261527 : Blo 2261435 2261527 := bstep (se 1 (by rfl) ⟨1696145, by rfl⟩ : syracuseStep 2261527 = 3392291) B3392291
theorem B2415025 : Blo 2261435 2415025 := bbase (se 2 (by rfl) ⟨905634, by rfl⟩ : syracuseStep 2415025 = 1811269) (by norm_num)
theorem B12880133 : Blo 2261435 12880133 := bstep (se 4 (by rfl) ⟨1207512, by rfl⟩ : syracuseStep 12880133 = 2415025) B2415025
theorem B8586755 : Blo 2261435 8586755 := bstep (se 1 (by rfl) ⟨6440066, by rfl⟩ : syracuseStep 8586755 = 12880133) B12880133
theorem B5724503 : Blo 2261435 5724503 := bstep (se 1 (by rfl) ⟨4293377, by rfl⟩ : syracuseStep 5724503 = 8586755) B8586755
theorem B3816335 : Blo 2261435 3816335 := bstep (se 1 (by rfl) ⟨2862251, by rfl⟩ : syracuseStep 3816335 = 5724503) B5724503
theorem B2544223 : Blo 2261435 2544223 := bstep (se 1 (by rfl) ⟨1908167, by rfl⟩ : syracuseStep 2544223 = 3816335) B3816335
theorem B3392297 : Blo 2261435 3392297 := bstep (se 2 (by rfl) ⟨1272111, by rfl⟩ : syracuseStep 3392297 = 2544223) B2544223
theorem B2261531 : Blo 2261435 2261531 := bstep (se 1 (by rfl) ⟨1696148, by rfl⟩ : syracuseStep 2261531 = 3392297) B3392297
theorem B2415029 : Blo 2261435 2415029 := bbase (se 5 (by rfl) ⟨113204, by rfl⟩ : syracuseStep 2415029 = 226409) (by norm_num)
theorem B6440077 : Blo 2261435 6440077 := bstep (se 3 (by rfl) ⟨1207514, by rfl⟩ : syracuseStep 6440077 = 2415029) B2415029
theorem B8586769 : Blo 2261435 8586769 := bstep (se 2 (by rfl) ⟨3220038, by rfl⟩ : syracuseStep 8586769 = 6440077) B6440077
theorem B11449025 : Blo 2261435 11449025 := bstep (se 2 (by rfl) ⟨4293384, by rfl⟩ : syracuseStep 11449025 = 8586769) B8586769
theorem B7632683 : Blo 2261435 7632683 := bstep (se 1 (by rfl) ⟨5724512, by rfl⟩ : syracuseStep 7632683 = 11449025) B11449025
theorem B5088455 : Blo 2261435 5088455 := bstep (se 1 (by rfl) ⟨3816341, by rfl⟩ : syracuseStep 5088455 = 7632683) B7632683
theorem B3392303 : Blo 2261435 3392303 := bstep (se 1 (by rfl) ⟨2544227, by rfl⟩ : syracuseStep 3392303 = 5088455) B5088455
theorem B2261535 : Blo 2261435 2261535 := bstep (se 1 (by rfl) ⟨1696151, by rfl⟩ : syracuseStep 2261535 = 3392303) B3392303
theorem B3392309 : Blo 2261435 3392309 := bbase (se 5 (by rfl) ⟨159014, by rfl⟩ : syracuseStep 3392309 = 318029) (by norm_num)
theorem B2261539 : Blo 2261435 2261539 := bstep (se 1 (by rfl) ⟨1696154, by rfl⟩ : syracuseStep 2261539 = 3392309) B3392309
theorem B5724533 : Blo 2261435 5724533 := bbase (se 5 (by rfl) ⟨268337, by rfl⟩ : syracuseStep 5724533 = 536675) (by norm_num)
theorem B3816355 : Blo 2261435 3816355 := bstep (se 1 (by rfl) ⟨2862266, by rfl⟩ : syracuseStep 3816355 = 5724533) B5724533
theorem B5088473 : Blo 2261435 5088473 := bstep (se 2 (by rfl) ⟨1908177, by rfl⟩ : syracuseStep 5088473 = 3816355) B3816355
theorem B3392315 : Blo 2261435 3392315 := bstep (se 1 (by rfl) ⟨2544236, by rfl⟩ : syracuseStep 3392315 = 5088473) B5088473
theorem B2261543 : Blo 2261435 2261543 := bstep (se 1 (by rfl) ⟨1696157, by rfl⟩ : syracuseStep 2261543 = 3392315) B3392315
theorem B2544241 : Blo 2261435 2544241 := bbase (se 2 (by rfl) ⟨954090, by rfl⟩ : syracuseStep 2544241 = 1908181) (by norm_num)
theorem B3392321 : Blo 2261435 3392321 := bstep (se 2 (by rfl) ⟨1272120, by rfl⟩ : syracuseStep 3392321 = 2544241) B2544241
theorem B2261547 : Blo 2261435 2261547 := bstep (se 1 (by rfl) ⟨1696160, by rfl⟩ : syracuseStep 2261547 = 3392321) B3392321
theorem B2323685 : Blo 2261435 2323685 := bbase (se 4 (by rfl) ⟨217845, by rfl⟩ : syracuseStep 2323685 = 435691) (by norm_num)
theorem B6196493 : Blo 2261435 6196493 := bstep (se 3 (by rfl) ⟨1161842, by rfl⟩ : syracuseStep 6196493 = 2323685) B2323685
theorem B4130995 : Blo 2261435 4130995 := bstep (se 1 (by rfl) ⟨3098246, by rfl⟩ : syracuseStep 4130995 = 6196493) B6196493
theorem B5507993 : Blo 2261435 5507993 := bstep (se 2 (by rfl) ⟨2065497, by rfl⟩ : syracuseStep 5507993 = 4130995) B4130995
theorem B3671995 : Blo 2261435 3671995 := bstep (se 1 (by rfl) ⟨2753996, by rfl⟩ : syracuseStep 3671995 = 5507993) B5507993
theorem B4895993 : Blo 2261435 4895993 := bstep (se 2 (by rfl) ⟨1835997, by rfl⟩ : syracuseStep 4895993 = 3671995) B3671995
theorem B3263995 : Blo 2261435 3263995 := bstep (se 1 (by rfl) ⟨2447996, by rfl⟩ : syracuseStep 3263995 = 4895993) B4895993
theorem B17407973 : Blo 2261435 17407973 := bstep (se 4 (by rfl) ⟨1631997, by rfl⟩ : syracuseStep 17407973 = 3263995) B3263995
theorem B46421261 : Blo 2261435 46421261 := bstep (se 3 (by rfl) ⟨8703986, by rfl⟩ : syracuseStep 46421261 = 17407973) B17407973
theorem B30947507 : Blo 2261435 30947507 := bstep (se 1 (by rfl) ⟨23210630, by rfl⟩ : syracuseStep 30947507 = 46421261) B46421261
theorem B20631671 : Blo 2261435 20631671 := bstep (se 1 (by rfl) ⟨15473753, by rfl⟩ : syracuseStep 20631671 = 30947507) B30947507
theorem B13754447 : Blo 2261435 13754447 := bstep (se 1 (by rfl) ⟨10315835, by rfl⟩ : syracuseStep 13754447 = 20631671) B20631671
theorem B9169631 : Blo 2261435 9169631 := bstep (se 1 (by rfl) ⟨6877223, by rfl⟩ : syracuseStep 9169631 = 13754447) B13754447
theorem B6113087 : Blo 2261435 6113087 := bstep (se 1 (by rfl) ⟨4584815, by rfl⟩ : syracuseStep 6113087 = 9169631) B9169631
theorem B4075391 : Blo 2261435 4075391 := bstep (se 1 (by rfl) ⟨3056543, by rfl⟩ : syracuseStep 4075391 = 6113087) B6113087
theorem B10867709 : Blo 2261435 10867709 := bstep (se 3 (by rfl) ⟨2037695, by rfl⟩ : syracuseStep 10867709 = 4075391) B4075391
theorem B7245139 : Blo 2261435 7245139 := bstep (se 1 (by rfl) ⟨5433854, by rfl⟩ : syracuseStep 7245139 = 10867709) B10867709
theorem B9660185 : Blo 2261435 9660185 := bstep (se 2 (by rfl) ⟨3622569, by rfl⟩ : syracuseStep 9660185 = 7245139) B7245139
theorem B6440123 : Blo 2261435 6440123 := bstep (se 1 (by rfl) ⟨4830092, by rfl⟩ : syracuseStep 6440123 = 9660185) B9660185
theorem B4293415 : Blo 2261435 4293415 := bstep (se 1 (by rfl) ⟨3220061, by rfl⟩ : syracuseStep 4293415 = 6440123) B6440123
theorem B5724553 : Blo 2261435 5724553 := bstep (se 2 (by rfl) ⟨2146707, by rfl⟩ : syracuseStep 5724553 = 4293415) B4293415
theorem B7632737 : Blo 2261435 7632737 := bstep (se 2 (by rfl) ⟨2862276, by rfl⟩ : syracuseStep 7632737 = 5724553) B5724553
theorem B5088491 : Blo 2261435 5088491 := bstep (se 1 (by rfl) ⟨3816368, by rfl⟩ : syracuseStep 5088491 = 7632737) B7632737
theorem B3392327 : Blo 2261435 3392327 := bstep (se 1 (by rfl) ⟨2544245, by rfl⟩ : syracuseStep 3392327 = 5088491) B5088491
theorem B2261551 : Blo 2261435 2261551 := bstep (se 1 (by rfl) ⟨1696163, by rfl⟩ : syracuseStep 2261551 = 3392327) B3392327
theorem B3392333 : Blo 2261435 3392333 := bbase (se 3 (by rfl) ⟨636062, by rfl⟩ : syracuseStep 3392333 = 1272125) (by norm_num)
theorem B2261555 : Blo 2261435 2261555 := bstep (se 1 (by rfl) ⟨1696166, by rfl⟩ : syracuseStep 2261555 = 3392333) B3392333
theorem B5088509 : Blo 2261435 5088509 := bbase (se 3 (by rfl) ⟨954095, by rfl⟩ : syracuseStep 5088509 = 1908191) (by norm_num)
theorem B3392339 : Blo 2261435 3392339 := bstep (se 1 (by rfl) ⟨2544254, by rfl⟩ : syracuseStep 3392339 = 5088509) B5088509
theorem B2261559 : Blo 2261435 2261559 := bstep (se 1 (by rfl) ⟨1696169, by rfl⟩ : syracuseStep 2261559 = 3392339) B3392339
theorem B3816389 : Blo 2261435 3816389 := bbase (se 4 (by rfl) ⟨357786, by rfl⟩ : syracuseStep 3816389 = 715573) (by norm_num)
theorem B2544259 : Blo 2261435 2544259 := bstep (se 1 (by rfl) ⟨1908194, by rfl⟩ : syracuseStep 2544259 = 3816389) B3816389
theorem B3392345 : Blo 2261435 3392345 := bstep (se 2 (by rfl) ⟨1272129, by rfl⟩ : syracuseStep 3392345 = 2544259) B2544259
theorem B2261563 : Blo 2261435 2261563 := bstep (se 1 (by rfl) ⟨1696172, by rfl⟩ : syracuseStep 2261563 = 3392345) B3392345
theorem B17173781 : Blo 2261435 17173781 := bbase (se 6 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 17173781 = 805021) (by norm_num)
theorem B11449187 : Blo 2261435 11449187 := bstep (se 1 (by rfl) ⟨8586890, by rfl⟩ : syracuseStep 11449187 = 17173781) B17173781
theorem B7632791 : Blo 2261435 7632791 := bstep (se 1 (by rfl) ⟨5724593, by rfl⟩ : syracuseStep 7632791 = 11449187) B11449187
theorem B5088527 : Blo 2261435 5088527 := bstep (se 1 (by rfl) ⟨3816395, by rfl⟩ : syracuseStep 5088527 = 7632791) B7632791
theorem B3392351 : Blo 2261435 3392351 := bstep (se 1 (by rfl) ⟨2544263, by rfl⟩ : syracuseStep 3392351 = 5088527) B5088527
theorem B2261567 : Blo 2261435 2261567 := bstep (se 1 (by rfl) ⟨1696175, by rfl⟩ : syracuseStep 2261567 = 3392351) B3392351
theorem B3392357 : Blo 2261435 3392357 := bbase (se 4 (by rfl) ⟨318033, by rfl⟩ : syracuseStep 3392357 = 636067) (by norm_num)
theorem B2261571 : Blo 2261435 2261571 := bstep (se 1 (by rfl) ⟨1696178, by rfl⟩ : syracuseStep 2261571 = 3392357) B3392357
theorem B4293461 : Blo 2261435 4293461 := bbase (se 9 (by rfl) ⟨12578, by rfl⟩ : syracuseStep 4293461 = 25157) (by norm_num)
theorem B2862307 : Blo 2261435 2862307 := bstep (se 1 (by rfl) ⟨2146730, by rfl⟩ : syracuseStep 2862307 = 4293461) B4293461
theorem B3816409 : Blo 2261435 3816409 := bstep (se 2 (by rfl) ⟨1431153, by rfl⟩ : syracuseStep 3816409 = 2862307) B2862307
theorem B5088545 : Blo 2261435 5088545 := bstep (se 2 (by rfl) ⟨1908204, by rfl⟩ : syracuseStep 5088545 = 3816409) B3816409
theorem B3392363 : Blo 2261435 3392363 := bstep (se 1 (by rfl) ⟨2544272, by rfl⟩ : syracuseStep 3392363 = 5088545) B5088545
theorem B2261575 : Blo 2261435 2261575 := bstep (se 1 (by rfl) ⟨1696181, by rfl⟩ : syracuseStep 2261575 = 3392363) B3392363
theorem B2544277 : Blo 2261435 2544277 := bbase (se 6 (by rfl) ⟨59631, by rfl⟩ : syracuseStep 2544277 = 119263) (by norm_num)
theorem B3392369 : Blo 2261435 3392369 := bstep (se 2 (by rfl) ⟨1272138, by rfl⟩ : syracuseStep 3392369 = 2544277) B2544277
theorem B2261579 : Blo 2261435 2261579 := bstep (se 1 (by rfl) ⟨1696184, by rfl⟩ : syracuseStep 2261579 = 3392369) B3392369
theorem B2862317 : Blo 2261435 2862317 := bbase (se 3 (by rfl) ⟨536684, by rfl⟩ : syracuseStep 2862317 = 1073369) (by norm_num)
theorem B7632845 : Blo 2261435 7632845 := bstep (se 3 (by rfl) ⟨1431158, by rfl⟩ : syracuseStep 7632845 = 2862317) B2862317
theorem B5088563 : Blo 2261435 5088563 := bstep (se 1 (by rfl) ⟨3816422, by rfl⟩ : syracuseStep 5088563 = 7632845) B7632845
theorem B3392375 : Blo 2261435 3392375 := bstep (se 1 (by rfl) ⟨2544281, by rfl⟩ : syracuseStep 3392375 = 5088563) B5088563
theorem B2261583 : Blo 2261435 2261583 := bstep (se 1 (by rfl) ⟨1696187, by rfl⟩ : syracuseStep 2261583 = 3392375) B3392375
theorem B3392381 : Blo 2261435 3392381 := bbase (se 3 (by rfl) ⟨636071, by rfl⟩ : syracuseStep 3392381 = 1272143) (by norm_num)
theorem B2261587 : Blo 2261435 2261587 := bstep (se 1 (by rfl) ⟨1696190, by rfl⟩ : syracuseStep 2261587 = 3392381) B3392381
theorem B5088581 : Blo 2261435 5088581 := bbase (se 4 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 5088581 = 954109) (by norm_num)
theorem B3392387 : Blo 2261435 3392387 := bstep (se 1 (by rfl) ⟨2544290, by rfl⟩ : syracuseStep 3392387 = 5088581) B5088581
theorem B2261591 : Blo 2261435 2261591 := bstep (se 1 (by rfl) ⟨1696193, by rfl⟩ : syracuseStep 2261591 = 3392387) B3392387
theorem B7737029 : Blo 2261435 7737029 := bbase (se 4 (by rfl) ⟨725346, by rfl⟩ : syracuseStep 7737029 = 1450693) (by norm_num)
theorem B5158019 : Blo 2261435 5158019 := bstep (se 1 (by rfl) ⟨3868514, by rfl⟩ : syracuseStep 5158019 = 7737029) B7737029
theorem B13754717 : Blo 2261435 13754717 := bstep (se 3 (by rfl) ⟨2579009, by rfl⟩ : syracuseStep 13754717 = 5158019) B5158019
theorem B9169811 : Blo 2261435 9169811 := bstep (se 1 (by rfl) ⟨6877358, by rfl⟩ : syracuseStep 9169811 = 13754717) B13754717
theorem B6113207 : Blo 2261435 6113207 := bstep (se 1 (by rfl) ⟨4584905, by rfl⟩ : syracuseStep 6113207 = 9169811) B9169811
theorem B4075471 : Blo 2261435 4075471 := bstep (se 1 (by rfl) ⟨3056603, by rfl⟩ : syracuseStep 4075471 = 6113207) B6113207
theorem B5433961 : Blo 2261435 5433961 := bstep (se 2 (by rfl) ⟨2037735, by rfl⟩ : syracuseStep 5433961 = 4075471) B4075471
theorem B7245281 : Blo 2261435 7245281 := bstep (se 2 (by rfl) ⟨2716980, by rfl⟩ : syracuseStep 7245281 = 5433961) B5433961
theorem B4830187 : Blo 2261435 4830187 := bstep (se 1 (by rfl) ⟨3622640, by rfl⟩ : syracuseStep 4830187 = 7245281) B7245281
theorem B6440249 : Blo 2261435 6440249 := bstep (se 2 (by rfl) ⟨2415093, by rfl⟩ : syracuseStep 6440249 = 4830187) B4830187
theorem B4293499 : Blo 2261435 4293499 := bstep (se 1 (by rfl) ⟨3220124, by rfl⟩ : syracuseStep 4293499 = 6440249) B6440249
theorem B5724665 : Blo 2261435 5724665 := bstep (se 2 (by rfl) ⟨2146749, by rfl⟩ : syracuseStep 5724665 = 4293499) B4293499
theorem B3816443 : Blo 2261435 3816443 := bstep (se 1 (by rfl) ⟨2862332, by rfl⟩ : syracuseStep 3816443 = 5724665) B5724665
theorem B2544295 : Blo 2261435 2544295 := bstep (se 1 (by rfl) ⟨1908221, by rfl⟩ : syracuseStep 2544295 = 3816443) B3816443
theorem B3392393 : Blo 2261435 3392393 := bstep (se 2 (by rfl) ⟨1272147, by rfl⟩ : syracuseStep 3392393 = 2544295) B2544295
theorem B2261595 : Blo 2261435 2261595 := bstep (se 1 (by rfl) ⟨1696196, by rfl⟩ : syracuseStep 2261595 = 3392393) B3392393
theorem B11449349 : Blo 2261435 11449349 := bbase (se 4 (by rfl) ⟨1073376, by rfl⟩ : syracuseStep 11449349 = 2146753) (by norm_num)
theorem B7632899 : Blo 2261435 7632899 := bstep (se 1 (by rfl) ⟨5724674, by rfl⟩ : syracuseStep 7632899 = 11449349) B11449349
theorem B5088599 : Blo 2261435 5088599 := bstep (se 1 (by rfl) ⟨3816449, by rfl⟩ : syracuseStep 5088599 = 7632899) B7632899
theorem B3392399 : Blo 2261435 3392399 := bstep (se 1 (by rfl) ⟨2544299, by rfl⟩ : syracuseStep 3392399 = 5088599) B5088599
theorem B2261599 : Blo 2261435 2261599 := bstep (se 1 (by rfl) ⟨1696199, by rfl⟩ : syracuseStep 2261599 = 3392399) B3392399
theorem B3392405 : Blo 2261435 3392405 := bbase (se 6 (by rfl) ⟨79509, by rfl⟩ : syracuseStep 3392405 = 159019) (by norm_num)
theorem B2261603 : Blo 2261435 2261603 := bstep (se 1 (by rfl) ⟨1696202, by rfl⟩ : syracuseStep 2261603 = 3392405) B3392405
theorem B12880565 : Blo 2261435 12880565 := bbase (se 5 (by rfl) ⟨603776, by rfl⟩ : syracuseStep 12880565 = 1207553) (by norm_num)
theorem B8587043 : Blo 2261435 8587043 := bstep (se 1 (by rfl) ⟨6440282, by rfl⟩ : syracuseStep 8587043 = 12880565) B12880565
theorem B5724695 : Blo 2261435 5724695 := bstep (se 1 (by rfl) ⟨4293521, by rfl⟩ : syracuseStep 5724695 = 8587043) B8587043
theorem B3816463 : Blo 2261435 3816463 := bstep (se 1 (by rfl) ⟨2862347, by rfl⟩ : syracuseStep 3816463 = 5724695) B5724695
theorem B5088617 : Blo 2261435 5088617 := bstep (se 2 (by rfl) ⟨1908231, by rfl⟩ : syracuseStep 5088617 = 3816463) B3816463
theorem B3392411 : Blo 2261435 3392411 := bstep (se 1 (by rfl) ⟨2544308, by rfl⟩ : syracuseStep 3392411 = 5088617) B5088617
theorem B2261607 : Blo 2261435 2261607 := bstep (se 1 (by rfl) ⟨1696205, by rfl⟩ : syracuseStep 2261607 = 3392411) B3392411
theorem B2544313 : Blo 2261435 2544313 := bbase (se 2 (by rfl) ⟨954117, by rfl⟩ : syracuseStep 2544313 = 1908235) (by norm_num)
theorem B3392417 : Blo 2261435 3392417 := bstep (se 2 (by rfl) ⟨1272156, by rfl⟩ : syracuseStep 3392417 = 2544313) B2544313
theorem B2261611 : Blo 2261435 2261611 := bstep (se 1 (by rfl) ⟨1696208, by rfl⟩ : syracuseStep 2261611 = 3392417) B3392417
theorem B4830229 : Blo 2261435 4830229 := bbase (se 6 (by rfl) ⟨113208, by rfl⟩ : syracuseStep 4830229 = 226417) (by norm_num)
theorem B6440305 : Blo 2261435 6440305 := bstep (se 2 (by rfl) ⟨2415114, by rfl⟩ : syracuseStep 6440305 = 4830229) B4830229
theorem B8587073 : Blo 2261435 8587073 := bstep (se 2 (by rfl) ⟨3220152, by rfl⟩ : syracuseStep 8587073 = 6440305) B6440305
theorem B5724715 : Blo 2261435 5724715 := bstep (se 1 (by rfl) ⟨4293536, by rfl⟩ : syracuseStep 5724715 = 8587073) B8587073
theorem B7632953 : Blo 2261435 7632953 := bstep (se 2 (by rfl) ⟨2862357, by rfl⟩ : syracuseStep 7632953 = 5724715) B5724715
theorem B5088635 : Blo 2261435 5088635 := bstep (se 1 (by rfl) ⟨3816476, by rfl⟩ : syracuseStep 5088635 = 7632953) B7632953
theorem B3392423 : Blo 2261435 3392423 := bstep (se 1 (by rfl) ⟨2544317, by rfl⟩ : syracuseStep 3392423 = 5088635) B5088635
theorem B2261615 : Blo 2261435 2261615 := bstep (se 1 (by rfl) ⟨1696211, by rfl⟩ : syracuseStep 2261615 = 3392423) B3392423
theorem B3392429 : Blo 2261435 3392429 := bbase (se 3 (by rfl) ⟨636080, by rfl⟩ : syracuseStep 3392429 = 1272161) (by norm_num)
theorem B2261619 : Blo 2261435 2261619 := bstep (se 1 (by rfl) ⟨1696214, by rfl⟩ : syracuseStep 2261619 = 3392429) B3392429
theorem B5088653 : Blo 2261435 5088653 := bbase (se 3 (by rfl) ⟨954122, by rfl⟩ : syracuseStep 5088653 = 1908245) (by norm_num)
theorem B3392435 : Blo 2261435 3392435 := bstep (se 1 (by rfl) ⟨2544326, by rfl⟩ : syracuseStep 3392435 = 5088653) B5088653
theorem B2261623 : Blo 2261435 2261623 := bstep (se 1 (by rfl) ⟨1696217, by rfl⟩ : syracuseStep 2261623 = 3392435) B3392435
theorem B2862373 : Blo 2261435 2862373 := bbase (se 4 (by rfl) ⟨268347, by rfl⟩ : syracuseStep 2862373 = 536695) (by norm_num)
theorem B3816497 : Blo 2261435 3816497 := bstep (se 2 (by rfl) ⟨1431186, by rfl⟩ : syracuseStep 3816497 = 2862373) B2862373
theorem B2544331 : Blo 2261435 2544331 := bstep (se 1 (by rfl) ⟨1908248, by rfl⟩ : syracuseStep 2544331 = 3816497) B3816497
theorem B3392441 : Blo 2261435 3392441 := bstep (se 2 (by rfl) ⟨1272165, by rfl⟩ : syracuseStep 3392441 = 2544331) B2544331
theorem B2261627 : Blo 2261435 2261627 := bstep (se 1 (by rfl) ⟨1696220, by rfl⟩ : syracuseStep 2261627 = 3392441) B3392441
theorem B10316197 : Blo 2261435 10316197 := bbase (se 4 (by rfl) ⟨967143, by rfl⟩ : syracuseStep 10316197 = 1934287) (by norm_num)
theorem B13754929 : Blo 2261435 13754929 := bstep (se 2 (by rfl) ⟨5158098, by rfl⟩ : syracuseStep 13754929 = 10316197) B10316197
theorem B18339905 : Blo 2261435 18339905 := bstep (se 2 (by rfl) ⟨6877464, by rfl⟩ : syracuseStep 18339905 = 13754929) B13754929
theorem B48906413 : Blo 2261435 48906413 := bstep (se 3 (by rfl) ⟨9169952, by rfl⟩ : syracuseStep 48906413 = 18339905) B18339905
theorem B32604275 : Blo 2261435 32604275 := bstep (se 1 (by rfl) ⟨24453206, by rfl⟩ : syracuseStep 32604275 = 48906413) B48906413
theorem B21736183 : Blo 2261435 21736183 := bstep (se 1 (by rfl) ⟨16302137, by rfl⟩ : syracuseStep 21736183 = 32604275) B32604275
theorem B28981577 : Blo 2261435 28981577 := bstep (se 2 (by rfl) ⟨10868091, by rfl⟩ : syracuseStep 28981577 = 21736183) B21736183
theorem B19321051 : Blo 2261435 19321051 := bstep (se 1 (by rfl) ⟨14490788, by rfl⟩ : syracuseStep 19321051 = 28981577) B28981577
theorem B25761401 : Blo 2261435 25761401 := bstep (se 2 (by rfl) ⟨9660525, by rfl⟩ : syracuseStep 25761401 = 19321051) B19321051
theorem B17174267 : Blo 2261435 17174267 := bstep (se 1 (by rfl) ⟨12880700, by rfl⟩ : syracuseStep 17174267 = 25761401) B25761401
theorem B11449511 : Blo 2261435 11449511 := bstep (se 1 (by rfl) ⟨8587133, by rfl⟩ : syracuseStep 11449511 = 17174267) B17174267
theorem B7633007 : Blo 2261435 7633007 := bstep (se 1 (by rfl) ⟨5724755, by rfl⟩ : syracuseStep 7633007 = 11449511) B11449511
theorem B5088671 : Blo 2261435 5088671 := bstep (se 1 (by rfl) ⟨3816503, by rfl⟩ : syracuseStep 5088671 = 7633007) B7633007
theorem B3392447 : Blo 2261435 3392447 := bstep (se 1 (by rfl) ⟨2544335, by rfl⟩ : syracuseStep 3392447 = 5088671) B5088671
theorem B2261631 : Blo 2261435 2261631 := bstep (se 1 (by rfl) ⟨1696223, by rfl⟩ : syracuseStep 2261631 = 3392447) B3392447
theorem B3392453 : Blo 2261435 3392453 := bbase (se 4 (by rfl) ⟨318042, by rfl⟩ : syracuseStep 3392453 = 636085) (by norm_num)
theorem B2261635 : Blo 2261435 2261635 := bstep (se 1 (by rfl) ⟨1696226, by rfl⟩ : syracuseStep 2261635 = 3392453) B3392453
theorem B3816517 : Blo 2261435 3816517 := bbase (se 4 (by rfl) ⟨357798, by rfl⟩ : syracuseStep 3816517 = 715597) (by norm_num)
theorem B5088689 : Blo 2261435 5088689 := bstep (se 2 (by rfl) ⟨1908258, by rfl⟩ : syracuseStep 5088689 = 3816517) B3816517
theorem B3392459 : Blo 2261435 3392459 := bstep (se 1 (by rfl) ⟨2544344, by rfl⟩ : syracuseStep 3392459 = 5088689) B5088689
theorem B2261639 : Blo 2261435 2261639 := bstep (se 1 (by rfl) ⟨1696229, by rfl⟩ : syracuseStep 2261639 = 3392459) B3392459
theorem B2544349 : Blo 2261435 2544349 := bbase (se 3 (by rfl) ⟨477065, by rfl⟩ : syracuseStep 2544349 = 954131) (by norm_num)
theorem B3392465 : Blo 2261435 3392465 := bstep (se 2 (by rfl) ⟨1272174, by rfl⟩ : syracuseStep 3392465 = 2544349) B2544349
theorem B2261643 : Blo 2261435 2261643 := bstep (se 1 (by rfl) ⟨1696232, by rfl⟩ : syracuseStep 2261643 = 3392465) B3392465
theorem B7633061 : Blo 2261435 7633061 := bbase (se 4 (by rfl) ⟨715599, by rfl⟩ : syracuseStep 7633061 = 1431199) (by norm_num)
theorem B5088707 : Blo 2261435 5088707 := bstep (se 1 (by rfl) ⟨3816530, by rfl⟩ : syracuseStep 5088707 = 7633061) B7633061
theorem B3392471 : Blo 2261435 3392471 := bstep (se 1 (by rfl) ⟨2544353, by rfl⟩ : syracuseStep 3392471 = 5088707) B5088707
theorem B2261647 : Blo 2261435 2261647 := bstep (se 1 (by rfl) ⟨1696235, by rfl⟩ : syracuseStep 2261647 = 3392471) B3392471
theorem B3392477 : Blo 2261435 3392477 := bbase (se 3 (by rfl) ⟨636089, by rfl⟩ : syracuseStep 3392477 = 1272179) (by norm_num)
theorem B2261651 : Blo 2261435 2261651 := bstep (se 1 (by rfl) ⟨1696238, by rfl⟩ : syracuseStep 2261651 = 3392477) B3392477
theorem B5088725 : Blo 2261435 5088725 := bbase (se 7 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 5088725 = 119267) (by norm_num)
theorem B3392483 : Blo 2261435 3392483 := bstep (se 1 (by rfl) ⟨2544362, by rfl⟩ : syracuseStep 3392483 = 5088725) B5088725
theorem B2261655 : Blo 2261435 2261655 := bstep (se 1 (by rfl) ⟨1696241, by rfl⟩ : syracuseStep 2261655 = 3392483) B3392483
theorem B2448113 : Blo 2261435 2448113 := bbase (se 2 (by rfl) ⟨918042, by rfl⟩ : syracuseStep 2448113 = 1836085) (by norm_num)
theorem B26113205 : Blo 2261435 26113205 := bstep (se 5 (by rfl) ⟨1224056, by rfl⟩ : syracuseStep 26113205 = 2448113) B2448113
theorem B17408803 : Blo 2261435 17408803 := bstep (se 1 (by rfl) ⟨13056602, by rfl⟩ : syracuseStep 17408803 = 26113205) B26113205
theorem B23211737 : Blo 2261435 23211737 := bstep (se 2 (by rfl) ⟨8704401, by rfl⟩ : syracuseStep 23211737 = 17408803) B17408803
theorem B15474491 : Blo 2261435 15474491 := bstep (se 1 (by rfl) ⟨11605868, by rfl⟩ : syracuseStep 15474491 = 23211737) B23211737
theorem B10316327 : Blo 2261435 10316327 := bstep (se 1 (by rfl) ⟨7737245, by rfl⟩ : syracuseStep 10316327 = 15474491) B15474491
theorem B27510205 : Blo 2261435 27510205 := bstep (se 3 (by rfl) ⟨5158163, by rfl⟩ : syracuseStep 27510205 = 10316327) B10316327
theorem B36680273 : Blo 2261435 36680273 := bstep (se 2 (by rfl) ⟨13755102, by rfl⟩ : syracuseStep 36680273 = 27510205) B27510205
theorem B24453515 : Blo 2261435 24453515 := bstep (se 1 (by rfl) ⟨18340136, by rfl⟩ : syracuseStep 24453515 = 36680273) B36680273
theorem B16302343 : Blo 2261435 16302343 := bstep (se 1 (by rfl) ⟨12226757, by rfl⟩ : syracuseStep 16302343 = 24453515) B24453515
theorem B21736457 : Blo 2261435 21736457 := bstep (se 2 (by rfl) ⟨8151171, by rfl⟩ : syracuseStep 21736457 = 16302343) B16302343
theorem B14490971 : Blo 2261435 14490971 := bstep (se 1 (by rfl) ⟨10868228, by rfl⟩ : syracuseStep 14490971 = 21736457) B21736457
theorem B9660647 : Blo 2261435 9660647 := bstep (se 1 (by rfl) ⟨7245485, by rfl⟩ : syracuseStep 9660647 = 14490971) B14490971
theorem B6440431 : Blo 2261435 6440431 := bstep (se 1 (by rfl) ⟨4830323, by rfl⟩ : syracuseStep 6440431 = 9660647) B9660647
theorem B8587241 : Blo 2261435 8587241 := bstep (se 2 (by rfl) ⟨3220215, by rfl⟩ : syracuseStep 8587241 = 6440431) B6440431
theorem B5724827 : Blo 2261435 5724827 := bstep (se 1 (by rfl) ⟨4293620, by rfl⟩ : syracuseStep 5724827 = 8587241) B8587241
theorem B3816551 : Blo 2261435 3816551 := bstep (se 1 (by rfl) ⟨2862413, by rfl⟩ : syracuseStep 3816551 = 5724827) B5724827
theorem B2544367 : Blo 2261435 2544367 := bstep (se 1 (by rfl) ⟨1908275, by rfl⟩ : syracuseStep 2544367 = 3816551) B3816551
theorem B3392489 : Blo 2261435 3392489 := bstep (se 2 (by rfl) ⟨1272183, by rfl⟩ : syracuseStep 3392489 = 2544367) B2544367
theorem B2261659 : Blo 2261435 2261659 := bstep (se 1 (by rfl) ⟨1696244, by rfl⟩ : syracuseStep 2261659 = 3392489) B3392489
theorem B2292521 : Blo 2261435 2292521 := bbase (se 2 (by rfl) ⟨859695, by rfl⟩ : syracuseStep 2292521 = 1719391) (by norm_num)
theorem B6113389 : Blo 2261435 6113389 := bstep (se 3 (by rfl) ⟨1146260, by rfl⟩ : syracuseStep 6113389 = 2292521) B2292521
theorem B8151185 : Blo 2261435 8151185 := bstep (se 2 (by rfl) ⟨3056694, by rfl⟩ : syracuseStep 8151185 = 6113389) B6113389
theorem B5434123 : Blo 2261435 5434123 := bstep (se 1 (by rfl) ⟨4075592, by rfl⟩ : syracuseStep 5434123 = 8151185) B8151185
theorem B7245497 : Blo 2261435 7245497 := bstep (se 2 (by rfl) ⟨2717061, by rfl⟩ : syracuseStep 7245497 = 5434123) B5434123
theorem B19321325 : Blo 2261435 19321325 := bstep (se 3 (by rfl) ⟨3622748, by rfl⟩ : syracuseStep 19321325 = 7245497) B7245497
theorem B12880883 : Blo 2261435 12880883 := bstep (se 1 (by rfl) ⟨9660662, by rfl⟩ : syracuseStep 12880883 = 19321325) B19321325
theorem B8587255 : Blo 2261435 8587255 := bstep (se 1 (by rfl) ⟨6440441, by rfl⟩ : syracuseStep 8587255 = 12880883) B12880883
theorem B11449673 : Blo 2261435 11449673 := bstep (se 2 (by rfl) ⟨4293627, by rfl⟩ : syracuseStep 11449673 = 8587255) B8587255
theorem B7633115 : Blo 2261435 7633115 := bstep (se 1 (by rfl) ⟨5724836, by rfl⟩ : syracuseStep 7633115 = 11449673) B11449673
theorem B5088743 : Blo 2261435 5088743 := bstep (se 1 (by rfl) ⟨3816557, by rfl⟩ : syracuseStep 5088743 = 7633115) B7633115
theorem B3392495 : Blo 2261435 3392495 := bstep (se 1 (by rfl) ⟨2544371, by rfl⟩ : syracuseStep 3392495 = 5088743) B5088743
theorem B2261663 : Blo 2261435 2261663 := bstep (se 1 (by rfl) ⟨1696247, by rfl⟩ : syracuseStep 2261663 = 3392495) B3392495
theorem B3392501 : Blo 2261435 3392501 := bbase (se 5 (by rfl) ⟨159023, by rfl⟩ : syracuseStep 3392501 = 318047) (by norm_num)
theorem B2261667 : Blo 2261435 2261667 := bstep (se 1 (by rfl) ⟨1696250, by rfl⟩ : syracuseStep 2261667 = 3392501) B3392501
theorem B4830349 : Blo 2261435 4830349 := bbase (se 3 (by rfl) ⟨905690, by rfl⟩ : syracuseStep 4830349 = 1811381) (by norm_num)
theorem B6440465 : Blo 2261435 6440465 := bstep (se 2 (by rfl) ⟨2415174, by rfl⟩ : syracuseStep 6440465 = 4830349) B4830349
theorem B4293643 : Blo 2261435 4293643 := bstep (se 1 (by rfl) ⟨3220232, by rfl⟩ : syracuseStep 4293643 = 6440465) B6440465
theorem B5724857 : Blo 2261435 5724857 := bstep (se 2 (by rfl) ⟨2146821, by rfl⟩ : syracuseStep 5724857 = 4293643) B4293643
theorem B3816571 : Blo 2261435 3816571 := bstep (se 1 (by rfl) ⟨2862428, by rfl⟩ : syracuseStep 3816571 = 5724857) B5724857
theorem B5088761 : Blo 2261435 5088761 := bstep (se 2 (by rfl) ⟨1908285, by rfl⟩ : syracuseStep 5088761 = 3816571) B3816571
theorem B3392507 : Blo 2261435 3392507 := bstep (se 1 (by rfl) ⟨2544380, by rfl⟩ : syracuseStep 3392507 = 5088761) B5088761
theorem B2261671 : Blo 2261435 2261671 := bstep (se 1 (by rfl) ⟨1696253, by rfl⟩ : syracuseStep 2261671 = 3392507) B3392507
theorem B2544385 : Blo 2261435 2544385 := bbase (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) (by norm_num)
theorem B3392513 : Blo 2261435 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B2261675 : Blo 2261435 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B5724877 : Blo 2261435 5724877 := bbase (se 3 (by rfl) ⟨1073414, by rfl⟩ : syracuseStep 5724877 = 2146829) (by norm_num)
theorem B7633169 : Blo 2261435 7633169 := bstep (se 2 (by rfl) ⟨2862438, by rfl⟩ : syracuseStep 7633169 = 5724877) B5724877
theorem B5088779 : Blo 2261435 5088779 := bstep (se 1 (by rfl) ⟨3816584, by rfl⟩ : syracuseStep 5088779 = 7633169) B7633169
theorem B3392519 : Blo 2261435 3392519 := bstep (se 1 (by rfl) ⟨2544389, by rfl⟩ : syracuseStep 3392519 = 5088779) B5088779
theorem B2261679 : Blo 2261435 2261679 := bstep (se 1 (by rfl) ⟨1696259, by rfl⟩ : syracuseStep 2261679 = 3392519) B3392519
theorem B3392525 : Blo 2261435 3392525 := bbase (se 3 (by rfl) ⟨636098, by rfl⟩ : syracuseStep 3392525 = 1272197) (by norm_num)
theorem B2261683 : Blo 2261435 2261683 := bstep (se 1 (by rfl) ⟨1696262, by rfl⟩ : syracuseStep 2261683 = 3392525) B3392525
theorem B5088797 : Blo 2261435 5088797 := bbase (se 3 (by rfl) ⟨954149, by rfl⟩ : syracuseStep 5088797 = 1908299) (by norm_num)
theorem B3392531 : Blo 2261435 3392531 := bstep (se 1 (by rfl) ⟨2544398, by rfl⟩ : syracuseStep 3392531 = 5088797) B5088797
theorem B2261687 : Blo 2261435 2261687 := bstep (se 1 (by rfl) ⟨1696265, by rfl⟩ : syracuseStep 2261687 = 3392531) B3392531
theorem B3816605 : Blo 2261435 3816605 := bbase (se 3 (by rfl) ⟨715613, by rfl⟩ : syracuseStep 3816605 = 1431227) (by norm_num)
theorem B2544403 : Blo 2261435 2544403 := bstep (se 1 (by rfl) ⟨1908302, by rfl⟩ : syracuseStep 2544403 = 3816605) B3816605
theorem B3392537 : Blo 2261435 3392537 := bstep (se 2 (by rfl) ⟨1272201, by rfl⟩ : syracuseStep 3392537 = 2544403) B2544403
theorem B2261691 : Blo 2261435 2261691 := bstep (se 1 (by rfl) ⟨1696268, by rfl⟩ : syracuseStep 2261691 = 3392537) B3392537
theorem B17409077 : Blo 2261435 17409077 := bbase (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) (by norm_num)
theorem B11606051 : Blo 2261435 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B7737367 : Blo 2261435 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B10316489 : Blo 2261435 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B110042549 : Blo 2261435 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B73361699 : Blo 2261435 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B48907799 : Blo 2261435 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B32605199 : Blo 2261435 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B21736799 : Blo 2261435 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B14491199 : Blo 2261435 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B9660799 : Blo 2261435 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B12881065 : Blo 2261435 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B17174753 : Blo 2261435 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B11449835 : Blo 2261435 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B7633223 : Blo 2261435 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B5088815 : Blo 2261435 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3392543 : Blo 2261435 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B2261695 : Blo 2261435 2261695 := bstep (se 1 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 2261695 = 3392543) B3392543
theorem B3392549 : Blo 2261435 3392549 := bbase (se 4 (by rfl) ⟨318051, by rfl⟩ : syracuseStep 3392549 = 636103) (by norm_num)
theorem B2261699 : Blo 2261435 2261699 := bstep (se 1 (by rfl) ⟨1696274, by rfl⟩ : syracuseStep 2261699 = 3392549) B3392549
theorem B2862469 : Blo 2261435 2862469 := bbase (se 4 (by rfl) ⟨268356, by rfl⟩ : syracuseStep 2862469 = 536713) (by norm_num)
theorem B3816625 : Blo 2261435 3816625 := bstep (se 2 (by rfl) ⟨1431234, by rfl⟩ : syracuseStep 3816625 = 2862469) B2862469
theorem B5088833 : Blo 2261435 5088833 := bstep (se 2 (by rfl) ⟨1908312, by rfl⟩ : syracuseStep 5088833 = 3816625) B3816625
theorem B3392555 : Blo 2261435 3392555 := bstep (se 1 (by rfl) ⟨2544416, by rfl⟩ : syracuseStep 3392555 = 5088833) B5088833
theorem B2261703 : Blo 2261435 2261703 := bstep (se 1 (by rfl) ⟨1696277, by rfl⟩ : syracuseStep 2261703 = 3392555) B3392555
theorem B2544421 : Blo 2261435 2544421 := bbase (se 4 (by rfl) ⟨238539, by rfl⟩ : syracuseStep 2544421 = 477079) (by norm_num)
theorem B3392561 : Blo 2261435 3392561 := bstep (se 2 (by rfl) ⟨1272210, by rfl⟩ : syracuseStep 3392561 = 2544421) B2544421
theorem B2261707 : Blo 2261435 2261707 := bstep (se 1 (by rfl) ⟨1696280, by rfl⟩ : syracuseStep 2261707 = 3392561) B3392561
theorem B9660869 : Blo 2261435 9660869 := bbase (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) (by norm_num)
theorem B6440579 : Blo 2261435 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B4293719 : Blo 2261435 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B2862479 : Blo 2261435 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B7633277 : Blo 2261435 7633277 := bstep (se 3 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 7633277 = 2862479) B2862479
theorem B5088851 : Blo 2261435 5088851 := bstep (se 1 (by rfl) ⟨3816638, by rfl⟩ : syracuseStep 5088851 = 7633277) B7633277
theorem B3392567 : Blo 2261435 3392567 := bstep (se 1 (by rfl) ⟨2544425, by rfl⟩ : syracuseStep 3392567 = 5088851) B5088851
theorem B2261711 : Blo 2261435 2261711 := bstep (se 1 (by rfl) ⟨1696283, by rfl⟩ : syracuseStep 2261711 = 3392567) B3392567
theorem B3392573 : Blo 2261435 3392573 := bbase (se 3 (by rfl) ⟨636107, by rfl⟩ : syracuseStep 3392573 = 1272215) (by norm_num)
theorem B2261715 : Blo 2261435 2261715 := bstep (se 1 (by rfl) ⟨1696286, by rfl⟩ : syracuseStep 2261715 = 3392573) B3392573
theorem B5088869 : Blo 2261435 5088869 := bbase (se 4 (by rfl) ⟨477081, by rfl⟩ : syracuseStep 5088869 = 954163) (by norm_num)
theorem B3392579 : Blo 2261435 3392579 := bstep (se 1 (by rfl) ⟨2544434, by rfl⟩ : syracuseStep 3392579 = 5088869) B5088869
theorem B2261719 : Blo 2261435 2261719 := bstep (se 1 (by rfl) ⟨1696289, by rfl⟩ : syracuseStep 2261719 = 3392579) B3392579
theorem B5724989 : Blo 2261435 5724989 := bbase (se 3 (by rfl) ⟨1073435, by rfl⟩ : syracuseStep 5724989 = 2146871) (by norm_num)
theorem B3816659 : Blo 2261435 3816659 := bstep (se 1 (by rfl) ⟨2862494, by rfl⟩ : syracuseStep 3816659 = 5724989) B5724989
theorem B2544439 : Blo 2261435 2544439 := bstep (se 1 (by rfl) ⟨1908329, by rfl⟩ : syracuseStep 2544439 = 3816659) B3816659
theorem B3392585 : Blo 2261435 3392585 := bstep (se 2 (by rfl) ⟨1272219, by rfl⟩ : syracuseStep 3392585 = 2544439) B2544439
theorem B2261723 : Blo 2261435 2261723 := bstep (se 1 (by rfl) ⟨1696292, by rfl⟩ : syracuseStep 2261723 = 3392585) B3392585
theorem B4293749 : Blo 2261435 4293749 := bbase (se 5 (by rfl) ⟨201269, by rfl⟩ : syracuseStep 4293749 = 402539) (by norm_num)
theorem B11449997 : Blo 2261435 11449997 := bstep (se 3 (by rfl) ⟨2146874, by rfl⟩ : syracuseStep 11449997 = 4293749) B4293749
theorem B7633331 : Blo 2261435 7633331 := bstep (se 1 (by rfl) ⟨5724998, by rfl⟩ : syracuseStep 7633331 = 11449997) B11449997
theorem B5088887 : Blo 2261435 5088887 := bstep (se 1 (by rfl) ⟨3816665, by rfl⟩ : syracuseStep 5088887 = 7633331) B7633331
theorem B3392591 : Blo 2261435 3392591 := bstep (se 1 (by rfl) ⟨2544443, by rfl⟩ : syracuseStep 3392591 = 5088887) B5088887
theorem B2261727 : Blo 2261435 2261727 := bstep (se 1 (by rfl) ⟨1696295, by rfl⟩ : syracuseStep 2261727 = 3392591) B3392591
theorem B3392597 : Blo 2261435 3392597 := bbase (se 8 (by rfl) ⟨19878, by rfl⟩ : syracuseStep 3392597 = 39757) (by norm_num)
theorem B2261731 : Blo 2261435 2261731 := bstep (se 1 (by rfl) ⟨1696298, by rfl⟩ : syracuseStep 2261731 = 3392597) B3392597
theorem B8151445 : Blo 2261435 8151445 := bbase (se 6 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 8151445 = 382099) (by norm_num)
theorem B10868593 : Blo 2261435 10868593 := bstep (se 2 (by rfl) ⟨4075722, by rfl⟩ : syracuseStep 10868593 = 8151445) B8151445
theorem B14491457 : Blo 2261435 14491457 := bstep (se 2 (by rfl) ⟨5434296, by rfl⟩ : syracuseStep 14491457 = 10868593) B10868593
theorem B9660971 : Blo 2261435 9660971 := bstep (se 1 (by rfl) ⟨7245728, by rfl⟩ : syracuseStep 9660971 = 14491457) B14491457
theorem B6440647 : Blo 2261435 6440647 := bstep (se 1 (by rfl) ⟨4830485, by rfl⟩ : syracuseStep 6440647 = 9660971) B9660971
theorem B8587529 : Blo 2261435 8587529 := bstep (se 2 (by rfl) ⟨3220323, by rfl⟩ : syracuseStep 8587529 = 6440647) B6440647
theorem B5725019 : Blo 2261435 5725019 := bstep (se 1 (by rfl) ⟨4293764, by rfl⟩ : syracuseStep 5725019 = 8587529) B8587529
theorem B3816679 : Blo 2261435 3816679 := bstep (se 1 (by rfl) ⟨2862509, by rfl⟩ : syracuseStep 3816679 = 5725019) B5725019
theorem B5088905 : Blo 2261435 5088905 := bstep (se 2 (by rfl) ⟨1908339, by rfl⟩ : syracuseStep 5088905 = 3816679) B3816679
theorem B3392603 : Blo 2261435 3392603 := bstep (se 1 (by rfl) ⟨2544452, by rfl⟩ : syracuseStep 3392603 = 5088905) B5088905
theorem B2261735 : Blo 2261435 2261735 := bstep (se 1 (by rfl) ⟨1696301, by rfl⟩ : syracuseStep 2261735 = 3392603) B3392603
theorem B2544457 : Blo 2261435 2544457 := bbase (se 2 (by rfl) ⟨954171, by rfl⟩ : syracuseStep 2544457 = 1908343) (by norm_num)
theorem B3392609 : Blo 2261435 3392609 := bstep (se 2 (by rfl) ⟨1272228, by rfl⟩ : syracuseStep 3392609 = 2544457) B2544457
theorem B2261739 : Blo 2261435 2261739 := bstep (se 1 (by rfl) ⟨1696304, by rfl⟩ : syracuseStep 2261739 = 3392609) B3392609
theorem B6113605 : Blo 2261435 6113605 := bbase (se 4 (by rfl) ⟨573150, by rfl⟩ : syracuseStep 6113605 = 1146301) (by norm_num)
theorem B8151473 : Blo 2261435 8151473 := bstep (se 2 (by rfl) ⟨3056802, by rfl⟩ : syracuseStep 8151473 = 6113605) B6113605
theorem B21737261 : Blo 2261435 21737261 := bstep (se 3 (by rfl) ⟨4075736, by rfl⟩ : syracuseStep 21737261 = 8151473) B8151473
theorem B14491507 : Blo 2261435 14491507 := bstep (se 1 (by rfl) ⟨10868630, by rfl⟩ : syracuseStep 14491507 = 21737261) B21737261
theorem B19322009 : Blo 2261435 19322009 := bstep (se 2 (by rfl) ⟨7245753, by rfl⟩ : syracuseStep 19322009 = 14491507) B14491507
theorem B12881339 : Blo 2261435 12881339 := bstep (se 1 (by rfl) ⟨9661004, by rfl⟩ : syracuseStep 12881339 = 19322009) B19322009
theorem B8587559 : Blo 2261435 8587559 := bstep (se 1 (by rfl) ⟨6440669, by rfl⟩ : syracuseStep 8587559 = 12881339) B12881339
theorem B5725039 : Blo 2261435 5725039 := bstep (se 1 (by rfl) ⟨4293779, by rfl⟩ : syracuseStep 5725039 = 8587559) B8587559
theorem B7633385 : Blo 2261435 7633385 := bstep (se 2 (by rfl) ⟨2862519, by rfl⟩ : syracuseStep 7633385 = 5725039) B5725039
theorem B5088923 : Blo 2261435 5088923 := bstep (se 1 (by rfl) ⟨3816692, by rfl⟩ : syracuseStep 5088923 = 7633385) B7633385
theorem B3392615 : Blo 2261435 3392615 := bstep (se 1 (by rfl) ⟨2544461, by rfl⟩ : syracuseStep 3392615 = 5088923) B5088923
theorem B2261743 : Blo 2261435 2261743 := bstep (se 1 (by rfl) ⟨1696307, by rfl⟩ : syracuseStep 2261743 = 3392615) B3392615
theorem B3392621 : Blo 2261435 3392621 := bbase (se 3 (by rfl) ⟨636116, by rfl⟩ : syracuseStep 3392621 = 1272233) (by norm_num)
theorem B2261747 : Blo 2261435 2261747 := bstep (se 1 (by rfl) ⟨1696310, by rfl⟩ : syracuseStep 2261747 = 3392621) B3392621
theorem B5088941 : Blo 2261435 5088941 := bbase (se 3 (by rfl) ⟨954176, by rfl⟩ : syracuseStep 5088941 = 1908353) (by norm_num)
theorem B3392627 : Blo 2261435 3392627 := bstep (se 1 (by rfl) ⟨2544470, by rfl⟩ : syracuseStep 3392627 = 5088941) B5088941
theorem B2261751 : Blo 2261435 2261751 := bstep (se 1 (by rfl) ⟨1696313, by rfl⟩ : syracuseStep 2261751 = 3392627) B3392627
theorem B2717173 : Blo 2261435 2717173 := bbase (se 5 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 2717173 = 254735) (by norm_num)
theorem B3622897 : Blo 2261435 3622897 := bstep (se 2 (by rfl) ⟨1358586, by rfl⟩ : syracuseStep 3622897 = 2717173) B2717173
theorem B4830529 : Blo 2261435 4830529 := bstep (se 2 (by rfl) ⟨1811448, by rfl⟩ : syracuseStep 4830529 = 3622897) B3622897
theorem B6440705 : Blo 2261435 6440705 := bstep (se 2 (by rfl) ⟨2415264, by rfl⟩ : syracuseStep 6440705 = 4830529) B4830529
theorem B4293803 : Blo 2261435 4293803 := bstep (se 1 (by rfl) ⟨3220352, by rfl⟩ : syracuseStep 4293803 = 6440705) B6440705
theorem B2862535 : Blo 2261435 2862535 := bstep (se 1 (by rfl) ⟨2146901, by rfl⟩ : syracuseStep 2862535 = 4293803) B4293803
theorem B3816713 : Blo 2261435 3816713 := bstep (se 2 (by rfl) ⟨1431267, by rfl⟩ : syracuseStep 3816713 = 2862535) B2862535
theorem B2544475 : Blo 2261435 2544475 := bstep (se 1 (by rfl) ⟨1908356, by rfl⟩ : syracuseStep 2544475 = 3816713) B3816713
theorem B3392633 : Blo 2261435 3392633 := bstep (se 2 (by rfl) ⟨1272237, by rfl⟩ : syracuseStep 3392633 = 2544475) B2544475
theorem B2261755 : Blo 2261435 2261755 := bstep (se 1 (by rfl) ⟨1696316, by rfl⟩ : syracuseStep 2261755 = 3392633) B3392633
theorem B4075765 : Blo 2261435 4075765 := bbase (se 5 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 4075765 = 382103) (by norm_num)
theorem B21737413 : Blo 2261435 21737413 := bstep (se 4 (by rfl) ⟨2037882, by rfl⟩ : syracuseStep 21737413 = 4075765) B4075765
theorem B28983217 : Blo 2261435 28983217 := bstep (se 2 (by rfl) ⟨10868706, by rfl⟩ : syracuseStep 28983217 = 21737413) B21737413
theorem B38644289 : Blo 2261435 38644289 := bstep (se 2 (by rfl) ⟨14491608, by rfl⟩ : syracuseStep 38644289 = 28983217) B28983217
theorem B25762859 : Blo 2261435 25762859 := bstep (se 1 (by rfl) ⟨19322144, by rfl⟩ : syracuseStep 25762859 = 38644289) B38644289
theorem B17175239 : Blo 2261435 17175239 := bstep (se 1 (by rfl) ⟨12881429, by rfl⟩ : syracuseStep 17175239 = 25762859) B25762859
theorem B11450159 : Blo 2261435 11450159 := bstep (se 1 (by rfl) ⟨8587619, by rfl⟩ : syracuseStep 11450159 = 17175239) B17175239
theorem B7633439 : Blo 2261435 7633439 := bstep (se 1 (by rfl) ⟨5725079, by rfl⟩ : syracuseStep 7633439 = 11450159) B11450159
theorem B5088959 : Blo 2261435 5088959 := bstep (se 1 (by rfl) ⟨3816719, by rfl⟩ : syracuseStep 5088959 = 7633439) B7633439
theorem B3392639 : Blo 2261435 3392639 := bstep (se 1 (by rfl) ⟨2544479, by rfl⟩ : syracuseStep 3392639 = 5088959) B5088959
theorem B2261759 : Blo 2261435 2261759 := bstep (se 1 (by rfl) ⟨1696319, by rfl⟩ : syracuseStep 2261759 = 3392639) B3392639
theorem B3392645 : Blo 2261435 3392645 := bbase (se 4 (by rfl) ⟨318060, by rfl⟩ : syracuseStep 3392645 = 636121) (by norm_num)
theorem B2261763 : Blo 2261435 2261763 := bstep (se 1 (by rfl) ⟨1696322, by rfl⟩ : syracuseStep 2261763 = 3392645) B3392645
theorem B3816733 : Blo 2261435 3816733 := bbase (se 3 (by rfl) ⟨715637, by rfl⟩ : syracuseStep 3816733 = 1431275) (by norm_num)
theorem B5088977 : Blo 2261435 5088977 := bstep (se 2 (by rfl) ⟨1908366, by rfl⟩ : syracuseStep 5088977 = 3816733) B3816733
theorem B3392651 : Blo 2261435 3392651 := bstep (se 1 (by rfl) ⟨2544488, by rfl⟩ : syracuseStep 3392651 = 5088977) B5088977
theorem B2261767 : Blo 2261435 2261767 := bstep (se 1 (by rfl) ⟨1696325, by rfl⟩ : syracuseStep 2261767 = 3392651) B3392651
theorem B2544493 : Blo 2261435 2544493 := bbase (se 3 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 2544493 = 954185) (by norm_num)
theorem B3392657 : Blo 2261435 3392657 := bstep (se 2 (by rfl) ⟨1272246, by rfl⟩ : syracuseStep 3392657 = 2544493) B2544493
theorem B2261771 : Blo 2261435 2261771 := bstep (se 1 (by rfl) ⟨1696328, by rfl⟩ : syracuseStep 2261771 = 3392657) B3392657
theorem B7633493 : Blo 2261435 7633493 := bbase (se 8 (by rfl) ⟨44727, by rfl⟩ : syracuseStep 7633493 = 89455) (by norm_num)
theorem B5088995 : Blo 2261435 5088995 := bstep (se 1 (by rfl) ⟨3816746, by rfl⟩ : syracuseStep 5088995 = 7633493) B7633493
theorem B3392663 : Blo 2261435 3392663 := bstep (se 1 (by rfl) ⟨2544497, by rfl⟩ : syracuseStep 3392663 = 5088995) B5088995
theorem B2261775 : Blo 2261435 2261775 := bstep (se 1 (by rfl) ⟨1696331, by rfl⟩ : syracuseStep 2261775 = 3392663) B3392663
theorem B3392669 : Blo 2261435 3392669 := bbase (se 3 (by rfl) ⟨636125, by rfl⟩ : syracuseStep 3392669 = 1272251) (by norm_num)
theorem B2261779 : Blo 2261435 2261779 := bstep (se 1 (by rfl) ⟨1696334, by rfl⟩ : syracuseStep 2261779 = 3392669) B3392669
theorem B5089013 : Blo 2261435 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B3392675 : Blo 2261435 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B2261783 : Blo 2261435 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B4647853 : Blo 2261435 4647853 := bbase (se 3 (by rfl) ⟨871472, by rfl⟩ : syracuseStep 4647853 = 1742945) (by norm_num)
theorem B6197137 : Blo 2261435 6197137 := bstep (se 2 (by rfl) ⟨2323926, by rfl⟩ : syracuseStep 6197137 = 4647853) B4647853
theorem B33051397 : Blo 2261435 33051397 := bstep (se 4 (by rfl) ⟨3098568, by rfl⟩ : syracuseStep 33051397 = 6197137) B6197137
theorem B44068529 : Blo 2261435 44068529 := bstep (se 2 (by rfl) ⟨16525698, by rfl⟩ : syracuseStep 44068529 = 33051397) B33051397
theorem B29379019 : Blo 2261435 29379019 := bstep (se 1 (by rfl) ⟨22034264, by rfl⟩ : syracuseStep 29379019 = 44068529) B44068529
theorem B39172025 : Blo 2261435 39172025 := bstep (se 2 (by rfl) ⟨14689509, by rfl⟩ : syracuseStep 39172025 = 29379019) B29379019
theorem B26114683 : Blo 2261435 26114683 := bstep (se 1 (by rfl) ⟨19586012, by rfl⟩ : syracuseStep 26114683 = 39172025) B39172025
theorem B34819577 : Blo 2261435 34819577 := bstep (se 2 (by rfl) ⟨13057341, by rfl⟩ : syracuseStep 34819577 = 26114683) B26114683
theorem B23213051 : Blo 2261435 23213051 := bstep (se 1 (by rfl) ⟨17409788, by rfl⟩ : syracuseStep 23213051 = 34819577) B34819577
theorem B15475367 : Blo 2261435 15475367 := bstep (se 1 (by rfl) ⟨11606525, by rfl⟩ : syracuseStep 15475367 = 23213051) B23213051
theorem B10316911 : Blo 2261435 10316911 := bstep (se 1 (by rfl) ⟨7737683, by rfl⟩ : syracuseStep 10316911 = 15475367) B15475367
theorem B13755881 : Blo 2261435 13755881 := bstep (se 2 (by rfl) ⟨5158455, by rfl⟩ : syracuseStep 13755881 = 10316911) B10316911
theorem B9170587 : Blo 2261435 9170587 := bstep (se 1 (by rfl) ⟨6877940, by rfl⟩ : syracuseStep 9170587 = 13755881) B13755881
theorem B12227449 : Blo 2261435 12227449 := bstep (se 2 (by rfl) ⟨4585293, by rfl⟩ : syracuseStep 12227449 = 9170587) B9170587
theorem B16303265 : Blo 2261435 16303265 := bstep (se 2 (by rfl) ⟨6113724, by rfl⟩ : syracuseStep 16303265 = 12227449) B12227449
theorem B10868843 : Blo 2261435 10868843 := bstep (se 1 (by rfl) ⟨8151632, by rfl⟩ : syracuseStep 10868843 = 16303265) B16303265
theorem B28983581 : Blo 2261435 28983581 := bstep (se 3 (by rfl) ⟨5434421, by rfl⟩ : syracuseStep 28983581 = 10868843) B10868843
theorem B19322387 : Blo 2261435 19322387 := bstep (se 1 (by rfl) ⟨14491790, by rfl⟩ : syracuseStep 19322387 = 28983581) B28983581
theorem B12881591 : Blo 2261435 12881591 := bstep (se 1 (by rfl) ⟨9661193, by rfl⟩ : syracuseStep 12881591 = 19322387) B19322387
theorem B8587727 : Blo 2261435 8587727 := bstep (se 1 (by rfl) ⟨6440795, by rfl⟩ : syracuseStep 8587727 = 12881591) B12881591
theorem B5725151 : Blo 2261435 5725151 := bstep (se 1 (by rfl) ⟨4293863, by rfl⟩ : syracuseStep 5725151 = 8587727) B8587727
theorem B3816767 : Blo 2261435 3816767 := bstep (se 1 (by rfl) ⟨2862575, by rfl⟩ : syracuseStep 3816767 = 5725151) B5725151
theorem B2544511 : Blo 2261435 2544511 := bstep (se 1 (by rfl) ⟨1908383, by rfl⟩ : syracuseStep 2544511 = 3816767) B3816767
theorem B3392681 : Blo 2261435 3392681 := bstep (se 2 (by rfl) ⟨1272255, by rfl⟩ : syracuseStep 3392681 = 2544511) B2544511
theorem B2261787 : Blo 2261435 2261787 := bstep (se 1 (by rfl) ⟨1696340, by rfl⟩ : syracuseStep 2261787 = 3392681) B3392681
theorem B4830605 : Blo 2261435 4830605 := bbase (se 3 (by rfl) ⟨905738, by rfl⟩ : syracuseStep 4830605 = 1811477) (by norm_num)
theorem B3220403 : Blo 2261435 3220403 := bstep (se 1 (by rfl) ⟨2415302, by rfl⟩ : syracuseStep 3220403 = 4830605) B4830605
theorem B8587741 : Blo 2261435 8587741 := bstep (se 3 (by rfl) ⟨1610201, by rfl⟩ : syracuseStep 8587741 = 3220403) B3220403
theorem B11450321 : Blo 2261435 11450321 := bstep (se 2 (by rfl) ⟨4293870, by rfl⟩ : syracuseStep 11450321 = 8587741) B8587741
theorem B7633547 : Blo 2261435 7633547 := bstep (se 1 (by rfl) ⟨5725160, by rfl⟩ : syracuseStep 7633547 = 11450321) B11450321
theorem B5089031 : Blo 2261435 5089031 := bstep (se 1 (by rfl) ⟨3816773, by rfl⟩ : syracuseStep 5089031 = 7633547) B7633547
theorem B3392687 : Blo 2261435 3392687 := bstep (se 1 (by rfl) ⟨2544515, by rfl⟩ : syracuseStep 3392687 = 5089031) B5089031
theorem B2261791 : Blo 2261435 2261791 := bstep (se 1 (by rfl) ⟨1696343, by rfl⟩ : syracuseStep 2261791 = 3392687) B3392687
theorem B3392693 : Blo 2261435 3392693 := bbase (se 5 (by rfl) ⟨159032, by rfl⟩ : syracuseStep 3392693 = 318065) (by norm_num)
theorem B2261795 : Blo 2261435 2261795 := bstep (se 1 (by rfl) ⟨1696346, by rfl⟩ : syracuseStep 2261795 = 3392693) B3392693
theorem B5725181 : Blo 2261435 5725181 := bbase (se 3 (by rfl) ⟨1073471, by rfl⟩ : syracuseStep 5725181 = 2146943) (by norm_num)
theorem B3816787 : Blo 2261435 3816787 := bstep (se 1 (by rfl) ⟨2862590, by rfl⟩ : syracuseStep 3816787 = 5725181) B5725181
theorem B5089049 : Blo 2261435 5089049 := bstep (se 2 (by rfl) ⟨1908393, by rfl⟩ : syracuseStep 5089049 = 3816787) B3816787
theorem B3392699 : Blo 2261435 3392699 := bstep (se 1 (by rfl) ⟨2544524, by rfl⟩ : syracuseStep 3392699 = 5089049) B5089049
theorem B2261799 : Blo 2261435 2261799 := bstep (se 1 (by rfl) ⟨1696349, by rfl⟩ : syracuseStep 2261799 = 3392699) B3392699
theorem B2544529 : Blo 2261435 2544529 := bbase (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) (by norm_num)
theorem B3392705 : Blo 2261435 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B2261803 : Blo 2261435 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B4293901 : Blo 2261435 4293901 := bbase (se 3 (by rfl) ⟨805106, by rfl⟩ : syracuseStep 4293901 = 1610213) (by norm_num)
theorem B5725201 : Blo 2261435 5725201 := bstep (se 2 (by rfl) ⟨2146950, by rfl⟩ : syracuseStep 5725201 = 4293901) B4293901
theorem B7633601 : Blo 2261435 7633601 := bstep (se 2 (by rfl) ⟨2862600, by rfl⟩ : syracuseStep 7633601 = 5725201) B5725201
theorem B5089067 : Blo 2261435 5089067 := bstep (se 1 (by rfl) ⟨3816800, by rfl⟩ : syracuseStep 5089067 = 7633601) B7633601
theorem B3392711 : Blo 2261435 3392711 := bstep (se 1 (by rfl) ⟨2544533, by rfl⟩ : syracuseStep 3392711 = 5089067) B5089067
theorem B2261807 : Blo 2261435 2261807 := bstep (se 1 (by rfl) ⟨1696355, by rfl⟩ : syracuseStep 2261807 = 3392711) B3392711
theorem B3392717 : Blo 2261435 3392717 := bbase (se 3 (by rfl) ⟨636134, by rfl⟩ : syracuseStep 3392717 = 1272269) (by norm_num)
theorem B2261811 : Blo 2261435 2261811 := bstep (se 1 (by rfl) ⟨1696358, by rfl⟩ : syracuseStep 2261811 = 3392717) B3392717
theorem B5089085 : Blo 2261435 5089085 := bbase (se 3 (by rfl) ⟨954203, by rfl⟩ : syracuseStep 5089085 = 1908407) (by norm_num)
theorem B3392723 : Blo 2261435 3392723 := bstep (se 1 (by rfl) ⟨2544542, by rfl⟩ : syracuseStep 3392723 = 5089085) B5089085
theorem B2261815 : Blo 2261435 2261815 := bstep (se 1 (by rfl) ⟨1696361, by rfl⟩ : syracuseStep 2261815 = 3392723) B3392723
theorem B3816821 : Blo 2261435 3816821 := bbase (se 5 (by rfl) ⟨178913, by rfl⟩ : syracuseStep 3816821 = 357827) (by norm_num)
theorem B2544547 : Blo 2261435 2544547 := bstep (se 1 (by rfl) ⟨1908410, by rfl⟩ : syracuseStep 2544547 = 3816821) B3816821
theorem B3392729 : Blo 2261435 3392729 := bstep (se 2 (by rfl) ⟨1272273, by rfl⟩ : syracuseStep 3392729 = 2544547) B2544547
theorem B2261819 : Blo 2261435 2261819 := bstep (se 1 (by rfl) ⟨1696364, by rfl⟩ : syracuseStep 2261819 = 3392729) B3392729
theorem B3623005 : Blo 2261435 3623005 := bbase (se 3 (by rfl) ⟨679313, by rfl⟩ : syracuseStep 3623005 = 1358627) (by norm_num)
theorem B4830673 : Blo 2261435 4830673 := bstep (se 2 (by rfl) ⟨1811502, by rfl⟩ : syracuseStep 4830673 = 3623005) B3623005
theorem B6440897 : Blo 2261435 6440897 := bstep (se 2 (by rfl) ⟨2415336, by rfl⟩ : syracuseStep 6440897 = 4830673) B4830673
theorem B17175725 : Blo 2261435 17175725 := bstep (se 3 (by rfl) ⟨3220448, by rfl⟩ : syracuseStep 17175725 = 6440897) B6440897
theorem B11450483 : Blo 2261435 11450483 := bstep (se 1 (by rfl) ⟨8587862, by rfl⟩ : syracuseStep 11450483 = 17175725) B17175725
theorem B7633655 : Blo 2261435 7633655 := bstep (se 1 (by rfl) ⟨5725241, by rfl⟩ : syracuseStep 7633655 = 11450483) B11450483
theorem B5089103 : Blo 2261435 5089103 := bstep (se 1 (by rfl) ⟨3816827, by rfl⟩ : syracuseStep 5089103 = 7633655) B7633655
theorem B3392735 : Blo 2261435 3392735 := bstep (se 1 (by rfl) ⟨2544551, by rfl⟩ : syracuseStep 3392735 = 5089103) B5089103
theorem B2261823 : Blo 2261435 2261823 := bstep (se 1 (by rfl) ⟨1696367, by rfl⟩ : syracuseStep 2261823 = 3392735) B3392735
theorem B3392741 : Blo 2261435 3392741 := bbase (se 4 (by rfl) ⟨318069, by rfl⟩ : syracuseStep 3392741 = 636139) (by norm_num)
theorem B2261827 : Blo 2261435 2261827 := bstep (se 1 (by rfl) ⟨1696370, by rfl⟩ : syracuseStep 2261827 = 3392741) B3392741
theorem B7246037 : Blo 2261435 7246037 := bbase (se 7 (by rfl) ⟨84914, by rfl⟩ : syracuseStep 7246037 = 169829) (by norm_num)
theorem B4830691 : Blo 2261435 4830691 := bstep (se 1 (by rfl) ⟨3623018, by rfl⟩ : syracuseStep 4830691 = 7246037) B7246037
theorem B6440921 : Blo 2261435 6440921 := bstep (se 2 (by rfl) ⟨2415345, by rfl⟩ : syracuseStep 6440921 = 4830691) B4830691
theorem B4293947 : Blo 2261435 4293947 := bstep (se 1 (by rfl) ⟨3220460, by rfl⟩ : syracuseStep 4293947 = 6440921) B6440921
theorem B2862631 : Blo 2261435 2862631 := bstep (se 1 (by rfl) ⟨2146973, by rfl⟩ : syracuseStep 2862631 = 4293947) B4293947
theorem B3816841 : Blo 2261435 3816841 := bstep (se 2 (by rfl) ⟨1431315, by rfl⟩ : syracuseStep 3816841 = 2862631) B2862631
theorem B5089121 : Blo 2261435 5089121 := bstep (se 2 (by rfl) ⟨1908420, by rfl⟩ : syracuseStep 5089121 = 3816841) B3816841
theorem B3392747 : Blo 2261435 3392747 := bstep (se 1 (by rfl) ⟨2544560, by rfl⟩ : syracuseStep 3392747 = 5089121) B5089121
theorem B2261831 : Blo 2261435 2261831 := bstep (se 1 (by rfl) ⟨1696373, by rfl⟩ : syracuseStep 2261831 = 3392747) B3392747
theorem B2544565 : Blo 2261435 2544565 := bbase (se 5 (by rfl) ⟨119276, by rfl⟩ : syracuseStep 2544565 = 238553) (by norm_num)
theorem B3392753 : Blo 2261435 3392753 := bstep (se 2 (by rfl) ⟨1272282, by rfl⟩ : syracuseStep 3392753 = 2544565) B2544565
theorem B2261835 : Blo 2261435 2261835 := bstep (se 1 (by rfl) ⟨1696376, by rfl⟩ : syracuseStep 2261835 = 3392753) B3392753
theorem B2862641 : Blo 2261435 2862641 := bbase (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) (by norm_num)
theorem B7633709 : Blo 2261435 7633709 := bstep (se 3 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 7633709 = 2862641) B2862641
theorem B5089139 : Blo 2261435 5089139 := bstep (se 1 (by rfl) ⟨3816854, by rfl⟩ : syracuseStep 5089139 = 7633709) B7633709
theorem B3392759 : Blo 2261435 3392759 := bstep (se 1 (by rfl) ⟨2544569, by rfl⟩ : syracuseStep 3392759 = 5089139) B5089139
theorem B2261839 : Blo 2261435 2261839 := bstep (se 1 (by rfl) ⟨1696379, by rfl⟩ : syracuseStep 2261839 = 3392759) B3392759
theorem B3392765 : Blo 2261435 3392765 := bbase (se 3 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 3392765 = 1272287) (by norm_num)
theorem B2261843 : Blo 2261435 2261843 := bstep (se 1 (by rfl) ⟨1696382, by rfl⟩ : syracuseStep 2261843 = 3392765) B3392765
theorem B5089157 : Blo 2261435 5089157 := bbase (se 4 (by rfl) ⟨477108, by rfl⟩ : syracuseStep 5089157 = 954217) (by norm_num)
theorem B3392771 : Blo 2261435 3392771 := bstep (se 1 (by rfl) ⟨2544578, by rfl⟩ : syracuseStep 3392771 = 5089157) B5089157
theorem B2261847 : Blo 2261435 2261847 := bstep (se 1 (by rfl) ⟨1696385, by rfl⟩ : syracuseStep 2261847 = 3392771) B3392771
theorem B4075933 : Blo 2261435 4075933 := bbase (se 3 (by rfl) ⟨764237, by rfl⟩ : syracuseStep 4075933 = 1528475) (by norm_num)
theorem B5434577 : Blo 2261435 5434577 := bstep (se 2 (by rfl) ⟨2037966, by rfl⟩ : syracuseStep 5434577 = 4075933) B4075933
theorem B3623051 : Blo 2261435 3623051 := bstep (se 1 (by rfl) ⟨2717288, by rfl⟩ : syracuseStep 3623051 = 5434577) B5434577
theorem B2415367 : Blo 2261435 2415367 := bstep (se 1 (by rfl) ⟨1811525, by rfl⟩ : syracuseStep 2415367 = 3623051) B3623051
theorem B3220489 : Blo 2261435 3220489 := bstep (se 2 (by rfl) ⟨1207683, by rfl⟩ : syracuseStep 3220489 = 2415367) B2415367
theorem B4293985 : Blo 2261435 4293985 := bstep (se 2 (by rfl) ⟨1610244, by rfl⟩ : syracuseStep 4293985 = 3220489) B3220489
theorem B5725313 : Blo 2261435 5725313 := bstep (se 2 (by rfl) ⟨2146992, by rfl⟩ : syracuseStep 5725313 = 4293985) B4293985
theorem B3816875 : Blo 2261435 3816875 := bstep (se 1 (by rfl) ⟨2862656, by rfl⟩ : syracuseStep 3816875 = 5725313) B5725313
theorem B2544583 : Blo 2261435 2544583 := bstep (se 1 (by rfl) ⟨1908437, by rfl⟩ : syracuseStep 2544583 = 3816875) B3816875
theorem B3392777 : Blo 2261435 3392777 := bstep (se 2 (by rfl) ⟨1272291, by rfl⟩ : syracuseStep 3392777 = 2544583) B2544583
theorem B2261851 : Blo 2261435 2261851 := bstep (se 1 (by rfl) ⟨1696388, by rfl⟩ : syracuseStep 2261851 = 3392777) B3392777
theorem B11450645 : Blo 2261435 11450645 := bbase (se 6 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 11450645 = 536749) (by norm_num)
theorem B7633763 : Blo 2261435 7633763 := bstep (se 1 (by rfl) ⟨5725322, by rfl⟩ : syracuseStep 7633763 = 11450645) B11450645
theorem B5089175 : Blo 2261435 5089175 := bstep (se 1 (by rfl) ⟨3816881, by rfl⟩ : syracuseStep 5089175 = 7633763) B7633763
theorem B3392783 : Blo 2261435 3392783 := bstep (se 1 (by rfl) ⟨2544587, by rfl⟩ : syracuseStep 3392783 = 5089175) B5089175
theorem B2261855 : Blo 2261435 2261855 := bstep (se 1 (by rfl) ⟨1696391, by rfl⟩ : syracuseStep 2261855 = 3392783) B3392783
theorem B3392789 : Blo 2261435 3392789 := bbase (se 6 (by rfl) ⟨79518, by rfl⟩ : syracuseStep 3392789 = 159037) (by norm_num)
theorem B2261859 : Blo 2261435 2261859 := bstep (se 1 (by rfl) ⟨1696394, by rfl⟩ : syracuseStep 2261859 = 3392789) B3392789
theorem B55025365 : Blo 2261435 55025365 := bbase (se 7 (by rfl) ⟨644828, by rfl⟩ : syracuseStep 55025365 = 1289657) (by norm_num)
theorem B73367153 : Blo 2261435 73367153 := bstep (se 2 (by rfl) ⟨27512682, by rfl⟩ : syracuseStep 73367153 = 55025365) B55025365
theorem B48911435 : Blo 2261435 48911435 := bstep (se 1 (by rfl) ⟨36683576, by rfl⟩ : syracuseStep 48911435 = 73367153) B73367153
theorem B32607623 : Blo 2261435 32607623 := bstep (se 1 (by rfl) ⟨24455717, by rfl⟩ : syracuseStep 32607623 = 48911435) B48911435
theorem B21738415 : Blo 2261435 21738415 := bstep (se 1 (by rfl) ⟨16303811, by rfl⟩ : syracuseStep 21738415 = 32607623) B32607623
theorem B28984553 : Blo 2261435 28984553 := bstep (se 2 (by rfl) ⟨10869207, by rfl⟩ : syracuseStep 28984553 = 21738415) B21738415
theorem B19323035 : Blo 2261435 19323035 := bstep (se 1 (by rfl) ⟨14492276, by rfl⟩ : syracuseStep 19323035 = 28984553) B28984553
theorem B12882023 : Blo 2261435 12882023 := bstep (se 1 (by rfl) ⟨9661517, by rfl⟩ : syracuseStep 12882023 = 19323035) B19323035
theorem B8588015 : Blo 2261435 8588015 := bstep (se 1 (by rfl) ⟨6441011, by rfl⟩ : syracuseStep 8588015 = 12882023) B12882023
theorem B5725343 : Blo 2261435 5725343 := bstep (se 1 (by rfl) ⟨4294007, by rfl⟩ : syracuseStep 5725343 = 8588015) B8588015
theorem B3816895 : Blo 2261435 3816895 := bstep (se 1 (by rfl) ⟨2862671, by rfl⟩ : syracuseStep 3816895 = 5725343) B5725343
theorem B5089193 : Blo 2261435 5089193 := bstep (se 2 (by rfl) ⟨1908447, by rfl⟩ : syracuseStep 5089193 = 3816895) B3816895
theorem B3392795 : Blo 2261435 3392795 := bstep (se 1 (by rfl) ⟨2544596, by rfl⟩ : syracuseStep 3392795 = 5089193) B5089193
theorem B2261863 : Blo 2261435 2261863 := bstep (se 1 (by rfl) ⟨1696397, by rfl⟩ : syracuseStep 2261863 = 3392795) B3392795
theorem B2544601 : Blo 2261435 2544601 := bbase (se 2 (by rfl) ⟨954225, by rfl⟩ : syracuseStep 2544601 = 1908451) (by norm_num)
theorem B3392801 : Blo 2261435 3392801 := bstep (se 2 (by rfl) ⟨1272300, by rfl⟩ : syracuseStep 3392801 = 2544601) B2544601
theorem B2261867 : Blo 2261435 2261867 := bstep (se 1 (by rfl) ⟨1696400, by rfl⟩ : syracuseStep 2261867 = 3392801) B3392801
theorem B3220517 : Blo 2261435 3220517 := bbase (se 4 (by rfl) ⟨301923, by rfl⟩ : syracuseStep 3220517 = 603847) (by norm_num)
theorem B8588045 : Blo 2261435 8588045 := bstep (se 3 (by rfl) ⟨1610258, by rfl⟩ : syracuseStep 8588045 = 3220517) B3220517
theorem B5725363 : Blo 2261435 5725363 := bstep (se 1 (by rfl) ⟨4294022, by rfl⟩ : syracuseStep 5725363 = 8588045) B8588045
theorem B7633817 : Blo 2261435 7633817 := bstep (se 2 (by rfl) ⟨2862681, by rfl⟩ : syracuseStep 7633817 = 5725363) B5725363
theorem B5089211 : Blo 2261435 5089211 := bstep (se 1 (by rfl) ⟨3816908, by rfl⟩ : syracuseStep 5089211 = 7633817) B7633817
theorem B3392807 : Blo 2261435 3392807 := bstep (se 1 (by rfl) ⟨2544605, by rfl⟩ : syracuseStep 3392807 = 5089211) B5089211
theorem B2261871 : Blo 2261435 2261871 := bstep (se 1 (by rfl) ⟨1696403, by rfl⟩ : syracuseStep 2261871 = 3392807) B3392807
theorem B3392813 : Blo 2261435 3392813 := bbase (se 3 (by rfl) ⟨636152, by rfl⟩ : syracuseStep 3392813 = 1272305) (by norm_num)
theorem B2261875 : Blo 2261435 2261875 := bstep (se 1 (by rfl) ⟨1696406, by rfl⟩ : syracuseStep 2261875 = 3392813) B3392813
theorem B5089229 : Blo 2261435 5089229 := bbase (se 3 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 5089229 = 1908461) (by norm_num)
theorem B3392819 : Blo 2261435 3392819 := bstep (se 1 (by rfl) ⟨2544614, by rfl⟩ : syracuseStep 3392819 = 5089229) B5089229
theorem B2261879 : Blo 2261435 2261879 := bstep (se 1 (by rfl) ⟨1696409, by rfl⟩ : syracuseStep 2261879 = 3392819) B3392819
theorem B2862697 : Blo 2261435 2862697 := bbase (se 2 (by rfl) ⟨1073511, by rfl⟩ : syracuseStep 2862697 = 2147023) (by norm_num)
theorem B3816929 : Blo 2261435 3816929 := bstep (se 2 (by rfl) ⟨1431348, by rfl⟩ : syracuseStep 3816929 = 2862697) B2862697
theorem B2544619 : Blo 2261435 2544619 := bstep (se 1 (by rfl) ⟨1908464, by rfl⟩ : syracuseStep 2544619 = 3816929) B3816929
theorem B3392825 : Blo 2261435 3392825 := bstep (se 2 (by rfl) ⟨1272309, by rfl⟩ : syracuseStep 3392825 = 2544619) B2544619
theorem B2261883 : Blo 2261435 2261883 := bstep (se 1 (by rfl) ⟨1696412, by rfl⟩ : syracuseStep 2261883 = 3392825) B3392825
theorem B5434661 : Blo 2261435 5434661 := bbase (se 4 (by rfl) ⟨509499, by rfl⟩ : syracuseStep 5434661 = 1018999) (by norm_num)
theorem B14492429 : Blo 2261435 14492429 := bstep (se 3 (by rfl) ⟨2717330, by rfl⟩ : syracuseStep 14492429 = 5434661) B5434661
theorem B9661619 : Blo 2261435 9661619 := bstep (se 1 (by rfl) ⟨7246214, by rfl⟩ : syracuseStep 9661619 = 14492429) B14492429
theorem B25764317 : Blo 2261435 25764317 := bstep (se 3 (by rfl) ⟨4830809, by rfl⟩ : syracuseStep 25764317 = 9661619) B9661619
theorem B17176211 : Blo 2261435 17176211 := bstep (se 1 (by rfl) ⟨12882158, by rfl⟩ : syracuseStep 17176211 = 25764317) B25764317
theorem B11450807 : Blo 2261435 11450807 := bstep (se 1 (by rfl) ⟨8588105, by rfl⟩ : syracuseStep 11450807 = 17176211) B17176211
theorem B7633871 : Blo 2261435 7633871 := bstep (se 1 (by rfl) ⟨5725403, by rfl⟩ : syracuseStep 7633871 = 11450807) B11450807
theorem B5089247 : Blo 2261435 5089247 := bstep (se 1 (by rfl) ⟨3816935, by rfl⟩ : syracuseStep 5089247 = 7633871) B7633871
theorem B3392831 : Blo 2261435 3392831 := bstep (se 1 (by rfl) ⟨2544623, by rfl⟩ : syracuseStep 3392831 = 5089247) B5089247
theorem B2261887 : Blo 2261435 2261887 := bstep (se 1 (by rfl) ⟨1696415, by rfl⟩ : syracuseStep 2261887 = 3392831) B3392831
theorem B3392837 : Blo 2261435 3392837 := bbase (se 4 (by rfl) ⟨318078, by rfl⟩ : syracuseStep 3392837 = 636157) (by norm_num)
theorem B2261891 : Blo 2261435 2261891 := bstep (se 1 (by rfl) ⟨1696418, by rfl⟩ : syracuseStep 2261891 = 3392837) B3392837
theorem B3816949 : Blo 2261435 3816949 := bbase (se 5 (by rfl) ⟨178919, by rfl⟩ : syracuseStep 3816949 = 357839) (by norm_num)
theorem B5089265 : Blo 2261435 5089265 := bstep (se 2 (by rfl) ⟨1908474, by rfl⟩ : syracuseStep 5089265 = 3816949) B3816949
theorem B3392843 : Blo 2261435 3392843 := bstep (se 1 (by rfl) ⟨2544632, by rfl⟩ : syracuseStep 3392843 = 5089265) B5089265
theorem B2261895 : Blo 2261435 2261895 := bstep (se 1 (by rfl) ⟨1696421, by rfl⟩ : syracuseStep 2261895 = 3392843) B3392843
theorem B2544637 : Blo 2261435 2544637 := bbase (se 3 (by rfl) ⟨477119, by rfl⟩ : syracuseStep 2544637 = 954239) (by norm_num)
theorem B3392849 : Blo 2261435 3392849 := bstep (se 2 (by rfl) ⟨1272318, by rfl⟩ : syracuseStep 3392849 = 2544637) B2544637
theorem B2261899 : Blo 2261435 2261899 := bstep (se 1 (by rfl) ⟨1696424, by rfl⟩ : syracuseStep 2261899 = 3392849) B3392849
theorem B7633925 : Blo 2261435 7633925 := bbase (se 4 (by rfl) ⟨715680, by rfl⟩ : syracuseStep 7633925 = 1431361) (by norm_num)
theorem B5089283 : Blo 2261435 5089283 := bstep (se 1 (by rfl) ⟨3816962, by rfl⟩ : syracuseStep 5089283 = 7633925) B7633925
theorem B3392855 : Blo 2261435 3392855 := bstep (se 1 (by rfl) ⟨2544641, by rfl⟩ : syracuseStep 3392855 = 5089283) B5089283
theorem B2261903 : Blo 2261435 2261903 := bstep (se 1 (by rfl) ⟨1696427, by rfl⟩ : syracuseStep 2261903 = 3392855) B3392855
theorem B3392861 : Blo 2261435 3392861 := bbase (se 3 (by rfl) ⟨636161, by rfl⟩ : syracuseStep 3392861 = 1272323) (by norm_num)
theorem B2261907 : Blo 2261435 2261907 := bstep (se 1 (by rfl) ⟨1696430, by rfl⟩ : syracuseStep 2261907 = 3392861) B3392861
theorem B5089301 : Blo 2261435 5089301 := bbase (se 6 (by rfl) ⟨119280, by rfl⟩ : syracuseStep 5089301 = 238561) (by norm_num)
theorem B3392867 : Blo 2261435 3392867 := bstep (se 1 (by rfl) ⟨2544650, by rfl⟩ : syracuseStep 3392867 = 5089301) B5089301
theorem B2261911 : Blo 2261435 2261911 := bstep (se 1 (by rfl) ⟨1696433, by rfl⟩ : syracuseStep 2261911 = 3392867) B3392867
theorem B8588213 : Blo 2261435 8588213 := bbase (se 5 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 8588213 = 805145) (by norm_num)
theorem B5725475 : Blo 2261435 5725475 := bstep (se 1 (by rfl) ⟨4294106, by rfl⟩ : syracuseStep 5725475 = 8588213) B8588213
theorem B3816983 : Blo 2261435 3816983 := bstep (se 1 (by rfl) ⟨2862737, by rfl⟩ : syracuseStep 3816983 = 5725475) B5725475
theorem B2544655 : Blo 2261435 2544655 := bstep (se 1 (by rfl) ⟨1908491, by rfl⟩ : syracuseStep 2544655 = 3816983) B3816983
theorem B3392873 : Blo 2261435 3392873 := bstep (se 2 (by rfl) ⟨1272327, by rfl⟩ : syracuseStep 3392873 = 2544655) B2544655
theorem B2261915 : Blo 2261435 2261915 := bstep (se 1 (by rfl) ⟨1696436, by rfl⟩ : syracuseStep 2261915 = 3392873) B3392873
theorem B2292781 : Blo 2261435 2292781 := bbase (se 3 (by rfl) ⟨429896, by rfl⟩ : syracuseStep 2292781 = 859793) (by norm_num)
theorem B3057041 : Blo 2261435 3057041 := bstep (se 2 (by rfl) ⟨1146390, by rfl⟩ : syracuseStep 3057041 = 2292781) B2292781
theorem B8152109 : Blo 2261435 8152109 := bstep (se 3 (by rfl) ⟨1528520, by rfl⟩ : syracuseStep 8152109 = 3057041) B3057041
theorem B5434739 : Blo 2261435 5434739 := bstep (se 1 (by rfl) ⟨4076054, by rfl⟩ : syracuseStep 5434739 = 8152109) B8152109
theorem B3623159 : Blo 2261435 3623159 := bstep (se 1 (by rfl) ⟨2717369, by rfl⟩ : syracuseStep 3623159 = 5434739) B5434739
theorem B2415439 : Blo 2261435 2415439 := bstep (se 1 (by rfl) ⟨1811579, by rfl⟩ : syracuseStep 2415439 = 3623159) B3623159
theorem B12882341 : Blo 2261435 12882341 := bstep (se 4 (by rfl) ⟨1207719, by rfl⟩ : syracuseStep 12882341 = 2415439) B2415439
theorem B8588227 : Blo 2261435 8588227 := bstep (se 1 (by rfl) ⟨6441170, by rfl⟩ : syracuseStep 8588227 = 12882341) B12882341
theorem B11450969 : Blo 2261435 11450969 := bstep (se 2 (by rfl) ⟨4294113, by rfl⟩ : syracuseStep 11450969 = 8588227) B8588227
theorem B7633979 : Blo 2261435 7633979 := bstep (se 1 (by rfl) ⟨5725484, by rfl⟩ : syracuseStep 7633979 = 11450969) B11450969
theorem B5089319 : Blo 2261435 5089319 := bstep (se 1 (by rfl) ⟨3816989, by rfl⟩ : syracuseStep 5089319 = 7633979) B7633979
theorem B3392879 : Blo 2261435 3392879 := bstep (se 1 (by rfl) ⟨2544659, by rfl⟩ : syracuseStep 3392879 = 5089319) B5089319
theorem B2261919 : Blo 2261435 2261919 := bstep (se 1 (by rfl) ⟨1696439, by rfl⟩ : syracuseStep 2261919 = 3392879) B3392879
theorem B3392885 : Blo 2261435 3392885 := bbase (se 5 (by rfl) ⟨159041, by rfl⟩ : syracuseStep 3392885 = 318083) (by norm_num)
theorem B2261923 : Blo 2261435 2261923 := bstep (se 1 (by rfl) ⟨1696442, by rfl⟩ : syracuseStep 2261923 = 3392885) B3392885
theorem B3220597 : Blo 2261435 3220597 := bbase (se 5 (by rfl) ⟨150965, by rfl⟩ : syracuseStep 3220597 = 301931) (by norm_num)
theorem B4294129 : Blo 2261435 4294129 := bstep (se 2 (by rfl) ⟨1610298, by rfl⟩ : syracuseStep 4294129 = 3220597) B3220597
theorem B5725505 : Blo 2261435 5725505 := bstep (se 2 (by rfl) ⟨2147064, by rfl⟩ : syracuseStep 5725505 = 4294129) B4294129
theorem B3817003 : Blo 2261435 3817003 := bstep (se 1 (by rfl) ⟨2862752, by rfl⟩ : syracuseStep 3817003 = 5725505) B5725505
theorem B5089337 : Blo 2261435 5089337 := bstep (se 2 (by rfl) ⟨1908501, by rfl⟩ : syracuseStep 5089337 = 3817003) B3817003
theorem B3392891 : Blo 2261435 3392891 := bstep (se 1 (by rfl) ⟨2544668, by rfl⟩ : syracuseStep 3392891 = 5089337) B5089337
theorem B2261927 : Blo 2261435 2261927 := bstep (se 1 (by rfl) ⟨1696445, by rfl⟩ : syracuseStep 2261927 = 3392891) B3392891
theorem B2544673 : Blo 2261435 2544673 := bbase (se 2 (by rfl) ⟨954252, by rfl⟩ : syracuseStep 2544673 = 1908505) (by norm_num)
theorem B3392897 : Blo 2261435 3392897 := bstep (se 2 (by rfl) ⟨1272336, by rfl⟩ : syracuseStep 3392897 = 2544673) B2544673
theorem B2261931 : Blo 2261435 2261931 := bstep (se 1 (by rfl) ⟨1696448, by rfl⟩ : syracuseStep 2261931 = 3392897) B3392897
theorem B5725525 : Blo 2261435 5725525 := bbase (se 11 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 5725525 = 8387) (by norm_num)
theorem B7634033 : Blo 2261435 7634033 := bstep (se 2 (by rfl) ⟨2862762, by rfl⟩ : syracuseStep 7634033 = 5725525) B5725525
theorem B5089355 : Blo 2261435 5089355 := bstep (se 1 (by rfl) ⟨3817016, by rfl⟩ : syracuseStep 5089355 = 7634033) B7634033
theorem B3392903 : Blo 2261435 3392903 := bstep (se 1 (by rfl) ⟨2544677, by rfl⟩ : syracuseStep 3392903 = 5089355) B5089355
theorem B2261935 : Blo 2261435 2261935 := bstep (se 1 (by rfl) ⟨1696451, by rfl⟩ : syracuseStep 2261935 = 3392903) B3392903
theorem B3392909 : Blo 2261435 3392909 := bbase (se 3 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 3392909 = 1272341) (by norm_num)
theorem B2261939 : Blo 2261435 2261939 := bstep (se 1 (by rfl) ⟨1696454, by rfl⟩ : syracuseStep 2261939 = 3392909) B3392909
theorem B5089373 : Blo 2261435 5089373 := bbase (se 3 (by rfl) ⟨954257, by rfl⟩ : syracuseStep 5089373 = 1908515) (by norm_num)
theorem B3392915 : Blo 2261435 3392915 := bstep (se 1 (by rfl) ⟨2544686, by rfl⟩ : syracuseStep 3392915 = 5089373) B5089373
theorem B2261943 : Blo 2261435 2261943 := bstep (se 1 (by rfl) ⟨1696457, by rfl⟩ : syracuseStep 2261943 = 3392915) B3392915
theorem B3817037 : Blo 2261435 3817037 := bbase (se 3 (by rfl) ⟨715694, by rfl⟩ : syracuseStep 3817037 = 1431389) (by norm_num)
theorem B2544691 : Blo 2261435 2544691 := bstep (se 1 (by rfl) ⟨1908518, by rfl⟩ : syracuseStep 2544691 = 3817037) B3817037
theorem B3392921 : Blo 2261435 3392921 := bstep (se 2 (by rfl) ⟨1272345, by rfl⟩ : syracuseStep 3392921 = 2544691) B2544691
theorem B2261947 : Blo 2261435 2261947 := bstep (se 1 (by rfl) ⟨1696460, by rfl⟩ : syracuseStep 2261947 = 3392921) B3392921
theorem B2901841 : Blo 2261435 2901841 := bbase (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) (by norm_num)
theorem B61905941 : Blo 2261435 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B41270627 : Blo 2261435 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B27513751 : Blo 2261435 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B36685001 : Blo 2261435 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B24456667 : Blo 2261435 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B32608889 : Blo 2261435 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B21739259 : Blo 2261435 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B14492839 : Blo 2261435 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B19323785 : Blo 2261435 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B12882523 : Blo 2261435 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B17176697 : Blo 2261435 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B11451131 : Blo 2261435 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B7634087 : Blo 2261435 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B5089391 : Blo 2261435 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B3392927 : Blo 2261435 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B2261951 : Blo 2261435 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B3392933 : Blo 2261435 3392933 := bbase (se 4 (by rfl) ⟨318087, by rfl⟩ : syracuseStep 3392933 = 636175) (by norm_num)
theorem B2261955 : Blo 2261435 2261955 := bstep (se 1 (by rfl) ⟨1696466, by rfl⟩ : syracuseStep 2261955 = 3392933) B3392933
theorem B2862793 : Blo 2261435 2862793 := bbase (se 2 (by rfl) ⟨1073547, by rfl⟩ : syracuseStep 2862793 = 2147095) (by norm_num)
theorem B3817057 : Blo 2261435 3817057 := bstep (se 2 (by rfl) ⟨1431396, by rfl⟩ : syracuseStep 3817057 = 2862793) B2862793
theorem B5089409 : Blo 2261435 5089409 := bstep (se 2 (by rfl) ⟨1908528, by rfl⟩ : syracuseStep 5089409 = 3817057) B3817057
theorem B3392939 : Blo 2261435 3392939 := bstep (se 1 (by rfl) ⟨2544704, by rfl⟩ : syracuseStep 3392939 = 5089409) B5089409
theorem B2261959 : Blo 2261435 2261959 := bstep (se 1 (by rfl) ⟨1696469, by rfl⟩ : syracuseStep 2261959 = 3392939) B3392939
theorem B2544709 : Blo 2261435 2544709 := bbase (se 4 (by rfl) ⟨238566, by rfl⟩ : syracuseStep 2544709 = 477133) (by norm_num)
theorem B3392945 : Blo 2261435 3392945 := bstep (se 2 (by rfl) ⟨1272354, by rfl⟩ : syracuseStep 3392945 = 2544709) B2544709
theorem B2261963 : Blo 2261435 2261963 := bstep (se 1 (by rfl) ⟨1696472, by rfl⟩ : syracuseStep 2261963 = 3392945) B3392945
theorem B4294205 : Blo 2261435 4294205 := bbase (se 3 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 4294205 = 1610327) (by norm_num)
theorem B2862803 : Blo 2261435 2862803 := bstep (se 1 (by rfl) ⟨2147102, by rfl⟩ : syracuseStep 2862803 = 4294205) B4294205
theorem B7634141 : Blo 2261435 7634141 := bstep (se 3 (by rfl) ⟨1431401, by rfl⟩ : syracuseStep 7634141 = 2862803) B2862803
theorem B5089427 : Blo 2261435 5089427 := bstep (se 1 (by rfl) ⟨3817070, by rfl⟩ : syracuseStep 5089427 = 7634141) B7634141
theorem B3392951 : Blo 2261435 3392951 := bstep (se 1 (by rfl) ⟨2544713, by rfl⟩ : syracuseStep 3392951 = 5089427) B5089427
theorem B2261967 : Blo 2261435 2261967 := bstep (se 1 (by rfl) ⟨1696475, by rfl⟩ : syracuseStep 2261967 = 3392951) B3392951
theorem B3392957 : Blo 2261435 3392957 := bbase (se 3 (by rfl) ⟨636179, by rfl⟩ : syracuseStep 3392957 = 1272359) (by norm_num)
theorem B2261971 : Blo 2261435 2261971 := bstep (se 1 (by rfl) ⟨1696478, by rfl⟩ : syracuseStep 2261971 = 3392957) B3392957
theorem B5089445 : Blo 2261435 5089445 := bbase (se 4 (by rfl) ⟨477135, by rfl⟩ : syracuseStep 5089445 = 954271) (by norm_num)
theorem B3392963 : Blo 2261435 3392963 := bstep (se 1 (by rfl) ⟨2544722, by rfl⟩ : syracuseStep 3392963 = 5089445) B5089445
theorem B2261975 : Blo 2261435 2261975 := bstep (se 1 (by rfl) ⟨1696481, by rfl⟩ : syracuseStep 2261975 = 3392963) B3392963
theorem B5725637 : Blo 2261435 5725637 := bbase (se 4 (by rfl) ⟨536778, by rfl⟩ : syracuseStep 5725637 = 1073557) (by norm_num)
theorem B3817091 : Blo 2261435 3817091 := bstep (se 1 (by rfl) ⟨2862818, by rfl⟩ : syracuseStep 3817091 = 5725637) B5725637
theorem B2544727 : Blo 2261435 2544727 := bstep (se 1 (by rfl) ⟨1908545, by rfl⟩ : syracuseStep 2544727 = 3817091) B3817091
theorem B3392969 : Blo 2261435 3392969 := bstep (se 2 (by rfl) ⟨1272363, by rfl⟩ : syracuseStep 3392969 = 2544727) B2544727
theorem B2261979 : Blo 2261435 2261979 := bstep (se 1 (by rfl) ⟨1696484, by rfl⟩ : syracuseStep 2261979 = 3392969) B3392969
theorem B6972389 : Blo 2261435 6972389 := bbase (se 4 (by rfl) ⟨653661, by rfl⟩ : syracuseStep 6972389 = 1307323) (by norm_num)
theorem B4648259 : Blo 2261435 4648259 := bstep (se 1 (by rfl) ⟨3486194, by rfl⟩ : syracuseStep 4648259 = 6972389) B6972389
theorem B3098839 : Blo 2261435 3098839 := bstep (se 1 (by rfl) ⟨2324129, by rfl⟩ : syracuseStep 3098839 = 4648259) B4648259
theorem B4131785 : Blo 2261435 4131785 := bstep (se 2 (by rfl) ⟨1549419, by rfl⟩ : syracuseStep 4131785 = 3098839) B3098839
theorem B2754523 : Blo 2261435 2754523 := bstep (se 1 (by rfl) ⟨2065892, by rfl⟩ : syracuseStep 2754523 = 4131785) B4131785
theorem B3672697 : Blo 2261435 3672697 := bstep (se 2 (by rfl) ⟨1377261, by rfl⟩ : syracuseStep 3672697 = 2754523) B2754523
theorem B4896929 : Blo 2261435 4896929 := bstep (se 2 (by rfl) ⟨1836348, by rfl⟩ : syracuseStep 4896929 = 3672697) B3672697
theorem B3264619 : Blo 2261435 3264619 := bstep (se 1 (by rfl) ⟨2448464, by rfl⟩ : syracuseStep 3264619 = 4896929) B4896929
theorem B4352825 : Blo 2261435 4352825 := bstep (se 2 (by rfl) ⟨1632309, by rfl⟩ : syracuseStep 4352825 = 3264619) B3264619
theorem B11607533 : Blo 2261435 11607533 := bstep (se 3 (by rfl) ⟨2176412, by rfl⟩ : syracuseStep 11607533 = 4352825) B4352825
theorem B7738355 : Blo 2261435 7738355 := bstep (se 1 (by rfl) ⟨5803766, by rfl⟩ : syracuseStep 7738355 = 11607533) B11607533
theorem B5158903 : Blo 2261435 5158903 := bstep (se 1 (by rfl) ⟨3869177, by rfl⟩ : syracuseStep 5158903 = 7738355) B7738355
theorem B6878537 : Blo 2261435 6878537 := bstep (se 2 (by rfl) ⟨2579451, by rfl⟩ : syracuseStep 6878537 = 5158903) B5158903
theorem B4585691 : Blo 2261435 4585691 := bstep (se 1 (by rfl) ⟨3439268, by rfl⟩ : syracuseStep 4585691 = 6878537) B6878537
theorem B12228509 : Blo 2261435 12228509 := bstep (se 3 (by rfl) ⟨2292845, by rfl⟩ : syracuseStep 12228509 = 4585691) B4585691
theorem B8152339 : Blo 2261435 8152339 := bstep (se 1 (by rfl) ⟨6114254, by rfl⟩ : syracuseStep 8152339 = 12228509) B12228509
theorem B10869785 : Blo 2261435 10869785 := bstep (se 2 (by rfl) ⟨4076169, by rfl⟩ : syracuseStep 10869785 = 8152339) B8152339
theorem B7246523 : Blo 2261435 7246523 := bstep (se 1 (by rfl) ⟨5434892, by rfl⟩ : syracuseStep 7246523 = 10869785) B10869785
theorem B4831015 : Blo 2261435 4831015 := bstep (se 1 (by rfl) ⟨3623261, by rfl⟩ : syracuseStep 4831015 = 7246523) B7246523
theorem B6441353 : Blo 2261435 6441353 := bstep (se 2 (by rfl) ⟨2415507, by rfl⟩ : syracuseStep 6441353 = 4831015) B4831015
theorem B4294235 : Blo 2261435 4294235 := bstep (se 1 (by rfl) ⟨3220676, by rfl⟩ : syracuseStep 4294235 = 6441353) B6441353
theorem B11451293 : Blo 2261435 11451293 := bstep (se 3 (by rfl) ⟨2147117, by rfl⟩ : syracuseStep 11451293 = 4294235) B4294235
theorem B7634195 : Blo 2261435 7634195 := bstep (se 1 (by rfl) ⟨5725646, by rfl⟩ : syracuseStep 7634195 = 11451293) B11451293
theorem B5089463 : Blo 2261435 5089463 := bstep (se 1 (by rfl) ⟨3817097, by rfl⟩ : syracuseStep 5089463 = 7634195) B7634195
theorem B3392975 : Blo 2261435 3392975 := bstep (se 1 (by rfl) ⟨2544731, by rfl⟩ : syracuseStep 3392975 = 5089463) B5089463
theorem B2261983 : Blo 2261435 2261983 := bstep (se 1 (by rfl) ⟨1696487, by rfl⟩ : syracuseStep 2261983 = 3392975) B3392975
theorem B3392981 : Blo 2261435 3392981 := bbase (se 7 (by rfl) ⟨39761, by rfl⟩ : syracuseStep 3392981 = 79523) (by norm_num)
theorem B2261987 : Blo 2261435 2261987 := bstep (se 1 (by rfl) ⟨1696490, by rfl⟩ : syracuseStep 2261987 = 3392981) B3392981
theorem B8588501 : Blo 2261435 8588501 := bbase (se 7 (by rfl) ⟨100646, by rfl⟩ : syracuseStep 8588501 = 201293) (by norm_num)
theorem B5725667 : Blo 2261435 5725667 := bstep (se 1 (by rfl) ⟨4294250, by rfl⟩ : syracuseStep 5725667 = 8588501) B8588501
theorem B3817111 : Blo 2261435 3817111 := bstep (se 1 (by rfl) ⟨2862833, by rfl⟩ : syracuseStep 3817111 = 5725667) B5725667
theorem B5089481 : Blo 2261435 5089481 := bstep (se 2 (by rfl) ⟨1908555, by rfl⟩ : syracuseStep 5089481 = 3817111) B3817111
theorem B3392987 : Blo 2261435 3392987 := bstep (se 1 (by rfl) ⟨2544740, by rfl⟩ : syracuseStep 3392987 = 5089481) B5089481
theorem B2261991 : Blo 2261435 2261991 := bstep (se 1 (by rfl) ⟨1696493, by rfl⟩ : syracuseStep 2261991 = 3392987) B3392987
theorem B2544745 : Blo 2261435 2544745 := bbase (se 2 (by rfl) ⟨954279, by rfl⟩ : syracuseStep 2544745 = 1908559) (by norm_num)
theorem B3392993 : Blo 2261435 3392993 := bstep (se 2 (by rfl) ⟨1272372, by rfl⟩ : syracuseStep 3392993 = 2544745) B2544745
theorem B2261995 : Blo 2261435 2261995 := bstep (se 1 (by rfl) ⟨1696496, by rfl⟩ : syracuseStep 2261995 = 3392993) B3392993
theorem B3057149 : Blo 2261435 3057149 := bbase (se 3 (by rfl) ⟨573215, by rfl⟩ : syracuseStep 3057149 = 1146431) (by norm_num)
theorem B8152397 : Blo 2261435 8152397 := bstep (se 3 (by rfl) ⟨1528574, by rfl⟩ : syracuseStep 8152397 = 3057149) B3057149
theorem B5434931 : Blo 2261435 5434931 := bstep (se 1 (by rfl) ⟨4076198, by rfl⟩ : syracuseStep 5434931 = 8152397) B8152397
theorem B3623287 : Blo 2261435 3623287 := bstep (se 1 (by rfl) ⟨2717465, by rfl⟩ : syracuseStep 3623287 = 5434931) B5434931
theorem B4831049 : Blo 2261435 4831049 := bstep (se 2 (by rfl) ⟨1811643, by rfl⟩ : syracuseStep 4831049 = 3623287) B3623287
theorem B12882797 : Blo 2261435 12882797 := bstep (se 3 (by rfl) ⟨2415524, by rfl⟩ : syracuseStep 12882797 = 4831049) B4831049
theorem B8588531 : Blo 2261435 8588531 := bstep (se 1 (by rfl) ⟨6441398, by rfl⟩ : syracuseStep 8588531 = 12882797) B12882797
theorem B5725687 : Blo 2261435 5725687 := bstep (se 1 (by rfl) ⟨4294265, by rfl⟩ : syracuseStep 5725687 = 8588531) B8588531
theorem B7634249 : Blo 2261435 7634249 := bstep (se 2 (by rfl) ⟨2862843, by rfl⟩ : syracuseStep 7634249 = 5725687) B5725687
theorem B5089499 : Blo 2261435 5089499 := bstep (se 1 (by rfl) ⟨3817124, by rfl⟩ : syracuseStep 5089499 = 7634249) B7634249
theorem B3392999 : Blo 2261435 3392999 := bstep (se 1 (by rfl) ⟨2544749, by rfl⟩ : syracuseStep 3392999 = 5089499) B5089499
theorem B2261999 : Blo 2261435 2261999 := bstep (se 1 (by rfl) ⟨1696499, by rfl⟩ : syracuseStep 2261999 = 3392999) B3392999
theorem B3393005 : Blo 2261435 3393005 := bbase (se 3 (by rfl) ⟨636188, by rfl⟩ : syracuseStep 3393005 = 1272377) (by norm_num)
theorem B2262003 : Blo 2261435 2262003 := bstep (se 1 (by rfl) ⟨1696502, by rfl⟩ : syracuseStep 2262003 = 3393005) B3393005
theorem B5089517 : Blo 2261435 5089517 := bbase (se 3 (by rfl) ⟨954284, by rfl⟩ : syracuseStep 5089517 = 1908569) (by norm_num)
theorem B3393011 : Blo 2261435 3393011 := bstep (se 1 (by rfl) ⟨2544758, by rfl⟩ : syracuseStep 3393011 = 5089517) B5089517
theorem B2262007 : Blo 2261435 2262007 := bstep (se 1 (by rfl) ⟨1696505, by rfl⟩ : syracuseStep 2262007 = 3393011) B3393011
theorem B3220717 : Blo 2261435 3220717 := bbase (se 3 (by rfl) ⟨603884, by rfl⟩ : syracuseStep 3220717 = 1207769) (by norm_num)
theorem B4294289 : Blo 2261435 4294289 := bstep (se 2 (by rfl) ⟨1610358, by rfl⟩ : syracuseStep 4294289 = 3220717) B3220717
theorem B2862859 : Blo 2261435 2862859 := bstep (se 1 (by rfl) ⟨2147144, by rfl⟩ : syracuseStep 2862859 = 4294289) B4294289
theorem B3817145 : Blo 2261435 3817145 := bstep (se 2 (by rfl) ⟨1431429, by rfl⟩ : syracuseStep 3817145 = 2862859) B2862859
theorem B2544763 : Blo 2261435 2544763 := bstep (se 1 (by rfl) ⟨1908572, by rfl⟩ : syracuseStep 2544763 = 3817145) B3817145
theorem B3393017 : Blo 2261435 3393017 := bstep (se 2 (by rfl) ⟨1272381, by rfl⟩ : syracuseStep 3393017 = 2544763) B2544763
theorem B2262011 : Blo 2261435 2262011 := bstep (se 1 (by rfl) ⟨1696508, by rfl⟩ : syracuseStep 2262011 = 3393017) B3393017
theorem B3922021 : Blo 2261435 3922021 := bbase (se 4 (by rfl) ⟨367689, by rfl⟩ : syracuseStep 3922021 = 735379) (by norm_num)
theorem B5229361 : Blo 2261435 5229361 := bstep (se 2 (by rfl) ⟨1961010, by rfl⟩ : syracuseStep 5229361 = 3922021) B3922021
theorem B6972481 : Blo 2261435 6972481 := bstep (se 2 (by rfl) ⟨2614680, by rfl⟩ : syracuseStep 6972481 = 5229361) B5229361
theorem B9296641 : Blo 2261435 9296641 := bstep (se 2 (by rfl) ⟨3486240, by rfl⟩ : syracuseStep 9296641 = 6972481) B6972481
theorem B12395521 : Blo 2261435 12395521 := bstep (se 2 (by rfl) ⟨4648320, by rfl⟩ : syracuseStep 12395521 = 9296641) B9296641
theorem B16527361 : Blo 2261435 16527361 := bstep (se 2 (by rfl) ⟨6197760, by rfl⟩ : syracuseStep 16527361 = 12395521) B12395521
theorem B22036481 : Blo 2261435 22036481 := bstep (se 2 (by rfl) ⟨8263680, by rfl⟩ : syracuseStep 22036481 = 16527361) B16527361
theorem B14690987 : Blo 2261435 14690987 := bstep (se 1 (by rfl) ⟨11018240, by rfl⟩ : syracuseStep 14690987 = 22036481) B22036481
theorem B9793991 : Blo 2261435 9793991 := bstep (se 1 (by rfl) ⟨7345493, by rfl⟩ : syracuseStep 9793991 = 14690987) B14690987
theorem B26117309 : Blo 2261435 26117309 := bstep (se 3 (by rfl) ⟨4896995, by rfl⟩ : syracuseStep 26117309 = 9793991) B9793991
theorem B17411539 : Blo 2261435 17411539 := bstep (se 1 (by rfl) ⟨13058654, by rfl⟩ : syracuseStep 17411539 = 26117309) B26117309
theorem B23215385 : Blo 2261435 23215385 := bstep (se 2 (by rfl) ⟨8705769, by rfl⟩ : syracuseStep 23215385 = 17411539) B17411539
theorem B15476923 : Blo 2261435 15476923 := bstep (se 1 (by rfl) ⟨11607692, by rfl⟩ : syracuseStep 15476923 = 23215385) B23215385
theorem B20635897 : Blo 2261435 20635897 := bstep (se 2 (by rfl) ⟨7738461, by rfl⟩ : syracuseStep 20635897 = 15476923) B15476923
theorem B27514529 : Blo 2261435 27514529 := bstep (se 2 (by rfl) ⟨10317948, by rfl⟩ : syracuseStep 27514529 = 20635897) B20635897
theorem B18343019 : Blo 2261435 18343019 := bstep (se 1 (by rfl) ⟨13757264, by rfl⟩ : syracuseStep 18343019 = 27514529) B27514529
theorem B12228679 : Blo 2261435 12228679 := bstep (se 1 (by rfl) ⟨9171509, by rfl⟩ : syracuseStep 12228679 = 18343019) B18343019
theorem B16304905 : Blo 2261435 16304905 := bstep (se 2 (by rfl) ⟨6114339, by rfl⟩ : syracuseStep 16304905 = 12228679) B12228679
theorem B86959493 : Blo 2261435 86959493 := bstep (se 4 (by rfl) ⟨8152452, by rfl⟩ : syracuseStep 86959493 = 16304905) B16304905
theorem B57972995 : Blo 2261435 57972995 := bstep (se 1 (by rfl) ⟨43479746, by rfl⟩ : syracuseStep 57972995 = 86959493) B86959493
theorem B38648663 : Blo 2261435 38648663 := bstep (se 1 (by rfl) ⟨28986497, by rfl⟩ : syracuseStep 38648663 = 57972995) B57972995
theorem B25765775 : Blo 2261435 25765775 := bstep (se 1 (by rfl) ⟨19324331, by rfl⟩ : syracuseStep 25765775 = 38648663) B38648663
theorem B17177183 : Blo 2261435 17177183 := bstep (se 1 (by rfl) ⟨12882887, by rfl⟩ : syracuseStep 17177183 = 25765775) B25765775
theorem B11451455 : Blo 2261435 11451455 := bstep (se 1 (by rfl) ⟨8588591, by rfl⟩ : syracuseStep 11451455 = 17177183) B17177183
theorem B7634303 : Blo 2261435 7634303 := bstep (se 1 (by rfl) ⟨5725727, by rfl⟩ : syracuseStep 7634303 = 11451455) B11451455
theorem B5089535 : Blo 2261435 5089535 := bstep (se 1 (by rfl) ⟨3817151, by rfl⟩ : syracuseStep 5089535 = 7634303) B7634303
theorem B3393023 : Blo 2261435 3393023 := bstep (se 1 (by rfl) ⟨2544767, by rfl⟩ : syracuseStep 3393023 = 5089535) B5089535
theorem B2262015 : Blo 2261435 2262015 := bstep (se 1 (by rfl) ⟨1696511, by rfl⟩ : syracuseStep 2262015 = 3393023) B3393023
theorem B3393029 : Blo 2261435 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B2262019 : Blo 2261435 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B3817165 : Blo 2261435 3817165 := bbase (se 3 (by rfl) ⟨715718, by rfl⟩ : syracuseStep 3817165 = 1431437) (by norm_num)
theorem B5089553 : Blo 2261435 5089553 := bstep (se 2 (by rfl) ⟨1908582, by rfl⟩ : syracuseStep 5089553 = 3817165) B3817165
theorem B3393035 : Blo 2261435 3393035 := bstep (se 1 (by rfl) ⟨2544776, by rfl⟩ : syracuseStep 3393035 = 5089553) B5089553
theorem B2262023 : Blo 2261435 2262023 := bstep (se 1 (by rfl) ⟨1696517, by rfl⟩ : syracuseStep 2262023 = 3393035) B3393035
theorem B2544781 : Blo 2261435 2544781 := bbase (se 3 (by rfl) ⟨477146, by rfl⟩ : syracuseStep 2544781 = 954293) (by norm_num)
theorem B3393041 : Blo 2261435 3393041 := bstep (se 2 (by rfl) ⟨1272390, by rfl⟩ : syracuseStep 3393041 = 2544781) B2544781
theorem B2262027 : Blo 2261435 2262027 := bstep (se 1 (by rfl) ⟨1696520, by rfl⟩ : syracuseStep 2262027 = 3393041) B3393041
theorem B7634357 : Blo 2261435 7634357 := bbase (se 5 (by rfl) ⟨357860, by rfl⟩ : syracuseStep 7634357 = 715721) (by norm_num)
theorem B5089571 : Blo 2261435 5089571 := bstep (se 1 (by rfl) ⟨3817178, by rfl⟩ : syracuseStep 5089571 = 7634357) B7634357
theorem B3393047 : Blo 2261435 3393047 := bstep (se 1 (by rfl) ⟨2544785, by rfl⟩ : syracuseStep 3393047 = 5089571) B5089571
theorem B2262031 : Blo 2261435 2262031 := bstep (se 1 (by rfl) ⟨1696523, by rfl⟩ : syracuseStep 2262031 = 3393047) B3393047
theorem B3393053 : Blo 2261435 3393053 := bbase (se 3 (by rfl) ⟨636197, by rfl⟩ : syracuseStep 3393053 = 1272395) (by norm_num)
theorem B2262035 : Blo 2261435 2262035 := bstep (se 1 (by rfl) ⟨1696526, by rfl⟩ : syracuseStep 2262035 = 3393053) B3393053
theorem B5089589 : Blo 2261435 5089589 := bbase (se 5 (by rfl) ⟨238574, by rfl⟩ : syracuseStep 5089589 = 477149) (by norm_num)
theorem B3393059 : Blo 2261435 3393059 := bstep (se 1 (by rfl) ⟨2544794, by rfl⟩ : syracuseStep 3393059 = 5089589) B5089589
theorem B2262039 : Blo 2261435 2262039 := bstep (se 1 (by rfl) ⟨1696529, by rfl⟩ : syracuseStep 2262039 = 3393059) B3393059
theorem B2941553 : Blo 2261435 2941553 := bbase (se 2 (by rfl) ⟨1103082, by rfl⟩ : syracuseStep 2941553 = 2206165) (by norm_num)
theorem B7844141 : Blo 2261435 7844141 := bstep (se 3 (by rfl) ⟨1470776, by rfl⟩ : syracuseStep 7844141 = 2941553) B2941553
theorem B5229427 : Blo 2261435 5229427 := bstep (se 1 (by rfl) ⟨3922070, by rfl⟩ : syracuseStep 5229427 = 7844141) B7844141
theorem B6972569 : Blo 2261435 6972569 := bstep (se 2 (by rfl) ⟨2614713, by rfl⟩ : syracuseStep 6972569 = 5229427) B5229427
theorem B4648379 : Blo 2261435 4648379 := bstep (se 1 (by rfl) ⟨3486284, by rfl⟩ : syracuseStep 4648379 = 6972569) B6972569
theorem B12395677 : Blo 2261435 12395677 := bstep (se 3 (by rfl) ⟨2324189, by rfl⟩ : syracuseStep 12395677 = 4648379) B4648379
theorem B16527569 : Blo 2261435 16527569 := bstep (se 2 (by rfl) ⟨6197838, by rfl⟩ : syracuseStep 16527569 = 12395677) B12395677
theorem B176294069 : Blo 2261435 176294069 := bstep (se 5 (by rfl) ⟨8263784, by rfl⟩ : syracuseStep 176294069 = 16527569) B16527569
theorem B117529379 : Blo 2261435 117529379 := bstep (se 1 (by rfl) ⟨88147034, by rfl⟩ : syracuseStep 117529379 = 176294069) B176294069
theorem B78352919 : Blo 2261435 78352919 := bstep (se 1 (by rfl) ⟨58764689, by rfl⟩ : syracuseStep 78352919 = 117529379) B117529379
theorem B52235279 : Blo 2261435 52235279 := bstep (se 1 (by rfl) ⟨39176459, by rfl⟩ : syracuseStep 52235279 = 78352919) B78352919
theorem B34823519 : Blo 2261435 34823519 := bstep (se 1 (by rfl) ⟨26117639, by rfl⟩ : syracuseStep 34823519 = 52235279) B52235279
theorem B23215679 : Blo 2261435 23215679 := bstep (se 1 (by rfl) ⟨17411759, by rfl⟩ : syracuseStep 23215679 = 34823519) B34823519
theorem B15477119 : Blo 2261435 15477119 := bstep (se 1 (by rfl) ⟨11607839, by rfl⟩ : syracuseStep 15477119 = 23215679) B23215679
theorem B10318079 : Blo 2261435 10318079 := bstep (se 1 (by rfl) ⟨7738559, by rfl⟩ : syracuseStep 10318079 = 15477119) B15477119
theorem B6878719 : Blo 2261435 6878719 := bstep (se 1 (by rfl) ⟨5159039, by rfl⟩ : syracuseStep 6878719 = 10318079) B10318079
theorem B9171625 : Blo 2261435 9171625 := bstep (se 2 (by rfl) ⟨3439359, by rfl⟩ : syracuseStep 9171625 = 6878719) B6878719
theorem B12228833 : Blo 2261435 12228833 := bstep (se 2 (by rfl) ⟨4585812, by rfl⟩ : syracuseStep 12228833 = 9171625) B9171625
theorem B32610221 : Blo 2261435 32610221 := bstep (se 3 (by rfl) ⟨6114416, by rfl⟩ : syracuseStep 32610221 = 12228833) B12228833
theorem B21740147 : Blo 2261435 21740147 := bstep (se 1 (by rfl) ⟨16305110, by rfl⟩ : syracuseStep 21740147 = 32610221) B32610221
theorem B14493431 : Blo 2261435 14493431 := bstep (se 1 (by rfl) ⟨10870073, by rfl⟩ : syracuseStep 14493431 = 21740147) B21740147
theorem B9662287 : Blo 2261435 9662287 := bstep (se 1 (by rfl) ⟨7246715, by rfl⟩ : syracuseStep 9662287 = 14493431) B14493431
theorem B12883049 : Blo 2261435 12883049 := bstep (se 2 (by rfl) ⟨4831143, by rfl⟩ : syracuseStep 12883049 = 9662287) B9662287
theorem B8588699 : Blo 2261435 8588699 := bstep (se 1 (by rfl) ⟨6441524, by rfl⟩ : syracuseStep 8588699 = 12883049) B12883049
theorem B5725799 : Blo 2261435 5725799 := bstep (se 1 (by rfl) ⟨4294349, by rfl⟩ : syracuseStep 5725799 = 8588699) B8588699
theorem B3817199 : Blo 2261435 3817199 := bstep (se 1 (by rfl) ⟨2862899, by rfl⟩ : syracuseStep 3817199 = 5725799) B5725799
theorem B2544799 : Blo 2261435 2544799 := bstep (se 1 (by rfl) ⟨1908599, by rfl⟩ : syracuseStep 2544799 = 3817199) B3817199
theorem B3393065 : Blo 2261435 3393065 := bstep (se 2 (by rfl) ⟨1272399, by rfl⟩ : syracuseStep 3393065 = 2544799) B2544799
theorem B2262043 : Blo 2261435 2262043 := bstep (se 1 (by rfl) ⟨1696532, by rfl⟩ : syracuseStep 2262043 = 3393065) B3393065
theorem B48915413 : Blo 2261435 48915413 := bbase (se 7 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 48915413 = 1146455) (by norm_num)
theorem B32610275 : Blo 2261435 32610275 := bstep (se 1 (by rfl) ⟨24457706, by rfl⟩ : syracuseStep 32610275 = 48915413) B48915413
theorem B21740183 : Blo 2261435 21740183 := bstep (se 1 (by rfl) ⟨16305137, by rfl⟩ : syracuseStep 21740183 = 32610275) B32610275
theorem B14493455 : Blo 2261435 14493455 := bstep (se 1 (by rfl) ⟨10870091, by rfl⟩ : syracuseStep 14493455 = 21740183) B21740183
theorem B9662303 : Blo 2261435 9662303 := bstep (se 1 (by rfl) ⟨7246727, by rfl⟩ : syracuseStep 9662303 = 14493455) B14493455
theorem B6441535 : Blo 2261435 6441535 := bstep (se 1 (by rfl) ⟨4831151, by rfl⟩ : syracuseStep 6441535 = 9662303) B9662303
theorem B8588713 : Blo 2261435 8588713 := bstep (se 2 (by rfl) ⟨3220767, by rfl⟩ : syracuseStep 8588713 = 6441535) B6441535
theorem B11451617 : Blo 2261435 11451617 := bstep (se 2 (by rfl) ⟨4294356, by rfl⟩ : syracuseStep 11451617 = 8588713) B8588713
theorem B7634411 : Blo 2261435 7634411 := bstep (se 1 (by rfl) ⟨5725808, by rfl⟩ : syracuseStep 7634411 = 11451617) B11451617
theorem B5089607 : Blo 2261435 5089607 := bstep (se 1 (by rfl) ⟨3817205, by rfl⟩ : syracuseStep 5089607 = 7634411) B7634411
theorem B3393071 : Blo 2261435 3393071 := bstep (se 1 (by rfl) ⟨2544803, by rfl⟩ : syracuseStep 3393071 = 5089607) B5089607
theorem B2262047 : Blo 2261435 2262047 := bstep (se 1 (by rfl) ⟨1696535, by rfl⟩ : syracuseStep 2262047 = 3393071) B3393071
theorem B3393077 : Blo 2261435 3393077 := bbase (se 5 (by rfl) ⟨159050, by rfl⟩ : syracuseStep 3393077 = 318101) (by norm_num)
theorem B2262051 : Blo 2261435 2262051 := bstep (se 1 (by rfl) ⟨1696538, by rfl⟩ : syracuseStep 2262051 = 3393077) B3393077
theorem B5725829 : Blo 2261435 5725829 := bbase (se 4 (by rfl) ⟨536796, by rfl⟩ : syracuseStep 5725829 = 1073593) (by norm_num)
theorem B3817219 : Blo 2261435 3817219 := bstep (se 1 (by rfl) ⟨2862914, by rfl⟩ : syracuseStep 3817219 = 5725829) B5725829
theorem B5089625 : Blo 2261435 5089625 := bstep (se 2 (by rfl) ⟨1908609, by rfl⟩ : syracuseStep 5089625 = 3817219) B3817219
theorem B3393083 : Blo 2261435 3393083 := bstep (se 1 (by rfl) ⟨2544812, by rfl⟩ : syracuseStep 3393083 = 5089625) B5089625
theorem B2262055 : Blo 2261435 2262055 := bstep (se 1 (by rfl) ⟨1696541, by rfl⟩ : syracuseStep 2262055 = 3393083) B3393083
theorem B2544817 : Blo 2261435 2544817 := bbase (se 2 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 2544817 = 1908613) (by norm_num)
theorem B3393089 : Blo 2261435 3393089 := bstep (se 2 (by rfl) ⟨1272408, by rfl⟩ : syracuseStep 3393089 = 2544817) B2544817
theorem B2262059 : Blo 2261435 2262059 := bstep (se 1 (by rfl) ⟨1696544, by rfl⟩ : syracuseStep 2262059 = 3393089) B3393089
theorem B2415593 : Blo 2261435 2415593 := bbase (se 2 (by rfl) ⟨905847, by rfl⟩ : syracuseStep 2415593 = 1811695) (by norm_num)
theorem B6441581 : Blo 2261435 6441581 := bstep (se 3 (by rfl) ⟨1207796, by rfl⟩ : syracuseStep 6441581 = 2415593) B2415593
theorem B4294387 : Blo 2261435 4294387 := bstep (se 1 (by rfl) ⟨3220790, by rfl⟩ : syracuseStep 4294387 = 6441581) B6441581
theorem B5725849 : Blo 2261435 5725849 := bstep (se 2 (by rfl) ⟨2147193, by rfl⟩ : syracuseStep 5725849 = 4294387) B4294387
theorem B7634465 : Blo 2261435 7634465 := bstep (se 2 (by rfl) ⟨2862924, by rfl⟩ : syracuseStep 7634465 = 5725849) B5725849
theorem B5089643 : Blo 2261435 5089643 := bstep (se 1 (by rfl) ⟨3817232, by rfl⟩ : syracuseStep 5089643 = 7634465) B7634465
theorem B3393095 : Blo 2261435 3393095 := bstep (se 1 (by rfl) ⟨2544821, by rfl⟩ : syracuseStep 3393095 = 5089643) B5089643
theorem B2262063 : Blo 2261435 2262063 := bstep (se 1 (by rfl) ⟨1696547, by rfl⟩ : syracuseStep 2262063 = 3393095) B3393095
theorem B3393101 : Blo 2261435 3393101 := bbase (se 3 (by rfl) ⟨636206, by rfl⟩ : syracuseStep 3393101 = 1272413) (by norm_num)
theorem B2262067 : Blo 2261435 2262067 := bstep (se 1 (by rfl) ⟨1696550, by rfl⟩ : syracuseStep 2262067 = 3393101) B3393101
theorem B5089661 : Blo 2261435 5089661 := bbase (se 3 (by rfl) ⟨954311, by rfl⟩ : syracuseStep 5089661 = 1908623) (by norm_num)
theorem B3393107 : Blo 2261435 3393107 := bstep (se 1 (by rfl) ⟨2544830, by rfl⟩ : syracuseStep 3393107 = 5089661) B5089661
theorem B2262071 : Blo 2261435 2262071 := bstep (se 1 (by rfl) ⟨1696553, by rfl⟩ : syracuseStep 2262071 = 3393107) B3393107
theorem B3817253 : Blo 2261435 3817253 := bbase (se 4 (by rfl) ⟨357867, by rfl⟩ : syracuseStep 3817253 = 715735) (by norm_num)
theorem B2544835 : Blo 2261435 2544835 := bstep (se 1 (by rfl) ⟨1908626, by rfl⟩ : syracuseStep 2544835 = 3817253) B3817253
theorem B3393113 : Blo 2261435 3393113 := bstep (se 2 (by rfl) ⟨1272417, by rfl⟩ : syracuseStep 3393113 = 2544835) B2544835
theorem B2262075 : Blo 2261435 2262075 := bstep (se 1 (by rfl) ⟨1696556, by rfl⟩ : syracuseStep 2262075 = 3393113) B3393113
theorem B3220813 : Blo 2261435 3220813 := bbase (se 3 (by rfl) ⟨603902, by rfl⟩ : syracuseStep 3220813 = 1207805) (by norm_num)
theorem B17177669 : Blo 2261435 17177669 := bstep (se 4 (by rfl) ⟨1610406, by rfl⟩ : syracuseStep 17177669 = 3220813) B3220813
theorem B11451779 : Blo 2261435 11451779 := bstep (se 1 (by rfl) ⟨8588834, by rfl⟩ : syracuseStep 11451779 = 17177669) B17177669
theorem B7634519 : Blo 2261435 7634519 := bstep (se 1 (by rfl) ⟨5725889, by rfl⟩ : syracuseStep 7634519 = 11451779) B11451779
theorem B5089679 : Blo 2261435 5089679 := bstep (se 1 (by rfl) ⟨3817259, by rfl⟩ : syracuseStep 5089679 = 7634519) B7634519
theorem B3393119 : Blo 2261435 3393119 := bstep (se 1 (by rfl) ⟨2544839, by rfl⟩ : syracuseStep 3393119 = 5089679) B5089679
theorem B2262079 : Blo 2261435 2262079 := bstep (se 1 (by rfl) ⟨1696559, by rfl⟩ : syracuseStep 2262079 = 3393119) B3393119
theorem B3393125 : Blo 2261435 3393125 := bbase (se 4 (by rfl) ⟨318105, by rfl⟩ : syracuseStep 3393125 = 636211) (by norm_num)
theorem B2262083 : Blo 2261435 2262083 := bstep (se 1 (by rfl) ⟨1696562, by rfl⟩ : syracuseStep 2262083 = 3393125) B3393125
theorem B3623429 : Blo 2261435 3623429 := bbase (se 4 (by rfl) ⟨339696, by rfl⟩ : syracuseStep 3623429 = 679393) (by norm_num)
theorem B2415619 : Blo 2261435 2415619 := bstep (se 1 (by rfl) ⟨1811714, by rfl⟩ : syracuseStep 2415619 = 3623429) B3623429
theorem B3220825 : Blo 2261435 3220825 := bstep (se 2 (by rfl) ⟨1207809, by rfl⟩ : syracuseStep 3220825 = 2415619) B2415619
theorem B4294433 : Blo 2261435 4294433 := bstep (se 2 (by rfl) ⟨1610412, by rfl⟩ : syracuseStep 4294433 = 3220825) B3220825
theorem B2862955 : Blo 2261435 2862955 := bstep (se 1 (by rfl) ⟨2147216, by rfl⟩ : syracuseStep 2862955 = 4294433) B4294433
theorem B3817273 : Blo 2261435 3817273 := bstep (se 2 (by rfl) ⟨1431477, by rfl⟩ : syracuseStep 3817273 = 2862955) B2862955
theorem B5089697 : Blo 2261435 5089697 := bstep (se 2 (by rfl) ⟨1908636, by rfl⟩ : syracuseStep 5089697 = 3817273) B3817273
theorem B3393131 : Blo 2261435 3393131 := bstep (se 1 (by rfl) ⟨2544848, by rfl⟩ : syracuseStep 3393131 = 5089697) B5089697
theorem B2262087 : Blo 2261435 2262087 := bstep (se 1 (by rfl) ⟨1696565, by rfl⟩ : syracuseStep 2262087 = 3393131) B3393131
theorem B2544853 : Blo 2261435 2544853 := bbase (se 7 (by rfl) ⟨29822, by rfl⟩ : syracuseStep 2544853 = 59645) (by norm_num)
theorem B3393137 : Blo 2261435 3393137 := bstep (se 2 (by rfl) ⟨1272426, by rfl⟩ : syracuseStep 3393137 = 2544853) B2544853
theorem B2262091 : Blo 2261435 2262091 := bstep (se 1 (by rfl) ⟨1696568, by rfl⟩ : syracuseStep 2262091 = 3393137) B3393137
theorem B2862965 : Blo 2261435 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B7634573 : Blo 2261435 7634573 := bstep (se 3 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 7634573 = 2862965) B2862965
theorem B5089715 : Blo 2261435 5089715 := bstep (se 1 (by rfl) ⟨3817286, by rfl⟩ : syracuseStep 5089715 = 7634573) B7634573
theorem B3393143 : Blo 2261435 3393143 := bstep (se 1 (by rfl) ⟨2544857, by rfl⟩ : syracuseStep 3393143 = 5089715) B5089715
theorem B2262095 : Blo 2261435 2262095 := bstep (se 1 (by rfl) ⟨1696571, by rfl⟩ : syracuseStep 2262095 = 3393143) B3393143
theorem B3393149 : Blo 2261435 3393149 := bbase (se 3 (by rfl) ⟨636215, by rfl⟩ : syracuseStep 3393149 = 1272431) (by norm_num)
theorem B2262099 : Blo 2261435 2262099 := bstep (se 1 (by rfl) ⟨1696574, by rfl⟩ : syracuseStep 2262099 = 3393149) B3393149
theorem B5089733 : Blo 2261435 5089733 := bbase (se 4 (by rfl) ⟨477162, by rfl⟩ : syracuseStep 5089733 = 954325) (by norm_num)
theorem B3393155 : Blo 2261435 3393155 := bstep (se 1 (by rfl) ⟨2544866, by rfl⟩ : syracuseStep 3393155 = 5089733) B5089733
theorem B2262103 : Blo 2261435 2262103 := bstep (se 1 (by rfl) ⟨1696577, by rfl⟩ : syracuseStep 2262103 = 3393155) B3393155
theorem B10318373 : Blo 2261435 10318373 := bbase (se 4 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 10318373 = 1934695) (by norm_num)
theorem B6878915 : Blo 2261435 6878915 := bstep (se 1 (by rfl) ⟨5159186, by rfl⟩ : syracuseStep 6878915 = 10318373) B10318373
theorem B4585943 : Blo 2261435 4585943 := bstep (se 1 (by rfl) ⟨3439457, by rfl⟩ : syracuseStep 4585943 = 6878915) B6878915
theorem B12229181 : Blo 2261435 12229181 := bstep (se 3 (by rfl) ⟨2292971, by rfl⟩ : syracuseStep 12229181 = 4585943) B4585943
theorem B8152787 : Blo 2261435 8152787 := bstep (se 1 (by rfl) ⟨6114590, by rfl⟩ : syracuseStep 8152787 = 12229181) B12229181
theorem B5435191 : Blo 2261435 5435191 := bstep (se 1 (by rfl) ⟨4076393, by rfl⟩ : syracuseStep 5435191 = 8152787) B8152787
theorem B7246921 : Blo 2261435 7246921 := bstep (se 2 (by rfl) ⟨2717595, by rfl⟩ : syracuseStep 7246921 = 5435191) B5435191
theorem B9662561 : Blo 2261435 9662561 := bstep (se 2 (by rfl) ⟨3623460, by rfl⟩ : syracuseStep 9662561 = 7246921) B7246921
theorem B6441707 : Blo 2261435 6441707 := bstep (se 1 (by rfl) ⟨4831280, by rfl⟩ : syracuseStep 6441707 = 9662561) B9662561
theorem B4294471 : Blo 2261435 4294471 := bstep (se 1 (by rfl) ⟨3220853, by rfl⟩ : syracuseStep 4294471 = 6441707) B6441707
theorem B5725961 : Blo 2261435 5725961 := bstep (se 2 (by rfl) ⟨2147235, by rfl⟩ : syracuseStep 5725961 = 4294471) B4294471
theorem B3817307 : Blo 2261435 3817307 := bstep (se 1 (by rfl) ⟨2862980, by rfl⟩ : syracuseStep 3817307 = 5725961) B5725961
theorem B2544871 : Blo 2261435 2544871 := bstep (se 1 (by rfl) ⟨1908653, by rfl⟩ : syracuseStep 2544871 = 3817307) B3817307
theorem B3393161 : Blo 2261435 3393161 := bstep (se 2 (by rfl) ⟨1272435, by rfl⟩ : syracuseStep 3393161 = 2544871) B2544871
theorem B2262107 : Blo 2261435 2262107 := bstep (se 1 (by rfl) ⟨1696580, by rfl⟩ : syracuseStep 2262107 = 3393161) B3393161
theorem B11451941 : Blo 2261435 11451941 := bbase (se 4 (by rfl) ⟨1073619, by rfl⟩ : syracuseStep 11451941 = 2147239) (by norm_num)
theorem B7634627 : Blo 2261435 7634627 := bstep (se 1 (by rfl) ⟨5725970, by rfl⟩ : syracuseStep 7634627 = 11451941) B11451941
theorem B5089751 : Blo 2261435 5089751 := bstep (se 1 (by rfl) ⟨3817313, by rfl⟩ : syracuseStep 5089751 = 7634627) B7634627
theorem B3393167 : Blo 2261435 3393167 := bstep (se 1 (by rfl) ⟨2544875, by rfl⟩ : syracuseStep 3393167 = 5089751) B5089751
theorem B2262111 : Blo 2261435 2262111 := bstep (se 1 (by rfl) ⟨1696583, by rfl⟩ : syracuseStep 2262111 = 3393167) B3393167
theorem B3393173 : Blo 2261435 3393173 := bbase (se 6 (by rfl) ⟨79527, by rfl⟩ : syracuseStep 3393173 = 159055) (by norm_num)
theorem B2262115 : Blo 2261435 2262115 := bstep (se 1 (by rfl) ⟨1696586, by rfl⟩ : syracuseStep 2262115 = 3393173) B3393173
theorem B12910421 : Blo 2261435 12910421 := bbase (se 9 (by rfl) ⟨37823, by rfl⟩ : syracuseStep 12910421 = 75647) (by norm_num)
theorem B8606947 : Blo 2261435 8606947 := bstep (se 1 (by rfl) ⟨6455210, by rfl⟩ : syracuseStep 8606947 = 12910421) B12910421
theorem B11475929 : Blo 2261435 11475929 := bstep (se 2 (by rfl) ⟨4303473, by rfl⟩ : syracuseStep 11475929 = 8606947) B8606947
theorem B30602477 : Blo 2261435 30602477 := bstep (se 3 (by rfl) ⟨5737964, by rfl⟩ : syracuseStep 30602477 = 11475929) B11475929
theorem B20401651 : Blo 2261435 20401651 := bstep (se 1 (by rfl) ⟨15301238, by rfl⟩ : syracuseStep 20401651 = 30602477) B30602477
theorem B108808805 : Blo 2261435 108808805 := bstep (se 4 (by rfl) ⟨10200825, by rfl⟩ : syracuseStep 108808805 = 20401651) B20401651
theorem B290156813 : Blo 2261435 290156813 := bstep (se 3 (by rfl) ⟨54404402, by rfl⟩ : syracuseStep 290156813 = 108808805) B108808805
theorem B193437875 : Blo 2261435 193437875 := bstep (se 1 (by rfl) ⟨145078406, by rfl⟩ : syracuseStep 193437875 = 290156813) B290156813
theorem B128958583 : Blo 2261435 128958583 := bstep (se 1 (by rfl) ⟨96718937, by rfl⟩ : syracuseStep 128958583 = 193437875) B193437875
theorem B171944777 : Blo 2261435 171944777 := bstep (se 2 (by rfl) ⟨64479291, by rfl⟩ : syracuseStep 171944777 = 128958583) B128958583
theorem B114629851 : Blo 2261435 114629851 := bstep (se 1 (by rfl) ⟨85972388, by rfl⟩ : syracuseStep 114629851 = 171944777) B171944777
theorem B152839801 : Blo 2261435 152839801 := bstep (se 2 (by rfl) ⟨57314925, by rfl⟩ : syracuseStep 152839801 = 114629851) B114629851
theorem B203786401 : Blo 2261435 203786401 := bstep (se 2 (by rfl) ⟨76419900, by rfl⟩ : syracuseStep 203786401 = 152839801) B152839801
theorem B271715201 : Blo 2261435 271715201 := bstep (se 2 (by rfl) ⟨101893200, by rfl⟩ : syracuseStep 271715201 = 203786401) B203786401
theorem B181143467 : Blo 2261435 181143467 := bstep (se 1 (by rfl) ⟨135857600, by rfl⟩ : syracuseStep 181143467 = 271715201) B271715201
theorem B120762311 : Blo 2261435 120762311 := bstep (se 1 (by rfl) ⟨90571733, by rfl⟩ : syracuseStep 120762311 = 181143467) B181143467
theorem B322032829 : Blo 2261435 322032829 := bstep (se 3 (by rfl) ⟨60381155, by rfl⟩ : syracuseStep 322032829 = 120762311) B120762311
theorem B429377105 : Blo 2261435 429377105 := bstep (se 2 (by rfl) ⟨161016414, by rfl⟩ : syracuseStep 429377105 = 322032829) B322032829
theorem B286251403 : Blo 2261435 286251403 := bstep (se 1 (by rfl) ⟨214688552, by rfl⟩ : syracuseStep 286251403 = 429377105) B429377105
theorem B381668537 : Blo 2261435 381668537 := bstep (se 2 (by rfl) ⟨143125701, by rfl⟩ : syracuseStep 381668537 = 286251403) B286251403
theorem B1017782765 : Blo 2261435 1017782765 := bstep (se 3 (by rfl) ⟨190834268, by rfl⟩ : syracuseStep 1017782765 = 381668537) B381668537
theorem B678521843 : Blo 2261435 678521843 := bstep (se 1 (by rfl) ⟨508891382, by rfl⟩ : syracuseStep 678521843 = 1017782765) B1017782765
theorem B452347895 : Blo 2261435 452347895 := bstep (se 1 (by rfl) ⟨339260921, by rfl⟩ : syracuseStep 452347895 = 678521843) B678521843
theorem B301565263 : Blo 2261435 301565263 := bstep (se 1 (by rfl) ⟨226173947, by rfl⟩ : syracuseStep 301565263 = 452347895) B452347895
theorem B402087017 : Blo 2261435 402087017 := bstep (se 2 (by rfl) ⟨150782631, by rfl⟩ : syracuseStep 402087017 = 301565263) B301565263
theorem B268058011 : Blo 2261435 268058011 := bstep (se 1 (by rfl) ⟨201043508, by rfl⟩ : syracuseStep 268058011 = 402087017) B402087017
theorem B357410681 : Blo 2261435 357410681 := bstep (se 2 (by rfl) ⟨134029005, by rfl⟩ : syracuseStep 357410681 = 268058011) B268058011
theorem B238273787 : Blo 2261435 238273787 := bstep (se 1 (by rfl) ⟨178705340, by rfl⟩ : syracuseStep 238273787 = 357410681) B357410681
theorem B158849191 : Blo 2261435 158849191 := bstep (se 1 (by rfl) ⟨119136893, by rfl⟩ : syracuseStep 158849191 = 238273787) B238273787
theorem B847195685 : Blo 2261435 847195685 := bstep (se 4 (by rfl) ⟨79424595, by rfl⟩ : syracuseStep 847195685 = 158849191) B158849191
theorem B564797123 : Blo 2261435 564797123 := bstep (se 1 (by rfl) ⟨423597842, by rfl⟩ : syracuseStep 564797123 = 847195685) B847195685
theorem B376531415 : Blo 2261435 376531415 := bstep (se 1 (by rfl) ⟨282398561, by rfl⟩ : syracuseStep 376531415 = 564797123) B564797123
theorem B251020943 : Blo 2261435 251020943 := bstep (se 1 (by rfl) ⟨188265707, by rfl⟩ : syracuseStep 251020943 = 376531415) B376531415
theorem B167347295 : Blo 2261435 167347295 := bstep (se 1 (by rfl) ⟨125510471, by rfl⟩ : syracuseStep 167347295 = 251020943) B251020943
theorem B111564863 : Blo 2261435 111564863 := bstep (se 1 (by rfl) ⟨83673647, by rfl⟩ : syracuseStep 111564863 = 167347295) B167347295
theorem B74376575 : Blo 2261435 74376575 := bstep (se 1 (by rfl) ⟨55782431, by rfl⟩ : syracuseStep 74376575 = 111564863) B111564863
theorem B49584383 : Blo 2261435 49584383 := bstep (se 1 (by rfl) ⟨37188287, by rfl⟩ : syracuseStep 49584383 = 74376575) B74376575
theorem B33056255 : Blo 2261435 33056255 := bstep (se 1 (by rfl) ⟨24792191, by rfl⟩ : syracuseStep 33056255 = 49584383) B49584383
theorem B22037503 : Blo 2261435 22037503 := bstep (se 1 (by rfl) ⟨16528127, by rfl⟩ : syracuseStep 22037503 = 33056255) B33056255
theorem B29383337 : Blo 2261435 29383337 := bstep (se 2 (by rfl) ⟨11018751, by rfl⟩ : syracuseStep 29383337 = 22037503) B22037503
theorem B19588891 : Blo 2261435 19588891 := bstep (se 1 (by rfl) ⟨14691668, by rfl⟩ : syracuseStep 19588891 = 29383337) B29383337
theorem B26118521 : Blo 2261435 26118521 := bstep (se 2 (by rfl) ⟨9794445, by rfl⟩ : syracuseStep 26118521 = 19588891) B19588891
theorem B17412347 : Blo 2261435 17412347 := bstep (se 1 (by rfl) ⟨13059260, by rfl⟩ : syracuseStep 17412347 = 26118521) B26118521
theorem B11608231 : Blo 2261435 11608231 := bstep (se 1 (by rfl) ⟨8706173, by rfl⟩ : syracuseStep 11608231 = 17412347) B17412347
theorem B15477641 : Blo 2261435 15477641 := bstep (se 2 (by rfl) ⟨5804115, by rfl⟩ : syracuseStep 15477641 = 11608231) B11608231
theorem B10318427 : Blo 2261435 10318427 := bstep (se 1 (by rfl) ⟨7738820, by rfl⟩ : syracuseStep 10318427 = 15477641) B15477641
theorem B6878951 : Blo 2261435 6878951 := bstep (se 1 (by rfl) ⟨5159213, by rfl⟩ : syracuseStep 6878951 = 10318427) B10318427
theorem B4585967 : Blo 2261435 4585967 := bstep (se 1 (by rfl) ⟨3439475, by rfl⟩ : syracuseStep 4585967 = 6878951) B6878951
theorem B3057311 : Blo 2261435 3057311 := bstep (se 1 (by rfl) ⟨2292983, by rfl⟩ : syracuseStep 3057311 = 4585967) B4585967
theorem B8152829 : Blo 2261435 8152829 := bstep (se 3 (by rfl) ⟨1528655, by rfl⟩ : syracuseStep 8152829 = 3057311) B3057311
theorem B5435219 : Blo 2261435 5435219 := bstep (se 1 (by rfl) ⟨4076414, by rfl⟩ : syracuseStep 5435219 = 8152829) B8152829
theorem B14493917 : Blo 2261435 14493917 := bstep (se 3 (by rfl) ⟨2717609, by rfl⟩ : syracuseStep 14493917 = 5435219) B5435219
theorem B9662611 : Blo 2261435 9662611 := bstep (se 1 (by rfl) ⟨7246958, by rfl⟩ : syracuseStep 9662611 = 14493917) B14493917
theorem B12883481 : Blo 2261435 12883481 := bstep (se 2 (by rfl) ⟨4831305, by rfl⟩ : syracuseStep 12883481 = 9662611) B9662611
theorem B8588987 : Blo 2261435 8588987 := bstep (se 1 (by rfl) ⟨6441740, by rfl⟩ : syracuseStep 8588987 = 12883481) B12883481
theorem B5725991 : Blo 2261435 5725991 := bstep (se 1 (by rfl) ⟨4294493, by rfl⟩ : syracuseStep 5725991 = 8588987) B8588987
theorem B3817327 : Blo 2261435 3817327 := bstep (se 1 (by rfl) ⟨2862995, by rfl⟩ : syracuseStep 3817327 = 5725991) B5725991
theorem B5089769 : Blo 2261435 5089769 := bstep (se 2 (by rfl) ⟨1908663, by rfl⟩ : syracuseStep 5089769 = 3817327) B3817327
theorem B3393179 : Blo 2261435 3393179 := bstep (se 1 (by rfl) ⟨2544884, by rfl⟩ : syracuseStep 3393179 = 5089769) B5089769
theorem B2262119 : Blo 2261435 2262119 := bstep (se 1 (by rfl) ⟨1696589, by rfl⟩ : syracuseStep 2262119 = 3393179) B3393179
theorem B2544889 : Blo 2261435 2544889 := bbase (se 2 (by rfl) ⟨954333, by rfl⟩ : syracuseStep 2544889 = 1908667) (by norm_num)
theorem B3393185 : Blo 2261435 3393185 := bstep (se 2 (by rfl) ⟨1272444, by rfl⟩ : syracuseStep 3393185 = 2544889) B2544889
theorem B2262123 : Blo 2261435 2262123 := bstep (se 1 (by rfl) ⟨1696592, by rfl⟩ : syracuseStep 2262123 = 3393185) B3393185
theorem B9662645 : Blo 2261435 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B6441763 : Blo 2261435 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B8589017 : Blo 2261435 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B5726011 : Blo 2261435 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B7634681 : Blo 2261435 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B5089787 : Blo 2261435 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B3393191 : Blo 2261435 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B2262127 : Blo 2261435 2262127 := bstep (se 1 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 2262127 = 3393191) B3393191
theorem B3393197 : Blo 2261435 3393197 := bbase (se 3 (by rfl) ⟨636224, by rfl⟩ : syracuseStep 3393197 = 1272449) (by norm_num)
theorem B2262131 : Blo 2261435 2262131 := bstep (se 1 (by rfl) ⟨1696598, by rfl⟩ : syracuseStep 2262131 = 3393197) B3393197
theorem B5089805 : Blo 2261435 5089805 := bbase (se 3 (by rfl) ⟨954338, by rfl⟩ : syracuseStep 5089805 = 1908677) (by norm_num)
theorem B3393203 : Blo 2261435 3393203 := bstep (se 1 (by rfl) ⟨2544902, by rfl⟩ : syracuseStep 3393203 = 5089805) B5089805
theorem B2262135 : Blo 2261435 2262135 := bstep (se 1 (by rfl) ⟨1696601, by rfl⟩ : syracuseStep 2262135 = 3393203) B3393203
theorem B2863021 : Blo 2261435 2863021 := bbase (se 3 (by rfl) ⟨536816, by rfl⟩ : syracuseStep 2863021 = 1073633) (by norm_num)
theorem B3817361 : Blo 2261435 3817361 := bstep (se 2 (by rfl) ⟨1431510, by rfl⟩ : syracuseStep 3817361 = 2863021) B2863021
theorem B2544907 : Blo 2261435 2544907 := bstep (se 1 (by rfl) ⟨1908680, by rfl⟩ : syracuseStep 2544907 = 3817361) B3817361
theorem B3393209 : Blo 2261435 3393209 := bstep (se 2 (by rfl) ⟨1272453, by rfl⟩ : syracuseStep 3393209 = 2544907) B2544907
theorem B2262139 : Blo 2261435 2262139 := bstep (se 1 (by rfl) ⟨1696604, by rfl⟩ : syracuseStep 2262139 = 3393209) B3393209
theorem B14494069 : Blo 2261435 14494069 := bbase (se 5 (by rfl) ⟨679409, by rfl⟩ : syracuseStep 14494069 = 1358819) (by norm_num)
theorem B19325425 : Blo 2261435 19325425 := bstep (se 2 (by rfl) ⟨7247034, by rfl⟩ : syracuseStep 19325425 = 14494069) B14494069
theorem B25767233 : Blo 2261435 25767233 := bstep (se 2 (by rfl) ⟨9662712, by rfl⟩ : syracuseStep 25767233 = 19325425) B19325425
theorem B17178155 : Blo 2261435 17178155 := bstep (se 1 (by rfl) ⟨12883616, by rfl⟩ : syracuseStep 17178155 = 25767233) B25767233
theorem B11452103 : Blo 2261435 11452103 := bstep (se 1 (by rfl) ⟨8589077, by rfl⟩ : syracuseStep 11452103 = 17178155) B17178155
theorem B7634735 : Blo 2261435 7634735 := bstep (se 1 (by rfl) ⟨5726051, by rfl⟩ : syracuseStep 7634735 = 11452103) B11452103
theorem B5089823 : Blo 2261435 5089823 := bstep (se 1 (by rfl) ⟨3817367, by rfl⟩ : syracuseStep 5089823 = 7634735) B7634735
theorem B3393215 : Blo 2261435 3393215 := bstep (se 1 (by rfl) ⟨2544911, by rfl⟩ : syracuseStep 3393215 = 5089823) B5089823
theorem B2262143 : Blo 2261435 2262143 := bstep (se 1 (by rfl) ⟨1696607, by rfl⟩ : syracuseStep 2262143 = 3393215) B3393215
theorem B3393221 : Blo 2261435 3393221 := bbase (se 4 (by rfl) ⟨318114, by rfl⟩ : syracuseStep 3393221 = 636229) (by norm_num)
theorem B2262147 : Blo 2261435 2262147 := bstep (se 1 (by rfl) ⟨1696610, by rfl⟩ : syracuseStep 2262147 = 3393221) B3393221
theorem B3817381 : Blo 2261435 3817381 := bbase (se 4 (by rfl) ⟨357879, by rfl⟩ : syracuseStep 3817381 = 715759) (by norm_num)
theorem B5089841 : Blo 2261435 5089841 := bstep (se 2 (by rfl) ⟨1908690, by rfl⟩ : syracuseStep 5089841 = 3817381) B3817381
theorem B3393227 : Blo 2261435 3393227 := bstep (se 1 (by rfl) ⟨2544920, by rfl⟩ : syracuseStep 3393227 = 5089841) B5089841
theorem B2262151 : Blo 2261435 2262151 := bstep (se 1 (by rfl) ⟨1696613, by rfl⟩ : syracuseStep 2262151 = 3393227) B3393227
theorem B2544925 : Blo 2261435 2544925 := bbase (se 3 (by rfl) ⟨477173, by rfl⟩ : syracuseStep 2544925 = 954347) (by norm_num)
theorem B3393233 : Blo 2261435 3393233 := bstep (se 2 (by rfl) ⟨1272462, by rfl⟩ : syracuseStep 3393233 = 2544925) B2544925
theorem B2262155 : Blo 2261435 2262155 := bstep (se 1 (by rfl) ⟨1696616, by rfl⟩ : syracuseStep 2262155 = 3393233) B3393233
theorem B7634789 : Blo 2261435 7634789 := bbase (se 4 (by rfl) ⟨715761, by rfl⟩ : syracuseStep 7634789 = 1431523) (by norm_num)
theorem B5089859 : Blo 2261435 5089859 := bstep (se 1 (by rfl) ⟨3817394, by rfl⟩ : syracuseStep 5089859 = 7634789) B7634789
theorem B3393239 : Blo 2261435 3393239 := bstep (se 1 (by rfl) ⟨2544929, by rfl⟩ : syracuseStep 3393239 = 5089859) B5089859
theorem B2262159 : Blo 2261435 2262159 := bstep (se 1 (by rfl) ⟨1696619, by rfl⟩ : syracuseStep 2262159 = 3393239) B3393239
theorem B3393245 : Blo 2261435 3393245 := bbase (se 3 (by rfl) ⟨636233, by rfl⟩ : syracuseStep 3393245 = 1272467) (by norm_num)
theorem B2262163 : Blo 2261435 2262163 := bstep (se 1 (by rfl) ⟨1696622, by rfl⟩ : syracuseStep 2262163 = 3393245) B3393245
theorem B5089877 : Blo 2261435 5089877 := bbase (se 8 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 5089877 = 59647) (by norm_num)
theorem B3393251 : Blo 2261435 3393251 := bstep (se 1 (by rfl) ⟨2544938, by rfl⟩ : syracuseStep 3393251 = 5089877) B5089877
theorem B2262167 : Blo 2261435 2262167 := bstep (se 1 (by rfl) ⟨1696625, by rfl⟩ : syracuseStep 2262167 = 3393251) B3393251
theorem B4076509 : Blo 2261435 4076509 := bbase (se 3 (by rfl) ⟨764345, by rfl⟩ : syracuseStep 4076509 = 1528691) (by norm_num)
theorem B5435345 : Blo 2261435 5435345 := bstep (se 2 (by rfl) ⟨2038254, by rfl⟩ : syracuseStep 5435345 = 4076509) B4076509
theorem B3623563 : Blo 2261435 3623563 := bstep (se 1 (by rfl) ⟨2717672, by rfl⟩ : syracuseStep 3623563 = 5435345) B5435345
theorem B4831417 : Blo 2261435 4831417 := bstep (se 2 (by rfl) ⟨1811781, by rfl⟩ : syracuseStep 4831417 = 3623563) B3623563
theorem B6441889 : Blo 2261435 6441889 := bstep (se 2 (by rfl) ⟨2415708, by rfl⟩ : syracuseStep 6441889 = 4831417) B4831417
theorem B8589185 : Blo 2261435 8589185 := bstep (se 2 (by rfl) ⟨3220944, by rfl⟩ : syracuseStep 8589185 = 6441889) B6441889
theorem B5726123 : Blo 2261435 5726123 := bstep (se 1 (by rfl) ⟨4294592, by rfl⟩ : syracuseStep 5726123 = 8589185) B8589185
theorem B3817415 : Blo 2261435 3817415 := bstep (se 1 (by rfl) ⟨2863061, by rfl⟩ : syracuseStep 3817415 = 5726123) B5726123
theorem B2544943 : Blo 2261435 2544943 := bstep (se 1 (by rfl) ⟨1908707, by rfl⟩ : syracuseStep 2544943 = 3817415) B3817415
theorem B3393257 : Blo 2261435 3393257 := bstep (se 2 (by rfl) ⟨1272471, by rfl⟩ : syracuseStep 3393257 = 2544943) B2544943
theorem B2262171 : Blo 2261435 2262171 := bstep (se 1 (by rfl) ⟨1696628, by rfl⟩ : syracuseStep 2262171 = 3393257) B3393257
theorem B6114773 : Blo 2261435 6114773 := bbase (se 7 (by rfl) ⟨71657, by rfl⟩ : syracuseStep 6114773 = 143315) (by norm_num)
theorem B4076515 : Blo 2261435 4076515 := bstep (se 1 (by rfl) ⟨3057386, by rfl⟩ : syracuseStep 4076515 = 6114773) B6114773
theorem B5435353 : Blo 2261435 5435353 := bstep (se 2 (by rfl) ⟨2038257, by rfl⟩ : syracuseStep 5435353 = 4076515) B4076515
theorem B28988549 : Blo 2261435 28988549 := bstep (se 4 (by rfl) ⟨2717676, by rfl⟩ : syracuseStep 28988549 = 5435353) B5435353
theorem B19325699 : Blo 2261435 19325699 := bstep (se 1 (by rfl) ⟨14494274, by rfl⟩ : syracuseStep 19325699 = 28988549) B28988549
theorem B12883799 : Blo 2261435 12883799 := bstep (se 1 (by rfl) ⟨9662849, by rfl⟩ : syracuseStep 12883799 = 19325699) B19325699
theorem B8589199 : Blo 2261435 8589199 := bstep (se 1 (by rfl) ⟨6441899, by rfl⟩ : syracuseStep 8589199 = 12883799) B12883799
theorem B11452265 : Blo 2261435 11452265 := bstep (se 2 (by rfl) ⟨4294599, by rfl⟩ : syracuseStep 11452265 = 8589199) B8589199
theorem B7634843 : Blo 2261435 7634843 := bstep (se 1 (by rfl) ⟨5726132, by rfl⟩ : syracuseStep 7634843 = 11452265) B11452265
theorem B5089895 : Blo 2261435 5089895 := bstep (se 1 (by rfl) ⟨3817421, by rfl⟩ : syracuseStep 5089895 = 7634843) B7634843
theorem B3393263 : Blo 2261435 3393263 := bstep (se 1 (by rfl) ⟨2544947, by rfl⟩ : syracuseStep 3393263 = 5089895) B5089895
theorem B2262175 : Blo 2261435 2262175 := bstep (se 1 (by rfl) ⟨1696631, by rfl⟩ : syracuseStep 2262175 = 3393263) B3393263
theorem B3393269 : Blo 2261435 3393269 := bbase (se 5 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 3393269 = 318119) (by norm_num)
theorem B2262179 : Blo 2261435 2262179 := bstep (se 1 (by rfl) ⟨1696634, by rfl⟩ : syracuseStep 2262179 = 3393269) B3393269
theorem B9662885 : Blo 2261435 9662885 := bbase (se 4 (by rfl) ⟨905895, by rfl⟩ : syracuseStep 9662885 = 1811791) (by norm_num)
theorem B6441923 : Blo 2261435 6441923 := bstep (se 1 (by rfl) ⟨4831442, by rfl⟩ : syracuseStep 6441923 = 9662885) B9662885
theorem B4294615 : Blo 2261435 4294615 := bstep (se 1 (by rfl) ⟨3220961, by rfl⟩ : syracuseStep 4294615 = 6441923) B6441923
theorem B5726153 : Blo 2261435 5726153 := bstep (se 2 (by rfl) ⟨2147307, by rfl⟩ : syracuseStep 5726153 = 4294615) B4294615
theorem B3817435 : Blo 2261435 3817435 := bstep (se 1 (by rfl) ⟨2863076, by rfl⟩ : syracuseStep 3817435 = 5726153) B5726153
theorem B5089913 : Blo 2261435 5089913 := bstep (se 2 (by rfl) ⟨1908717, by rfl⟩ : syracuseStep 5089913 = 3817435) B3817435
theorem B3393275 : Blo 2261435 3393275 := bstep (se 1 (by rfl) ⟨2544956, by rfl⟩ : syracuseStep 3393275 = 5089913) B5089913
theorem B2262183 : Blo 2261435 2262183 := bstep (se 1 (by rfl) ⟨1696637, by rfl⟩ : syracuseStep 2262183 = 3393275) B3393275
theorem B2544961 : Blo 2261435 2544961 := bbase (se 2 (by rfl) ⟨954360, by rfl⟩ : syracuseStep 2544961 = 1908721) (by norm_num)
theorem B3393281 : Blo 2261435 3393281 := bstep (se 2 (by rfl) ⟨1272480, by rfl⟩ : syracuseStep 3393281 = 2544961) B2544961
theorem B2262187 : Blo 2261435 2262187 := bstep (se 1 (by rfl) ⟨1696640, by rfl⟩ : syracuseStep 2262187 = 3393281) B3393281
theorem B5726173 : Blo 2261435 5726173 := bbase (se 3 (by rfl) ⟨1073657, by rfl⟩ : syracuseStep 5726173 = 2147315) (by norm_num)
theorem B7634897 : Blo 2261435 7634897 := bstep (se 2 (by rfl) ⟨2863086, by rfl⟩ : syracuseStep 7634897 = 5726173) B5726173
theorem B5089931 : Blo 2261435 5089931 := bstep (se 1 (by rfl) ⟨3817448, by rfl⟩ : syracuseStep 5089931 = 7634897) B7634897
theorem B3393287 : Blo 2261435 3393287 := bstep (se 1 (by rfl) ⟨2544965, by rfl⟩ : syracuseStep 3393287 = 5089931) B5089931
theorem B2262191 : Blo 2261435 2262191 := bstep (se 1 (by rfl) ⟨1696643, by rfl⟩ : syracuseStep 2262191 = 3393287) B3393287
theorem B3393293 : Blo 2261435 3393293 := bbase (se 3 (by rfl) ⟨636242, by rfl⟩ : syracuseStep 3393293 = 1272485) (by norm_num)
theorem B2262195 : Blo 2261435 2262195 := bstep (se 1 (by rfl) ⟨1696646, by rfl⟩ : syracuseStep 2262195 = 3393293) B3393293
theorem B5089949 : Blo 2261435 5089949 := bbase (se 3 (by rfl) ⟨954365, by rfl⟩ : syracuseStep 5089949 = 1908731) (by norm_num)
theorem B3393299 : Blo 2261435 3393299 := bstep (se 1 (by rfl) ⟨2544974, by rfl⟩ : syracuseStep 3393299 = 5089949) B5089949
theorem B2262199 : Blo 2261435 2262199 := bstep (se 1 (by rfl) ⟨1696649, by rfl⟩ : syracuseStep 2262199 = 3393299) B3393299
theorem B3817469 : Blo 2261435 3817469 := bbase (se 3 (by rfl) ⟨715775, by rfl⟩ : syracuseStep 3817469 = 1431551) (by norm_num)
theorem B2544979 : Blo 2261435 2544979 := bstep (se 1 (by rfl) ⟨1908734, by rfl⟩ : syracuseStep 2544979 = 3817469) B3817469
theorem B3393305 : Blo 2261435 3393305 := bstep (se 2 (by rfl) ⟨1272489, by rfl⟩ : syracuseStep 3393305 = 2544979) B2544979
theorem B2262203 : Blo 2261435 2262203 := bstep (se 1 (by rfl) ⟨1696652, by rfl⟩ : syracuseStep 2262203 = 3393305) B3393305
theorem B4831493 : Blo 2261435 4831493 := bbase (se 4 (by rfl) ⟨452952, by rfl⟩ : syracuseStep 4831493 = 905905) (by norm_num)
theorem B12883981 : Blo 2261435 12883981 := bstep (se 3 (by rfl) ⟨2415746, by rfl⟩ : syracuseStep 12883981 = 4831493) B4831493
theorem B17178641 : Blo 2261435 17178641 := bstep (se 2 (by rfl) ⟨6441990, by rfl⟩ : syracuseStep 17178641 = 12883981) B12883981
theorem B11452427 : Blo 2261435 11452427 := bstep (se 1 (by rfl) ⟨8589320, by rfl⟩ : syracuseStep 11452427 = 17178641) B17178641
theorem B7634951 : Blo 2261435 7634951 := bstep (se 1 (by rfl) ⟨5726213, by rfl⟩ : syracuseStep 7634951 = 11452427) B11452427
theorem B5089967 : Blo 2261435 5089967 := bstep (se 1 (by rfl) ⟨3817475, by rfl⟩ : syracuseStep 5089967 = 7634951) B7634951
theorem B3393311 : Blo 2261435 3393311 := bstep (se 1 (by rfl) ⟨2544983, by rfl⟩ : syracuseStep 3393311 = 5089967) B5089967
theorem B2262207 : Blo 2261435 2262207 := bstep (se 1 (by rfl) ⟨1696655, by rfl⟩ : syracuseStep 2262207 = 3393311) B3393311
theorem B3393317 : Blo 2261435 3393317 := bbase (se 4 (by rfl) ⟨318123, by rfl⟩ : syracuseStep 3393317 = 636247) (by norm_num)
theorem B2262211 : Blo 2261435 2262211 := bstep (se 1 (by rfl) ⟨1696658, by rfl⟩ : syracuseStep 2262211 = 3393317) B3393317
theorem B2863117 : Blo 2261435 2863117 := bbase (se 3 (by rfl) ⟨536834, by rfl⟩ : syracuseStep 2863117 = 1073669) (by norm_num)
theorem B3817489 : Blo 2261435 3817489 := bstep (se 2 (by rfl) ⟨1431558, by rfl⟩ : syracuseStep 3817489 = 2863117) B2863117
theorem B5089985 : Blo 2261435 5089985 := bstep (se 2 (by rfl) ⟨1908744, by rfl⟩ : syracuseStep 5089985 = 3817489) B3817489
theorem B3393323 : Blo 2261435 3393323 := bstep (se 1 (by rfl) ⟨2544992, by rfl⟩ : syracuseStep 3393323 = 5089985) B5089985
theorem B2262215 : Blo 2261435 2262215 := bstep (se 1 (by rfl) ⟨1696661, by rfl⟩ : syracuseStep 2262215 = 3393323) B3393323
theorem B2544997 : Blo 2261435 2544997 := bbase (se 4 (by rfl) ⟨238593, by rfl⟩ : syracuseStep 2544997 = 477187) (by norm_num)
theorem B3393329 : Blo 2261435 3393329 := bstep (se 2 (by rfl) ⟨1272498, by rfl⟩ : syracuseStep 3393329 = 2544997) B2544997
theorem B2262219 : Blo 2261435 2262219 := bstep (se 1 (by rfl) ⟨1696664, by rfl⟩ : syracuseStep 2262219 = 3393329) B3393329
theorem B6442037 : Blo 2261435 6442037 := bbase (se 5 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 6442037 = 603941) (by norm_num)
theorem B4294691 : Blo 2261435 4294691 := bstep (se 1 (by rfl) ⟨3221018, by rfl⟩ : syracuseStep 4294691 = 6442037) B6442037
theorem B2863127 : Blo 2261435 2863127 := bstep (se 1 (by rfl) ⟨2147345, by rfl⟩ : syracuseStep 2863127 = 4294691) B4294691
theorem B7635005 : Blo 2261435 7635005 := bstep (se 3 (by rfl) ⟨1431563, by rfl⟩ : syracuseStep 7635005 = 2863127) B2863127
theorem B5090003 : Blo 2261435 5090003 := bstep (se 1 (by rfl) ⟨3817502, by rfl⟩ : syracuseStep 5090003 = 7635005) B7635005
theorem B3393335 : Blo 2261435 3393335 := bstep (se 1 (by rfl) ⟨2545001, by rfl⟩ : syracuseStep 3393335 = 5090003) B5090003
theorem B2262223 : Blo 2261435 2262223 := bstep (se 1 (by rfl) ⟨1696667, by rfl⟩ : syracuseStep 2262223 = 3393335) B3393335
theorem B3393341 : Blo 2261435 3393341 := bbase (se 3 (by rfl) ⟨636251, by rfl⟩ : syracuseStep 3393341 = 1272503) (by norm_num)
theorem B2262227 : Blo 2261435 2262227 := bstep (se 1 (by rfl) ⟨1696670, by rfl⟩ : syracuseStep 2262227 = 3393341) B3393341
theorem B5090021 : Blo 2261435 5090021 := bbase (se 4 (by rfl) ⟨477189, by rfl⟩ : syracuseStep 5090021 = 954379) (by norm_num)
theorem B3393347 : Blo 2261435 3393347 := bstep (se 1 (by rfl) ⟨2545010, by rfl⟩ : syracuseStep 3393347 = 5090021) B5090021
theorem B2262231 : Blo 2261435 2262231 := bstep (se 1 (by rfl) ⟨1696673, by rfl⟩ : syracuseStep 2262231 = 3393347) B3393347
theorem B5726285 : Blo 2261435 5726285 := bbase (se 3 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 5726285 = 2147357) (by norm_num)
theorem B3817523 : Blo 2261435 3817523 := bstep (se 1 (by rfl) ⟨2863142, by rfl⟩ : syracuseStep 3817523 = 5726285) B5726285
theorem B2545015 : Blo 2261435 2545015 := bstep (se 1 (by rfl) ⟨1908761, by rfl⟩ : syracuseStep 2545015 = 3817523) B3817523
theorem B3393353 : Blo 2261435 3393353 := bstep (se 2 (by rfl) ⟨1272507, by rfl⟩ : syracuseStep 3393353 = 2545015) B2545015
theorem B2262235 : Blo 2261435 2262235 := bstep (se 1 (by rfl) ⟨1696676, by rfl⟩ : syracuseStep 2262235 = 3393353) B3393353
theorem B2415781 : Blo 2261435 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B3221041 : Blo 2261435 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B4294721 : Blo 2261435 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B11452589 : Blo 2261435 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B7635059 : Blo 2261435 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B5090039 : Blo 2261435 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B3393359 : Blo 2261435 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2262239 : Blo 2261435 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B3393365 : Blo 2261435 3393365 := bbase (se 9 (by rfl) ⟨9941, by rfl⟩ : syracuseStep 3393365 = 19883) (by norm_num)
theorem B2262243 : Blo 2261435 2262243 := bstep (se 1 (by rfl) ⟨1696682, by rfl⟩ : syracuseStep 2262243 = 3393365) B3393365
theorem B9172453 : Blo 2261435 9172453 := bbase (se 4 (by rfl) ⟨859917, by rfl⟩ : syracuseStep 9172453 = 1719835) (by norm_num)
theorem B12229937 : Blo 2261435 12229937 := bstep (se 2 (by rfl) ⟨4586226, by rfl⟩ : syracuseStep 12229937 = 9172453) B9172453
theorem B8153291 : Blo 2261435 8153291 := bstep (se 1 (by rfl) ⟨6114968, by rfl⟩ : syracuseStep 8153291 = 12229937) B12229937
theorem B5435527 : Blo 2261435 5435527 := bstep (se 1 (by rfl) ⟨4076645, by rfl⟩ : syracuseStep 5435527 = 8153291) B8153291
theorem B7247369 : Blo 2261435 7247369 := bstep (se 2 (by rfl) ⟨2717763, by rfl⟩ : syracuseStep 7247369 = 5435527) B5435527
theorem B4831579 : Blo 2261435 4831579 := bstep (se 1 (by rfl) ⟨3623684, by rfl⟩ : syracuseStep 4831579 = 7247369) B7247369
theorem B6442105 : Blo 2261435 6442105 := bstep (se 2 (by rfl) ⟨2415789, by rfl⟩ : syracuseStep 6442105 = 4831579) B4831579
theorem B8589473 : Blo 2261435 8589473 := bstep (se 2 (by rfl) ⟨3221052, by rfl⟩ : syracuseStep 8589473 = 6442105) B6442105
theorem B5726315 : Blo 2261435 5726315 := bstep (se 1 (by rfl) ⟨4294736, by rfl⟩ : syracuseStep 5726315 = 8589473) B8589473
theorem B3817543 : Blo 2261435 3817543 := bstep (se 1 (by rfl) ⟨2863157, by rfl⟩ : syracuseStep 3817543 = 5726315) B5726315
theorem B5090057 : Blo 2261435 5090057 := bstep (se 2 (by rfl) ⟨1908771, by rfl⟩ : syracuseStep 5090057 = 3817543) B3817543
theorem B3393371 : Blo 2261435 3393371 := bstep (se 1 (by rfl) ⟨2545028, by rfl⟩ : syracuseStep 3393371 = 5090057) B5090057
theorem B2262247 : Blo 2261435 2262247 := bstep (se 1 (by rfl) ⟨1696685, by rfl⟩ : syracuseStep 2262247 = 3393371) B3393371
theorem B2545033 : Blo 2261435 2545033 := bbase (se 2 (by rfl) ⟨954387, by rfl⟩ : syracuseStep 2545033 = 1908775) (by norm_num)
theorem B3393377 : Blo 2261435 3393377 := bstep (se 2 (by rfl) ⟨1272516, by rfl⟩ : syracuseStep 3393377 = 2545033) B2545033
theorem B2262251 : Blo 2261435 2262251 := bstep (se 1 (by rfl) ⟨1696688, by rfl⟩ : syracuseStep 2262251 = 3393377) B3393377
theorem B2579761 : Blo 2261435 2579761 := bbase (se 2 (by rfl) ⟨967410, by rfl⟩ : syracuseStep 2579761 = 1934821) (by norm_num)
theorem B13758725 : Blo 2261435 13758725 := bstep (se 4 (by rfl) ⟨1289880, by rfl⟩ : syracuseStep 13758725 = 2579761) B2579761
theorem B9172483 : Blo 2261435 9172483 := bstep (se 1 (by rfl) ⟨6879362, by rfl⟩ : syracuseStep 9172483 = 13758725) B13758725
theorem B48919909 : Blo 2261435 48919909 := bstep (se 4 (by rfl) ⟨4586241, by rfl⟩ : syracuseStep 48919909 = 9172483) B9172483
theorem B65226545 : Blo 2261435 65226545 := bstep (se 2 (by rfl) ⟨24459954, by rfl⟩ : syracuseStep 65226545 = 48919909) B48919909
theorem B43484363 : Blo 2261435 43484363 := bstep (se 1 (by rfl) ⟨32613272, by rfl⟩ : syracuseStep 43484363 = 65226545) B65226545
theorem B28989575 : Blo 2261435 28989575 := bstep (se 1 (by rfl) ⟨21742181, by rfl⟩ : syracuseStep 28989575 = 43484363) B43484363
theorem B19326383 : Blo 2261435 19326383 := bstep (se 1 (by rfl) ⟨14494787, by rfl⟩ : syracuseStep 19326383 = 28989575) B28989575
theorem B12884255 : Blo 2261435 12884255 := bstep (se 1 (by rfl) ⟨9663191, by rfl⟩ : syracuseStep 12884255 = 19326383) B19326383
theorem B8589503 : Blo 2261435 8589503 := bstep (se 1 (by rfl) ⟨6442127, by rfl⟩ : syracuseStep 8589503 = 12884255) B12884255
theorem B5726335 : Blo 2261435 5726335 := bstep (se 1 (by rfl) ⟨4294751, by rfl⟩ : syracuseStep 5726335 = 8589503) B8589503
theorem B7635113 : Blo 2261435 7635113 := bstep (se 2 (by rfl) ⟨2863167, by rfl⟩ : syracuseStep 7635113 = 5726335) B5726335
theorem B5090075 : Blo 2261435 5090075 := bstep (se 1 (by rfl) ⟨3817556, by rfl⟩ : syracuseStep 5090075 = 7635113) B7635113
theorem B3393383 : Blo 2261435 3393383 := bstep (se 1 (by rfl) ⟨2545037, by rfl⟩ : syracuseStep 3393383 = 5090075) B5090075
theorem B2262255 : Blo 2261435 2262255 := bstep (se 1 (by rfl) ⟨1696691, by rfl⟩ : syracuseStep 2262255 = 3393383) B3393383
theorem B3393389 : Blo 2261435 3393389 := bbase (se 3 (by rfl) ⟨636260, by rfl⟩ : syracuseStep 3393389 = 1272521) (by norm_num)
theorem B2262259 : Blo 2261435 2262259 := bstep (se 1 (by rfl) ⟨1696694, by rfl⟩ : syracuseStep 2262259 = 3393389) B3393389
theorem B5090093 : Blo 2261435 5090093 := bbase (se 3 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 5090093 = 1908785) (by norm_num)
theorem B3393395 : Blo 2261435 3393395 := bstep (se 1 (by rfl) ⟨2545046, by rfl⟩ : syracuseStep 3393395 = 5090093) B5090093
theorem B2262263 : Blo 2261435 2262263 := bstep (se 1 (by rfl) ⟨1696697, by rfl⟩ : syracuseStep 2262263 = 3393395) B3393395
theorem B3623717 : Blo 2261435 3623717 := bbase (se 4 (by rfl) ⟨339723, by rfl⟩ : syracuseStep 3623717 = 679447) (by norm_num)
theorem B9663245 : Blo 2261435 9663245 := bstep (se 3 (by rfl) ⟨1811858, by rfl⟩ : syracuseStep 9663245 = 3623717) B3623717
theorem B6442163 : Blo 2261435 6442163 := bstep (se 1 (by rfl) ⟨4831622, by rfl⟩ : syracuseStep 6442163 = 9663245) B9663245
theorem B4294775 : Blo 2261435 4294775 := bstep (se 1 (by rfl) ⟨3221081, by rfl⟩ : syracuseStep 4294775 = 6442163) B6442163
theorem B2863183 : Blo 2261435 2863183 := bstep (se 1 (by rfl) ⟨2147387, by rfl⟩ : syracuseStep 2863183 = 4294775) B4294775
theorem B3817577 : Blo 2261435 3817577 := bstep (se 2 (by rfl) ⟨1431591, by rfl⟩ : syracuseStep 3817577 = 2863183) B2863183
theorem B2545051 : Blo 2261435 2545051 := bstep (se 1 (by rfl) ⟨1908788, by rfl⟩ : syracuseStep 2545051 = 3817577) B3817577
theorem B3393401 : Blo 2261435 3393401 := bstep (se 2 (by rfl) ⟨1272525, by rfl⟩ : syracuseStep 3393401 = 2545051) B2545051
theorem B2262267 : Blo 2261435 2262267 := bstep (se 1 (by rfl) ⟨1696700, by rfl⟩ : syracuseStep 2262267 = 3393401) B3393401
theorem B4132309 : Blo 2261435 4132309 := bbase (se 7 (by rfl) ⟨48425, by rfl⟩ : syracuseStep 4132309 = 96851) (by norm_num)
theorem B5509745 : Blo 2261435 5509745 := bstep (se 2 (by rfl) ⟨2066154, by rfl⟩ : syracuseStep 5509745 = 4132309) B4132309
theorem B3673163 : Blo 2261435 3673163 := bstep (se 1 (by rfl) ⟨2754872, by rfl⟩ : syracuseStep 3673163 = 5509745) B5509745
theorem B2448775 : Blo 2261435 2448775 := bstep (se 1 (by rfl) ⟨1836581, by rfl⟩ : syracuseStep 2448775 = 3673163) B3673163
theorem B13060133 : Blo 2261435 13060133 := bstep (se 4 (by rfl) ⟨1224387, by rfl⟩ : syracuseStep 13060133 = 2448775) B2448775
theorem B8706755 : Blo 2261435 8706755 := bstep (se 1 (by rfl) ⟨6530066, by rfl⟩ : syracuseStep 8706755 = 13060133) B13060133
theorem B5804503 : Blo 2261435 5804503 := bstep (se 1 (by rfl) ⟨4353377, by rfl⟩ : syracuseStep 5804503 = 8706755) B8706755
theorem B123829397 : Blo 2261435 123829397 := bstep (se 6 (by rfl) ⟨2902251, by rfl⟩ : syracuseStep 123829397 = 5804503) B5804503
theorem B82552931 : Blo 2261435 82552931 := bstep (se 1 (by rfl) ⟨61914698, by rfl⟩ : syracuseStep 82552931 = 123829397) B123829397
theorem B55035287 : Blo 2261435 55035287 := bstep (se 1 (by rfl) ⟨41276465, by rfl⟩ : syracuseStep 55035287 = 82552931) B82552931
theorem B36690191 : Blo 2261435 36690191 := bstep (se 1 (by rfl) ⟨27517643, by rfl⟩ : syracuseStep 36690191 = 55035287) B55035287
theorem B24460127 : Blo 2261435 24460127 := bstep (se 1 (by rfl) ⟨18345095, by rfl⟩ : syracuseStep 24460127 = 36690191) B36690191
theorem B16306751 : Blo 2261435 16306751 := bstep (se 1 (by rfl) ⟨12230063, by rfl⟩ : syracuseStep 16306751 = 24460127) B24460127
theorem B10871167 : Blo 2261435 10871167 := bstep (se 1 (by rfl) ⟨8153375, by rfl⟩ : syracuseStep 10871167 = 16306751) B16306751
theorem B14494889 : Blo 2261435 14494889 := bstep (se 2 (by rfl) ⟨5435583, by rfl⟩ : syracuseStep 14494889 = 10871167) B10871167
theorem B38653037 : Blo 2261435 38653037 := bstep (se 3 (by rfl) ⟨7247444, by rfl⟩ : syracuseStep 38653037 = 14494889) B14494889
theorem B25768691 : Blo 2261435 25768691 := bstep (se 1 (by rfl) ⟨19326518, by rfl⟩ : syracuseStep 25768691 = 38653037) B38653037
theorem B17179127 : Blo 2261435 17179127 := bstep (se 1 (by rfl) ⟨12884345, by rfl⟩ : syracuseStep 17179127 = 25768691) B25768691
theorem B11452751 : Blo 2261435 11452751 := bstep (se 1 (by rfl) ⟨8589563, by rfl⟩ : syracuseStep 11452751 = 17179127) B17179127
theorem B7635167 : Blo 2261435 7635167 := bstep (se 1 (by rfl) ⟨5726375, by rfl⟩ : syracuseStep 7635167 = 11452751) B11452751
theorem B5090111 : Blo 2261435 5090111 := bstep (se 1 (by rfl) ⟨3817583, by rfl⟩ : syracuseStep 5090111 = 7635167) B7635167
theorem B3393407 : Blo 2261435 3393407 := bstep (se 1 (by rfl) ⟨2545055, by rfl⟩ : syracuseStep 3393407 = 5090111) B5090111
theorem B2262271 : Blo 2261435 2262271 := bstep (se 1 (by rfl) ⟨1696703, by rfl⟩ : syracuseStep 2262271 = 3393407) B3393407
theorem B3393413 : Blo 2261435 3393413 := bbase (se 4 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 3393413 = 636265) (by norm_num)
theorem B2262275 : Blo 2261435 2262275 := bstep (se 1 (by rfl) ⟨1696706, by rfl⟩ : syracuseStep 2262275 = 3393413) B3393413
theorem B3817597 : Blo 2261435 3817597 := bbase (se 3 (by rfl) ⟨715799, by rfl⟩ : syracuseStep 3817597 = 1431599) (by norm_num)
theorem B5090129 : Blo 2261435 5090129 := bstep (se 2 (by rfl) ⟨1908798, by rfl⟩ : syracuseStep 5090129 = 3817597) B3817597
theorem B3393419 : Blo 2261435 3393419 := bstep (se 1 (by rfl) ⟨2545064, by rfl⟩ : syracuseStep 3393419 = 5090129) B5090129
theorem B2262279 : Blo 2261435 2262279 := bstep (se 1 (by rfl) ⟨1696709, by rfl⟩ : syracuseStep 2262279 = 3393419) B3393419
theorem B2545069 : Blo 2261435 2545069 := bbase (se 3 (by rfl) ⟨477200, by rfl⟩ : syracuseStep 2545069 = 954401) (by norm_num)
theorem B3393425 : Blo 2261435 3393425 := bstep (se 2 (by rfl) ⟨1272534, by rfl⟩ : syracuseStep 3393425 = 2545069) B2545069
theorem B2262283 : Blo 2261435 2262283 := bstep (se 1 (by rfl) ⟨1696712, by rfl⟩ : syracuseStep 2262283 = 3393425) B3393425
theorem B7635221 : Blo 2261435 7635221 := bbase (se 6 (by rfl) ⟨178950, by rfl⟩ : syracuseStep 7635221 = 357901) (by norm_num)
theorem B5090147 : Blo 2261435 5090147 := bstep (se 1 (by rfl) ⟨3817610, by rfl⟩ : syracuseStep 5090147 = 7635221) B7635221
theorem B3393431 : Blo 2261435 3393431 := bstep (se 1 (by rfl) ⟨2545073, by rfl⟩ : syracuseStep 3393431 = 5090147) B5090147
theorem B2262287 : Blo 2261435 2262287 := bstep (se 1 (by rfl) ⟨1696715, by rfl⟩ : syracuseStep 2262287 = 3393431) B3393431
theorem B3393437 : Blo 2261435 3393437 := bbase (se 3 (by rfl) ⟨636269, by rfl⟩ : syracuseStep 3393437 = 1272539) (by norm_num)
theorem B2262291 : Blo 2261435 2262291 := bstep (se 1 (by rfl) ⟨1696718, by rfl⟩ : syracuseStep 2262291 = 3393437) B3393437
theorem B5090165 : Blo 2261435 5090165 := bbase (se 5 (by rfl) ⟨238601, by rfl⟩ : syracuseStep 5090165 = 477203) (by norm_num)
theorem B3393443 : Blo 2261435 3393443 := bstep (se 1 (by rfl) ⟨2545082, by rfl⟩ : syracuseStep 3393443 = 5090165) B5090165
theorem B2262295 : Blo 2261435 2262295 := bstep (se 1 (by rfl) ⟨1696721, by rfl⟩ : syracuseStep 2262295 = 3393443) B3393443
theorem B6530149 : Blo 2261435 6530149 := bbase (se 4 (by rfl) ⟨612201, by rfl⟩ : syracuseStep 6530149 = 1224403) (by norm_num)
theorem B8706865 : Blo 2261435 8706865 := bstep (se 2 (by rfl) ⟨3265074, by rfl⟩ : syracuseStep 8706865 = 6530149) B6530149
theorem B11609153 : Blo 2261435 11609153 := bstep (se 2 (by rfl) ⟨4353432, by rfl⟩ : syracuseStep 11609153 = 8706865) B8706865
theorem B7739435 : Blo 2261435 7739435 := bstep (se 1 (by rfl) ⟨5804576, by rfl⟩ : syracuseStep 7739435 = 11609153) B11609153
theorem B5159623 : Blo 2261435 5159623 := bstep (se 1 (by rfl) ⟨3869717, by rfl⟩ : syracuseStep 5159623 = 7739435) B7739435
theorem B6879497 : Blo 2261435 6879497 := bstep (se 2 (by rfl) ⟨2579811, by rfl⟩ : syracuseStep 6879497 = 5159623) B5159623
theorem B73381301 : Blo 2261435 73381301 := bstep (se 5 (by rfl) ⟨3439748, by rfl⟩ : syracuseStep 73381301 = 6879497) B6879497
theorem B48920867 : Blo 2261435 48920867 := bstep (se 1 (by rfl) ⟨36690650, by rfl⟩ : syracuseStep 48920867 = 73381301) B73381301
theorem B32613911 : Blo 2261435 32613911 := bstep (se 1 (by rfl) ⟨24460433, by rfl⟩ : syracuseStep 32613911 = 48920867) B48920867
theorem B21742607 : Blo 2261435 21742607 := bstep (se 1 (by rfl) ⟨16306955, by rfl⟩ : syracuseStep 21742607 = 32613911) B32613911
theorem B14495071 : Blo 2261435 14495071 := bstep (se 1 (by rfl) ⟨10871303, by rfl⟩ : syracuseStep 14495071 = 21742607) B21742607
theorem B19326761 : Blo 2261435 19326761 := bstep (se 2 (by rfl) ⟨7247535, by rfl⟩ : syracuseStep 19326761 = 14495071) B14495071
theorem B12884507 : Blo 2261435 12884507 := bstep (se 1 (by rfl) ⟨9663380, by rfl⟩ : syracuseStep 12884507 = 19326761) B19326761
theorem B8589671 : Blo 2261435 8589671 := bstep (se 1 (by rfl) ⟨6442253, by rfl⟩ : syracuseStep 8589671 = 12884507) B12884507
theorem B5726447 : Blo 2261435 5726447 := bstep (se 1 (by rfl) ⟨4294835, by rfl⟩ : syracuseStep 5726447 = 8589671) B8589671
theorem B3817631 : Blo 2261435 3817631 := bstep (se 1 (by rfl) ⟨2863223, by rfl⟩ : syracuseStep 3817631 = 5726447) B5726447
theorem B2545087 : Blo 2261435 2545087 := bstep (se 1 (by rfl) ⟨1908815, by rfl⟩ : syracuseStep 2545087 = 3817631) B3817631
theorem B3393449 : Blo 2261435 3393449 := bstep (se 2 (by rfl) ⟨1272543, by rfl⟩ : syracuseStep 3393449 = 2545087) B2545087
theorem B2262299 : Blo 2261435 2262299 := bstep (se 1 (by rfl) ⟨1696724, by rfl⟩ : syracuseStep 2262299 = 3393449) B3393449
theorem B8589685 : Blo 2261435 8589685 := bbase (se 5 (by rfl) ⟨402641, by rfl⟩ : syracuseStep 8589685 = 805283) (by norm_num)
theorem B11452913 : Blo 2261435 11452913 := bstep (se 2 (by rfl) ⟨4294842, by rfl⟩ : syracuseStep 11452913 = 8589685) B8589685
theorem B7635275 : Blo 2261435 7635275 := bstep (se 1 (by rfl) ⟨5726456, by rfl⟩ : syracuseStep 7635275 = 11452913) B11452913
theorem B5090183 : Blo 2261435 5090183 := bstep (se 1 (by rfl) ⟨3817637, by rfl⟩ : syracuseStep 5090183 = 7635275) B7635275
theorem B3393455 : Blo 2261435 3393455 := bstep (se 1 (by rfl) ⟨2545091, by rfl⟩ : syracuseStep 3393455 = 5090183) B5090183
theorem B2262303 : Blo 2261435 2262303 := bstep (se 1 (by rfl) ⟨1696727, by rfl⟩ : syracuseStep 2262303 = 3393455) B3393455
theorem B3393461 : Blo 2261435 3393461 := bbase (se 5 (by rfl) ⟨159068, by rfl⟩ : syracuseStep 3393461 = 318137) (by norm_num)
theorem B2262307 : Blo 2261435 2262307 := bstep (se 1 (by rfl) ⟨1696730, by rfl⟩ : syracuseStep 2262307 = 3393461) B3393461
theorem B5726477 : Blo 2261435 5726477 := bbase (se 3 (by rfl) ⟨1073714, by rfl⟩ : syracuseStep 5726477 = 2147429) (by norm_num)
theorem B3817651 : Blo 2261435 3817651 := bstep (se 1 (by rfl) ⟨2863238, by rfl⟩ : syracuseStep 3817651 = 5726477) B5726477
theorem B5090201 : Blo 2261435 5090201 := bstep (se 2 (by rfl) ⟨1908825, by rfl⟩ : syracuseStep 5090201 = 3817651) B3817651
theorem B3393467 : Blo 2261435 3393467 := bstep (se 1 (by rfl) ⟨2545100, by rfl⟩ : syracuseStep 3393467 = 5090201) B5090201
theorem B2262311 : Blo 2261435 2262311 := bstep (se 1 (by rfl) ⟨1696733, by rfl⟩ : syracuseStep 2262311 = 3393467) B3393467
theorem B2545105 : Blo 2261435 2545105 := bbase (se 2 (by rfl) ⟨954414, by rfl⟩ : syracuseStep 2545105 = 1908829) (by norm_num)
theorem B3393473 : Blo 2261435 3393473 := bstep (se 2 (by rfl) ⟨1272552, by rfl⟩ : syracuseStep 3393473 = 2545105) B2545105
theorem B2262315 : Blo 2261435 2262315 := bstep (se 1 (by rfl) ⟨1696736, by rfl⟩ : syracuseStep 2262315 = 3393473) B3393473
theorem B4831733 : Blo 2261435 4831733 := bbase (se 5 (by rfl) ⟨226487, by rfl⟩ : syracuseStep 4831733 = 452975) (by norm_num)
theorem B3221155 : Blo 2261435 3221155 := bstep (se 1 (by rfl) ⟨2415866, by rfl⟩ : syracuseStep 3221155 = 4831733) B4831733
theorem B4294873 : Blo 2261435 4294873 := bstep (se 2 (by rfl) ⟨1610577, by rfl⟩ : syracuseStep 4294873 = 3221155) B3221155
theorem B5726497 : Blo 2261435 5726497 := bstep (se 2 (by rfl) ⟨2147436, by rfl⟩ : syracuseStep 5726497 = 4294873) B4294873
theorem B7635329 : Blo 2261435 7635329 := bstep (se 2 (by rfl) ⟨2863248, by rfl⟩ : syracuseStep 7635329 = 5726497) B5726497
theorem B5090219 : Blo 2261435 5090219 := bstep (se 1 (by rfl) ⟨3817664, by rfl⟩ : syracuseStep 5090219 = 7635329) B7635329
theorem B3393479 : Blo 2261435 3393479 := bstep (se 1 (by rfl) ⟨2545109, by rfl⟩ : syracuseStep 3393479 = 5090219) B5090219
theorem B2262319 : Blo 2261435 2262319 := bstep (se 1 (by rfl) ⟨1696739, by rfl⟩ : syracuseStep 2262319 = 3393479) B3393479
theorem B3393485 : Blo 2261435 3393485 := bbase (se 3 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 3393485 = 1272557) (by norm_num)
theorem B2262323 : Blo 2261435 2262323 := bstep (se 1 (by rfl) ⟨1696742, by rfl⟩ : syracuseStep 2262323 = 3393485) B3393485
theorem B5090237 : Blo 2261435 5090237 := bbase (se 3 (by rfl) ⟨954419, by rfl⟩ : syracuseStep 5090237 = 1908839) (by norm_num)
theorem B3393491 : Blo 2261435 3393491 := bstep (se 1 (by rfl) ⟨2545118, by rfl⟩ : syracuseStep 3393491 = 5090237) B5090237
theorem B2262327 : Blo 2261435 2262327 := bstep (se 1 (by rfl) ⟨1696745, by rfl⟩ : syracuseStep 2262327 = 3393491) B3393491
theorem B3817685 : Blo 2261435 3817685 := bbase (se 7 (by rfl) ⟨44738, by rfl⟩ : syracuseStep 3817685 = 89477) (by norm_num)
theorem B2545123 : Blo 2261435 2545123 := bstep (se 1 (by rfl) ⟨1908842, by rfl⟩ : syracuseStep 2545123 = 3817685) B3817685
theorem B3393497 : Blo 2261435 3393497 := bstep (se 2 (by rfl) ⟨1272561, by rfl⟩ : syracuseStep 3393497 = 2545123) B2545123
theorem B2262331 : Blo 2261435 2262331 := bstep (se 1 (by rfl) ⟨1696748, by rfl⟩ : syracuseStep 2262331 = 3393497) B3393497
theorem B2717869 : Blo 2261435 2717869 := bbase (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) (by norm_num)
theorem B3623825 : Blo 2261435 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B9663533 : Blo 2261435 9663533 := bstep (se 3 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 9663533 = 3623825) B3623825
theorem B6442355 : Blo 2261435 6442355 := bstep (se 1 (by rfl) ⟨4831766, by rfl⟩ : syracuseStep 6442355 = 9663533) B9663533
theorem B17179613 : Blo 2261435 17179613 := bstep (se 3 (by rfl) ⟨3221177, by rfl⟩ : syracuseStep 17179613 = 6442355) B6442355
theorem B11453075 : Blo 2261435 11453075 := bstep (se 1 (by rfl) ⟨8589806, by rfl⟩ : syracuseStep 11453075 = 17179613) B17179613
theorem B7635383 : Blo 2261435 7635383 := bstep (se 1 (by rfl) ⟨5726537, by rfl⟩ : syracuseStep 7635383 = 11453075) B11453075
theorem B5090255 : Blo 2261435 5090255 := bstep (se 1 (by rfl) ⟨3817691, by rfl⟩ : syracuseStep 5090255 = 7635383) B7635383
theorem B3393503 : Blo 2261435 3393503 := bstep (se 1 (by rfl) ⟨2545127, by rfl⟩ : syracuseStep 3393503 = 5090255) B5090255
theorem B2262335 : Blo 2261435 2262335 := bstep (se 1 (by rfl) ⟨1696751, by rfl⟩ : syracuseStep 2262335 = 3393503) B3393503
theorem B3393509 : Blo 2261435 3393509 := bbase (se 4 (by rfl) ⟨318141, by rfl⟩ : syracuseStep 3393509 = 636283) (by norm_num)
theorem B2262339 : Blo 2261435 2262339 := bstep (se 1 (by rfl) ⟨1696754, by rfl⟩ : syracuseStep 2262339 = 3393509) B3393509
theorem B5804693 : Blo 2261435 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B3869795 : Blo 2261435 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B2579863 : Blo 2261435 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B3439817 : Blo 2261435 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2293211 : Blo 2261435 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B6115229 : Blo 2261435 6115229 := bstep (se 3 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 6115229 = 2293211) B2293211
theorem B4076819 : Blo 2261435 4076819 := bstep (se 1 (by rfl) ⟨3057614, by rfl⟩ : syracuseStep 4076819 = 6115229) B6115229
theorem B2717879 : Blo 2261435 2717879 := bstep (se 1 (by rfl) ⟨2038409, by rfl⟩ : syracuseStep 2717879 = 4076819) B4076819
theorem B7247677 : Blo 2261435 7247677 := bstep (se 3 (by rfl) ⟨1358939, by rfl⟩ : syracuseStep 7247677 = 2717879) B2717879
theorem B9663569 : Blo 2261435 9663569 := bstep (se 2 (by rfl) ⟨3623838, by rfl⟩ : syracuseStep 9663569 = 7247677) B7247677
theorem B6442379 : Blo 2261435 6442379 := bstep (se 1 (by rfl) ⟨4831784, by rfl⟩ : syracuseStep 6442379 = 9663569) B9663569
theorem B4294919 : Blo 2261435 4294919 := bstep (se 1 (by rfl) ⟨3221189, by rfl⟩ : syracuseStep 4294919 = 6442379) B6442379
theorem B2863279 : Blo 2261435 2863279 := bstep (se 1 (by rfl) ⟨2147459, by rfl⟩ : syracuseStep 2863279 = 4294919) B4294919
theorem B3817705 : Blo 2261435 3817705 := bstep (se 2 (by rfl) ⟨1431639, by rfl⟩ : syracuseStep 3817705 = 2863279) B2863279
theorem B5090273 : Blo 2261435 5090273 := bstep (se 2 (by rfl) ⟨1908852, by rfl⟩ : syracuseStep 5090273 = 3817705) B3817705
theorem B3393515 : Blo 2261435 3393515 := bstep (se 1 (by rfl) ⟨2545136, by rfl⟩ : syracuseStep 3393515 = 5090273) B5090273
theorem B2262343 : Blo 2261435 2262343 := bstep (se 1 (by rfl) ⟨1696757, by rfl⟩ : syracuseStep 2262343 = 3393515) B3393515
theorem B2545141 : Blo 2261435 2545141 := bbase (se 5 (by rfl) ⟨119303, by rfl⟩ : syracuseStep 2545141 = 238607) (by norm_num)
theorem B3393521 : Blo 2261435 3393521 := bstep (se 2 (by rfl) ⟨1272570, by rfl⟩ : syracuseStep 3393521 = 2545141) B2545141
theorem B2262347 : Blo 2261435 2262347 := bstep (se 1 (by rfl) ⟨1696760, by rfl⟩ : syracuseStep 2262347 = 3393521) B3393521
theorem B2863289 : Blo 2261435 2863289 := bbase (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) (by norm_num)
theorem B7635437 : Blo 2261435 7635437 := bstep (se 3 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 7635437 = 2863289) B2863289
theorem B5090291 : Blo 2261435 5090291 := bstep (se 1 (by rfl) ⟨3817718, by rfl⟩ : syracuseStep 5090291 = 7635437) B7635437
theorem B3393527 : Blo 2261435 3393527 := bstep (se 1 (by rfl) ⟨2545145, by rfl⟩ : syracuseStep 3393527 = 5090291) B5090291
theorem B2262351 : Blo 2261435 2262351 := bstep (se 1 (by rfl) ⟨1696763, by rfl⟩ : syracuseStep 2262351 = 3393527) B3393527
theorem B3393533 : Blo 2261435 3393533 := bbase (se 3 (by rfl) ⟨636287, by rfl⟩ : syracuseStep 3393533 = 1272575) (by norm_num)
theorem B2262355 : Blo 2261435 2262355 := bstep (se 1 (by rfl) ⟨1696766, by rfl⟩ : syracuseStep 2262355 = 3393533) B3393533
theorem B5090309 : Blo 2261435 5090309 := bbase (se 4 (by rfl) ⟨477216, by rfl⟩ : syracuseStep 5090309 = 954433) (by norm_num)
theorem B3393539 : Blo 2261435 3393539 := bstep (se 1 (by rfl) ⟨2545154, by rfl⟩ : syracuseStep 3393539 = 5090309) B5090309
theorem B2262359 : Blo 2261435 2262359 := bstep (se 1 (by rfl) ⟨1696769, by rfl⟩ : syracuseStep 2262359 = 3393539) B3393539
theorem B4294957 : Blo 2261435 4294957 := bbase (se 3 (by rfl) ⟨805304, by rfl⟩ : syracuseStep 4294957 = 1610609) (by norm_num)
theorem B5726609 : Blo 2261435 5726609 := bstep (se 2 (by rfl) ⟨2147478, by rfl⟩ : syracuseStep 5726609 = 4294957) B4294957
theorem B3817739 : Blo 2261435 3817739 := bstep (se 1 (by rfl) ⟨2863304, by rfl⟩ : syracuseStep 3817739 = 5726609) B5726609
theorem B2545159 : Blo 2261435 2545159 := bstep (se 1 (by rfl) ⟨1908869, by rfl⟩ : syracuseStep 2545159 = 3817739) B3817739
theorem B3393545 : Blo 2261435 3393545 := bstep (se 2 (by rfl) ⟨1272579, by rfl⟩ : syracuseStep 3393545 = 2545159) B2545159
theorem B2262363 : Blo 2261435 2262363 := bstep (se 1 (by rfl) ⟨1696772, by rfl⟩ : syracuseStep 2262363 = 3393545) B3393545
theorem B11453237 : Blo 2261435 11453237 := bbase (se 5 (by rfl) ⟨536870, by rfl⟩ : syracuseStep 11453237 = 1073741) (by norm_num)
theorem B7635491 : Blo 2261435 7635491 := bstep (se 1 (by rfl) ⟨5726618, by rfl⟩ : syracuseStep 7635491 = 11453237) B11453237
theorem B5090327 : Blo 2261435 5090327 := bstep (se 1 (by rfl) ⟨3817745, by rfl⟩ : syracuseStep 5090327 = 7635491) B7635491
theorem B3393551 : Blo 2261435 3393551 := bstep (se 1 (by rfl) ⟨2545163, by rfl⟩ : syracuseStep 3393551 = 5090327) B5090327
theorem B2262367 : Blo 2261435 2262367 := bstep (se 1 (by rfl) ⟨1696775, by rfl⟩ : syracuseStep 2262367 = 3393551) B3393551
theorem B3393557 : Blo 2261435 3393557 := bbase (se 6 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 3393557 = 159073) (by norm_num)
theorem B2262371 : Blo 2261435 2262371 := bstep (se 1 (by rfl) ⟨1696778, by rfl⟩ : syracuseStep 2262371 = 3393557) B3393557
theorem B2717917 : Blo 2261435 2717917 := bbase (se 3 (by rfl) ⟨509609, by rfl⟩ : syracuseStep 2717917 = 1019219) (by norm_num)
theorem B14495557 : Blo 2261435 14495557 := bstep (se 4 (by rfl) ⟨1358958, by rfl⟩ : syracuseStep 14495557 = 2717917) B2717917
theorem B19327409 : Blo 2261435 19327409 := bstep (se 2 (by rfl) ⟨7247778, by rfl⟩ : syracuseStep 19327409 = 14495557) B14495557
theorem B12884939 : Blo 2261435 12884939 := bstep (se 1 (by rfl) ⟨9663704, by rfl⟩ : syracuseStep 12884939 = 19327409) B19327409
theorem B8589959 : Blo 2261435 8589959 := bstep (se 1 (by rfl) ⟨6442469, by rfl⟩ : syracuseStep 8589959 = 12884939) B12884939
theorem B5726639 : Blo 2261435 5726639 := bstep (se 1 (by rfl) ⟨4294979, by rfl⟩ : syracuseStep 5726639 = 8589959) B8589959
theorem B3817759 : Blo 2261435 3817759 := bstep (se 1 (by rfl) ⟨2863319, by rfl⟩ : syracuseStep 3817759 = 5726639) B5726639
theorem B5090345 : Blo 2261435 5090345 := bstep (se 2 (by rfl) ⟨1908879, by rfl⟩ : syracuseStep 5090345 = 3817759) B3817759
theorem B3393563 : Blo 2261435 3393563 := bstep (se 1 (by rfl) ⟨2545172, by rfl⟩ : syracuseStep 3393563 = 5090345) B5090345
theorem B2262375 : Blo 2261435 2262375 := bstep (se 1 (by rfl) ⟨1696781, by rfl⟩ : syracuseStep 2262375 = 3393563) B3393563
theorem B2545177 : Blo 2261435 2545177 := bbase (se 2 (by rfl) ⟨954441, by rfl⟩ : syracuseStep 2545177 = 1908883) (by norm_num)
theorem B3393569 : Blo 2261435 3393569 := bstep (se 2 (by rfl) ⟨1272588, by rfl⟩ : syracuseStep 3393569 = 2545177) B2545177
theorem B2262379 : Blo 2261435 2262379 := bstep (se 1 (by rfl) ⟨1696784, by rfl⟩ : syracuseStep 2262379 = 3393569) B3393569
theorem B8589989 : Blo 2261435 8589989 := bbase (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) (by norm_num)
theorem B5726659 : Blo 2261435 5726659 := bstep (se 1 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 5726659 = 8589989) B8589989
theorem B7635545 : Blo 2261435 7635545 := bstep (se 2 (by rfl) ⟨2863329, by rfl⟩ : syracuseStep 7635545 = 5726659) B5726659
theorem B5090363 : Blo 2261435 5090363 := bstep (se 1 (by rfl) ⟨3817772, by rfl⟩ : syracuseStep 5090363 = 7635545) B7635545
theorem B3393575 : Blo 2261435 3393575 := bstep (se 1 (by rfl) ⟨2545181, by rfl⟩ : syracuseStep 3393575 = 5090363) B5090363
theorem B2262383 : Blo 2261435 2262383 := bstep (se 1 (by rfl) ⟨1696787, by rfl⟩ : syracuseStep 2262383 = 3393575) B3393575
theorem B3393581 : Blo 2261435 3393581 := bbase (se 3 (by rfl) ⟨636296, by rfl⟩ : syracuseStep 3393581 = 1272593) (by norm_num)
theorem B2262387 : Blo 2261435 2262387 := bstep (se 1 (by rfl) ⟨1696790, by rfl⟩ : syracuseStep 2262387 = 3393581) B3393581
theorem B5090381 : Blo 2261435 5090381 := bbase (se 3 (by rfl) ⟨954446, by rfl⟩ : syracuseStep 5090381 = 1908893) (by norm_num)
theorem B3393587 : Blo 2261435 3393587 := bstep (se 1 (by rfl) ⟨2545190, by rfl⟩ : syracuseStep 3393587 = 5090381) B5090381
theorem B2262391 : Blo 2261435 2262391 := bstep (se 1 (by rfl) ⟨1696793, by rfl⟩ : syracuseStep 2262391 = 3393587) B3393587
theorem B2863345 : Blo 2261435 2863345 := bbase (se 2 (by rfl) ⟨1073754, by rfl⟩ : syracuseStep 2863345 = 2147509) (by norm_num)
theorem B3817793 : Blo 2261435 3817793 := bstep (se 2 (by rfl) ⟨1431672, by rfl⟩ : syracuseStep 3817793 = 2863345) B2863345
theorem B2545195 : Blo 2261435 2545195 := bstep (se 1 (by rfl) ⟨1908896, by rfl⟩ : syracuseStep 2545195 = 3817793) B3817793
theorem B3393593 : Blo 2261435 3393593 := bstep (se 2 (by rfl) ⟨1272597, by rfl⟩ : syracuseStep 3393593 = 2545195) B2545195
theorem B2262395 : Blo 2261435 2262395 := bstep (se 1 (by rfl) ⟨1696796, by rfl⟩ : syracuseStep 2262395 = 3393593) B3393593
theorem B41278805 : Blo 2261435 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B27519203 : Blo 2261435 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B18346135 : Blo 2261435 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B24461513 : Blo 2261435 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B16307675 : Blo 2261435 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B10871783 : Blo 2261435 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B7247855 : Blo 2261435 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B4831903 : Blo 2261435 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B25770149 : Blo 2261435 25770149 := bstep (se 4 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 25770149 = 4831903) B4831903
theorem B17180099 : Blo 2261435 17180099 := bstep (se 1 (by rfl) ⟨12885074, by rfl⟩ : syracuseStep 17180099 = 25770149) B25770149
theorem B11453399 : Blo 2261435 11453399 := bstep (se 1 (by rfl) ⟨8590049, by rfl⟩ : syracuseStep 11453399 = 17180099) B17180099
theorem B7635599 : Blo 2261435 7635599 := bstep (se 1 (by rfl) ⟨5726699, by rfl⟩ : syracuseStep 7635599 = 11453399) B11453399
theorem B5090399 : Blo 2261435 5090399 := bstep (se 1 (by rfl) ⟨3817799, by rfl⟩ : syracuseStep 5090399 = 7635599) B7635599
theorem B3393599 : Blo 2261435 3393599 := bstep (se 1 (by rfl) ⟨2545199, by rfl⟩ : syracuseStep 3393599 = 5090399) B5090399
theorem B2262399 : Blo 2261435 2262399 := bstep (se 1 (by rfl) ⟨1696799, by rfl⟩ : syracuseStep 2262399 = 3393599) B3393599
theorem B3393605 : Blo 2261435 3393605 := bbase (se 4 (by rfl) ⟨318150, by rfl⟩ : syracuseStep 3393605 = 636301) (by norm_num)
theorem B2262403 : Blo 2261435 2262403 := bstep (se 1 (by rfl) ⟨1696802, by rfl⟩ : syracuseStep 2262403 = 3393605) B3393605
theorem B3817813 : Blo 2261435 3817813 := bbase (se 10 (by rfl) ⟨5592, by rfl⟩ : syracuseStep 3817813 = 11185) (by norm_num)
theorem B5090417 : Blo 2261435 5090417 := bstep (se 2 (by rfl) ⟨1908906, by rfl⟩ : syracuseStep 5090417 = 3817813) B3817813
theorem B3393611 : Blo 2261435 3393611 := bstep (se 1 (by rfl) ⟨2545208, by rfl⟩ : syracuseStep 3393611 = 5090417) B5090417
theorem B2262407 : Blo 2261435 2262407 := bstep (se 1 (by rfl) ⟨1696805, by rfl⟩ : syracuseStep 2262407 = 3393611) B3393611
theorem B2545213 : Blo 2261435 2545213 := bbase (se 3 (by rfl) ⟨477227, by rfl⟩ : syracuseStep 2545213 = 954455) (by norm_num)
theorem B3393617 : Blo 2261435 3393617 := bstep (se 2 (by rfl) ⟨1272606, by rfl⟩ : syracuseStep 3393617 = 2545213) B2545213
theorem B2262411 : Blo 2261435 2262411 := bstep (se 1 (by rfl) ⟨1696808, by rfl⟩ : syracuseStep 2262411 = 3393617) B3393617
theorem B7635653 : Blo 2261435 7635653 := bbase (se 4 (by rfl) ⟨715842, by rfl⟩ : syracuseStep 7635653 = 1431685) (by norm_num)
theorem B5090435 : Blo 2261435 5090435 := bstep (se 1 (by rfl) ⟨3817826, by rfl⟩ : syracuseStep 5090435 = 7635653) B7635653
theorem B3393623 : Blo 2261435 3393623 := bstep (se 1 (by rfl) ⟨2545217, by rfl⟩ : syracuseStep 3393623 = 5090435) B5090435
theorem B2262415 : Blo 2261435 2262415 := bstep (se 1 (by rfl) ⟨1696811, by rfl⟩ : syracuseStep 2262415 = 3393623) B3393623
theorem B3393629 : Blo 2261435 3393629 := bbase (se 3 (by rfl) ⟨636305, by rfl⟩ : syracuseStep 3393629 = 1272611) (by norm_num)
theorem B2262419 : Blo 2261435 2262419 := bstep (se 1 (by rfl) ⟨1696814, by rfl⟩ : syracuseStep 2262419 = 3393629) B3393629
theorem B5090453 : Blo 2261435 5090453 := bbase (se 6 (by rfl) ⟨119307, by rfl⟩ : syracuseStep 5090453 = 238615) (by norm_num)
theorem B3393635 : Blo 2261435 3393635 := bstep (se 1 (by rfl) ⟨2545226, by rfl⟩ : syracuseStep 3393635 = 5090453) B5090453
theorem B2262423 : Blo 2261435 2262423 := bstep (se 1 (by rfl) ⟨1696817, by rfl⟩ : syracuseStep 2262423 = 3393635) B3393635
theorem B3221309 : Blo 2261435 3221309 := bbase (se 3 (by rfl) ⟨603995, by rfl⟩ : syracuseStep 3221309 = 1207991) (by norm_num)
theorem B8590157 : Blo 2261435 8590157 := bstep (se 3 (by rfl) ⟨1610654, by rfl⟩ : syracuseStep 8590157 = 3221309) B3221309
theorem B5726771 : Blo 2261435 5726771 := bstep (se 1 (by rfl) ⟨4295078, by rfl⟩ : syracuseStep 5726771 = 8590157) B8590157
theorem B3817847 : Blo 2261435 3817847 := bstep (se 1 (by rfl) ⟨2863385, by rfl⟩ : syracuseStep 3817847 = 5726771) B5726771
theorem B2545231 : Blo 2261435 2545231 := bstep (se 1 (by rfl) ⟨1908923, by rfl⟩ : syracuseStep 2545231 = 3817847) B3817847
theorem B3393641 : Blo 2261435 3393641 := bstep (se 2 (by rfl) ⟨1272615, by rfl⟩ : syracuseStep 3393641 = 2545231) B2545231
theorem B2262427 : Blo 2261435 2262427 := bstep (se 1 (by rfl) ⟨1696820, by rfl⟩ : syracuseStep 2262427 = 3393641) B3393641
theorem B3439949 : Blo 2261435 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B9173197 : Blo 2261435 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B12230929 : Blo 2261435 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B16307905 : Blo 2261435 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B21743873 : Blo 2261435 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B14495915 : Blo 2261435 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B9663943 : Blo 2261435 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B12885257 : Blo 2261435 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B8590171 : Blo 2261435 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B11453561 : Blo 2261435 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B7635707 : Blo 2261435 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B5090471 : Blo 2261435 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B3393647 : Blo 2261435 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B2262431 : Blo 2261435 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B3393653 : Blo 2261435 3393653 := bbase (se 5 (by rfl) ⟨159077, by rfl⟩ : syracuseStep 3393653 = 318155) (by norm_num)
theorem B2262435 : Blo 2261435 2262435 := bstep (se 1 (by rfl) ⟨1696826, by rfl⟩ : syracuseStep 2262435 = 3393653) B3393653
theorem B4295101 : Blo 2261435 4295101 := bbase (se 3 (by rfl) ⟨805331, by rfl⟩ : syracuseStep 4295101 = 1610663) (by norm_num)
theorem B5726801 : Blo 2261435 5726801 := bstep (se 2 (by rfl) ⟨2147550, by rfl⟩ : syracuseStep 5726801 = 4295101) B4295101
theorem B3817867 : Blo 2261435 3817867 := bstep (se 1 (by rfl) ⟨2863400, by rfl⟩ : syracuseStep 3817867 = 5726801) B5726801
theorem B5090489 : Blo 2261435 5090489 := bstep (se 2 (by rfl) ⟨1908933, by rfl⟩ : syracuseStep 5090489 = 3817867) B3817867
theorem B3393659 : Blo 2261435 3393659 := bstep (se 1 (by rfl) ⟨2545244, by rfl⟩ : syracuseStep 3393659 = 5090489) B5090489
theorem B2262439 : Blo 2261435 2262439 := bstep (se 1 (by rfl) ⟨1696829, by rfl⟩ : syracuseStep 2262439 = 3393659) B3393659
theorem B2545249 : Blo 2261435 2545249 := bbase (se 2 (by rfl) ⟨954468, by rfl⟩ : syracuseStep 2545249 = 1908937) (by norm_num)
theorem B3393665 : Blo 2261435 3393665 := bstep (se 2 (by rfl) ⟨1272624, by rfl⟩ : syracuseStep 3393665 = 2545249) B2545249
theorem B2262443 : Blo 2261435 2262443 := bstep (se 1 (by rfl) ⟨1696832, by rfl⟩ : syracuseStep 2262443 = 3393665) B3393665
theorem B5726821 : Blo 2261435 5726821 := bbase (se 4 (by rfl) ⟨536889, by rfl⟩ : syracuseStep 5726821 = 1073779) (by norm_num)
theorem B7635761 : Blo 2261435 7635761 := bstep (se 2 (by rfl) ⟨2863410, by rfl⟩ : syracuseStep 7635761 = 5726821) B5726821
theorem B5090507 : Blo 2261435 5090507 := bstep (se 1 (by rfl) ⟨3817880, by rfl⟩ : syracuseStep 5090507 = 7635761) B7635761
theorem B3393671 : Blo 2261435 3393671 := bstep (se 1 (by rfl) ⟨2545253, by rfl⟩ : syracuseStep 3393671 = 5090507) B5090507
theorem B2262447 : Blo 2261435 2262447 := bstep (se 1 (by rfl) ⟨1696835, by rfl⟩ : syracuseStep 2262447 = 3393671) B3393671
theorem B3393677 : Blo 2261435 3393677 := bbase (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) (by norm_num)
theorem B2262451 : Blo 2261435 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B5090525 : Blo 2261435 5090525 := bbase (se 3 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 5090525 = 1908947) (by norm_num)
theorem B3393683 : Blo 2261435 3393683 := bstep (se 1 (by rfl) ⟨2545262, by rfl⟩ : syracuseStep 3393683 = 5090525) B5090525
theorem B2262455 : Blo 2261435 2262455 := bstep (se 1 (by rfl) ⟨1696841, by rfl⟩ : syracuseStep 2262455 = 3393683) B3393683
theorem B3817901 : Blo 2261435 3817901 := bbase (se 3 (by rfl) ⟨715856, by rfl⟩ : syracuseStep 3817901 = 1431713) (by norm_num)
theorem B2545267 : Blo 2261435 2545267 := bstep (se 1 (by rfl) ⟨1908950, by rfl⟩ : syracuseStep 2545267 = 3817901) B3817901
theorem B3393689 : Blo 2261435 3393689 := bstep (se 2 (by rfl) ⟨1272633, by rfl⟩ : syracuseStep 3393689 = 2545267) B2545267
theorem B2262459 : Blo 2261435 2262459 := bstep (se 1 (by rfl) ⟨1696844, by rfl⟩ : syracuseStep 2262459 = 3393689) B3393689
theorem B47073557 : Blo 2261435 47073557 := bbase (se 6 (by rfl) ⟨1103286, by rfl⟩ : syracuseStep 47073557 = 2206573) (by norm_num)
theorem B31382371 : Blo 2261435 31382371 := bstep (se 1 (by rfl) ⟨23536778, by rfl⟩ : syracuseStep 31382371 = 47073557) B47073557
theorem B41843161 : Blo 2261435 41843161 := bstep (se 2 (by rfl) ⟨15691185, by rfl⟩ : syracuseStep 41843161 = 31382371) B31382371
theorem B223163525 : Blo 2261435 223163525 := bstep (se 4 (by rfl) ⟨20921580, by rfl⟩ : syracuseStep 223163525 = 41843161) B41843161
theorem B595102733 : Blo 2261435 595102733 := bstep (se 3 (by rfl) ⟨111581762, by rfl⟩ : syracuseStep 595102733 = 223163525) B223163525
theorem B396735155 : Blo 2261435 396735155 := bstep (se 1 (by rfl) ⟨297551366, by rfl⟩ : syracuseStep 396735155 = 595102733) B595102733
theorem B264490103 : Blo 2261435 264490103 := bstep (se 1 (by rfl) ⟨198367577, by rfl⟩ : syracuseStep 264490103 = 396735155) B396735155
theorem B176326735 : Blo 2261435 176326735 := bstep (se 1 (by rfl) ⟨132245051, by rfl⟩ : syracuseStep 176326735 = 264490103) B264490103
theorem B235102313 : Blo 2261435 235102313 := bstep (se 2 (by rfl) ⟨88163367, by rfl⟩ : syracuseStep 235102313 = 176326735) B176326735
theorem B156734875 : Blo 2261435 156734875 := bstep (se 1 (by rfl) ⟨117551156, by rfl⟩ : syracuseStep 156734875 = 235102313) B235102313
theorem B208979833 : Blo 2261435 208979833 := bstep (se 2 (by rfl) ⟨78367437, by rfl⟩ : syracuseStep 208979833 = 156734875) B156734875
theorem B278639777 : Blo 2261435 278639777 := bstep (se 2 (by rfl) ⟨104489916, by rfl⟩ : syracuseStep 278639777 = 208979833) B208979833
theorem B185759851 : Blo 2261435 185759851 := bstep (se 1 (by rfl) ⟨139319888, by rfl⟩ : syracuseStep 185759851 = 278639777) B278639777
theorem B247679801 : Blo 2261435 247679801 := bstep (se 2 (by rfl) ⟨92879925, by rfl⟩ : syracuseStep 247679801 = 185759851) B185759851
theorem B165119867 : Blo 2261435 165119867 := bstep (se 1 (by rfl) ⟨123839900, by rfl⟩ : syracuseStep 165119867 = 247679801) B247679801
theorem B110079911 : Blo 2261435 110079911 := bstep (se 1 (by rfl) ⟨82559933, by rfl⟩ : syracuseStep 110079911 = 165119867) B165119867
theorem B73386607 : Blo 2261435 73386607 := bstep (se 1 (by rfl) ⟨55039955, by rfl⟩ : syracuseStep 73386607 = 110079911) B110079911
theorem B97848809 : Blo 2261435 97848809 := bstep (se 2 (by rfl) ⟨36693303, by rfl⟩ : syracuseStep 97848809 = 73386607) B73386607
theorem B65232539 : Blo 2261435 65232539 := bstep (se 1 (by rfl) ⟨48924404, by rfl⟩ : syracuseStep 65232539 = 97848809) B97848809
theorem B43488359 : Blo 2261435 43488359 := bstep (se 1 (by rfl) ⟨32616269, by rfl⟩ : syracuseStep 43488359 = 65232539) B65232539
theorem B28992239 : Blo 2261435 28992239 := bstep (se 1 (by rfl) ⟨21744179, by rfl⟩ : syracuseStep 28992239 = 43488359) B43488359
theorem B19328159 : Blo 2261435 19328159 := bstep (se 1 (by rfl) ⟨14496119, by rfl⟩ : syracuseStep 19328159 = 28992239) B28992239
theorem B12885439 : Blo 2261435 12885439 := bstep (se 1 (by rfl) ⟨9664079, by rfl⟩ : syracuseStep 12885439 = 19328159) B19328159
theorem B17180585 : Blo 2261435 17180585 := bstep (se 2 (by rfl) ⟨6442719, by rfl⟩ : syracuseStep 17180585 = 12885439) B12885439
theorem B11453723 : Blo 2261435 11453723 := bstep (se 1 (by rfl) ⟨8590292, by rfl⟩ : syracuseStep 11453723 = 17180585) B17180585
theorem B7635815 : Blo 2261435 7635815 := bstep (se 1 (by rfl) ⟨5726861, by rfl⟩ : syracuseStep 7635815 = 11453723) B11453723
theorem B5090543 : Blo 2261435 5090543 := bstep (se 1 (by rfl) ⟨3817907, by rfl⟩ : syracuseStep 5090543 = 7635815) B7635815
theorem B3393695 : Blo 2261435 3393695 := bstep (se 1 (by rfl) ⟨2545271, by rfl⟩ : syracuseStep 3393695 = 5090543) B5090543
theorem B2262463 : Blo 2261435 2262463 := bstep (se 1 (by rfl) ⟨1696847, by rfl⟩ : syracuseStep 2262463 = 3393695) B3393695
theorem B3393701 : Blo 2261435 3393701 := bbase (se 4 (by rfl) ⟨318159, by rfl⟩ : syracuseStep 3393701 = 636319) (by norm_num)
theorem B2262467 : Blo 2261435 2262467 := bstep (se 1 (by rfl) ⟨1696850, by rfl⟩ : syracuseStep 2262467 = 3393701) B3393701
theorem B2863441 : Blo 2261435 2863441 := bbase (se 2 (by rfl) ⟨1073790, by rfl⟩ : syracuseStep 2863441 = 2147581) (by norm_num)
theorem B3817921 : Blo 2261435 3817921 := bstep (se 2 (by rfl) ⟨1431720, by rfl⟩ : syracuseStep 3817921 = 2863441) B2863441
theorem B5090561 : Blo 2261435 5090561 := bstep (se 2 (by rfl) ⟨1908960, by rfl⟩ : syracuseStep 5090561 = 3817921) B3817921
theorem B3393707 : Blo 2261435 3393707 := bstep (se 1 (by rfl) ⟨2545280, by rfl⟩ : syracuseStep 3393707 = 5090561) B5090561
theorem B2262471 : Blo 2261435 2262471 := bstep (se 1 (by rfl) ⟨1696853, by rfl⟩ : syracuseStep 2262471 = 3393707) B3393707
theorem B2545285 : Blo 2261435 2545285 := bbase (se 4 (by rfl) ⟨238620, by rfl⟩ : syracuseStep 2545285 = 477241) (by norm_num)
theorem B3393713 : Blo 2261435 3393713 := bstep (se 2 (by rfl) ⟨1272642, by rfl⟩ : syracuseStep 3393713 = 2545285) B2545285
theorem B2262475 : Blo 2261435 2262475 := bstep (se 1 (by rfl) ⟨1696856, by rfl⟩ : syracuseStep 2262475 = 3393713) B3393713
theorem B5436085 : Blo 2261435 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B7248113 : Blo 2261435 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B4832075 : Blo 2261435 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B3221383 : Blo 2261435 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B4295177 : Blo 2261435 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B2863451 : Blo 2261435 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B7635869 : Blo 2261435 7635869 := bstep (se 3 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 7635869 = 2863451) B2863451
theorem B5090579 : Blo 2261435 5090579 := bstep (se 1 (by rfl) ⟨3817934, by rfl⟩ : syracuseStep 5090579 = 7635869) B7635869
theorem B3393719 : Blo 2261435 3393719 := bstep (se 1 (by rfl) ⟨2545289, by rfl⟩ : syracuseStep 3393719 = 5090579) B5090579
theorem B2262479 : Blo 2261435 2262479 := bstep (se 1 (by rfl) ⟨1696859, by rfl⟩ : syracuseStep 2262479 = 3393719) B3393719
theorem B3393725 : Blo 2261435 3393725 := bbase (se 3 (by rfl) ⟨636323, by rfl⟩ : syracuseStep 3393725 = 1272647) (by norm_num)
theorem B2262483 : Blo 2261435 2262483 := bstep (se 1 (by rfl) ⟨1696862, by rfl⟩ : syracuseStep 2262483 = 3393725) B3393725
theorem B5090597 : Blo 2261435 5090597 := bbase (se 4 (by rfl) ⟨477243, by rfl⟩ : syracuseStep 5090597 = 954487) (by norm_num)
theorem B3393731 : Blo 2261435 3393731 := bstep (se 1 (by rfl) ⟨2545298, by rfl⟩ : syracuseStep 3393731 = 5090597) B5090597
theorem B2262487 : Blo 2261435 2262487 := bstep (se 1 (by rfl) ⟨1696865, by rfl⟩ : syracuseStep 2262487 = 3393731) B3393731
theorem B5726933 : Blo 2261435 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B3817955 : Blo 2261435 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B2545303 : Blo 2261435 2545303 := bstep (se 1 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 2545303 = 3817955) B3817955
theorem B3393737 : Blo 2261435 3393737 := bstep (se 2 (by rfl) ⟨1272651, by rfl⟩ : syracuseStep 3393737 = 2545303) B2545303
theorem B2262491 : Blo 2261435 2262491 := bstep (se 1 (by rfl) ⟨1696868, by rfl⟩ : syracuseStep 2262491 = 3393737) B3393737
theorem B10872245 : Blo 2261435 10872245 := bbase (se 5 (by rfl) ⟨509636, by rfl⟩ : syracuseStep 10872245 = 1019273) (by norm_num)
theorem B7248163 : Blo 2261435 7248163 := bstep (se 1 (by rfl) ⟨5436122, by rfl⟩ : syracuseStep 7248163 = 10872245) B10872245
theorem B9664217 : Blo 2261435 9664217 := bstep (se 2 (by rfl) ⟨3624081, by rfl⟩ : syracuseStep 9664217 = 7248163) B7248163
theorem B6442811 : Blo 2261435 6442811 := bstep (se 1 (by rfl) ⟨4832108, by rfl⟩ : syracuseStep 6442811 = 9664217) B9664217
theorem B4295207 : Blo 2261435 4295207 := bstep (se 1 (by rfl) ⟨3221405, by rfl⟩ : syracuseStep 4295207 = 6442811) B6442811
theorem B11453885 : Blo 2261435 11453885 := bstep (se 3 (by rfl) ⟨2147603, by rfl⟩ : syracuseStep 11453885 = 4295207) B4295207
theorem B7635923 : Blo 2261435 7635923 := bstep (se 1 (by rfl) ⟨5726942, by rfl⟩ : syracuseStep 7635923 = 11453885) B11453885
theorem B5090615 : Blo 2261435 5090615 := bstep (se 1 (by rfl) ⟨3817961, by rfl⟩ : syracuseStep 5090615 = 7635923) B7635923
theorem B3393743 : Blo 2261435 3393743 := bstep (se 1 (by rfl) ⟨2545307, by rfl⟩ : syracuseStep 3393743 = 5090615) B5090615
theorem B2262495 : Blo 2261435 2262495 := bstep (se 1 (by rfl) ⟨1696871, by rfl⟩ : syracuseStep 2262495 = 3393743) B3393743
theorem B3393749 : Blo 2261435 3393749 := bbase (se 7 (by rfl) ⟨39770, by rfl⟩ : syracuseStep 3393749 = 79541) (by norm_num)
theorem B2262499 : Blo 2261435 2262499 := bstep (se 1 (by rfl) ⟨1696874, by rfl⟩ : syracuseStep 2262499 = 3393749) B3393749
theorem B3723661 : Blo 2261435 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B19859525 : Blo 2261435 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B13239683 : Blo 2261435 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B8826455 : Blo 2261435 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B23537213 : Blo 2261435 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B15691475 : Blo 2261435 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B10460983 : Blo 2261435 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B13947977 : Blo 2261435 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B9298651 : Blo 2261435 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B12398201 : Blo 2261435 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B8265467 : Blo 2261435 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B5510311 : Blo 2261435 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B117553301 : Blo 2261435 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B78368867 : Blo 2261435 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B52245911 : Blo 2261435 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B34830607 : Blo 2261435 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B46440809 : Blo 2261435 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B30960539 : Blo 2261435 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B20640359 : Blo 2261435 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B13760239 : Blo 2261435 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B18346985 : Blo 2261435 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B12231323 : Blo 2261435 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B8154215 : Blo 2261435 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B5436143 : Blo 2261435 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B3624095 : Blo 2261435 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B2416063 : Blo 2261435 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B3221417 : Blo 2261435 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B8590445 : Blo 2261435 8590445 := bstep (se 3 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 8590445 = 3221417) B3221417
theorem B5726963 : Blo 2261435 5726963 := bstep (se 1 (by rfl) ⟨4295222, by rfl⟩ : syracuseStep 5726963 = 8590445) B8590445
theorem B3817975 : Blo 2261435 3817975 := bstep (se 1 (by rfl) ⟨2863481, by rfl⟩ : syracuseStep 3817975 = 5726963) B5726963
theorem B5090633 : Blo 2261435 5090633 := bstep (se 2 (by rfl) ⟨1908987, by rfl⟩ : syracuseStep 5090633 = 3817975) B3817975
theorem B3393755 : Blo 2261435 3393755 := bstep (se 1 (by rfl) ⟨2545316, by rfl⟩ : syracuseStep 3393755 = 5090633) B5090633
theorem B2262503 : Blo 2261435 2262503 := bstep (se 1 (by rfl) ⟨1696877, by rfl⟩ : syracuseStep 2262503 = 3393755) B3393755
theorem B2545321 : Blo 2261435 2545321 := bbase (se 2 (by rfl) ⟨954495, by rfl⟩ : syracuseStep 2545321 = 1908991) (by norm_num)
theorem B3393761 : Blo 2261435 3393761 := bstep (se 2 (by rfl) ⟨1272660, by rfl⟩ : syracuseStep 3393761 = 2545321) B2545321
theorem B2262507 : Blo 2261435 2262507 := bstep (se 1 (by rfl) ⟨1696880, by rfl⟩ : syracuseStep 2262507 = 3393761) B3393761
theorem B2293381 : Blo 2261435 2293381 := bbase (se 4 (by rfl) ⟨215004, by rfl⟩ : syracuseStep 2293381 = 430009) (by norm_num)
theorem B3057841 : Blo 2261435 3057841 := bstep (se 2 (by rfl) ⟨1146690, by rfl⟩ : syracuseStep 3057841 = 2293381) B2293381
theorem B4077121 : Blo 2261435 4077121 := bstep (se 2 (by rfl) ⟨1528920, by rfl⟩ : syracuseStep 4077121 = 3057841) B3057841
theorem B5436161 : Blo 2261435 5436161 := bstep (se 2 (by rfl) ⟨2038560, by rfl⟩ : syracuseStep 5436161 = 4077121) B4077121
theorem B3624107 : Blo 2261435 3624107 := bstep (se 1 (by rfl) ⟨2718080, by rfl⟩ : syracuseStep 3624107 = 5436161) B5436161
theorem B9664285 : Blo 2261435 9664285 := bstep (se 3 (by rfl) ⟨1812053, by rfl⟩ : syracuseStep 9664285 = 3624107) B3624107
theorem B12885713 : Blo 2261435 12885713 := bstep (se 2 (by rfl) ⟨4832142, by rfl⟩ : syracuseStep 12885713 = 9664285) B9664285
theorem B8590475 : Blo 2261435 8590475 := bstep (se 1 (by rfl) ⟨6442856, by rfl⟩ : syracuseStep 8590475 = 12885713) B12885713
theorem B5726983 : Blo 2261435 5726983 := bstep (se 1 (by rfl) ⟨4295237, by rfl⟩ : syracuseStep 5726983 = 8590475) B8590475
theorem B7635977 : Blo 2261435 7635977 := bstep (se 2 (by rfl) ⟨2863491, by rfl⟩ : syracuseStep 7635977 = 5726983) B5726983
theorem B5090651 : Blo 2261435 5090651 := bstep (se 1 (by rfl) ⟨3817988, by rfl⟩ : syracuseStep 5090651 = 7635977) B7635977
theorem B3393767 : Blo 2261435 3393767 := bstep (se 1 (by rfl) ⟨2545325, by rfl⟩ : syracuseStep 3393767 = 5090651) B5090651
theorem B2262511 : Blo 2261435 2262511 := bstep (se 1 (by rfl) ⟨1696883, by rfl⟩ : syracuseStep 2262511 = 3393767) B3393767
theorem B3393773 : Blo 2261435 3393773 := bbase (se 3 (by rfl) ⟨636332, by rfl⟩ : syracuseStep 3393773 = 1272665) (by norm_num)
theorem B2262515 : Blo 2261435 2262515 := bstep (se 1 (by rfl) ⟨1696886, by rfl⟩ : syracuseStep 2262515 = 3393773) B3393773
theorem B5090669 : Blo 2261435 5090669 := bbase (se 3 (by rfl) ⟨954500, by rfl⟩ : syracuseStep 5090669 = 1909001) (by norm_num)
theorem B3393779 : Blo 2261435 3393779 := bstep (se 1 (by rfl) ⟨2545334, by rfl⟩ : syracuseStep 3393779 = 5090669) B5090669
theorem B2262519 : Blo 2261435 2262519 := bstep (se 1 (by rfl) ⟨1696889, by rfl⟩ : syracuseStep 2262519 = 3393779) B3393779
theorem B4295261 : Blo 2261435 4295261 := bbase (se 3 (by rfl) ⟨805361, by rfl⟩ : syracuseStep 4295261 = 1610723) (by norm_num)
theorem B2863507 : Blo 2261435 2863507 := bstep (se 1 (by rfl) ⟨2147630, by rfl⟩ : syracuseStep 2863507 = 4295261) B4295261
theorem B3818009 : Blo 2261435 3818009 := bstep (se 2 (by rfl) ⟨1431753, by rfl⟩ : syracuseStep 3818009 = 2863507) B2863507
theorem B2545339 : Blo 2261435 2545339 := bstep (se 1 (by rfl) ⟨1909004, by rfl⟩ : syracuseStep 2545339 = 3818009) B3818009
theorem B3393785 : Blo 2261435 3393785 := bstep (se 2 (by rfl) ⟨1272669, by rfl⟩ : syracuseStep 3393785 = 2545339) B2545339
theorem B2262523 : Blo 2261435 2262523 := bstep (se 1 (by rfl) ⟨1696892, by rfl⟩ : syracuseStep 2262523 = 3393785) B3393785
theorem B4077149 : Blo 2261435 4077149 := bbase (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) (by norm_num)
theorem B10872397 : Blo 2261435 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B57986117 : Blo 2261435 57986117 := bstep (se 4 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 57986117 = 10872397) B10872397
theorem B38657411 : Blo 2261435 38657411 := bstep (se 1 (by rfl) ⟨28993058, by rfl⟩ : syracuseStep 38657411 = 57986117) B57986117
theorem B25771607 : Blo 2261435 25771607 := bstep (se 1 (by rfl) ⟨19328705, by rfl⟩ : syracuseStep 25771607 = 38657411) B38657411
theorem B17181071 : Blo 2261435 17181071 := bstep (se 1 (by rfl) ⟨12885803, by rfl⟩ : syracuseStep 17181071 = 25771607) B25771607
theorem B11454047 : Blo 2261435 11454047 := bstep (se 1 (by rfl) ⟨8590535, by rfl⟩ : syracuseStep 11454047 = 17181071) B17181071
theorem B7636031 : Blo 2261435 7636031 := bstep (se 1 (by rfl) ⟨5727023, by rfl⟩ : syracuseStep 7636031 = 11454047) B11454047
theorem B5090687 : Blo 2261435 5090687 := bstep (se 1 (by rfl) ⟨3818015, by rfl⟩ : syracuseStep 5090687 = 7636031) B7636031
theorem B3393791 : Blo 2261435 3393791 := bstep (se 1 (by rfl) ⟨2545343, by rfl⟩ : syracuseStep 3393791 = 5090687) B5090687
theorem B2262527 : Blo 2261435 2262527 := bstep (se 1 (by rfl) ⟨1696895, by rfl⟩ : syracuseStep 2262527 = 3393791) B3393791
theorem B3393797 : Blo 2261435 3393797 := bbase (se 4 (by rfl) ⟨318168, by rfl⟩ : syracuseStep 3393797 = 636337) (by norm_num)
theorem B2262531 : Blo 2261435 2262531 := bstep (se 1 (by rfl) ⟨1696898, by rfl⟩ : syracuseStep 2262531 = 3393797) B3393797
theorem B3818029 : Blo 2261435 3818029 := bbase (se 3 (by rfl) ⟨715880, by rfl⟩ : syracuseStep 3818029 = 1431761) (by norm_num)
theorem B5090705 : Blo 2261435 5090705 := bstep (se 2 (by rfl) ⟨1909014, by rfl⟩ : syracuseStep 5090705 = 3818029) B3818029
theorem B3393803 : Blo 2261435 3393803 := bstep (se 1 (by rfl) ⟨2545352, by rfl⟩ : syracuseStep 3393803 = 5090705) B5090705
theorem B2262535 : Blo 2261435 2262535 := bstep (se 1 (by rfl) ⟨1696901, by rfl⟩ : syracuseStep 2262535 = 3393803) B3393803
theorem B2545357 : Blo 2261435 2545357 := bbase (se 3 (by rfl) ⟨477254, by rfl⟩ : syracuseStep 2545357 = 954509) (by norm_num)
theorem B3393809 : Blo 2261435 3393809 := bstep (se 2 (by rfl) ⟨1272678, by rfl⟩ : syracuseStep 3393809 = 2545357) B2545357
theorem B2262539 : Blo 2261435 2262539 := bstep (se 1 (by rfl) ⟨1696904, by rfl⟩ : syracuseStep 2262539 = 3393809) B3393809
theorem B7636085 : Blo 2261435 7636085 := bbase (se 5 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 7636085 = 715883) (by norm_num)
theorem B5090723 : Blo 2261435 5090723 := bstep (se 1 (by rfl) ⟨3818042, by rfl⟩ : syracuseStep 5090723 = 7636085) B7636085
theorem B3393815 : Blo 2261435 3393815 := bstep (se 1 (by rfl) ⟨2545361, by rfl⟩ : syracuseStep 3393815 = 5090723) B5090723
theorem B2262543 : Blo 2261435 2262543 := bstep (se 1 (by rfl) ⟨1696907, by rfl⟩ : syracuseStep 2262543 = 3393815) B3393815
theorem B3393821 : Blo 2261435 3393821 := bbase (se 3 (by rfl) ⟨636341, by rfl⟩ : syracuseStep 3393821 = 1272683) (by norm_num)
theorem B2262547 : Blo 2261435 2262547 := bstep (se 1 (by rfl) ⟨1696910, by rfl⟩ : syracuseStep 2262547 = 3393821) B3393821
theorem B5090741 : Blo 2261435 5090741 := bbase (se 5 (by rfl) ⟨238628, by rfl⟩ : syracuseStep 5090741 = 477257) (by norm_num)
theorem B3393827 : Blo 2261435 3393827 := bstep (se 1 (by rfl) ⟨2545370, by rfl⟩ : syracuseStep 3393827 = 5090741) B5090741
theorem B2262551 : Blo 2261435 2262551 := bstep (se 1 (by rfl) ⟨1696913, by rfl⟩ : syracuseStep 2262551 = 3393827) B3393827
theorem B4832237 : Blo 2261435 4832237 := bbase (se 3 (by rfl) ⟨906044, by rfl⟩ : syracuseStep 4832237 = 1812089) (by norm_num)
theorem B12885965 : Blo 2261435 12885965 := bstep (se 3 (by rfl) ⟨2416118, by rfl⟩ : syracuseStep 12885965 = 4832237) B4832237
theorem B8590643 : Blo 2261435 8590643 := bstep (se 1 (by rfl) ⟨6442982, by rfl⟩ : syracuseStep 8590643 = 12885965) B12885965
theorem B5727095 : Blo 2261435 5727095 := bstep (se 1 (by rfl) ⟨4295321, by rfl⟩ : syracuseStep 5727095 = 8590643) B8590643
theorem B3818063 : Blo 2261435 3818063 := bstep (se 1 (by rfl) ⟨2863547, by rfl⟩ : syracuseStep 3818063 = 5727095) B5727095
theorem B2545375 : Blo 2261435 2545375 := bstep (se 1 (by rfl) ⟨1909031, by rfl⟩ : syracuseStep 2545375 = 3818063) B3818063
theorem B3393833 : Blo 2261435 3393833 := bstep (se 2 (by rfl) ⟨1272687, by rfl⟩ : syracuseStep 3393833 = 2545375) B2545375
theorem B2262555 : Blo 2261435 2262555 := bstep (se 1 (by rfl) ⟨1696916, by rfl⟩ : syracuseStep 2262555 = 3393833) B3393833
theorem B4832245 : Blo 2261435 4832245 := bbase (se 5 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 4832245 = 453023) (by norm_num)
theorem B6442993 : Blo 2261435 6442993 := bstep (se 2 (by rfl) ⟨2416122, by rfl⟩ : syracuseStep 6442993 = 4832245) B4832245
theorem B8590657 : Blo 2261435 8590657 := bstep (se 2 (by rfl) ⟨3221496, by rfl⟩ : syracuseStep 8590657 = 6442993) B6442993
theorem B11454209 : Blo 2261435 11454209 := bstep (se 2 (by rfl) ⟨4295328, by rfl⟩ : syracuseStep 11454209 = 8590657) B8590657
theorem B7636139 : Blo 2261435 7636139 := bstep (se 1 (by rfl) ⟨5727104, by rfl⟩ : syracuseStep 7636139 = 11454209) B11454209
theorem B5090759 : Blo 2261435 5090759 := bstep (se 1 (by rfl) ⟨3818069, by rfl⟩ : syracuseStep 5090759 = 7636139) B7636139
theorem B3393839 : Blo 2261435 3393839 := bstep (se 1 (by rfl) ⟨2545379, by rfl⟩ : syracuseStep 3393839 = 5090759) B5090759
theorem B2262559 : Blo 2261435 2262559 := bstep (se 1 (by rfl) ⟨1696919, by rfl⟩ : syracuseStep 2262559 = 3393839) B3393839
theorem B3393845 : Blo 2261435 3393845 := bbase (se 5 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 3393845 = 318173) (by norm_num)
theorem B2262563 : Blo 2261435 2262563 := bstep (se 1 (by rfl) ⟨1696922, by rfl⟩ : syracuseStep 2262563 = 3393845) B3393845
theorem B5727125 : Blo 2261435 5727125 := bbase (se 6 (by rfl) ⟨134229, by rfl⟩ : syracuseStep 5727125 = 268459) (by norm_num)
theorem B3818083 : Blo 2261435 3818083 := bstep (se 1 (by rfl) ⟨2863562, by rfl⟩ : syracuseStep 3818083 = 5727125) B5727125
theorem B5090777 : Blo 2261435 5090777 := bstep (se 2 (by rfl) ⟨1909041, by rfl⟩ : syracuseStep 5090777 = 3818083) B3818083
theorem B3393851 : Blo 2261435 3393851 := bstep (se 1 (by rfl) ⟨2545388, by rfl⟩ : syracuseStep 3393851 = 5090777) B5090777
theorem B2262567 : Blo 2261435 2262567 := bstep (se 1 (by rfl) ⟨1696925, by rfl⟩ : syracuseStep 2262567 = 3393851) B3393851
theorem B2545393 : Blo 2261435 2545393 := bbase (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) (by norm_num)
theorem B3393857 : Blo 2261435 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B2262571 : Blo 2261435 2262571 := bstep (se 1 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 2262571 = 3393857) B3393857
theorem B15480757 : Blo 2261435 15480757 := bbase (se 5 (by rfl) ⟨725660, by rfl⟩ : syracuseStep 15480757 = 1451321) (by norm_num)
theorem B20641009 : Blo 2261435 20641009 := bstep (se 2 (by rfl) ⟨7740378, by rfl⟩ : syracuseStep 20641009 = 15480757) B15480757
theorem B27521345 : Blo 2261435 27521345 := bstep (se 2 (by rfl) ⟨10320504, by rfl⟩ : syracuseStep 27521345 = 20641009) B20641009
theorem B18347563 : Blo 2261435 18347563 := bstep (se 1 (by rfl) ⟨13760672, by rfl⟩ : syracuseStep 18347563 = 27521345) B27521345
theorem B24463417 : Blo 2261435 24463417 := bstep (se 2 (by rfl) ⟨9173781, by rfl⟩ : syracuseStep 24463417 = 18347563) B18347563
theorem B32617889 : Blo 2261435 32617889 := bstep (se 2 (by rfl) ⟨12231708, by rfl⟩ : syracuseStep 32617889 = 24463417) B24463417
theorem B21745259 : Blo 2261435 21745259 := bstep (se 1 (by rfl) ⟨16308944, by rfl⟩ : syracuseStep 21745259 = 32617889) B32617889
theorem B14496839 : Blo 2261435 14496839 := bstep (se 1 (by rfl) ⟨10872629, by rfl⟩ : syracuseStep 14496839 = 21745259) B21745259
theorem B9664559 : Blo 2261435 9664559 := bstep (se 1 (by rfl) ⟨7248419, by rfl⟩ : syracuseStep 9664559 = 14496839) B14496839
theorem B6443039 : Blo 2261435 6443039 := bstep (se 1 (by rfl) ⟨4832279, by rfl⟩ : syracuseStep 6443039 = 9664559) B9664559
theorem B4295359 : Blo 2261435 4295359 := bstep (se 1 (by rfl) ⟨3221519, by rfl⟩ : syracuseStep 4295359 = 6443039) B6443039
theorem B5727145 : Blo 2261435 5727145 := bstep (se 2 (by rfl) ⟨2147679, by rfl⟩ : syracuseStep 5727145 = 4295359) B4295359
theorem B7636193 : Blo 2261435 7636193 := bstep (se 2 (by rfl) ⟨2863572, by rfl⟩ : syracuseStep 7636193 = 5727145) B5727145
theorem B5090795 : Blo 2261435 5090795 := bstep (se 1 (by rfl) ⟨3818096, by rfl⟩ : syracuseStep 5090795 = 7636193) B7636193
theorem B3393863 : Blo 2261435 3393863 := bstep (se 1 (by rfl) ⟨2545397, by rfl⟩ : syracuseStep 3393863 = 5090795) B5090795
theorem B2262575 : Blo 2261435 2262575 := bstep (se 1 (by rfl) ⟨1696931, by rfl⟩ : syracuseStep 2262575 = 3393863) B3393863
theorem B3393869 : Blo 2261435 3393869 := bbase (se 3 (by rfl) ⟨636350, by rfl⟩ : syracuseStep 3393869 = 1272701) (by norm_num)
theorem B2262579 : Blo 2261435 2262579 := bstep (se 1 (by rfl) ⟨1696934, by rfl⟩ : syracuseStep 2262579 = 3393869) B3393869
theorem B5090813 : Blo 2261435 5090813 := bbase (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) (by norm_num)
theorem B3393875 : Blo 2261435 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B2262583 : Blo 2261435 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B3818117 : Blo 2261435 3818117 := bbase (se 4 (by rfl) ⟨357948, by rfl⟩ : syracuseStep 3818117 = 715897) (by norm_num)
theorem B2545411 : Blo 2261435 2545411 := bstep (se 1 (by rfl) ⟨1909058, by rfl⟩ : syracuseStep 2545411 = 3818117) B3818117
theorem B3393881 : Blo 2261435 3393881 := bstep (se 2 (by rfl) ⟨1272705, by rfl⟩ : syracuseStep 3393881 = 2545411) B2545411
theorem B2262587 : Blo 2261435 2262587 := bstep (se 1 (by rfl) ⟨1696940, by rfl⟩ : syracuseStep 2262587 = 3393881) B3393881
theorem B17181557 : Blo 2261435 17181557 := bbase (se 5 (by rfl) ⟨805385, by rfl⟩ : syracuseStep 17181557 = 1610771) (by norm_num)
theorem B11454371 : Blo 2261435 11454371 := bstep (se 1 (by rfl) ⟨8590778, by rfl⟩ : syracuseStep 11454371 = 17181557) B17181557
theorem B7636247 : Blo 2261435 7636247 := bstep (se 1 (by rfl) ⟨5727185, by rfl⟩ : syracuseStep 7636247 = 11454371) B11454371
theorem B5090831 : Blo 2261435 5090831 := bstep (se 1 (by rfl) ⟨3818123, by rfl⟩ : syracuseStep 5090831 = 7636247) B7636247
theorem B3393887 : Blo 2261435 3393887 := bstep (se 1 (by rfl) ⟨2545415, by rfl⟩ : syracuseStep 3393887 = 5090831) B5090831
theorem B2262591 : Blo 2261435 2262591 := bstep (se 1 (by rfl) ⟨1696943, by rfl⟩ : syracuseStep 2262591 = 3393887) B3393887
theorem B3393893 : Blo 2261435 3393893 := bbase (se 4 (by rfl) ⟨318177, by rfl⟩ : syracuseStep 3393893 = 636355) (by norm_num)
theorem B2262595 : Blo 2261435 2262595 := bstep (se 1 (by rfl) ⟨1696946, by rfl⟩ : syracuseStep 2262595 = 3393893) B3393893
theorem B4295405 : Blo 2261435 4295405 := bbase (se 3 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 4295405 = 1610777) (by norm_num)
theorem B2863603 : Blo 2261435 2863603 := bstep (se 1 (by rfl) ⟨2147702, by rfl⟩ : syracuseStep 2863603 = 4295405) B4295405
theorem B3818137 : Blo 2261435 3818137 := bstep (se 2 (by rfl) ⟨1431801, by rfl⟩ : syracuseStep 3818137 = 2863603) B2863603
theorem B5090849 : Blo 2261435 5090849 := bstep (se 2 (by rfl) ⟨1909068, by rfl⟩ : syracuseStep 5090849 = 3818137) B3818137
theorem B3393899 : Blo 2261435 3393899 := bstep (se 1 (by rfl) ⟨2545424, by rfl⟩ : syracuseStep 3393899 = 5090849) B5090849
theorem B2262599 : Blo 2261435 2262599 := bstep (se 1 (by rfl) ⟨1696949, by rfl⟩ : syracuseStep 2262599 = 3393899) B3393899
theorem B2545429 : Blo 2261435 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B3393905 : Blo 2261435 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B2262603 : Blo 2261435 2262603 := bstep (se 1 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 2262603 = 3393905) B3393905
theorem B2863613 : Blo 2261435 2863613 := bbase (se 3 (by rfl) ⟨536927, by rfl⟩ : syracuseStep 2863613 = 1073855) (by norm_num)
theorem B7636301 : Blo 2261435 7636301 := bstep (se 3 (by rfl) ⟨1431806, by rfl⟩ : syracuseStep 7636301 = 2863613) B2863613
theorem B5090867 : Blo 2261435 5090867 := bstep (se 1 (by rfl) ⟨3818150, by rfl⟩ : syracuseStep 5090867 = 7636301) B7636301
theorem B3393911 : Blo 2261435 3393911 := bstep (se 1 (by rfl) ⟨2545433, by rfl⟩ : syracuseStep 3393911 = 5090867) B5090867
theorem B2262607 : Blo 2261435 2262607 := bstep (se 1 (by rfl) ⟨1696955, by rfl⟩ : syracuseStep 2262607 = 3393911) B3393911
theorem B3393917 : Blo 2261435 3393917 := bbase (se 3 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 3393917 = 1272719) (by norm_num)
theorem B2262611 : Blo 2261435 2262611 := bstep (se 1 (by rfl) ⟨1696958, by rfl⟩ : syracuseStep 2262611 = 3393917) B3393917
theorem B5090885 : Blo 2261435 5090885 := bbase (se 4 (by rfl) ⟨477270, by rfl⟩ : syracuseStep 5090885 = 954541) (by norm_num)
theorem B3393923 : Blo 2261435 3393923 := bstep (se 1 (by rfl) ⟨2545442, by rfl⟩ : syracuseStep 3393923 = 5090885) B5090885
theorem B2262615 : Blo 2261435 2262615 := bstep (se 1 (by rfl) ⟨1696961, by rfl⟩ : syracuseStep 2262615 = 3393923) B3393923
theorem B4077317 : Blo 2261435 4077317 := bbase (se 4 (by rfl) ⟨382248, by rfl⟩ : syracuseStep 4077317 = 764497) (by norm_num)
theorem B2718211 : Blo 2261435 2718211 := bstep (se 1 (by rfl) ⟨2038658, by rfl⟩ : syracuseStep 2718211 = 4077317) B4077317
theorem B3624281 : Blo 2261435 3624281 := bstep (se 2 (by rfl) ⟨1359105, by rfl⟩ : syracuseStep 3624281 = 2718211) B2718211
theorem B2416187 : Blo 2261435 2416187 := bstep (se 1 (by rfl) ⟨1812140, by rfl⟩ : syracuseStep 2416187 = 3624281) B3624281
theorem B6443165 : Blo 2261435 6443165 := bstep (se 3 (by rfl) ⟨1208093, by rfl⟩ : syracuseStep 6443165 = 2416187) B2416187
theorem B4295443 : Blo 2261435 4295443 := bstep (se 1 (by rfl) ⟨3221582, by rfl⟩ : syracuseStep 4295443 = 6443165) B6443165
theorem B5727257 : Blo 2261435 5727257 := bstep (se 2 (by rfl) ⟨2147721, by rfl⟩ : syracuseStep 5727257 = 4295443) B4295443
theorem B3818171 : Blo 2261435 3818171 := bstep (se 1 (by rfl) ⟨2863628, by rfl⟩ : syracuseStep 3818171 = 5727257) B5727257
theorem B2545447 : Blo 2261435 2545447 := bstep (se 1 (by rfl) ⟨1909085, by rfl⟩ : syracuseStep 2545447 = 3818171) B3818171
theorem B3393929 : Blo 2261435 3393929 := bstep (se 2 (by rfl) ⟨1272723, by rfl⟩ : syracuseStep 3393929 = 2545447) B2545447
theorem B2262619 : Blo 2261435 2262619 := bstep (se 1 (by rfl) ⟨1696964, by rfl⟩ : syracuseStep 2262619 = 3393929) B3393929
theorem B11454533 : Blo 2261435 11454533 := bbase (se 4 (by rfl) ⟨1073862, by rfl⟩ : syracuseStep 11454533 = 2147725) (by norm_num)
theorem B7636355 : Blo 2261435 7636355 := bstep (se 1 (by rfl) ⟨5727266, by rfl⟩ : syracuseStep 7636355 = 11454533) B11454533
theorem B5090903 : Blo 2261435 5090903 := bstep (se 1 (by rfl) ⟨3818177, by rfl⟩ : syracuseStep 5090903 = 7636355) B7636355
theorem B3393935 : Blo 2261435 3393935 := bstep (se 1 (by rfl) ⟨2545451, by rfl⟩ : syracuseStep 3393935 = 5090903) B5090903
theorem B2262623 : Blo 2261435 2262623 := bstep (se 1 (by rfl) ⟨1696967, by rfl⟩ : syracuseStep 2262623 = 3393935) B3393935
theorem B3393941 : Blo 2261435 3393941 := bbase (se 6 (by rfl) ⟨79545, by rfl⟩ : syracuseStep 3393941 = 159091) (by norm_num)
theorem B2262627 : Blo 2261435 2262627 := bstep (se 1 (by rfl) ⟨1696970, by rfl⟩ : syracuseStep 2262627 = 3393941) B3393941
theorem B4587005 : Blo 2261435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 2261435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 2261435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 2261435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 2261435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 2261435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 2261435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 2261435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 2261435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 2261435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 2261435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 2261435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B2262631 : Blo 2261435 2262631 := bstep (se 1 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 2262631 = 3393947) B3393947
theorem B2545465 : Blo 2261435 2545465 := bbase (se 2 (by rfl) ⟨954549, by rfl⟩ : syracuseStep 2545465 = 1909099) (by norm_num)
theorem B3393953 : Blo 2261435 3393953 := bstep (se 2 (by rfl) ⟨1272732, by rfl⟩ : syracuseStep 3393953 = 2545465) B2545465
theorem B2262635 : Blo 2261435 2262635 := bstep (se 1 (by rfl) ⟨1696976, by rfl⟩ : syracuseStep 2262635 = 3393953) B3393953
theorem B6443221 : Blo 2261435 6443221 := bbase (se 7 (by rfl) ⟨75506, by rfl⟩ : syracuseStep 6443221 = 151013) (by norm_num)
theorem B8590961 : Blo 2261435 8590961 := bstep (se 2 (by rfl) ⟨3221610, by rfl⟩ : syracuseStep 8590961 = 6443221) B6443221
theorem B5727307 : Blo 2261435 5727307 := bstep (se 1 (by rfl) ⟨4295480, by rfl⟩ : syracuseStep 5727307 = 8590961) B8590961
theorem B7636409 : Blo 2261435 7636409 := bstep (se 2 (by rfl) ⟨2863653, by rfl⟩ : syracuseStep 7636409 = 5727307) B5727307
theorem B5090939 : Blo 2261435 5090939 := bstep (se 1 (by rfl) ⟨3818204, by rfl⟩ : syracuseStep 5090939 = 7636409) B7636409
theorem B3393959 : Blo 2261435 3393959 := bstep (se 1 (by rfl) ⟨2545469, by rfl⟩ : syracuseStep 3393959 = 5090939) B5090939
theorem B2262639 : Blo 2261435 2262639 := bstep (se 1 (by rfl) ⟨1696979, by rfl⟩ : syracuseStep 2262639 = 3393959) B3393959
theorem B3393965 : Blo 2261435 3393965 := bbase (se 3 (by rfl) ⟨636368, by rfl⟩ : syracuseStep 3393965 = 1272737) (by norm_num)
theorem B2262643 : Blo 2261435 2262643 := bstep (se 1 (by rfl) ⟨1696982, by rfl⟩ : syracuseStep 2262643 = 3393965) B3393965
theorem B5090957 : Blo 2261435 5090957 := bbase (se 3 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 5090957 = 1909109) (by norm_num)
theorem B3393971 : Blo 2261435 3393971 := bstep (se 1 (by rfl) ⟨2545478, by rfl⟩ : syracuseStep 3393971 = 5090957) B5090957
theorem B2262647 : Blo 2261435 2262647 := bstep (se 1 (by rfl) ⟨1696985, by rfl⟩ : syracuseStep 2262647 = 3393971) B3393971
theorem B2863669 : Blo 2261435 2863669 := bbase (se 5 (by rfl) ⟨134234, by rfl⟩ : syracuseStep 2863669 = 268469) (by norm_num)
theorem B3818225 : Blo 2261435 3818225 := bstep (se 2 (by rfl) ⟨1431834, by rfl⟩ : syracuseStep 3818225 = 2863669) B2863669
theorem B2545483 : Blo 2261435 2545483 := bstep (se 1 (by rfl) ⟨1909112, by rfl⟩ : syracuseStep 2545483 = 3818225) B3818225
theorem B3393977 : Blo 2261435 3393977 := bstep (se 2 (by rfl) ⟨1272741, by rfl⟩ : syracuseStep 3393977 = 2545483) B2545483
theorem B2262651 : Blo 2261435 2262651 := bstep (se 1 (by rfl) ⟨1696988, by rfl⟩ : syracuseStep 2262651 = 3393977) B3393977
theorem B2580217 : Blo 2261435 2580217 := bbase (se 2 (by rfl) ⟨967581, by rfl⟩ : syracuseStep 2580217 = 1935163) (by norm_num)
theorem B13761157 : Blo 2261435 13761157 := bstep (se 4 (by rfl) ⟨1290108, by rfl⟩ : syracuseStep 13761157 = 2580217) B2580217
theorem B18348209 : Blo 2261435 18348209 := bstep (se 2 (by rfl) ⟨6880578, by rfl⟩ : syracuseStep 18348209 = 13761157) B13761157
theorem B12232139 : Blo 2261435 12232139 := bstep (se 1 (by rfl) ⟨9174104, by rfl⟩ : syracuseStep 12232139 = 18348209) B18348209
theorem B32619037 : Blo 2261435 32619037 := bstep (se 3 (by rfl) ⟨6116069, by rfl⟩ : syracuseStep 32619037 = 12232139) B12232139
theorem B43492049 : Blo 2261435 43492049 := bstep (se 2 (by rfl) ⟨16309518, by rfl⟩ : syracuseStep 43492049 = 32619037) B32619037
theorem B28994699 : Blo 2261435 28994699 := bstep (se 1 (by rfl) ⟨21746024, by rfl⟩ : syracuseStep 28994699 = 43492049) B43492049
theorem B19329799 : Blo 2261435 19329799 := bstep (se 1 (by rfl) ⟨14497349, by rfl⟩ : syracuseStep 19329799 = 28994699) B28994699
theorem B25773065 : Blo 2261435 25773065 := bstep (se 2 (by rfl) ⟨9664899, by rfl⟩ : syracuseStep 25773065 = 19329799) B19329799
theorem B17182043 : Blo 2261435 17182043 := bstep (se 1 (by rfl) ⟨12886532, by rfl⟩ : syracuseStep 17182043 = 25773065) B25773065
theorem B11454695 : Blo 2261435 11454695 := bstep (se 1 (by rfl) ⟨8591021, by rfl⟩ : syracuseStep 11454695 = 17182043) B17182043
theorem B7636463 : Blo 2261435 7636463 := bstep (se 1 (by rfl) ⟨5727347, by rfl⟩ : syracuseStep 7636463 = 11454695) B11454695
theorem B5090975 : Blo 2261435 5090975 := bstep (se 1 (by rfl) ⟨3818231, by rfl⟩ : syracuseStep 5090975 = 7636463) B7636463
theorem B3393983 : Blo 2261435 3393983 := bstep (se 1 (by rfl) ⟨2545487, by rfl⟩ : syracuseStep 3393983 = 5090975) B5090975
theorem B2262655 : Blo 2261435 2262655 := bstep (se 1 (by rfl) ⟨1696991, by rfl⟩ : syracuseStep 2262655 = 3393983) B3393983
theorem B3393989 : Blo 2261435 3393989 := bbase (se 4 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 3393989 = 636373) (by norm_num)
theorem B2262659 : Blo 2261435 2262659 := bstep (se 1 (by rfl) ⟨1696994, by rfl⟩ : syracuseStep 2262659 = 3393989) B3393989
theorem B3818245 : Blo 2261435 3818245 := bbase (se 4 (by rfl) ⟨357960, by rfl⟩ : syracuseStep 3818245 = 715921) (by norm_num)
theorem B5090993 : Blo 2261435 5090993 := bstep (se 2 (by rfl) ⟨1909122, by rfl⟩ : syracuseStep 5090993 = 3818245) B3818245
theorem B3393995 : Blo 2261435 3393995 := bstep (se 1 (by rfl) ⟨2545496, by rfl⟩ : syracuseStep 3393995 = 5090993) B5090993
theorem B2262663 : Blo 2261435 2262663 := bstep (se 1 (by rfl) ⟨1696997, by rfl⟩ : syracuseStep 2262663 = 3393995) B3393995
theorem B2545501 : Blo 2261435 2545501 := bbase (se 3 (by rfl) ⟨477281, by rfl⟩ : syracuseStep 2545501 = 954563) (by norm_num)
theorem B3394001 : Blo 2261435 3394001 := bstep (se 2 (by rfl) ⟨1272750, by rfl⟩ : syracuseStep 3394001 = 2545501) B2545501
theorem B2262667 : Blo 2261435 2262667 := bstep (se 1 (by rfl) ⟨1697000, by rfl⟩ : syracuseStep 2262667 = 3394001) B3394001
theorem B7636517 : Blo 2261435 7636517 := bbase (se 4 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 7636517 = 1431847) (by norm_num)
theorem B5091011 : Blo 2261435 5091011 := bstep (se 1 (by rfl) ⟨3818258, by rfl⟩ : syracuseStep 5091011 = 7636517) B7636517
theorem B3394007 : Blo 2261435 3394007 := bstep (se 1 (by rfl) ⟨2545505, by rfl⟩ : syracuseStep 3394007 = 5091011) B5091011
theorem B2262671 : Blo 2261435 2262671 := bstep (se 1 (by rfl) ⟨1697003, by rfl⟩ : syracuseStep 2262671 = 3394007) B3394007
theorem B3394013 : Blo 2261435 3394013 := bbase (se 3 (by rfl) ⟨636377, by rfl⟩ : syracuseStep 3394013 = 1272755) (by norm_num)
theorem B2262675 : Blo 2261435 2262675 := bstep (se 1 (by rfl) ⟨1697006, by rfl⟩ : syracuseStep 2262675 = 3394013) B3394013
theorem B5091029 : Blo 2261435 5091029 := bbase (se 7 (by rfl) ⟨59660, by rfl⟩ : syracuseStep 5091029 = 119321) (by norm_num)
theorem B3394019 : Blo 2261435 3394019 := bstep (se 1 (by rfl) ⟨2545514, by rfl⟩ : syracuseStep 3394019 = 5091029) B5091029
theorem B2262679 : Blo 2261435 2262679 := bstep (se 1 (by rfl) ⟨1697009, by rfl⟩ : syracuseStep 2262679 = 3394019) B3394019
theorem B2516509 : Blo 2261435 2516509 := bbase (se 3 (by rfl) ⟨471845, by rfl⟩ : syracuseStep 2516509 = 943691) (by norm_num)
theorem B3355345 : Blo 2261435 3355345 := bstep (se 2 (by rfl) ⟨1258254, by rfl⟩ : syracuseStep 3355345 = 2516509) B2516509
theorem B17895173 : Blo 2261435 17895173 := bstep (se 4 (by rfl) ⟨1677672, by rfl⟩ : syracuseStep 17895173 = 3355345) B3355345
theorem B47720461 : Blo 2261435 47720461 := bstep (se 3 (by rfl) ⟨8947586, by rfl⟩ : syracuseStep 47720461 = 17895173) B17895173
theorem B63627281 : Blo 2261435 63627281 := bstep (se 2 (by rfl) ⟨23860230, by rfl⟩ : syracuseStep 63627281 = 47720461) B47720461
theorem B42418187 : Blo 2261435 42418187 := bstep (se 1 (by rfl) ⟨31813640, by rfl⟩ : syracuseStep 42418187 = 63627281) B63627281
theorem B28278791 : Blo 2261435 28278791 := bstep (se 1 (by rfl) ⟨21209093, by rfl⟩ : syracuseStep 28278791 = 42418187) B42418187
theorem B18852527 : Blo 2261435 18852527 := bstep (se 1 (by rfl) ⟨14139395, by rfl⟩ : syracuseStep 18852527 = 28278791) B28278791
theorem B50273405 : Blo 2261435 50273405 := bstep (se 3 (by rfl) ⟨9426263, by rfl⟩ : syracuseStep 50273405 = 18852527) B18852527
theorem B33515603 : Blo 2261435 33515603 := bstep (se 1 (by rfl) ⟨25136702, by rfl⟩ : syracuseStep 33515603 = 50273405) B50273405
theorem B22343735 : Blo 2261435 22343735 := bstep (se 1 (by rfl) ⟨16757801, by rfl⟩ : syracuseStep 22343735 = 33515603) B33515603
theorem B59583293 : Blo 2261435 59583293 := bstep (se 3 (by rfl) ⟨11171867, by rfl⟩ : syracuseStep 59583293 = 22343735) B22343735
theorem B39722195 : Blo 2261435 39722195 := bstep (se 1 (by rfl) ⟨29791646, by rfl⟩ : syracuseStep 39722195 = 59583293) B59583293
theorem B105925853 : Blo 2261435 105925853 := bstep (se 3 (by rfl) ⟨19861097, by rfl⟩ : syracuseStep 105925853 = 39722195) B39722195
theorem B282468941 : Blo 2261435 282468941 := bstep (se 3 (by rfl) ⟨52962926, by rfl⟩ : syracuseStep 282468941 = 105925853) B105925853
theorem B188312627 : Blo 2261435 188312627 := bstep (se 1 (by rfl) ⟨141234470, by rfl⟩ : syracuseStep 188312627 = 282468941) B282468941
theorem B125541751 : Blo 2261435 125541751 := bstep (se 1 (by rfl) ⟨94156313, by rfl⟩ : syracuseStep 125541751 = 188312627) B188312627
theorem B167389001 : Blo 2261435 167389001 := bstep (se 2 (by rfl) ⟨62770875, by rfl⟩ : syracuseStep 167389001 = 125541751) B125541751
theorem B111592667 : Blo 2261435 111592667 := bstep (se 1 (by rfl) ⟨83694500, by rfl⟩ : syracuseStep 111592667 = 167389001) B167389001
theorem B74395111 : Blo 2261435 74395111 := bstep (se 1 (by rfl) ⟨55796333, by rfl⟩ : syracuseStep 74395111 = 111592667) B111592667
theorem B99193481 : Blo 2261435 99193481 := bstep (se 2 (by rfl) ⟨37197555, by rfl⟩ : syracuseStep 99193481 = 74395111) B74395111
theorem B66128987 : Blo 2261435 66128987 := bstep (se 1 (by rfl) ⟨49596740, by rfl⟩ : syracuseStep 66128987 = 99193481) B99193481
theorem B44085991 : Blo 2261435 44085991 := bstep (se 1 (by rfl) ⟨33064493, by rfl⟩ : syracuseStep 44085991 = 66128987) B66128987
theorem B58781321 : Blo 2261435 58781321 := bstep (se 2 (by rfl) ⟨22042995, by rfl⟩ : syracuseStep 58781321 = 44085991) B44085991
theorem B39187547 : Blo 2261435 39187547 := bstep (se 1 (by rfl) ⟨29390660, by rfl⟩ : syracuseStep 39187547 = 58781321) B58781321
theorem B26125031 : Blo 2261435 26125031 := bstep (se 1 (by rfl) ⟨19593773, by rfl⟩ : syracuseStep 26125031 = 39187547) B39187547
theorem B69666749 : Blo 2261435 69666749 := bstep (se 3 (by rfl) ⟨13062515, by rfl⟩ : syracuseStep 69666749 = 26125031) B26125031
theorem B46444499 : Blo 2261435 46444499 := bstep (se 1 (by rfl) ⟨34833374, by rfl⟩ : syracuseStep 46444499 = 69666749) B69666749
theorem B30962999 : Blo 2261435 30962999 := bstep (se 1 (by rfl) ⟨23222249, by rfl⟩ : syracuseStep 30962999 = 46444499) B46444499
theorem B20641999 : Blo 2261435 20641999 := bstep (se 1 (by rfl) ⟨15481499, by rfl⟩ : syracuseStep 20641999 = 30962999) B30962999
theorem B27522665 : Blo 2261435 27522665 := bstep (se 2 (by rfl) ⟨10320999, by rfl⟩ : syracuseStep 27522665 = 20641999) B20641999
theorem B18348443 : Blo 2261435 18348443 := bstep (se 1 (by rfl) ⟨13761332, by rfl⟩ : syracuseStep 18348443 = 27522665) B27522665
theorem B12232295 : Blo 2261435 12232295 := bstep (se 1 (by rfl) ⟨9174221, by rfl⟩ : syracuseStep 12232295 = 18348443) B18348443
theorem B8154863 : Blo 2261435 8154863 := bstep (se 1 (by rfl) ⟨6116147, by rfl⟩ : syracuseStep 8154863 = 12232295) B12232295
theorem B5436575 : Blo 2261435 5436575 := bstep (se 1 (by rfl) ⟨4077431, by rfl⟩ : syracuseStep 5436575 = 8154863) B8154863
theorem B3624383 : Blo 2261435 3624383 := bstep (se 1 (by rfl) ⟨2718287, by rfl⟩ : syracuseStep 3624383 = 5436575) B5436575
theorem B9665021 : Blo 2261435 9665021 := bstep (se 3 (by rfl) ⟨1812191, by rfl⟩ : syracuseStep 9665021 = 3624383) B3624383
theorem B6443347 : Blo 2261435 6443347 := bstep (se 1 (by rfl) ⟨4832510, by rfl⟩ : syracuseStep 6443347 = 9665021) B9665021
theorem B8591129 : Blo 2261435 8591129 := bstep (se 2 (by rfl) ⟨3221673, by rfl⟩ : syracuseStep 8591129 = 6443347) B6443347
theorem B5727419 : Blo 2261435 5727419 := bstep (se 1 (by rfl) ⟨4295564, by rfl⟩ : syracuseStep 5727419 = 8591129) B8591129
theorem B3818279 : Blo 2261435 3818279 := bstep (se 1 (by rfl) ⟨2863709, by rfl⟩ : syracuseStep 3818279 = 5727419) B5727419
theorem B2545519 : Blo 2261435 2545519 := bstep (se 1 (by rfl) ⟨1909139, by rfl⟩ : syracuseStep 2545519 = 3818279) B3818279
theorem B3394025 : Blo 2261435 3394025 := bstep (se 2 (by rfl) ⟨1272759, by rfl⟩ : syracuseStep 3394025 = 2545519) B2545519
theorem B2262683 : Blo 2261435 2262683 := bstep (se 1 (by rfl) ⟨1697012, by rfl⟩ : syracuseStep 2262683 = 3394025) B3394025
theorem B8708357 : Blo 2261435 8708357 := bbase (se 4 (by rfl) ⟨816408, by rfl⟩ : syracuseStep 8708357 = 1632817) (by norm_num)
theorem B23222285 : Blo 2261435 23222285 := bstep (se 3 (by rfl) ⟨4354178, by rfl⟩ : syracuseStep 23222285 = 8708357) B8708357
theorem B15481523 : Blo 2261435 15481523 := bstep (se 1 (by rfl) ⟨11611142, by rfl⟩ : syracuseStep 15481523 = 23222285) B23222285
theorem B10321015 : Blo 2261435 10321015 := bstep (se 1 (by rfl) ⟨7740761, by rfl⟩ : syracuseStep 10321015 = 15481523) B15481523
theorem B13761353 : Blo 2261435 13761353 := bstep (se 2 (by rfl) ⟨5160507, by rfl⟩ : syracuseStep 13761353 = 10321015) B10321015
theorem B9174235 : Blo 2261435 9174235 := bstep (se 1 (by rfl) ⟨6880676, by rfl⟩ : syracuseStep 9174235 = 13761353) B13761353
theorem B12232313 : Blo 2261435 12232313 := bstep (se 2 (by rfl) ⟨4587117, by rfl⟩ : syracuseStep 12232313 = 9174235) B9174235
theorem B8154875 : Blo 2261435 8154875 := bstep (se 1 (by rfl) ⟨6116156, by rfl⟩ : syracuseStep 8154875 = 12232313) B12232313
theorem B21746333 : Blo 2261435 21746333 := bstep (se 3 (by rfl) ⟨4077437, by rfl⟩ : syracuseStep 21746333 = 8154875) B8154875
theorem B14497555 : Blo 2261435 14497555 := bstep (se 1 (by rfl) ⟨10873166, by rfl⟩ : syracuseStep 14497555 = 21746333) B21746333
theorem B19330073 : Blo 2261435 19330073 := bstep (se 2 (by rfl) ⟨7248777, by rfl⟩ : syracuseStep 19330073 = 14497555) B14497555
theorem B12886715 : Blo 2261435 12886715 := bstep (se 1 (by rfl) ⟨9665036, by rfl⟩ : syracuseStep 12886715 = 19330073) B19330073
theorem B8591143 : Blo 2261435 8591143 := bstep (se 1 (by rfl) ⟨6443357, by rfl⟩ : syracuseStep 8591143 = 12886715) B12886715
theorem B11454857 : Blo 2261435 11454857 := bstep (se 2 (by rfl) ⟨4295571, by rfl⟩ : syracuseStep 11454857 = 8591143) B8591143
theorem B7636571 : Blo 2261435 7636571 := bstep (se 1 (by rfl) ⟨5727428, by rfl⟩ : syracuseStep 7636571 = 11454857) B11454857
theorem B5091047 : Blo 2261435 5091047 := bstep (se 1 (by rfl) ⟨3818285, by rfl⟩ : syracuseStep 5091047 = 7636571) B7636571
theorem B3394031 : Blo 2261435 3394031 := bstep (se 1 (by rfl) ⟨2545523, by rfl⟩ : syracuseStep 3394031 = 5091047) B5091047
theorem B2262687 : Blo 2261435 2262687 := bstep (se 1 (by rfl) ⟨1697015, by rfl⟩ : syracuseStep 2262687 = 3394031) B3394031
theorem B3394037 : Blo 2261435 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2262691 : Blo 2261435 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B6443381 : Blo 2261435 6443381 := bbase (se 5 (by rfl) ⟨302033, by rfl⟩ : syracuseStep 6443381 = 604067) (by norm_num)
theorem B4295587 : Blo 2261435 4295587 := bstep (se 1 (by rfl) ⟨3221690, by rfl⟩ : syracuseStep 4295587 = 6443381) B6443381
theorem B5727449 : Blo 2261435 5727449 := bstep (se 2 (by rfl) ⟨2147793, by rfl⟩ : syracuseStep 5727449 = 4295587) B4295587
theorem B3818299 : Blo 2261435 3818299 := bstep (se 1 (by rfl) ⟨2863724, by rfl⟩ : syracuseStep 3818299 = 5727449) B5727449
theorem B5091065 : Blo 2261435 5091065 := bstep (se 2 (by rfl) ⟨1909149, by rfl⟩ : syracuseStep 5091065 = 3818299) B3818299
theorem B3394043 : Blo 2261435 3394043 := bstep (se 1 (by rfl) ⟨2545532, by rfl⟩ : syracuseStep 3394043 = 5091065) B5091065
theorem B2262695 : Blo 2261435 2262695 := bstep (se 1 (by rfl) ⟨1697021, by rfl⟩ : syracuseStep 2262695 = 3394043) B3394043
theorem B2545537 : Blo 2261435 2545537 := bbase (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) (by norm_num)
theorem B3394049 : Blo 2261435 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B2262699 : Blo 2261435 2262699 := bstep (se 1 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 2262699 = 3394049) B3394049
theorem B5727469 : Blo 2261435 5727469 := bbase (se 3 (by rfl) ⟨1073900, by rfl⟩ : syracuseStep 5727469 = 2147801) (by norm_num)
theorem B7636625 : Blo 2261435 7636625 := bstep (se 2 (by rfl) ⟨2863734, by rfl⟩ : syracuseStep 7636625 = 5727469) B5727469
theorem B5091083 : Blo 2261435 5091083 := bstep (se 1 (by rfl) ⟨3818312, by rfl⟩ : syracuseStep 5091083 = 7636625) B7636625
theorem B3394055 : Blo 2261435 3394055 := bstep (se 1 (by rfl) ⟨2545541, by rfl⟩ : syracuseStep 3394055 = 5091083) B5091083
theorem B2262703 : Blo 2261435 2262703 := bstep (se 1 (by rfl) ⟨1697027, by rfl⟩ : syracuseStep 2262703 = 3394055) B3394055
theorem B3394061 : Blo 2261435 3394061 := bbase (se 3 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 3394061 = 1272773) (by norm_num)
theorem B2262707 : Blo 2261435 2262707 := bstep (se 1 (by rfl) ⟨1697030, by rfl⟩ : syracuseStep 2262707 = 3394061) B3394061
theorem B5091101 : Blo 2261435 5091101 := bbase (se 3 (by rfl) ⟨954581, by rfl⟩ : syracuseStep 5091101 = 1909163) (by norm_num)
theorem B3394067 : Blo 2261435 3394067 := bstep (se 1 (by rfl) ⟨2545550, by rfl⟩ : syracuseStep 3394067 = 5091101) B5091101
theorem B2262711 : Blo 2261435 2262711 := bstep (se 1 (by rfl) ⟨1697033, by rfl⟩ : syracuseStep 2262711 = 3394067) B3394067
theorem B3818333 : Blo 2261435 3818333 := bbase (se 3 (by rfl) ⟨715937, by rfl⟩ : syracuseStep 3818333 = 1431875) (by norm_num)
theorem B2545555 : Blo 2261435 2545555 := bstep (se 1 (by rfl) ⟨1909166, by rfl⟩ : syracuseStep 2545555 = 3818333) B3818333
theorem B3394073 : Blo 2261435 3394073 := bstep (se 2 (by rfl) ⟨1272777, by rfl⟩ : syracuseStep 3394073 = 2545555) B2545555
theorem B2262715 : Blo 2261435 2262715 := bstep (se 1 (by rfl) ⟨1697036, by rfl⟩ : syracuseStep 2262715 = 3394073) B3394073
theorem B9665173 : Blo 2261435 9665173 := bbase (se 6 (by rfl) ⟨226527, by rfl⟩ : syracuseStep 9665173 = 453055) (by norm_num)
theorem B12886897 : Blo 2261435 12886897 := bstep (se 2 (by rfl) ⟨4832586, by rfl⟩ : syracuseStep 12886897 = 9665173) B9665173
theorem B17182529 : Blo 2261435 17182529 := bstep (se 2 (by rfl) ⟨6443448, by rfl⟩ : syracuseStep 17182529 = 12886897) B12886897
theorem B11455019 : Blo 2261435 11455019 := bstep (se 1 (by rfl) ⟨8591264, by rfl⟩ : syracuseStep 11455019 = 17182529) B17182529
theorem B7636679 : Blo 2261435 7636679 := bstep (se 1 (by rfl) ⟨5727509, by rfl⟩ : syracuseStep 7636679 = 11455019) B11455019
theorem B5091119 : Blo 2261435 5091119 := bstep (se 1 (by rfl) ⟨3818339, by rfl⟩ : syracuseStep 5091119 = 7636679) B7636679
theorem B3394079 : Blo 2261435 3394079 := bstep (se 1 (by rfl) ⟨2545559, by rfl⟩ : syracuseStep 3394079 = 5091119) B5091119
theorem B2262719 : Blo 2261435 2262719 := bstep (se 1 (by rfl) ⟨1697039, by rfl⟩ : syracuseStep 2262719 = 3394079) B3394079
theorem B3394085 : Blo 2261435 3394085 := bbase (se 4 (by rfl) ⟨318195, by rfl⟩ : syracuseStep 3394085 = 636391) (by norm_num)
theorem B2262723 : Blo 2261435 2262723 := bstep (se 1 (by rfl) ⟨1697042, by rfl⟩ : syracuseStep 2262723 = 3394085) B3394085
theorem B2863765 : Blo 2261435 2863765 := bbase (se 6 (by rfl) ⟨67119, by rfl⟩ : syracuseStep 2863765 = 134239) (by norm_num)
theorem B3818353 : Blo 2261435 3818353 := bstep (se 2 (by rfl) ⟨1431882, by rfl⟩ : syracuseStep 3818353 = 2863765) B2863765
theorem B5091137 : Blo 2261435 5091137 := bstep (se 2 (by rfl) ⟨1909176, by rfl⟩ : syracuseStep 5091137 = 3818353) B3818353
theorem B3394091 : Blo 2261435 3394091 := bstep (se 1 (by rfl) ⟨2545568, by rfl⟩ : syracuseStep 3394091 = 5091137) B5091137
theorem B2262727 : Blo 2261435 2262727 := bstep (se 1 (by rfl) ⟨1697045, by rfl⟩ : syracuseStep 2262727 = 3394091) B3394091
theorem B2545573 : Blo 2261435 2545573 := bbase (se 4 (by rfl) ⟨238647, by rfl⟩ : syracuseStep 2545573 = 477295) (by norm_num)
theorem B3394097 : Blo 2261435 3394097 := bstep (se 2 (by rfl) ⟨1272786, by rfl⟩ : syracuseStep 3394097 = 2545573) B2545573
theorem B2262731 : Blo 2261435 2262731 := bstep (se 1 (by rfl) ⟨1697048, by rfl⟩ : syracuseStep 2262731 = 3394097) B3394097
theorem B2615513 : Blo 2261435 2615513 := bbase (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) (by norm_num)
theorem B27898805 : Blo 2261435 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B18599203 : Blo 2261435 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B99195749 : Blo 2261435 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B66130499 : Blo 2261435 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B44086999 : Blo 2261435 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B58782665 : Blo 2261435 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B39188443 : Blo 2261435 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B52251257 : Blo 2261435 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B34834171 : Blo 2261435 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B46445561 : Blo 2261435 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B30963707 : Blo 2261435 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B20642471 : Blo 2261435 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B13761647 : Blo 2261435 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B9174431 : Blo 2261435 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B24465149 : Blo 2261435 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B16310099 : Blo 2261435 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B10873399 : Blo 2261435 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B14497865 : Blo 2261435 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B9665243 : Blo 2261435 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B6443495 : Blo 2261435 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B4295663 : Blo 2261435 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B2863775 : Blo 2261435 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B7636733 : Blo 2261435 7636733 := bstep (se 3 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 7636733 = 2863775) B2863775
theorem B5091155 : Blo 2261435 5091155 := bstep (se 1 (by rfl) ⟨3818366, by rfl⟩ : syracuseStep 5091155 = 7636733) B7636733
theorem B3394103 : Blo 2261435 3394103 := bstep (se 1 (by rfl) ⟨2545577, by rfl⟩ : syracuseStep 3394103 = 5091155) B5091155
theorem B2262735 : Blo 2261435 2262735 := bstep (se 1 (by rfl) ⟨1697051, by rfl⟩ : syracuseStep 2262735 = 3394103) B3394103
theorem B3394109 : Blo 2261435 3394109 := bbase (se 3 (by rfl) ⟨636395, by rfl⟩ : syracuseStep 3394109 = 1272791) (by norm_num)
theorem B2262739 : Blo 2261435 2262739 := bstep (se 1 (by rfl) ⟨1697054, by rfl⟩ : syracuseStep 2262739 = 3394109) B3394109
theorem B5091173 : Blo 2261435 5091173 := bbase (se 4 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 5091173 = 954595) (by norm_num)
theorem B3394115 : Blo 2261435 3394115 := bstep (se 1 (by rfl) ⟨2545586, by rfl⟩ : syracuseStep 3394115 = 5091173) B5091173
theorem B2262743 : Blo 2261435 2262743 := bstep (se 1 (by rfl) ⟨1697057, by rfl⟩ : syracuseStep 2262743 = 3394115) B3394115
theorem B5727581 : Blo 2261435 5727581 := bbase (se 3 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 5727581 = 2147843) (by norm_num)
theorem B3818387 : Blo 2261435 3818387 := bstep (se 1 (by rfl) ⟨2863790, by rfl⟩ : syracuseStep 3818387 = 5727581) B5727581
theorem B2545591 : Blo 2261435 2545591 := bstep (se 1 (by rfl) ⟨1909193, by rfl⟩ : syracuseStep 2545591 = 3818387) B3818387
theorem B3394121 : Blo 2261435 3394121 := bstep (se 2 (by rfl) ⟨1272795, by rfl⟩ : syracuseStep 3394121 = 2545591) B2545591
theorem B2262747 : Blo 2261435 2262747 := bstep (se 1 (by rfl) ⟨1697060, by rfl⟩ : syracuseStep 2262747 = 3394121) B3394121
theorem B4295693 : Blo 2261435 4295693 := bbase (se 3 (by rfl) ⟨805442, by rfl⟩ : syracuseStep 4295693 = 1610885) (by norm_num)
theorem B11455181 : Blo 2261435 11455181 := bstep (se 3 (by rfl) ⟨2147846, by rfl⟩ : syracuseStep 11455181 = 4295693) B4295693
theorem B7636787 : Blo 2261435 7636787 := bstep (se 1 (by rfl) ⟨5727590, by rfl⟩ : syracuseStep 7636787 = 11455181) B11455181
theorem B5091191 : Blo 2261435 5091191 := bstep (se 1 (by rfl) ⟨3818393, by rfl⟩ : syracuseStep 5091191 = 7636787) B7636787
theorem B3394127 : Blo 2261435 3394127 := bstep (se 1 (by rfl) ⟨2545595, by rfl⟩ : syracuseStep 3394127 = 5091191) B5091191
theorem B2262751 : Blo 2261435 2262751 := bstep (se 1 (by rfl) ⟨1697063, by rfl⟩ : syracuseStep 2262751 = 3394127) B3394127
theorem B3394133 : Blo 2261435 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B2262755 : Blo 2261435 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B5436757 : Blo 2261435 5436757 := bbase (se 13 (by rfl) ⟨995, by rfl⟩ : syracuseStep 5436757 = 1991) (by norm_num)
theorem B7249009 : Blo 2261435 7249009 := bstep (se 2 (by rfl) ⟨2718378, by rfl⟩ : syracuseStep 7249009 = 5436757) B5436757
theorem B9665345 : Blo 2261435 9665345 := bstep (se 2 (by rfl) ⟨3624504, by rfl⟩ : syracuseStep 9665345 = 7249009) B7249009
theorem B6443563 : Blo 2261435 6443563 := bstep (se 1 (by rfl) ⟨4832672, by rfl⟩ : syracuseStep 6443563 = 9665345) B9665345
theorem B8591417 : Blo 2261435 8591417 := bstep (se 2 (by rfl) ⟨3221781, by rfl⟩ : syracuseStep 8591417 = 6443563) B6443563
theorem B5727611 : Blo 2261435 5727611 := bstep (se 1 (by rfl) ⟨4295708, by rfl⟩ : syracuseStep 5727611 = 8591417) B8591417
theorem B3818407 : Blo 2261435 3818407 := bstep (se 1 (by rfl) ⟨2863805, by rfl⟩ : syracuseStep 3818407 = 5727611) B5727611
theorem B5091209 : Blo 2261435 5091209 := bstep (se 2 (by rfl) ⟨1909203, by rfl⟩ : syracuseStep 5091209 = 3818407) B3818407
theorem B3394139 : Blo 2261435 3394139 := bstep (se 1 (by rfl) ⟨2545604, by rfl⟩ : syracuseStep 3394139 = 5091209) B5091209
theorem B2262759 : Blo 2261435 2262759 := bstep (se 1 (by rfl) ⟨1697069, by rfl⟩ : syracuseStep 2262759 = 3394139) B3394139
theorem B2545609 : Blo 2261435 2545609 := bbase (se 2 (by rfl) ⟨954603, by rfl⟩ : syracuseStep 2545609 = 1909207) (by norm_num)
theorem B3394145 : Blo 2261435 3394145 := bstep (se 2 (by rfl) ⟨1272804, by rfl⟩ : syracuseStep 3394145 = 2545609) B2545609
theorem B2262763 : Blo 2261435 2262763 := bstep (se 1 (by rfl) ⟨1697072, by rfl⟩ : syracuseStep 2262763 = 3394145) B3394145
theorem B3624517 : Blo 2261435 3624517 := bbase (se 4 (by rfl) ⟨339798, by rfl⟩ : syracuseStep 3624517 = 679597) (by norm_num)
theorem B19330757 : Blo 2261435 19330757 := bstep (se 4 (by rfl) ⟨1812258, by rfl⟩ : syracuseStep 19330757 = 3624517) B3624517
theorem B12887171 : Blo 2261435 12887171 := bstep (se 1 (by rfl) ⟨9665378, by rfl⟩ : syracuseStep 12887171 = 19330757) B19330757
theorem B8591447 : Blo 2261435 8591447 := bstep (se 1 (by rfl) ⟨6443585, by rfl⟩ : syracuseStep 8591447 = 12887171) B12887171
theorem B5727631 : Blo 2261435 5727631 := bstep (se 1 (by rfl) ⟨4295723, by rfl⟩ : syracuseStep 5727631 = 8591447) B8591447
theorem B7636841 : Blo 2261435 7636841 := bstep (se 2 (by rfl) ⟨2863815, by rfl⟩ : syracuseStep 7636841 = 5727631) B5727631
theorem B5091227 : Blo 2261435 5091227 := bstep (se 1 (by rfl) ⟨3818420, by rfl⟩ : syracuseStep 5091227 = 7636841) B7636841
theorem B3394151 : Blo 2261435 3394151 := bstep (se 1 (by rfl) ⟨2545613, by rfl⟩ : syracuseStep 3394151 = 5091227) B5091227
theorem B2262767 : Blo 2261435 2262767 := bstep (se 1 (by rfl) ⟨1697075, by rfl⟩ : syracuseStep 2262767 = 3394151) B3394151
theorem B3394157 : Blo 2261435 3394157 := bbase (se 3 (by rfl) ⟨636404, by rfl⟩ : syracuseStep 3394157 = 1272809) (by norm_num)
theorem B2262771 : Blo 2261435 2262771 := bstep (se 1 (by rfl) ⟨1697078, by rfl⟩ : syracuseStep 2262771 = 3394157) B3394157
theorem B5091245 : Blo 2261435 5091245 := bbase (se 3 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 5091245 = 1909217) (by norm_num)
theorem B3394163 : Blo 2261435 3394163 := bstep (se 1 (by rfl) ⟨2545622, by rfl⟩ : syracuseStep 3394163 = 5091245) B5091245
theorem B2262775 : Blo 2261435 2262775 := bstep (se 1 (by rfl) ⟨1697081, by rfl⟩ : syracuseStep 2262775 = 3394163) B3394163
theorem B6443621 : Blo 2261435 6443621 := bbase (se 4 (by rfl) ⟨604089, by rfl⟩ : syracuseStep 6443621 = 1208179) (by norm_num)
theorem B4295747 : Blo 2261435 4295747 := bstep (se 1 (by rfl) ⟨3221810, by rfl⟩ : syracuseStep 4295747 = 6443621) B6443621
theorem B2863831 : Blo 2261435 2863831 := bstep (se 1 (by rfl) ⟨2147873, by rfl⟩ : syracuseStep 2863831 = 4295747) B4295747
theorem B3818441 : Blo 2261435 3818441 := bstep (se 2 (by rfl) ⟨1431915, by rfl⟩ : syracuseStep 3818441 = 2863831) B2863831
theorem B2545627 : Blo 2261435 2545627 := bstep (se 1 (by rfl) ⟨1909220, by rfl⟩ : syracuseStep 2545627 = 3818441) B3818441
theorem B3394169 : Blo 2261435 3394169 := bstep (se 2 (by rfl) ⟨1272813, by rfl⟩ : syracuseStep 3394169 = 2545627) B2545627
theorem B2262779 : Blo 2261435 2262779 := bstep (se 1 (by rfl) ⟨1697084, by rfl⟩ : syracuseStep 2262779 = 3394169) B3394169
theorem B132263765 : Blo 2261435 132263765 := bbase (se 9 (by rfl) ⟨387491, by rfl⟩ : syracuseStep 132263765 = 774983) (by norm_num)
theorem B88175843 : Blo 2261435 88175843 := bstep (se 1 (by rfl) ⟨66131882, by rfl⟩ : syracuseStep 88175843 = 132263765) B132263765
theorem B58783895 : Blo 2261435 58783895 := bstep (se 1 (by rfl) ⟨44087921, by rfl⟩ : syracuseStep 58783895 = 88175843) B88175843
theorem B39189263 : Blo 2261435 39189263 := bstep (se 1 (by rfl) ⟨29391947, by rfl⟩ : syracuseStep 39189263 = 58783895) B58783895
theorem B104504701 : Blo 2261435 104504701 := bstep (se 3 (by rfl) ⟨19594631, by rfl⟩ : syracuseStep 104504701 = 39189263) B39189263
theorem B139339601 : Blo 2261435 139339601 := bstep (se 2 (by rfl) ⟨52252350, by rfl⟩ : syracuseStep 139339601 = 104504701) B104504701
theorem B92893067 : Blo 2261435 92893067 := bstep (se 1 (by rfl) ⟨69669800, by rfl⟩ : syracuseStep 92893067 = 139339601) B139339601
theorem B61928711 : Blo 2261435 61928711 := bstep (se 1 (by rfl) ⟨46446533, by rfl⟩ : syracuseStep 61928711 = 92893067) B92893067
theorem B41285807 : Blo 2261435 41285807 := bstep (se 1 (by rfl) ⟨30964355, by rfl⟩ : syracuseStep 41285807 = 61928711) B61928711
theorem B27523871 : Blo 2261435 27523871 := bstep (se 1 (by rfl) ⟨20642903, by rfl⟩ : syracuseStep 27523871 = 41285807) B41285807
theorem B18349247 : Blo 2261435 18349247 := bstep (se 1 (by rfl) ⟨13761935, by rfl⟩ : syracuseStep 18349247 = 27523871) B27523871
theorem B12232831 : Blo 2261435 12232831 := bstep (se 1 (by rfl) ⟨9174623, by rfl⟩ : syracuseStep 12232831 = 18349247) B18349247
theorem B16310441 : Blo 2261435 16310441 := bstep (se 2 (by rfl) ⟨6116415, by rfl⟩ : syracuseStep 16310441 = 12232831) B12232831
theorem B43494509 : Blo 2261435 43494509 := bstep (se 3 (by rfl) ⟨8155220, by rfl⟩ : syracuseStep 43494509 = 16310441) B16310441
theorem B28996339 : Blo 2261435 28996339 := bstep (se 1 (by rfl) ⟨21747254, by rfl⟩ : syracuseStep 28996339 = 43494509) B43494509
theorem B38661785 : Blo 2261435 38661785 := bstep (se 2 (by rfl) ⟨14498169, by rfl⟩ : syracuseStep 38661785 = 28996339) B28996339
theorem B25774523 : Blo 2261435 25774523 := bstep (se 1 (by rfl) ⟨19330892, by rfl⟩ : syracuseStep 25774523 = 38661785) B38661785
theorem B17183015 : Blo 2261435 17183015 := bstep (se 1 (by rfl) ⟨12887261, by rfl⟩ : syracuseStep 17183015 = 25774523) B25774523
theorem B11455343 : Blo 2261435 11455343 := bstep (se 1 (by rfl) ⟨8591507, by rfl⟩ : syracuseStep 11455343 = 17183015) B17183015
theorem B7636895 : Blo 2261435 7636895 := bstep (se 1 (by rfl) ⟨5727671, by rfl⟩ : syracuseStep 7636895 = 11455343) B11455343
theorem B5091263 : Blo 2261435 5091263 := bstep (se 1 (by rfl) ⟨3818447, by rfl⟩ : syracuseStep 5091263 = 7636895) B7636895
theorem B3394175 : Blo 2261435 3394175 := bstep (se 1 (by rfl) ⟨2545631, by rfl⟩ : syracuseStep 3394175 = 5091263) B5091263
theorem B2262783 : Blo 2261435 2262783 := bstep (se 1 (by rfl) ⟨1697087, by rfl⟩ : syracuseStep 2262783 = 3394175) B3394175
theorem B3394181 : Blo 2261435 3394181 := bbase (se 4 (by rfl) ⟨318204, by rfl⟩ : syracuseStep 3394181 = 636409) (by norm_num)
theorem B2262787 : Blo 2261435 2262787 := bstep (se 1 (by rfl) ⟨1697090, by rfl⟩ : syracuseStep 2262787 = 3394181) B3394181
theorem B3818461 : Blo 2261435 3818461 := bbase (se 3 (by rfl) ⟨715961, by rfl⟩ : syracuseStep 3818461 = 1431923) (by norm_num)
theorem B5091281 : Blo 2261435 5091281 := bstep (se 2 (by rfl) ⟨1909230, by rfl⟩ : syracuseStep 5091281 = 3818461) B3818461
theorem B3394187 : Blo 2261435 3394187 := bstep (se 1 (by rfl) ⟨2545640, by rfl⟩ : syracuseStep 3394187 = 5091281) B5091281
theorem B2262791 : Blo 2261435 2262791 := bstep (se 1 (by rfl) ⟨1697093, by rfl⟩ : syracuseStep 2262791 = 3394187) B3394187
theorem B2545645 : Blo 2261435 2545645 := bbase (se 3 (by rfl) ⟨477308, by rfl⟩ : syracuseStep 2545645 = 954617) (by norm_num)
theorem B3394193 : Blo 2261435 3394193 := bstep (se 2 (by rfl) ⟨1272822, by rfl⟩ : syracuseStep 3394193 = 2545645) B2545645
theorem B2262795 : Blo 2261435 2262795 := bstep (se 1 (by rfl) ⟨1697096, by rfl⟩ : syracuseStep 2262795 = 3394193) B3394193
theorem B7636949 : Blo 2261435 7636949 := bbase (se 7 (by rfl) ⟨89495, by rfl⟩ : syracuseStep 7636949 = 178991) (by norm_num)
theorem B5091299 : Blo 2261435 5091299 := bstep (se 1 (by rfl) ⟨3818474, by rfl⟩ : syracuseStep 5091299 = 7636949) B7636949
theorem B3394199 : Blo 2261435 3394199 := bstep (se 1 (by rfl) ⟨2545649, by rfl⟩ : syracuseStep 3394199 = 5091299) B5091299
theorem B2262799 : Blo 2261435 2262799 := bstep (se 1 (by rfl) ⟨1697099, by rfl⟩ : syracuseStep 2262799 = 3394199) B3394199
theorem B3394205 : Blo 2261435 3394205 := bbase (se 3 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 3394205 = 1272827) (by norm_num)
theorem B2262803 : Blo 2261435 2262803 := bstep (se 1 (by rfl) ⟨1697102, by rfl⟩ : syracuseStep 2262803 = 3394205) B3394205
theorem B5091317 : Blo 2261435 5091317 := bbase (se 5 (by rfl) ⟨238655, by rfl⟩ : syracuseStep 5091317 = 477311) (by norm_num)
theorem B3394211 : Blo 2261435 3394211 := bstep (se 1 (by rfl) ⟨2545658, by rfl⟩ : syracuseStep 3394211 = 5091317) B5091317
theorem B2262807 : Blo 2261435 2262807 := bstep (se 1 (by rfl) ⟨1697105, by rfl⟩ : syracuseStep 2262807 = 3394211) B3394211
theorem B3265813 : Blo 2261435 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B4354417 : Blo 2261435 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B23223557 : Blo 2261435 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B61929485 : Blo 2261435 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B41286323 : Blo 2261435 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B27524215 : Blo 2261435 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B146795813 : Blo 2261435 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B97863875 : Blo 2261435 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B65242583 : Blo 2261435 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B43495055 : Blo 2261435 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B28996703 : Blo 2261435 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B19331135 : Blo 2261435 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B12887423 : Blo 2261435 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B8591615 : Blo 2261435 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B5727743 : Blo 2261435 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B3818495 : Blo 2261435 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B2545663 : Blo 2261435 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B3394217 : Blo 2261435 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B2262811 : Blo 2261435 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B3221861 : Blo 2261435 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B8591629 : Blo 2261435 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B11455505 : Blo 2261435 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B7637003 : Blo 2261435 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B5091335 : Blo 2261435 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B3394223 : Blo 2261435 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B2262815 : Blo 2261435 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B3394229 : Blo 2261435 3394229 := bbase (se 5 (by rfl) ⟨159104, by rfl⟩ : syracuseStep 3394229 = 318209) (by norm_num)
theorem B2262819 : Blo 2261435 2262819 := bstep (se 1 (by rfl) ⟨1697114, by rfl⟩ : syracuseStep 2262819 = 3394229) B3394229
theorem B5727773 : Blo 2261435 5727773 := bbase (se 3 (by rfl) ⟨1073957, by rfl⟩ : syracuseStep 5727773 = 2147915) (by norm_num)
theorem B3818515 : Blo 2261435 3818515 := bstep (se 1 (by rfl) ⟨2863886, by rfl⟩ : syracuseStep 3818515 = 5727773) B5727773
theorem B5091353 : Blo 2261435 5091353 := bstep (se 2 (by rfl) ⟨1909257, by rfl⟩ : syracuseStep 5091353 = 3818515) B3818515
theorem B3394235 : Blo 2261435 3394235 := bstep (se 1 (by rfl) ⟨2545676, by rfl⟩ : syracuseStep 3394235 = 5091353) B5091353
theorem B2262823 : Blo 2261435 2262823 := bstep (se 1 (by rfl) ⟨1697117, by rfl⟩ : syracuseStep 2262823 = 3394235) B3394235
theorem B2545681 : Blo 2261435 2545681 := bbase (se 2 (by rfl) ⟨954630, by rfl⟩ : syracuseStep 2545681 = 1909261) (by norm_num)
theorem B3394241 : Blo 2261435 3394241 := bstep (se 2 (by rfl) ⟨1272840, by rfl⟩ : syracuseStep 3394241 = 2545681) B2545681
theorem B2262827 : Blo 2261435 2262827 := bstep (se 1 (by rfl) ⟨1697120, by rfl⟩ : syracuseStep 2262827 = 3394241) B3394241
theorem B4295845 : Blo 2261435 4295845 := bbase (se 4 (by rfl) ⟨402735, by rfl⟩ : syracuseStep 4295845 = 805471) (by norm_num)
theorem B5727793 : Blo 2261435 5727793 := bstep (se 2 (by rfl) ⟨2147922, by rfl⟩ : syracuseStep 5727793 = 4295845) B4295845
theorem B7637057 : Blo 2261435 7637057 := bstep (se 2 (by rfl) ⟨2863896, by rfl⟩ : syracuseStep 7637057 = 5727793) B5727793
theorem B5091371 : Blo 2261435 5091371 := bstep (se 1 (by rfl) ⟨3818528, by rfl⟩ : syracuseStep 5091371 = 7637057) B7637057
theorem B3394247 : Blo 2261435 3394247 := bstep (se 1 (by rfl) ⟨2545685, by rfl⟩ : syracuseStep 3394247 = 5091371) B5091371
theorem B2262831 : Blo 2261435 2262831 := bstep (se 1 (by rfl) ⟨1697123, by rfl⟩ : syracuseStep 2262831 = 3394247) B3394247
theorem B3394253 : Blo 2261435 3394253 := bbase (se 3 (by rfl) ⟨636422, by rfl⟩ : syracuseStep 3394253 = 1272845) (by norm_num)
theorem B2262835 : Blo 2261435 2262835 := bstep (se 1 (by rfl) ⟨1697126, by rfl⟩ : syracuseStep 2262835 = 3394253) B3394253
theorem B5091389 : Blo 2261435 5091389 := bbase (se 3 (by rfl) ⟨954635, by rfl⟩ : syracuseStep 5091389 = 1909271) (by norm_num)
theorem B3394259 : Blo 2261435 3394259 := bstep (se 1 (by rfl) ⟨2545694, by rfl⟩ : syracuseStep 3394259 = 5091389) B5091389
theorem B2262839 : Blo 2261435 2262839 := bstep (se 1 (by rfl) ⟨1697129, by rfl⟩ : syracuseStep 2262839 = 3394259) B3394259
theorem B3818549 : Blo 2261435 3818549 := bbase (se 5 (by rfl) ⟨178994, by rfl⟩ : syracuseStep 3818549 = 357989) (by norm_num)
theorem B2545699 : Blo 2261435 2545699 := bstep (se 1 (by rfl) ⟨1909274, by rfl⟩ : syracuseStep 2545699 = 3818549) B3818549
theorem B3394265 : Blo 2261435 3394265 := bstep (se 2 (by rfl) ⟨1272849, by rfl⟩ : syracuseStep 3394265 = 2545699) B2545699
theorem B2262843 : Blo 2261435 2262843 := bstep (se 1 (by rfl) ⟨1697132, by rfl⟩ : syracuseStep 2262843 = 3394265) B3394265
theorem B6443813 : Blo 2261435 6443813 := bbase (se 4 (by rfl) ⟨604107, by rfl⟩ : syracuseStep 6443813 = 1208215) (by norm_num)
theorem B17183501 : Blo 2261435 17183501 := bstep (se 3 (by rfl) ⟨3221906, by rfl⟩ : syracuseStep 17183501 = 6443813) B6443813
theorem B11455667 : Blo 2261435 11455667 := bstep (se 1 (by rfl) ⟨8591750, by rfl⟩ : syracuseStep 11455667 = 17183501) B17183501
theorem B7637111 : Blo 2261435 7637111 := bstep (se 1 (by rfl) ⟨5727833, by rfl⟩ : syracuseStep 7637111 = 11455667) B11455667
theorem B5091407 : Blo 2261435 5091407 := bstep (se 1 (by rfl) ⟨3818555, by rfl⟩ : syracuseStep 5091407 = 7637111) B7637111
theorem B3394271 : Blo 2261435 3394271 := bstep (se 1 (by rfl) ⟨2545703, by rfl⟩ : syracuseStep 3394271 = 5091407) B5091407
theorem B2262847 : Blo 2261435 2262847 := bstep (se 1 (by rfl) ⟨1697135, by rfl⟩ : syracuseStep 2262847 = 3394271) B3394271
theorem B3394277 : Blo 2261435 3394277 := bbase (se 4 (by rfl) ⟨318213, by rfl⟩ : syracuseStep 3394277 = 636427) (by norm_num)
theorem B2262851 : Blo 2261435 2262851 := bstep (se 1 (by rfl) ⟨1697138, by rfl⟩ : syracuseStep 2262851 = 3394277) B3394277
theorem B5436989 : Blo 2261435 5436989 := bbase (se 3 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 5436989 = 2038871) (by norm_num)
theorem B3624659 : Blo 2261435 3624659 := bstep (se 1 (by rfl) ⟨2718494, by rfl⟩ : syracuseStep 3624659 = 5436989) B5436989
theorem B2416439 : Blo 2261435 2416439 := bstep (se 1 (by rfl) ⟨1812329, by rfl⟩ : syracuseStep 2416439 = 3624659) B3624659
theorem B6443837 : Blo 2261435 6443837 := bstep (se 3 (by rfl) ⟨1208219, by rfl⟩ : syracuseStep 6443837 = 2416439) B2416439
theorem B4295891 : Blo 2261435 4295891 := bstep (se 1 (by rfl) ⟨3221918, by rfl⟩ : syracuseStep 4295891 = 6443837) B6443837
theorem B2863927 : Blo 2261435 2863927 := bstep (se 1 (by rfl) ⟨2147945, by rfl⟩ : syracuseStep 2863927 = 4295891) B4295891
theorem B3818569 : Blo 2261435 3818569 := bstep (se 2 (by rfl) ⟨1431963, by rfl⟩ : syracuseStep 3818569 = 2863927) B2863927
theorem B5091425 : Blo 2261435 5091425 := bstep (se 2 (by rfl) ⟨1909284, by rfl⟩ : syracuseStep 5091425 = 3818569) B3818569
theorem B3394283 : Blo 2261435 3394283 := bstep (se 1 (by rfl) ⟨2545712, by rfl⟩ : syracuseStep 3394283 = 5091425) B5091425
theorem B2262855 : Blo 2261435 2262855 := bstep (se 1 (by rfl) ⟨1697141, by rfl⟩ : syracuseStep 2262855 = 3394283) B3394283
theorem B2545717 : Blo 2261435 2545717 := bbase (se 5 (by rfl) ⟨119330, by rfl⟩ : syracuseStep 2545717 = 238661) (by norm_num)
theorem B3394289 : Blo 2261435 3394289 := bstep (se 2 (by rfl) ⟨1272858, by rfl⟩ : syracuseStep 3394289 = 2545717) B2545717
theorem B2262859 : Blo 2261435 2262859 := bstep (se 1 (by rfl) ⟨1697144, by rfl⟩ : syracuseStep 2262859 = 3394289) B3394289
theorem B2863937 : Blo 2261435 2863937 := bbase (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) (by norm_num)
theorem B7637165 : Blo 2261435 7637165 := bstep (se 3 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 7637165 = 2863937) B2863937
theorem B5091443 : Blo 2261435 5091443 := bstep (se 1 (by rfl) ⟨3818582, by rfl⟩ : syracuseStep 5091443 = 7637165) B7637165
theorem B3394295 : Blo 2261435 3394295 := bstep (se 1 (by rfl) ⟨2545721, by rfl⟩ : syracuseStep 3394295 = 5091443) B5091443
theorem B2262863 : Blo 2261435 2262863 := bstep (se 1 (by rfl) ⟨1697147, by rfl⟩ : syracuseStep 2262863 = 3394295) B3394295
theorem B3394301 : Blo 2261435 3394301 := bbase (se 3 (by rfl) ⟨636431, by rfl⟩ : syracuseStep 3394301 = 1272863) (by norm_num)
theorem B2262867 : Blo 2261435 2262867 := bstep (se 1 (by rfl) ⟨1697150, by rfl⟩ : syracuseStep 2262867 = 3394301) B3394301
theorem B5091461 : Blo 2261435 5091461 := bbase (se 4 (by rfl) ⟨477324, by rfl⟩ : syracuseStep 5091461 = 954649) (by norm_num)
theorem B3394307 : Blo 2261435 3394307 := bstep (se 1 (by rfl) ⟨2545730, by rfl⟩ : syracuseStep 3394307 = 5091461) B5091461
theorem B2262871 : Blo 2261435 2262871 := bstep (se 1 (by rfl) ⟨1697153, by rfl⟩ : syracuseStep 2262871 = 3394307) B3394307
theorem B5437037 : Blo 2261435 5437037 := bbase (se 3 (by rfl) ⟨1019444, by rfl⟩ : syracuseStep 5437037 = 2038889) (by norm_num)
theorem B3624691 : Blo 2261435 3624691 := bstep (se 1 (by rfl) ⟨2718518, by rfl⟩ : syracuseStep 3624691 = 5437037) B5437037
theorem B4832921 : Blo 2261435 4832921 := bstep (se 2 (by rfl) ⟨1812345, by rfl⟩ : syracuseStep 4832921 = 3624691) B3624691
theorem B3221947 : Blo 2261435 3221947 := bstep (se 1 (by rfl) ⟨2416460, by rfl⟩ : syracuseStep 3221947 = 4832921) B4832921
theorem B4295929 : Blo 2261435 4295929 := bstep (se 2 (by rfl) ⟨1610973, by rfl⟩ : syracuseStep 4295929 = 3221947) B3221947
theorem B5727905 : Blo 2261435 5727905 := bstep (se 2 (by rfl) ⟨2147964, by rfl⟩ : syracuseStep 5727905 = 4295929) B4295929
theorem B3818603 : Blo 2261435 3818603 := bstep (se 1 (by rfl) ⟨2863952, by rfl⟩ : syracuseStep 3818603 = 5727905) B5727905
theorem B2545735 : Blo 2261435 2545735 := bstep (se 1 (by rfl) ⟨1909301, by rfl⟩ : syracuseStep 2545735 = 3818603) B3818603
theorem B3394313 : Blo 2261435 3394313 := bstep (se 2 (by rfl) ⟨1272867, by rfl⟩ : syracuseStep 3394313 = 2545735) B2545735
theorem B2262875 : Blo 2261435 2262875 := bstep (se 1 (by rfl) ⟨1697156, by rfl⟩ : syracuseStep 2262875 = 3394313) B3394313
theorem B11455829 : Blo 2261435 11455829 := bbase (se 11 (by rfl) ⟨8390, by rfl⟩ : syracuseStep 11455829 = 16781) (by norm_num)
theorem B7637219 : Blo 2261435 7637219 := bstep (se 1 (by rfl) ⟨5727914, by rfl⟩ : syracuseStep 7637219 = 11455829) B11455829
theorem B5091479 : Blo 2261435 5091479 := bstep (se 1 (by rfl) ⟨3818609, by rfl⟩ : syracuseStep 5091479 = 7637219) B7637219
theorem B3394319 : Blo 2261435 3394319 := bstep (se 1 (by rfl) ⟨2545739, by rfl⟩ : syracuseStep 3394319 = 5091479) B5091479
theorem B2262879 : Blo 2261435 2262879 := bstep (se 1 (by rfl) ⟨1697159, by rfl⟩ : syracuseStep 2262879 = 3394319) B3394319
theorem B3394325 : Blo 2261435 3394325 := bbase (se 6 (by rfl) ⟨79554, by rfl⟩ : syracuseStep 3394325 = 159109) (by norm_num)
theorem B2262883 : Blo 2261435 2262883 := bstep (se 1 (by rfl) ⟨1697162, by rfl⟩ : syracuseStep 2262883 = 3394325) B3394325
theorem B6881285 : Blo 2261435 6881285 := bbase (se 4 (by rfl) ⟨645120, by rfl⟩ : syracuseStep 6881285 = 1290241) (by norm_num)
theorem B4587523 : Blo 2261435 4587523 := bstep (se 1 (by rfl) ⟨3440642, by rfl⟩ : syracuseStep 4587523 = 6881285) B6881285
theorem B24466789 : Blo 2261435 24466789 := bstep (se 4 (by rfl) ⟨2293761, by rfl⟩ : syracuseStep 24466789 = 4587523) B4587523
theorem B32622385 : Blo 2261435 32622385 := bstep (se 2 (by rfl) ⟨12233394, by rfl⟩ : syracuseStep 32622385 = 24466789) B24466789
theorem B43496513 : Blo 2261435 43496513 := bstep (se 2 (by rfl) ⟨16311192, by rfl⟩ : syracuseStep 43496513 = 32622385) B32622385
theorem B28997675 : Blo 2261435 28997675 := bstep (se 1 (by rfl) ⟨21748256, by rfl⟩ : syracuseStep 28997675 = 43496513) B43496513
theorem B19331783 : Blo 2261435 19331783 := bstep (se 1 (by rfl) ⟨14498837, by rfl⟩ : syracuseStep 19331783 = 28997675) B28997675
theorem B12887855 : Blo 2261435 12887855 := bstep (se 1 (by rfl) ⟨9665891, by rfl⟩ : syracuseStep 12887855 = 19331783) B19331783
theorem B8591903 : Blo 2261435 8591903 := bstep (se 1 (by rfl) ⟨6443927, by rfl⟩ : syracuseStep 8591903 = 12887855) B12887855
theorem B5727935 : Blo 2261435 5727935 := bstep (se 1 (by rfl) ⟨4295951, by rfl⟩ : syracuseStep 5727935 = 8591903) B8591903
theorem B3818623 : Blo 2261435 3818623 := bstep (se 1 (by rfl) ⟨2863967, by rfl⟩ : syracuseStep 3818623 = 5727935) B5727935
theorem B5091497 : Blo 2261435 5091497 := bstep (se 2 (by rfl) ⟨1909311, by rfl⟩ : syracuseStep 5091497 = 3818623) B3818623
theorem B3394331 : Blo 2261435 3394331 := bstep (se 1 (by rfl) ⟨2545748, by rfl⟩ : syracuseStep 3394331 = 5091497) B5091497
theorem B2262887 : Blo 2261435 2262887 := bstep (se 1 (by rfl) ⟨1697165, by rfl⟩ : syracuseStep 2262887 = 3394331) B3394331
theorem B2545753 : Blo 2261435 2545753 := bbase (se 2 (by rfl) ⟨954657, by rfl⟩ : syracuseStep 2545753 = 1909315) (by norm_num)
theorem B3394337 : Blo 2261435 3394337 := bstep (se 2 (by rfl) ⟨1272876, by rfl⟩ : syracuseStep 3394337 = 2545753) B2545753
theorem B2262891 : Blo 2261435 2262891 := bstep (se 1 (by rfl) ⟨1697168, by rfl⟩ : syracuseStep 2262891 = 3394337) B3394337
theorem B7249445 : Blo 2261435 7249445 := bbase (se 4 (by rfl) ⟨679635, by rfl⟩ : syracuseStep 7249445 = 1359271) (by norm_num)
theorem B4832963 : Blo 2261435 4832963 := bstep (se 1 (by rfl) ⟨3624722, by rfl⟩ : syracuseStep 4832963 = 7249445) B7249445
theorem B3221975 : Blo 2261435 3221975 := bstep (se 1 (by rfl) ⟨2416481, by rfl⟩ : syracuseStep 3221975 = 4832963) B4832963
theorem B8591933 : Blo 2261435 8591933 := bstep (se 3 (by rfl) ⟨1610987, by rfl⟩ : syracuseStep 8591933 = 3221975) B3221975
theorem B5727955 : Blo 2261435 5727955 := bstep (se 1 (by rfl) ⟨4295966, by rfl⟩ : syracuseStep 5727955 = 8591933) B8591933
theorem B7637273 : Blo 2261435 7637273 := bstep (se 2 (by rfl) ⟨2863977, by rfl⟩ : syracuseStep 7637273 = 5727955) B5727955
theorem B5091515 : Blo 2261435 5091515 := bstep (se 1 (by rfl) ⟨3818636, by rfl⟩ : syracuseStep 5091515 = 7637273) B7637273
theorem B3394343 : Blo 2261435 3394343 := bstep (se 1 (by rfl) ⟨2545757, by rfl⟩ : syracuseStep 3394343 = 5091515) B5091515
theorem B2262895 : Blo 2261435 2262895 := bstep (se 1 (by rfl) ⟨1697171, by rfl⟩ : syracuseStep 2262895 = 3394343) B3394343
theorem B3394349 : Blo 2261435 3394349 := bbase (se 3 (by rfl) ⟨636440, by rfl⟩ : syracuseStep 3394349 = 1272881) (by norm_num)
theorem B2262899 : Blo 2261435 2262899 := bstep (se 1 (by rfl) ⟨1697174, by rfl⟩ : syracuseStep 2262899 = 3394349) B3394349
theorem B5091533 : Blo 2261435 5091533 := bbase (se 3 (by rfl) ⟨954662, by rfl⟩ : syracuseStep 5091533 = 1909325) (by norm_num)
theorem B3394355 : Blo 2261435 3394355 := bstep (se 1 (by rfl) ⟨2545766, by rfl⟩ : syracuseStep 3394355 = 5091533) B5091533
theorem B2262903 : Blo 2261435 2262903 := bstep (se 1 (by rfl) ⟨1697177, by rfl⟩ : syracuseStep 2262903 = 3394355) B3394355
theorem B2863993 : Blo 2261435 2863993 := bbase (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) (by norm_num)
theorem B3818657 : Blo 2261435 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B2545771 : Blo 2261435 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B3394361 : Blo 2261435 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B2262907 : Blo 2261435 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B3058381 : Blo 2261435 3058381 := bbase (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) (by norm_num)
theorem B16311365 : Blo 2261435 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B10874243 : Blo 2261435 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B7249495 : Blo 2261435 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B9665993 : Blo 2261435 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B25775981 : Blo 2261435 25775981 := bstep (se 3 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 25775981 = 9665993) B9665993
theorem B17183987 : Blo 2261435 17183987 := bstep (se 1 (by rfl) ⟨12887990, by rfl⟩ : syracuseStep 17183987 = 25775981) B25775981
theorem B11455991 : Blo 2261435 11455991 := bstep (se 1 (by rfl) ⟨8591993, by rfl⟩ : syracuseStep 11455991 = 17183987) B17183987
theorem B7637327 : Blo 2261435 7637327 := bstep (se 1 (by rfl) ⟨5727995, by rfl⟩ : syracuseStep 7637327 = 11455991) B11455991
theorem B5091551 : Blo 2261435 5091551 := bstep (se 1 (by rfl) ⟨3818663, by rfl⟩ : syracuseStep 5091551 = 7637327) B7637327
theorem B3394367 : Blo 2261435 3394367 := bstep (se 1 (by rfl) ⟨2545775, by rfl⟩ : syracuseStep 3394367 = 5091551) B5091551
theorem B2262911 : Blo 2261435 2262911 := bstep (se 1 (by rfl) ⟨1697183, by rfl⟩ : syracuseStep 2262911 = 3394367) B3394367
theorem B3394373 : Blo 2261435 3394373 := bbase (se 4 (by rfl) ⟨318222, by rfl⟩ : syracuseStep 3394373 = 636445) (by norm_num)
theorem B2262915 : Blo 2261435 2262915 := bstep (se 1 (by rfl) ⟨1697186, by rfl⟩ : syracuseStep 2262915 = 3394373) B3394373
theorem B3818677 : Blo 2261435 3818677 := bbase (se 5 (by rfl) ⟨179000, by rfl⟩ : syracuseStep 3818677 = 358001) (by norm_num)
theorem B5091569 : Blo 2261435 5091569 := bstep (se 2 (by rfl) ⟨1909338, by rfl⟩ : syracuseStep 5091569 = 3818677) B3818677
theorem B3394379 : Blo 2261435 3394379 := bstep (se 1 (by rfl) ⟨2545784, by rfl⟩ : syracuseStep 3394379 = 5091569) B5091569
theorem B2262919 : Blo 2261435 2262919 := bstep (se 1 (by rfl) ⟨1697189, by rfl⟩ : syracuseStep 2262919 = 3394379) B3394379
theorem B2545789 : Blo 2261435 2545789 := bbase (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) (by norm_num)
theorem B3394385 : Blo 2261435 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B2262923 : Blo 2261435 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B7637381 : Blo 2261435 7637381 := bbase (se 4 (by rfl) ⟨716004, by rfl⟩ : syracuseStep 7637381 = 1432009) (by norm_num)
theorem B5091587 : Blo 2261435 5091587 := bstep (se 1 (by rfl) ⟨3818690, by rfl⟩ : syracuseStep 5091587 = 7637381) B7637381
theorem B3394391 : Blo 2261435 3394391 := bstep (se 1 (by rfl) ⟨2545793, by rfl⟩ : syracuseStep 3394391 = 5091587) B5091587
theorem B2262927 : Blo 2261435 2262927 := bstep (se 1 (by rfl) ⟨1697195, by rfl⟩ : syracuseStep 2262927 = 3394391) B3394391
theorem B3394397 : Blo 2261435 3394397 := bbase (se 3 (by rfl) ⟨636449, by rfl⟩ : syracuseStep 3394397 = 1272899) (by norm_num)
theorem B2262931 : Blo 2261435 2262931 := bstep (se 1 (by rfl) ⟨1697198, by rfl⟩ : syracuseStep 2262931 = 3394397) B3394397
theorem B5091605 : Blo 2261435 5091605 := bbase (se 6 (by rfl) ⟨119334, by rfl⟩ : syracuseStep 5091605 = 238669) (by norm_num)
theorem B3394403 : Blo 2261435 3394403 := bstep (se 1 (by rfl) ⟨2545802, by rfl⟩ : syracuseStep 3394403 = 5091605) B5091605
theorem B2262935 : Blo 2261435 2262935 := bstep (se 1 (by rfl) ⟨1697201, by rfl⟩ : syracuseStep 2262935 = 3394403) B3394403
theorem B8592101 : Blo 2261435 8592101 := bbase (se 4 (by rfl) ⟨805509, by rfl⟩ : syracuseStep 8592101 = 1611019) (by norm_num)
theorem B5728067 : Blo 2261435 5728067 := bstep (se 1 (by rfl) ⟨4296050, by rfl⟩ : syracuseStep 5728067 = 8592101) B8592101
theorem B3818711 : Blo 2261435 3818711 := bstep (se 1 (by rfl) ⟨2864033, by rfl⟩ : syracuseStep 3818711 = 5728067) B5728067
theorem B2545807 : Blo 2261435 2545807 := bstep (se 1 (by rfl) ⟨1909355, by rfl⟩ : syracuseStep 2545807 = 3818711) B3818711
theorem B3394409 : Blo 2261435 3394409 := bstep (se 2 (by rfl) ⟨1272903, by rfl⟩ : syracuseStep 3394409 = 2545807) B2545807
theorem B2262939 : Blo 2261435 2262939 := bstep (se 1 (by rfl) ⟨1697204, by rfl⟩ : syracuseStep 2262939 = 3394409) B3394409
theorem B18350549 : Blo 2261435 18350549 := bbase (se 7 (by rfl) ⟨215045, by rfl⟩ : syracuseStep 18350549 = 430091) (by norm_num)
theorem B12233699 : Blo 2261435 12233699 := bstep (se 1 (by rfl) ⟨9175274, by rfl⟩ : syracuseStep 12233699 = 18350549) B18350549
theorem B8155799 : Blo 2261435 8155799 := bstep (se 1 (by rfl) ⟨6116849, by rfl⟩ : syracuseStep 8155799 = 12233699) B12233699
theorem B5437199 : Blo 2261435 5437199 := bstep (se 1 (by rfl) ⟨4077899, by rfl⟩ : syracuseStep 5437199 = 8155799) B8155799
theorem B3624799 : Blo 2261435 3624799 := bstep (se 1 (by rfl) ⟨2718599, by rfl⟩ : syracuseStep 3624799 = 5437199) B5437199
theorem B4833065 : Blo 2261435 4833065 := bstep (se 2 (by rfl) ⟨1812399, by rfl⟩ : syracuseStep 4833065 = 3624799) B3624799
theorem B12888173 : Blo 2261435 12888173 := bstep (se 3 (by rfl) ⟨2416532, by rfl⟩ : syracuseStep 12888173 = 4833065) B4833065
theorem B8592115 : Blo 2261435 8592115 := bstep (se 1 (by rfl) ⟨6444086, by rfl⟩ : syracuseStep 8592115 = 12888173) B12888173
theorem B11456153 : Blo 2261435 11456153 := bstep (se 2 (by rfl) ⟨4296057, by rfl⟩ : syracuseStep 11456153 = 8592115) B8592115
theorem B7637435 : Blo 2261435 7637435 := bstep (se 1 (by rfl) ⟨5728076, by rfl⟩ : syracuseStep 7637435 = 11456153) B11456153
theorem B5091623 : Blo 2261435 5091623 := bstep (se 1 (by rfl) ⟨3818717, by rfl⟩ : syracuseStep 5091623 = 7637435) B7637435
theorem B3394415 : Blo 2261435 3394415 := bstep (se 1 (by rfl) ⟨2545811, by rfl⟩ : syracuseStep 3394415 = 5091623) B5091623
theorem B2262943 : Blo 2261435 2262943 := bstep (se 1 (by rfl) ⟨1697207, by rfl⟩ : syracuseStep 2262943 = 3394415) B3394415
theorem B3394421 : Blo 2261435 3394421 := bbase (se 5 (by rfl) ⟨159113, by rfl⟩ : syracuseStep 3394421 = 318227) (by norm_num)
theorem B2262947 : Blo 2261435 2262947 := bstep (se 1 (by rfl) ⟨1697210, by rfl⟩ : syracuseStep 2262947 = 3394421) B3394421
theorem B8155829 : Blo 2261435 8155829 := bbase (se 5 (by rfl) ⟨382304, by rfl⟩ : syracuseStep 8155829 = 764609) (by norm_num)
theorem B5437219 : Blo 2261435 5437219 := bstep (se 1 (by rfl) ⟨4077914, by rfl⟩ : syracuseStep 5437219 = 8155829) B8155829
theorem B7249625 : Blo 2261435 7249625 := bstep (se 2 (by rfl) ⟨2718609, by rfl⟩ : syracuseStep 7249625 = 5437219) B5437219
theorem B4833083 : Blo 2261435 4833083 := bstep (se 1 (by rfl) ⟨3624812, by rfl⟩ : syracuseStep 4833083 = 7249625) B7249625
theorem B3222055 : Blo 2261435 3222055 := bstep (se 1 (by rfl) ⟨2416541, by rfl⟩ : syracuseStep 3222055 = 4833083) B4833083
theorem B4296073 : Blo 2261435 4296073 := bstep (se 2 (by rfl) ⟨1611027, by rfl⟩ : syracuseStep 4296073 = 3222055) B3222055
theorem B5728097 : Blo 2261435 5728097 := bstep (se 2 (by rfl) ⟨2148036, by rfl⟩ : syracuseStep 5728097 = 4296073) B4296073
theorem B3818731 : Blo 2261435 3818731 := bstep (se 1 (by rfl) ⟨2864048, by rfl⟩ : syracuseStep 3818731 = 5728097) B5728097
theorem B5091641 : Blo 2261435 5091641 := bstep (se 2 (by rfl) ⟨1909365, by rfl⟩ : syracuseStep 5091641 = 3818731) B3818731
theorem B3394427 : Blo 2261435 3394427 := bstep (se 1 (by rfl) ⟨2545820, by rfl⟩ : syracuseStep 3394427 = 5091641) B5091641
theorem B2262951 : Blo 2261435 2262951 := bstep (se 1 (by rfl) ⟨1697213, by rfl⟩ : syracuseStep 2262951 = 3394427) B3394427
theorem B2545825 : Blo 2261435 2545825 := bbase (se 2 (by rfl) ⟨954684, by rfl⟩ : syracuseStep 2545825 = 1909369) (by norm_num)
theorem B3394433 : Blo 2261435 3394433 := bstep (se 2 (by rfl) ⟨1272912, by rfl⟩ : syracuseStep 3394433 = 2545825) B2545825
theorem B2262955 : Blo 2261435 2262955 := bstep (se 1 (by rfl) ⟨1697216, by rfl⟩ : syracuseStep 2262955 = 3394433) B3394433
theorem B5728117 : Blo 2261435 5728117 := bbase (se 5 (by rfl) ⟨268505, by rfl⟩ : syracuseStep 5728117 = 537011) (by norm_num)
theorem B7637489 : Blo 2261435 7637489 := bstep (se 2 (by rfl) ⟨2864058, by rfl⟩ : syracuseStep 7637489 = 5728117) B5728117
theorem B5091659 : Blo 2261435 5091659 := bstep (se 1 (by rfl) ⟨3818744, by rfl⟩ : syracuseStep 5091659 = 7637489) B7637489
theorem B3394439 : Blo 2261435 3394439 := bstep (se 1 (by rfl) ⟨2545829, by rfl⟩ : syracuseStep 3394439 = 5091659) B5091659
theorem B2262959 : Blo 2261435 2262959 := bstep (se 1 (by rfl) ⟨1697219, by rfl⟩ : syracuseStep 2262959 = 3394439) B3394439
theorem B3394445 : Blo 2261435 3394445 := bbase (se 3 (by rfl) ⟨636458, by rfl⟩ : syracuseStep 3394445 = 1272917) (by norm_num)
theorem B2262963 : Blo 2261435 2262963 := bstep (se 1 (by rfl) ⟨1697222, by rfl⟩ : syracuseStep 2262963 = 3394445) B3394445
theorem B5091677 : Blo 2261435 5091677 := bbase (se 3 (by rfl) ⟨954689, by rfl⟩ : syracuseStep 5091677 = 1909379) (by norm_num)
theorem B3394451 : Blo 2261435 3394451 := bstep (se 1 (by rfl) ⟨2545838, by rfl⟩ : syracuseStep 3394451 = 5091677) B5091677
theorem B2262967 : Blo 2261435 2262967 := bstep (se 1 (by rfl) ⟨1697225, by rfl⟩ : syracuseStep 2262967 = 3394451) B3394451
theorem B3818765 : Blo 2261435 3818765 := bbase (se 3 (by rfl) ⟨716018, by rfl⟩ : syracuseStep 3818765 = 1432037) (by norm_num)
theorem B2545843 : Blo 2261435 2545843 := bstep (se 1 (by rfl) ⟨1909382, by rfl⟩ : syracuseStep 2545843 = 3818765) B3818765
theorem B3394457 : Blo 2261435 3394457 := bstep (se 2 (by rfl) ⟨1272921, by rfl⟩ : syracuseStep 3394457 = 2545843) B2545843
theorem B2262971 : Blo 2261435 2262971 := bstep (se 1 (by rfl) ⟨1697228, by rfl⟩ : syracuseStep 2262971 = 3394457) B3394457
theorem B19332533 : Blo 2261435 19332533 := bbase (se 5 (by rfl) ⟨906212, by rfl⟩ : syracuseStep 19332533 = 1812425) (by norm_num)
theorem B12888355 : Blo 2261435 12888355 := bstep (se 1 (by rfl) ⟨9666266, by rfl⟩ : syracuseStep 12888355 = 19332533) B19332533
theorem B17184473 : Blo 2261435 17184473 := bstep (se 2 (by rfl) ⟨6444177, by rfl⟩ : syracuseStep 17184473 = 12888355) B12888355
theorem B11456315 : Blo 2261435 11456315 := bstep (se 1 (by rfl) ⟨8592236, by rfl⟩ : syracuseStep 11456315 = 17184473) B17184473
theorem B7637543 : Blo 2261435 7637543 := bstep (se 1 (by rfl) ⟨5728157, by rfl⟩ : syracuseStep 7637543 = 11456315) B11456315
theorem B5091695 : Blo 2261435 5091695 := bstep (se 1 (by rfl) ⟨3818771, by rfl⟩ : syracuseStep 5091695 = 7637543) B7637543
theorem B3394463 : Blo 2261435 3394463 := bstep (se 1 (by rfl) ⟨2545847, by rfl⟩ : syracuseStep 3394463 = 5091695) B5091695
theorem B2262975 : Blo 2261435 2262975 := bstep (se 1 (by rfl) ⟨1697231, by rfl⟩ : syracuseStep 2262975 = 3394463) B3394463
theorem B3394469 : Blo 2261435 3394469 := bbase (se 4 (by rfl) ⟨318231, by rfl⟩ : syracuseStep 3394469 = 636463) (by norm_num)
theorem B2262979 : Blo 2261435 2262979 := bstep (se 1 (by rfl) ⟨1697234, by rfl⟩ : syracuseStep 2262979 = 3394469) B3394469
theorem B2864089 : Blo 2261435 2864089 := bbase (se 2 (by rfl) ⟨1074033, by rfl⟩ : syracuseStep 2864089 = 2148067) (by norm_num)
theorem B3818785 : Blo 2261435 3818785 := bstep (se 2 (by rfl) ⟨1432044, by rfl⟩ : syracuseStep 3818785 = 2864089) B2864089
theorem B5091713 : Blo 2261435 5091713 := bstep (se 2 (by rfl) ⟨1909392, by rfl⟩ : syracuseStep 5091713 = 3818785) B3818785
theorem B3394475 : Blo 2261435 3394475 := bstep (se 1 (by rfl) ⟨2545856, by rfl⟩ : syracuseStep 3394475 = 5091713) B5091713
theorem B2262983 : Blo 2261435 2262983 := bstep (se 1 (by rfl) ⟨1697237, by rfl⟩ : syracuseStep 2262983 = 3394475) B3394475
theorem B2545861 : Blo 2261435 2545861 := bbase (se 4 (by rfl) ⟨238674, by rfl⟩ : syracuseStep 2545861 = 477349) (by norm_num)
theorem B3394481 : Blo 2261435 3394481 := bstep (se 2 (by rfl) ⟨1272930, by rfl⟩ : syracuseStep 3394481 = 2545861) B2545861
theorem B2262987 : Blo 2261435 2262987 := bstep (se 1 (by rfl) ⟨1697240, by rfl⟩ : syracuseStep 2262987 = 3394481) B3394481
theorem B4296149 : Blo 2261435 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B2864099 : Blo 2261435 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B7637597 : Blo 2261435 7637597 := bstep (se 3 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 7637597 = 2864099) B2864099
theorem B5091731 : Blo 2261435 5091731 := bstep (se 1 (by rfl) ⟨3818798, by rfl⟩ : syracuseStep 5091731 = 7637597) B7637597
theorem B3394487 : Blo 2261435 3394487 := bstep (se 1 (by rfl) ⟨2545865, by rfl⟩ : syracuseStep 3394487 = 5091731) B5091731
theorem B2262991 : Blo 2261435 2262991 := bstep (se 1 (by rfl) ⟨1697243, by rfl⟩ : syracuseStep 2262991 = 3394487) B3394487
theorem B3394493 : Blo 2261435 3394493 := bbase (se 3 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 3394493 = 1272935) (by norm_num)
theorem B2262995 : Blo 2261435 2262995 := bstep (se 1 (by rfl) ⟨1697246, by rfl⟩ : syracuseStep 2262995 = 3394493) B3394493
theorem B5091749 : Blo 2261435 5091749 := bbase (se 4 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 5091749 = 954703) (by norm_num)
theorem B3394499 : Blo 2261435 3394499 := bstep (se 1 (by rfl) ⟨2545874, by rfl⟩ : syracuseStep 3394499 = 5091749) B5091749
theorem B2262999 : Blo 2261435 2262999 := bstep (se 1 (by rfl) ⟨1697249, by rfl⟩ : syracuseStep 2262999 = 3394499) B3394499
theorem B5728229 : Blo 2261435 5728229 := bbase (se 4 (by rfl) ⟨537021, by rfl⟩ : syracuseStep 5728229 = 1074043) (by norm_num)
theorem B3818819 : Blo 2261435 3818819 := bstep (se 1 (by rfl) ⟨2864114, by rfl⟩ : syracuseStep 3818819 = 5728229) B5728229
theorem B2545879 : Blo 2261435 2545879 := bstep (se 1 (by rfl) ⟨1909409, by rfl⟩ : syracuseStep 2545879 = 3818819) B3818819
theorem B3394505 : Blo 2261435 3394505 := bstep (se 2 (by rfl) ⟨1272939, by rfl⟩ : syracuseStep 3394505 = 2545879) B2545879
theorem B2263003 : Blo 2261435 2263003 := bstep (se 1 (by rfl) ⟨1697252, by rfl⟩ : syracuseStep 2263003 = 3394505) B3394505
theorem B2416601 : Blo 2261435 2416601 := bbase (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) (by norm_num)
theorem B6444269 : Blo 2261435 6444269 := bstep (se 3 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 6444269 = 2416601) B2416601
theorem B4296179 : Blo 2261435 4296179 := bstep (se 1 (by rfl) ⟨3222134, by rfl⟩ : syracuseStep 4296179 = 6444269) B6444269
theorem B11456477 : Blo 2261435 11456477 := bstep (se 3 (by rfl) ⟨2148089, by rfl⟩ : syracuseStep 11456477 = 4296179) B4296179
theorem B7637651 : Blo 2261435 7637651 := bstep (se 1 (by rfl) ⟨5728238, by rfl⟩ : syracuseStep 7637651 = 11456477) B11456477
theorem B5091767 : Blo 2261435 5091767 := bstep (se 1 (by rfl) ⟨3818825, by rfl⟩ : syracuseStep 5091767 = 7637651) B7637651
theorem B3394511 : Blo 2261435 3394511 := bstep (se 1 (by rfl) ⟨2545883, by rfl⟩ : syracuseStep 3394511 = 5091767) B5091767
theorem B2263007 : Blo 2261435 2263007 := bstep (se 1 (by rfl) ⟨1697255, by rfl⟩ : syracuseStep 2263007 = 3394511) B3394511
theorem B3394517 : Blo 2261435 3394517 := bbase (se 7 (by rfl) ⟨39779, by rfl⟩ : syracuseStep 3394517 = 79559) (by norm_num)
theorem B2263011 : Blo 2261435 2263011 := bstep (se 1 (by rfl) ⟨1697258, by rfl⟩ : syracuseStep 2263011 = 3394517) B3394517
theorem B8592389 : Blo 2261435 8592389 := bbase (se 4 (by rfl) ⟨805536, by rfl⟩ : syracuseStep 8592389 = 1611073) (by norm_num)
theorem B5728259 : Blo 2261435 5728259 := bstep (se 1 (by rfl) ⟨4296194, by rfl⟩ : syracuseStep 5728259 = 8592389) B8592389
theorem B3818839 : Blo 2261435 3818839 := bstep (se 1 (by rfl) ⟨2864129, by rfl⟩ : syracuseStep 3818839 = 5728259) B5728259
theorem B5091785 : Blo 2261435 5091785 := bstep (se 2 (by rfl) ⟨1909419, by rfl⟩ : syracuseStep 5091785 = 3818839) B3818839
theorem B3394523 : Blo 2261435 3394523 := bstep (se 1 (by rfl) ⟨2545892, by rfl⟩ : syracuseStep 3394523 = 5091785) B5091785
theorem B2263015 : Blo 2261435 2263015 := bstep (se 1 (by rfl) ⟨1697261, by rfl⟩ : syracuseStep 2263015 = 3394523) B3394523
theorem B2545897 : Blo 2261435 2545897 := bbase (se 2 (by rfl) ⟨954711, by rfl⟩ : syracuseStep 2545897 = 1909423) (by norm_num)
theorem B3394529 : Blo 2261435 3394529 := bstep (se 2 (by rfl) ⟨1272948, by rfl⟩ : syracuseStep 3394529 = 2545897) B2545897
theorem B2263019 : Blo 2261435 2263019 := bstep (se 1 (by rfl) ⟨1697264, by rfl⟩ : syracuseStep 2263019 = 3394529) B3394529
theorem B12888629 : Blo 2261435 12888629 := bbase (se 5 (by rfl) ⟨604154, by rfl⟩ : syracuseStep 12888629 = 1208309) (by norm_num)
theorem B8592419 : Blo 2261435 8592419 := bstep (se 1 (by rfl) ⟨6444314, by rfl⟩ : syracuseStep 8592419 = 12888629) B12888629
theorem B5728279 : Blo 2261435 5728279 := bstep (se 1 (by rfl) ⟨4296209, by rfl⟩ : syracuseStep 5728279 = 8592419) B8592419
theorem B7637705 : Blo 2261435 7637705 := bstep (se 2 (by rfl) ⟨2864139, by rfl⟩ : syracuseStep 7637705 = 5728279) B5728279
theorem B5091803 : Blo 2261435 5091803 := bstep (se 1 (by rfl) ⟨3818852, by rfl⟩ : syracuseStep 5091803 = 7637705) B7637705
theorem B3394535 : Blo 2261435 3394535 := bstep (se 1 (by rfl) ⟨2545901, by rfl⟩ : syracuseStep 3394535 = 5091803) B5091803
theorem B2263023 : Blo 2261435 2263023 := bstep (se 1 (by rfl) ⟨1697267, by rfl⟩ : syracuseStep 2263023 = 3394535) B3394535
theorem B3394541 : Blo 2261435 3394541 := bbase (se 3 (by rfl) ⟨636476, by rfl⟩ : syracuseStep 3394541 = 1272953) (by norm_num)
theorem B2263027 : Blo 2261435 2263027 := bstep (se 1 (by rfl) ⟨1697270, by rfl⟩ : syracuseStep 2263027 = 3394541) B3394541
theorem B5091821 : Blo 2261435 5091821 := bbase (se 3 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 5091821 = 1909433) (by norm_num)
theorem B3394547 : Blo 2261435 3394547 := bstep (se 1 (by rfl) ⟨2545910, by rfl⟩ : syracuseStep 3394547 = 5091821) B5091821
theorem B2263031 : Blo 2261435 2263031 := bstep (se 1 (by rfl) ⟨1697273, by rfl⟩ : syracuseStep 2263031 = 3394547) B3394547
theorem B11612933 : Blo 2261435 11612933 := bbase (se 4 (by rfl) ⟨1088712, by rfl⟩ : syracuseStep 11612933 = 2177425) (by norm_num)
theorem B7741955 : Blo 2261435 7741955 := bstep (se 1 (by rfl) ⟨5806466, by rfl⟩ : syracuseStep 7741955 = 11612933) B11612933
theorem B5161303 : Blo 2261435 5161303 := bstep (se 1 (by rfl) ⟨3870977, by rfl⟩ : syracuseStep 5161303 = 7741955) B7741955
theorem B27526949 : Blo 2261435 27526949 := bstep (se 4 (by rfl) ⟨2580651, by rfl⟩ : syracuseStep 27526949 = 5161303) B5161303
theorem B18351299 : Blo 2261435 18351299 := bstep (se 1 (by rfl) ⟨13763474, by rfl⟩ : syracuseStep 18351299 = 27526949) B27526949
theorem B12234199 : Blo 2261435 12234199 := bstep (se 1 (by rfl) ⟨9175649, by rfl⟩ : syracuseStep 12234199 = 18351299) B18351299
theorem B16312265 : Blo 2261435 16312265 := bstep (se 2 (by rfl) ⟨6117099, by rfl⟩ : syracuseStep 16312265 = 12234199) B12234199
theorem B10874843 : Blo 2261435 10874843 := bstep (se 1 (by rfl) ⟨8156132, by rfl⟩ : syracuseStep 10874843 = 16312265) B16312265
theorem B7249895 : Blo 2261435 7249895 := bstep (se 1 (by rfl) ⟨5437421, by rfl⟩ : syracuseStep 7249895 = 10874843) B10874843
theorem B4833263 : Blo 2261435 4833263 := bstep (se 1 (by rfl) ⟨3624947, by rfl⟩ : syracuseStep 4833263 = 7249895) B7249895
theorem B3222175 : Blo 2261435 3222175 := bstep (se 1 (by rfl) ⟨2416631, by rfl⟩ : syracuseStep 3222175 = 4833263) B4833263
theorem B4296233 : Blo 2261435 4296233 := bstep (se 2 (by rfl) ⟨1611087, by rfl⟩ : syracuseStep 4296233 = 3222175) B3222175
theorem B2864155 : Blo 2261435 2864155 := bstep (se 1 (by rfl) ⟨2148116, by rfl⟩ : syracuseStep 2864155 = 4296233) B4296233
theorem B3818873 : Blo 2261435 3818873 := bstep (se 2 (by rfl) ⟨1432077, by rfl⟩ : syracuseStep 3818873 = 2864155) B2864155
theorem B2545915 : Blo 2261435 2545915 := bstep (se 1 (by rfl) ⟨1909436, by rfl⟩ : syracuseStep 2545915 = 3818873) B3818873
theorem B3394553 : Blo 2261435 3394553 := bstep (se 2 (by rfl) ⟨1272957, by rfl⟩ : syracuseStep 3394553 = 2545915) B2545915
theorem B2263035 : Blo 2261435 2263035 := bstep (se 1 (by rfl) ⟨1697276, by rfl⟩ : syracuseStep 2263035 = 3394553) B3394553
theorem B3100285 : Blo 2261435 3100285 := bbase (se 3 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 3100285 = 1162607) (by norm_num)
theorem B4133713 : Blo 2261435 4133713 := bstep (se 2 (by rfl) ⟨1550142, by rfl⟩ : syracuseStep 4133713 = 3100285) B3100285
theorem B5511617 : Blo 2261435 5511617 := bstep (se 2 (by rfl) ⟨2066856, by rfl⟩ : syracuseStep 5511617 = 4133713) B4133713
theorem B3674411 : Blo 2261435 3674411 := bstep (se 1 (by rfl) ⟨2755808, by rfl⟩ : syracuseStep 3674411 = 5511617) B5511617
theorem B2449607 : Blo 2261435 2449607 := bstep (se 1 (by rfl) ⟨1837205, by rfl⟩ : syracuseStep 2449607 = 3674411) B3674411
theorem B6532285 : Blo 2261435 6532285 := bstep (se 3 (by rfl) ⟨1224803, by rfl⟩ : syracuseStep 6532285 = 2449607) B2449607
theorem B8709713 : Blo 2261435 8709713 := bstep (se 2 (by rfl) ⟨3266142, by rfl⟩ : syracuseStep 8709713 = 6532285) B6532285
theorem B5806475 : Blo 2261435 5806475 := bstep (se 1 (by rfl) ⟨4354856, by rfl⟩ : syracuseStep 5806475 = 8709713) B8709713
theorem B3870983 : Blo 2261435 3870983 := bstep (se 1 (by rfl) ⟨2903237, by rfl⟩ : syracuseStep 3870983 = 5806475) B5806475
theorem B2580655 : Blo 2261435 2580655 := bstep (se 1 (by rfl) ⟨1935491, by rfl⟩ : syracuseStep 2580655 = 3870983) B3870983
theorem B3440873 : Blo 2261435 3440873 := bstep (se 2 (by rfl) ⟨1290327, by rfl⟩ : syracuseStep 3440873 = 2580655) B2580655
theorem B9175661 : Blo 2261435 9175661 := bstep (se 3 (by rfl) ⟨1720436, by rfl⟩ : syracuseStep 9175661 = 3440873) B3440873
theorem B97873717 : Blo 2261435 97873717 := bstep (se 5 (by rfl) ⟨4587830, by rfl⟩ : syracuseStep 97873717 = 9175661) B9175661
theorem B130498289 : Blo 2261435 130498289 := bstep (se 2 (by rfl) ⟨48936858, by rfl⟩ : syracuseStep 130498289 = 97873717) B97873717
theorem B86998859 : Blo 2261435 86998859 := bstep (se 1 (by rfl) ⟨65249144, by rfl⟩ : syracuseStep 86998859 = 130498289) B130498289
theorem B57999239 : Blo 2261435 57999239 := bstep (se 1 (by rfl) ⟨43499429, by rfl⟩ : syracuseStep 57999239 = 86998859) B86998859
theorem B38666159 : Blo 2261435 38666159 := bstep (se 1 (by rfl) ⟨28999619, by rfl⟩ : syracuseStep 38666159 = 57999239) B57999239
theorem B25777439 : Blo 2261435 25777439 := bstep (se 1 (by rfl) ⟨19333079, by rfl⟩ : syracuseStep 25777439 = 38666159) B38666159
theorem B17184959 : Blo 2261435 17184959 := bstep (se 1 (by rfl) ⟨12888719, by rfl⟩ : syracuseStep 17184959 = 25777439) B25777439
theorem B11456639 : Blo 2261435 11456639 := bstep (se 1 (by rfl) ⟨8592479, by rfl⟩ : syracuseStep 11456639 = 17184959) B17184959
theorem B7637759 : Blo 2261435 7637759 := bstep (se 1 (by rfl) ⟨5728319, by rfl⟩ : syracuseStep 7637759 = 11456639) B11456639
theorem B5091839 : Blo 2261435 5091839 := bstep (se 1 (by rfl) ⟨3818879, by rfl⟩ : syracuseStep 5091839 = 7637759) B7637759
theorem B3394559 : Blo 2261435 3394559 := bstep (se 1 (by rfl) ⟨2545919, by rfl⟩ : syracuseStep 3394559 = 5091839) B5091839
theorem B2263039 : Blo 2261435 2263039 := bstep (se 1 (by rfl) ⟨1697279, by rfl⟩ : syracuseStep 2263039 = 3394559) B3394559
theorem B3394565 : Blo 2261435 3394565 := bbase (se 4 (by rfl) ⟨318240, by rfl⟩ : syracuseStep 3394565 = 636481) (by norm_num)
theorem B2263043 : Blo 2261435 2263043 := bstep (se 1 (by rfl) ⟨1697282, by rfl⟩ : syracuseStep 2263043 = 3394565) B3394565
theorem B3818893 : Blo 2261435 3818893 := bbase (se 3 (by rfl) ⟨716042, by rfl⟩ : syracuseStep 3818893 = 1432085) (by norm_num)
theorem B5091857 : Blo 2261435 5091857 := bstep (se 2 (by rfl) ⟨1909446, by rfl⟩ : syracuseStep 5091857 = 3818893) B3818893
theorem B3394571 : Blo 2261435 3394571 := bstep (se 1 (by rfl) ⟨2545928, by rfl⟩ : syracuseStep 3394571 = 5091857) B5091857
theorem B2263047 : Blo 2261435 2263047 := bstep (se 1 (by rfl) ⟨1697285, by rfl⟩ : syracuseStep 2263047 = 3394571) B3394571
theorem B2545933 : Blo 2261435 2545933 := bbase (se 3 (by rfl) ⟨477362, by rfl⟩ : syracuseStep 2545933 = 954725) (by norm_num)
theorem B3394577 : Blo 2261435 3394577 := bstep (se 2 (by rfl) ⟨1272966, by rfl⟩ : syracuseStep 3394577 = 2545933) B2545933
theorem B2263051 : Blo 2261435 2263051 := bstep (se 1 (by rfl) ⟨1697288, by rfl⟩ : syracuseStep 2263051 = 3394577) B3394577
theorem B7637813 : Blo 2261435 7637813 := bbase (se 5 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 7637813 = 716045) (by norm_num)
theorem B5091875 : Blo 2261435 5091875 := bstep (se 1 (by rfl) ⟨3818906, by rfl⟩ : syracuseStep 5091875 = 7637813) B7637813
theorem B3394583 : Blo 2261435 3394583 := bstep (se 1 (by rfl) ⟨2545937, by rfl⟩ : syracuseStep 3394583 = 5091875) B5091875
theorem B2263055 : Blo 2261435 2263055 := bstep (se 1 (by rfl) ⟨1697291, by rfl⟩ : syracuseStep 2263055 = 3394583) B3394583
theorem B3394589 : Blo 2261435 3394589 := bbase (se 3 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 3394589 = 1272971) (by norm_num)
theorem B2263059 : Blo 2261435 2263059 := bstep (se 1 (by rfl) ⟨1697294, by rfl⟩ : syracuseStep 2263059 = 3394589) B3394589
theorem B5091893 : Blo 2261435 5091893 := bbase (se 5 (by rfl) ⟨238682, by rfl⟩ : syracuseStep 5091893 = 477365) (by norm_num)
theorem B3394595 : Blo 2261435 3394595 := bstep (se 1 (by rfl) ⟨2545946, by rfl⟩ : syracuseStep 3394595 = 5091893) B5091893
theorem B2263063 : Blo 2261435 2263063 := bstep (se 1 (by rfl) ⟨1697297, by rfl⟩ : syracuseStep 2263063 = 3394595) B3394595
theorem B9666661 : Blo 2261435 9666661 := bbase (se 4 (by rfl) ⟨906249, by rfl⟩ : syracuseStep 9666661 = 1812499) (by norm_num)
theorem B12888881 : Blo 2261435 12888881 := bstep (se 2 (by rfl) ⟨4833330, by rfl⟩ : syracuseStep 12888881 = 9666661) B9666661
theorem B8592587 : Blo 2261435 8592587 := bstep (se 1 (by rfl) ⟨6444440, by rfl⟩ : syracuseStep 8592587 = 12888881) B12888881
theorem B5728391 : Blo 2261435 5728391 := bstep (se 1 (by rfl) ⟨4296293, by rfl⟩ : syracuseStep 5728391 = 8592587) B8592587
theorem B3818927 : Blo 2261435 3818927 := bstep (se 1 (by rfl) ⟨2864195, by rfl⟩ : syracuseStep 3818927 = 5728391) B5728391
theorem B2545951 : Blo 2261435 2545951 := bstep (se 1 (by rfl) ⟨1909463, by rfl⟩ : syracuseStep 2545951 = 3818927) B3818927
theorem B3394601 : Blo 2261435 3394601 := bstep (se 2 (by rfl) ⟨1272975, by rfl⟩ : syracuseStep 3394601 = 2545951) B2545951
theorem B2263067 : Blo 2261435 2263067 := bstep (se 1 (by rfl) ⟨1697300, by rfl⟩ : syracuseStep 2263067 = 3394601) B3394601
theorem B9666677 : Blo 2261435 9666677 := bbase (se 5 (by rfl) ⟨453125, by rfl⟩ : syracuseStep 9666677 = 906251) (by norm_num)
theorem B6444451 : Blo 2261435 6444451 := bstep (se 1 (by rfl) ⟨4833338, by rfl⟩ : syracuseStep 6444451 = 9666677) B9666677
theorem B8592601 : Blo 2261435 8592601 := bstep (se 2 (by rfl) ⟨3222225, by rfl⟩ : syracuseStep 8592601 = 6444451) B6444451
theorem B11456801 : Blo 2261435 11456801 := bstep (se 2 (by rfl) ⟨4296300, by rfl⟩ : syracuseStep 11456801 = 8592601) B8592601
theorem B7637867 : Blo 2261435 7637867 := bstep (se 1 (by rfl) ⟨5728400, by rfl⟩ : syracuseStep 7637867 = 11456801) B11456801
theorem B5091911 : Blo 2261435 5091911 := bstep (se 1 (by rfl) ⟨3818933, by rfl⟩ : syracuseStep 5091911 = 7637867) B7637867
theorem B3394607 : Blo 2261435 3394607 := bstep (se 1 (by rfl) ⟨2545955, by rfl⟩ : syracuseStep 3394607 = 5091911) B5091911
theorem B2263071 : Blo 2261435 2263071 := bstep (se 1 (by rfl) ⟨1697303, by rfl⟩ : syracuseStep 2263071 = 3394607) B3394607
theorem B3394613 : Blo 2261435 3394613 := bbase (se 5 (by rfl) ⟨159122, by rfl⟩ : syracuseStep 3394613 = 318245) (by norm_num)
theorem B2263075 : Blo 2261435 2263075 := bstep (se 1 (by rfl) ⟨1697306, by rfl⟩ : syracuseStep 2263075 = 3394613) B3394613
theorem B5728421 : Blo 2261435 5728421 := bbase (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) (by norm_num)
theorem B3818947 : Blo 2261435 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B5091929 : Blo 2261435 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B3394619 : Blo 2261435 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B2263079 : Blo 2261435 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B2545969 : Blo 2261435 2545969 := bbase (se 2 (by rfl) ⟨954738, by rfl⟩ : syracuseStep 2545969 = 1909477) (by norm_num)
theorem B3394625 : Blo 2261435 3394625 := bstep (se 2 (by rfl) ⟨1272984, by rfl⟩ : syracuseStep 3394625 = 2545969) B2545969
theorem B2263083 : Blo 2261435 2263083 := bstep (se 1 (by rfl) ⟨1697312, by rfl⟩ : syracuseStep 2263083 = 3394625) B3394625
theorem B4833373 : Blo 2261435 4833373 := bbase (se 3 (by rfl) ⟨906257, by rfl⟩ : syracuseStep 4833373 = 1812515) (by norm_num)
theorem B6444497 : Blo 2261435 6444497 := bstep (se 2 (by rfl) ⟨2416686, by rfl⟩ : syracuseStep 6444497 = 4833373) B4833373
theorem B4296331 : Blo 2261435 4296331 := bstep (se 1 (by rfl) ⟨3222248, by rfl⟩ : syracuseStep 4296331 = 6444497) B6444497
theorem B5728441 : Blo 2261435 5728441 := bstep (se 2 (by rfl) ⟨2148165, by rfl⟩ : syracuseStep 5728441 = 4296331) B4296331
theorem B7637921 : Blo 2261435 7637921 := bstep (se 2 (by rfl) ⟨2864220, by rfl⟩ : syracuseStep 7637921 = 5728441) B5728441
theorem B5091947 : Blo 2261435 5091947 := bstep (se 1 (by rfl) ⟨3818960, by rfl⟩ : syracuseStep 5091947 = 7637921) B7637921
theorem B3394631 : Blo 2261435 3394631 := bstep (se 1 (by rfl) ⟨2545973, by rfl⟩ : syracuseStep 3394631 = 5091947) B5091947
theorem B2263087 : Blo 2261435 2263087 := bstep (se 1 (by rfl) ⟨1697315, by rfl⟩ : syracuseStep 2263087 = 3394631) B3394631
theorem B3394637 : Blo 2261435 3394637 := bbase (se 3 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 3394637 = 1272989) (by norm_num)
theorem B2263091 : Blo 2261435 2263091 := bstep (se 1 (by rfl) ⟨1697318, by rfl⟩ : syracuseStep 2263091 = 3394637) B3394637
theorem B5091965 : Blo 2261435 5091965 := bbase (se 3 (by rfl) ⟨954743, by rfl⟩ : syracuseStep 5091965 = 1909487) (by norm_num)
theorem B3394643 : Blo 2261435 3394643 := bstep (se 1 (by rfl) ⟨2545982, by rfl⟩ : syracuseStep 3394643 = 5091965) B5091965
theorem B2263095 : Blo 2261435 2263095 := bstep (se 1 (by rfl) ⟨1697321, by rfl⟩ : syracuseStep 2263095 = 3394643) B3394643
theorem B3818981 : Blo 2261435 3818981 := bbase (se 4 (by rfl) ⟨358029, by rfl⟩ : syracuseStep 3818981 = 716059) (by norm_num)
theorem B2545987 : Blo 2261435 2545987 := bstep (se 1 (by rfl) ⟨1909490, by rfl⟩ : syracuseStep 2545987 = 3818981) B3818981
theorem B3394649 : Blo 2261435 3394649 := bstep (se 2 (by rfl) ⟨1272993, by rfl⟩ : syracuseStep 3394649 = 2545987) B2545987
theorem B2263099 : Blo 2261435 2263099 := bstep (se 1 (by rfl) ⟨1697324, by rfl⟩ : syracuseStep 2263099 = 3394649) B3394649
theorem B4414397 : Blo 2261435 4414397 := bbase (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) (by norm_num)
theorem B11771725 : Blo 2261435 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B15695633 : Blo 2261435 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B10463755 : Blo 2261435 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B13951673 : Blo 2261435 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B9301115 : Blo 2261435 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B24802973 : Blo 2261435 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B16535315 : Blo 2261435 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B11023543 : Blo 2261435 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B14698057 : Blo 2261435 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B19597409 : Blo 2261435 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B13064939 : Blo 2261435 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B8709959 : Blo 2261435 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B5806639 : Blo 2261435 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B7742185 : Blo 2261435 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B41291653 : Blo 2261435 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B55055537 : Blo 2261435 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B36703691 : Blo 2261435 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B24469127 : Blo 2261435 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B16312751 : Blo 2261435 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B10875167 : Blo 2261435 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B7250111 : Blo 2261435 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B4833407 : Blo 2261435 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B3222271 : Blo 2261435 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B17185445 : Blo 2261435 17185445 := bstep (se 4 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 17185445 = 3222271) B3222271
theorem B11456963 : Blo 2261435 11456963 := bstep (se 1 (by rfl) ⟨8592722, by rfl⟩ : syracuseStep 11456963 = 17185445) B17185445
theorem B7637975 : Blo 2261435 7637975 := bstep (se 1 (by rfl) ⟨5728481, by rfl⟩ : syracuseStep 7637975 = 11456963) B11456963
theorem B5091983 : Blo 2261435 5091983 := bstep (se 1 (by rfl) ⟨3818987, by rfl⟩ : syracuseStep 5091983 = 7637975) B7637975
theorem B3394655 : Blo 2261435 3394655 := bstep (se 1 (by rfl) ⟨2545991, by rfl⟩ : syracuseStep 3394655 = 5091983) B5091983
theorem B2263103 : Blo 2261435 2263103 := bstep (se 1 (by rfl) ⟨1697327, by rfl⟩ : syracuseStep 2263103 = 3394655) B3394655
theorem B3394661 : Blo 2261435 3394661 := bbase (se 4 (by rfl) ⟨318249, by rfl⟩ : syracuseStep 3394661 = 636499) (by norm_num)
theorem B2263107 : Blo 2261435 2263107 := bstep (se 1 (by rfl) ⟨1697330, by rfl⟩ : syracuseStep 2263107 = 3394661) B3394661
theorem B3625069 : Blo 2261435 3625069 := bbase (se 3 (by rfl) ⟨679700, by rfl⟩ : syracuseStep 3625069 = 1359401) (by norm_num)
theorem B4833425 : Blo 2261435 4833425 := bstep (se 2 (by rfl) ⟨1812534, by rfl⟩ : syracuseStep 4833425 = 3625069) B3625069
theorem B3222283 : Blo 2261435 3222283 := bstep (se 1 (by rfl) ⟨2416712, by rfl⟩ : syracuseStep 3222283 = 4833425) B4833425
theorem B4296377 : Blo 2261435 4296377 := bstep (se 2 (by rfl) ⟨1611141, by rfl⟩ : syracuseStep 4296377 = 3222283) B3222283
theorem B2864251 : Blo 2261435 2864251 := bstep (se 1 (by rfl) ⟨2148188, by rfl⟩ : syracuseStep 2864251 = 4296377) B4296377
theorem B3819001 : Blo 2261435 3819001 := bstep (se 2 (by rfl) ⟨1432125, by rfl⟩ : syracuseStep 3819001 = 2864251) B2864251
theorem B5092001 : Blo 2261435 5092001 := bstep (se 2 (by rfl) ⟨1909500, by rfl⟩ : syracuseStep 5092001 = 3819001) B3819001
theorem B3394667 : Blo 2261435 3394667 := bstep (se 1 (by rfl) ⟨2546000, by rfl⟩ : syracuseStep 3394667 = 5092001) B5092001
theorem B2263111 : Blo 2261435 2263111 := bstep (se 1 (by rfl) ⟨1697333, by rfl⟩ : syracuseStep 2263111 = 3394667) B3394667
theorem B2546005 : Blo 2261435 2546005 := bbase (se 10 (by rfl) ⟨3729, by rfl⟩ : syracuseStep 2546005 = 7459) (by norm_num)
theorem B3394673 : Blo 2261435 3394673 := bstep (se 2 (by rfl) ⟨1273002, by rfl⟩ : syracuseStep 3394673 = 2546005) B2546005
theorem B2263115 : Blo 2261435 2263115 := bstep (se 1 (by rfl) ⟨1697336, by rfl⟩ : syracuseStep 2263115 = 3394673) B3394673
theorem B2864261 : Blo 2261435 2864261 := bbase (se 4 (by rfl) ⟨268524, by rfl⟩ : syracuseStep 2864261 = 537049) (by norm_num)
theorem B7638029 : Blo 2261435 7638029 := bstep (se 3 (by rfl) ⟨1432130, by rfl⟩ : syracuseStep 7638029 = 2864261) B2864261
theorem B5092019 : Blo 2261435 5092019 := bstep (se 1 (by rfl) ⟨3819014, by rfl⟩ : syracuseStep 5092019 = 7638029) B7638029
theorem B3394679 : Blo 2261435 3394679 := bstep (se 1 (by rfl) ⟨2546009, by rfl⟩ : syracuseStep 3394679 = 5092019) B5092019
theorem B2263119 : Blo 2261435 2263119 := bstep (se 1 (by rfl) ⟨1697339, by rfl⟩ : syracuseStep 2263119 = 3394679) B3394679
theorem B3394685 : Blo 2261435 3394685 := bbase (se 3 (by rfl) ⟨636503, by rfl⟩ : syracuseStep 3394685 = 1273007) (by norm_num)
theorem B2263123 : Blo 2261435 2263123 := bstep (se 1 (by rfl) ⟨1697342, by rfl⟩ : syracuseStep 2263123 = 3394685) B3394685
theorem B5092037 : Blo 2261435 5092037 := bbase (se 4 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 5092037 = 954757) (by norm_num)
theorem B3394691 : Blo 2261435 3394691 := bstep (se 1 (by rfl) ⟨2546018, by rfl⟩ : syracuseStep 3394691 = 5092037) B5092037
theorem B2263127 : Blo 2261435 2263127 := bstep (se 1 (by rfl) ⟨1697345, by rfl⟩ : syracuseStep 2263127 = 3394691) B3394691
theorem B2580761 : Blo 2261435 2580761 := bbase (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) (by norm_num)
theorem B6882029 : Blo 2261435 6882029 := bstep (se 3 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 6882029 = 2580761) B2580761
theorem B4588019 : Blo 2261435 4588019 := bstep (se 1 (by rfl) ⟨3441014, by rfl⟩ : syracuseStep 4588019 = 6882029) B6882029
theorem B3058679 : Blo 2261435 3058679 := bstep (se 1 (by rfl) ⟨2294009, by rfl⟩ : syracuseStep 3058679 = 4588019) B4588019
theorem B8156477 : Blo 2261435 8156477 := bstep (se 3 (by rfl) ⟨1529339, by rfl⟩ : syracuseStep 8156477 = 3058679) B3058679
theorem B21750605 : Blo 2261435 21750605 := bstep (se 3 (by rfl) ⟨4078238, by rfl⟩ : syracuseStep 21750605 = 8156477) B8156477
theorem B14500403 : Blo 2261435 14500403 := bstep (se 1 (by rfl) ⟨10875302, by rfl⟩ : syracuseStep 14500403 = 21750605) B21750605
theorem B9666935 : Blo 2261435 9666935 := bstep (se 1 (by rfl) ⟨7250201, by rfl⟩ : syracuseStep 9666935 = 14500403) B14500403
theorem B6444623 : Blo 2261435 6444623 := bstep (se 1 (by rfl) ⟨4833467, by rfl⟩ : syracuseStep 6444623 = 9666935) B9666935
theorem B4296415 : Blo 2261435 4296415 := bstep (se 1 (by rfl) ⟨3222311, by rfl⟩ : syracuseStep 4296415 = 6444623) B6444623
theorem B5728553 : Blo 2261435 5728553 := bstep (se 2 (by rfl) ⟨2148207, by rfl⟩ : syracuseStep 5728553 = 4296415) B4296415
theorem B3819035 : Blo 2261435 3819035 := bstep (se 1 (by rfl) ⟨2864276, by rfl⟩ : syracuseStep 3819035 = 5728553) B5728553
theorem B2546023 : Blo 2261435 2546023 := bstep (se 1 (by rfl) ⟨1909517, by rfl⟩ : syracuseStep 2546023 = 3819035) B3819035
theorem B3394697 : Blo 2261435 3394697 := bstep (se 2 (by rfl) ⟨1273011, by rfl⟩ : syracuseStep 3394697 = 2546023) B2546023
theorem B2263131 : Blo 2261435 2263131 := bstep (se 1 (by rfl) ⟨1697348, by rfl⟩ : syracuseStep 2263131 = 3394697) B3394697
theorem B11457125 : Blo 2261435 11457125 := bbase (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) (by norm_num)
theorem B7638083 : Blo 2261435 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B5092055 : Blo 2261435 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B3394703 : Blo 2261435 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2263135 : Blo 2261435 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B3394709 : Blo 2261435 3394709 := bbase (se 6 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 3394709 = 159127) (by norm_num)
theorem B2263139 : Blo 2261435 2263139 := bstep (se 1 (by rfl) ⟨1697354, by rfl⟩ : syracuseStep 2263139 = 3394709) B3394709
theorem B29396629 : Blo 2261435 29396629 := bbase (se 6 (by rfl) ⟨688983, by rfl⟩ : syracuseStep 29396629 = 1377967) (by norm_num)
theorem B39195505 : Blo 2261435 39195505 := bstep (se 2 (by rfl) ⟨14698314, by rfl⟩ : syracuseStep 39195505 = 29396629) B29396629
theorem B52260673 : Blo 2261435 52260673 := bstep (se 2 (by rfl) ⟨19597752, by rfl⟩ : syracuseStep 52260673 = 39195505) B39195505
theorem B69680897 : Blo 2261435 69680897 := bstep (se 2 (by rfl) ⟨26130336, by rfl⟩ : syracuseStep 69680897 = 52260673) B52260673
theorem B46453931 : Blo 2261435 46453931 := bstep (se 1 (by rfl) ⟨34840448, by rfl⟩ : syracuseStep 46453931 = 69680897) B69680897
theorem B30969287 : Blo 2261435 30969287 := bstep (se 1 (by rfl) ⟨23226965, by rfl⟩ : syracuseStep 30969287 = 46453931) B46453931
theorem B20646191 : Blo 2261435 20646191 := bstep (se 1 (by rfl) ⟨15484643, by rfl⟩ : syracuseStep 20646191 = 30969287) B30969287
theorem B55056509 : Blo 2261435 55056509 := bstep (se 3 (by rfl) ⟨10323095, by rfl⟩ : syracuseStep 55056509 = 20646191) B20646191
theorem B36704339 : Blo 2261435 36704339 := bstep (se 1 (by rfl) ⟨27528254, by rfl⟩ : syracuseStep 36704339 = 55056509) B55056509
theorem B24469559 : Blo 2261435 24469559 := bstep (se 1 (by rfl) ⟨18352169, by rfl⟩ : syracuseStep 24469559 = 36704339) B36704339
theorem B16313039 : Blo 2261435 16313039 := bstep (se 1 (by rfl) ⟨12234779, by rfl⟩ : syracuseStep 16313039 = 24469559) B24469559
theorem B10875359 : Blo 2261435 10875359 := bstep (se 1 (by rfl) ⟨8156519, by rfl⟩ : syracuseStep 10875359 = 16313039) B16313039
theorem B7250239 : Blo 2261435 7250239 := bstep (se 1 (by rfl) ⟨5437679, by rfl⟩ : syracuseStep 7250239 = 10875359) B10875359
theorem B9666985 : Blo 2261435 9666985 := bstep (se 2 (by rfl) ⟨3625119, by rfl⟩ : syracuseStep 9666985 = 7250239) B7250239
theorem B12889313 : Blo 2261435 12889313 := bstep (se 2 (by rfl) ⟨4833492, by rfl⟩ : syracuseStep 12889313 = 9666985) B9666985
theorem B8592875 : Blo 2261435 8592875 := bstep (se 1 (by rfl) ⟨6444656, by rfl⟩ : syracuseStep 8592875 = 12889313) B12889313
theorem B5728583 : Blo 2261435 5728583 := bstep (se 1 (by rfl) ⟨4296437, by rfl⟩ : syracuseStep 5728583 = 8592875) B8592875
theorem B3819055 : Blo 2261435 3819055 := bstep (se 1 (by rfl) ⟨2864291, by rfl⟩ : syracuseStep 3819055 = 5728583) B5728583
theorem B5092073 : Blo 2261435 5092073 := bstep (se 2 (by rfl) ⟨1909527, by rfl⟩ : syracuseStep 5092073 = 3819055) B3819055
theorem B3394715 : Blo 2261435 3394715 := bstep (se 1 (by rfl) ⟨2546036, by rfl⟩ : syracuseStep 3394715 = 5092073) B5092073
theorem B2263143 : Blo 2261435 2263143 := bstep (se 1 (by rfl) ⟨1697357, by rfl⟩ : syracuseStep 2263143 = 3394715) B3394715
theorem B2546041 : Blo 2261435 2546041 := bbase (se 2 (by rfl) ⟨954765, by rfl⟩ : syracuseStep 2546041 = 1909531) (by norm_num)
theorem B3394721 : Blo 2261435 3394721 := bstep (se 2 (by rfl) ⟨1273020, by rfl⟩ : syracuseStep 3394721 = 2546041) B2546041
theorem B2263147 : Blo 2261435 2263147 := bstep (se 1 (by rfl) ⟨1697360, by rfl⟩ : syracuseStep 2263147 = 3394721) B3394721
theorem B10875397 : Blo 2261435 10875397 := bbase (se 4 (by rfl) ⟨1019568, by rfl⟩ : syracuseStep 10875397 = 2039137) (by norm_num)
theorem B14500529 : Blo 2261435 14500529 := bstep (se 2 (by rfl) ⟨5437698, by rfl⟩ : syracuseStep 14500529 = 10875397) B10875397
theorem B9667019 : Blo 2261435 9667019 := bstep (se 1 (by rfl) ⟨7250264, by rfl⟩ : syracuseStep 9667019 = 14500529) B14500529
theorem B6444679 : Blo 2261435 6444679 := bstep (se 1 (by rfl) ⟨4833509, by rfl⟩ : syracuseStep 6444679 = 9667019) B9667019
theorem B8592905 : Blo 2261435 8592905 := bstep (se 2 (by rfl) ⟨3222339, by rfl⟩ : syracuseStep 8592905 = 6444679) B6444679
theorem B5728603 : Blo 2261435 5728603 := bstep (se 1 (by rfl) ⟨4296452, by rfl⟩ : syracuseStep 5728603 = 8592905) B8592905
theorem B7638137 : Blo 2261435 7638137 := bstep (se 2 (by rfl) ⟨2864301, by rfl⟩ : syracuseStep 7638137 = 5728603) B5728603
theorem B5092091 : Blo 2261435 5092091 := bstep (se 1 (by rfl) ⟨3819068, by rfl⟩ : syracuseStep 5092091 = 7638137) B7638137
theorem B3394727 : Blo 2261435 3394727 := bstep (se 1 (by rfl) ⟨2546045, by rfl⟩ : syracuseStep 3394727 = 5092091) B5092091
theorem B2263151 : Blo 2261435 2263151 := bstep (se 1 (by rfl) ⟨1697363, by rfl⟩ : syracuseStep 2263151 = 3394727) B3394727
theorem B3394733 : Blo 2261435 3394733 := bbase (se 3 (by rfl) ⟨636512, by rfl⟩ : syracuseStep 3394733 = 1273025) (by norm_num)
theorem B2263155 : Blo 2261435 2263155 := bstep (se 1 (by rfl) ⟨1697366, by rfl⟩ : syracuseStep 2263155 = 3394733) B3394733
theorem B5092109 : Blo 2261435 5092109 := bbase (se 3 (by rfl) ⟨954770, by rfl⟩ : syracuseStep 5092109 = 1909541) (by norm_num)
theorem B3394739 : Blo 2261435 3394739 := bstep (se 1 (by rfl) ⟨2546054, by rfl⟩ : syracuseStep 3394739 = 5092109) B5092109
theorem B2263159 : Blo 2261435 2263159 := bstep (se 1 (by rfl) ⟨1697369, by rfl⟩ : syracuseStep 2263159 = 3394739) B3394739
theorem B2864317 : Blo 2261435 2864317 := bbase (se 3 (by rfl) ⟨537059, by rfl⟩ : syracuseStep 2864317 = 1074119) (by norm_num)
theorem B3819089 : Blo 2261435 3819089 := bstep (se 2 (by rfl) ⟨1432158, by rfl⟩ : syracuseStep 3819089 = 2864317) B2864317
theorem B2546059 : Blo 2261435 2546059 := bstep (se 1 (by rfl) ⟨1909544, by rfl⟩ : syracuseStep 2546059 = 3819089) B3819089
theorem B3394745 : Blo 2261435 3394745 := bstep (se 2 (by rfl) ⟨1273029, by rfl⟩ : syracuseStep 3394745 = 2546059) B2546059
theorem B2263163 : Blo 2261435 2263163 := bstep (se 1 (by rfl) ⟨1697372, by rfl⟩ : syracuseStep 2263163 = 3394745) B3394745
theorem B7742405 : Blo 2261435 7742405 := bbase (se 4 (by rfl) ⟨725850, by rfl⟩ : syracuseStep 7742405 = 1451701) (by norm_num)
theorem B5161603 : Blo 2261435 5161603 := bstep (se 1 (by rfl) ⟨3871202, by rfl⟩ : syracuseStep 5161603 = 7742405) B7742405
theorem B6882137 : Blo 2261435 6882137 := bstep (se 2 (by rfl) ⟨2580801, by rfl⟩ : syracuseStep 6882137 = 5161603) B5161603
theorem B4588091 : Blo 2261435 4588091 := bstep (se 1 (by rfl) ⟨3441068, by rfl⟩ : syracuseStep 4588091 = 6882137) B6882137
theorem B3058727 : Blo 2261435 3058727 := bstep (se 1 (by rfl) ⟨2294045, by rfl⟩ : syracuseStep 3058727 = 4588091) B4588091
theorem B8156605 : Blo 2261435 8156605 := bstep (se 3 (by rfl) ⟨1529363, by rfl⟩ : syracuseStep 8156605 = 3058727) B3058727
theorem B10875473 : Blo 2261435 10875473 := bstep (se 2 (by rfl) ⟨4078302, by rfl⟩ : syracuseStep 10875473 = 8156605) B8156605
theorem B7250315 : Blo 2261435 7250315 := bstep (se 1 (by rfl) ⟨5437736, by rfl⟩ : syracuseStep 7250315 = 10875473) B10875473
theorem B19334173 : Blo 2261435 19334173 := bstep (se 3 (by rfl) ⟨3625157, by rfl⟩ : syracuseStep 19334173 = 7250315) B7250315
theorem B25778897 : Blo 2261435 25778897 := bstep (se 2 (by rfl) ⟨9667086, by rfl⟩ : syracuseStep 25778897 = 19334173) B19334173
theorem B17185931 : Blo 2261435 17185931 := bstep (se 1 (by rfl) ⟨12889448, by rfl⟩ : syracuseStep 17185931 = 25778897) B25778897
theorem B11457287 : Blo 2261435 11457287 := bstep (se 1 (by rfl) ⟨8592965, by rfl⟩ : syracuseStep 11457287 = 17185931) B17185931
theorem B7638191 : Blo 2261435 7638191 := bstep (se 1 (by rfl) ⟨5728643, by rfl⟩ : syracuseStep 7638191 = 11457287) B11457287
theorem B5092127 : Blo 2261435 5092127 := bstep (se 1 (by rfl) ⟨3819095, by rfl⟩ : syracuseStep 5092127 = 7638191) B7638191
theorem B3394751 : Blo 2261435 3394751 := bstep (se 1 (by rfl) ⟨2546063, by rfl⟩ : syracuseStep 3394751 = 5092127) B5092127
theorem B2263167 : Blo 2261435 2263167 := bstep (se 1 (by rfl) ⟨1697375, by rfl⟩ : syracuseStep 2263167 = 3394751) B3394751
theorem B3394757 : Blo 2261435 3394757 := bbase (se 4 (by rfl) ⟨318258, by rfl⟩ : syracuseStep 3394757 = 636517) (by norm_num)
theorem B2263171 : Blo 2261435 2263171 := bstep (se 1 (by rfl) ⟨1697378, by rfl⟩ : syracuseStep 2263171 = 3394757) B3394757
theorem B3819109 : Blo 2261435 3819109 := bbase (se 4 (by rfl) ⟨358041, by rfl⟩ : syracuseStep 3819109 = 716083) (by norm_num)
theorem B5092145 : Blo 2261435 5092145 := bstep (se 2 (by rfl) ⟨1909554, by rfl⟩ : syracuseStep 5092145 = 3819109) B3819109
theorem B3394763 : Blo 2261435 3394763 := bstep (se 1 (by rfl) ⟨2546072, by rfl⟩ : syracuseStep 3394763 = 5092145) B5092145
theorem B2263175 : Blo 2261435 2263175 := bstep (se 1 (by rfl) ⟨1697381, by rfl⟩ : syracuseStep 2263175 = 3394763) B3394763
theorem B2546077 : Blo 2261435 2546077 := bbase (se 3 (by rfl) ⟨477389, by rfl⟩ : syracuseStep 2546077 = 954779) (by norm_num)
theorem B3394769 : Blo 2261435 3394769 := bstep (se 2 (by rfl) ⟨1273038, by rfl⟩ : syracuseStep 3394769 = 2546077) B2546077
theorem B2263179 : Blo 2261435 2263179 := bstep (se 1 (by rfl) ⟨1697384, by rfl⟩ : syracuseStep 2263179 = 3394769) B3394769
theorem B7638245 : Blo 2261435 7638245 := bbase (se 4 (by rfl) ⟨716085, by rfl⟩ : syracuseStep 7638245 = 1432171) (by norm_num)
theorem B5092163 : Blo 2261435 5092163 := bstep (se 1 (by rfl) ⟨3819122, by rfl⟩ : syracuseStep 5092163 = 7638245) B7638245
theorem B3394775 : Blo 2261435 3394775 := bstep (se 1 (by rfl) ⟨2546081, by rfl⟩ : syracuseStep 3394775 = 5092163) B5092163
theorem B2263183 : Blo 2261435 2263183 := bstep (se 1 (by rfl) ⟨1697387, by rfl⟩ : syracuseStep 2263183 = 3394775) B3394775
theorem B3394781 : Blo 2261435 3394781 := bbase (se 3 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 3394781 = 1273043) (by norm_num)
theorem B2263187 : Blo 2261435 2263187 := bstep (se 1 (by rfl) ⟨1697390, by rfl⟩ : syracuseStep 2263187 = 3394781) B3394781
theorem B5092181 : Blo 2261435 5092181 := bbase (se 9 (by rfl) ⟨14918, by rfl⟩ : syracuseStep 5092181 = 29837) (by norm_num)
theorem B3394787 : Blo 2261435 3394787 := bstep (se 1 (by rfl) ⟨2546090, by rfl⟩ : syracuseStep 3394787 = 5092181) B5092181
theorem B2263191 : Blo 2261435 2263191 := bstep (se 1 (by rfl) ⟨1697393, by rfl⟩ : syracuseStep 2263191 = 3394787) B3394787
theorem B6444805 : Blo 2261435 6444805 := bbase (se 4 (by rfl) ⟨604200, by rfl⟩ : syracuseStep 6444805 = 1208401) (by norm_num)
theorem B8593073 : Blo 2261435 8593073 := bstep (se 2 (by rfl) ⟨3222402, by rfl⟩ : syracuseStep 8593073 = 6444805) B6444805
theorem B5728715 : Blo 2261435 5728715 := bstep (se 1 (by rfl) ⟨4296536, by rfl⟩ : syracuseStep 5728715 = 8593073) B8593073
theorem B3819143 : Blo 2261435 3819143 := bstep (se 1 (by rfl) ⟨2864357, by rfl⟩ : syracuseStep 3819143 = 5728715) B5728715
theorem B2546095 : Blo 2261435 2546095 := bstep (se 1 (by rfl) ⟨1909571, by rfl⟩ : syracuseStep 2546095 = 3819143) B3819143
theorem B3394793 : Blo 2261435 3394793 := bstep (se 2 (by rfl) ⟨1273047, by rfl⟩ : syracuseStep 3394793 = 2546095) B2546095
theorem B2263195 : Blo 2261435 2263195 := bstep (se 1 (by rfl) ⟨1697396, by rfl⟩ : syracuseStep 2263195 = 3394793) B3394793
theorem B41293397 : Blo 2261435 41293397 := bbase (se 8 (by rfl) ⟨241953, by rfl⟩ : syracuseStep 41293397 = 483907) (by norm_num)
theorem B27528931 : Blo 2261435 27528931 := bstep (se 1 (by rfl) ⟨20646698, by rfl⟩ : syracuseStep 27528931 = 41293397) B41293397
theorem B36705241 : Blo 2261435 36705241 := bstep (se 2 (by rfl) ⟨13764465, by rfl⟩ : syracuseStep 36705241 = 27528931) B27528931
theorem B48940321 : Blo 2261435 48940321 := bstep (se 2 (by rfl) ⟨18352620, by rfl⟩ : syracuseStep 48940321 = 36705241) B36705241
theorem B65253761 : Blo 2261435 65253761 := bstep (se 2 (by rfl) ⟨24470160, by rfl⟩ : syracuseStep 65253761 = 48940321) B48940321
theorem B43502507 : Blo 2261435 43502507 := bstep (se 1 (by rfl) ⟨32626880, by rfl⟩ : syracuseStep 43502507 = 65253761) B65253761
theorem B29001671 : Blo 2261435 29001671 := bstep (se 1 (by rfl) ⟨21751253, by rfl⟩ : syracuseStep 29001671 = 43502507) B43502507
theorem B19334447 : Blo 2261435 19334447 := bstep (se 1 (by rfl) ⟨14500835, by rfl⟩ : syracuseStep 19334447 = 29001671) B29001671
theorem B12889631 : Blo 2261435 12889631 := bstep (se 1 (by rfl) ⟨9667223, by rfl⟩ : syracuseStep 12889631 = 19334447) B19334447
theorem B8593087 : Blo 2261435 8593087 := bstep (se 1 (by rfl) ⟨6444815, by rfl⟩ : syracuseStep 8593087 = 12889631) B12889631
theorem B11457449 : Blo 2261435 11457449 := bstep (se 2 (by rfl) ⟨4296543, by rfl⟩ : syracuseStep 11457449 = 8593087) B8593087
theorem B7638299 : Blo 2261435 7638299 := bstep (se 1 (by rfl) ⟨5728724, by rfl⟩ : syracuseStep 7638299 = 11457449) B11457449
theorem B5092199 : Blo 2261435 5092199 := bstep (se 1 (by rfl) ⟨3819149, by rfl⟩ : syracuseStep 5092199 = 7638299) B7638299
theorem B3394799 : Blo 2261435 3394799 := bstep (se 1 (by rfl) ⟨2546099, by rfl⟩ : syracuseStep 3394799 = 5092199) B5092199
theorem B2263199 : Blo 2261435 2263199 := bstep (se 1 (by rfl) ⟨1697399, by rfl⟩ : syracuseStep 2263199 = 3394799) B3394799
theorem B3394805 : Blo 2261435 3394805 := bbase (se 5 (by rfl) ⟨159131, by rfl⟩ : syracuseStep 3394805 = 318263) (by norm_num)
theorem B2263203 : Blo 2261435 2263203 := bstep (se 1 (by rfl) ⟨1697402, by rfl⟩ : syracuseStep 2263203 = 3394805) B3394805
theorem B9799157 : Blo 2261435 9799157 := bbase (se 5 (by rfl) ⟨459335, by rfl⟩ : syracuseStep 9799157 = 918671) (by norm_num)
theorem B6532771 : Blo 2261435 6532771 := bstep (se 1 (by rfl) ⟨4899578, by rfl⟩ : syracuseStep 6532771 = 9799157) B9799157
theorem B8710361 : Blo 2261435 8710361 := bstep (se 2 (by rfl) ⟨3266385, by rfl⟩ : syracuseStep 8710361 = 6532771) B6532771
theorem B5806907 : Blo 2261435 5806907 := bstep (se 1 (by rfl) ⟨4355180, by rfl⟩ : syracuseStep 5806907 = 8710361) B8710361
theorem B3871271 : Blo 2261435 3871271 := bstep (se 1 (by rfl) ⟨2903453, by rfl⟩ : syracuseStep 3871271 = 5806907) B5806907
theorem B10323389 : Blo 2261435 10323389 := bstep (se 3 (by rfl) ⟨1935635, by rfl⟩ : syracuseStep 10323389 = 3871271) B3871271
theorem B6882259 : Blo 2261435 6882259 := bstep (se 1 (by rfl) ⟨5161694, by rfl⟩ : syracuseStep 6882259 = 10323389) B10323389
theorem B9176345 : Blo 2261435 9176345 := bstep (se 2 (by rfl) ⟨3441129, by rfl⟩ : syracuseStep 9176345 = 6882259) B6882259
theorem B6117563 : Blo 2261435 6117563 := bstep (se 1 (by rfl) ⟨4588172, by rfl⟩ : syracuseStep 6117563 = 9176345) B9176345
theorem B16313501 : Blo 2261435 16313501 := bstep (se 3 (by rfl) ⟨3058781, by rfl⟩ : syracuseStep 16313501 = 6117563) B6117563
theorem B10875667 : Blo 2261435 10875667 := bstep (se 1 (by rfl) ⟨8156750, by rfl⟩ : syracuseStep 10875667 = 16313501) B16313501
theorem B14500889 : Blo 2261435 14500889 := bstep (se 2 (by rfl) ⟨5437833, by rfl⟩ : syracuseStep 14500889 = 10875667) B10875667
theorem B9667259 : Blo 2261435 9667259 := bstep (se 1 (by rfl) ⟨7250444, by rfl⟩ : syracuseStep 9667259 = 14500889) B14500889
theorem B6444839 : Blo 2261435 6444839 := bstep (se 1 (by rfl) ⟨4833629, by rfl⟩ : syracuseStep 6444839 = 9667259) B9667259
theorem B4296559 : Blo 2261435 4296559 := bstep (se 1 (by rfl) ⟨3222419, by rfl⟩ : syracuseStep 4296559 = 6444839) B6444839
theorem B5728745 : Blo 2261435 5728745 := bstep (se 2 (by rfl) ⟨2148279, by rfl⟩ : syracuseStep 5728745 = 4296559) B4296559
theorem B3819163 : Blo 2261435 3819163 := bstep (se 1 (by rfl) ⟨2864372, by rfl⟩ : syracuseStep 3819163 = 5728745) B5728745
theorem B5092217 : Blo 2261435 5092217 := bstep (se 2 (by rfl) ⟨1909581, by rfl⟩ : syracuseStep 5092217 = 3819163) B3819163
theorem B3394811 : Blo 2261435 3394811 := bstep (se 1 (by rfl) ⟨2546108, by rfl⟩ : syracuseStep 3394811 = 5092217) B5092217
theorem B2263207 : Blo 2261435 2263207 := bstep (se 1 (by rfl) ⟨1697405, by rfl⟩ : syracuseStep 2263207 = 3394811) B3394811
theorem B2546113 : Blo 2261435 2546113 := bbase (se 2 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 2546113 = 1909585) (by norm_num)
theorem B3394817 : Blo 2261435 3394817 := bstep (se 2 (by rfl) ⟨1273056, by rfl⟩ : syracuseStep 3394817 = 2546113) B2546113
theorem B2263211 : Blo 2261435 2263211 := bstep (se 1 (by rfl) ⟨1697408, by rfl⟩ : syracuseStep 2263211 = 3394817) B3394817
theorem B5728765 : Blo 2261435 5728765 := bbase (se 3 (by rfl) ⟨1074143, by rfl⟩ : syracuseStep 5728765 = 2148287) (by norm_num)
theorem B7638353 : Blo 2261435 7638353 := bstep (se 2 (by rfl) ⟨2864382, by rfl⟩ : syracuseStep 7638353 = 5728765) B5728765
theorem B5092235 : Blo 2261435 5092235 := bstep (se 1 (by rfl) ⟨3819176, by rfl⟩ : syracuseStep 5092235 = 7638353) B7638353
theorem B3394823 : Blo 2261435 3394823 := bstep (se 1 (by rfl) ⟨2546117, by rfl⟩ : syracuseStep 3394823 = 5092235) B5092235
theorem B2263215 : Blo 2261435 2263215 := bstep (se 1 (by rfl) ⟨1697411, by rfl⟩ : syracuseStep 2263215 = 3394823) B3394823
theorem B3394829 : Blo 2261435 3394829 := bbase (se 3 (by rfl) ⟨636530, by rfl⟩ : syracuseStep 3394829 = 1273061) (by norm_num)
theorem B2263219 : Blo 2261435 2263219 := bstep (se 1 (by rfl) ⟨1697414, by rfl⟩ : syracuseStep 2263219 = 3394829) B3394829
theorem B5092253 : Blo 2261435 5092253 := bbase (se 3 (by rfl) ⟨954797, by rfl⟩ : syracuseStep 5092253 = 1909595) (by norm_num)
theorem B3394835 : Blo 2261435 3394835 := bstep (se 1 (by rfl) ⟨2546126, by rfl⟩ : syracuseStep 3394835 = 5092253) B5092253
theorem B2263223 : Blo 2261435 2263223 := bstep (se 1 (by rfl) ⟨1697417, by rfl⟩ : syracuseStep 2263223 = 3394835) B3394835
theorem B3819197 : Blo 2261435 3819197 := bbase (se 3 (by rfl) ⟨716099, by rfl⟩ : syracuseStep 3819197 = 1432199) (by norm_num)
theorem B2546131 : Blo 2261435 2546131 := bstep (se 1 (by rfl) ⟨1909598, by rfl⟩ : syracuseStep 2546131 = 3819197) B3819197
theorem B3394841 : Blo 2261435 3394841 := bstep (se 2 (by rfl) ⟨1273065, by rfl⟩ : syracuseStep 3394841 = 2546131) B2546131
theorem B2263227 : Blo 2261435 2263227 := bstep (se 1 (by rfl) ⟨1697420, by rfl⟩ : syracuseStep 2263227 = 3394841) B3394841
theorem B12889813 : Blo 2261435 12889813 := bbase (se 7 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 12889813 = 302105) (by norm_num)
theorem B17186417 : Blo 2261435 17186417 := bstep (se 2 (by rfl) ⟨6444906, by rfl⟩ : syracuseStep 17186417 = 12889813) B12889813
theorem B11457611 : Blo 2261435 11457611 := bstep (se 1 (by rfl) ⟨8593208, by rfl⟩ : syracuseStep 11457611 = 17186417) B17186417
theorem B7638407 : Blo 2261435 7638407 := bstep (se 1 (by rfl) ⟨5728805, by rfl⟩ : syracuseStep 7638407 = 11457611) B11457611
theorem B5092271 : Blo 2261435 5092271 := bstep (se 1 (by rfl) ⟨3819203, by rfl⟩ : syracuseStep 5092271 = 7638407) B7638407
theorem B3394847 : Blo 2261435 3394847 := bstep (se 1 (by rfl) ⟨2546135, by rfl⟩ : syracuseStep 3394847 = 5092271) B5092271
theorem B2263231 : Blo 2261435 2263231 := bstep (se 1 (by rfl) ⟨1697423, by rfl⟩ : syracuseStep 2263231 = 3394847) B3394847
theorem B3394853 : Blo 2261435 3394853 := bbase (se 4 (by rfl) ⟨318267, by rfl⟩ : syracuseStep 3394853 = 636535) (by norm_num)
theorem B2263235 : Blo 2261435 2263235 := bstep (se 1 (by rfl) ⟨1697426, by rfl⟩ : syracuseStep 2263235 = 3394853) B3394853
theorem B2864413 : Blo 2261435 2864413 := bbase (se 3 (by rfl) ⟨537077, by rfl⟩ : syracuseStep 2864413 = 1074155) (by norm_num)
theorem B3819217 : Blo 2261435 3819217 := bstep (se 2 (by rfl) ⟨1432206, by rfl⟩ : syracuseStep 3819217 = 2864413) B2864413
theorem B5092289 : Blo 2261435 5092289 := bstep (se 2 (by rfl) ⟨1909608, by rfl⟩ : syracuseStep 5092289 = 3819217) B3819217
theorem B3394859 : Blo 2261435 3394859 := bstep (se 1 (by rfl) ⟨2546144, by rfl⟩ : syracuseStep 3394859 = 5092289) B5092289
theorem B2263239 : Blo 2261435 2263239 := bstep (se 1 (by rfl) ⟨1697429, by rfl⟩ : syracuseStep 2263239 = 3394859) B3394859
theorem B2546149 : Blo 2261435 2546149 := bbase (se 4 (by rfl) ⟨238701, by rfl⟩ : syracuseStep 2546149 = 477403) (by norm_num)
theorem B3394865 : Blo 2261435 3394865 := bstep (se 2 (by rfl) ⟨1273074, by rfl⟩ : syracuseStep 3394865 = 2546149) B2546149
theorem B2263243 : Blo 2261435 2263243 := bstep (se 1 (by rfl) ⟨1697432, by rfl⟩ : syracuseStep 2263243 = 3394865) B3394865
theorem B2718965 : Blo 2261435 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B7250573 : Blo 2261435 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B4833715 : Blo 2261435 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B6444953 : Blo 2261435 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B4296635 : Blo 2261435 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B2864423 : Blo 2261435 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B7638461 : Blo 2261435 7638461 := bstep (se 3 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 7638461 = 2864423) B2864423
theorem B5092307 : Blo 2261435 5092307 := bstep (se 1 (by rfl) ⟨3819230, by rfl⟩ : syracuseStep 5092307 = 7638461) B7638461
theorem B3394871 : Blo 2261435 3394871 := bstep (se 1 (by rfl) ⟨2546153, by rfl⟩ : syracuseStep 3394871 = 5092307) B5092307
theorem B2263247 : Blo 2261435 2263247 := bstep (se 1 (by rfl) ⟨1697435, by rfl⟩ : syracuseStep 2263247 = 3394871) B3394871
theorem B3394877 : Blo 2261435 3394877 := bbase (se 3 (by rfl) ⟨636539, by rfl⟩ : syracuseStep 3394877 = 1273079) (by norm_num)
theorem B2263251 : Blo 2261435 2263251 := bstep (se 1 (by rfl) ⟨1697438, by rfl⟩ : syracuseStep 2263251 = 3394877) B3394877
theorem B5092325 : Blo 2261435 5092325 := bbase (se 4 (by rfl) ⟨477405, by rfl⟩ : syracuseStep 5092325 = 954811) (by norm_num)
theorem B3394883 : Blo 2261435 3394883 := bstep (se 1 (by rfl) ⟨2546162, by rfl⟩ : syracuseStep 3394883 = 5092325) B5092325
theorem B2263255 : Blo 2261435 2263255 := bstep (se 1 (by rfl) ⟨1697441, by rfl⟩ : syracuseStep 2263255 = 3394883) B3394883
theorem B5728877 : Blo 2261435 5728877 := bbase (se 3 (by rfl) ⟨1074164, by rfl⟩ : syracuseStep 5728877 = 2148329) (by norm_num)
theorem B3819251 : Blo 2261435 3819251 := bstep (se 1 (by rfl) ⟨2864438, by rfl⟩ : syracuseStep 3819251 = 5728877) B5728877
theorem B2546167 : Blo 2261435 2546167 := bstep (se 1 (by rfl) ⟨1909625, by rfl⟩ : syracuseStep 2546167 = 3819251) B3819251
theorem B3394889 : Blo 2261435 3394889 := bstep (se 2 (by rfl) ⟨1273083, by rfl⟩ : syracuseStep 3394889 = 2546167) B2546167
theorem B2263259 : Blo 2261435 2263259 := bstep (se 1 (by rfl) ⟨1697444, by rfl⟩ : syracuseStep 2263259 = 3394889) B3394889
theorem B4833749 : Blo 2261435 4833749 := bbase (se 7 (by rfl) ⟨56645, by rfl⟩ : syracuseStep 4833749 = 113291) (by norm_num)
theorem B3222499 : Blo 2261435 3222499 := bstep (se 1 (by rfl) ⟨2416874, by rfl⟩ : syracuseStep 3222499 = 4833749) B4833749
theorem B4296665 : Blo 2261435 4296665 := bstep (se 2 (by rfl) ⟨1611249, by rfl⟩ : syracuseStep 4296665 = 3222499) B3222499
theorem B11457773 : Blo 2261435 11457773 := bstep (se 3 (by rfl) ⟨2148332, by rfl⟩ : syracuseStep 11457773 = 4296665) B4296665
theorem B7638515 : Blo 2261435 7638515 := bstep (se 1 (by rfl) ⟨5728886, by rfl⟩ : syracuseStep 7638515 = 11457773) B11457773
theorem B5092343 : Blo 2261435 5092343 := bstep (se 1 (by rfl) ⟨3819257, by rfl⟩ : syracuseStep 5092343 = 7638515) B7638515
theorem B3394895 : Blo 2261435 3394895 := bstep (se 1 (by rfl) ⟨2546171, by rfl⟩ : syracuseStep 3394895 = 5092343) B5092343
theorem B2263263 : Blo 2261435 2263263 := bstep (se 1 (by rfl) ⟨1697447, by rfl⟩ : syracuseStep 2263263 = 3394895) B3394895
theorem B3394901 : Blo 2261435 3394901 := bbase (se 11 (by rfl) ⟨2486, by rfl⟩ : syracuseStep 3394901 = 4973) (by norm_num)
theorem B2263267 : Blo 2261435 2263267 := bstep (se 1 (by rfl) ⟨1697450, by rfl⟩ : syracuseStep 2263267 = 3394901) B3394901
theorem B3625325 : Blo 2261435 3625325 := bbase (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) (by norm_num)
theorem B2416883 : Blo 2261435 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B6445021 : Blo 2261435 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B8593361 : Blo 2261435 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B5728907 : Blo 2261435 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B3819271 : Blo 2261435 3819271 := bstep (se 1 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 3819271 = 5728907) B5728907
theorem B5092361 : Blo 2261435 5092361 := bstep (se 2 (by rfl) ⟨1909635, by rfl⟩ : syracuseStep 5092361 = 3819271) B3819271
theorem B3394907 : Blo 2261435 3394907 := bstep (se 1 (by rfl) ⟨2546180, by rfl⟩ : syracuseStep 3394907 = 5092361) B5092361
theorem B2263271 : Blo 2261435 2263271 := bstep (se 1 (by rfl) ⟨1697453, by rfl⟩ : syracuseStep 2263271 = 3394907) B3394907
theorem B2546185 : Blo 2261435 2546185 := bbase (se 2 (by rfl) ⟨954819, by rfl⟩ : syracuseStep 2546185 = 1909639) (by norm_num)
theorem B3394913 : Blo 2261435 3394913 := bstep (se 2 (by rfl) ⟨1273092, by rfl⟩ : syracuseStep 3394913 = 2546185) B2546185
theorem B2263275 : Blo 2261435 2263275 := bstep (se 1 (by rfl) ⟨1697456, by rfl⟩ : syracuseStep 2263275 = 3394913) B3394913
theorem B2903545 : Blo 2261435 2903545 := bbase (se 2 (by rfl) ⟨1088829, by rfl⟩ : syracuseStep 2903545 = 2177659) (by norm_num)
theorem B15485573 : Blo 2261435 15485573 := bstep (se 4 (by rfl) ⟨1451772, by rfl⟩ : syracuseStep 15485573 = 2903545) B2903545
theorem B10323715 : Blo 2261435 10323715 := bstep (se 1 (by rfl) ⟨7742786, by rfl⟩ : syracuseStep 10323715 = 15485573) B15485573
theorem B13764953 : Blo 2261435 13764953 := bstep (se 2 (by rfl) ⟨5161857, by rfl⟩ : syracuseStep 13764953 = 10323715) B10323715
theorem B9176635 : Blo 2261435 9176635 := bstep (se 1 (by rfl) ⟨6882476, by rfl⟩ : syracuseStep 9176635 = 13764953) B13764953
theorem B48942053 : Blo 2261435 48942053 := bstep (se 4 (by rfl) ⟨4588317, by rfl⟩ : syracuseStep 48942053 = 9176635) B9176635
theorem B32628035 : Blo 2261435 32628035 := bstep (se 1 (by rfl) ⟨24471026, by rfl⟩ : syracuseStep 32628035 = 48942053) B48942053
theorem B21752023 : Blo 2261435 21752023 := bstep (se 1 (by rfl) ⟨16314017, by rfl⟩ : syracuseStep 21752023 = 32628035) B32628035
theorem B29002697 : Blo 2261435 29002697 := bstep (se 2 (by rfl) ⟨10876011, by rfl⟩ : syracuseStep 29002697 = 21752023) B21752023
theorem B19335131 : Blo 2261435 19335131 := bstep (se 1 (by rfl) ⟨14501348, by rfl⟩ : syracuseStep 19335131 = 29002697) B29002697
theorem B12890087 : Blo 2261435 12890087 := bstep (se 1 (by rfl) ⟨9667565, by rfl⟩ : syracuseStep 12890087 = 19335131) B19335131
theorem B8593391 : Blo 2261435 8593391 := bstep (se 1 (by rfl) ⟨6445043, by rfl⟩ : syracuseStep 8593391 = 12890087) B12890087
theorem B5728927 : Blo 2261435 5728927 := bstep (se 1 (by rfl) ⟨4296695, by rfl⟩ : syracuseStep 5728927 = 8593391) B8593391
theorem B7638569 : Blo 2261435 7638569 := bstep (se 2 (by rfl) ⟨2864463, by rfl⟩ : syracuseStep 7638569 = 5728927) B5728927
theorem B5092379 : Blo 2261435 5092379 := bstep (se 1 (by rfl) ⟨3819284, by rfl⟩ : syracuseStep 5092379 = 7638569) B7638569
theorem B3394919 : Blo 2261435 3394919 := bstep (se 1 (by rfl) ⟨2546189, by rfl⟩ : syracuseStep 3394919 = 5092379) B5092379
theorem B2263279 : Blo 2261435 2263279 := bstep (se 1 (by rfl) ⟨1697459, by rfl⟩ : syracuseStep 2263279 = 3394919) B3394919
theorem B3394925 : Blo 2261435 3394925 := bbase (se 3 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 3394925 = 1273097) (by norm_num)
theorem B2263283 : Blo 2261435 2263283 := bstep (se 1 (by rfl) ⟨1697462, by rfl⟩ : syracuseStep 2263283 = 3394925) B3394925
theorem B5092397 : Blo 2261435 5092397 := bbase (se 3 (by rfl) ⟨954824, by rfl⟩ : syracuseStep 5092397 = 1909649) (by norm_num)
theorem B3394931 : Blo 2261435 3394931 := bstep (se 1 (by rfl) ⟨2546198, by rfl⟩ : syracuseStep 3394931 = 5092397) B5092397
theorem B2263287 : Blo 2261435 2263287 := bstep (se 1 (by rfl) ⟨1697465, by rfl⟩ : syracuseStep 2263287 = 3394931) B3394931
theorem B14501429 : Blo 2261435 14501429 := bbase (se 5 (by rfl) ⟨679754, by rfl⟩ : syracuseStep 14501429 = 1359509) (by norm_num)
theorem B9667619 : Blo 2261435 9667619 := bstep (se 1 (by rfl) ⟨7250714, by rfl⟩ : syracuseStep 9667619 = 14501429) B14501429
theorem B6445079 : Blo 2261435 6445079 := bstep (se 1 (by rfl) ⟨4833809, by rfl⟩ : syracuseStep 6445079 = 9667619) B9667619
theorem B4296719 : Blo 2261435 4296719 := bstep (se 1 (by rfl) ⟨3222539, by rfl⟩ : syracuseStep 4296719 = 6445079) B6445079
theorem B2864479 : Blo 2261435 2864479 := bstep (se 1 (by rfl) ⟨2148359, by rfl⟩ : syracuseStep 2864479 = 4296719) B4296719
theorem B3819305 : Blo 2261435 3819305 := bstep (se 2 (by rfl) ⟨1432239, by rfl⟩ : syracuseStep 3819305 = 2864479) B2864479
theorem B2546203 : Blo 2261435 2546203 := bstep (se 1 (by rfl) ⟨1909652, by rfl⟩ : syracuseStep 2546203 = 3819305) B3819305
theorem B3394937 : Blo 2261435 3394937 := bstep (se 2 (by rfl) ⟨1273101, by rfl⟩ : syracuseStep 3394937 = 2546203) B2546203
theorem B2263291 : Blo 2261435 2263291 := bstep (se 1 (by rfl) ⟨1697468, by rfl⟩ : syracuseStep 2263291 = 3394937) B3394937
theorem B7250725 : Blo 2261435 7250725 := bbase (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) (by norm_num)
theorem B38670533 : Blo 2261435 38670533 := bstep (se 4 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 38670533 = 7250725) B7250725
theorem B25780355 : Blo 2261435 25780355 := bstep (se 1 (by rfl) ⟨19335266, by rfl⟩ : syracuseStep 25780355 = 38670533) B38670533
theorem B17186903 : Blo 2261435 17186903 := bstep (se 1 (by rfl) ⟨12890177, by rfl⟩ : syracuseStep 17186903 = 25780355) B25780355
theorem B11457935 : Blo 2261435 11457935 := bstep (se 1 (by rfl) ⟨8593451, by rfl⟩ : syracuseStep 11457935 = 17186903) B17186903
theorem B7638623 : Blo 2261435 7638623 := bstep (se 1 (by rfl) ⟨5728967, by rfl⟩ : syracuseStep 7638623 = 11457935) B11457935
theorem B5092415 : Blo 2261435 5092415 := bstep (se 1 (by rfl) ⟨3819311, by rfl⟩ : syracuseStep 5092415 = 7638623) B7638623
theorem B3394943 : Blo 2261435 3394943 := bstep (se 1 (by rfl) ⟨2546207, by rfl⟩ : syracuseStep 3394943 = 5092415) B5092415
theorem B2263295 : Blo 2261435 2263295 := bstep (se 1 (by rfl) ⟨1697471, by rfl⟩ : syracuseStep 2263295 = 3394943) B3394943
theorem B3394949 : Blo 2261435 3394949 := bbase (se 4 (by rfl) ⟨318276, by rfl⟩ : syracuseStep 3394949 = 636553) (by norm_num)
theorem B2263299 : Blo 2261435 2263299 := bstep (se 1 (by rfl) ⟨1697474, by rfl⟩ : syracuseStep 2263299 = 3394949) B3394949
theorem B3819325 : Blo 2261435 3819325 := bbase (se 3 (by rfl) ⟨716123, by rfl⟩ : syracuseStep 3819325 = 1432247) (by norm_num)
theorem B5092433 : Blo 2261435 5092433 := bstep (se 2 (by rfl) ⟨1909662, by rfl⟩ : syracuseStep 5092433 = 3819325) B3819325
theorem B3394955 : Blo 2261435 3394955 := bstep (se 1 (by rfl) ⟨2546216, by rfl⟩ : syracuseStep 3394955 = 5092433) B5092433
theorem B2263303 : Blo 2261435 2263303 := bstep (se 1 (by rfl) ⟨1697477, by rfl⟩ : syracuseStep 2263303 = 3394955) B3394955
theorem B2546221 : Blo 2261435 2546221 := bbase (se 3 (by rfl) ⟨477416, by rfl⟩ : syracuseStep 2546221 = 954833) (by norm_num)
theorem B3394961 : Blo 2261435 3394961 := bstep (se 2 (by rfl) ⟨1273110, by rfl⟩ : syracuseStep 3394961 = 2546221) B2546221
theorem B2263307 : Blo 2261435 2263307 := bstep (se 1 (by rfl) ⟨1697480, by rfl⟩ : syracuseStep 2263307 = 3394961) B3394961
theorem B7638677 : Blo 2261435 7638677 := bbase (se 6 (by rfl) ⟨179031, by rfl⟩ : syracuseStep 7638677 = 358063) (by norm_num)
theorem B5092451 : Blo 2261435 5092451 := bstep (se 1 (by rfl) ⟨3819338, by rfl⟩ : syracuseStep 5092451 = 7638677) B7638677
theorem B3394967 : Blo 2261435 3394967 := bstep (se 1 (by rfl) ⟨2546225, by rfl⟩ : syracuseStep 3394967 = 5092451) B5092451
theorem B2263311 : Blo 2261435 2263311 := bstep (se 1 (by rfl) ⟨1697483, by rfl⟩ : syracuseStep 2263311 = 3394967) B3394967
theorem B3394973 : Blo 2261435 3394973 := bbase (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) (by norm_num)
theorem B2263315 : Blo 2261435 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B5092469 : Blo 2261435 5092469 := bbase (se 5 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 5092469 = 477419) (by norm_num)
theorem B3394979 : Blo 2261435 3394979 := bstep (se 1 (by rfl) ⟨2546234, by rfl⟩ : syracuseStep 3394979 = 5092469) B5092469
theorem B2263319 : Blo 2261435 2263319 := bstep (se 1 (by rfl) ⟨1697489, by rfl⟩ : syracuseStep 2263319 = 3394979) B3394979
theorem B19335509 : Blo 2261435 19335509 := bbase (se 10 (by rfl) ⟨28323, by rfl⟩ : syracuseStep 19335509 = 56647) (by norm_num)
theorem B12890339 : Blo 2261435 12890339 := bstep (se 1 (by rfl) ⟨9667754, by rfl⟩ : syracuseStep 12890339 = 19335509) B19335509
theorem B8593559 : Blo 2261435 8593559 := bstep (se 1 (by rfl) ⟨6445169, by rfl⟩ : syracuseStep 8593559 = 12890339) B12890339
theorem B5729039 : Blo 2261435 5729039 := bstep (se 1 (by rfl) ⟨4296779, by rfl⟩ : syracuseStep 5729039 = 8593559) B8593559
theorem B3819359 : Blo 2261435 3819359 := bstep (se 1 (by rfl) ⟨2864519, by rfl⟩ : syracuseStep 3819359 = 5729039) B5729039
theorem B2546239 : Blo 2261435 2546239 := bstep (se 1 (by rfl) ⟨1909679, by rfl⟩ : syracuseStep 2546239 = 3819359) B3819359
theorem B3394985 : Blo 2261435 3394985 := bstep (se 2 (by rfl) ⟨1273119, by rfl⟩ : syracuseStep 3394985 = 2546239) B2546239
theorem B2263323 : Blo 2261435 2263323 := bstep (se 1 (by rfl) ⟨1697492, by rfl⟩ : syracuseStep 2263323 = 3394985) B3394985
theorem B8593573 : Blo 2261435 8593573 := bbase (se 4 (by rfl) ⟨805647, by rfl⟩ : syracuseStep 8593573 = 1611295) (by norm_num)
theorem B11458097 : Blo 2261435 11458097 := bstep (se 2 (by rfl) ⟨4296786, by rfl⟩ : syracuseStep 11458097 = 8593573) B8593573
theorem B7638731 : Blo 2261435 7638731 := bstep (se 1 (by rfl) ⟨5729048, by rfl⟩ : syracuseStep 7638731 = 11458097) B11458097
theorem B5092487 : Blo 2261435 5092487 := bstep (se 1 (by rfl) ⟨3819365, by rfl⟩ : syracuseStep 5092487 = 7638731) B7638731
theorem B3394991 : Blo 2261435 3394991 := bstep (se 1 (by rfl) ⟨2546243, by rfl⟩ : syracuseStep 3394991 = 5092487) B5092487
theorem B2263327 : Blo 2261435 2263327 := bstep (se 1 (by rfl) ⟨1697495, by rfl⟩ : syracuseStep 2263327 = 3394991) B3394991
theorem B3394997 : Blo 2261435 3394997 := bbase (se 5 (by rfl) ⟨159140, by rfl⟩ : syracuseStep 3394997 = 318281) (by norm_num)
theorem B2263331 : Blo 2261435 2263331 := bstep (se 1 (by rfl) ⟨1697498, by rfl⟩ : syracuseStep 2263331 = 3394997) B3394997
theorem B5729069 : Blo 2261435 5729069 := bbase (se 3 (by rfl) ⟨1074200, by rfl⟩ : syracuseStep 5729069 = 2148401) (by norm_num)
theorem B3819379 : Blo 2261435 3819379 := bstep (se 1 (by rfl) ⟨2864534, by rfl⟩ : syracuseStep 3819379 = 5729069) B5729069
theorem B5092505 : Blo 2261435 5092505 := bstep (se 2 (by rfl) ⟨1909689, by rfl⟩ : syracuseStep 5092505 = 3819379) B3819379
theorem B3395003 : Blo 2261435 3395003 := bstep (se 1 (by rfl) ⟨2546252, by rfl⟩ : syracuseStep 3395003 = 5092505) B5092505
theorem B2263335 : Blo 2261435 2263335 := bstep (se 1 (by rfl) ⟨1697501, by rfl⟩ : syracuseStep 2263335 = 3395003) B3395003
theorem B2546257 : Blo 2261435 2546257 := bbase (se 2 (by rfl) ⟨954846, by rfl⟩ : syracuseStep 2546257 = 1909693) (by norm_num)
theorem B3395009 : Blo 2261435 3395009 := bstep (se 2 (by rfl) ⟨1273128, by rfl⟩ : syracuseStep 3395009 = 2546257) B2546257
theorem B2263339 : Blo 2261435 2263339 := bstep (se 1 (by rfl) ⟨1697504, by rfl⟩ : syracuseStep 2263339 = 3395009) B3395009
theorem B3222613 : Blo 2261435 3222613 := bbase (se 8 (by rfl) ⟨18882, by rfl⟩ : syracuseStep 3222613 = 37765) (by norm_num)
theorem B4296817 : Blo 2261435 4296817 := bstep (se 2 (by rfl) ⟨1611306, by rfl⟩ : syracuseStep 4296817 = 3222613) B3222613
theorem B5729089 : Blo 2261435 5729089 := bstep (se 2 (by rfl) ⟨2148408, by rfl⟩ : syracuseStep 5729089 = 4296817) B4296817
theorem B7638785 : Blo 2261435 7638785 := bstep (se 2 (by rfl) ⟨2864544, by rfl⟩ : syracuseStep 7638785 = 5729089) B5729089
theorem B5092523 : Blo 2261435 5092523 := bstep (se 1 (by rfl) ⟨3819392, by rfl⟩ : syracuseStep 5092523 = 7638785) B7638785
theorem B3395015 : Blo 2261435 3395015 := bstep (se 1 (by rfl) ⟨2546261, by rfl⟩ : syracuseStep 3395015 = 5092523) B5092523
theorem B2263343 : Blo 2261435 2263343 := bstep (se 1 (by rfl) ⟨1697507, by rfl⟩ : syracuseStep 2263343 = 3395015) B3395015
theorem B3395021 : Blo 2261435 3395021 := bbase (se 3 (by rfl) ⟨636566, by rfl⟩ : syracuseStep 3395021 = 1273133) (by norm_num)
theorem B2263347 : Blo 2261435 2263347 := bstep (se 1 (by rfl) ⟨1697510, by rfl⟩ : syracuseStep 2263347 = 3395021) B3395021
theorem B5092541 : Blo 2261435 5092541 := bbase (se 3 (by rfl) ⟨954851, by rfl⟩ : syracuseStep 5092541 = 1909703) (by norm_num)
theorem B3395027 : Blo 2261435 3395027 := bstep (se 1 (by rfl) ⟨2546270, by rfl⟩ : syracuseStep 3395027 = 5092541) B5092541
theorem B2263351 : Blo 2261435 2263351 := bstep (se 1 (by rfl) ⟨1697513, by rfl⟩ : syracuseStep 2263351 = 3395027) B3395027
theorem B3819413 : Blo 2261435 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B2546275 : Blo 2261435 2546275 := bstep (se 1 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 2546275 = 3819413) B3819413
theorem B3395033 : Blo 2261435 3395033 := bstep (se 2 (by rfl) ⟨1273137, by rfl⟩ : syracuseStep 3395033 = 2546275) B2546275
theorem B2263355 : Blo 2261435 2263355 := bstep (se 1 (by rfl) ⟨1697516, by rfl⟩ : syracuseStep 2263355 = 3395033) B3395033
theorem B2581021 : Blo 2261435 2581021 := bbase (se 3 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 2581021 = 967883) (by norm_num)
theorem B3441361 : Blo 2261435 3441361 := bstep (se 2 (by rfl) ⟨1290510, by rfl⟩ : syracuseStep 3441361 = 2581021) B2581021
theorem B4588481 : Blo 2261435 4588481 := bstep (se 2 (by rfl) ⟨1720680, by rfl⟩ : syracuseStep 4588481 = 3441361) B3441361
theorem B3058987 : Blo 2261435 3058987 := bstep (se 1 (by rfl) ⟨2294240, by rfl⟩ : syracuseStep 3058987 = 4588481) B4588481
theorem B4078649 : Blo 2261435 4078649 := bstep (se 2 (by rfl) ⟨1529493, by rfl⟩ : syracuseStep 4078649 = 3058987) B3058987
theorem B2719099 : Blo 2261435 2719099 := bstep (se 1 (by rfl) ⟨2039324, by rfl⟩ : syracuseStep 2719099 = 4078649) B4078649
theorem B14501861 : Blo 2261435 14501861 := bstep (se 4 (by rfl) ⟨1359549, by rfl⟩ : syracuseStep 14501861 = 2719099) B2719099
theorem B9667907 : Blo 2261435 9667907 := bstep (se 1 (by rfl) ⟨7250930, by rfl⟩ : syracuseStep 9667907 = 14501861) B14501861
theorem B6445271 : Blo 2261435 6445271 := bstep (se 1 (by rfl) ⟨4833953, by rfl⟩ : syracuseStep 6445271 = 9667907) B9667907
theorem B17187389 : Blo 2261435 17187389 := bstep (se 3 (by rfl) ⟨3222635, by rfl⟩ : syracuseStep 17187389 = 6445271) B6445271
theorem B11458259 : Blo 2261435 11458259 := bstep (se 1 (by rfl) ⟨8593694, by rfl⟩ : syracuseStep 11458259 = 17187389) B17187389
theorem B7638839 : Blo 2261435 7638839 := bstep (se 1 (by rfl) ⟨5729129, by rfl⟩ : syracuseStep 7638839 = 11458259) B11458259
theorem B5092559 : Blo 2261435 5092559 := bstep (se 1 (by rfl) ⟨3819419, by rfl⟩ : syracuseStep 5092559 = 7638839) B7638839
theorem B3395039 : Blo 2261435 3395039 := bstep (se 1 (by rfl) ⟨2546279, by rfl⟩ : syracuseStep 3395039 = 5092559) B5092559
theorem B2263359 : Blo 2261435 2263359 := bstep (se 1 (by rfl) ⟨1697519, by rfl⟩ : syracuseStep 2263359 = 3395039) B3395039
theorem B3395045 : Blo 2261435 3395045 := bbase (se 4 (by rfl) ⟨318285, by rfl⟩ : syracuseStep 3395045 = 636571) (by norm_num)
theorem B2263363 : Blo 2261435 2263363 := bstep (se 1 (by rfl) ⟨1697522, by rfl⟩ : syracuseStep 2263363 = 3395045) B3395045
theorem B20691413 : Blo 2261435 20691413 := bbase (se 7 (by rfl) ⟨242477, by rfl⟩ : syracuseStep 20691413 = 484955) (by norm_num)
theorem B13794275 : Blo 2261435 13794275 := bstep (se 1 (by rfl) ⟨10345706, by rfl⟩ : syracuseStep 13794275 = 20691413) B20691413
theorem B9196183 : Blo 2261435 9196183 := bstep (se 1 (by rfl) ⟨6897137, by rfl⟩ : syracuseStep 9196183 = 13794275) B13794275
theorem B12261577 : Blo 2261435 12261577 := bstep (se 2 (by rfl) ⟨4598091, by rfl⟩ : syracuseStep 12261577 = 9196183) B9196183
theorem B16348769 : Blo 2261435 16348769 := bstep (se 2 (by rfl) ⟨6130788, by rfl⟩ : syracuseStep 16348769 = 12261577) B12261577
theorem B10899179 : Blo 2261435 10899179 := bstep (se 1 (by rfl) ⟨8174384, by rfl⟩ : syracuseStep 10899179 = 16348769) B16348769
theorem B465031637 : Blo 2261435 465031637 := bstep (se 7 (by rfl) ⟨5449589, by rfl⟩ : syracuseStep 465031637 = 10899179) B10899179
theorem B310021091 : Blo 2261435 310021091 := bstep (se 1 (by rfl) ⟨232515818, by rfl⟩ : syracuseStep 310021091 = 465031637) B465031637
theorem B206680727 : Blo 2261435 206680727 := bstep (se 1 (by rfl) ⟨155010545, by rfl⟩ : syracuseStep 206680727 = 310021091) B310021091
theorem B137787151 : Blo 2261435 137787151 := bstep (se 1 (by rfl) ⟨103340363, by rfl⟩ : syracuseStep 137787151 = 206680727) B206680727
theorem B183716201 : Blo 2261435 183716201 := bstep (se 2 (by rfl) ⟨68893575, by rfl⟩ : syracuseStep 183716201 = 137787151) B137787151
theorem B122477467 : Blo 2261435 122477467 := bstep (se 1 (by rfl) ⟨91858100, by rfl⟩ : syracuseStep 122477467 = 183716201) B183716201
theorem B163303289 : Blo 2261435 163303289 := bstep (se 2 (by rfl) ⟨61238733, by rfl⟩ : syracuseStep 163303289 = 122477467) B122477467
theorem B108868859 : Blo 2261435 108868859 := bstep (se 1 (by rfl) ⟨81651644, by rfl⟩ : syracuseStep 108868859 = 163303289) B163303289
theorem B72579239 : Blo 2261435 72579239 := bstep (se 1 (by rfl) ⟨54434429, by rfl⟩ : syracuseStep 72579239 = 108868859) B108868859
theorem B48386159 : Blo 2261435 48386159 := bstep (se 1 (by rfl) ⟨36289619, by rfl⟩ : syracuseStep 48386159 = 72579239) B72579239
theorem B32257439 : Blo 2261435 32257439 := bstep (se 1 (by rfl) ⟨24193079, by rfl⟩ : syracuseStep 32257439 = 48386159) B48386159
theorem B21504959 : Blo 2261435 21504959 := bstep (se 1 (by rfl) ⟨16128719, by rfl⟩ : syracuseStep 21504959 = 32257439) B32257439
theorem B14336639 : Blo 2261435 14336639 := bstep (se 1 (by rfl) ⟨10752479, by rfl⟩ : syracuseStep 14336639 = 21504959) B21504959
theorem B9557759 : Blo 2261435 9557759 := bstep (se 1 (by rfl) ⟨7168319, by rfl⟩ : syracuseStep 9557759 = 14336639) B14336639
theorem B6371839 : Blo 2261435 6371839 := bstep (se 1 (by rfl) ⟨4778879, by rfl⟩ : syracuseStep 6371839 = 9557759) B9557759
theorem B8495785 : Blo 2261435 8495785 := bstep (se 2 (by rfl) ⟨3185919, by rfl⟩ : syracuseStep 8495785 = 6371839) B6371839
theorem B45310853 : Blo 2261435 45310853 := bstep (se 4 (by rfl) ⟨4247892, by rfl⟩ : syracuseStep 45310853 = 8495785) B8495785
theorem B120828941 : Blo 2261435 120828941 := bstep (se 3 (by rfl) ⟨22655426, by rfl⟩ : syracuseStep 120828941 = 45310853) B45310853
theorem B80552627 : Blo 2261435 80552627 := bstep (se 1 (by rfl) ⟨60414470, by rfl⟩ : syracuseStep 80552627 = 120828941) B120828941
theorem B53701751 : Blo 2261435 53701751 := bstep (se 1 (by rfl) ⟨40276313, by rfl⟩ : syracuseStep 53701751 = 80552627) B80552627
theorem B143204669 : Blo 2261435 143204669 := bstep (se 3 (by rfl) ⟨26850875, by rfl⟩ : syracuseStep 143204669 = 53701751) B53701751
theorem B95469779 : Blo 2261435 95469779 := bstep (se 1 (by rfl) ⟨71602334, by rfl⟩ : syracuseStep 95469779 = 143204669) B143204669
theorem B63646519 : Blo 2261435 63646519 := bstep (se 1 (by rfl) ⟨47734889, by rfl⟩ : syracuseStep 63646519 = 95469779) B95469779
theorem B84862025 : Blo 2261435 84862025 := bstep (se 2 (by rfl) ⟨31823259, by rfl⟩ : syracuseStep 84862025 = 63646519) B63646519
theorem B56574683 : Blo 2261435 56574683 := bstep (se 1 (by rfl) ⟨42431012, by rfl⟩ : syracuseStep 56574683 = 84862025) B84862025
theorem B37716455 : Blo 2261435 37716455 := bstep (se 1 (by rfl) ⟨28287341, by rfl⟩ : syracuseStep 37716455 = 56574683) B56574683
theorem B25144303 : Blo 2261435 25144303 := bstep (se 1 (by rfl) ⟨18858227, by rfl⟩ : syracuseStep 25144303 = 37716455) B37716455
theorem B33525737 : Blo 2261435 33525737 := bstep (se 2 (by rfl) ⟨12572151, by rfl⟩ : syracuseStep 33525737 = 25144303) B25144303
theorem B22350491 : Blo 2261435 22350491 := bstep (se 1 (by rfl) ⟨16762868, by rfl⟩ : syracuseStep 22350491 = 33525737) B33525737
theorem B14900327 : Blo 2261435 14900327 := bstep (se 1 (by rfl) ⟨11175245, by rfl⟩ : syracuseStep 14900327 = 22350491) B22350491
theorem B9933551 : Blo 2261435 9933551 := bstep (se 1 (by rfl) ⟨7450163, by rfl⟩ : syracuseStep 9933551 = 14900327) B14900327
theorem B6622367 : Blo 2261435 6622367 := bstep (se 1 (by rfl) ⟨4966775, by rfl⟩ : syracuseStep 6622367 = 9933551) B9933551
theorem B70638581 : Blo 2261435 70638581 := bstep (se 5 (by rfl) ⟨3311183, by rfl⟩ : syracuseStep 70638581 = 6622367) B6622367
theorem B47092387 : Blo 2261435 47092387 := bstep (se 1 (by rfl) ⟨35319290, by rfl⟩ : syracuseStep 47092387 = 70638581) B70638581
theorem B62789849 : Blo 2261435 62789849 := bstep (se 2 (by rfl) ⟨23546193, by rfl⟩ : syracuseStep 62789849 = 47092387) B47092387
theorem B41859899 : Blo 2261435 41859899 := bstep (se 1 (by rfl) ⟨31394924, by rfl⟩ : syracuseStep 41859899 = 62789849) B62789849
theorem B27906599 : Blo 2261435 27906599 := bstep (se 1 (by rfl) ⟨20929949, by rfl⟩ : syracuseStep 27906599 = 41859899) B41859899
theorem B18604399 : Blo 2261435 18604399 := bstep (se 1 (by rfl) ⟨13953299, by rfl⟩ : syracuseStep 18604399 = 27906599) B27906599
theorem B24805865 : Blo 2261435 24805865 := bstep (se 2 (by rfl) ⟨9302199, by rfl⟩ : syracuseStep 24805865 = 18604399) B18604399
theorem B66148973 : Blo 2261435 66148973 := bstep (se 3 (by rfl) ⟨12402932, by rfl⟩ : syracuseStep 66148973 = 24805865) B24805865
theorem B44099315 : Blo 2261435 44099315 := bstep (se 1 (by rfl) ⟨33074486, by rfl⟩ : syracuseStep 44099315 = 66148973) B66148973
theorem B29399543 : Blo 2261435 29399543 := bstep (se 1 (by rfl) ⟨22049657, by rfl⟩ : syracuseStep 29399543 = 44099315) B44099315
theorem B19599695 : Blo 2261435 19599695 := bstep (se 1 (by rfl) ⟨14699771, by rfl⟩ : syracuseStep 19599695 = 29399543) B29399543
theorem B13066463 : Blo 2261435 13066463 := bstep (se 1 (by rfl) ⟨9799847, by rfl⟩ : syracuseStep 13066463 = 19599695) B19599695
theorem B8710975 : Blo 2261435 8710975 := bstep (se 1 (by rfl) ⟨6533231, by rfl⟩ : syracuseStep 8710975 = 13066463) B13066463
theorem B11614633 : Blo 2261435 11614633 := bstep (se 2 (by rfl) ⟨4355487, by rfl⟩ : syracuseStep 11614633 = 8710975) B8710975
theorem B61944709 : Blo 2261435 61944709 := bstep (se 4 (by rfl) ⟨5807316, by rfl⟩ : syracuseStep 61944709 = 11614633) B11614633
theorem B82592945 : Blo 2261435 82592945 := bstep (se 2 (by rfl) ⟨30972354, by rfl⟩ : syracuseStep 82592945 = 61944709) B61944709
theorem B55061963 : Blo 2261435 55061963 := bstep (se 1 (by rfl) ⟨41296472, by rfl⟩ : syracuseStep 55061963 = 82592945) B82592945
theorem B36707975 : Blo 2261435 36707975 := bstep (se 1 (by rfl) ⟨27530981, by rfl⟩ : syracuseStep 36707975 = 55061963) B55061963
theorem B24471983 : Blo 2261435 24471983 := bstep (se 1 (by rfl) ⟨18353987, by rfl⟩ : syracuseStep 24471983 = 36707975) B36707975
theorem B16314655 : Blo 2261435 16314655 := bstep (se 1 (by rfl) ⟨12235991, by rfl⟩ : syracuseStep 16314655 = 24471983) B24471983
theorem B21752873 : Blo 2261435 21752873 := bstep (se 2 (by rfl) ⟨8157327, by rfl⟩ : syracuseStep 21752873 = 16314655) B16314655
theorem B14501915 : Blo 2261435 14501915 := bstep (se 1 (by rfl) ⟨10876436, by rfl⟩ : syracuseStep 14501915 = 21752873) B21752873
theorem B9667943 : Blo 2261435 9667943 := bstep (se 1 (by rfl) ⟨7250957, by rfl⟩ : syracuseStep 9667943 = 14501915) B14501915
theorem B6445295 : Blo 2261435 6445295 := bstep (se 1 (by rfl) ⟨4833971, by rfl⟩ : syracuseStep 6445295 = 9667943) B9667943
theorem B4296863 : Blo 2261435 4296863 := bstep (se 1 (by rfl) ⟨3222647, by rfl⟩ : syracuseStep 4296863 = 6445295) B6445295
theorem B2864575 : Blo 2261435 2864575 := bstep (se 1 (by rfl) ⟨2148431, by rfl⟩ : syracuseStep 2864575 = 4296863) B4296863
theorem B3819433 : Blo 2261435 3819433 := bstep (se 2 (by rfl) ⟨1432287, by rfl⟩ : syracuseStep 3819433 = 2864575) B2864575
theorem B5092577 : Blo 2261435 5092577 := bstep (se 2 (by rfl) ⟨1909716, by rfl⟩ : syracuseStep 5092577 = 3819433) B3819433
theorem B3395051 : Blo 2261435 3395051 := bstep (se 1 (by rfl) ⟨2546288, by rfl⟩ : syracuseStep 3395051 = 5092577) B5092577
theorem B2263367 : Blo 2261435 2263367 := bstep (se 1 (by rfl) ⟨1697525, by rfl⟩ : syracuseStep 2263367 = 3395051) B3395051
theorem B2546293 : Blo 2261435 2546293 := bbase (se 5 (by rfl) ⟨119357, by rfl⟩ : syracuseStep 2546293 = 238715) (by norm_num)
theorem B3395057 : Blo 2261435 3395057 := bstep (se 2 (by rfl) ⟨1273146, by rfl⟩ : syracuseStep 3395057 = 2546293) B2546293
theorem B2263371 : Blo 2261435 2263371 := bstep (se 1 (by rfl) ⟨1697528, by rfl⟩ : syracuseStep 2263371 = 3395057) B3395057
theorem B2864585 : Blo 2261435 2864585 := bbase (se 2 (by rfl) ⟨1074219, by rfl⟩ : syracuseStep 2864585 = 2148439) (by norm_num)
theorem B7638893 : Blo 2261435 7638893 := bstep (se 3 (by rfl) ⟨1432292, by rfl⟩ : syracuseStep 7638893 = 2864585) B2864585
theorem B5092595 : Blo 2261435 5092595 := bstep (se 1 (by rfl) ⟨3819446, by rfl⟩ : syracuseStep 5092595 = 7638893) B7638893
theorem B3395063 : Blo 2261435 3395063 := bstep (se 1 (by rfl) ⟨2546297, by rfl⟩ : syracuseStep 3395063 = 5092595) B5092595
theorem B2263375 : Blo 2261435 2263375 := bstep (se 1 (by rfl) ⟨1697531, by rfl⟩ : syracuseStep 2263375 = 3395063) B3395063
theorem B3395069 : Blo 2261435 3395069 := bbase (se 3 (by rfl) ⟨636575, by rfl⟩ : syracuseStep 3395069 = 1273151) (by norm_num)
theorem B2263379 : Blo 2261435 2263379 := bstep (se 1 (by rfl) ⟨1697534, by rfl⟩ : syracuseStep 2263379 = 3395069) B3395069
theorem B5092613 : Blo 2261435 5092613 := bbase (se 4 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 5092613 = 954865) (by norm_num)
theorem B3395075 : Blo 2261435 3395075 := bstep (se 1 (by rfl) ⟨2546306, by rfl⟩ : syracuseStep 3395075 = 5092613) B5092613
theorem B2263383 : Blo 2261435 2263383 := bstep (se 1 (by rfl) ⟨1697537, by rfl⟩ : syracuseStep 2263383 = 3395075) B3395075
theorem B4296901 : Blo 2261435 4296901 := bbase (se 4 (by rfl) ⟨402834, by rfl⟩ : syracuseStep 4296901 = 805669) (by norm_num)
theorem B5729201 : Blo 2261435 5729201 := bstep (se 2 (by rfl) ⟨2148450, by rfl⟩ : syracuseStep 5729201 = 4296901) B4296901
theorem B3819467 : Blo 2261435 3819467 := bstep (se 1 (by rfl) ⟨2864600, by rfl⟩ : syracuseStep 3819467 = 5729201) B5729201
theorem B2546311 : Blo 2261435 2546311 := bstep (se 1 (by rfl) ⟨1909733, by rfl⟩ : syracuseStep 2546311 = 3819467) B3819467
theorem B3395081 : Blo 2261435 3395081 := bstep (se 2 (by rfl) ⟨1273155, by rfl⟩ : syracuseStep 3395081 = 2546311) B2546311
theorem B2263387 : Blo 2261435 2263387 := bstep (se 1 (by rfl) ⟨1697540, by rfl⟩ : syracuseStep 2263387 = 3395081) B3395081
theorem B11458421 : Blo 2261435 11458421 := bbase (se 5 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 11458421 = 1074227) (by norm_num)
theorem B7638947 : Blo 2261435 7638947 := bstep (se 1 (by rfl) ⟨5729210, by rfl⟩ : syracuseStep 7638947 = 11458421) B11458421
theorem B5092631 : Blo 2261435 5092631 := bstep (se 1 (by rfl) ⟨3819473, by rfl⟩ : syracuseStep 5092631 = 7638947) B7638947
theorem B3395087 : Blo 2261435 3395087 := bstep (se 1 (by rfl) ⟨2546315, by rfl⟩ : syracuseStep 3395087 = 5092631) B5092631
theorem B2263391 : Blo 2261435 2263391 := bstep (se 1 (by rfl) ⟨1697543, by rfl⟩ : syracuseStep 2263391 = 3395087) B3395087
theorem B3395093 : Blo 2261435 3395093 := bbase (se 6 (by rfl) ⟨79572, by rfl⟩ : syracuseStep 3395093 = 159145) (by norm_num)
theorem B2263395 : Blo 2261435 2263395 := bstep (se 1 (by rfl) ⟨1697546, by rfl⟩ : syracuseStep 2263395 = 3395093) B3395093
theorem B2294281 : Blo 2261435 2294281 := bbase (se 2 (by rfl) ⟨860355, by rfl⟩ : syracuseStep 2294281 = 1720711) (by norm_num)
theorem B3059041 : Blo 2261435 3059041 := bstep (se 2 (by rfl) ⟨1147140, by rfl⟩ : syracuseStep 3059041 = 2294281) B2294281
theorem B4078721 : Blo 2261435 4078721 := bstep (se 2 (by rfl) ⟨1529520, by rfl⟩ : syracuseStep 4078721 = 3059041) B3059041
theorem B10876589 : Blo 2261435 10876589 := bstep (se 3 (by rfl) ⟨2039360, by rfl⟩ : syracuseStep 10876589 = 4078721) B4078721
theorem B7251059 : Blo 2261435 7251059 := bstep (se 1 (by rfl) ⟨5438294, by rfl⟩ : syracuseStep 7251059 = 10876589) B10876589
theorem B19336157 : Blo 2261435 19336157 := bstep (se 3 (by rfl) ⟨3625529, by rfl⟩ : syracuseStep 19336157 = 7251059) B7251059
theorem B12890771 : Blo 2261435 12890771 := bstep (se 1 (by rfl) ⟨9668078, by rfl⟩ : syracuseStep 12890771 = 19336157) B19336157
theorem B8593847 : Blo 2261435 8593847 := bstep (se 1 (by rfl) ⟨6445385, by rfl⟩ : syracuseStep 8593847 = 12890771) B12890771
theorem B5729231 : Blo 2261435 5729231 := bstep (se 1 (by rfl) ⟨4296923, by rfl⟩ : syracuseStep 5729231 = 8593847) B8593847
theorem B3819487 : Blo 2261435 3819487 := bstep (se 1 (by rfl) ⟨2864615, by rfl⟩ : syracuseStep 3819487 = 5729231) B5729231
theorem B5092649 : Blo 2261435 5092649 := bstep (se 2 (by rfl) ⟨1909743, by rfl⟩ : syracuseStep 5092649 = 3819487) B3819487
theorem B3395099 : Blo 2261435 3395099 := bstep (se 1 (by rfl) ⟨2546324, by rfl⟩ : syracuseStep 3395099 = 5092649) B5092649
theorem B2263399 : Blo 2261435 2263399 := bstep (se 1 (by rfl) ⟨1697549, by rfl⟩ : syracuseStep 2263399 = 3395099) B3395099
theorem B2546329 : Blo 2261435 2546329 := bbase (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) (by norm_num)
theorem B3395105 : Blo 2261435 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B2263403 : Blo 2261435 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B8593877 : Blo 2261435 8593877 := bbase (se 7 (by rfl) ⟨100709, by rfl⟩ : syracuseStep 8593877 = 201419) (by norm_num)
theorem B5729251 : Blo 2261435 5729251 := bstep (se 1 (by rfl) ⟨4296938, by rfl⟩ : syracuseStep 5729251 = 8593877) B8593877
theorem B7639001 : Blo 2261435 7639001 := bstep (se 2 (by rfl) ⟨2864625, by rfl⟩ : syracuseStep 7639001 = 5729251) B5729251
theorem B5092667 : Blo 2261435 5092667 := bstep (se 1 (by rfl) ⟨3819500, by rfl⟩ : syracuseStep 5092667 = 7639001) B7639001
theorem B3395111 : Blo 2261435 3395111 := bstep (se 1 (by rfl) ⟨2546333, by rfl⟩ : syracuseStep 3395111 = 5092667) B5092667
theorem B2263407 : Blo 2261435 2263407 := bstep (se 1 (by rfl) ⟨1697555, by rfl⟩ : syracuseStep 2263407 = 3395111) B3395111
theorem B3395117 : Blo 2261435 3395117 := bbase (se 3 (by rfl) ⟨636584, by rfl⟩ : syracuseStep 3395117 = 1273169) (by norm_num)
theorem B2263411 : Blo 2261435 2263411 := bstep (se 1 (by rfl) ⟨1697558, by rfl⟩ : syracuseStep 2263411 = 3395117) B3395117
theorem B5092685 : Blo 2261435 5092685 := bbase (se 3 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 5092685 = 1909757) (by norm_num)
theorem B3395123 : Blo 2261435 3395123 := bstep (se 1 (by rfl) ⟨2546342, by rfl⟩ : syracuseStep 3395123 = 5092685) B5092685
theorem B2263415 : Blo 2261435 2263415 := bstep (se 1 (by rfl) ⟨1697561, by rfl⟩ : syracuseStep 2263415 = 3395123) B3395123
theorem B2864641 : Blo 2261435 2864641 := bbase (se 2 (by rfl) ⟨1074240, by rfl⟩ : syracuseStep 2864641 = 2148481) (by norm_num)
theorem B3819521 : Blo 2261435 3819521 := bstep (se 2 (by rfl) ⟨1432320, by rfl⟩ : syracuseStep 3819521 = 2864641) B2864641
theorem B2546347 : Blo 2261435 2546347 := bstep (se 1 (by rfl) ⟨1909760, by rfl⟩ : syracuseStep 2546347 = 3819521) B3819521
theorem B3395129 : Blo 2261435 3395129 := bstep (se 2 (by rfl) ⟨1273173, by rfl⟩ : syracuseStep 3395129 = 2546347) B2546347
theorem B2263419 : Blo 2261435 2263419 := bstep (se 1 (by rfl) ⟨1697564, by rfl⟩ : syracuseStep 2263419 = 3395129) B3395129
theorem B2417045 : Blo 2261435 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B25781813 : Blo 2261435 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B17187875 : Blo 2261435 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B11458583 : Blo 2261435 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B7639055 : Blo 2261435 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B5092703 : Blo 2261435 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B3395135 : Blo 2261435 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B2263423 : Blo 2261435 2263423 := bstep (se 1 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 2263423 = 3395135) B3395135
theorem B3395141 : Blo 2261435 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B2263427 : Blo 2261435 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B3819541 : Blo 2261435 3819541 := bbase (se 6 (by rfl) ⟨89520, by rfl⟩ : syracuseStep 3819541 = 179041) (by norm_num)
theorem B5092721 : Blo 2261435 5092721 := bstep (se 2 (by rfl) ⟨1909770, by rfl⟩ : syracuseStep 5092721 = 3819541) B3819541
theorem B3395147 : Blo 2261435 3395147 := bstep (se 1 (by rfl) ⟨2546360, by rfl⟩ : syracuseStep 3395147 = 5092721) B5092721
theorem B2263431 : Blo 2261435 2263431 := bstep (se 1 (by rfl) ⟨1697573, by rfl⟩ : syracuseStep 2263431 = 3395147) B3395147
theorem B2546365 : Blo 2261435 2546365 := bbase (se 3 (by rfl) ⟨477443, by rfl⟩ : syracuseStep 2546365 = 954887) (by norm_num)
theorem B3395153 : Blo 2261435 3395153 := bstep (se 2 (by rfl) ⟨1273182, by rfl⟩ : syracuseStep 3395153 = 2546365) B2546365
theorem B2263435 : Blo 2261435 2263435 := bstep (se 1 (by rfl) ⟨1697576, by rfl⟩ : syracuseStep 2263435 = 3395153) B3395153
theorem C0 (j : ℕ) (h1 : 565358 ≤ j) (h2 : j ≤ 565858) : Blo 2261435 (4 * j + 3) := by
  interval_cases j
  · exact B2261435
  · exact B2261439
  · exact B2261443
  · exact B2261447
  · exact B2261451
  · exact B2261455
  · exact B2261459
  · exact B2261463
  · exact B2261467
  · exact B2261471
  · exact B2261475
  · exact B2261479
  · exact B2261483
  · exact B2261487
  · exact B2261491
  · exact B2261495
  · exact B2261499
  · exact B2261503
  · exact B2261507
  · exact B2261511
  · exact B2261515
  · exact B2261519
  · exact B2261523
  · exact B2261527
  · exact B2261531
  · exact B2261535
  · exact B2261539
  · exact B2261543
  · exact B2261547
  · exact B2261551
  · exact B2261555
  · exact B2261559
  · exact B2261563
  · exact B2261567
  · exact B2261571
  · exact B2261575
  · exact B2261579
  · exact B2261583
  · exact B2261587
  · exact B2261591
  · exact B2261595
  · exact B2261599
  · exact B2261603
  · exact B2261607
  · exact B2261611
  · exact B2261615
  · exact B2261619
  · exact B2261623
  · exact B2261627
  · exact B2261631
  · exact B2261635
  · exact B2261639
  · exact B2261643
  · exact B2261647
  · exact B2261651
  · exact B2261655
  · exact B2261659
  · exact B2261663
  · exact B2261667
  · exact B2261671
  · exact B2261675
  · exact B2261679
  · exact B2261683
  · exact B2261687
  · exact B2261691
  · exact B2261695
  · exact B2261699
  · exact B2261703
  · exact B2261707
  · exact B2261711
  · exact B2261715
  · exact B2261719
  · exact B2261723
  · exact B2261727
  · exact B2261731
  · exact B2261735
  · exact B2261739
  · exact B2261743
  · exact B2261747
  · exact B2261751
  · exact B2261755
  · exact B2261759
  · exact B2261763
  · exact B2261767
  · exact B2261771
  · exact B2261775
  · exact B2261779
  · exact B2261783
  · exact B2261787
  · exact B2261791
  · exact B2261795
  · exact B2261799
  · exact B2261803
  · exact B2261807
  · exact B2261811
  · exact B2261815
  · exact B2261819
  · exact B2261823
  · exact B2261827
  · exact B2261831
  · exact B2261835
  · exact B2261839
  · exact B2261843
  · exact B2261847
  · exact B2261851
  · exact B2261855
  · exact B2261859
  · exact B2261863
  · exact B2261867
  · exact B2261871
  · exact B2261875
  · exact B2261879
  · exact B2261883
  · exact B2261887
  · exact B2261891
  · exact B2261895
  · exact B2261899
  · exact B2261903
  · exact B2261907
  · exact B2261911
  · exact B2261915
  · exact B2261919
  · exact B2261923
  · exact B2261927
  · exact B2261931
  · exact B2261935
  · exact B2261939
  · exact B2261943
  · exact B2261947
  · exact B2261951
  · exact B2261955
  · exact B2261959
  · exact B2261963
  · exact B2261967
  · exact B2261971
  · exact B2261975
  · exact B2261979
  · exact B2261983
  · exact B2261987
  · exact B2261991
  · exact B2261995
  · exact B2261999
  · exact B2262003
  · exact B2262007
  · exact B2262011
  · exact B2262015
  · exact B2262019
  · exact B2262023
  · exact B2262027
  · exact B2262031
  · exact B2262035
  · exact B2262039
  · exact B2262043
  · exact B2262047
  · exact B2262051
  · exact B2262055
  · exact B2262059
  · exact B2262063
  · exact B2262067
  · exact B2262071
  · exact B2262075
  · exact B2262079
  · exact B2262083
  · exact B2262087
  · exact B2262091
  · exact B2262095
  · exact B2262099
  · exact B2262103
  · exact B2262107
  · exact B2262111
  · exact B2262115
  · exact B2262119
  · exact B2262123
  · exact B2262127
  · exact B2262131
  · exact B2262135
  · exact B2262139
  · exact B2262143
  · exact B2262147
  · exact B2262151
  · exact B2262155
  · exact B2262159
  · exact B2262163
  · exact B2262167
  · exact B2262171
  · exact B2262175
  · exact B2262179
  · exact B2262183
  · exact B2262187
  · exact B2262191
  · exact B2262195
  · exact B2262199
  · exact B2262203
  · exact B2262207
  · exact B2262211
  · exact B2262215
  · exact B2262219
  · exact B2262223
  · exact B2262227
  · exact B2262231
  · exact B2262235
  · exact B2262239
  · exact B2262243
  · exact B2262247
  · exact B2262251
  · exact B2262255
  · exact B2262259
  · exact B2262263
  · exact B2262267
  · exact B2262271
  · exact B2262275
  · exact B2262279
  · exact B2262283
  · exact B2262287
  · exact B2262291
  · exact B2262295
  · exact B2262299
  · exact B2262303
  · exact B2262307
  · exact B2262311
  · exact B2262315
  · exact B2262319
  · exact B2262323
  · exact B2262327
  · exact B2262331
  · exact B2262335
  · exact B2262339
  · exact B2262343
  · exact B2262347
  · exact B2262351
  · exact B2262355
  · exact B2262359
  · exact B2262363
  · exact B2262367
  · exact B2262371
  · exact B2262375
  · exact B2262379
  · exact B2262383
  · exact B2262387
  · exact B2262391
  · exact B2262395
  · exact B2262399
  · exact B2262403
  · exact B2262407
  · exact B2262411
  · exact B2262415
  · exact B2262419
  · exact B2262423
  · exact B2262427
  · exact B2262431
  · exact B2262435
  · exact B2262439
  · exact B2262443
  · exact B2262447
  · exact B2262451
  · exact B2262455
  · exact B2262459
  · exact B2262463
  · exact B2262467
  · exact B2262471
  · exact B2262475
  · exact B2262479
  · exact B2262483
  · exact B2262487
  · exact B2262491
  · exact B2262495
  · exact B2262499
  · exact B2262503
  · exact B2262507
  · exact B2262511
  · exact B2262515
  · exact B2262519
  · exact B2262523
  · exact B2262527
  · exact B2262531
  · exact B2262535
  · exact B2262539
  · exact B2262543
  · exact B2262547
  · exact B2262551
  · exact B2262555
  · exact B2262559
  · exact B2262563
  · exact B2262567
  · exact B2262571
  · exact B2262575
  · exact B2262579
  · exact B2262583
  · exact B2262587
  · exact B2262591
  · exact B2262595
  · exact B2262599
  · exact B2262603
  · exact B2262607
  · exact B2262611
  · exact B2262615
  · exact B2262619
  · exact B2262623
  · exact B2262627
  · exact B2262631
  · exact B2262635
  · exact B2262639
  · exact B2262643
  · exact B2262647
  · exact B2262651
  · exact B2262655
  · exact B2262659
  · exact B2262663
  · exact B2262667
  · exact B2262671
  · exact B2262675
  · exact B2262679
  · exact B2262683
  · exact B2262687
  · exact B2262691
  · exact B2262695
  · exact B2262699
  · exact B2262703
  · exact B2262707
  · exact B2262711
  · exact B2262715
  · exact B2262719
  · exact B2262723
  · exact B2262727
  · exact B2262731
  · exact B2262735
  · exact B2262739
  · exact B2262743
  · exact B2262747
  · exact B2262751
  · exact B2262755
  · exact B2262759
  · exact B2262763
  · exact B2262767
  · exact B2262771
  · exact B2262775
  · exact B2262779
  · exact B2262783
  · exact B2262787
  · exact B2262791
  · exact B2262795
  · exact B2262799
  · exact B2262803
  · exact B2262807
  · exact B2262811
  · exact B2262815
  · exact B2262819
  · exact B2262823
  · exact B2262827
  · exact B2262831
  · exact B2262835
  · exact B2262839
  · exact B2262843
  · exact B2262847
  · exact B2262851
  · exact B2262855
  · exact B2262859
  · exact B2262863
  · exact B2262867
  · exact B2262871
  · exact B2262875
  · exact B2262879
  · exact B2262883
  · exact B2262887
  · exact B2262891
  · exact B2262895
  · exact B2262899
  · exact B2262903
  · exact B2262907
  · exact B2262911
  · exact B2262915
  · exact B2262919
  · exact B2262923
  · exact B2262927
  · exact B2262931
  · exact B2262935
  · exact B2262939
  · exact B2262943
  · exact B2262947
  · exact B2262951
  · exact B2262955
  · exact B2262959
  · exact B2262963
  · exact B2262967
  · exact B2262971
  · exact B2262975
  · exact B2262979
  · exact B2262983
  · exact B2262987
  · exact B2262991
  · exact B2262995
  · exact B2262999
  · exact B2263003
  · exact B2263007
  · exact B2263011
  · exact B2263015
  · exact B2263019
  · exact B2263023
  · exact B2263027
  · exact B2263031
  · exact B2263035
  · exact B2263039
  · exact B2263043
  · exact B2263047
  · exact B2263051
  · exact B2263055
  · exact B2263059
  · exact B2263063
  · exact B2263067
  · exact B2263071
  · exact B2263075
  · exact B2263079
  · exact B2263083
  · exact B2263087
  · exact B2263091
  · exact B2263095
  · exact B2263099
  · exact B2263103
  · exact B2263107
  · exact B2263111
  · exact B2263115
  · exact B2263119
  · exact B2263123
  · exact B2263127
  · exact B2263131
  · exact B2263135
  · exact B2263139
  · exact B2263143
  · exact B2263147
  · exact B2263151
  · exact B2263155
  · exact B2263159
  · exact B2263163
  · exact B2263167
  · exact B2263171
  · exact B2263175
  · exact B2263179
  · exact B2263183
  · exact B2263187
  · exact B2263191
  · exact B2263195
  · exact B2263199
  · exact B2263203
  · exact B2263207
  · exact B2263211
  · exact B2263215
  · exact B2263219
  · exact B2263223
  · exact B2263227
  · exact B2263231
  · exact B2263235
  · exact B2263239
  · exact B2263243
  · exact B2263247
  · exact B2263251
  · exact B2263255
  · exact B2263259
  · exact B2263263
  · exact B2263267
  · exact B2263271
  · exact B2263275
  · exact B2263279
  · exact B2263283
  · exact B2263287
  · exact B2263291
  · exact B2263295
  · exact B2263299
  · exact B2263303
  · exact B2263307
  · exact B2263311
  · exact B2263315
  · exact B2263319
  · exact B2263323
  · exact B2263327
  · exact B2263331
  · exact B2263335
  · exact B2263339
  · exact B2263343
  · exact B2263347
  · exact B2263351
  · exact B2263355
  · exact B2263359
  · exact B2263363
  · exact B2263367
  · exact B2263371
  · exact B2263375
  · exact B2263379
  · exact B2263383
  · exact B2263387
  · exact B2263391
  · exact B2263395
  · exact B2263399
  · exact B2263403
  · exact B2263407
  · exact B2263411
  · exact B2263415
  · exact B2263419
  · exact B2263423
  · exact B2263427
  · exact B2263431
  · exact B2263435
theorem solution (m : ℕ) (hlo : 2261435 ≤ m) (hhi : m ≤ 2263435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 565358 ≤ j := by omega
    have hj2 : j ≤ 565858 := by omega
    have hb : Blo 2261435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
