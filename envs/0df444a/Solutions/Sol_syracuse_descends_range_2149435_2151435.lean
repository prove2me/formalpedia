-- Prove2me | solution 1 for syracuse_descends_range_2149435_2151435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:26.45866+00:00
-- url     : https://prove2.me/submissions/2c00a8dd-e1d0-4836-bfb3-285c5bbd9cd7

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

theorem B3627173 : Blo 2149435 3627173 := bbase (se 4 (by rfl) ⟨340047, by rfl⟩ : syracuseStep 3627173 = 680095) (by norm_num)
theorem B2418115 : Blo 2149435 2418115 := bstep (se 1 (by rfl) ⟨1813586, by rfl⟩ : syracuseStep 2418115 = 3627173) B3627173
theorem B3224153 : Blo 2149435 3224153 := bstep (se 2 (by rfl) ⟨1209057, by rfl⟩ : syracuseStep 3224153 = 2418115) B2418115
theorem B2149435 : Blo 2149435 2149435 := bstep (se 1 (by rfl) ⟨1612076, by rfl⟩ : syracuseStep 2149435 = 3224153) B3224153
theorem B2295325 : Blo 2149435 2295325 := bbase (se 3 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 2295325 = 860747) (by norm_num)
theorem B3060433 : Blo 2149435 3060433 := bstep (se 2 (by rfl) ⟨1147662, by rfl⟩ : syracuseStep 3060433 = 2295325) B2295325
theorem B16322309 : Blo 2149435 16322309 := bstep (se 4 (by rfl) ⟨1530216, by rfl⟩ : syracuseStep 16322309 = 3060433) B3060433
theorem B10881539 : Blo 2149435 10881539 := bstep (se 1 (by rfl) ⟨8161154, by rfl⟩ : syracuseStep 10881539 = 16322309) B16322309
theorem B7254359 : Blo 2149435 7254359 := bstep (se 1 (by rfl) ⟨5440769, by rfl⟩ : syracuseStep 7254359 = 10881539) B10881539
theorem B4836239 : Blo 2149435 4836239 := bstep (se 1 (by rfl) ⟨3627179, by rfl⟩ : syracuseStep 4836239 = 7254359) B7254359
theorem B3224159 : Blo 2149435 3224159 := bstep (se 1 (by rfl) ⟨2418119, by rfl⟩ : syracuseStep 3224159 = 4836239) B4836239
theorem B2149439 : Blo 2149435 2149439 := bstep (se 1 (by rfl) ⟨1612079, by rfl⟩ : syracuseStep 2149439 = 3224159) B3224159
theorem B3224165 : Blo 2149435 3224165 := bbase (se 4 (by rfl) ⟨302265, by rfl⟩ : syracuseStep 3224165 = 604531) (by norm_num)
theorem B2149443 : Blo 2149435 2149443 := bstep (se 1 (by rfl) ⟨1612082, by rfl⟩ : syracuseStep 2149443 = 3224165) B3224165
theorem B3060445 : Blo 2149435 3060445 := bbase (se 3 (by rfl) ⟨573833, by rfl⟩ : syracuseStep 3060445 = 1147667) (by norm_num)
theorem B4080593 : Blo 2149435 4080593 := bstep (se 2 (by rfl) ⟨1530222, by rfl⟩ : syracuseStep 4080593 = 3060445) B3060445
theorem B2720395 : Blo 2149435 2720395 := bstep (se 1 (by rfl) ⟨2040296, by rfl⟩ : syracuseStep 2720395 = 4080593) B4080593
theorem B3627193 : Blo 2149435 3627193 := bstep (se 2 (by rfl) ⟨1360197, by rfl⟩ : syracuseStep 3627193 = 2720395) B2720395
theorem B4836257 : Blo 2149435 4836257 := bstep (se 2 (by rfl) ⟨1813596, by rfl⟩ : syracuseStep 4836257 = 3627193) B3627193
theorem B3224171 : Blo 2149435 3224171 := bstep (se 1 (by rfl) ⟨2418128, by rfl⟩ : syracuseStep 3224171 = 4836257) B4836257
theorem B2149447 : Blo 2149435 2149447 := bstep (se 1 (by rfl) ⟨1612085, by rfl⟩ : syracuseStep 2149447 = 3224171) B3224171
theorem B2418133 : Blo 2149435 2418133 := bbase (se 7 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 2418133 = 56675) (by norm_num)
theorem B3224177 : Blo 2149435 3224177 := bstep (se 2 (by rfl) ⟨1209066, by rfl⟩ : syracuseStep 3224177 = 2418133) B2418133
theorem B2149451 : Blo 2149435 2149451 := bstep (se 1 (by rfl) ⟨1612088, by rfl⟩ : syracuseStep 2149451 = 3224177) B3224177
theorem B2720405 : Blo 2149435 2720405 := bbase (se 6 (by rfl) ⟨63759, by rfl⟩ : syracuseStep 2720405 = 127519) (by norm_num)
theorem B7254413 : Blo 2149435 7254413 := bstep (se 3 (by rfl) ⟨1360202, by rfl⟩ : syracuseStep 7254413 = 2720405) B2720405
theorem B4836275 : Blo 2149435 4836275 := bstep (se 1 (by rfl) ⟨3627206, by rfl⟩ : syracuseStep 4836275 = 7254413) B7254413
theorem B3224183 : Blo 2149435 3224183 := bstep (se 1 (by rfl) ⟨2418137, by rfl⟩ : syracuseStep 3224183 = 4836275) B4836275
theorem B2149455 : Blo 2149435 2149455 := bstep (se 1 (by rfl) ⟨1612091, by rfl⟩ : syracuseStep 2149455 = 3224183) B3224183
theorem B3224189 : Blo 2149435 3224189 := bbase (se 3 (by rfl) ⟨604535, by rfl⟩ : syracuseStep 3224189 = 1209071) (by norm_num)
theorem B2149459 : Blo 2149435 2149459 := bstep (se 1 (by rfl) ⟨1612094, by rfl⟩ : syracuseStep 2149459 = 3224189) B3224189
theorem B4836293 : Blo 2149435 4836293 := bbase (se 4 (by rfl) ⟨453402, by rfl⟩ : syracuseStep 4836293 = 906805) (by norm_num)
theorem B3224195 : Blo 2149435 3224195 := bstep (se 1 (by rfl) ⟨2418146, by rfl⟩ : syracuseStep 3224195 = 4836293) B4836293
theorem B2149463 : Blo 2149435 2149463 := bstep (se 1 (by rfl) ⟨1612097, by rfl⟩ : syracuseStep 2149463 = 3224195) B3224195
theorem B3873413 : Blo 2149435 3873413 := bbase (se 4 (by rfl) ⟨363132, by rfl⟩ : syracuseStep 3873413 = 726265) (by norm_num)
theorem B2582275 : Blo 2149435 2582275 := bstep (se 1 (by rfl) ⟨1936706, by rfl⟩ : syracuseStep 2582275 = 3873413) B3873413
theorem B3443033 : Blo 2149435 3443033 := bstep (se 2 (by rfl) ⟨1291137, by rfl⟩ : syracuseStep 3443033 = 2582275) B2582275
theorem B9181421 : Blo 2149435 9181421 := bstep (se 3 (by rfl) ⟨1721516, by rfl⟩ : syracuseStep 9181421 = 3443033) B3443033
theorem B6120947 : Blo 2149435 6120947 := bstep (se 1 (by rfl) ⟨4590710, by rfl⟩ : syracuseStep 6120947 = 9181421) B9181421
theorem B4080631 : Blo 2149435 4080631 := bstep (se 1 (by rfl) ⟨3060473, by rfl⟩ : syracuseStep 4080631 = 6120947) B6120947
theorem B5440841 : Blo 2149435 5440841 := bstep (se 2 (by rfl) ⟨2040315, by rfl⟩ : syracuseStep 5440841 = 4080631) B4080631
theorem B3627227 : Blo 2149435 3627227 := bstep (se 1 (by rfl) ⟨2720420, by rfl⟩ : syracuseStep 3627227 = 5440841) B5440841
theorem B2418151 : Blo 2149435 2418151 := bstep (se 1 (by rfl) ⟨1813613, by rfl⟩ : syracuseStep 2418151 = 3627227) B3627227
theorem B3224201 : Blo 2149435 3224201 := bstep (se 2 (by rfl) ⟨1209075, by rfl⟩ : syracuseStep 3224201 = 2418151) B2418151
theorem B2149467 : Blo 2149435 2149467 := bstep (se 1 (by rfl) ⟨1612100, by rfl⟩ : syracuseStep 2149467 = 3224201) B3224201
theorem B10881701 : Blo 2149435 10881701 := bbase (se 4 (by rfl) ⟨1020159, by rfl⟩ : syracuseStep 10881701 = 2040319) (by norm_num)
theorem B7254467 : Blo 2149435 7254467 := bstep (se 1 (by rfl) ⟨5440850, by rfl⟩ : syracuseStep 7254467 = 10881701) B10881701
theorem B4836311 : Blo 2149435 4836311 := bstep (se 1 (by rfl) ⟨3627233, by rfl⟩ : syracuseStep 4836311 = 7254467) B7254467
theorem B3224207 : Blo 2149435 3224207 := bstep (se 1 (by rfl) ⟨2418155, by rfl⟩ : syracuseStep 3224207 = 4836311) B4836311
theorem B2149471 : Blo 2149435 2149471 := bstep (se 1 (by rfl) ⟨1612103, by rfl⟩ : syracuseStep 2149471 = 3224207) B3224207
theorem B3224213 : Blo 2149435 3224213 := bbase (se 6 (by rfl) ⟨75567, by rfl⟩ : syracuseStep 3224213 = 151135) (by norm_num)
theorem B2149475 : Blo 2149435 2149475 := bstep (se 1 (by rfl) ⟨1612106, by rfl⟩ : syracuseStep 2149475 = 3224213) B3224213
theorem B9804629 : Blo 2149435 9804629 := bbase (se 9 (by rfl) ⟨28724, by rfl⟩ : syracuseStep 9804629 = 57449) (by norm_num)
theorem B6536419 : Blo 2149435 6536419 := bstep (se 1 (by rfl) ⟨4902314, by rfl⟩ : syracuseStep 6536419 = 9804629) B9804629
theorem B34860901 : Blo 2149435 34860901 := bstep (se 4 (by rfl) ⟨3268209, by rfl⟩ : syracuseStep 34860901 = 6536419) B6536419
theorem B46481201 : Blo 2149435 46481201 := bstep (se 2 (by rfl) ⟨17430450, by rfl⟩ : syracuseStep 46481201 = 34860901) B34860901
theorem B30987467 : Blo 2149435 30987467 := bstep (se 1 (by rfl) ⟨23240600, by rfl⟩ : syracuseStep 30987467 = 46481201) B46481201
theorem B20658311 : Blo 2149435 20658311 := bstep (se 1 (by rfl) ⟨15493733, by rfl⟩ : syracuseStep 20658311 = 30987467) B30987467
theorem B13772207 : Blo 2149435 13772207 := bstep (se 1 (by rfl) ⟨10329155, by rfl⟩ : syracuseStep 13772207 = 20658311) B20658311
theorem B9181471 : Blo 2149435 9181471 := bstep (se 1 (by rfl) ⟨6886103, by rfl⟩ : syracuseStep 9181471 = 13772207) B13772207
theorem B12241961 : Blo 2149435 12241961 := bstep (se 2 (by rfl) ⟨4590735, by rfl⟩ : syracuseStep 12241961 = 9181471) B9181471
theorem B8161307 : Blo 2149435 8161307 := bstep (se 1 (by rfl) ⟨6120980, by rfl⟩ : syracuseStep 8161307 = 12241961) B12241961
theorem B5440871 : Blo 2149435 5440871 := bstep (se 1 (by rfl) ⟨4080653, by rfl⟩ : syracuseStep 5440871 = 8161307) B8161307
theorem B3627247 : Blo 2149435 3627247 := bstep (se 1 (by rfl) ⟨2720435, by rfl⟩ : syracuseStep 3627247 = 5440871) B5440871
theorem B4836329 : Blo 2149435 4836329 := bstep (se 2 (by rfl) ⟨1813623, by rfl⟩ : syracuseStep 4836329 = 3627247) B3627247
theorem B3224219 : Blo 2149435 3224219 := bstep (se 1 (by rfl) ⟨2418164, by rfl⟩ : syracuseStep 3224219 = 4836329) B4836329
theorem B2149479 : Blo 2149435 2149479 := bstep (se 1 (by rfl) ⟨1612109, by rfl⟩ : syracuseStep 2149479 = 3224219) B3224219
theorem B2418169 : Blo 2149435 2418169 := bbase (se 2 (by rfl) ⟨906813, by rfl⟩ : syracuseStep 2418169 = 1813627) (by norm_num)
theorem B3224225 : Blo 2149435 3224225 := bstep (se 2 (by rfl) ⟨1209084, by rfl⟩ : syracuseStep 3224225 = 2418169) B2418169
theorem B2149483 : Blo 2149435 2149483 := bstep (se 1 (by rfl) ⟨1612112, by rfl⟩ : syracuseStep 2149483 = 3224225) B3224225
theorem B5164597 : Blo 2149435 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B6886129 : Blo 2149435 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B9181505 : Blo 2149435 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B6121003 : Blo 2149435 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B8161337 : Blo 2149435 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B5440891 : Blo 2149435 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B7254521 : Blo 2149435 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B4836347 : Blo 2149435 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B3224231 : Blo 2149435 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B2149487 : Blo 2149435 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B3224237 : Blo 2149435 3224237 := bbase (se 3 (by rfl) ⟨604544, by rfl⟩ : syracuseStep 3224237 = 1209089) (by norm_num)
theorem B2149491 : Blo 2149435 2149491 := bstep (se 1 (by rfl) ⟨1612118, by rfl⟩ : syracuseStep 2149491 = 3224237) B3224237
theorem B4836365 : Blo 2149435 4836365 := bbase (se 3 (by rfl) ⟨906818, by rfl⟩ : syracuseStep 4836365 = 1813637) (by norm_num)
theorem B3224243 : Blo 2149435 3224243 := bstep (se 1 (by rfl) ⟨2418182, by rfl⟩ : syracuseStep 3224243 = 4836365) B4836365
theorem B2149495 : Blo 2149435 2149495 := bstep (se 1 (by rfl) ⟨1612121, by rfl⟩ : syracuseStep 2149495 = 3224243) B3224243
theorem B2720461 : Blo 2149435 2720461 := bbase (se 3 (by rfl) ⟨510086, by rfl⟩ : syracuseStep 2720461 = 1020173) (by norm_num)
theorem B3627281 : Blo 2149435 3627281 := bstep (se 2 (by rfl) ⟨1360230, by rfl⟩ : syracuseStep 3627281 = 2720461) B2720461
theorem B2418187 : Blo 2149435 2418187 := bstep (se 1 (by rfl) ⟨1813640, by rfl⟩ : syracuseStep 2418187 = 3627281) B3627281
theorem B3224249 : Blo 2149435 3224249 := bstep (se 2 (by rfl) ⟨1209093, by rfl⟩ : syracuseStep 3224249 = 2418187) B2418187
theorem B2149499 : Blo 2149435 2149499 := bstep (se 1 (by rfl) ⟨1612124, by rfl⟩ : syracuseStep 2149499 = 3224249) B3224249
theorem B5515165 : Blo 2149435 5515165 := bbase (se 3 (by rfl) ⟨1034093, by rfl⟩ : syracuseStep 5515165 = 2068187) (by norm_num)
theorem B7353553 : Blo 2149435 7353553 := bstep (se 2 (by rfl) ⟨2757582, by rfl⟩ : syracuseStep 7353553 = 5515165) B5515165
theorem B9804737 : Blo 2149435 9804737 := bstep (se 2 (by rfl) ⟨3676776, by rfl⟩ : syracuseStep 9804737 = 7353553) B7353553
theorem B26145965 : Blo 2149435 26145965 := bstep (se 3 (by rfl) ⟨4902368, by rfl⟩ : syracuseStep 26145965 = 9804737) B9804737
theorem B17430643 : Blo 2149435 17430643 := bstep (se 1 (by rfl) ⟨13072982, by rfl⟩ : syracuseStep 17430643 = 26145965) B26145965
theorem B23240857 : Blo 2149435 23240857 := bstep (se 2 (by rfl) ⟨8715321, by rfl⟩ : syracuseStep 23240857 = 17430643) B17430643
theorem B30987809 : Blo 2149435 30987809 := bstep (se 2 (by rfl) ⟨11620428, by rfl⟩ : syracuseStep 30987809 = 23240857) B23240857
theorem B20658539 : Blo 2149435 20658539 := bstep (se 1 (by rfl) ⟨15493904, by rfl⟩ : syracuseStep 20658539 = 30987809) B30987809
theorem B13772359 : Blo 2149435 13772359 := bstep (se 1 (by rfl) ⟨10329269, by rfl⟩ : syracuseStep 13772359 = 20658539) B20658539
theorem B18363145 : Blo 2149435 18363145 := bstep (se 2 (by rfl) ⟨6886179, by rfl⟩ : syracuseStep 18363145 = 13772359) B13772359
theorem B24484193 : Blo 2149435 24484193 := bstep (se 2 (by rfl) ⟨9181572, by rfl⟩ : syracuseStep 24484193 = 18363145) B18363145
theorem B16322795 : Blo 2149435 16322795 := bstep (se 1 (by rfl) ⟨12242096, by rfl⟩ : syracuseStep 16322795 = 24484193) B24484193
theorem B10881863 : Blo 2149435 10881863 := bstep (se 1 (by rfl) ⟨8161397, by rfl⟩ : syracuseStep 10881863 = 16322795) B16322795
theorem B7254575 : Blo 2149435 7254575 := bstep (se 1 (by rfl) ⟨5440931, by rfl⟩ : syracuseStep 7254575 = 10881863) B10881863
theorem B4836383 : Blo 2149435 4836383 := bstep (se 1 (by rfl) ⟨3627287, by rfl⟩ : syracuseStep 4836383 = 7254575) B7254575
theorem B3224255 : Blo 2149435 3224255 := bstep (se 1 (by rfl) ⟨2418191, by rfl⟩ : syracuseStep 3224255 = 4836383) B4836383
theorem B2149503 : Blo 2149435 2149503 := bstep (se 1 (by rfl) ⟨1612127, by rfl⟩ : syracuseStep 2149503 = 3224255) B3224255
theorem B3224261 : Blo 2149435 3224261 := bbase (se 4 (by rfl) ⟨302274, by rfl⟩ : syracuseStep 3224261 = 604549) (by norm_num)
theorem B2149507 : Blo 2149435 2149507 := bstep (se 1 (by rfl) ⟨1612130, by rfl⟩ : syracuseStep 2149507 = 3224261) B3224261
theorem B3627301 : Blo 2149435 3627301 := bbase (se 4 (by rfl) ⟨340059, by rfl⟩ : syracuseStep 3627301 = 680119) (by norm_num)
theorem B4836401 : Blo 2149435 4836401 := bstep (se 2 (by rfl) ⟨1813650, by rfl⟩ : syracuseStep 4836401 = 3627301) B3627301
theorem B3224267 : Blo 2149435 3224267 := bstep (se 1 (by rfl) ⟨2418200, by rfl⟩ : syracuseStep 3224267 = 4836401) B4836401
theorem B2149511 : Blo 2149435 2149511 := bstep (se 1 (by rfl) ⟨1612133, by rfl⟩ : syracuseStep 2149511 = 3224267) B3224267
theorem B2418205 : Blo 2149435 2418205 := bbase (se 3 (by rfl) ⟨453413, by rfl⟩ : syracuseStep 2418205 = 906827) (by norm_num)
theorem B3224273 : Blo 2149435 3224273 := bstep (se 2 (by rfl) ⟨1209102, by rfl⟩ : syracuseStep 3224273 = 2418205) B2418205
theorem B2149515 : Blo 2149435 2149515 := bstep (se 1 (by rfl) ⟨1612136, by rfl⟩ : syracuseStep 2149515 = 3224273) B3224273
theorem B7254629 : Blo 2149435 7254629 := bbase (se 4 (by rfl) ⟨680121, by rfl⟩ : syracuseStep 7254629 = 1360243) (by norm_num)
theorem B4836419 : Blo 2149435 4836419 := bstep (se 1 (by rfl) ⟨3627314, by rfl⟩ : syracuseStep 4836419 = 7254629) B7254629
theorem B3224279 : Blo 2149435 3224279 := bstep (se 1 (by rfl) ⟨2418209, by rfl⟩ : syracuseStep 3224279 = 4836419) B4836419
theorem B2149519 : Blo 2149435 2149519 := bstep (se 1 (by rfl) ⟨1612139, by rfl⟩ : syracuseStep 2149519 = 3224279) B3224279
theorem B3224285 : Blo 2149435 3224285 := bbase (se 3 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 3224285 = 1209107) (by norm_num)
theorem B2149523 : Blo 2149435 2149523 := bstep (se 1 (by rfl) ⟨1612142, by rfl⟩ : syracuseStep 2149523 = 3224285) B3224285
theorem B4836437 : Blo 2149435 4836437 := bbase (se 8 (by rfl) ⟨28338, by rfl⟩ : syracuseStep 4836437 = 56677) (by norm_num)
theorem B3224291 : Blo 2149435 3224291 := bstep (se 1 (by rfl) ⟨2418218, by rfl⟩ : syracuseStep 3224291 = 4836437) B4836437
theorem B2149527 : Blo 2149435 2149527 := bstep (se 1 (by rfl) ⟨1612145, by rfl⟩ : syracuseStep 2149527 = 3224291) B3224291
theorem B9306965 : Blo 2149435 9306965 := bbase (se 9 (by rfl) ⟨27266, by rfl⟩ : syracuseStep 9306965 = 54533) (by norm_num)
theorem B6204643 : Blo 2149435 6204643 := bstep (se 1 (by rfl) ⟨4653482, by rfl⟩ : syracuseStep 6204643 = 9306965) B9306965
theorem B33091429 : Blo 2149435 33091429 := bstep (se 4 (by rfl) ⟨3102321, by rfl⟩ : syracuseStep 33091429 = 6204643) B6204643
theorem B44121905 : Blo 2149435 44121905 := bstep (se 2 (by rfl) ⟨16545714, by rfl⟩ : syracuseStep 44121905 = 33091429) B33091429
theorem B29414603 : Blo 2149435 29414603 := bstep (se 1 (by rfl) ⟨22060952, by rfl⟩ : syracuseStep 29414603 = 44121905) B44121905
theorem B78438941 : Blo 2149435 78438941 := bstep (se 3 (by rfl) ⟨14707301, by rfl⟩ : syracuseStep 78438941 = 29414603) B29414603
theorem B52292627 : Blo 2149435 52292627 := bstep (se 1 (by rfl) ⟨39219470, by rfl⟩ : syracuseStep 52292627 = 78438941) B78438941
theorem B34861751 : Blo 2149435 34861751 := bstep (se 1 (by rfl) ⟨26146313, by rfl⟩ : syracuseStep 34861751 = 52292627) B52292627
theorem B23241167 : Blo 2149435 23241167 := bstep (se 1 (by rfl) ⟨17430875, by rfl⟩ : syracuseStep 23241167 = 34861751) B34861751
theorem B15494111 : Blo 2149435 15494111 := bstep (se 1 (by rfl) ⟨11620583, by rfl⟩ : syracuseStep 15494111 = 23241167) B23241167
theorem B10329407 : Blo 2149435 10329407 := bstep (se 1 (by rfl) ⟨7747055, by rfl⟩ : syracuseStep 10329407 = 15494111) B15494111
theorem B6886271 : Blo 2149435 6886271 := bstep (se 1 (by rfl) ⟨5164703, by rfl⟩ : syracuseStep 6886271 = 10329407) B10329407
theorem B4590847 : Blo 2149435 4590847 := bstep (se 1 (by rfl) ⟨3443135, by rfl⟩ : syracuseStep 4590847 = 6886271) B6886271
theorem B6121129 : Blo 2149435 6121129 := bstep (se 2 (by rfl) ⟨2295423, by rfl⟩ : syracuseStep 6121129 = 4590847) B4590847
theorem B8161505 : Blo 2149435 8161505 := bstep (se 2 (by rfl) ⟨3060564, by rfl⟩ : syracuseStep 8161505 = 6121129) B6121129
theorem B5441003 : Blo 2149435 5441003 := bstep (se 1 (by rfl) ⟨4080752, by rfl⟩ : syracuseStep 5441003 = 8161505) B8161505
theorem B3627335 : Blo 2149435 3627335 := bstep (se 1 (by rfl) ⟨2720501, by rfl⟩ : syracuseStep 3627335 = 5441003) B5441003
theorem B2418223 : Blo 2149435 2418223 := bstep (se 1 (by rfl) ⟨1813667, by rfl⟩ : syracuseStep 2418223 = 3627335) B3627335
theorem B3224297 : Blo 2149435 3224297 := bstep (se 2 (by rfl) ⟨1209111, by rfl⟩ : syracuseStep 3224297 = 2418223) B2418223
theorem B2149531 : Blo 2149435 2149531 := bstep (se 1 (by rfl) ⟨1612148, by rfl⟩ : syracuseStep 2149531 = 3224297) B3224297
theorem B2326745 : Blo 2149435 2326745 := bbase (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) (by norm_num)
theorem B6204653 : Blo 2149435 6204653 := bstep (se 3 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 6204653 = 2326745) B2326745
theorem B4136435 : Blo 2149435 4136435 := bstep (se 1 (by rfl) ⟨3102326, by rfl⟩ : syracuseStep 4136435 = 6204653) B6204653
theorem B176487893 : Blo 2149435 176487893 := bstep (se 7 (by rfl) ⟨2068217, by rfl⟩ : syracuseStep 176487893 = 4136435) B4136435
theorem B117658595 : Blo 2149435 117658595 := bstep (se 1 (by rfl) ⟨88243946, by rfl⟩ : syracuseStep 117658595 = 176487893) B176487893
theorem B78439063 : Blo 2149435 78439063 := bstep (se 1 (by rfl) ⟨58829297, by rfl⟩ : syracuseStep 78439063 = 117658595) B117658595
theorem B104585417 : Blo 2149435 104585417 := bstep (se 2 (by rfl) ⟨39219531, by rfl⟩ : syracuseStep 104585417 = 78439063) B78439063
theorem B69723611 : Blo 2149435 69723611 := bstep (se 1 (by rfl) ⟨52292708, by rfl⟩ : syracuseStep 69723611 = 104585417) B104585417
theorem B46482407 : Blo 2149435 46482407 := bstep (se 1 (by rfl) ⟨34861805, by rfl⟩ : syracuseStep 46482407 = 69723611) B69723611
theorem B30988271 : Blo 2149435 30988271 := bstep (se 1 (by rfl) ⟨23241203, by rfl⟩ : syracuseStep 30988271 = 46482407) B46482407
theorem B20658847 : Blo 2149435 20658847 := bstep (se 1 (by rfl) ⟨15494135, by rfl⟩ : syracuseStep 20658847 = 30988271) B30988271
theorem B27545129 : Blo 2149435 27545129 := bstep (se 2 (by rfl) ⟨10329423, by rfl⟩ : syracuseStep 27545129 = 20658847) B20658847
theorem B18363419 : Blo 2149435 18363419 := bstep (se 1 (by rfl) ⟨13772564, by rfl⟩ : syracuseStep 18363419 = 27545129) B27545129
theorem B12242279 : Blo 2149435 12242279 := bstep (se 1 (by rfl) ⟨9181709, by rfl⟩ : syracuseStep 12242279 = 18363419) B18363419
theorem B8161519 : Blo 2149435 8161519 := bstep (se 1 (by rfl) ⟨6121139, by rfl⟩ : syracuseStep 8161519 = 12242279) B12242279
theorem B10882025 : Blo 2149435 10882025 := bstep (se 2 (by rfl) ⟨4080759, by rfl⟩ : syracuseStep 10882025 = 8161519) B8161519
theorem B7254683 : Blo 2149435 7254683 := bstep (se 1 (by rfl) ⟨5441012, by rfl⟩ : syracuseStep 7254683 = 10882025) B10882025
theorem B4836455 : Blo 2149435 4836455 := bstep (se 1 (by rfl) ⟨3627341, by rfl⟩ : syracuseStep 4836455 = 7254683) B7254683
theorem B3224303 : Blo 2149435 3224303 := bstep (se 1 (by rfl) ⟨2418227, by rfl⟩ : syracuseStep 3224303 = 4836455) B4836455
theorem B2149535 : Blo 2149435 2149535 := bstep (se 1 (by rfl) ⟨1612151, by rfl⟩ : syracuseStep 2149535 = 3224303) B3224303
theorem B3224309 : Blo 2149435 3224309 := bbase (se 5 (by rfl) ⟨151139, by rfl⟩ : syracuseStep 3224309 = 302279) (by norm_num)
theorem B2149539 : Blo 2149435 2149539 := bstep (se 1 (by rfl) ⟨1612154, by rfl⟩ : syracuseStep 2149539 = 3224309) B3224309
theorem B6886309 : Blo 2149435 6886309 := bbase (se 4 (by rfl) ⟨645591, by rfl⟩ : syracuseStep 6886309 = 1291183) (by norm_num)
theorem B9181745 : Blo 2149435 9181745 := bstep (se 2 (by rfl) ⟨3443154, by rfl⟩ : syracuseStep 9181745 = 6886309) B6886309
theorem B6121163 : Blo 2149435 6121163 := bstep (se 1 (by rfl) ⟨4590872, by rfl⟩ : syracuseStep 6121163 = 9181745) B9181745
theorem B4080775 : Blo 2149435 4080775 := bstep (se 1 (by rfl) ⟨3060581, by rfl⟩ : syracuseStep 4080775 = 6121163) B6121163
theorem B5441033 : Blo 2149435 5441033 := bstep (se 2 (by rfl) ⟨2040387, by rfl⟩ : syracuseStep 5441033 = 4080775) B4080775
theorem B3627355 : Blo 2149435 3627355 := bstep (se 1 (by rfl) ⟨2720516, by rfl⟩ : syracuseStep 3627355 = 5441033) B5441033
theorem B4836473 : Blo 2149435 4836473 := bstep (se 2 (by rfl) ⟨1813677, by rfl⟩ : syracuseStep 4836473 = 3627355) B3627355
theorem B3224315 : Blo 2149435 3224315 := bstep (se 1 (by rfl) ⟨2418236, by rfl⟩ : syracuseStep 3224315 = 4836473) B4836473
theorem B2149543 : Blo 2149435 2149543 := bstep (se 1 (by rfl) ⟨1612157, by rfl⟩ : syracuseStep 2149543 = 3224315) B3224315
theorem B2418241 : Blo 2149435 2418241 := bbase (se 2 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 2418241 = 1813681) (by norm_num)
theorem B3224321 : Blo 2149435 3224321 := bstep (se 2 (by rfl) ⟨1209120, by rfl⟩ : syracuseStep 3224321 = 2418241) B2418241
theorem B2149547 : Blo 2149435 2149547 := bstep (se 1 (by rfl) ⟨1612160, by rfl⟩ : syracuseStep 2149547 = 3224321) B3224321
theorem B5441053 : Blo 2149435 5441053 := bbase (se 3 (by rfl) ⟨1020197, by rfl⟩ : syracuseStep 5441053 = 2040395) (by norm_num)
theorem B7254737 : Blo 2149435 7254737 := bstep (se 2 (by rfl) ⟨2720526, by rfl⟩ : syracuseStep 7254737 = 5441053) B5441053
theorem B4836491 : Blo 2149435 4836491 := bstep (se 1 (by rfl) ⟨3627368, by rfl⟩ : syracuseStep 4836491 = 7254737) B7254737
theorem B3224327 : Blo 2149435 3224327 := bstep (se 1 (by rfl) ⟨2418245, by rfl⟩ : syracuseStep 3224327 = 4836491) B4836491
theorem B2149551 : Blo 2149435 2149551 := bstep (se 1 (by rfl) ⟨1612163, by rfl⟩ : syracuseStep 2149551 = 3224327) B3224327
theorem B3224333 : Blo 2149435 3224333 := bbase (se 3 (by rfl) ⟨604562, by rfl⟩ : syracuseStep 3224333 = 1209125) (by norm_num)
theorem B2149555 : Blo 2149435 2149555 := bstep (se 1 (by rfl) ⟨1612166, by rfl⟩ : syracuseStep 2149555 = 3224333) B3224333
theorem B4836509 : Blo 2149435 4836509 := bbase (se 3 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 4836509 = 1813691) (by norm_num)
theorem B3224339 : Blo 2149435 3224339 := bstep (se 1 (by rfl) ⟨2418254, by rfl⟩ : syracuseStep 3224339 = 4836509) B4836509
theorem B2149559 : Blo 2149435 2149559 := bstep (se 1 (by rfl) ⟨1612169, by rfl⟩ : syracuseStep 2149559 = 3224339) B3224339
theorem B3627389 : Blo 2149435 3627389 := bbase (se 3 (by rfl) ⟨680135, by rfl⟩ : syracuseStep 3627389 = 1360271) (by norm_num)
theorem B2418259 : Blo 2149435 2418259 := bstep (se 1 (by rfl) ⟨1813694, by rfl⟩ : syracuseStep 2418259 = 3627389) B3627389
theorem B3224345 : Blo 2149435 3224345 := bstep (se 2 (by rfl) ⟨1209129, by rfl⟩ : syracuseStep 3224345 = 2418259) B2418259
theorem B2149563 : Blo 2149435 2149563 := bstep (se 1 (by rfl) ⟨1612172, by rfl⟩ : syracuseStep 2149563 = 3224345) B3224345
theorem B5164789 : Blo 2149435 5164789 := bbase (se 5 (by rfl) ⟨242099, by rfl⟩ : syracuseStep 5164789 = 484199) (by norm_num)
theorem B6886385 : Blo 2149435 6886385 := bstep (se 2 (by rfl) ⟨2582394, by rfl⟩ : syracuseStep 6886385 = 5164789) B5164789
theorem B4590923 : Blo 2149435 4590923 := bstep (se 1 (by rfl) ⟨3443192, by rfl⟩ : syracuseStep 4590923 = 6886385) B6886385
theorem B12242461 : Blo 2149435 12242461 := bstep (se 3 (by rfl) ⟨2295461, by rfl⟩ : syracuseStep 12242461 = 4590923) B4590923
theorem B16323281 : Blo 2149435 16323281 := bstep (se 2 (by rfl) ⟨6121230, by rfl⟩ : syracuseStep 16323281 = 12242461) B12242461
theorem B10882187 : Blo 2149435 10882187 := bstep (se 1 (by rfl) ⟨8161640, by rfl⟩ : syracuseStep 10882187 = 16323281) B16323281
theorem B7254791 : Blo 2149435 7254791 := bstep (se 1 (by rfl) ⟨5441093, by rfl⟩ : syracuseStep 7254791 = 10882187) B10882187
theorem B4836527 : Blo 2149435 4836527 := bstep (se 1 (by rfl) ⟨3627395, by rfl⟩ : syracuseStep 4836527 = 7254791) B7254791
theorem B3224351 : Blo 2149435 3224351 := bstep (se 1 (by rfl) ⟨2418263, by rfl⟩ : syracuseStep 3224351 = 4836527) B4836527
theorem B2149567 : Blo 2149435 2149567 := bstep (se 1 (by rfl) ⟨1612175, by rfl⟩ : syracuseStep 2149567 = 3224351) B3224351
theorem B3224357 : Blo 2149435 3224357 := bbase (se 4 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 3224357 = 604567) (by norm_num)
theorem B2149571 : Blo 2149435 2149571 := bstep (se 1 (by rfl) ⟨1612178, by rfl⟩ : syracuseStep 2149571 = 3224357) B3224357
theorem B2720557 : Blo 2149435 2720557 := bbase (se 3 (by rfl) ⟨510104, by rfl⟩ : syracuseStep 2720557 = 1020209) (by norm_num)
theorem B3627409 : Blo 2149435 3627409 := bstep (se 2 (by rfl) ⟨1360278, by rfl⟩ : syracuseStep 3627409 = 2720557) B2720557
theorem B4836545 : Blo 2149435 4836545 := bstep (se 2 (by rfl) ⟨1813704, by rfl⟩ : syracuseStep 4836545 = 3627409) B3627409
theorem B3224363 : Blo 2149435 3224363 := bstep (se 1 (by rfl) ⟨2418272, by rfl⟩ : syracuseStep 3224363 = 4836545) B4836545
theorem B2149575 : Blo 2149435 2149575 := bstep (se 1 (by rfl) ⟨1612181, by rfl⟩ : syracuseStep 2149575 = 3224363) B3224363
theorem B2418277 : Blo 2149435 2418277 := bbase (se 4 (by rfl) ⟨226713, by rfl⟩ : syracuseStep 2418277 = 453427) (by norm_num)
theorem B3224369 : Blo 2149435 3224369 := bstep (se 2 (by rfl) ⟨1209138, by rfl⟩ : syracuseStep 3224369 = 2418277) B2418277
theorem B2149579 : Blo 2149435 2149579 := bstep (se 1 (by rfl) ⟨1612184, by rfl⟩ : syracuseStep 2149579 = 3224369) B3224369
theorem B5164829 : Blo 2149435 5164829 := bbase (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) (by norm_num)
theorem B3443219 : Blo 2149435 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B2295479 : Blo 2149435 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B6121277 : Blo 2149435 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B4080851 : Blo 2149435 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B2720567 : Blo 2149435 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B7254845 : Blo 2149435 7254845 := bstep (se 3 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 7254845 = 2720567) B2720567
theorem B4836563 : Blo 2149435 4836563 := bstep (se 1 (by rfl) ⟨3627422, by rfl⟩ : syracuseStep 4836563 = 7254845) B7254845
theorem B3224375 : Blo 2149435 3224375 := bstep (se 1 (by rfl) ⟨2418281, by rfl⟩ : syracuseStep 3224375 = 4836563) B4836563
theorem B2149583 : Blo 2149435 2149583 := bstep (se 1 (by rfl) ⟨1612187, by rfl⟩ : syracuseStep 2149583 = 3224375) B3224375
theorem B3224381 : Blo 2149435 3224381 := bbase (se 3 (by rfl) ⟨604571, by rfl⟩ : syracuseStep 3224381 = 1209143) (by norm_num)
theorem B2149587 : Blo 2149435 2149587 := bstep (se 1 (by rfl) ⟨1612190, by rfl⟩ : syracuseStep 2149587 = 3224381) B3224381
theorem B4836581 : Blo 2149435 4836581 := bbase (se 4 (by rfl) ⟨453429, by rfl⟩ : syracuseStep 4836581 = 906859) (by norm_num)
theorem B3224387 : Blo 2149435 3224387 := bstep (se 1 (by rfl) ⟨2418290, by rfl⟩ : syracuseStep 3224387 = 4836581) B4836581
theorem B2149591 : Blo 2149435 2149591 := bstep (se 1 (by rfl) ⟨1612193, by rfl⟩ : syracuseStep 2149591 = 3224387) B3224387
theorem B5441165 : Blo 2149435 5441165 := bbase (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) (by norm_num)
theorem B3627443 : Blo 2149435 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B2418295 : Blo 2149435 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B3224393 : Blo 2149435 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B2149595 : Blo 2149435 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B3060661 : Blo 2149435 3060661 := bbase (se 5 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 3060661 = 286937) (by norm_num)
theorem B4080881 : Blo 2149435 4080881 := bstep (se 2 (by rfl) ⟨1530330, by rfl⟩ : syracuseStep 4080881 = 3060661) B3060661
theorem B10882349 : Blo 2149435 10882349 := bstep (se 3 (by rfl) ⟨2040440, by rfl⟩ : syracuseStep 10882349 = 4080881) B4080881
theorem B7254899 : Blo 2149435 7254899 := bstep (se 1 (by rfl) ⟨5441174, by rfl⟩ : syracuseStep 7254899 = 10882349) B10882349
theorem B4836599 : Blo 2149435 4836599 := bstep (se 1 (by rfl) ⟨3627449, by rfl⟩ : syracuseStep 4836599 = 7254899) B7254899
theorem B3224399 : Blo 2149435 3224399 := bstep (se 1 (by rfl) ⟨2418299, by rfl⟩ : syracuseStep 3224399 = 4836599) B4836599
theorem B2149599 : Blo 2149435 2149599 := bstep (se 1 (by rfl) ⟨1612199, by rfl⟩ : syracuseStep 2149599 = 3224399) B3224399
theorem B3224405 : Blo 2149435 3224405 := bbase (se 9 (by rfl) ⟨9446, by rfl⟩ : syracuseStep 3224405 = 18893) (by norm_num)
theorem B2149603 : Blo 2149435 2149603 := bstep (se 1 (by rfl) ⟨1612202, by rfl⟩ : syracuseStep 2149603 = 3224405) B3224405
theorem B2178937 : Blo 2149435 2178937 := bbase (se 2 (by rfl) ⟨817101, by rfl⟩ : syracuseStep 2178937 = 1634203) (by norm_num)
theorem B2905249 : Blo 2149435 2905249 := bstep (se 2 (by rfl) ⟨1089468, by rfl⟩ : syracuseStep 2905249 = 2178937) B2178937
theorem B3873665 : Blo 2149435 3873665 := bstep (se 2 (by rfl) ⟨1452624, by rfl⟩ : syracuseStep 3873665 = 2905249) B2905249
theorem B2582443 : Blo 2149435 2582443 := bstep (se 1 (by rfl) ⟨1936832, by rfl⟩ : syracuseStep 2582443 = 3873665) B3873665
theorem B3443257 : Blo 2149435 3443257 := bstep (se 2 (by rfl) ⟨1291221, by rfl⟩ : syracuseStep 3443257 = 2582443) B2582443
theorem B4591009 : Blo 2149435 4591009 := bstep (se 2 (by rfl) ⟨1721628, by rfl⟩ : syracuseStep 4591009 = 3443257) B3443257
theorem B6121345 : Blo 2149435 6121345 := bstep (se 2 (by rfl) ⟨2295504, by rfl⟩ : syracuseStep 6121345 = 4591009) B4591009
theorem B8161793 : Blo 2149435 8161793 := bstep (se 2 (by rfl) ⟨3060672, by rfl⟩ : syracuseStep 8161793 = 6121345) B6121345
theorem B5441195 : Blo 2149435 5441195 := bstep (se 1 (by rfl) ⟨4080896, by rfl⟩ : syracuseStep 5441195 = 8161793) B8161793
theorem B3627463 : Blo 2149435 3627463 := bstep (se 1 (by rfl) ⟨2720597, by rfl⟩ : syracuseStep 3627463 = 5441195) B5441195
theorem B4836617 : Blo 2149435 4836617 := bstep (se 2 (by rfl) ⟨1813731, by rfl⟩ : syracuseStep 4836617 = 3627463) B3627463
theorem B3224411 : Blo 2149435 3224411 := bstep (se 1 (by rfl) ⟨2418308, by rfl⟩ : syracuseStep 3224411 = 4836617) B4836617
theorem B2149607 : Blo 2149435 2149607 := bstep (se 1 (by rfl) ⟨1612205, by rfl⟩ : syracuseStep 2149607 = 3224411) B3224411
theorem B2418313 : Blo 2149435 2418313 := bbase (se 2 (by rfl) ⟨906867, by rfl⟩ : syracuseStep 2418313 = 1813735) (by norm_num)
theorem B3224417 : Blo 2149435 3224417 := bstep (se 2 (by rfl) ⟨1209156, by rfl⟩ : syracuseStep 3224417 = 2418313) B2418313
theorem B2149611 : Blo 2149435 2149611 := bstep (se 1 (by rfl) ⟨1612208, by rfl⟩ : syracuseStep 2149611 = 3224417) B3224417
theorem B23242069 : Blo 2149435 23242069 := bbase (se 12 (by rfl) ⟨8511, by rfl⟩ : syracuseStep 23242069 = 17023) (by norm_num)
theorem B30989425 : Blo 2149435 30989425 := bstep (se 2 (by rfl) ⟨11621034, by rfl⟩ : syracuseStep 30989425 = 23242069) B23242069
theorem B41319233 : Blo 2149435 41319233 := bstep (se 2 (by rfl) ⟨15494712, by rfl⟩ : syracuseStep 41319233 = 30989425) B30989425
theorem B27546155 : Blo 2149435 27546155 := bstep (se 1 (by rfl) ⟨20659616, by rfl⟩ : syracuseStep 27546155 = 41319233) B41319233
theorem B18364103 : Blo 2149435 18364103 := bstep (se 1 (by rfl) ⟨13773077, by rfl⟩ : syracuseStep 18364103 = 27546155) B27546155
theorem B12242735 : Blo 2149435 12242735 := bstep (se 1 (by rfl) ⟨9182051, by rfl⟩ : syracuseStep 12242735 = 18364103) B18364103
theorem B8161823 : Blo 2149435 8161823 := bstep (se 1 (by rfl) ⟨6121367, by rfl⟩ : syracuseStep 8161823 = 12242735) B12242735
theorem B5441215 : Blo 2149435 5441215 := bstep (se 1 (by rfl) ⟨4080911, by rfl⟩ : syracuseStep 5441215 = 8161823) B8161823
theorem B7254953 : Blo 2149435 7254953 := bstep (se 2 (by rfl) ⟨2720607, by rfl⟩ : syracuseStep 7254953 = 5441215) B5441215
theorem B4836635 : Blo 2149435 4836635 := bstep (se 1 (by rfl) ⟨3627476, by rfl⟩ : syracuseStep 4836635 = 7254953) B7254953
theorem B3224423 : Blo 2149435 3224423 := bstep (se 1 (by rfl) ⟨2418317, by rfl⟩ : syracuseStep 3224423 = 4836635) B4836635
theorem B2149615 : Blo 2149435 2149615 := bstep (se 1 (by rfl) ⟨1612211, by rfl⟩ : syracuseStep 2149615 = 3224423) B3224423
theorem B3224429 : Blo 2149435 3224429 := bbase (se 3 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 3224429 = 1209161) (by norm_num)
theorem B2149619 : Blo 2149435 2149619 := bstep (se 1 (by rfl) ⟨1612214, by rfl⟩ : syracuseStep 2149619 = 3224429) B3224429
theorem B4836653 : Blo 2149435 4836653 := bbase (se 3 (by rfl) ⟨906872, by rfl⟩ : syracuseStep 4836653 = 1813745) (by norm_num)
theorem B3224435 : Blo 2149435 3224435 := bstep (se 1 (by rfl) ⟨2418326, by rfl⟩ : syracuseStep 3224435 = 4836653) B4836653
theorem B2149623 : Blo 2149435 2149623 := bstep (se 1 (by rfl) ⟨1612217, by rfl⟩ : syracuseStep 2149623 = 3224435) B3224435
theorem B3873701 : Blo 2149435 3873701 := bbase (se 4 (by rfl) ⟨363159, by rfl⟩ : syracuseStep 3873701 = 726319) (by norm_num)
theorem B10329869 : Blo 2149435 10329869 := bstep (se 3 (by rfl) ⟨1936850, by rfl⟩ : syracuseStep 10329869 = 3873701) B3873701
theorem B6886579 : Blo 2149435 6886579 := bstep (se 1 (by rfl) ⟨5164934, by rfl⟩ : syracuseStep 6886579 = 10329869) B10329869
theorem B9182105 : Blo 2149435 9182105 := bstep (se 2 (by rfl) ⟨3443289, by rfl⟩ : syracuseStep 9182105 = 6886579) B6886579
theorem B6121403 : Blo 2149435 6121403 := bstep (se 1 (by rfl) ⟨4591052, by rfl⟩ : syracuseStep 6121403 = 9182105) B9182105
theorem B4080935 : Blo 2149435 4080935 := bstep (se 1 (by rfl) ⟨3060701, by rfl⟩ : syracuseStep 4080935 = 6121403) B6121403
theorem B2720623 : Blo 2149435 2720623 := bstep (se 1 (by rfl) ⟨2040467, by rfl⟩ : syracuseStep 2720623 = 4080935) B4080935
theorem B3627497 : Blo 2149435 3627497 := bstep (se 2 (by rfl) ⟨1360311, by rfl⟩ : syracuseStep 3627497 = 2720623) B2720623
theorem B2418331 : Blo 2149435 2418331 := bstep (se 1 (by rfl) ⟨1813748, by rfl⟩ : syracuseStep 2418331 = 3627497) B3627497
theorem B3224441 : Blo 2149435 3224441 := bstep (se 2 (by rfl) ⟨1209165, by rfl⟩ : syracuseStep 3224441 = 2418331) B2418331
theorem B2149627 : Blo 2149435 2149627 := bstep (se 1 (by rfl) ⟨1612220, by rfl⟩ : syracuseStep 2149627 = 3224441) B3224441
theorem B2326849 : Blo 2149435 2326849 := bbase (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) (by norm_num)
theorem B12409861 : Blo 2149435 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B16546481 : Blo 2149435 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B11030987 : Blo 2149435 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B7353991 : Blo 2149435 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B9805321 : Blo 2149435 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B13073761 : Blo 2149435 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B17431681 : Blo 2149435 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B23242241 : Blo 2149435 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B15494827 : Blo 2149435 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B20659769 : Blo 2149435 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B13773179 : Blo 2149435 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B36728477 : Blo 2149435 36728477 := bstep (se 3 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 36728477 = 13773179) B13773179
theorem B24485651 : Blo 2149435 24485651 := bstep (se 1 (by rfl) ⟨18364238, by rfl⟩ : syracuseStep 24485651 = 36728477) B36728477
theorem B16323767 : Blo 2149435 16323767 := bstep (se 1 (by rfl) ⟨12242825, by rfl⟩ : syracuseStep 16323767 = 24485651) B24485651
theorem B10882511 : Blo 2149435 10882511 := bstep (se 1 (by rfl) ⟨8161883, by rfl⟩ : syracuseStep 10882511 = 16323767) B16323767
theorem B7255007 : Blo 2149435 7255007 := bstep (se 1 (by rfl) ⟨5441255, by rfl⟩ : syracuseStep 7255007 = 10882511) B10882511
theorem B4836671 : Blo 2149435 4836671 := bstep (se 1 (by rfl) ⟨3627503, by rfl⟩ : syracuseStep 4836671 = 7255007) B7255007
theorem B3224447 : Blo 2149435 3224447 := bstep (se 1 (by rfl) ⟨2418335, by rfl⟩ : syracuseStep 3224447 = 4836671) B4836671
theorem B2149631 : Blo 2149435 2149631 := bstep (se 1 (by rfl) ⟨1612223, by rfl⟩ : syracuseStep 2149631 = 3224447) B3224447
theorem B3224453 : Blo 2149435 3224453 := bbase (se 4 (by rfl) ⟨302292, by rfl⟩ : syracuseStep 3224453 = 604585) (by norm_num)
theorem B2149635 : Blo 2149435 2149635 := bstep (se 1 (by rfl) ⟨1612226, by rfl⟩ : syracuseStep 2149635 = 3224453) B3224453
theorem B3627517 : Blo 2149435 3627517 := bbase (se 3 (by rfl) ⟨680159, by rfl⟩ : syracuseStep 3627517 = 1360319) (by norm_num)
theorem B4836689 : Blo 2149435 4836689 := bstep (se 2 (by rfl) ⟨1813758, by rfl⟩ : syracuseStep 4836689 = 3627517) B3627517
theorem B3224459 : Blo 2149435 3224459 := bstep (se 1 (by rfl) ⟨2418344, by rfl⟩ : syracuseStep 3224459 = 4836689) B4836689
theorem B2149639 : Blo 2149435 2149639 := bstep (se 1 (by rfl) ⟨1612229, by rfl⟩ : syracuseStep 2149639 = 3224459) B3224459
theorem B2418349 : Blo 2149435 2418349 := bbase (se 3 (by rfl) ⟨453440, by rfl⟩ : syracuseStep 2418349 = 906881) (by norm_num)
theorem B3224465 : Blo 2149435 3224465 := bstep (se 2 (by rfl) ⟨1209174, by rfl⟩ : syracuseStep 3224465 = 2418349) B2418349
theorem B2149643 : Blo 2149435 2149643 := bstep (se 1 (by rfl) ⟨1612232, by rfl⟩ : syracuseStep 2149643 = 3224465) B3224465
theorem B7255061 : Blo 2149435 7255061 := bbase (se 6 (by rfl) ⟨170040, by rfl⟩ : syracuseStep 7255061 = 340081) (by norm_num)
theorem B4836707 : Blo 2149435 4836707 := bstep (se 1 (by rfl) ⟨3627530, by rfl⟩ : syracuseStep 4836707 = 7255061) B7255061
theorem B3224471 : Blo 2149435 3224471 := bstep (se 1 (by rfl) ⟨2418353, by rfl⟩ : syracuseStep 3224471 = 4836707) B4836707
theorem B2149647 : Blo 2149435 2149647 := bstep (se 1 (by rfl) ⟨1612235, by rfl⟩ : syracuseStep 2149647 = 3224471) B3224471
theorem B3224477 : Blo 2149435 3224477 := bbase (se 3 (by rfl) ⟨604589, by rfl⟩ : syracuseStep 3224477 = 1209179) (by norm_num)
theorem B2149651 : Blo 2149435 2149651 := bstep (se 1 (by rfl) ⟨1612238, by rfl⟩ : syracuseStep 2149651 = 3224477) B3224477
theorem B4836725 : Blo 2149435 4836725 := bbase (se 5 (by rfl) ⟨226721, by rfl⟩ : syracuseStep 4836725 = 453443) (by norm_num)
theorem B3224483 : Blo 2149435 3224483 := bstep (se 1 (by rfl) ⟨2418362, by rfl⟩ : syracuseStep 3224483 = 4836725) B4836725
theorem B2149655 : Blo 2149435 2149655 := bstep (se 1 (by rfl) ⟨1612241, by rfl⟩ : syracuseStep 2149655 = 3224483) B3224483
theorem B10330021 : Blo 2149435 10330021 := bbase (se 4 (by rfl) ⟨968439, by rfl⟩ : syracuseStep 10330021 = 1936879) (by norm_num)
theorem B13773361 : Blo 2149435 13773361 := bstep (se 2 (by rfl) ⟨5165010, by rfl⟩ : syracuseStep 13773361 = 10330021) B10330021
theorem B18364481 : Blo 2149435 18364481 := bstep (se 2 (by rfl) ⟨6886680, by rfl⟩ : syracuseStep 18364481 = 13773361) B13773361
theorem B12242987 : Blo 2149435 12242987 := bstep (se 1 (by rfl) ⟨9182240, by rfl⟩ : syracuseStep 12242987 = 18364481) B18364481
theorem B8161991 : Blo 2149435 8161991 := bstep (se 1 (by rfl) ⟨6121493, by rfl⟩ : syracuseStep 8161991 = 12242987) B12242987
theorem B5441327 : Blo 2149435 5441327 := bstep (se 1 (by rfl) ⟨4080995, by rfl⟩ : syracuseStep 5441327 = 8161991) B8161991
theorem B3627551 : Blo 2149435 3627551 := bstep (se 1 (by rfl) ⟨2720663, by rfl⟩ : syracuseStep 3627551 = 5441327) B5441327
theorem B2418367 : Blo 2149435 2418367 := bstep (se 1 (by rfl) ⟨1813775, by rfl⟩ : syracuseStep 2418367 = 3627551) B3627551
theorem B3224489 : Blo 2149435 3224489 := bstep (se 2 (by rfl) ⟨1209183, by rfl⟩ : syracuseStep 3224489 = 2418367) B2418367
theorem B2149659 : Blo 2149435 2149659 := bstep (se 1 (by rfl) ⟨1612244, by rfl⟩ : syracuseStep 2149659 = 3224489) B3224489
theorem B8162005 : Blo 2149435 8162005 := bbase (se 7 (by rfl) ⟨95648, by rfl⟩ : syracuseStep 8162005 = 191297) (by norm_num)
theorem B10882673 : Blo 2149435 10882673 := bstep (se 2 (by rfl) ⟨4081002, by rfl⟩ : syracuseStep 10882673 = 8162005) B8162005
theorem B7255115 : Blo 2149435 7255115 := bstep (se 1 (by rfl) ⟨5441336, by rfl⟩ : syracuseStep 7255115 = 10882673) B10882673
theorem B4836743 : Blo 2149435 4836743 := bstep (se 1 (by rfl) ⟨3627557, by rfl⟩ : syracuseStep 4836743 = 7255115) B7255115
theorem B3224495 : Blo 2149435 3224495 := bstep (se 1 (by rfl) ⟨2418371, by rfl⟩ : syracuseStep 3224495 = 4836743) B4836743
theorem B2149663 : Blo 2149435 2149663 := bstep (se 1 (by rfl) ⟨1612247, by rfl⟩ : syracuseStep 2149663 = 3224495) B3224495
theorem B3224501 : Blo 2149435 3224501 := bbase (se 5 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 3224501 = 302297) (by norm_num)
theorem B2149667 : Blo 2149435 2149667 := bstep (se 1 (by rfl) ⟨1612250, by rfl⟩ : syracuseStep 2149667 = 3224501) B3224501
theorem B5441357 : Blo 2149435 5441357 := bbase (se 3 (by rfl) ⟨1020254, by rfl⟩ : syracuseStep 5441357 = 2040509) (by norm_num)
theorem B3627571 : Blo 2149435 3627571 := bstep (se 1 (by rfl) ⟨2720678, by rfl⟩ : syracuseStep 3627571 = 5441357) B5441357
theorem B4836761 : Blo 2149435 4836761 := bstep (se 2 (by rfl) ⟨1813785, by rfl⟩ : syracuseStep 4836761 = 3627571) B3627571
theorem B3224507 : Blo 2149435 3224507 := bstep (se 1 (by rfl) ⟨2418380, by rfl⟩ : syracuseStep 3224507 = 4836761) B4836761
theorem B2149671 : Blo 2149435 2149671 := bstep (se 1 (by rfl) ⟨1612253, by rfl⟩ : syracuseStep 2149671 = 3224507) B3224507
theorem B2418385 : Blo 2149435 2418385 := bbase (se 2 (by rfl) ⟨906894, by rfl⟩ : syracuseStep 2418385 = 1813789) (by norm_num)
theorem B3224513 : Blo 2149435 3224513 := bstep (se 2 (by rfl) ⟨1209192, by rfl⟩ : syracuseStep 3224513 = 2418385) B2418385
theorem B2149675 : Blo 2149435 2149675 := bstep (se 1 (by rfl) ⟨1612256, by rfl⟩ : syracuseStep 2149675 = 3224513) B3224513
theorem B7747589 : Blo 2149435 7747589 := bbase (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) (by norm_num)
theorem B5165059 : Blo 2149435 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B6886745 : Blo 2149435 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B4591163 : Blo 2149435 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B3060775 : Blo 2149435 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B4081033 : Blo 2149435 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B5441377 : Blo 2149435 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B7255169 : Blo 2149435 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B4836779 : Blo 2149435 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B3224519 : Blo 2149435 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B2149679 : Blo 2149435 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B3224525 : Blo 2149435 3224525 := bbase (se 3 (by rfl) ⟨604598, by rfl⟩ : syracuseStep 3224525 = 1209197) (by norm_num)
theorem B2149683 : Blo 2149435 2149683 := bstep (se 1 (by rfl) ⟨1612262, by rfl⟩ : syracuseStep 2149683 = 3224525) B3224525
theorem B4836797 : Blo 2149435 4836797 := bbase (se 3 (by rfl) ⟨906899, by rfl⟩ : syracuseStep 4836797 = 1813799) (by norm_num)
theorem B3224531 : Blo 2149435 3224531 := bstep (se 1 (by rfl) ⟨2418398, by rfl⟩ : syracuseStep 3224531 = 4836797) B4836797
theorem B2149687 : Blo 2149435 2149687 := bstep (se 1 (by rfl) ⟨1612265, by rfl⟩ : syracuseStep 2149687 = 3224531) B3224531
theorem B3627605 : Blo 2149435 3627605 := bbase (se 8 (by rfl) ⟨21255, by rfl⟩ : syracuseStep 3627605 = 42511) (by norm_num)
theorem B2418403 : Blo 2149435 2418403 := bstep (se 1 (by rfl) ⟨1813802, by rfl⟩ : syracuseStep 2418403 = 3627605) B3627605
theorem B3224537 : Blo 2149435 3224537 := bstep (se 2 (by rfl) ⟨1209201, by rfl⟩ : syracuseStep 3224537 = 2418403) B2418403
theorem B2149691 : Blo 2149435 2149691 := bstep (se 1 (by rfl) ⟨1612268, by rfl⟩ : syracuseStep 2149691 = 3224537) B3224537
theorem B6537077 : Blo 2149435 6537077 := bbase (se 5 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 6537077 = 612851) (by norm_num)
theorem B4358051 : Blo 2149435 4358051 := bstep (se 1 (by rfl) ⟨3268538, by rfl⟩ : syracuseStep 4358051 = 6537077) B6537077
theorem B2905367 : Blo 2149435 2905367 := bstep (se 1 (by rfl) ⟨2179025, by rfl⟩ : syracuseStep 2905367 = 4358051) B4358051
theorem B7747645 : Blo 2149435 7747645 := bstep (se 3 (by rfl) ⟨1452683, by rfl⟩ : syracuseStep 7747645 = 2905367) B2905367
theorem B10330193 : Blo 2149435 10330193 := bstep (se 2 (by rfl) ⟨3873822, by rfl⟩ : syracuseStep 10330193 = 7747645) B7747645
theorem B6886795 : Blo 2149435 6886795 := bstep (se 1 (by rfl) ⟨5165096, by rfl⟩ : syracuseStep 6886795 = 10330193) B10330193
theorem B9182393 : Blo 2149435 9182393 := bstep (se 2 (by rfl) ⟨3443397, by rfl⟩ : syracuseStep 9182393 = 6886795) B6886795
theorem B6121595 : Blo 2149435 6121595 := bstep (se 1 (by rfl) ⟨4591196, by rfl⟩ : syracuseStep 6121595 = 9182393) B9182393
theorem B16324253 : Blo 2149435 16324253 := bstep (se 3 (by rfl) ⟨3060797, by rfl⟩ : syracuseStep 16324253 = 6121595) B6121595
theorem B10882835 : Blo 2149435 10882835 := bstep (se 1 (by rfl) ⟨8162126, by rfl⟩ : syracuseStep 10882835 = 16324253) B16324253
theorem B7255223 : Blo 2149435 7255223 := bstep (se 1 (by rfl) ⟨5441417, by rfl⟩ : syracuseStep 7255223 = 10882835) B10882835
theorem B4836815 : Blo 2149435 4836815 := bstep (se 1 (by rfl) ⟨3627611, by rfl⟩ : syracuseStep 4836815 = 7255223) B7255223
theorem B3224543 : Blo 2149435 3224543 := bstep (se 1 (by rfl) ⟨2418407, by rfl⟩ : syracuseStep 3224543 = 4836815) B4836815
theorem B2149695 : Blo 2149435 2149695 := bstep (se 1 (by rfl) ⟨1612271, by rfl⟩ : syracuseStep 2149695 = 3224543) B3224543
theorem B3224549 : Blo 2149435 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B2149699 : Blo 2149435 2149699 := bstep (se 1 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 2149699 = 3224549) B3224549
theorem B5165117 : Blo 2149435 5165117 := bbase (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) (by norm_num)
theorem B3443411 : Blo 2149435 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B9182429 : Blo 2149435 9182429 := bstep (se 3 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 9182429 = 3443411) B3443411
theorem B6121619 : Blo 2149435 6121619 := bstep (se 1 (by rfl) ⟨4591214, by rfl⟩ : syracuseStep 6121619 = 9182429) B9182429
theorem B4081079 : Blo 2149435 4081079 := bstep (se 1 (by rfl) ⟨3060809, by rfl⟩ : syracuseStep 4081079 = 6121619) B6121619
theorem B2720719 : Blo 2149435 2720719 := bstep (se 1 (by rfl) ⟨2040539, by rfl⟩ : syracuseStep 2720719 = 4081079) B4081079
theorem B3627625 : Blo 2149435 3627625 := bstep (se 2 (by rfl) ⟨1360359, by rfl⟩ : syracuseStep 3627625 = 2720719) B2720719
theorem B4836833 : Blo 2149435 4836833 := bstep (se 2 (by rfl) ⟨1813812, by rfl⟩ : syracuseStep 4836833 = 3627625) B3627625
theorem B3224555 : Blo 2149435 3224555 := bstep (se 1 (by rfl) ⟨2418416, by rfl⟩ : syracuseStep 3224555 = 4836833) B4836833
theorem B2149703 : Blo 2149435 2149703 := bstep (se 1 (by rfl) ⟨1612277, by rfl⟩ : syracuseStep 2149703 = 3224555) B3224555
theorem B2418421 : Blo 2149435 2418421 := bbase (se 5 (by rfl) ⟨113363, by rfl⟩ : syracuseStep 2418421 = 226727) (by norm_num)
theorem B3224561 : Blo 2149435 3224561 := bstep (se 2 (by rfl) ⟨1209210, by rfl⟩ : syracuseStep 3224561 = 2418421) B2418421
theorem B2149707 : Blo 2149435 2149707 := bstep (se 1 (by rfl) ⟨1612280, by rfl⟩ : syracuseStep 2149707 = 3224561) B3224561
theorem B2720729 : Blo 2149435 2720729 := bbase (se 2 (by rfl) ⟨1020273, by rfl⟩ : syracuseStep 2720729 = 2040547) (by norm_num)
theorem B7255277 : Blo 2149435 7255277 := bstep (se 3 (by rfl) ⟨1360364, by rfl⟩ : syracuseStep 7255277 = 2720729) B2720729
theorem B4836851 : Blo 2149435 4836851 := bstep (se 1 (by rfl) ⟨3627638, by rfl⟩ : syracuseStep 4836851 = 7255277) B7255277
theorem B3224567 : Blo 2149435 3224567 := bstep (se 1 (by rfl) ⟨2418425, by rfl⟩ : syracuseStep 3224567 = 4836851) B4836851
theorem B2149711 : Blo 2149435 2149711 := bstep (se 1 (by rfl) ⟨1612283, by rfl⟩ : syracuseStep 2149711 = 3224567) B3224567
theorem B3224573 : Blo 2149435 3224573 := bbase (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) (by norm_num)
theorem B2149715 : Blo 2149435 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B4836869 : Blo 2149435 4836869 := bbase (se 4 (by rfl) ⟨453456, by rfl⟩ : syracuseStep 4836869 = 906913) (by norm_num)
theorem B3224579 : Blo 2149435 3224579 := bstep (se 1 (by rfl) ⟨2418434, by rfl⟩ : syracuseStep 3224579 = 4836869) B4836869
theorem B2149719 : Blo 2149435 2149719 := bstep (se 1 (by rfl) ⟨1612289, by rfl⟩ : syracuseStep 2149719 = 3224579) B3224579
theorem B4081117 : Blo 2149435 4081117 := bbase (se 3 (by rfl) ⟨765209, by rfl⟩ : syracuseStep 4081117 = 1530419) (by norm_num)
theorem B5441489 : Blo 2149435 5441489 := bstep (se 2 (by rfl) ⟨2040558, by rfl⟩ : syracuseStep 5441489 = 4081117) B4081117
theorem B3627659 : Blo 2149435 3627659 := bstep (se 1 (by rfl) ⟨2720744, by rfl⟩ : syracuseStep 3627659 = 5441489) B5441489
theorem B2418439 : Blo 2149435 2418439 := bstep (se 1 (by rfl) ⟨1813829, by rfl⟩ : syracuseStep 2418439 = 3627659) B3627659
theorem B3224585 : Blo 2149435 3224585 := bstep (se 2 (by rfl) ⟨1209219, by rfl⟩ : syracuseStep 3224585 = 2418439) B2418439
theorem B2149723 : Blo 2149435 2149723 := bstep (se 1 (by rfl) ⟨1612292, by rfl⟩ : syracuseStep 2149723 = 3224585) B3224585
theorem B10882997 : Blo 2149435 10882997 := bbase (se 5 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 10882997 = 1020281) (by norm_num)
theorem B7255331 : Blo 2149435 7255331 := bstep (se 1 (by rfl) ⟨5441498, by rfl⟩ : syracuseStep 7255331 = 10882997) B10882997
theorem B4836887 : Blo 2149435 4836887 := bstep (se 1 (by rfl) ⟨3627665, by rfl⟩ : syracuseStep 4836887 = 7255331) B7255331
theorem B3224591 : Blo 2149435 3224591 := bstep (se 1 (by rfl) ⟨2418443, by rfl⟩ : syracuseStep 3224591 = 4836887) B4836887
theorem B2149727 : Blo 2149435 2149727 := bstep (se 1 (by rfl) ⟨1612295, by rfl⟩ : syracuseStep 2149727 = 3224591) B3224591
theorem B3224597 : Blo 2149435 3224597 := bbase (se 6 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 3224597 = 151153) (by norm_num)
theorem B2149731 : Blo 2149435 2149731 := bstep (se 1 (by rfl) ⟨1612298, by rfl⟩ : syracuseStep 2149731 = 3224597) B3224597
theorem B2905421 : Blo 2149435 2905421 := bbase (se 3 (by rfl) ⟨544766, by rfl⟩ : syracuseStep 2905421 = 1089533) (by norm_num)
theorem B30991157 : Blo 2149435 30991157 := bstep (se 5 (by rfl) ⟨1452710, by rfl⟩ : syracuseStep 30991157 = 2905421) B2905421
theorem B20660771 : Blo 2149435 20660771 := bstep (se 1 (by rfl) ⟨15495578, by rfl⟩ : syracuseStep 20660771 = 30991157) B30991157
theorem B13773847 : Blo 2149435 13773847 := bstep (se 1 (by rfl) ⟨10330385, by rfl⟩ : syracuseStep 13773847 = 20660771) B20660771
theorem B18365129 : Blo 2149435 18365129 := bstep (se 2 (by rfl) ⟨6886923, by rfl⟩ : syracuseStep 18365129 = 13773847) B13773847
theorem B12243419 : Blo 2149435 12243419 := bstep (se 1 (by rfl) ⟨9182564, by rfl⟩ : syracuseStep 12243419 = 18365129) B18365129
theorem B8162279 : Blo 2149435 8162279 := bstep (se 1 (by rfl) ⟨6121709, by rfl⟩ : syracuseStep 8162279 = 12243419) B12243419
theorem B5441519 : Blo 2149435 5441519 := bstep (se 1 (by rfl) ⟨4081139, by rfl⟩ : syracuseStep 5441519 = 8162279) B8162279
theorem B3627679 : Blo 2149435 3627679 := bstep (se 1 (by rfl) ⟨2720759, by rfl⟩ : syracuseStep 3627679 = 5441519) B5441519
theorem B4836905 : Blo 2149435 4836905 := bstep (se 2 (by rfl) ⟨1813839, by rfl⟩ : syracuseStep 4836905 = 3627679) B3627679
theorem B3224603 : Blo 2149435 3224603 := bstep (se 1 (by rfl) ⟨2418452, by rfl⟩ : syracuseStep 3224603 = 4836905) B4836905
theorem B2149735 : Blo 2149435 2149735 := bstep (se 1 (by rfl) ⟨1612301, by rfl⟩ : syracuseStep 2149735 = 3224603) B3224603
theorem B2418457 : Blo 2149435 2418457 := bbase (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) (by norm_num)
theorem B3224609 : Blo 2149435 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B2149739 : Blo 2149435 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B8162309 : Blo 2149435 8162309 := bbase (se 4 (by rfl) ⟨765216, by rfl⟩ : syracuseStep 8162309 = 1530433) (by norm_num)
theorem B5441539 : Blo 2149435 5441539 := bstep (se 1 (by rfl) ⟨4081154, by rfl⟩ : syracuseStep 5441539 = 8162309) B8162309
theorem B7255385 : Blo 2149435 7255385 := bstep (se 2 (by rfl) ⟨2720769, by rfl⟩ : syracuseStep 7255385 = 5441539) B5441539
theorem B4836923 : Blo 2149435 4836923 := bstep (se 1 (by rfl) ⟨3627692, by rfl⟩ : syracuseStep 4836923 = 7255385) B7255385
theorem B3224615 : Blo 2149435 3224615 := bstep (se 1 (by rfl) ⟨2418461, by rfl⟩ : syracuseStep 3224615 = 4836923) B4836923
theorem B2149743 : Blo 2149435 2149743 := bstep (se 1 (by rfl) ⟨1612307, by rfl⟩ : syracuseStep 2149743 = 3224615) B3224615
theorem B3224621 : Blo 2149435 3224621 := bbase (se 3 (by rfl) ⟨604616, by rfl⟩ : syracuseStep 3224621 = 1209233) (by norm_num)
theorem B2149747 : Blo 2149435 2149747 := bstep (se 1 (by rfl) ⟨1612310, by rfl⟩ : syracuseStep 2149747 = 3224621) B3224621
theorem B4836941 : Blo 2149435 4836941 := bbase (se 3 (by rfl) ⟨906926, by rfl⟩ : syracuseStep 4836941 = 1813853) (by norm_num)
theorem B3224627 : Blo 2149435 3224627 := bstep (se 1 (by rfl) ⟨2418470, by rfl⟩ : syracuseStep 3224627 = 4836941) B4836941
theorem B2149751 : Blo 2149435 2149751 := bstep (se 1 (by rfl) ⟨1612313, by rfl⟩ : syracuseStep 2149751 = 3224627) B3224627
theorem B2720785 : Blo 2149435 2720785 := bbase (se 2 (by rfl) ⟨1020294, by rfl⟩ : syracuseStep 2720785 = 2040589) (by norm_num)
theorem B3627713 : Blo 2149435 3627713 := bstep (se 2 (by rfl) ⟨1360392, by rfl⟩ : syracuseStep 3627713 = 2720785) B2720785
theorem B2418475 : Blo 2149435 2418475 := bstep (se 1 (by rfl) ⟨1813856, by rfl⟩ : syracuseStep 2418475 = 3627713) B3627713
theorem B3224633 : Blo 2149435 3224633 := bstep (se 2 (by rfl) ⟨1209237, by rfl⟩ : syracuseStep 3224633 = 2418475) B2418475
theorem B2149755 : Blo 2149435 2149755 := bstep (se 1 (by rfl) ⟨1612316, by rfl⟩ : syracuseStep 2149755 = 3224633) B3224633
theorem B4591333 : Blo 2149435 4591333 := bbase (se 4 (by rfl) ⟨430437, by rfl⟩ : syracuseStep 4591333 = 860875) (by norm_num)
theorem B24487109 : Blo 2149435 24487109 := bstep (se 4 (by rfl) ⟨2295666, by rfl⟩ : syracuseStep 24487109 = 4591333) B4591333
theorem B16324739 : Blo 2149435 16324739 := bstep (se 1 (by rfl) ⟨12243554, by rfl⟩ : syracuseStep 16324739 = 24487109) B24487109
theorem B10883159 : Blo 2149435 10883159 := bstep (se 1 (by rfl) ⟨8162369, by rfl⟩ : syracuseStep 10883159 = 16324739) B16324739
theorem B7255439 : Blo 2149435 7255439 := bstep (se 1 (by rfl) ⟨5441579, by rfl⟩ : syracuseStep 7255439 = 10883159) B10883159
theorem B4836959 : Blo 2149435 4836959 := bstep (se 1 (by rfl) ⟨3627719, by rfl⟩ : syracuseStep 4836959 = 7255439) B7255439
theorem B3224639 : Blo 2149435 3224639 := bstep (se 1 (by rfl) ⟨2418479, by rfl⟩ : syracuseStep 3224639 = 4836959) B4836959
theorem B2149759 : Blo 2149435 2149759 := bstep (se 1 (by rfl) ⟨1612319, by rfl⟩ : syracuseStep 2149759 = 3224639) B3224639
theorem B3224645 : Blo 2149435 3224645 := bbase (se 4 (by rfl) ⟨302310, by rfl⟩ : syracuseStep 3224645 = 604621) (by norm_num)
theorem B2149763 : Blo 2149435 2149763 := bstep (se 1 (by rfl) ⟨1612322, by rfl⟩ : syracuseStep 2149763 = 3224645) B3224645
theorem B3627733 : Blo 2149435 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B4836977 : Blo 2149435 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B3224651 : Blo 2149435 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B2149767 : Blo 2149435 2149767 := bstep (se 1 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 2149767 = 3224651) B3224651
theorem B2418493 : Blo 2149435 2418493 := bbase (se 3 (by rfl) ⟨453467, by rfl⟩ : syracuseStep 2418493 = 906935) (by norm_num)
theorem B3224657 : Blo 2149435 3224657 := bstep (se 2 (by rfl) ⟨1209246, by rfl⟩ : syracuseStep 3224657 = 2418493) B2418493
theorem B2149771 : Blo 2149435 2149771 := bstep (se 1 (by rfl) ⟨1612328, by rfl⟩ : syracuseStep 2149771 = 3224657) B3224657
theorem B7255493 : Blo 2149435 7255493 := bbase (se 4 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 7255493 = 1360405) (by norm_num)
theorem B4836995 : Blo 2149435 4836995 := bstep (se 1 (by rfl) ⟨3627746, by rfl⟩ : syracuseStep 4836995 = 7255493) B7255493
theorem B3224663 : Blo 2149435 3224663 := bstep (se 1 (by rfl) ⟨2418497, by rfl⟩ : syracuseStep 3224663 = 4836995) B4836995
theorem B2149775 : Blo 2149435 2149775 := bstep (se 1 (by rfl) ⟨1612331, by rfl⟩ : syracuseStep 2149775 = 3224663) B3224663
theorem B3224669 : Blo 2149435 3224669 := bbase (se 3 (by rfl) ⟨604625, by rfl⟩ : syracuseStep 3224669 = 1209251) (by norm_num)
theorem B2149779 : Blo 2149435 2149779 := bstep (se 1 (by rfl) ⟨1612334, by rfl⟩ : syracuseStep 2149779 = 3224669) B3224669
theorem B4837013 : Blo 2149435 4837013 := bbase (se 6 (by rfl) ⟨113367, by rfl⟩ : syracuseStep 4837013 = 226735) (by norm_num)
theorem B3224675 : Blo 2149435 3224675 := bstep (se 1 (by rfl) ⟨2418506, by rfl⟩ : syracuseStep 3224675 = 4837013) B4837013
theorem B2149783 : Blo 2149435 2149783 := bstep (se 1 (by rfl) ⟨1612337, by rfl⟩ : syracuseStep 2149783 = 3224675) B3224675
theorem B2295697 : Blo 2149435 2295697 := bbase (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) (by norm_num)
theorem B3060929 : Blo 2149435 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B8162477 : Blo 2149435 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B5441651 : Blo 2149435 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B3627767 : Blo 2149435 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B2418511 : Blo 2149435 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B3224681 : Blo 2149435 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B2149787 : Blo 2149435 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B17432981 : Blo 2149435 17432981 := bbase (se 6 (by rfl) ⟨408585, by rfl⟩ : syracuseStep 17432981 = 817171) (by norm_num)
theorem B11621987 : Blo 2149435 11621987 := bstep (se 1 (by rfl) ⟨8716490, by rfl⟩ : syracuseStep 11621987 = 17432981) B17432981
theorem B7747991 : Blo 2149435 7747991 := bstep (se 1 (by rfl) ⟨5810993, by rfl⟩ : syracuseStep 7747991 = 11621987) B11621987
theorem B5165327 : Blo 2149435 5165327 := bstep (se 1 (by rfl) ⟨3873995, by rfl⟩ : syracuseStep 5165327 = 7747991) B7747991
theorem B13774205 : Blo 2149435 13774205 := bstep (se 3 (by rfl) ⟨2582663, by rfl⟩ : syracuseStep 13774205 = 5165327) B5165327
theorem B9182803 : Blo 2149435 9182803 := bstep (se 1 (by rfl) ⟨6887102, by rfl⟩ : syracuseStep 9182803 = 13774205) B13774205
theorem B12243737 : Blo 2149435 12243737 := bstep (se 2 (by rfl) ⟨4591401, by rfl⟩ : syracuseStep 12243737 = 9182803) B9182803
theorem B8162491 : Blo 2149435 8162491 := bstep (se 1 (by rfl) ⟨6121868, by rfl⟩ : syracuseStep 8162491 = 12243737) B12243737
theorem B10883321 : Blo 2149435 10883321 := bstep (se 2 (by rfl) ⟨4081245, by rfl⟩ : syracuseStep 10883321 = 8162491) B8162491
theorem B7255547 : Blo 2149435 7255547 := bstep (se 1 (by rfl) ⟨5441660, by rfl⟩ : syracuseStep 7255547 = 10883321) B10883321
theorem B4837031 : Blo 2149435 4837031 := bstep (se 1 (by rfl) ⟨3627773, by rfl⟩ : syracuseStep 4837031 = 7255547) B7255547
theorem B3224687 : Blo 2149435 3224687 := bstep (se 1 (by rfl) ⟨2418515, by rfl⟩ : syracuseStep 3224687 = 4837031) B4837031
theorem B2149791 : Blo 2149435 2149791 := bstep (se 1 (by rfl) ⟨1612343, by rfl⟩ : syracuseStep 2149791 = 3224687) B3224687
theorem B3224693 : Blo 2149435 3224693 := bbase (se 5 (by rfl) ⟨151157, by rfl⟩ : syracuseStep 3224693 = 302315) (by norm_num)
theorem B2149795 : Blo 2149435 2149795 := bstep (se 1 (by rfl) ⟨1612346, by rfl⟩ : syracuseStep 2149795 = 3224693) B3224693
theorem B4081261 : Blo 2149435 4081261 := bbase (se 3 (by rfl) ⟨765236, by rfl⟩ : syracuseStep 4081261 = 1530473) (by norm_num)
theorem B5441681 : Blo 2149435 5441681 := bstep (se 2 (by rfl) ⟨2040630, by rfl⟩ : syracuseStep 5441681 = 4081261) B4081261
theorem B3627787 : Blo 2149435 3627787 := bstep (se 1 (by rfl) ⟨2720840, by rfl⟩ : syracuseStep 3627787 = 5441681) B5441681
theorem B4837049 : Blo 2149435 4837049 := bstep (se 2 (by rfl) ⟨1813893, by rfl⟩ : syracuseStep 4837049 = 3627787) B3627787
theorem B3224699 : Blo 2149435 3224699 := bstep (se 1 (by rfl) ⟨2418524, by rfl⟩ : syracuseStep 3224699 = 4837049) B4837049
theorem B2149799 : Blo 2149435 2149799 := bstep (se 1 (by rfl) ⟨1612349, by rfl⟩ : syracuseStep 2149799 = 3224699) B3224699
theorem B2418529 : Blo 2149435 2418529 := bbase (se 2 (by rfl) ⟨906948, by rfl⟩ : syracuseStep 2418529 = 1813897) (by norm_num)
theorem B3224705 : Blo 2149435 3224705 := bstep (se 2 (by rfl) ⟨1209264, by rfl⟩ : syracuseStep 3224705 = 2418529) B2418529
theorem B2149803 : Blo 2149435 2149803 := bstep (se 1 (by rfl) ⟨1612352, by rfl⟩ : syracuseStep 2149803 = 3224705) B3224705
theorem B5441701 : Blo 2149435 5441701 := bbase (se 4 (by rfl) ⟨510159, by rfl⟩ : syracuseStep 5441701 = 1020319) (by norm_num)
theorem B7255601 : Blo 2149435 7255601 := bstep (se 2 (by rfl) ⟨2720850, by rfl⟩ : syracuseStep 7255601 = 5441701) B5441701
theorem B4837067 : Blo 2149435 4837067 := bstep (se 1 (by rfl) ⟨3627800, by rfl⟩ : syracuseStep 4837067 = 7255601) B7255601
theorem B3224711 : Blo 2149435 3224711 := bstep (se 1 (by rfl) ⟨2418533, by rfl⟩ : syracuseStep 3224711 = 4837067) B4837067
theorem B2149807 : Blo 2149435 2149807 := bstep (se 1 (by rfl) ⟨1612355, by rfl⟩ : syracuseStep 2149807 = 3224711) B3224711
theorem B3224717 : Blo 2149435 3224717 := bbase (se 3 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 3224717 = 1209269) (by norm_num)
theorem B2149811 : Blo 2149435 2149811 := bstep (se 1 (by rfl) ⟨1612358, by rfl⟩ : syracuseStep 2149811 = 3224717) B3224717
theorem B4837085 : Blo 2149435 4837085 := bbase (se 3 (by rfl) ⟨906953, by rfl⟩ : syracuseStep 4837085 = 1813907) (by norm_num)
theorem B3224723 : Blo 2149435 3224723 := bstep (se 1 (by rfl) ⟨2418542, by rfl⟩ : syracuseStep 3224723 = 4837085) B4837085
theorem B2149815 : Blo 2149435 2149815 := bstep (se 1 (by rfl) ⟨1612361, by rfl⟩ : syracuseStep 2149815 = 3224723) B3224723
theorem B3627821 : Blo 2149435 3627821 := bbase (se 3 (by rfl) ⟨680216, by rfl⟩ : syracuseStep 3627821 = 1360433) (by norm_num)
theorem B2418547 : Blo 2149435 2418547 := bstep (se 1 (by rfl) ⟨1813910, by rfl⟩ : syracuseStep 2418547 = 3627821) B3627821
theorem B3224729 : Blo 2149435 3224729 := bstep (se 2 (by rfl) ⟨1209273, by rfl⟩ : syracuseStep 3224729 = 2418547) B2418547
theorem B2149819 : Blo 2149435 2149819 := bstep (se 1 (by rfl) ⟨1612364, by rfl⟩ : syracuseStep 2149819 = 3224729) B3224729
theorem B9806197 : Blo 2149435 9806197 := bbase (se 5 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 9806197 = 919331) (by norm_num)
theorem B13074929 : Blo 2149435 13074929 := bstep (se 2 (by rfl) ⟨4903098, by rfl⟩ : syracuseStep 13074929 = 9806197) B9806197
theorem B8716619 : Blo 2149435 8716619 := bstep (se 1 (by rfl) ⟨6537464, by rfl⟩ : syracuseStep 8716619 = 13074929) B13074929
theorem B23244317 : Blo 2149435 23244317 := bstep (se 3 (by rfl) ⟨4358309, by rfl⟩ : syracuseStep 23244317 = 8716619) B8716619
theorem B15496211 : Blo 2149435 15496211 := bstep (se 1 (by rfl) ⟨11622158, by rfl⟩ : syracuseStep 15496211 = 23244317) B23244317
theorem B41323229 : Blo 2149435 41323229 := bstep (se 3 (by rfl) ⟨7748105, by rfl⟩ : syracuseStep 41323229 = 15496211) B15496211
theorem B27548819 : Blo 2149435 27548819 := bstep (se 1 (by rfl) ⟨20661614, by rfl⟩ : syracuseStep 27548819 = 41323229) B41323229
theorem B18365879 : Blo 2149435 18365879 := bstep (se 1 (by rfl) ⟨13774409, by rfl⟩ : syracuseStep 18365879 = 27548819) B27548819
theorem B12243919 : Blo 2149435 12243919 := bstep (se 1 (by rfl) ⟨9182939, by rfl⟩ : syracuseStep 12243919 = 18365879) B18365879
theorem B16325225 : Blo 2149435 16325225 := bstep (se 2 (by rfl) ⟨6121959, by rfl⟩ : syracuseStep 16325225 = 12243919) B12243919
theorem B10883483 : Blo 2149435 10883483 := bstep (se 1 (by rfl) ⟨8162612, by rfl⟩ : syracuseStep 10883483 = 16325225) B16325225
theorem B7255655 : Blo 2149435 7255655 := bstep (se 1 (by rfl) ⟨5441741, by rfl⟩ : syracuseStep 7255655 = 10883483) B10883483
theorem B4837103 : Blo 2149435 4837103 := bstep (se 1 (by rfl) ⟨3627827, by rfl⟩ : syracuseStep 4837103 = 7255655) B7255655
theorem B3224735 : Blo 2149435 3224735 := bstep (se 1 (by rfl) ⟨2418551, by rfl⟩ : syracuseStep 3224735 = 4837103) B4837103
theorem B2149823 : Blo 2149435 2149823 := bstep (se 1 (by rfl) ⟨1612367, by rfl⟩ : syracuseStep 2149823 = 3224735) B3224735
theorem B3224741 : Blo 2149435 3224741 := bbase (se 4 (by rfl) ⟨302319, by rfl⟩ : syracuseStep 3224741 = 604639) (by norm_num)
theorem B2149827 : Blo 2149435 2149827 := bstep (se 1 (by rfl) ⟨1612370, by rfl⟩ : syracuseStep 2149827 = 3224741) B3224741
theorem B2720881 : Blo 2149435 2720881 := bbase (se 2 (by rfl) ⟨1020330, by rfl⟩ : syracuseStep 2720881 = 2040661) (by norm_num)
theorem B3627841 : Blo 2149435 3627841 := bstep (se 2 (by rfl) ⟨1360440, by rfl⟩ : syracuseStep 3627841 = 2720881) B2720881
theorem B4837121 : Blo 2149435 4837121 := bstep (se 2 (by rfl) ⟨1813920, by rfl⟩ : syracuseStep 4837121 = 3627841) B3627841
theorem B3224747 : Blo 2149435 3224747 := bstep (se 1 (by rfl) ⟨2418560, by rfl⟩ : syracuseStep 3224747 = 4837121) B4837121
theorem B2149831 : Blo 2149435 2149831 := bstep (se 1 (by rfl) ⟨1612373, by rfl⟩ : syracuseStep 2149831 = 3224747) B3224747
theorem B2418565 : Blo 2149435 2418565 := bbase (se 4 (by rfl) ⟨226740, by rfl⟩ : syracuseStep 2418565 = 453481) (by norm_num)
theorem B3224753 : Blo 2149435 3224753 := bstep (se 2 (by rfl) ⟨1209282, by rfl⟩ : syracuseStep 3224753 = 2418565) B2418565
theorem B2149835 : Blo 2149435 2149835 := bstep (se 1 (by rfl) ⟨1612376, by rfl⟩ : syracuseStep 2149835 = 3224753) B3224753
theorem B3443629 : Blo 2149435 3443629 := bbase (se 3 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 3443629 = 1291361) (by norm_num)
theorem B4591505 : Blo 2149435 4591505 := bstep (se 2 (by rfl) ⟨1721814, by rfl⟩ : syracuseStep 4591505 = 3443629) B3443629
theorem B3061003 : Blo 2149435 3061003 := bstep (se 1 (by rfl) ⟨2295752, by rfl⟩ : syracuseStep 3061003 = 4591505) B4591505
theorem B4081337 : Blo 2149435 4081337 := bstep (se 2 (by rfl) ⟨1530501, by rfl⟩ : syracuseStep 4081337 = 3061003) B3061003
theorem B2720891 : Blo 2149435 2720891 := bstep (se 1 (by rfl) ⟨2040668, by rfl⟩ : syracuseStep 2720891 = 4081337) B4081337
theorem B7255709 : Blo 2149435 7255709 := bstep (se 3 (by rfl) ⟨1360445, by rfl⟩ : syracuseStep 7255709 = 2720891) B2720891
theorem B4837139 : Blo 2149435 4837139 := bstep (se 1 (by rfl) ⟨3627854, by rfl⟩ : syracuseStep 4837139 = 7255709) B7255709
theorem B3224759 : Blo 2149435 3224759 := bstep (se 1 (by rfl) ⟨2418569, by rfl⟩ : syracuseStep 3224759 = 4837139) B4837139
theorem B2149839 : Blo 2149435 2149839 := bstep (se 1 (by rfl) ⟨1612379, by rfl⟩ : syracuseStep 2149839 = 3224759) B3224759
theorem B3224765 : Blo 2149435 3224765 := bbase (se 3 (by rfl) ⟨604643, by rfl⟩ : syracuseStep 3224765 = 1209287) (by norm_num)
theorem B2149843 : Blo 2149435 2149843 := bstep (se 1 (by rfl) ⟨1612382, by rfl⟩ : syracuseStep 2149843 = 3224765) B3224765
theorem B4837157 : Blo 2149435 4837157 := bbase (se 4 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 4837157 = 906967) (by norm_num)
theorem B3224771 : Blo 2149435 3224771 := bstep (se 1 (by rfl) ⟨2418578, by rfl⟩ : syracuseStep 3224771 = 4837157) B4837157
theorem B2149847 : Blo 2149435 2149847 := bstep (se 1 (by rfl) ⟨1612385, by rfl⟩ : syracuseStep 2149847 = 3224771) B3224771
theorem B5441813 : Blo 2149435 5441813 := bbase (se 6 (by rfl) ⟨127542, by rfl⟩ : syracuseStep 5441813 = 255085) (by norm_num)
theorem B3627875 : Blo 2149435 3627875 := bstep (se 1 (by rfl) ⟨2720906, by rfl⟩ : syracuseStep 3627875 = 5441813) B5441813
theorem B2418583 : Blo 2149435 2418583 := bstep (se 1 (by rfl) ⟨1813937, by rfl⟩ : syracuseStep 2418583 = 3627875) B3627875
theorem B3224777 : Blo 2149435 3224777 := bstep (se 2 (by rfl) ⟨1209291, by rfl⟩ : syracuseStep 3224777 = 2418583) B2418583
theorem B2149851 : Blo 2149435 2149851 := bstep (se 1 (by rfl) ⟨1612388, by rfl⟩ : syracuseStep 2149851 = 3224777) B3224777
theorem B9183077 : Blo 2149435 9183077 := bbase (se 4 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 9183077 = 1721827) (by norm_num)
theorem B6122051 : Blo 2149435 6122051 := bstep (se 1 (by rfl) ⟨4591538, by rfl⟩ : syracuseStep 6122051 = 9183077) B9183077
theorem B4081367 : Blo 2149435 4081367 := bstep (se 1 (by rfl) ⟨3061025, by rfl⟩ : syracuseStep 4081367 = 6122051) B6122051
theorem B10883645 : Blo 2149435 10883645 := bstep (se 3 (by rfl) ⟨2040683, by rfl⟩ : syracuseStep 10883645 = 4081367) B4081367
theorem B7255763 : Blo 2149435 7255763 := bstep (se 1 (by rfl) ⟨5441822, by rfl⟩ : syracuseStep 7255763 = 10883645) B10883645
theorem B4837175 : Blo 2149435 4837175 := bstep (se 1 (by rfl) ⟨3627881, by rfl⟩ : syracuseStep 4837175 = 7255763) B7255763
theorem B3224783 : Blo 2149435 3224783 := bstep (se 1 (by rfl) ⟨2418587, by rfl⟩ : syracuseStep 3224783 = 4837175) B4837175
theorem B2149855 : Blo 2149435 2149855 := bstep (se 1 (by rfl) ⟨1612391, by rfl⟩ : syracuseStep 2149855 = 3224783) B3224783
theorem B3224789 : Blo 2149435 3224789 := bbase (se 7 (by rfl) ⟨37790, by rfl⟩ : syracuseStep 3224789 = 75581) (by norm_num)
theorem B2149859 : Blo 2149435 2149859 := bstep (se 1 (by rfl) ⟨1612394, by rfl⟩ : syracuseStep 2149859 = 3224789) B3224789
theorem B3061037 : Blo 2149435 3061037 := bbase (se 3 (by rfl) ⟨573944, by rfl⟩ : syracuseStep 3061037 = 1147889) (by norm_num)
theorem B8162765 : Blo 2149435 8162765 := bstep (se 3 (by rfl) ⟨1530518, by rfl⟩ : syracuseStep 8162765 = 3061037) B3061037
theorem B5441843 : Blo 2149435 5441843 := bstep (se 1 (by rfl) ⟨4081382, by rfl⟩ : syracuseStep 5441843 = 8162765) B8162765
theorem B3627895 : Blo 2149435 3627895 := bstep (se 1 (by rfl) ⟨2720921, by rfl⟩ : syracuseStep 3627895 = 5441843) B5441843
theorem B4837193 : Blo 2149435 4837193 := bstep (se 2 (by rfl) ⟨1813947, by rfl⟩ : syracuseStep 4837193 = 3627895) B3627895
theorem B3224795 : Blo 2149435 3224795 := bstep (se 1 (by rfl) ⟨2418596, by rfl⟩ : syracuseStep 3224795 = 4837193) B4837193
theorem B2149863 : Blo 2149435 2149863 := bstep (se 1 (by rfl) ⟨1612397, by rfl⟩ : syracuseStep 2149863 = 3224795) B3224795
theorem B2418601 : Blo 2149435 2418601 := bbase (se 2 (by rfl) ⟨906975, by rfl⟩ : syracuseStep 2418601 = 1813951) (by norm_num)
theorem B3224801 : Blo 2149435 3224801 := bstep (se 2 (by rfl) ⟨1209300, by rfl⟩ : syracuseStep 3224801 = 2418601) B2418601
theorem B2149867 : Blo 2149435 2149867 := bstep (se 1 (by rfl) ⟨1612400, by rfl⟩ : syracuseStep 2149867 = 3224801) B3224801
theorem B2653717 : Blo 2149435 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B3538289 : Blo 2149435 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B9435437 : Blo 2149435 9435437 := bstep (se 3 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 9435437 = 3538289) B3538289
theorem B6290291 : Blo 2149435 6290291 := bstep (se 1 (by rfl) ⟨4717718, by rfl⟩ : syracuseStep 6290291 = 9435437) B9435437
theorem B4193527 : Blo 2149435 4193527 := bstep (se 1 (by rfl) ⟨3145145, by rfl⟩ : syracuseStep 4193527 = 6290291) B6290291
theorem B5591369 : Blo 2149435 5591369 := bstep (se 2 (by rfl) ⟨2096763, by rfl⟩ : syracuseStep 5591369 = 4193527) B4193527
theorem B14910317 : Blo 2149435 14910317 := bstep (se 3 (by rfl) ⟨2795684, by rfl⟩ : syracuseStep 14910317 = 5591369) B5591369
theorem B9940211 : Blo 2149435 9940211 := bstep (se 1 (by rfl) ⟨7455158, by rfl⟩ : syracuseStep 9940211 = 14910317) B14910317
theorem B6626807 : Blo 2149435 6626807 := bstep (se 1 (by rfl) ⟨4970105, by rfl⟩ : syracuseStep 6626807 = 9940211) B9940211
theorem B4417871 : Blo 2149435 4417871 := bstep (se 1 (by rfl) ⟨3313403, by rfl⟩ : syracuseStep 4417871 = 6626807) B6626807
theorem B47123957 : Blo 2149435 47123957 := bstep (se 5 (by rfl) ⟨2208935, by rfl⟩ : syracuseStep 47123957 = 4417871) B4417871
theorem B31415971 : Blo 2149435 31415971 := bstep (se 1 (by rfl) ⟨23561978, by rfl⟩ : syracuseStep 31415971 = 47123957) B47123957
theorem B41887961 : Blo 2149435 41887961 := bstep (se 2 (by rfl) ⟨15707985, by rfl⟩ : syracuseStep 41887961 = 31415971) B31415971
theorem B27925307 : Blo 2149435 27925307 := bstep (se 1 (by rfl) ⟨20943980, by rfl⟩ : syracuseStep 27925307 = 41887961) B41887961
theorem B18616871 : Blo 2149435 18616871 := bstep (se 1 (by rfl) ⟨13962653, by rfl⟩ : syracuseStep 18616871 = 27925307) B27925307
theorem B12411247 : Blo 2149435 12411247 := bstep (se 1 (by rfl) ⟨9308435, by rfl⟩ : syracuseStep 12411247 = 18616871) B18616871
theorem B16548329 : Blo 2149435 16548329 := bstep (se 2 (by rfl) ⟨6205623, by rfl⟩ : syracuseStep 16548329 = 12411247) B12411247
theorem B11032219 : Blo 2149435 11032219 := bstep (se 1 (by rfl) ⟨8274164, by rfl⟩ : syracuseStep 11032219 = 16548329) B16548329
theorem B58838501 : Blo 2149435 58838501 := bstep (se 4 (by rfl) ⟨5516109, by rfl⟩ : syracuseStep 58838501 = 11032219) B11032219
theorem B39225667 : Blo 2149435 39225667 := bstep (se 1 (by rfl) ⟨29419250, by rfl⟩ : syracuseStep 39225667 = 58838501) B58838501
theorem B52300889 : Blo 2149435 52300889 := bstep (se 2 (by rfl) ⟨19612833, by rfl⟩ : syracuseStep 52300889 = 39225667) B39225667
theorem B34867259 : Blo 2149435 34867259 := bstep (se 1 (by rfl) ⟨26150444, by rfl⟩ : syracuseStep 34867259 = 52300889) B52300889
theorem B23244839 : Blo 2149435 23244839 := bstep (se 1 (by rfl) ⟨17433629, by rfl⟩ : syracuseStep 23244839 = 34867259) B34867259
theorem B15496559 : Blo 2149435 15496559 := bstep (se 1 (by rfl) ⟨11622419, by rfl⟩ : syracuseStep 15496559 = 23244839) B23244839
theorem B10331039 : Blo 2149435 10331039 := bstep (se 1 (by rfl) ⟨7748279, by rfl⟩ : syracuseStep 10331039 = 15496559) B15496559
theorem B6887359 : Blo 2149435 6887359 := bstep (se 1 (by rfl) ⟨5165519, by rfl⟩ : syracuseStep 6887359 = 10331039) B10331039
theorem B9183145 : Blo 2149435 9183145 := bstep (se 2 (by rfl) ⟨3443679, by rfl⟩ : syracuseStep 9183145 = 6887359) B6887359
theorem B12244193 : Blo 2149435 12244193 := bstep (se 2 (by rfl) ⟨4591572, by rfl⟩ : syracuseStep 12244193 = 9183145) B9183145
theorem B8162795 : Blo 2149435 8162795 := bstep (se 1 (by rfl) ⟨6122096, by rfl⟩ : syracuseStep 8162795 = 12244193) B12244193
theorem B5441863 : Blo 2149435 5441863 := bstep (se 1 (by rfl) ⟨4081397, by rfl⟩ : syracuseStep 5441863 = 8162795) B8162795
theorem B7255817 : Blo 2149435 7255817 := bstep (se 2 (by rfl) ⟨2720931, by rfl⟩ : syracuseStep 7255817 = 5441863) B5441863
theorem B4837211 : Blo 2149435 4837211 := bstep (se 1 (by rfl) ⟨3627908, by rfl⟩ : syracuseStep 4837211 = 7255817) B7255817
theorem B3224807 : Blo 2149435 3224807 := bstep (se 1 (by rfl) ⟨2418605, by rfl⟩ : syracuseStep 3224807 = 4837211) B4837211
theorem B2149871 : Blo 2149435 2149871 := bstep (se 1 (by rfl) ⟨1612403, by rfl⟩ : syracuseStep 2149871 = 3224807) B3224807
theorem B3224813 : Blo 2149435 3224813 := bbase (se 3 (by rfl) ⟨604652, by rfl⟩ : syracuseStep 3224813 = 1209305) (by norm_num)
theorem B2149875 : Blo 2149435 2149875 := bstep (se 1 (by rfl) ⟨1612406, by rfl⟩ : syracuseStep 2149875 = 3224813) B3224813
theorem B4837229 : Blo 2149435 4837229 := bbase (se 3 (by rfl) ⟨906980, by rfl⟩ : syracuseStep 4837229 = 1813961) (by norm_num)
theorem B3224819 : Blo 2149435 3224819 := bstep (se 1 (by rfl) ⟨2418614, by rfl⟩ : syracuseStep 3224819 = 4837229) B4837229
theorem B2149879 : Blo 2149435 2149879 := bstep (se 1 (by rfl) ⟨1612409, by rfl⟩ : syracuseStep 2149879 = 3224819) B3224819
theorem B4081421 : Blo 2149435 4081421 := bbase (se 3 (by rfl) ⟨765266, by rfl⟩ : syracuseStep 4081421 = 1530533) (by norm_num)
theorem B2720947 : Blo 2149435 2720947 := bstep (se 1 (by rfl) ⟨2040710, by rfl⟩ : syracuseStep 2720947 = 4081421) B4081421
theorem B3627929 : Blo 2149435 3627929 := bstep (se 2 (by rfl) ⟨1360473, by rfl⟩ : syracuseStep 3627929 = 2720947) B2720947
theorem B2418619 : Blo 2149435 2418619 := bstep (se 1 (by rfl) ⟨1813964, by rfl⟩ : syracuseStep 2418619 = 3627929) B3627929
theorem B3224825 : Blo 2149435 3224825 := bstep (se 2 (by rfl) ⟨1209309, by rfl⟩ : syracuseStep 3224825 = 2418619) B2418619
theorem B2149883 : Blo 2149435 2149883 := bstep (se 1 (by rfl) ⟨1612412, by rfl⟩ : syracuseStep 2149883 = 3224825) B3224825
theorem B20662229 : Blo 2149435 20662229 := bbase (se 7 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 20662229 = 484271) (by norm_num)
theorem B55099277 : Blo 2149435 55099277 := bstep (se 3 (by rfl) ⟨10331114, by rfl⟩ : syracuseStep 55099277 = 20662229) B20662229
theorem B36732851 : Blo 2149435 36732851 := bstep (se 1 (by rfl) ⟨27549638, by rfl⟩ : syracuseStep 36732851 = 55099277) B55099277
theorem B24488567 : Blo 2149435 24488567 := bstep (se 1 (by rfl) ⟨18366425, by rfl⟩ : syracuseStep 24488567 = 36732851) B36732851
theorem B16325711 : Blo 2149435 16325711 := bstep (se 1 (by rfl) ⟨12244283, by rfl⟩ : syracuseStep 16325711 = 24488567) B24488567
theorem B10883807 : Blo 2149435 10883807 := bstep (se 1 (by rfl) ⟨8162855, by rfl⟩ : syracuseStep 10883807 = 16325711) B16325711
theorem B7255871 : Blo 2149435 7255871 := bstep (se 1 (by rfl) ⟨5441903, by rfl⟩ : syracuseStep 7255871 = 10883807) B10883807
theorem B4837247 : Blo 2149435 4837247 := bstep (se 1 (by rfl) ⟨3627935, by rfl⟩ : syracuseStep 4837247 = 7255871) B7255871
theorem B3224831 : Blo 2149435 3224831 := bstep (se 1 (by rfl) ⟨2418623, by rfl⟩ : syracuseStep 3224831 = 4837247) B4837247
theorem B2149887 : Blo 2149435 2149887 := bstep (se 1 (by rfl) ⟨1612415, by rfl⟩ : syracuseStep 2149887 = 3224831) B3224831
theorem B3224837 : Blo 2149435 3224837 := bbase (se 4 (by rfl) ⟨302328, by rfl⟩ : syracuseStep 3224837 = 604657) (by norm_num)
theorem B2149891 : Blo 2149435 2149891 := bstep (se 1 (by rfl) ⟨1612418, by rfl⟩ : syracuseStep 2149891 = 3224837) B3224837
theorem B3627949 : Blo 2149435 3627949 := bbase (se 3 (by rfl) ⟨680240, by rfl⟩ : syracuseStep 3627949 = 1360481) (by norm_num)
theorem B4837265 : Blo 2149435 4837265 := bstep (se 2 (by rfl) ⟨1813974, by rfl⟩ : syracuseStep 4837265 = 3627949) B3627949
theorem B3224843 : Blo 2149435 3224843 := bstep (se 1 (by rfl) ⟨2418632, by rfl⟩ : syracuseStep 3224843 = 4837265) B4837265
theorem B2149895 : Blo 2149435 2149895 := bstep (se 1 (by rfl) ⟨1612421, by rfl⟩ : syracuseStep 2149895 = 3224843) B3224843
theorem B2418637 : Blo 2149435 2418637 := bbase (se 3 (by rfl) ⟨453494, by rfl⟩ : syracuseStep 2418637 = 906989) (by norm_num)
theorem B3224849 : Blo 2149435 3224849 := bstep (se 2 (by rfl) ⟨1209318, by rfl⟩ : syracuseStep 3224849 = 2418637) B2418637
theorem B2149899 : Blo 2149435 2149899 := bstep (se 1 (by rfl) ⟨1612424, by rfl⟩ : syracuseStep 2149899 = 3224849) B3224849
theorem B7255925 : Blo 2149435 7255925 := bbase (se 5 (by rfl) ⟨340121, by rfl⟩ : syracuseStep 7255925 = 680243) (by norm_num)
theorem B4837283 : Blo 2149435 4837283 := bstep (se 1 (by rfl) ⟨3627962, by rfl⟩ : syracuseStep 4837283 = 7255925) B7255925
theorem B3224855 : Blo 2149435 3224855 := bstep (se 1 (by rfl) ⟨2418641, by rfl⟩ : syracuseStep 3224855 = 4837283) B4837283
theorem B2149903 : Blo 2149435 2149903 := bstep (se 1 (by rfl) ⟨1612427, by rfl⟩ : syracuseStep 2149903 = 3224855) B3224855
theorem B3224861 : Blo 2149435 3224861 := bbase (se 3 (by rfl) ⟨604661, by rfl⟩ : syracuseStep 3224861 = 1209323) (by norm_num)
theorem B2149907 : Blo 2149435 2149907 := bstep (se 1 (by rfl) ⟨1612430, by rfl⟩ : syracuseStep 2149907 = 3224861) B3224861
theorem B4837301 : Blo 2149435 4837301 := bbase (se 5 (by rfl) ⟨226748, by rfl⟩ : syracuseStep 4837301 = 453497) (by norm_num)
theorem B3224867 : Blo 2149435 3224867 := bstep (se 1 (by rfl) ⟨2418650, by rfl⟩ : syracuseStep 3224867 = 4837301) B4837301
theorem B2149911 : Blo 2149435 2149911 := bstep (se 1 (by rfl) ⟨1612433, by rfl⟩ : syracuseStep 2149911 = 3224867) B3224867
theorem B2582813 : Blo 2149435 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B6887501 : Blo 2149435 6887501 := bstep (se 3 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 6887501 = 2582813) B2582813
theorem B4591667 : Blo 2149435 4591667 := bstep (se 1 (by rfl) ⟨3443750, by rfl⟩ : syracuseStep 4591667 = 6887501) B6887501
theorem B12244445 : Blo 2149435 12244445 := bstep (se 3 (by rfl) ⟨2295833, by rfl⟩ : syracuseStep 12244445 = 4591667) B4591667
theorem B8162963 : Blo 2149435 8162963 := bstep (se 1 (by rfl) ⟨6122222, by rfl⟩ : syracuseStep 8162963 = 12244445) B12244445
theorem B5441975 : Blo 2149435 5441975 := bstep (se 1 (by rfl) ⟨4081481, by rfl⟩ : syracuseStep 5441975 = 8162963) B8162963
theorem B3627983 : Blo 2149435 3627983 := bstep (se 1 (by rfl) ⟨2720987, by rfl⟩ : syracuseStep 3627983 = 5441975) B5441975
theorem B2418655 : Blo 2149435 2418655 := bstep (se 1 (by rfl) ⟨1813991, by rfl⟩ : syracuseStep 2418655 = 3627983) B3627983
theorem B3224873 : Blo 2149435 3224873 := bstep (se 2 (by rfl) ⟨1209327, by rfl⟩ : syracuseStep 3224873 = 2418655) B2418655
theorem B2149915 : Blo 2149435 2149915 := bstep (se 1 (by rfl) ⟨1612436, by rfl⟩ : syracuseStep 2149915 = 3224873) B3224873
theorem B7748453 : Blo 2149435 7748453 := bbase (se 4 (by rfl) ⟨726417, by rfl⟩ : syracuseStep 7748453 = 1452835) (by norm_num)
theorem B5165635 : Blo 2149435 5165635 := bstep (se 1 (by rfl) ⟨3874226, by rfl⟩ : syracuseStep 5165635 = 7748453) B7748453
theorem B6887513 : Blo 2149435 6887513 := bstep (se 2 (by rfl) ⟨2582817, by rfl⟩ : syracuseStep 6887513 = 5165635) B5165635
theorem B4591675 : Blo 2149435 4591675 := bstep (se 1 (by rfl) ⟨3443756, by rfl⟩ : syracuseStep 4591675 = 6887513) B6887513
theorem B6122233 : Blo 2149435 6122233 := bstep (se 2 (by rfl) ⟨2295837, by rfl⟩ : syracuseStep 6122233 = 4591675) B4591675
theorem B8162977 : Blo 2149435 8162977 := bstep (se 2 (by rfl) ⟨3061116, by rfl⟩ : syracuseStep 8162977 = 6122233) B6122233
theorem B10883969 : Blo 2149435 10883969 := bstep (se 2 (by rfl) ⟨4081488, by rfl⟩ : syracuseStep 10883969 = 8162977) B8162977
theorem B7255979 : Blo 2149435 7255979 := bstep (se 1 (by rfl) ⟨5441984, by rfl⟩ : syracuseStep 7255979 = 10883969) B10883969
theorem B4837319 : Blo 2149435 4837319 := bstep (se 1 (by rfl) ⟨3627989, by rfl⟩ : syracuseStep 4837319 = 7255979) B7255979
theorem B3224879 : Blo 2149435 3224879 := bstep (se 1 (by rfl) ⟨2418659, by rfl⟩ : syracuseStep 3224879 = 4837319) B4837319
theorem B2149919 : Blo 2149435 2149919 := bstep (se 1 (by rfl) ⟨1612439, by rfl⟩ : syracuseStep 2149919 = 3224879) B3224879
theorem B3224885 : Blo 2149435 3224885 := bbase (se 5 (by rfl) ⟨151166, by rfl⟩ : syracuseStep 3224885 = 302333) (by norm_num)
theorem B2149923 : Blo 2149435 2149923 := bstep (se 1 (by rfl) ⟨1612442, by rfl⟩ : syracuseStep 2149923 = 3224885) B3224885
theorem B5442005 : Blo 2149435 5442005 := bbase (se 7 (by rfl) ⟨63773, by rfl⟩ : syracuseStep 5442005 = 127547) (by norm_num)
theorem B3628003 : Blo 2149435 3628003 := bstep (se 1 (by rfl) ⟨2721002, by rfl⟩ : syracuseStep 3628003 = 5442005) B5442005
theorem B4837337 : Blo 2149435 4837337 := bstep (se 2 (by rfl) ⟨1814001, by rfl⟩ : syracuseStep 4837337 = 3628003) B3628003
theorem B3224891 : Blo 2149435 3224891 := bstep (se 1 (by rfl) ⟨2418668, by rfl⟩ : syracuseStep 3224891 = 4837337) B4837337
theorem B2149927 : Blo 2149435 2149927 := bstep (se 1 (by rfl) ⟨1612445, by rfl⟩ : syracuseStep 2149927 = 3224891) B3224891
theorem B2418673 : Blo 2149435 2418673 := bbase (se 2 (by rfl) ⟨907002, by rfl⟩ : syracuseStep 2418673 = 1814005) (by norm_num)
theorem B3224897 : Blo 2149435 3224897 := bstep (se 2 (by rfl) ⟨1209336, by rfl⟩ : syracuseStep 3224897 = 2418673) B2418673
theorem B2149931 : Blo 2149435 2149931 := bstep (se 1 (by rfl) ⟨1612448, by rfl⟩ : syracuseStep 2149931 = 3224897) B3224897
theorem B2618077 : Blo 2149435 2618077 := bbase (se 3 (by rfl) ⟨490889, by rfl⟩ : syracuseStep 2618077 = 981779) (by norm_num)
theorem B3490769 : Blo 2149435 3490769 := bstep (se 2 (by rfl) ⟨1309038, by rfl⟩ : syracuseStep 3490769 = 2618077) B2618077
theorem B2327179 : Blo 2149435 2327179 := bstep (se 1 (by rfl) ⟨1745384, by rfl⟩ : syracuseStep 2327179 = 3490769) B3490769
theorem B3102905 : Blo 2149435 3102905 := bstep (se 2 (by rfl) ⟨1163589, by rfl⟩ : syracuseStep 3102905 = 2327179) B2327179
theorem B8274413 : Blo 2149435 8274413 := bstep (se 3 (by rfl) ⟨1551452, by rfl⟩ : syracuseStep 8274413 = 3102905) B3102905
theorem B5516275 : Blo 2149435 5516275 := bstep (se 1 (by rfl) ⟨4137206, by rfl⟩ : syracuseStep 5516275 = 8274413) B8274413
theorem B7355033 : Blo 2149435 7355033 := bstep (se 2 (by rfl) ⟨2758137, by rfl⟩ : syracuseStep 7355033 = 5516275) B5516275
theorem B4903355 : Blo 2149435 4903355 := bstep (se 1 (by rfl) ⟨3677516, by rfl⟩ : syracuseStep 4903355 = 7355033) B7355033
theorem B13075613 : Blo 2149435 13075613 := bstep (se 3 (by rfl) ⟨2451677, by rfl⟩ : syracuseStep 13075613 = 4903355) B4903355
theorem B8717075 : Blo 2149435 8717075 := bstep (se 1 (by rfl) ⟨6537806, by rfl⟩ : syracuseStep 8717075 = 13075613) B13075613
theorem B5811383 : Blo 2149435 5811383 := bstep (se 1 (by rfl) ⟨4358537, by rfl⟩ : syracuseStep 5811383 = 8717075) B8717075
theorem B15497021 : Blo 2149435 15497021 := bstep (se 3 (by rfl) ⟨2905691, by rfl⟩ : syracuseStep 15497021 = 5811383) B5811383
theorem B10331347 : Blo 2149435 10331347 := bstep (se 1 (by rfl) ⟨7748510, by rfl⟩ : syracuseStep 10331347 = 15497021) B15497021
theorem B13775129 : Blo 2149435 13775129 := bstep (se 2 (by rfl) ⟨5165673, by rfl⟩ : syracuseStep 13775129 = 10331347) B10331347
theorem B9183419 : Blo 2149435 9183419 := bstep (se 1 (by rfl) ⟨6887564, by rfl⟩ : syracuseStep 9183419 = 13775129) B13775129
theorem B6122279 : Blo 2149435 6122279 := bstep (se 1 (by rfl) ⟨4591709, by rfl⟩ : syracuseStep 6122279 = 9183419) B9183419
theorem B4081519 : Blo 2149435 4081519 := bstep (se 1 (by rfl) ⟨3061139, by rfl⟩ : syracuseStep 4081519 = 6122279) B6122279
theorem B5442025 : Blo 2149435 5442025 := bstep (se 2 (by rfl) ⟨2040759, by rfl⟩ : syracuseStep 5442025 = 4081519) B4081519
theorem B7256033 : Blo 2149435 7256033 := bstep (se 2 (by rfl) ⟨2721012, by rfl⟩ : syracuseStep 7256033 = 5442025) B5442025
theorem B4837355 : Blo 2149435 4837355 := bstep (se 1 (by rfl) ⟨3628016, by rfl⟩ : syracuseStep 4837355 = 7256033) B7256033
theorem B3224903 : Blo 2149435 3224903 := bstep (se 1 (by rfl) ⟨2418677, by rfl⟩ : syracuseStep 3224903 = 4837355) B4837355
theorem B2149935 : Blo 2149435 2149935 := bstep (se 1 (by rfl) ⟨1612451, by rfl⟩ : syracuseStep 2149935 = 3224903) B3224903
theorem B3224909 : Blo 2149435 3224909 := bbase (se 3 (by rfl) ⟨604670, by rfl⟩ : syracuseStep 3224909 = 1209341) (by norm_num)
theorem B2149939 : Blo 2149435 2149939 := bstep (se 1 (by rfl) ⟨1612454, by rfl⟩ : syracuseStep 2149939 = 3224909) B3224909
theorem B4837373 : Blo 2149435 4837373 := bbase (se 3 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 4837373 = 1814015) (by norm_num)
theorem B3224915 : Blo 2149435 3224915 := bstep (se 1 (by rfl) ⟨2418686, by rfl⟩ : syracuseStep 3224915 = 4837373) B4837373
theorem B2149943 : Blo 2149435 2149943 := bstep (se 1 (by rfl) ⟨1612457, by rfl⟩ : syracuseStep 2149943 = 3224915) B3224915
theorem B3628037 : Blo 2149435 3628037 := bbase (se 4 (by rfl) ⟨340128, by rfl⟩ : syracuseStep 3628037 = 680257) (by norm_num)
theorem B2418691 : Blo 2149435 2418691 := bstep (se 1 (by rfl) ⟨1814018, by rfl⟩ : syracuseStep 2418691 = 3628037) B3628037
theorem B3224921 : Blo 2149435 3224921 := bstep (se 2 (by rfl) ⟨1209345, by rfl⟩ : syracuseStep 3224921 = 2418691) B2418691
theorem B2149947 : Blo 2149435 2149947 := bstep (se 1 (by rfl) ⟨1612460, by rfl⟩ : syracuseStep 2149947 = 3224921) B3224921
theorem B16326197 : Blo 2149435 16326197 := bbase (se 5 (by rfl) ⟨765290, by rfl⟩ : syracuseStep 16326197 = 1530581) (by norm_num)
theorem B10884131 : Blo 2149435 10884131 := bstep (se 1 (by rfl) ⟨8163098, by rfl⟩ : syracuseStep 10884131 = 16326197) B16326197
theorem B7256087 : Blo 2149435 7256087 := bstep (se 1 (by rfl) ⟨5442065, by rfl⟩ : syracuseStep 7256087 = 10884131) B10884131
theorem B4837391 : Blo 2149435 4837391 := bstep (se 1 (by rfl) ⟨3628043, by rfl⟩ : syracuseStep 4837391 = 7256087) B7256087
theorem B3224927 : Blo 2149435 3224927 := bstep (se 1 (by rfl) ⟨2418695, by rfl⟩ : syracuseStep 3224927 = 4837391) B4837391
theorem B2149951 : Blo 2149435 2149951 := bstep (se 1 (by rfl) ⟨1612463, by rfl⟩ : syracuseStep 2149951 = 3224927) B3224927
theorem B3224933 : Blo 2149435 3224933 := bbase (se 4 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 3224933 = 604675) (by norm_num)
theorem B2149955 : Blo 2149435 2149955 := bstep (se 1 (by rfl) ⟨1612466, by rfl⟩ : syracuseStep 2149955 = 3224933) B3224933
theorem B4081565 : Blo 2149435 4081565 := bbase (se 3 (by rfl) ⟨765293, by rfl⟩ : syracuseStep 4081565 = 1530587) (by norm_num)
theorem B2721043 : Blo 2149435 2721043 := bstep (se 1 (by rfl) ⟨2040782, by rfl⟩ : syracuseStep 2721043 = 4081565) B4081565
theorem B3628057 : Blo 2149435 3628057 := bstep (se 2 (by rfl) ⟨1360521, by rfl⟩ : syracuseStep 3628057 = 2721043) B2721043
theorem B4837409 : Blo 2149435 4837409 := bstep (se 2 (by rfl) ⟨1814028, by rfl⟩ : syracuseStep 4837409 = 3628057) B3628057
theorem B3224939 : Blo 2149435 3224939 := bstep (se 1 (by rfl) ⟨2418704, by rfl⟩ : syracuseStep 3224939 = 4837409) B4837409
theorem B2149959 : Blo 2149435 2149959 := bstep (se 1 (by rfl) ⟨1612469, by rfl⟩ : syracuseStep 2149959 = 3224939) B3224939
theorem B2418709 : Blo 2149435 2418709 := bbase (se 6 (by rfl) ⟨56688, by rfl⟩ : syracuseStep 2418709 = 113377) (by norm_num)
theorem B3224945 : Blo 2149435 3224945 := bstep (se 2 (by rfl) ⟨1209354, by rfl⟩ : syracuseStep 3224945 = 2418709) B2418709
theorem B2149963 : Blo 2149435 2149963 := bstep (se 1 (by rfl) ⟨1612472, by rfl⟩ : syracuseStep 2149963 = 3224945) B3224945
theorem B2721053 : Blo 2149435 2721053 := bbase (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) (by norm_num)
theorem B7256141 : Blo 2149435 7256141 := bstep (se 3 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 7256141 = 2721053) B2721053
theorem B4837427 : Blo 2149435 4837427 := bstep (se 1 (by rfl) ⟨3628070, by rfl⟩ : syracuseStep 4837427 = 7256141) B7256141
theorem B3224951 : Blo 2149435 3224951 := bstep (se 1 (by rfl) ⟨2418713, by rfl⟩ : syracuseStep 3224951 = 4837427) B4837427
theorem B2149967 : Blo 2149435 2149967 := bstep (se 1 (by rfl) ⟨1612475, by rfl⟩ : syracuseStep 2149967 = 3224951) B3224951
theorem B3224957 : Blo 2149435 3224957 := bbase (se 3 (by rfl) ⟨604679, by rfl⟩ : syracuseStep 3224957 = 1209359) (by norm_num)
theorem B2149971 : Blo 2149435 2149971 := bstep (se 1 (by rfl) ⟨1612478, by rfl⟩ : syracuseStep 2149971 = 3224957) B3224957
theorem B4837445 : Blo 2149435 4837445 := bbase (se 4 (by rfl) ⟨453510, by rfl⟩ : syracuseStep 4837445 = 907021) (by norm_num)
theorem B3224963 : Blo 2149435 3224963 := bstep (se 1 (by rfl) ⟨2418722, by rfl⟩ : syracuseStep 3224963 = 4837445) B4837445
theorem B2149975 : Blo 2149435 2149975 := bstep (se 1 (by rfl) ⟨1612481, by rfl⟩ : syracuseStep 2149975 = 3224963) B3224963
theorem B6122405 : Blo 2149435 6122405 := bbase (se 4 (by rfl) ⟨573975, by rfl⟩ : syracuseStep 6122405 = 1147951) (by norm_num)
theorem B4081603 : Blo 2149435 4081603 := bstep (se 1 (by rfl) ⟨3061202, by rfl⟩ : syracuseStep 4081603 = 6122405) B6122405
theorem B5442137 : Blo 2149435 5442137 := bstep (se 2 (by rfl) ⟨2040801, by rfl⟩ : syracuseStep 5442137 = 4081603) B4081603
theorem B3628091 : Blo 2149435 3628091 := bstep (se 1 (by rfl) ⟨2721068, by rfl⟩ : syracuseStep 3628091 = 5442137) B5442137
theorem B2418727 : Blo 2149435 2418727 := bstep (se 1 (by rfl) ⟨1814045, by rfl⟩ : syracuseStep 2418727 = 3628091) B3628091
theorem B3224969 : Blo 2149435 3224969 := bstep (se 2 (by rfl) ⟨1209363, by rfl⟩ : syracuseStep 3224969 = 2418727) B2418727
theorem B2149979 : Blo 2149435 2149979 := bstep (se 1 (by rfl) ⟨1612484, by rfl⟩ : syracuseStep 2149979 = 3224969) B3224969
theorem B10884293 : Blo 2149435 10884293 := bbase (se 4 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 10884293 = 2040805) (by norm_num)
theorem B7256195 : Blo 2149435 7256195 := bstep (se 1 (by rfl) ⟨5442146, by rfl⟩ : syracuseStep 7256195 = 10884293) B10884293
theorem B4837463 : Blo 2149435 4837463 := bstep (se 1 (by rfl) ⟨3628097, by rfl⟩ : syracuseStep 4837463 = 7256195) B7256195
theorem B3224975 : Blo 2149435 3224975 := bstep (se 1 (by rfl) ⟨2418731, by rfl⟩ : syracuseStep 3224975 = 4837463) B4837463
theorem B2149983 : Blo 2149435 2149983 := bstep (se 1 (by rfl) ⟨1612487, by rfl⟩ : syracuseStep 2149983 = 3224975) B3224975
theorem B3224981 : Blo 2149435 3224981 := bbase (se 6 (by rfl) ⟨75585, by rfl⟩ : syracuseStep 3224981 = 151171) (by norm_num)
theorem B2149987 : Blo 2149435 2149987 := bstep (se 1 (by rfl) ⟨1612490, by rfl⟩ : syracuseStep 2149987 = 3224981) B3224981
theorem B4591829 : Blo 2149435 4591829 := bbase (se 7 (by rfl) ⟨53810, by rfl⟩ : syracuseStep 4591829 = 107621) (by norm_num)
theorem B12244877 : Blo 2149435 12244877 := bstep (se 3 (by rfl) ⟨2295914, by rfl⟩ : syracuseStep 12244877 = 4591829) B4591829
theorem B8163251 : Blo 2149435 8163251 := bstep (se 1 (by rfl) ⟨6122438, by rfl⟩ : syracuseStep 8163251 = 12244877) B12244877
theorem B5442167 : Blo 2149435 5442167 := bstep (se 1 (by rfl) ⟨4081625, by rfl⟩ : syracuseStep 5442167 = 8163251) B8163251
theorem B3628111 : Blo 2149435 3628111 := bstep (se 1 (by rfl) ⟨2721083, by rfl⟩ : syracuseStep 3628111 = 5442167) B5442167
theorem B4837481 : Blo 2149435 4837481 := bstep (se 2 (by rfl) ⟨1814055, by rfl⟩ : syracuseStep 4837481 = 3628111) B3628111
theorem B3224987 : Blo 2149435 3224987 := bstep (se 1 (by rfl) ⟨2418740, by rfl⟩ : syracuseStep 3224987 = 4837481) B4837481
theorem B2149991 : Blo 2149435 2149991 := bstep (se 1 (by rfl) ⟨1612493, by rfl⟩ : syracuseStep 2149991 = 3224987) B3224987
theorem B2418745 : Blo 2149435 2418745 := bbase (se 2 (by rfl) ⟨907029, by rfl⟩ : syracuseStep 2418745 = 1814059) (by norm_num)
theorem B3224993 : Blo 2149435 3224993 := bstep (se 2 (by rfl) ⟨1209372, by rfl⟩ : syracuseStep 3224993 = 2418745) B2418745
theorem B2149995 : Blo 2149435 2149995 := bstep (se 1 (by rfl) ⟨1612496, by rfl⟩ : syracuseStep 2149995 = 3224993) B3224993
theorem B3443885 : Blo 2149435 3443885 := bbase (se 3 (by rfl) ⟨645728, by rfl⟩ : syracuseStep 3443885 = 1291457) (by norm_num)
theorem B2295923 : Blo 2149435 2295923 := bstep (se 1 (by rfl) ⟨1721942, by rfl⟩ : syracuseStep 2295923 = 3443885) B3443885
theorem B6122461 : Blo 2149435 6122461 := bstep (se 3 (by rfl) ⟨1147961, by rfl⟩ : syracuseStep 6122461 = 2295923) B2295923
theorem B8163281 : Blo 2149435 8163281 := bstep (se 2 (by rfl) ⟨3061230, by rfl⟩ : syracuseStep 8163281 = 6122461) B6122461
theorem B5442187 : Blo 2149435 5442187 := bstep (se 1 (by rfl) ⟨4081640, by rfl⟩ : syracuseStep 5442187 = 8163281) B8163281
theorem B7256249 : Blo 2149435 7256249 := bstep (se 2 (by rfl) ⟨2721093, by rfl⟩ : syracuseStep 7256249 = 5442187) B5442187
theorem B4837499 : Blo 2149435 4837499 := bstep (se 1 (by rfl) ⟨3628124, by rfl⟩ : syracuseStep 4837499 = 7256249) B7256249
theorem B3224999 : Blo 2149435 3224999 := bstep (se 1 (by rfl) ⟨2418749, by rfl⟩ : syracuseStep 3224999 = 4837499) B4837499
theorem B2149999 : Blo 2149435 2149999 := bstep (se 1 (by rfl) ⟨1612499, by rfl⟩ : syracuseStep 2149999 = 3224999) B3224999
theorem B3225005 : Blo 2149435 3225005 := bbase (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) (by norm_num)
theorem B2150003 : Blo 2149435 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B4837517 : Blo 2149435 4837517 := bbase (se 3 (by rfl) ⟨907034, by rfl⟩ : syracuseStep 4837517 = 1814069) (by norm_num)
theorem B3225011 : Blo 2149435 3225011 := bstep (se 1 (by rfl) ⟨2418758, by rfl⟩ : syracuseStep 3225011 = 4837517) B4837517
theorem B2150007 : Blo 2149435 2150007 := bstep (se 1 (by rfl) ⟨1612505, by rfl⟩ : syracuseStep 2150007 = 3225011) B3225011
theorem B2721109 : Blo 2149435 2721109 := bbase (se 12 (by rfl) ⟨996, by rfl⟩ : syracuseStep 2721109 = 1993) (by norm_num)
theorem B3628145 : Blo 2149435 3628145 := bstep (se 2 (by rfl) ⟨1360554, by rfl⟩ : syracuseStep 3628145 = 2721109) B2721109
theorem B2418763 : Blo 2149435 2418763 := bstep (se 1 (by rfl) ⟨1814072, by rfl⟩ : syracuseStep 2418763 = 3628145) B3628145
theorem B3225017 : Blo 2149435 3225017 := bstep (se 2 (by rfl) ⟨1209381, by rfl⟩ : syracuseStep 3225017 = 2418763) B2418763
theorem B2150011 : Blo 2149435 2150011 := bstep (se 1 (by rfl) ⟨1612508, by rfl⟩ : syracuseStep 2150011 = 3225017) B3225017
theorem B5591741 : Blo 2149435 5591741 := bbase (se 3 (by rfl) ⟨1048451, by rfl⟩ : syracuseStep 5591741 = 2096903) (by norm_num)
theorem B14911309 : Blo 2149435 14911309 := bstep (se 3 (by rfl) ⟨2795870, by rfl⟩ : syracuseStep 14911309 = 5591741) B5591741
theorem B19881745 : Blo 2149435 19881745 := bstep (se 2 (by rfl) ⟨7455654, by rfl⟩ : syracuseStep 19881745 = 14911309) B14911309
theorem B424143893 : Blo 2149435 424143893 := bstep (se 6 (by rfl) ⟨9940872, by rfl⟩ : syracuseStep 424143893 = 19881745) B19881745
theorem B282762595 : Blo 2149435 282762595 := bstep (se 1 (by rfl) ⟨212071946, by rfl⟩ : syracuseStep 282762595 = 424143893) B424143893
theorem B1508067173 : Blo 2149435 1508067173 := bstep (se 4 (by rfl) ⟨141381297, by rfl⟩ : syracuseStep 1508067173 = 282762595) B282762595
theorem B1005378115 : Blo 2149435 1005378115 := bstep (se 1 (by rfl) ⟨754033586, by rfl⟩ : syracuseStep 1005378115 = 1508067173) B1508067173
theorem B1340504153 : Blo 2149435 1340504153 := bstep (se 2 (by rfl) ⟨502689057, by rfl⟩ : syracuseStep 1340504153 = 1005378115) B1005378115
theorem B893669435 : Blo 2149435 893669435 := bstep (se 1 (by rfl) ⟨670252076, by rfl⟩ : syracuseStep 893669435 = 1340504153) B1340504153
theorem B595779623 : Blo 2149435 595779623 := bstep (se 1 (by rfl) ⟨446834717, by rfl⟩ : syracuseStep 595779623 = 893669435) B893669435
theorem B397186415 : Blo 2149435 397186415 := bstep (se 1 (by rfl) ⟨297889811, by rfl⟩ : syracuseStep 397186415 = 595779623) B595779623
theorem B264790943 : Blo 2149435 264790943 := bstep (se 1 (by rfl) ⟨198593207, by rfl⟩ : syracuseStep 264790943 = 397186415) B397186415
theorem B176527295 : Blo 2149435 176527295 := bstep (se 1 (by rfl) ⟨132395471, by rfl⟩ : syracuseStep 176527295 = 264790943) B264790943
theorem B117684863 : Blo 2149435 117684863 := bstep (se 1 (by rfl) ⟨88263647, by rfl⟩ : syracuseStep 117684863 = 176527295) B176527295
theorem B78456575 : Blo 2149435 78456575 := bstep (se 1 (by rfl) ⟨58842431, by rfl⟩ : syracuseStep 78456575 = 117684863) B117684863
theorem B52304383 : Blo 2149435 52304383 := bstep (se 1 (by rfl) ⟨39228287, by rfl⟩ : syracuseStep 52304383 = 78456575) B78456575
theorem B69739177 : Blo 2149435 69739177 := bstep (se 2 (by rfl) ⟨26152191, by rfl⟩ : syracuseStep 69739177 = 52304383) B52304383
theorem B92985569 : Blo 2149435 92985569 := bstep (se 2 (by rfl) ⟨34869588, by rfl⟩ : syracuseStep 92985569 = 69739177) B69739177
theorem B61990379 : Blo 2149435 61990379 := bstep (se 1 (by rfl) ⟨46492784, by rfl⟩ : syracuseStep 61990379 = 92985569) B92985569
theorem B41326919 : Blo 2149435 41326919 := bstep (se 1 (by rfl) ⟨30995189, by rfl⟩ : syracuseStep 41326919 = 61990379) B61990379
theorem B27551279 : Blo 2149435 27551279 := bstep (se 1 (by rfl) ⟨20663459, by rfl⟩ : syracuseStep 27551279 = 41326919) B41326919
theorem B18367519 : Blo 2149435 18367519 := bstep (se 1 (by rfl) ⟨13775639, by rfl⟩ : syracuseStep 18367519 = 27551279) B27551279
theorem B24490025 : Blo 2149435 24490025 := bstep (se 2 (by rfl) ⟨9183759, by rfl⟩ : syracuseStep 24490025 = 18367519) B18367519
theorem B16326683 : Blo 2149435 16326683 := bstep (se 1 (by rfl) ⟨12245012, by rfl⟩ : syracuseStep 16326683 = 24490025) B24490025
theorem B10884455 : Blo 2149435 10884455 := bstep (se 1 (by rfl) ⟨8163341, by rfl⟩ : syracuseStep 10884455 = 16326683) B16326683
theorem B7256303 : Blo 2149435 7256303 := bstep (se 1 (by rfl) ⟨5442227, by rfl⟩ : syracuseStep 7256303 = 10884455) B10884455
theorem B4837535 : Blo 2149435 4837535 := bstep (se 1 (by rfl) ⟨3628151, by rfl⟩ : syracuseStep 4837535 = 7256303) B7256303
theorem B3225023 : Blo 2149435 3225023 := bstep (se 1 (by rfl) ⟨2418767, by rfl⟩ : syracuseStep 3225023 = 4837535) B4837535
theorem B2150015 : Blo 2149435 2150015 := bstep (se 1 (by rfl) ⟨1612511, by rfl⟩ : syracuseStep 2150015 = 3225023) B3225023
theorem B3225029 : Blo 2149435 3225029 := bbase (se 4 (by rfl) ⟨302346, by rfl⟩ : syracuseStep 3225029 = 604693) (by norm_num)
theorem B2150019 : Blo 2149435 2150019 := bstep (se 1 (by rfl) ⟨1612514, by rfl⟩ : syracuseStep 2150019 = 3225029) B3225029
theorem B3628165 : Blo 2149435 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B4837553 : Blo 2149435 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B3225035 : Blo 2149435 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B2150023 : Blo 2149435 2150023 := bstep (se 1 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 2150023 = 3225035) B3225035
theorem B2418781 : Blo 2149435 2418781 := bbase (se 3 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 2418781 = 907043) (by norm_num)
theorem B3225041 : Blo 2149435 3225041 := bstep (se 2 (by rfl) ⟨1209390, by rfl⟩ : syracuseStep 3225041 = 2418781) B2418781
theorem B2150027 : Blo 2149435 2150027 := bstep (se 1 (by rfl) ⟨1612520, by rfl⟩ : syracuseStep 2150027 = 3225041) B3225041
theorem B7256357 : Blo 2149435 7256357 := bbase (se 4 (by rfl) ⟨680283, by rfl⟩ : syracuseStep 7256357 = 1360567) (by norm_num)
theorem B4837571 : Blo 2149435 4837571 := bstep (se 1 (by rfl) ⟨3628178, by rfl⟩ : syracuseStep 4837571 = 7256357) B7256357
theorem B3225047 : Blo 2149435 3225047 := bstep (se 1 (by rfl) ⟨2418785, by rfl⟩ : syracuseStep 3225047 = 4837571) B4837571
theorem B2150031 : Blo 2149435 2150031 := bstep (se 1 (by rfl) ⟨1612523, by rfl⟩ : syracuseStep 2150031 = 3225047) B3225047
theorem B3225053 : Blo 2149435 3225053 := bbase (se 3 (by rfl) ⟨604697, by rfl⟩ : syracuseStep 3225053 = 1209395) (by norm_num)
theorem B2150035 : Blo 2149435 2150035 := bstep (se 1 (by rfl) ⟨1612526, by rfl⟩ : syracuseStep 2150035 = 3225053) B3225053
theorem B4837589 : Blo 2149435 4837589 := bbase (se 7 (by rfl) ⟨56690, by rfl⟩ : syracuseStep 4837589 = 113381) (by norm_num)
theorem B3225059 : Blo 2149435 3225059 := bstep (se 1 (by rfl) ⟨2418794, by rfl⟩ : syracuseStep 3225059 = 4837589) B4837589
theorem B2150039 : Blo 2149435 2150039 := bstep (se 1 (by rfl) ⟨1612529, by rfl⟩ : syracuseStep 2150039 = 3225059) B3225059
theorem B14710805 : Blo 2149435 14710805 := bbase (se 6 (by rfl) ⟨344784, by rfl⟩ : syracuseStep 14710805 = 689569) (by norm_num)
theorem B9807203 : Blo 2149435 9807203 := bstep (se 1 (by rfl) ⟨7355402, by rfl⟩ : syracuseStep 9807203 = 14710805) B14710805
theorem B26152541 : Blo 2149435 26152541 := bstep (se 3 (by rfl) ⟨4903601, by rfl⟩ : syracuseStep 26152541 = 9807203) B9807203
theorem B17435027 : Blo 2149435 17435027 := bstep (se 1 (by rfl) ⟨13076270, by rfl⟩ : syracuseStep 17435027 = 26152541) B26152541
theorem B11623351 : Blo 2149435 11623351 := bstep (se 1 (by rfl) ⟨8717513, by rfl⟩ : syracuseStep 11623351 = 17435027) B17435027
theorem B15497801 : Blo 2149435 15497801 := bstep (se 2 (by rfl) ⟨5811675, by rfl⟩ : syracuseStep 15497801 = 11623351) B11623351
theorem B10331867 : Blo 2149435 10331867 := bstep (se 1 (by rfl) ⟨7748900, by rfl⟩ : syracuseStep 10331867 = 15497801) B15497801
theorem B6887911 : Blo 2149435 6887911 := bstep (se 1 (by rfl) ⟨5165933, by rfl⟩ : syracuseStep 6887911 = 10331867) B10331867
theorem B9183881 : Blo 2149435 9183881 := bstep (se 2 (by rfl) ⟨3443955, by rfl⟩ : syracuseStep 9183881 = 6887911) B6887911
theorem B6122587 : Blo 2149435 6122587 := bstep (se 1 (by rfl) ⟨4591940, by rfl⟩ : syracuseStep 6122587 = 9183881) B9183881
theorem B8163449 : Blo 2149435 8163449 := bstep (se 2 (by rfl) ⟨3061293, by rfl⟩ : syracuseStep 8163449 = 6122587) B6122587
theorem B5442299 : Blo 2149435 5442299 := bstep (se 1 (by rfl) ⟨4081724, by rfl⟩ : syracuseStep 5442299 = 8163449) B8163449
theorem B3628199 : Blo 2149435 3628199 := bstep (se 1 (by rfl) ⟨2721149, by rfl⟩ : syracuseStep 3628199 = 5442299) B5442299
theorem B2418799 : Blo 2149435 2418799 := bstep (se 1 (by rfl) ⟨1814099, by rfl⟩ : syracuseStep 2418799 = 3628199) B3628199
theorem B3225065 : Blo 2149435 3225065 := bstep (se 2 (by rfl) ⟨1209399, by rfl⟩ : syracuseStep 3225065 = 2418799) B2418799
theorem B2150043 : Blo 2149435 2150043 := bstep (se 1 (by rfl) ⟨1612532, by rfl⟩ : syracuseStep 2150043 = 3225065) B3225065
theorem B4358765 : Blo 2149435 4358765 := bbase (se 3 (by rfl) ⟨817268, by rfl⟩ : syracuseStep 4358765 = 1634537) (by norm_num)
theorem B2905843 : Blo 2149435 2905843 := bstep (se 1 (by rfl) ⟨2179382, by rfl⟩ : syracuseStep 2905843 = 4358765) B4358765
theorem B3874457 : Blo 2149435 3874457 := bstep (se 2 (by rfl) ⟨1452921, by rfl⟩ : syracuseStep 3874457 = 2905843) B2905843
theorem B2582971 : Blo 2149435 2582971 := bstep (se 1 (by rfl) ⟨1937228, by rfl⟩ : syracuseStep 2582971 = 3874457) B3874457
theorem B13775845 : Blo 2149435 13775845 := bstep (se 4 (by rfl) ⟨1291485, by rfl⟩ : syracuseStep 13775845 = 2582971) B2582971
theorem B18367793 : Blo 2149435 18367793 := bstep (se 2 (by rfl) ⟨6887922, by rfl⟩ : syracuseStep 18367793 = 13775845) B13775845
theorem B12245195 : Blo 2149435 12245195 := bstep (se 1 (by rfl) ⟨9183896, by rfl⟩ : syracuseStep 12245195 = 18367793) B18367793
theorem B8163463 : Blo 2149435 8163463 := bstep (se 1 (by rfl) ⟨6122597, by rfl⟩ : syracuseStep 8163463 = 12245195) B12245195
theorem B10884617 : Blo 2149435 10884617 := bstep (se 2 (by rfl) ⟨4081731, by rfl⟩ : syracuseStep 10884617 = 8163463) B8163463
theorem B7256411 : Blo 2149435 7256411 := bstep (se 1 (by rfl) ⟨5442308, by rfl⟩ : syracuseStep 7256411 = 10884617) B10884617
theorem B4837607 : Blo 2149435 4837607 := bstep (se 1 (by rfl) ⟨3628205, by rfl⟩ : syracuseStep 4837607 = 7256411) B7256411
theorem B3225071 : Blo 2149435 3225071 := bstep (se 1 (by rfl) ⟨2418803, by rfl⟩ : syracuseStep 3225071 = 4837607) B4837607
theorem B2150047 : Blo 2149435 2150047 := bstep (se 1 (by rfl) ⟨1612535, by rfl⟩ : syracuseStep 2150047 = 3225071) B3225071
theorem B3225077 : Blo 2149435 3225077 := bbase (se 5 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 3225077 = 302351) (by norm_num)
theorem B2150051 : Blo 2149435 2150051 := bstep (se 1 (by rfl) ⟨1612538, by rfl⟩ : syracuseStep 2150051 = 3225077) B3225077
theorem B3727901 : Blo 2149435 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B9941069 : Blo 2149435 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B26509517 : Blo 2149435 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B17673011 : Blo 2149435 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B11782007 : Blo 2149435 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B7854671 : Blo 2149435 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B20945789 : Blo 2149435 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B13963859 : Blo 2149435 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B9309239 : Blo 2149435 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B6206159 : Blo 2149435 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B16549757 : Blo 2149435 16549757 := bstep (se 3 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 16549757 = 6206159) B6206159
theorem B11033171 : Blo 2149435 11033171 := bstep (se 1 (by rfl) ⟨8274878, by rfl⟩ : syracuseStep 11033171 = 16549757) B16549757
theorem B7355447 : Blo 2149435 7355447 := bstep (se 1 (by rfl) ⟨5516585, by rfl⟩ : syracuseStep 7355447 = 11033171) B11033171
theorem B4903631 : Blo 2149435 4903631 := bstep (se 1 (by rfl) ⟨3677723, by rfl⟩ : syracuseStep 4903631 = 7355447) B7355447
theorem B3269087 : Blo 2149435 3269087 := bstep (se 1 (by rfl) ⟨2451815, by rfl⟩ : syracuseStep 3269087 = 4903631) B4903631
theorem B2179391 : Blo 2149435 2179391 := bstep (se 1 (by rfl) ⟨1634543, by rfl⟩ : syracuseStep 2179391 = 3269087) B3269087
theorem B5811709 : Blo 2149435 5811709 := bstep (se 3 (by rfl) ⟨1089695, by rfl⟩ : syracuseStep 5811709 = 2179391) B2179391
theorem B7748945 : Blo 2149435 7748945 := bstep (se 2 (by rfl) ⟨2905854, by rfl⟩ : syracuseStep 7748945 = 5811709) B5811709
theorem B5165963 : Blo 2149435 5165963 := bstep (se 1 (by rfl) ⟨3874472, by rfl⟩ : syracuseStep 5165963 = 7748945) B7748945
theorem B3443975 : Blo 2149435 3443975 := bstep (se 1 (by rfl) ⟨2582981, by rfl⟩ : syracuseStep 3443975 = 5165963) B5165963
theorem B2295983 : Blo 2149435 2295983 := bstep (se 1 (by rfl) ⟨1721987, by rfl⟩ : syracuseStep 2295983 = 3443975) B3443975
theorem B6122621 : Blo 2149435 6122621 := bstep (se 3 (by rfl) ⟨1147991, by rfl⟩ : syracuseStep 6122621 = 2295983) B2295983
theorem B4081747 : Blo 2149435 4081747 := bstep (se 1 (by rfl) ⟨3061310, by rfl⟩ : syracuseStep 4081747 = 6122621) B6122621
theorem B5442329 : Blo 2149435 5442329 := bstep (se 2 (by rfl) ⟨2040873, by rfl⟩ : syracuseStep 5442329 = 4081747) B4081747
theorem B3628219 : Blo 2149435 3628219 := bstep (se 1 (by rfl) ⟨2721164, by rfl⟩ : syracuseStep 3628219 = 5442329) B5442329
theorem B4837625 : Blo 2149435 4837625 := bstep (se 2 (by rfl) ⟨1814109, by rfl⟩ : syracuseStep 4837625 = 3628219) B3628219
theorem B3225083 : Blo 2149435 3225083 := bstep (se 1 (by rfl) ⟨2418812, by rfl⟩ : syracuseStep 3225083 = 4837625) B4837625
theorem B2150055 : Blo 2149435 2150055 := bstep (se 1 (by rfl) ⟨1612541, by rfl⟩ : syracuseStep 2150055 = 3225083) B3225083
theorem B2418817 : Blo 2149435 2418817 := bbase (se 2 (by rfl) ⟨907056, by rfl⟩ : syracuseStep 2418817 = 1814113) (by norm_num)
theorem B3225089 : Blo 2149435 3225089 := bstep (se 2 (by rfl) ⟨1209408, by rfl⟩ : syracuseStep 3225089 = 2418817) B2418817
theorem B2150059 : Blo 2149435 2150059 := bstep (se 1 (by rfl) ⟨1612544, by rfl⟩ : syracuseStep 2150059 = 3225089) B3225089
theorem B5442349 : Blo 2149435 5442349 := bbase (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) (by norm_num)
theorem B7256465 : Blo 2149435 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B4837643 : Blo 2149435 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B3225095 : Blo 2149435 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B2150063 : Blo 2149435 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B3225101 : Blo 2149435 3225101 := bbase (se 3 (by rfl) ⟨604706, by rfl⟩ : syracuseStep 3225101 = 1209413) (by norm_num)
theorem B2150067 : Blo 2149435 2150067 := bstep (se 1 (by rfl) ⟨1612550, by rfl⟩ : syracuseStep 2150067 = 3225101) B3225101
theorem B4837661 : Blo 2149435 4837661 := bbase (se 3 (by rfl) ⟨907061, by rfl⟩ : syracuseStep 4837661 = 1814123) (by norm_num)
theorem B3225107 : Blo 2149435 3225107 := bstep (se 1 (by rfl) ⟨2418830, by rfl⟩ : syracuseStep 3225107 = 4837661) B4837661
theorem B2150071 : Blo 2149435 2150071 := bstep (se 1 (by rfl) ⟨1612553, by rfl⟩ : syracuseStep 2150071 = 3225107) B3225107
theorem B3628253 : Blo 2149435 3628253 := bbase (se 3 (by rfl) ⟨680297, by rfl⟩ : syracuseStep 3628253 = 1360595) (by norm_num)
theorem B2418835 : Blo 2149435 2418835 := bstep (se 1 (by rfl) ⟨1814126, by rfl⟩ : syracuseStep 2418835 = 3628253) B3628253
theorem B3225113 : Blo 2149435 3225113 := bstep (se 2 (by rfl) ⟨1209417, by rfl⟩ : syracuseStep 3225113 = 2418835) B2418835
theorem B2150075 : Blo 2149435 2150075 := bstep (se 1 (by rfl) ⟨1612556, by rfl⟩ : syracuseStep 2150075 = 3225113) B3225113
theorem B7749029 : Blo 2149435 7749029 := bbase (se 4 (by rfl) ⟨726471, by rfl⟩ : syracuseStep 7749029 = 1452943) (by norm_num)
theorem B5166019 : Blo 2149435 5166019 := bstep (se 1 (by rfl) ⟨3874514, by rfl⟩ : syracuseStep 5166019 = 7749029) B7749029
theorem B6888025 : Blo 2149435 6888025 := bstep (se 2 (by rfl) ⟨2583009, by rfl⟩ : syracuseStep 6888025 = 5166019) B5166019
theorem B9184033 : Blo 2149435 9184033 := bstep (se 2 (by rfl) ⟨3444012, by rfl⟩ : syracuseStep 9184033 = 6888025) B6888025
theorem B12245377 : Blo 2149435 12245377 := bstep (se 2 (by rfl) ⟨4592016, by rfl⟩ : syracuseStep 12245377 = 9184033) B9184033
theorem B16327169 : Blo 2149435 16327169 := bstep (se 2 (by rfl) ⟨6122688, by rfl⟩ : syracuseStep 16327169 = 12245377) B12245377
theorem B10884779 : Blo 2149435 10884779 := bstep (se 1 (by rfl) ⟨8163584, by rfl⟩ : syracuseStep 10884779 = 16327169) B16327169
theorem B7256519 : Blo 2149435 7256519 := bstep (se 1 (by rfl) ⟨5442389, by rfl⟩ : syracuseStep 7256519 = 10884779) B10884779
theorem B4837679 : Blo 2149435 4837679 := bstep (se 1 (by rfl) ⟨3628259, by rfl⟩ : syracuseStep 4837679 = 7256519) B7256519
theorem B3225119 : Blo 2149435 3225119 := bstep (se 1 (by rfl) ⟨2418839, by rfl⟩ : syracuseStep 3225119 = 4837679) B4837679
theorem B2150079 : Blo 2149435 2150079 := bstep (se 1 (by rfl) ⟨1612559, by rfl⟩ : syracuseStep 2150079 = 3225119) B3225119
theorem B3225125 : Blo 2149435 3225125 := bbase (se 4 (by rfl) ⟨302355, by rfl⟩ : syracuseStep 3225125 = 604711) (by norm_num)
theorem B2150083 : Blo 2149435 2150083 := bstep (se 1 (by rfl) ⟨1612562, by rfl⟩ : syracuseStep 2150083 = 3225125) B3225125
theorem B2721205 : Blo 2149435 2721205 := bbase (se 5 (by rfl) ⟨127556, by rfl⟩ : syracuseStep 2721205 = 255113) (by norm_num)
theorem B3628273 : Blo 2149435 3628273 := bstep (se 2 (by rfl) ⟨1360602, by rfl⟩ : syracuseStep 3628273 = 2721205) B2721205
theorem B4837697 : Blo 2149435 4837697 := bstep (se 2 (by rfl) ⟨1814136, by rfl⟩ : syracuseStep 4837697 = 3628273) B3628273
theorem B3225131 : Blo 2149435 3225131 := bstep (se 1 (by rfl) ⟨2418848, by rfl⟩ : syracuseStep 3225131 = 4837697) B4837697
theorem B2150087 : Blo 2149435 2150087 := bstep (se 1 (by rfl) ⟨1612565, by rfl⟩ : syracuseStep 2150087 = 3225131) B3225131
theorem B2418853 : Blo 2149435 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B3225137 : Blo 2149435 3225137 := bstep (se 2 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 3225137 = 2418853) B2418853
theorem B2150091 : Blo 2149435 2150091 := bstep (se 1 (by rfl) ⟨1612568, by rfl⟩ : syracuseStep 2150091 = 3225137) B3225137
theorem B15923957 : Blo 2149435 15923957 := bbase (se 5 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 15923957 = 1492871) (by norm_num)
theorem B42463885 : Blo 2149435 42463885 := bstep (se 3 (by rfl) ⟨7961978, by rfl⟩ : syracuseStep 42463885 = 15923957) B15923957
theorem B56618513 : Blo 2149435 56618513 := bstep (se 2 (by rfl) ⟨21231942, by rfl⟩ : syracuseStep 56618513 = 42463885) B42463885
theorem B37745675 : Blo 2149435 37745675 := bstep (se 1 (by rfl) ⟨28309256, by rfl⟩ : syracuseStep 37745675 = 56618513) B56618513
theorem B25163783 : Blo 2149435 25163783 := bstep (se 1 (by rfl) ⟨18872837, by rfl⟩ : syracuseStep 25163783 = 37745675) B37745675
theorem B16775855 : Blo 2149435 16775855 := bstep (se 1 (by rfl) ⟨12581891, by rfl⟩ : syracuseStep 16775855 = 25163783) B25163783
theorem B11183903 : Blo 2149435 11183903 := bstep (se 1 (by rfl) ⟨8387927, by rfl⟩ : syracuseStep 11183903 = 16775855) B16775855
theorem B7455935 : Blo 2149435 7455935 := bstep (se 1 (by rfl) ⟨5591951, by rfl⟩ : syracuseStep 7455935 = 11183903) B11183903
theorem B19882493 : Blo 2149435 19882493 := bstep (se 3 (by rfl) ⟨3727967, by rfl⟩ : syracuseStep 19882493 = 7455935) B7455935
theorem B13254995 : Blo 2149435 13254995 := bstep (se 1 (by rfl) ⟨9941246, by rfl⟩ : syracuseStep 13254995 = 19882493) B19882493
theorem B8836663 : Blo 2149435 8836663 := bstep (se 1 (by rfl) ⟨6627497, by rfl⟩ : syracuseStep 8836663 = 13254995) B13254995
theorem B11782217 : Blo 2149435 11782217 := bstep (se 2 (by rfl) ⟨4418331, by rfl⟩ : syracuseStep 11782217 = 8836663) B8836663
theorem B31419245 : Blo 2149435 31419245 := bstep (se 3 (by rfl) ⟨5891108, by rfl⟩ : syracuseStep 31419245 = 11782217) B11782217
theorem B20946163 : Blo 2149435 20946163 := bstep (se 1 (by rfl) ⟨15709622, by rfl⟩ : syracuseStep 20946163 = 31419245) B31419245
theorem B27928217 : Blo 2149435 27928217 := bstep (se 2 (by rfl) ⟨10473081, by rfl⟩ : syracuseStep 27928217 = 20946163) B20946163
theorem B18618811 : Blo 2149435 18618811 := bstep (se 1 (by rfl) ⟨13964108, by rfl⟩ : syracuseStep 18618811 = 27928217) B27928217
theorem B99300325 : Blo 2149435 99300325 := bstep (se 4 (by rfl) ⟨9309405, by rfl⟩ : syracuseStep 99300325 = 18618811) B18618811
theorem B132400433 : Blo 2149435 132400433 := bstep (se 2 (by rfl) ⟨49650162, by rfl⟩ : syracuseStep 132400433 = 99300325) B99300325
theorem B88266955 : Blo 2149435 88266955 := bstep (se 1 (by rfl) ⟨66200216, by rfl⟩ : syracuseStep 88266955 = 132400433) B132400433
theorem B117689273 : Blo 2149435 117689273 := bstep (se 2 (by rfl) ⟨44133477, by rfl⟩ : syracuseStep 117689273 = 88266955) B88266955
theorem B78459515 : Blo 2149435 78459515 := bstep (se 1 (by rfl) ⟨58844636, by rfl⟩ : syracuseStep 78459515 = 117689273) B117689273
theorem B52306343 : Blo 2149435 52306343 := bstep (se 1 (by rfl) ⟨39229757, by rfl⟩ : syracuseStep 52306343 = 78459515) B78459515
theorem B34870895 : Blo 2149435 34870895 := bstep (se 1 (by rfl) ⟨26153171, by rfl⟩ : syracuseStep 34870895 = 52306343) B52306343
theorem B23247263 : Blo 2149435 23247263 := bstep (se 1 (by rfl) ⟨17435447, by rfl⟩ : syracuseStep 23247263 = 34870895) B34870895
theorem B15498175 : Blo 2149435 15498175 := bstep (se 1 (by rfl) ⟨11623631, by rfl⟩ : syracuseStep 15498175 = 23247263) B23247263
theorem B20664233 : Blo 2149435 20664233 := bstep (se 2 (by rfl) ⟨7749087, by rfl⟩ : syracuseStep 20664233 = 15498175) B15498175
theorem B13776155 : Blo 2149435 13776155 := bstep (se 1 (by rfl) ⟨10332116, by rfl⟩ : syracuseStep 13776155 = 20664233) B20664233
theorem B9184103 : Blo 2149435 9184103 := bstep (se 1 (by rfl) ⟨6888077, by rfl⟩ : syracuseStep 9184103 = 13776155) B13776155
theorem B6122735 : Blo 2149435 6122735 := bstep (se 1 (by rfl) ⟨4592051, by rfl⟩ : syracuseStep 6122735 = 9184103) B9184103
theorem B4081823 : Blo 2149435 4081823 := bstep (se 1 (by rfl) ⟨3061367, by rfl⟩ : syracuseStep 4081823 = 6122735) B6122735
theorem B2721215 : Blo 2149435 2721215 := bstep (se 1 (by rfl) ⟨2040911, by rfl⟩ : syracuseStep 2721215 = 4081823) B4081823
theorem B7256573 : Blo 2149435 7256573 := bstep (se 3 (by rfl) ⟨1360607, by rfl⟩ : syracuseStep 7256573 = 2721215) B2721215
theorem B4837715 : Blo 2149435 4837715 := bstep (se 1 (by rfl) ⟨3628286, by rfl⟩ : syracuseStep 4837715 = 7256573) B7256573
theorem B3225143 : Blo 2149435 3225143 := bstep (se 1 (by rfl) ⟨2418857, by rfl⟩ : syracuseStep 3225143 = 4837715) B4837715
theorem B2150095 : Blo 2149435 2150095 := bstep (se 1 (by rfl) ⟨1612571, by rfl⟩ : syracuseStep 2150095 = 3225143) B3225143
theorem B3225149 : Blo 2149435 3225149 := bbase (se 3 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 3225149 = 1209431) (by norm_num)
theorem B2150099 : Blo 2149435 2150099 := bstep (se 1 (by rfl) ⟨1612574, by rfl⟩ : syracuseStep 2150099 = 3225149) B3225149
theorem B4837733 : Blo 2149435 4837733 := bbase (se 4 (by rfl) ⟨453537, by rfl⟩ : syracuseStep 4837733 = 907075) (by norm_num)
theorem B3225155 : Blo 2149435 3225155 := bstep (se 1 (by rfl) ⟨2418866, by rfl⟩ : syracuseStep 3225155 = 4837733) B4837733
theorem B2150103 : Blo 2149435 2150103 := bstep (se 1 (by rfl) ⟨1612577, by rfl⟩ : syracuseStep 2150103 = 3225155) B3225155
theorem B5442461 : Blo 2149435 5442461 := bbase (se 3 (by rfl) ⟨1020461, by rfl⟩ : syracuseStep 5442461 = 2040923) (by norm_num)
theorem B3628307 : Blo 2149435 3628307 := bstep (se 1 (by rfl) ⟨2721230, by rfl⟩ : syracuseStep 3628307 = 5442461) B5442461
theorem B2418871 : Blo 2149435 2418871 := bstep (se 1 (by rfl) ⟨1814153, by rfl⟩ : syracuseStep 2418871 = 3628307) B3628307
theorem B3225161 : Blo 2149435 3225161 := bstep (se 2 (by rfl) ⟨1209435, by rfl⟩ : syracuseStep 3225161 = 2418871) B2418871
theorem B2150107 : Blo 2149435 2150107 := bstep (se 1 (by rfl) ⟨1612580, by rfl⟩ : syracuseStep 2150107 = 3225161) B3225161
theorem B4081853 : Blo 2149435 4081853 := bbase (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) (by norm_num)
theorem B10884941 : Blo 2149435 10884941 := bstep (se 3 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 10884941 = 4081853) B4081853
theorem B7256627 : Blo 2149435 7256627 := bstep (se 1 (by rfl) ⟨5442470, by rfl⟩ : syracuseStep 7256627 = 10884941) B10884941
theorem B4837751 : Blo 2149435 4837751 := bstep (se 1 (by rfl) ⟨3628313, by rfl⟩ : syracuseStep 4837751 = 7256627) B7256627
theorem B3225167 : Blo 2149435 3225167 := bstep (se 1 (by rfl) ⟨2418875, by rfl⟩ : syracuseStep 3225167 = 4837751) B4837751
theorem B2150111 : Blo 2149435 2150111 := bstep (se 1 (by rfl) ⟨1612583, by rfl⟩ : syracuseStep 2150111 = 3225167) B3225167
theorem B3225173 : Blo 2149435 3225173 := bbase (se 8 (by rfl) ⟨18897, by rfl⟩ : syracuseStep 3225173 = 37795) (by norm_num)
theorem B2150115 : Blo 2149435 2150115 := bstep (se 1 (by rfl) ⟨1612586, by rfl⟩ : syracuseStep 2150115 = 3225173) B3225173
theorem B3444077 : Blo 2149435 3444077 := bbase (se 3 (by rfl) ⟨645764, by rfl⟩ : syracuseStep 3444077 = 1291529) (by norm_num)
theorem B9184205 : Blo 2149435 9184205 := bstep (se 3 (by rfl) ⟨1722038, by rfl⟩ : syracuseStep 9184205 = 3444077) B3444077
theorem B6122803 : Blo 2149435 6122803 := bstep (se 1 (by rfl) ⟨4592102, by rfl⟩ : syracuseStep 6122803 = 9184205) B9184205
theorem B8163737 : Blo 2149435 8163737 := bstep (se 2 (by rfl) ⟨3061401, by rfl⟩ : syracuseStep 8163737 = 6122803) B6122803
theorem B5442491 : Blo 2149435 5442491 := bstep (se 1 (by rfl) ⟨4081868, by rfl⟩ : syracuseStep 5442491 = 8163737) B8163737
theorem B3628327 : Blo 2149435 3628327 := bstep (se 1 (by rfl) ⟨2721245, by rfl⟩ : syracuseStep 3628327 = 5442491) B5442491
theorem B4837769 : Blo 2149435 4837769 := bstep (se 2 (by rfl) ⟨1814163, by rfl⟩ : syracuseStep 4837769 = 3628327) B3628327
theorem B3225179 : Blo 2149435 3225179 := bstep (se 1 (by rfl) ⟨2418884, by rfl⟩ : syracuseStep 3225179 = 4837769) B4837769
theorem B2150119 : Blo 2149435 2150119 := bstep (se 1 (by rfl) ⟨1612589, by rfl⟩ : syracuseStep 2150119 = 3225179) B3225179
theorem B2418889 : Blo 2149435 2418889 := bbase (se 2 (by rfl) ⟨907083, by rfl⟩ : syracuseStep 2418889 = 1814167) (by norm_num)
theorem B3225185 : Blo 2149435 3225185 := bstep (se 2 (by rfl) ⟨1209444, by rfl⟩ : syracuseStep 3225185 = 2418889) B2418889
theorem B2150123 : Blo 2149435 2150123 := bstep (se 1 (by rfl) ⟨1612592, by rfl⟩ : syracuseStep 2150123 = 3225185) B3225185
theorem B14711381 : Blo 2149435 14711381 := bbase (se 8 (by rfl) ⟨86199, by rfl⟩ : syracuseStep 14711381 = 172399) (by norm_num)
theorem B9807587 : Blo 2149435 9807587 := bstep (se 1 (by rfl) ⟨7355690, by rfl⟩ : syracuseStep 9807587 = 14711381) B14711381
theorem B6538391 : Blo 2149435 6538391 := bstep (se 1 (by rfl) ⟨4903793, by rfl⟩ : syracuseStep 6538391 = 9807587) B9807587
theorem B4358927 : Blo 2149435 4358927 := bstep (se 1 (by rfl) ⟨3269195, by rfl⟩ : syracuseStep 4358927 = 6538391) B6538391
theorem B2905951 : Blo 2149435 2905951 := bstep (se 1 (by rfl) ⟨2179463, by rfl⟩ : syracuseStep 2905951 = 4358927) B4358927
theorem B3874601 : Blo 2149435 3874601 := bstep (se 2 (by rfl) ⟨1452975, by rfl⟩ : syracuseStep 3874601 = 2905951) B2905951
theorem B10332269 : Blo 2149435 10332269 := bstep (se 3 (by rfl) ⟨1937300, by rfl⟩ : syracuseStep 10332269 = 3874601) B3874601
theorem B6888179 : Blo 2149435 6888179 := bstep (se 1 (by rfl) ⟨5166134, by rfl⟩ : syracuseStep 6888179 = 10332269) B10332269
theorem B18368477 : Blo 2149435 18368477 := bstep (se 3 (by rfl) ⟨3444089, by rfl⟩ : syracuseStep 18368477 = 6888179) B6888179
theorem B12245651 : Blo 2149435 12245651 := bstep (se 1 (by rfl) ⟨9184238, by rfl⟩ : syracuseStep 12245651 = 18368477) B18368477
theorem B8163767 : Blo 2149435 8163767 := bstep (se 1 (by rfl) ⟨6122825, by rfl⟩ : syracuseStep 8163767 = 12245651) B12245651
theorem B5442511 : Blo 2149435 5442511 := bstep (se 1 (by rfl) ⟨4081883, by rfl⟩ : syracuseStep 5442511 = 8163767) B8163767
theorem B7256681 : Blo 2149435 7256681 := bstep (se 2 (by rfl) ⟨2721255, by rfl⟩ : syracuseStep 7256681 = 5442511) B5442511
theorem B4837787 : Blo 2149435 4837787 := bstep (se 1 (by rfl) ⟨3628340, by rfl⟩ : syracuseStep 4837787 = 7256681) B7256681
theorem B3225191 : Blo 2149435 3225191 := bstep (se 1 (by rfl) ⟨2418893, by rfl⟩ : syracuseStep 3225191 = 4837787) B4837787
theorem B2150127 : Blo 2149435 2150127 := bstep (se 1 (by rfl) ⟨1612595, by rfl⟩ : syracuseStep 2150127 = 3225191) B3225191
theorem B3225197 : Blo 2149435 3225197 := bbase (se 3 (by rfl) ⟨604724, by rfl⟩ : syracuseStep 3225197 = 1209449) (by norm_num)
theorem B2150131 : Blo 2149435 2150131 := bstep (se 1 (by rfl) ⟨1612598, by rfl⟩ : syracuseStep 2150131 = 3225197) B3225197
theorem B4837805 : Blo 2149435 4837805 := bbase (se 3 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 4837805 = 1814177) (by norm_num)
theorem B3225203 : Blo 2149435 3225203 := bstep (se 1 (by rfl) ⟨2418902, by rfl⟩ : syracuseStep 3225203 = 4837805) B4837805
theorem B2150135 : Blo 2149435 2150135 := bstep (se 1 (by rfl) ⟨1612601, by rfl⟩ : syracuseStep 2150135 = 3225203) B3225203
theorem B2296073 : Blo 2149435 2296073 := bbase (se 2 (by rfl) ⟨861027, by rfl⟩ : syracuseStep 2296073 = 1722055) (by norm_num)
theorem B6122861 : Blo 2149435 6122861 := bstep (se 3 (by rfl) ⟨1148036, by rfl⟩ : syracuseStep 6122861 = 2296073) B2296073
theorem B4081907 : Blo 2149435 4081907 := bstep (se 1 (by rfl) ⟨3061430, by rfl⟩ : syracuseStep 4081907 = 6122861) B6122861
theorem B2721271 : Blo 2149435 2721271 := bstep (se 1 (by rfl) ⟨2040953, by rfl⟩ : syracuseStep 2721271 = 4081907) B4081907
theorem B3628361 : Blo 2149435 3628361 := bstep (se 2 (by rfl) ⟨1360635, by rfl⟩ : syracuseStep 3628361 = 2721271) B2721271
theorem B2418907 : Blo 2149435 2418907 := bstep (se 1 (by rfl) ⟨1814180, by rfl⟩ : syracuseStep 2418907 = 3628361) B3628361
theorem B3225209 : Blo 2149435 3225209 := bstep (se 2 (by rfl) ⟨1209453, by rfl⟩ : syracuseStep 3225209 = 2418907) B2418907
theorem B2150139 : Blo 2149435 2150139 := bstep (se 1 (by rfl) ⟨1612604, by rfl⟩ : syracuseStep 2150139 = 3225209) B3225209
theorem B61994069 : Blo 2149435 61994069 := bbase (se 8 (by rfl) ⟨363246, by rfl⟩ : syracuseStep 61994069 = 726493) (by norm_num)
theorem B41329379 : Blo 2149435 41329379 := bstep (se 1 (by rfl) ⟨30997034, by rfl⟩ : syracuseStep 41329379 = 61994069) B61994069
theorem B27552919 : Blo 2149435 27552919 := bstep (se 1 (by rfl) ⟨20664689, by rfl⟩ : syracuseStep 27552919 = 41329379) B41329379
theorem B36737225 : Blo 2149435 36737225 := bstep (se 2 (by rfl) ⟨13776459, by rfl⟩ : syracuseStep 36737225 = 27552919) B27552919
theorem B24491483 : Blo 2149435 24491483 := bstep (se 1 (by rfl) ⟨18368612, by rfl⟩ : syracuseStep 24491483 = 36737225) B36737225
theorem B16327655 : Blo 2149435 16327655 := bstep (se 1 (by rfl) ⟨12245741, by rfl⟩ : syracuseStep 16327655 = 24491483) B24491483
theorem B10885103 : Blo 2149435 10885103 := bstep (se 1 (by rfl) ⟨8163827, by rfl⟩ : syracuseStep 10885103 = 16327655) B16327655
theorem B7256735 : Blo 2149435 7256735 := bstep (se 1 (by rfl) ⟨5442551, by rfl⟩ : syracuseStep 7256735 = 10885103) B10885103
theorem B4837823 : Blo 2149435 4837823 := bstep (se 1 (by rfl) ⟨3628367, by rfl⟩ : syracuseStep 4837823 = 7256735) B7256735
theorem B3225215 : Blo 2149435 3225215 := bstep (se 1 (by rfl) ⟨2418911, by rfl⟩ : syracuseStep 3225215 = 4837823) B4837823
theorem B2150143 : Blo 2149435 2150143 := bstep (se 1 (by rfl) ⟨1612607, by rfl⟩ : syracuseStep 2150143 = 3225215) B3225215
theorem B3225221 : Blo 2149435 3225221 := bbase (se 4 (by rfl) ⟨302364, by rfl⟩ : syracuseStep 3225221 = 604729) (by norm_num)
theorem B2150147 : Blo 2149435 2150147 := bstep (se 1 (by rfl) ⟨1612610, by rfl⟩ : syracuseStep 2150147 = 3225221) B3225221
theorem B3628381 : Blo 2149435 3628381 := bbase (se 3 (by rfl) ⟨680321, by rfl⟩ : syracuseStep 3628381 = 1360643) (by norm_num)
theorem B4837841 : Blo 2149435 4837841 := bstep (se 2 (by rfl) ⟨1814190, by rfl⟩ : syracuseStep 4837841 = 3628381) B3628381
theorem B3225227 : Blo 2149435 3225227 := bstep (se 1 (by rfl) ⟨2418920, by rfl⟩ : syracuseStep 3225227 = 4837841) B4837841
theorem B2150151 : Blo 2149435 2150151 := bstep (se 1 (by rfl) ⟨1612613, by rfl⟩ : syracuseStep 2150151 = 3225227) B3225227
theorem B2418925 : Blo 2149435 2418925 := bbase (se 3 (by rfl) ⟨453548, by rfl⟩ : syracuseStep 2418925 = 907097) (by norm_num)
theorem B3225233 : Blo 2149435 3225233 := bstep (se 2 (by rfl) ⟨1209462, by rfl⟩ : syracuseStep 3225233 = 2418925) B2418925
theorem B2150155 : Blo 2149435 2150155 := bstep (se 1 (by rfl) ⟨1612616, by rfl⟩ : syracuseStep 2150155 = 3225233) B3225233
theorem B7256789 : Blo 2149435 7256789 := bbase (se 7 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 7256789 = 170081) (by norm_num)
theorem B4837859 : Blo 2149435 4837859 := bstep (se 1 (by rfl) ⟨3628394, by rfl⟩ : syracuseStep 4837859 = 7256789) B7256789
theorem B3225239 : Blo 2149435 3225239 := bstep (se 1 (by rfl) ⟨2418929, by rfl⟩ : syracuseStep 3225239 = 4837859) B4837859
theorem B2150159 : Blo 2149435 2150159 := bstep (se 1 (by rfl) ⟨1612619, by rfl⟩ : syracuseStep 2150159 = 3225239) B3225239
theorem B3225245 : Blo 2149435 3225245 := bbase (se 3 (by rfl) ⟨604733, by rfl⟩ : syracuseStep 3225245 = 1209467) (by norm_num)
theorem B2150163 : Blo 2149435 2150163 := bstep (se 1 (by rfl) ⟨1612622, by rfl⟩ : syracuseStep 2150163 = 3225245) B3225245
theorem B4837877 : Blo 2149435 4837877 := bbase (se 5 (by rfl) ⟨226775, by rfl⟩ : syracuseStep 4837877 = 453551) (by norm_num)
theorem B3225251 : Blo 2149435 3225251 := bstep (se 1 (by rfl) ⟨2418938, by rfl⟩ : syracuseStep 3225251 = 4837877) B4837877
theorem B2150167 : Blo 2149435 2150167 := bstep (se 1 (by rfl) ⟨1612625, by rfl⟩ : syracuseStep 2150167 = 3225251) B3225251
theorem B5812021 : Blo 2149435 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B7749361 : Blo 2149435 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B41329925 : Blo 2149435 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B27553283 : Blo 2149435 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B18368855 : Blo 2149435 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B12245903 : Blo 2149435 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B8163935 : Blo 2149435 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B5442623 : Blo 2149435 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B3628415 : Blo 2149435 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B2418943 : Blo 2149435 2418943 := bstep (se 1 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 2418943 = 3628415) B3628415
theorem B3225257 : Blo 2149435 3225257 := bstep (se 2 (by rfl) ⟨1209471, by rfl⟩ : syracuseStep 3225257 = 2418943) B2418943
theorem B2150171 : Blo 2149435 2150171 := bstep (se 1 (by rfl) ⟨1612628, by rfl⟩ : syracuseStep 2150171 = 3225257) B3225257
theorem B3269269 : Blo 2149435 3269269 := bbase (se 6 (by rfl) ⟨76623, by rfl⟩ : syracuseStep 3269269 = 153247) (by norm_num)
theorem B4359025 : Blo 2149435 4359025 := bstep (se 2 (by rfl) ⟨1634634, by rfl⟩ : syracuseStep 4359025 = 3269269) B3269269
theorem B5812033 : Blo 2149435 5812033 := bstep (se 2 (by rfl) ⟨2179512, by rfl⟩ : syracuseStep 5812033 = 4359025) B4359025
theorem B7749377 : Blo 2149435 7749377 := bstep (se 2 (by rfl) ⟨2906016, by rfl⟩ : syracuseStep 7749377 = 5812033) B5812033
theorem B5166251 : Blo 2149435 5166251 := bstep (se 1 (by rfl) ⟨3874688, by rfl⟩ : syracuseStep 5166251 = 7749377) B7749377
theorem B3444167 : Blo 2149435 3444167 := bstep (se 1 (by rfl) ⟨2583125, by rfl⟩ : syracuseStep 3444167 = 5166251) B5166251
theorem B2296111 : Blo 2149435 2296111 := bstep (se 1 (by rfl) ⟨1722083, by rfl⟩ : syracuseStep 2296111 = 3444167) B3444167
theorem B3061481 : Blo 2149435 3061481 := bstep (se 2 (by rfl) ⟨1148055, by rfl⟩ : syracuseStep 3061481 = 2296111) B2296111
theorem B8163949 : Blo 2149435 8163949 := bstep (se 3 (by rfl) ⟨1530740, by rfl⟩ : syracuseStep 8163949 = 3061481) B3061481
theorem B10885265 : Blo 2149435 10885265 := bstep (se 2 (by rfl) ⟨4081974, by rfl⟩ : syracuseStep 10885265 = 8163949) B8163949
theorem B7256843 : Blo 2149435 7256843 := bstep (se 1 (by rfl) ⟨5442632, by rfl⟩ : syracuseStep 7256843 = 10885265) B10885265
theorem B4837895 : Blo 2149435 4837895 := bstep (se 1 (by rfl) ⟨3628421, by rfl⟩ : syracuseStep 4837895 = 7256843) B7256843
theorem B3225263 : Blo 2149435 3225263 := bstep (se 1 (by rfl) ⟨2418947, by rfl⟩ : syracuseStep 3225263 = 4837895) B4837895
theorem B2150175 : Blo 2149435 2150175 := bstep (se 1 (by rfl) ⟨1612631, by rfl⟩ : syracuseStep 2150175 = 3225263) B3225263
theorem B3225269 : Blo 2149435 3225269 := bbase (se 5 (by rfl) ⟨151184, by rfl⟩ : syracuseStep 3225269 = 302369) (by norm_num)
theorem B2150179 : Blo 2149435 2150179 := bstep (se 1 (by rfl) ⟨1612634, by rfl⟩ : syracuseStep 2150179 = 3225269) B3225269
theorem B5442653 : Blo 2149435 5442653 := bbase (se 3 (by rfl) ⟨1020497, by rfl⟩ : syracuseStep 5442653 = 2040995) (by norm_num)
theorem B3628435 : Blo 2149435 3628435 := bstep (se 1 (by rfl) ⟨2721326, by rfl⟩ : syracuseStep 3628435 = 5442653) B5442653
theorem B4837913 : Blo 2149435 4837913 := bstep (se 2 (by rfl) ⟨1814217, by rfl⟩ : syracuseStep 4837913 = 3628435) B3628435
theorem B3225275 : Blo 2149435 3225275 := bstep (se 1 (by rfl) ⟨2418956, by rfl⟩ : syracuseStep 3225275 = 4837913) B4837913
theorem B2150183 : Blo 2149435 2150183 := bstep (se 1 (by rfl) ⟨1612637, by rfl⟩ : syracuseStep 2150183 = 3225275) B3225275
theorem B2418961 : Blo 2149435 2418961 := bbase (se 2 (by rfl) ⟨907110, by rfl⟩ : syracuseStep 2418961 = 1814221) (by norm_num)
theorem B3225281 : Blo 2149435 3225281 := bstep (se 2 (by rfl) ⟨1209480, by rfl⟩ : syracuseStep 3225281 = 2418961) B2418961
theorem B2150187 : Blo 2149435 2150187 := bstep (se 1 (by rfl) ⟨1612640, by rfl⟩ : syracuseStep 2150187 = 3225281) B3225281
theorem B4082005 : Blo 2149435 4082005 := bbase (se 10 (by rfl) ⟨5979, by rfl⟩ : syracuseStep 4082005 = 11959) (by norm_num)
theorem B5442673 : Blo 2149435 5442673 := bstep (se 2 (by rfl) ⟨2041002, by rfl⟩ : syracuseStep 5442673 = 4082005) B4082005
theorem B7256897 : Blo 2149435 7256897 := bstep (se 2 (by rfl) ⟨2721336, by rfl⟩ : syracuseStep 7256897 = 5442673) B5442673
theorem B4837931 : Blo 2149435 4837931 := bstep (se 1 (by rfl) ⟨3628448, by rfl⟩ : syracuseStep 4837931 = 7256897) B7256897
theorem B3225287 : Blo 2149435 3225287 := bstep (se 1 (by rfl) ⟨2418965, by rfl⟩ : syracuseStep 3225287 = 4837931) B4837931
theorem B2150191 : Blo 2149435 2150191 := bstep (se 1 (by rfl) ⟨1612643, by rfl⟩ : syracuseStep 2150191 = 3225287) B3225287
theorem B3225293 : Blo 2149435 3225293 := bbase (se 3 (by rfl) ⟨604742, by rfl⟩ : syracuseStep 3225293 = 1209485) (by norm_num)
theorem B2150195 : Blo 2149435 2150195 := bstep (se 1 (by rfl) ⟨1612646, by rfl⟩ : syracuseStep 2150195 = 3225293) B3225293
theorem B4837949 : Blo 2149435 4837949 := bbase (se 3 (by rfl) ⟨907115, by rfl⟩ : syracuseStep 4837949 = 1814231) (by norm_num)
theorem B3225299 : Blo 2149435 3225299 := bstep (se 1 (by rfl) ⟨2418974, by rfl⟩ : syracuseStep 3225299 = 4837949) B4837949
theorem B2150199 : Blo 2149435 2150199 := bstep (se 1 (by rfl) ⟨1612649, by rfl⟩ : syracuseStep 2150199 = 3225299) B3225299
theorem B3628469 : Blo 2149435 3628469 := bbase (se 5 (by rfl) ⟨170084, by rfl⟩ : syracuseStep 3628469 = 340169) (by norm_num)
theorem B2418979 : Blo 2149435 2418979 := bstep (se 1 (by rfl) ⟨1814234, by rfl⟩ : syracuseStep 2418979 = 3628469) B3628469
theorem B3225305 : Blo 2149435 3225305 := bstep (se 2 (by rfl) ⟨1209489, by rfl⟩ : syracuseStep 3225305 = 2418979) B2418979
theorem B2150203 : Blo 2149435 2150203 := bstep (se 1 (by rfl) ⟨1612652, by rfl⟩ : syracuseStep 2150203 = 3225305) B3225305
theorem B2296145 : Blo 2149435 2296145 := bbase (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) (by norm_num)
theorem B6123053 : Blo 2149435 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B16328141 : Blo 2149435 16328141 := bstep (se 3 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 16328141 = 6123053) B6123053
theorem B10885427 : Blo 2149435 10885427 := bstep (se 1 (by rfl) ⟨8164070, by rfl⟩ : syracuseStep 10885427 = 16328141) B16328141
theorem B7256951 : Blo 2149435 7256951 := bstep (se 1 (by rfl) ⟨5442713, by rfl⟩ : syracuseStep 7256951 = 10885427) B10885427
theorem B4837967 : Blo 2149435 4837967 := bstep (se 1 (by rfl) ⟨3628475, by rfl⟩ : syracuseStep 4837967 = 7256951) B7256951
theorem B3225311 : Blo 2149435 3225311 := bstep (se 1 (by rfl) ⟨2418983, by rfl⟩ : syracuseStep 3225311 = 4837967) B4837967
theorem B2150207 : Blo 2149435 2150207 := bstep (se 1 (by rfl) ⟨1612655, by rfl⟩ : syracuseStep 2150207 = 3225311) B3225311
theorem B3225317 : Blo 2149435 3225317 := bbase (se 4 (by rfl) ⟨302373, by rfl⟩ : syracuseStep 3225317 = 604747) (by norm_num)
theorem B2150211 : Blo 2149435 2150211 := bstep (se 1 (by rfl) ⟨1612658, by rfl⟩ : syracuseStep 2150211 = 3225317) B3225317
theorem B6123077 : Blo 2149435 6123077 := bbase (se 4 (by rfl) ⟨574038, by rfl⟩ : syracuseStep 6123077 = 1148077) (by norm_num)
theorem B4082051 : Blo 2149435 4082051 := bstep (se 1 (by rfl) ⟨3061538, by rfl⟩ : syracuseStep 4082051 = 6123077) B6123077
theorem B2721367 : Blo 2149435 2721367 := bstep (se 1 (by rfl) ⟨2041025, by rfl⟩ : syracuseStep 2721367 = 4082051) B4082051
theorem B3628489 : Blo 2149435 3628489 := bstep (se 2 (by rfl) ⟨1360683, by rfl⟩ : syracuseStep 3628489 = 2721367) B2721367
theorem B4837985 : Blo 2149435 4837985 := bstep (se 2 (by rfl) ⟨1814244, by rfl⟩ : syracuseStep 4837985 = 3628489) B3628489
theorem B3225323 : Blo 2149435 3225323 := bstep (se 1 (by rfl) ⟨2418992, by rfl⟩ : syracuseStep 3225323 = 4837985) B4837985
theorem B2150215 : Blo 2149435 2150215 := bstep (se 1 (by rfl) ⟨1612661, by rfl⟩ : syracuseStep 2150215 = 3225323) B3225323
theorem B2418997 : Blo 2149435 2418997 := bbase (se 5 (by rfl) ⟨113390, by rfl⟩ : syracuseStep 2418997 = 226781) (by norm_num)
theorem B3225329 : Blo 2149435 3225329 := bstep (se 2 (by rfl) ⟨1209498, by rfl⟩ : syracuseStep 3225329 = 2418997) B2418997
theorem B2150219 : Blo 2149435 2150219 := bstep (se 1 (by rfl) ⟨1612664, by rfl⟩ : syracuseStep 2150219 = 3225329) B3225329
theorem B2721377 : Blo 2149435 2721377 := bbase (se 2 (by rfl) ⟨1020516, by rfl⟩ : syracuseStep 2721377 = 2041033) (by norm_num)
theorem B7257005 : Blo 2149435 7257005 := bstep (se 3 (by rfl) ⟨1360688, by rfl⟩ : syracuseStep 7257005 = 2721377) B2721377
theorem B4838003 : Blo 2149435 4838003 := bstep (se 1 (by rfl) ⟨3628502, by rfl⟩ : syracuseStep 4838003 = 7257005) B7257005
theorem B3225335 : Blo 2149435 3225335 := bstep (se 1 (by rfl) ⟨2419001, by rfl⟩ : syracuseStep 3225335 = 4838003) B4838003
theorem B2150223 : Blo 2149435 2150223 := bstep (se 1 (by rfl) ⟨1612667, by rfl⟩ : syracuseStep 2150223 = 3225335) B3225335
theorem B3225341 : Blo 2149435 3225341 := bbase (se 3 (by rfl) ⟨604751, by rfl⟩ : syracuseStep 3225341 = 1209503) (by norm_num)
theorem B2150227 : Blo 2149435 2150227 := bstep (se 1 (by rfl) ⟨1612670, by rfl⟩ : syracuseStep 2150227 = 3225341) B3225341
theorem B4838021 : Blo 2149435 4838021 := bbase (se 4 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 4838021 = 907129) (by norm_num)
theorem B3225347 : Blo 2149435 3225347 := bstep (se 1 (by rfl) ⟨2419010, by rfl⟩ : syracuseStep 3225347 = 4838021) B4838021
theorem B2150231 : Blo 2149435 2150231 := bstep (se 1 (by rfl) ⟨1612673, by rfl⟩ : syracuseStep 2150231 = 3225347) B3225347
theorem B8718293 : Blo 2149435 8718293 := bbase (se 7 (by rfl) ⟨102167, by rfl⟩ : syracuseStep 8718293 = 204335) (by norm_num)
theorem B23248781 : Blo 2149435 23248781 := bstep (se 3 (by rfl) ⟨4359146, by rfl⟩ : syracuseStep 23248781 = 8718293) B8718293
theorem B15499187 : Blo 2149435 15499187 := bstep (se 1 (by rfl) ⟨11624390, by rfl⟩ : syracuseStep 15499187 = 23248781) B23248781
theorem B10332791 : Blo 2149435 10332791 := bstep (se 1 (by rfl) ⟨7749593, by rfl⟩ : syracuseStep 10332791 = 15499187) B15499187
theorem B6888527 : Blo 2149435 6888527 := bstep (se 1 (by rfl) ⟨5166395, by rfl⟩ : syracuseStep 6888527 = 10332791) B10332791
theorem B4592351 : Blo 2149435 4592351 := bstep (se 1 (by rfl) ⟨3444263, by rfl⟩ : syracuseStep 4592351 = 6888527) B6888527
theorem B3061567 : Blo 2149435 3061567 := bstep (se 1 (by rfl) ⟨2296175, by rfl⟩ : syracuseStep 3061567 = 4592351) B4592351
theorem B4082089 : Blo 2149435 4082089 := bstep (se 2 (by rfl) ⟨1530783, by rfl⟩ : syracuseStep 4082089 = 3061567) B3061567
theorem B5442785 : Blo 2149435 5442785 := bstep (se 2 (by rfl) ⟨2041044, by rfl⟩ : syracuseStep 5442785 = 4082089) B4082089
theorem B3628523 : Blo 2149435 3628523 := bstep (se 1 (by rfl) ⟨2721392, by rfl⟩ : syracuseStep 3628523 = 5442785) B5442785
theorem B2419015 : Blo 2149435 2419015 := bstep (se 1 (by rfl) ⟨1814261, by rfl⟩ : syracuseStep 2419015 = 3628523) B3628523
theorem B3225353 : Blo 2149435 3225353 := bstep (se 2 (by rfl) ⟨1209507, by rfl⟩ : syracuseStep 3225353 = 2419015) B2419015
theorem B2150235 : Blo 2149435 2150235 := bstep (se 1 (by rfl) ⟨1612676, by rfl⟩ : syracuseStep 2150235 = 3225353) B3225353
theorem B10885589 : Blo 2149435 10885589 := bbase (se 7 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 10885589 = 255131) (by norm_num)
theorem B7257059 : Blo 2149435 7257059 := bstep (se 1 (by rfl) ⟨5442794, by rfl⟩ : syracuseStep 7257059 = 10885589) B10885589
theorem B4838039 : Blo 2149435 4838039 := bstep (se 1 (by rfl) ⟨3628529, by rfl⟩ : syracuseStep 4838039 = 7257059) B7257059
theorem B3225359 : Blo 2149435 3225359 := bstep (se 1 (by rfl) ⟨2419019, by rfl⟩ : syracuseStep 3225359 = 4838039) B4838039
theorem B2150239 : Blo 2149435 2150239 := bstep (se 1 (by rfl) ⟨1612679, by rfl⟩ : syracuseStep 2150239 = 3225359) B3225359
theorem B3225365 : Blo 2149435 3225365 := bbase (se 6 (by rfl) ⟨75594, by rfl⟩ : syracuseStep 3225365 = 151189) (by norm_num)
theorem B2150243 : Blo 2149435 2150243 := bstep (se 1 (by rfl) ⟨1612682, by rfl⟩ : syracuseStep 2150243 = 3225365) B3225365
theorem B2758537 : Blo 2149435 2758537 := bbase (se 2 (by rfl) ⟨1034451, by rfl⟩ : syracuseStep 2758537 = 2068903) (by norm_num)
theorem B14712197 : Blo 2149435 14712197 := bstep (se 4 (by rfl) ⟨1379268, by rfl⟩ : syracuseStep 14712197 = 2758537) B2758537
theorem B39232525 : Blo 2149435 39232525 := bstep (se 3 (by rfl) ⟨7356098, by rfl⟩ : syracuseStep 39232525 = 14712197) B14712197
theorem B52310033 : Blo 2149435 52310033 := bstep (se 2 (by rfl) ⟨19616262, by rfl⟩ : syracuseStep 52310033 = 39232525) B39232525
theorem B34873355 : Blo 2149435 34873355 := bstep (se 1 (by rfl) ⟨26155016, by rfl⟩ : syracuseStep 34873355 = 52310033) B52310033
theorem B92995613 : Blo 2149435 92995613 := bstep (se 3 (by rfl) ⟨17436677, by rfl⟩ : syracuseStep 92995613 = 34873355) B34873355
theorem B61997075 : Blo 2149435 61997075 := bstep (se 1 (by rfl) ⟨46497806, by rfl⟩ : syracuseStep 61997075 = 92995613) B92995613
theorem B41331383 : Blo 2149435 41331383 := bstep (se 1 (by rfl) ⟨30998537, by rfl⟩ : syracuseStep 41331383 = 61997075) B61997075
theorem B27554255 : Blo 2149435 27554255 := bstep (se 1 (by rfl) ⟨20665691, by rfl⟩ : syracuseStep 27554255 = 41331383) B41331383
theorem B18369503 : Blo 2149435 18369503 := bstep (se 1 (by rfl) ⟨13777127, by rfl⟩ : syracuseStep 18369503 = 27554255) B27554255
theorem B12246335 : Blo 2149435 12246335 := bstep (se 1 (by rfl) ⟨9184751, by rfl⟩ : syracuseStep 12246335 = 18369503) B18369503
theorem B8164223 : Blo 2149435 8164223 := bstep (se 1 (by rfl) ⟨6123167, by rfl⟩ : syracuseStep 8164223 = 12246335) B12246335
theorem B5442815 : Blo 2149435 5442815 := bstep (se 1 (by rfl) ⟨4082111, by rfl⟩ : syracuseStep 5442815 = 8164223) B8164223
theorem B3628543 : Blo 2149435 3628543 := bstep (se 1 (by rfl) ⟨2721407, by rfl⟩ : syracuseStep 3628543 = 5442815) B5442815
theorem B4838057 : Blo 2149435 4838057 := bstep (se 2 (by rfl) ⟨1814271, by rfl⟩ : syracuseStep 4838057 = 3628543) B3628543
theorem B3225371 : Blo 2149435 3225371 := bstep (se 1 (by rfl) ⟨2419028, by rfl⟩ : syracuseStep 3225371 = 4838057) B4838057
theorem B2150247 : Blo 2149435 2150247 := bstep (se 1 (by rfl) ⟨1612685, by rfl⟩ : syracuseStep 2150247 = 3225371) B3225371
theorem B2419033 : Blo 2149435 2419033 := bbase (se 2 (by rfl) ⟨907137, by rfl⟩ : syracuseStep 2419033 = 1814275) (by norm_num)
theorem B3225377 : Blo 2149435 3225377 := bstep (se 2 (by rfl) ⟨1209516, by rfl⟩ : syracuseStep 3225377 = 2419033) B2419033
theorem B2150251 : Blo 2149435 2150251 := bstep (se 1 (by rfl) ⟨1612688, by rfl⟩ : syracuseStep 2150251 = 3225377) B3225377
theorem B2758549 : Blo 2149435 2758549 := bbase (se 6 (by rfl) ⟨64653, by rfl⟩ : syracuseStep 2758549 = 129307) (by norm_num)
theorem B3678065 : Blo 2149435 3678065 := bstep (se 2 (by rfl) ⟨1379274, by rfl⟩ : syracuseStep 3678065 = 2758549) B2758549
theorem B2452043 : Blo 2149435 2452043 := bstep (se 1 (by rfl) ⟨1839032, by rfl⟩ : syracuseStep 2452043 = 3678065) B3678065
theorem B6538781 : Blo 2149435 6538781 := bstep (se 3 (by rfl) ⟨1226021, by rfl⟩ : syracuseStep 6538781 = 2452043) B2452043
theorem B4359187 : Blo 2149435 4359187 := bstep (se 1 (by rfl) ⟨3269390, by rfl⟩ : syracuseStep 4359187 = 6538781) B6538781
theorem B5812249 : Blo 2149435 5812249 := bstep (se 2 (by rfl) ⟨2179593, by rfl⟩ : syracuseStep 5812249 = 4359187) B4359187
theorem B7749665 : Blo 2149435 7749665 := bstep (se 2 (by rfl) ⟨2906124, by rfl⟩ : syracuseStep 7749665 = 5812249) B5812249
theorem B5166443 : Blo 2149435 5166443 := bstep (se 1 (by rfl) ⟨3874832, by rfl⟩ : syracuseStep 5166443 = 7749665) B7749665
theorem B3444295 : Blo 2149435 3444295 := bstep (se 1 (by rfl) ⟨2583221, by rfl⟩ : syracuseStep 3444295 = 5166443) B5166443
theorem B4592393 : Blo 2149435 4592393 := bstep (se 2 (by rfl) ⟨1722147, by rfl⟩ : syracuseStep 4592393 = 3444295) B3444295
theorem B3061595 : Blo 2149435 3061595 := bstep (se 1 (by rfl) ⟨2296196, by rfl⟩ : syracuseStep 3061595 = 4592393) B4592393
theorem B8164253 : Blo 2149435 8164253 := bstep (se 3 (by rfl) ⟨1530797, by rfl⟩ : syracuseStep 8164253 = 3061595) B3061595
theorem B5442835 : Blo 2149435 5442835 := bstep (se 1 (by rfl) ⟨4082126, by rfl⟩ : syracuseStep 5442835 = 8164253) B8164253
theorem B7257113 : Blo 2149435 7257113 := bstep (se 2 (by rfl) ⟨2721417, by rfl⟩ : syracuseStep 7257113 = 5442835) B5442835
theorem B4838075 : Blo 2149435 4838075 := bstep (se 1 (by rfl) ⟨3628556, by rfl⟩ : syracuseStep 4838075 = 7257113) B7257113
theorem B3225383 : Blo 2149435 3225383 := bstep (se 1 (by rfl) ⟨2419037, by rfl⟩ : syracuseStep 3225383 = 4838075) B4838075
theorem B2150255 : Blo 2149435 2150255 := bstep (se 1 (by rfl) ⟨1612691, by rfl⟩ : syracuseStep 2150255 = 3225383) B3225383
theorem B3225389 : Blo 2149435 3225389 := bbase (se 3 (by rfl) ⟨604760, by rfl⟩ : syracuseStep 3225389 = 1209521) (by norm_num)
theorem B2150259 : Blo 2149435 2150259 := bstep (se 1 (by rfl) ⟨1612694, by rfl⟩ : syracuseStep 2150259 = 3225389) B3225389
theorem B4838093 : Blo 2149435 4838093 := bbase (se 3 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 4838093 = 1814285) (by norm_num)
theorem B3225395 : Blo 2149435 3225395 := bstep (se 1 (by rfl) ⟨2419046, by rfl⟩ : syracuseStep 3225395 = 4838093) B4838093
theorem B2150263 : Blo 2149435 2150263 := bstep (se 1 (by rfl) ⟨1612697, by rfl⟩ : syracuseStep 2150263 = 3225395) B3225395
theorem B2721433 : Blo 2149435 2721433 := bbase (se 2 (by rfl) ⟨1020537, by rfl⟩ : syracuseStep 2721433 = 2041075) (by norm_num)
theorem B3628577 : Blo 2149435 3628577 := bstep (se 2 (by rfl) ⟨1360716, by rfl⟩ : syracuseStep 3628577 = 2721433) B2721433
theorem B2419051 : Blo 2149435 2419051 := bstep (se 1 (by rfl) ⟨1814288, by rfl⟩ : syracuseStep 2419051 = 3628577) B3628577
theorem B3225401 : Blo 2149435 3225401 := bstep (se 2 (by rfl) ⟨1209525, by rfl⟩ : syracuseStep 3225401 = 2419051) B2419051
theorem B2150267 : Blo 2149435 2150267 := bstep (se 1 (by rfl) ⟨1612700, by rfl⟩ : syracuseStep 2150267 = 3225401) B3225401
theorem B9184853 : Blo 2149435 9184853 := bbase (se 8 (by rfl) ⟨53817, by rfl⟩ : syracuseStep 9184853 = 107635) (by norm_num)
theorem B24492941 : Blo 2149435 24492941 := bstep (se 3 (by rfl) ⟨4592426, by rfl⟩ : syracuseStep 24492941 = 9184853) B9184853
theorem B16328627 : Blo 2149435 16328627 := bstep (se 1 (by rfl) ⟨12246470, by rfl⟩ : syracuseStep 16328627 = 24492941) B24492941
theorem B10885751 : Blo 2149435 10885751 := bstep (se 1 (by rfl) ⟨8164313, by rfl⟩ : syracuseStep 10885751 = 16328627) B16328627
theorem B7257167 : Blo 2149435 7257167 := bstep (se 1 (by rfl) ⟨5442875, by rfl⟩ : syracuseStep 7257167 = 10885751) B10885751
theorem B4838111 : Blo 2149435 4838111 := bstep (se 1 (by rfl) ⟨3628583, by rfl⟩ : syracuseStep 4838111 = 7257167) B7257167
theorem B3225407 : Blo 2149435 3225407 := bstep (se 1 (by rfl) ⟨2419055, by rfl⟩ : syracuseStep 3225407 = 4838111) B4838111
theorem B2150271 : Blo 2149435 2150271 := bstep (se 1 (by rfl) ⟨1612703, by rfl⟩ : syracuseStep 2150271 = 3225407) B3225407
theorem B3225413 : Blo 2149435 3225413 := bbase (se 4 (by rfl) ⟨302382, by rfl⟩ : syracuseStep 3225413 = 604765) (by norm_num)
theorem B2150275 : Blo 2149435 2150275 := bstep (se 1 (by rfl) ⟨1612706, by rfl⟩ : syracuseStep 2150275 = 3225413) B3225413
theorem B3628597 : Blo 2149435 3628597 := bbase (se 5 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 3628597 = 340181) (by norm_num)
theorem B4838129 : Blo 2149435 4838129 := bstep (se 2 (by rfl) ⟨1814298, by rfl⟩ : syracuseStep 4838129 = 3628597) B3628597
theorem B3225419 : Blo 2149435 3225419 := bstep (se 1 (by rfl) ⟨2419064, by rfl⟩ : syracuseStep 3225419 = 4838129) B4838129
theorem B2150279 : Blo 2149435 2150279 := bstep (se 1 (by rfl) ⟨1612709, by rfl⟩ : syracuseStep 2150279 = 3225419) B3225419
theorem B2419069 : Blo 2149435 2419069 := bbase (se 3 (by rfl) ⟨453575, by rfl⟩ : syracuseStep 2419069 = 907151) (by norm_num)
theorem B3225425 : Blo 2149435 3225425 := bstep (se 2 (by rfl) ⟨1209534, by rfl⟩ : syracuseStep 3225425 = 2419069) B2419069
theorem B2150283 : Blo 2149435 2150283 := bstep (se 1 (by rfl) ⟨1612712, by rfl⟩ : syracuseStep 2150283 = 3225425) B3225425
theorem B7257221 : Blo 2149435 7257221 := bbase (se 4 (by rfl) ⟨680364, by rfl⟩ : syracuseStep 7257221 = 1360729) (by norm_num)
theorem B4838147 : Blo 2149435 4838147 := bstep (se 1 (by rfl) ⟨3628610, by rfl⟩ : syracuseStep 4838147 = 7257221) B7257221
theorem B3225431 : Blo 2149435 3225431 := bstep (se 1 (by rfl) ⟨2419073, by rfl⟩ : syracuseStep 3225431 = 4838147) B4838147
theorem B2150287 : Blo 2149435 2150287 := bstep (se 1 (by rfl) ⟨1612715, by rfl⟩ : syracuseStep 2150287 = 3225431) B3225431
theorem B3225437 : Blo 2149435 3225437 := bbase (se 3 (by rfl) ⟨604769, by rfl⟩ : syracuseStep 3225437 = 1209539) (by norm_num)
theorem B2150291 : Blo 2149435 2150291 := bstep (se 1 (by rfl) ⟨1612718, by rfl⟩ : syracuseStep 2150291 = 3225437) B3225437
theorem B4838165 : Blo 2149435 4838165 := bbase (se 6 (by rfl) ⟨113394, by rfl⟩ : syracuseStep 4838165 = 226789) (by norm_num)
theorem B3225443 : Blo 2149435 3225443 := bstep (se 1 (by rfl) ⟨2419082, by rfl⟩ : syracuseStep 3225443 = 4838165) B4838165
theorem B2150295 : Blo 2149435 2150295 := bstep (se 1 (by rfl) ⟨1612721, by rfl⟩ : syracuseStep 2150295 = 3225443) B3225443
theorem B8164421 : Blo 2149435 8164421 := bbase (se 4 (by rfl) ⟨765414, by rfl⟩ : syracuseStep 8164421 = 1530829) (by norm_num)
theorem B5442947 : Blo 2149435 5442947 := bstep (se 1 (by rfl) ⟨4082210, by rfl⟩ : syracuseStep 5442947 = 8164421) B8164421
theorem B3628631 : Blo 2149435 3628631 := bstep (se 1 (by rfl) ⟨2721473, by rfl⟩ : syracuseStep 3628631 = 5442947) B5442947
theorem B2419087 : Blo 2149435 2419087 := bstep (se 1 (by rfl) ⟨1814315, by rfl⟩ : syracuseStep 2419087 = 3628631) B3628631
theorem B3225449 : Blo 2149435 3225449 := bstep (se 2 (by rfl) ⟨1209543, by rfl⟩ : syracuseStep 3225449 = 2419087) B2419087
theorem B2150299 : Blo 2149435 2150299 := bstep (se 1 (by rfl) ⟨1612724, by rfl⟩ : syracuseStep 2150299 = 3225449) B3225449
theorem B2452097 : Blo 2149435 2452097 := bbase (se 2 (by rfl) ⟨919536, by rfl⟩ : syracuseStep 2452097 = 1839073) (by norm_num)
theorem B6538925 : Blo 2149435 6538925 := bstep (se 3 (by rfl) ⟨1226048, by rfl⟩ : syracuseStep 6538925 = 2452097) B2452097
theorem B17437133 : Blo 2149435 17437133 := bstep (se 3 (by rfl) ⟨3269462, by rfl⟩ : syracuseStep 17437133 = 6538925) B6538925
theorem B11624755 : Blo 2149435 11624755 := bstep (se 1 (by rfl) ⟨8718566, by rfl⟩ : syracuseStep 11624755 = 17437133) B17437133
theorem B15499673 : Blo 2149435 15499673 := bstep (se 2 (by rfl) ⟨5812377, by rfl⟩ : syracuseStep 15499673 = 11624755) B11624755
theorem B10333115 : Blo 2149435 10333115 := bstep (se 1 (by rfl) ⟨7749836, by rfl⟩ : syracuseStep 10333115 = 15499673) B15499673
theorem B6888743 : Blo 2149435 6888743 := bstep (se 1 (by rfl) ⟨5166557, by rfl⟩ : syracuseStep 6888743 = 10333115) B10333115
theorem B4592495 : Blo 2149435 4592495 := bstep (se 1 (by rfl) ⟨3444371, by rfl⟩ : syracuseStep 4592495 = 6888743) B6888743
theorem B12246653 : Blo 2149435 12246653 := bstep (se 3 (by rfl) ⟨2296247, by rfl⟩ : syracuseStep 12246653 = 4592495) B4592495
theorem B8164435 : Blo 2149435 8164435 := bstep (se 1 (by rfl) ⟨6123326, by rfl⟩ : syracuseStep 8164435 = 12246653) B12246653
theorem B10885913 : Blo 2149435 10885913 := bstep (se 2 (by rfl) ⟨4082217, by rfl⟩ : syracuseStep 10885913 = 8164435) B8164435
theorem B7257275 : Blo 2149435 7257275 := bstep (se 1 (by rfl) ⟨5442956, by rfl⟩ : syracuseStep 7257275 = 10885913) B10885913
theorem B4838183 : Blo 2149435 4838183 := bstep (se 1 (by rfl) ⟨3628637, by rfl⟩ : syracuseStep 4838183 = 7257275) B7257275
theorem B3225455 : Blo 2149435 3225455 := bstep (se 1 (by rfl) ⟨2419091, by rfl⟩ : syracuseStep 3225455 = 4838183) B4838183
theorem B2150303 : Blo 2149435 2150303 := bstep (se 1 (by rfl) ⟨1612727, by rfl⟩ : syracuseStep 2150303 = 3225455) B3225455
theorem B3225461 : Blo 2149435 3225461 := bbase (se 5 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 3225461 = 302387) (by norm_num)
theorem B2150307 : Blo 2149435 2150307 := bstep (se 1 (by rfl) ⟨1612730, by rfl⟩ : syracuseStep 2150307 = 3225461) B3225461
theorem B2583289 : Blo 2149435 2583289 := bbase (se 2 (by rfl) ⟨968733, by rfl⟩ : syracuseStep 2583289 = 1937467) (by norm_num)
theorem B3444385 : Blo 2149435 3444385 := bstep (se 2 (by rfl) ⟨1291644, by rfl⟩ : syracuseStep 3444385 = 2583289) B2583289
theorem B4592513 : Blo 2149435 4592513 := bstep (se 2 (by rfl) ⟨1722192, by rfl⟩ : syracuseStep 4592513 = 3444385) B3444385
theorem B3061675 : Blo 2149435 3061675 := bstep (se 1 (by rfl) ⟨2296256, by rfl⟩ : syracuseStep 3061675 = 4592513) B4592513
theorem B4082233 : Blo 2149435 4082233 := bstep (se 2 (by rfl) ⟨1530837, by rfl⟩ : syracuseStep 4082233 = 3061675) B3061675
theorem B5442977 : Blo 2149435 5442977 := bstep (se 2 (by rfl) ⟨2041116, by rfl⟩ : syracuseStep 5442977 = 4082233) B4082233
theorem B3628651 : Blo 2149435 3628651 := bstep (se 1 (by rfl) ⟨2721488, by rfl⟩ : syracuseStep 3628651 = 5442977) B5442977
theorem B4838201 : Blo 2149435 4838201 := bstep (se 2 (by rfl) ⟨1814325, by rfl⟩ : syracuseStep 4838201 = 3628651) B3628651
theorem B3225467 : Blo 2149435 3225467 := bstep (se 1 (by rfl) ⟨2419100, by rfl⟩ : syracuseStep 3225467 = 4838201) B4838201
theorem B2150311 : Blo 2149435 2150311 := bstep (se 1 (by rfl) ⟨1612733, by rfl⟩ : syracuseStep 2150311 = 3225467) B3225467
theorem B2419105 : Blo 2149435 2419105 := bbase (se 2 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 2419105 = 1814329) (by norm_num)
theorem B3225473 : Blo 2149435 3225473 := bstep (se 2 (by rfl) ⟨1209552, by rfl⟩ : syracuseStep 3225473 = 2419105) B2419105
theorem B2150315 : Blo 2149435 2150315 := bstep (se 1 (by rfl) ⟨1612736, by rfl⟩ : syracuseStep 2150315 = 3225473) B3225473
theorem B5442997 : Blo 2149435 5442997 := bbase (se 5 (by rfl) ⟨255140, by rfl⟩ : syracuseStep 5442997 = 510281) (by norm_num)
theorem B7257329 : Blo 2149435 7257329 := bstep (se 2 (by rfl) ⟨2721498, by rfl⟩ : syracuseStep 7257329 = 5442997) B5442997
theorem B4838219 : Blo 2149435 4838219 := bstep (se 1 (by rfl) ⟨3628664, by rfl⟩ : syracuseStep 4838219 = 7257329) B7257329
theorem B3225479 : Blo 2149435 3225479 := bstep (se 1 (by rfl) ⟨2419109, by rfl⟩ : syracuseStep 3225479 = 4838219) B4838219
theorem B2150319 : Blo 2149435 2150319 := bstep (se 1 (by rfl) ⟨1612739, by rfl⟩ : syracuseStep 2150319 = 3225479) B3225479
theorem B3225485 : Blo 2149435 3225485 := bbase (se 3 (by rfl) ⟨604778, by rfl⟩ : syracuseStep 3225485 = 1209557) (by norm_num)
theorem B2150323 : Blo 2149435 2150323 := bstep (se 1 (by rfl) ⟨1612742, by rfl⟩ : syracuseStep 2150323 = 3225485) B3225485
theorem B4838237 : Blo 2149435 4838237 := bbase (se 3 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 4838237 = 1814339) (by norm_num)
theorem B3225491 : Blo 2149435 3225491 := bstep (se 1 (by rfl) ⟨2419118, by rfl⟩ : syracuseStep 3225491 = 4838237) B4838237
theorem B2150327 : Blo 2149435 2150327 := bstep (se 1 (by rfl) ⟨1612745, by rfl⟩ : syracuseStep 2150327 = 3225491) B3225491
theorem B3628685 : Blo 2149435 3628685 := bbase (se 3 (by rfl) ⟨680378, by rfl⟩ : syracuseStep 3628685 = 1360757) (by norm_num)
theorem B2419123 : Blo 2149435 2419123 := bstep (se 1 (by rfl) ⟨1814342, by rfl⟩ : syracuseStep 2419123 = 3628685) B3628685
theorem B3225497 : Blo 2149435 3225497 := bstep (se 2 (by rfl) ⟨1209561, by rfl⟩ : syracuseStep 3225497 = 2419123) B2419123
theorem B2150331 : Blo 2149435 2150331 := bstep (se 1 (by rfl) ⟨1612748, by rfl⟩ : syracuseStep 2150331 = 3225497) B3225497
theorem B2583317 : Blo 2149435 2583317 := bbase (se 6 (by rfl) ⟨60546, by rfl⟩ : syracuseStep 2583317 = 121093) (by norm_num)
theorem B6888845 : Blo 2149435 6888845 := bstep (se 3 (by rfl) ⟨1291658, by rfl⟩ : syracuseStep 6888845 = 2583317) B2583317
theorem B18370253 : Blo 2149435 18370253 := bstep (se 3 (by rfl) ⟨3444422, by rfl⟩ : syracuseStep 18370253 = 6888845) B6888845
theorem B12246835 : Blo 2149435 12246835 := bstep (se 1 (by rfl) ⟨9185126, by rfl⟩ : syracuseStep 12246835 = 18370253) B18370253
theorem B16329113 : Blo 2149435 16329113 := bstep (se 2 (by rfl) ⟨6123417, by rfl⟩ : syracuseStep 16329113 = 12246835) B12246835
theorem B10886075 : Blo 2149435 10886075 := bstep (se 1 (by rfl) ⟨8164556, by rfl⟩ : syracuseStep 10886075 = 16329113) B16329113
theorem B7257383 : Blo 2149435 7257383 := bstep (se 1 (by rfl) ⟨5443037, by rfl⟩ : syracuseStep 7257383 = 10886075) B10886075
theorem B4838255 : Blo 2149435 4838255 := bstep (se 1 (by rfl) ⟨3628691, by rfl⟩ : syracuseStep 4838255 = 7257383) B7257383
theorem B3225503 : Blo 2149435 3225503 := bstep (se 1 (by rfl) ⟨2419127, by rfl⟩ : syracuseStep 3225503 = 4838255) B4838255
theorem B2150335 : Blo 2149435 2150335 := bstep (se 1 (by rfl) ⟨1612751, by rfl⟩ : syracuseStep 2150335 = 3225503) B3225503
theorem B3225509 : Blo 2149435 3225509 := bbase (se 4 (by rfl) ⟨302391, by rfl⟩ : syracuseStep 3225509 = 604783) (by norm_num)
theorem B2150339 : Blo 2149435 2150339 := bstep (se 1 (by rfl) ⟨1612754, by rfl⟩ : syracuseStep 2150339 = 3225509) B3225509
theorem B2721529 : Blo 2149435 2721529 := bbase (se 2 (by rfl) ⟨1020573, by rfl⟩ : syracuseStep 2721529 = 2041147) (by norm_num)
theorem B3628705 : Blo 2149435 3628705 := bstep (se 2 (by rfl) ⟨1360764, by rfl⟩ : syracuseStep 3628705 = 2721529) B2721529
theorem B4838273 : Blo 2149435 4838273 := bstep (se 2 (by rfl) ⟨1814352, by rfl⟩ : syracuseStep 4838273 = 3628705) B3628705
theorem B3225515 : Blo 2149435 3225515 := bstep (se 1 (by rfl) ⟨2419136, by rfl⟩ : syracuseStep 3225515 = 4838273) B4838273
theorem B2150343 : Blo 2149435 2150343 := bstep (se 1 (by rfl) ⟨1612757, by rfl⟩ : syracuseStep 2150343 = 3225515) B3225515
theorem B2419141 : Blo 2149435 2419141 := bbase (se 4 (by rfl) ⟨226794, by rfl⟩ : syracuseStep 2419141 = 453589) (by norm_num)
theorem B3225521 : Blo 2149435 3225521 := bstep (se 2 (by rfl) ⟨1209570, by rfl⟩ : syracuseStep 3225521 = 2419141) B2419141
theorem B2150347 : Blo 2149435 2150347 := bstep (se 1 (by rfl) ⟨1612760, by rfl⟩ : syracuseStep 2150347 = 3225521) B3225521
theorem B4082309 : Blo 2149435 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B2721539 : Blo 2149435 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B7257437 : Blo 2149435 7257437 := bstep (se 3 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 7257437 = 2721539) B2721539
theorem B4838291 : Blo 2149435 4838291 := bstep (se 1 (by rfl) ⟨3628718, by rfl⟩ : syracuseStep 4838291 = 7257437) B7257437
theorem B3225527 : Blo 2149435 3225527 := bstep (se 1 (by rfl) ⟨2419145, by rfl⟩ : syracuseStep 3225527 = 4838291) B4838291
theorem B2150351 : Blo 2149435 2150351 := bstep (se 1 (by rfl) ⟨1612763, by rfl⟩ : syracuseStep 2150351 = 3225527) B3225527
theorem B3225533 : Blo 2149435 3225533 := bbase (se 3 (by rfl) ⟨604787, by rfl⟩ : syracuseStep 3225533 = 1209575) (by norm_num)
theorem B2150355 : Blo 2149435 2150355 := bstep (se 1 (by rfl) ⟨1612766, by rfl⟩ : syracuseStep 2150355 = 3225533) B3225533
theorem B4838309 : Blo 2149435 4838309 := bbase (se 4 (by rfl) ⟨453591, by rfl⟩ : syracuseStep 4838309 = 907183) (by norm_num)
theorem B3225539 : Blo 2149435 3225539 := bstep (se 1 (by rfl) ⟨2419154, by rfl⟩ : syracuseStep 3225539 = 4838309) B4838309
theorem B2150359 : Blo 2149435 2150359 := bstep (se 1 (by rfl) ⟨1612769, by rfl⟩ : syracuseStep 2150359 = 3225539) B3225539
theorem B5443109 : Blo 2149435 5443109 := bbase (se 4 (by rfl) ⟨510291, by rfl⟩ : syracuseStep 5443109 = 1020583) (by norm_num)
theorem B3628739 : Blo 2149435 3628739 := bstep (se 1 (by rfl) ⟨2721554, by rfl⟩ : syracuseStep 3628739 = 5443109) B5443109
theorem B2419159 : Blo 2149435 2419159 := bstep (se 1 (by rfl) ⟨1814369, by rfl⟩ : syracuseStep 2419159 = 3628739) B3628739
theorem B3225545 : Blo 2149435 3225545 := bstep (se 2 (by rfl) ⟨1209579, by rfl⟩ : syracuseStep 3225545 = 2419159) B2419159
theorem B2150363 : Blo 2149435 2150363 := bstep (se 1 (by rfl) ⟨1612772, by rfl⟩ : syracuseStep 2150363 = 3225545) B3225545
theorem B6123509 : Blo 2149435 6123509 := bbase (se 5 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 6123509 = 574079) (by norm_num)
theorem B4082339 : Blo 2149435 4082339 := bstep (se 1 (by rfl) ⟨3061754, by rfl⟩ : syracuseStep 4082339 = 6123509) B6123509
theorem B10886237 : Blo 2149435 10886237 := bstep (se 3 (by rfl) ⟨2041169, by rfl⟩ : syracuseStep 10886237 = 4082339) B4082339
theorem B7257491 : Blo 2149435 7257491 := bstep (se 1 (by rfl) ⟨5443118, by rfl⟩ : syracuseStep 7257491 = 10886237) B10886237
theorem B4838327 : Blo 2149435 4838327 := bstep (se 1 (by rfl) ⟨3628745, by rfl⟩ : syracuseStep 4838327 = 7257491) B7257491
theorem B3225551 : Blo 2149435 3225551 := bstep (se 1 (by rfl) ⟨2419163, by rfl⟩ : syracuseStep 3225551 = 4838327) B4838327
theorem B2150367 : Blo 2149435 2150367 := bstep (se 1 (by rfl) ⟨1612775, by rfl⟩ : syracuseStep 2150367 = 3225551) B3225551
theorem B3225557 : Blo 2149435 3225557 := bbase (se 7 (by rfl) ⟨37799, by rfl⟩ : syracuseStep 3225557 = 75599) (by norm_num)
theorem B2150371 : Blo 2149435 2150371 := bstep (se 1 (by rfl) ⟨1612778, by rfl⟩ : syracuseStep 2150371 = 3225557) B3225557
theorem B8164709 : Blo 2149435 8164709 := bbase (se 4 (by rfl) ⟨765441, by rfl⟩ : syracuseStep 8164709 = 1530883) (by norm_num)
theorem B5443139 : Blo 2149435 5443139 := bstep (se 1 (by rfl) ⟨4082354, by rfl⟩ : syracuseStep 5443139 = 8164709) B8164709
theorem B3628759 : Blo 2149435 3628759 := bstep (se 1 (by rfl) ⟨2721569, by rfl⟩ : syracuseStep 3628759 = 5443139) B5443139
theorem B4838345 : Blo 2149435 4838345 := bstep (se 2 (by rfl) ⟨1814379, by rfl⟩ : syracuseStep 4838345 = 3628759) B3628759
theorem B3225563 : Blo 2149435 3225563 := bstep (se 1 (by rfl) ⟨2419172, by rfl⟩ : syracuseStep 3225563 = 4838345) B4838345
theorem B2150375 : Blo 2149435 2150375 := bstep (se 1 (by rfl) ⟨1612781, by rfl⟩ : syracuseStep 2150375 = 3225563) B3225563
theorem B2419177 : Blo 2149435 2419177 := bbase (se 2 (by rfl) ⟨907191, by rfl⟩ : syracuseStep 2419177 = 1814383) (by norm_num)
theorem B3225569 : Blo 2149435 3225569 := bstep (se 2 (by rfl) ⟨1209588, by rfl⟩ : syracuseStep 3225569 = 2419177) B2419177
theorem B2150379 : Blo 2149435 2150379 := bstep (se 1 (by rfl) ⟨1612784, by rfl⟩ : syracuseStep 2150379 = 3225569) B3225569
theorem B2296333 : Blo 2149435 2296333 := bbase (se 3 (by rfl) ⟨430562, by rfl⟩ : syracuseStep 2296333 = 861125) (by norm_num)
theorem B12247109 : Blo 2149435 12247109 := bstep (se 4 (by rfl) ⟨1148166, by rfl⟩ : syracuseStep 12247109 = 2296333) B2296333
theorem B8164739 : Blo 2149435 8164739 := bstep (se 1 (by rfl) ⟨6123554, by rfl⟩ : syracuseStep 8164739 = 12247109) B12247109
theorem B5443159 : Blo 2149435 5443159 := bstep (se 1 (by rfl) ⟨4082369, by rfl⟩ : syracuseStep 5443159 = 8164739) B8164739
theorem B7257545 : Blo 2149435 7257545 := bstep (se 2 (by rfl) ⟨2721579, by rfl⟩ : syracuseStep 7257545 = 5443159) B5443159
theorem B4838363 : Blo 2149435 4838363 := bstep (se 1 (by rfl) ⟨3628772, by rfl⟩ : syracuseStep 4838363 = 7257545) B7257545
theorem B3225575 : Blo 2149435 3225575 := bstep (se 1 (by rfl) ⟨2419181, by rfl⟩ : syracuseStep 3225575 = 4838363) B4838363
theorem B2150383 : Blo 2149435 2150383 := bstep (se 1 (by rfl) ⟨1612787, by rfl⟩ : syracuseStep 2150383 = 3225575) B3225575
theorem B3225581 : Blo 2149435 3225581 := bbase (se 3 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 3225581 = 1209593) (by norm_num)
theorem B2150387 : Blo 2149435 2150387 := bstep (se 1 (by rfl) ⟨1612790, by rfl⟩ : syracuseStep 2150387 = 3225581) B3225581
theorem B4838381 : Blo 2149435 4838381 := bbase (se 3 (by rfl) ⟨907196, by rfl⟩ : syracuseStep 4838381 = 1814393) (by norm_num)
theorem B3225587 : Blo 2149435 3225587 := bstep (se 1 (by rfl) ⟨2419190, by rfl⟩ : syracuseStep 3225587 = 4838381) B4838381
theorem B2150391 : Blo 2149435 2150391 := bstep (se 1 (by rfl) ⟨1612793, by rfl⟩ : syracuseStep 2150391 = 3225587) B3225587
theorem B4592693 : Blo 2149435 4592693 := bbase (se 5 (by rfl) ⟨215282, by rfl⟩ : syracuseStep 4592693 = 430565) (by norm_num)
theorem B3061795 : Blo 2149435 3061795 := bstep (se 1 (by rfl) ⟨2296346, by rfl⟩ : syracuseStep 3061795 = 4592693) B4592693
theorem B4082393 : Blo 2149435 4082393 := bstep (se 2 (by rfl) ⟨1530897, by rfl⟩ : syracuseStep 4082393 = 3061795) B3061795
theorem B2721595 : Blo 2149435 2721595 := bstep (se 1 (by rfl) ⟨2041196, by rfl⟩ : syracuseStep 2721595 = 4082393) B4082393
theorem B3628793 : Blo 2149435 3628793 := bstep (se 2 (by rfl) ⟨1360797, by rfl⟩ : syracuseStep 3628793 = 2721595) B2721595
theorem B2419195 : Blo 2149435 2419195 := bstep (se 1 (by rfl) ⟨1814396, by rfl⟩ : syracuseStep 2419195 = 3628793) B3628793
theorem B3225593 : Blo 2149435 3225593 := bstep (se 2 (by rfl) ⟨1209597, by rfl⟩ : syracuseStep 3225593 = 2419195) B2419195
theorem B2150395 : Blo 2149435 2150395 := bstep (se 1 (by rfl) ⟨1612796, by rfl⟩ : syracuseStep 2150395 = 3225593) B3225593
theorem B3103573 : Blo 2149435 3103573 := bbase (se 9 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 3103573 = 18185) (by norm_num)
theorem B66209557 : Blo 2149435 66209557 := bstep (se 6 (by rfl) ⟨1551786, by rfl⟩ : syracuseStep 66209557 = 3103573) B3103573
theorem B88279409 : Blo 2149435 88279409 := bstep (se 2 (by rfl) ⟨33104778, by rfl⟩ : syracuseStep 88279409 = 66209557) B66209557
theorem B235411757 : Blo 2149435 235411757 := bstep (se 3 (by rfl) ⟨44139704, by rfl⟩ : syracuseStep 235411757 = 88279409) B88279409
theorem B156941171 : Blo 2149435 156941171 := bstep (se 1 (by rfl) ⟨117705878, by rfl⟩ : syracuseStep 156941171 = 235411757) B235411757
theorem B104627447 : Blo 2149435 104627447 := bstep (se 1 (by rfl) ⟨78470585, by rfl⟩ : syracuseStep 104627447 = 156941171) B156941171
theorem B69751631 : Blo 2149435 69751631 := bstep (se 1 (by rfl) ⟨52313723, by rfl⟩ : syracuseStep 69751631 = 104627447) B104627447
theorem B186004349 : Blo 2149435 186004349 := bstep (se 3 (by rfl) ⟨34875815, by rfl⟩ : syracuseStep 186004349 = 69751631) B69751631
theorem B124002899 : Blo 2149435 124002899 := bstep (se 1 (by rfl) ⟨93002174, by rfl⟩ : syracuseStep 124002899 = 186004349) B186004349
theorem B82668599 : Blo 2149435 82668599 := bstep (se 1 (by rfl) ⟨62001449, by rfl⟩ : syracuseStep 82668599 = 124002899) B124002899
theorem B55112399 : Blo 2149435 55112399 := bstep (se 1 (by rfl) ⟨41334299, by rfl⟩ : syracuseStep 55112399 = 82668599) B82668599
theorem B36741599 : Blo 2149435 36741599 := bstep (se 1 (by rfl) ⟨27556199, by rfl⟩ : syracuseStep 36741599 = 55112399) B55112399
theorem B24494399 : Blo 2149435 24494399 := bstep (se 1 (by rfl) ⟨18370799, by rfl⟩ : syracuseStep 24494399 = 36741599) B36741599
theorem B16329599 : Blo 2149435 16329599 := bstep (se 1 (by rfl) ⟨12247199, by rfl⟩ : syracuseStep 16329599 = 24494399) B24494399
theorem B10886399 : Blo 2149435 10886399 := bstep (se 1 (by rfl) ⟨8164799, by rfl⟩ : syracuseStep 10886399 = 16329599) B16329599
theorem B7257599 : Blo 2149435 7257599 := bstep (se 1 (by rfl) ⟨5443199, by rfl⟩ : syracuseStep 7257599 = 10886399) B10886399
theorem B4838399 : Blo 2149435 4838399 := bstep (se 1 (by rfl) ⟨3628799, by rfl⟩ : syracuseStep 4838399 = 7257599) B7257599
theorem B3225599 : Blo 2149435 3225599 := bstep (se 1 (by rfl) ⟨2419199, by rfl⟩ : syracuseStep 3225599 = 4838399) B4838399
theorem B2150399 : Blo 2149435 2150399 := bstep (se 1 (by rfl) ⟨1612799, by rfl⟩ : syracuseStep 2150399 = 3225599) B3225599
theorem B3225605 : Blo 2149435 3225605 := bbase (se 4 (by rfl) ⟨302400, by rfl⟩ : syracuseStep 3225605 = 604801) (by norm_num)
theorem B2150403 : Blo 2149435 2150403 := bstep (se 1 (by rfl) ⟨1612802, by rfl⟩ : syracuseStep 2150403 = 3225605) B3225605
theorem B3628813 : Blo 2149435 3628813 := bbase (se 3 (by rfl) ⟨680402, by rfl⟩ : syracuseStep 3628813 = 1360805) (by norm_num)
theorem B4838417 : Blo 2149435 4838417 := bstep (se 2 (by rfl) ⟨1814406, by rfl⟩ : syracuseStep 4838417 = 3628813) B3628813
theorem B3225611 : Blo 2149435 3225611 := bstep (se 1 (by rfl) ⟨2419208, by rfl⟩ : syracuseStep 3225611 = 4838417) B4838417
theorem B2150407 : Blo 2149435 2150407 := bstep (se 1 (by rfl) ⟨1612805, by rfl⟩ : syracuseStep 2150407 = 3225611) B3225611
theorem B2419213 : Blo 2149435 2419213 := bbase (se 3 (by rfl) ⟨453602, by rfl⟩ : syracuseStep 2419213 = 907205) (by norm_num)
theorem B3225617 : Blo 2149435 3225617 := bstep (se 2 (by rfl) ⟨1209606, by rfl⟩ : syracuseStep 3225617 = 2419213) B2419213
theorem B2150411 : Blo 2149435 2150411 := bstep (se 1 (by rfl) ⟨1612808, by rfl⟩ : syracuseStep 2150411 = 3225617) B3225617
theorem B7257653 : Blo 2149435 7257653 := bbase (se 5 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 7257653 = 680405) (by norm_num)
theorem B4838435 : Blo 2149435 4838435 := bstep (se 1 (by rfl) ⟨3628826, by rfl⟩ : syracuseStep 4838435 = 7257653) B7257653
theorem B3225623 : Blo 2149435 3225623 := bstep (se 1 (by rfl) ⟨2419217, by rfl⟩ : syracuseStep 3225623 = 4838435) B4838435
theorem B2150415 : Blo 2149435 2150415 := bstep (se 1 (by rfl) ⟨1612811, by rfl⟩ : syracuseStep 2150415 = 3225623) B3225623
theorem B3225629 : Blo 2149435 3225629 := bbase (se 3 (by rfl) ⟨604805, by rfl⟩ : syracuseStep 3225629 = 1209611) (by norm_num)
theorem B2150419 : Blo 2149435 2150419 := bstep (se 1 (by rfl) ⟨1612814, by rfl⟩ : syracuseStep 2150419 = 3225629) B3225629
theorem B4838453 : Blo 2149435 4838453 := bbase (se 5 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 4838453 = 453605) (by norm_num)
theorem B3225635 : Blo 2149435 3225635 := bstep (se 1 (by rfl) ⟨2419226, by rfl⟩ : syracuseStep 3225635 = 4838453) B4838453
theorem B2150423 : Blo 2149435 2150423 := bstep (se 1 (by rfl) ⟨1612817, by rfl⟩ : syracuseStep 2150423 = 3225635) B3225635
theorem B6889141 : Blo 2149435 6889141 := bbase (se 5 (by rfl) ⟨322928, by rfl⟩ : syracuseStep 6889141 = 645857) (by norm_num)
theorem B9185521 : Blo 2149435 9185521 := bstep (se 2 (by rfl) ⟨3444570, by rfl⟩ : syracuseStep 9185521 = 6889141) B6889141
theorem B12247361 : Blo 2149435 12247361 := bstep (se 2 (by rfl) ⟨4592760, by rfl⟩ : syracuseStep 12247361 = 9185521) B9185521
theorem B8164907 : Blo 2149435 8164907 := bstep (se 1 (by rfl) ⟨6123680, by rfl⟩ : syracuseStep 8164907 = 12247361) B12247361
theorem B5443271 : Blo 2149435 5443271 := bstep (se 1 (by rfl) ⟨4082453, by rfl⟩ : syracuseStep 5443271 = 8164907) B8164907
theorem B3628847 : Blo 2149435 3628847 := bstep (se 1 (by rfl) ⟨2721635, by rfl⟩ : syracuseStep 3628847 = 5443271) B5443271
theorem B2419231 : Blo 2149435 2419231 := bstep (se 1 (by rfl) ⟨1814423, by rfl⟩ : syracuseStep 2419231 = 3628847) B3628847
theorem B3225641 : Blo 2149435 3225641 := bstep (se 2 (by rfl) ⟨1209615, by rfl⟩ : syracuseStep 3225641 = 2419231) B2419231
theorem B2150427 : Blo 2149435 2150427 := bstep (se 1 (by rfl) ⟨1612820, by rfl⟩ : syracuseStep 2150427 = 3225641) B3225641
theorem B3875149 : Blo 2149435 3875149 := bbase (se 3 (by rfl) ⟨726590, by rfl⟩ : syracuseStep 3875149 = 1453181) (by norm_num)
theorem B5166865 : Blo 2149435 5166865 := bstep (se 2 (by rfl) ⟨1937574, by rfl⟩ : syracuseStep 5166865 = 3875149) B3875149
theorem B6889153 : Blo 2149435 6889153 := bstep (se 2 (by rfl) ⟨2583432, by rfl⟩ : syracuseStep 6889153 = 5166865) B5166865
theorem B9185537 : Blo 2149435 9185537 := bstep (se 2 (by rfl) ⟨3444576, by rfl⟩ : syracuseStep 9185537 = 6889153) B6889153
theorem B6123691 : Blo 2149435 6123691 := bstep (se 1 (by rfl) ⟨4592768, by rfl⟩ : syracuseStep 6123691 = 9185537) B9185537
theorem B8164921 : Blo 2149435 8164921 := bstep (se 2 (by rfl) ⟨3061845, by rfl⟩ : syracuseStep 8164921 = 6123691) B6123691
theorem B10886561 : Blo 2149435 10886561 := bstep (se 2 (by rfl) ⟨4082460, by rfl⟩ : syracuseStep 10886561 = 8164921) B8164921
theorem B7257707 : Blo 2149435 7257707 := bstep (se 1 (by rfl) ⟨5443280, by rfl⟩ : syracuseStep 7257707 = 10886561) B10886561
theorem B4838471 : Blo 2149435 4838471 := bstep (se 1 (by rfl) ⟨3628853, by rfl⟩ : syracuseStep 4838471 = 7257707) B7257707
theorem B3225647 : Blo 2149435 3225647 := bstep (se 1 (by rfl) ⟨2419235, by rfl⟩ : syracuseStep 3225647 = 4838471) B4838471
theorem B2150431 : Blo 2149435 2150431 := bstep (se 1 (by rfl) ⟨1612823, by rfl⟩ : syracuseStep 2150431 = 3225647) B3225647
theorem B3225653 : Blo 2149435 3225653 := bbase (se 5 (by rfl) ⟨151202, by rfl⟩ : syracuseStep 3225653 = 302405) (by norm_num)
theorem B2150435 : Blo 2149435 2150435 := bstep (se 1 (by rfl) ⟨1612826, by rfl⟩ : syracuseStep 2150435 = 3225653) B3225653
theorem B5443301 : Blo 2149435 5443301 := bbase (se 4 (by rfl) ⟨510309, by rfl⟩ : syracuseStep 5443301 = 1020619) (by norm_num)
theorem B3628867 : Blo 2149435 3628867 := bstep (se 1 (by rfl) ⟨2721650, by rfl⟩ : syracuseStep 3628867 = 5443301) B5443301
theorem B4838489 : Blo 2149435 4838489 := bstep (se 2 (by rfl) ⟨1814433, by rfl⟩ : syracuseStep 4838489 = 3628867) B3628867
theorem B3225659 : Blo 2149435 3225659 := bstep (se 1 (by rfl) ⟨2419244, by rfl⟩ : syracuseStep 3225659 = 4838489) B4838489
theorem B2150439 : Blo 2149435 2150439 := bstep (se 1 (by rfl) ⟨1612829, by rfl⟩ : syracuseStep 2150439 = 3225659) B3225659
theorem B2419249 : Blo 2149435 2419249 := bbase (se 2 (by rfl) ⟨907218, by rfl⟩ : syracuseStep 2419249 = 1814437) (by norm_num)
theorem B3225665 : Blo 2149435 3225665 := bstep (se 2 (by rfl) ⟨1209624, by rfl⟩ : syracuseStep 3225665 = 2419249) B2419249
theorem B2150443 : Blo 2149435 2150443 := bstep (se 1 (by rfl) ⟨1612832, by rfl⟩ : syracuseStep 2150443 = 3225665) B3225665
theorem B6889205 : Blo 2149435 6889205 := bbase (se 5 (by rfl) ⟨322931, by rfl⟩ : syracuseStep 6889205 = 645863) (by norm_num)
theorem B4592803 : Blo 2149435 4592803 := bstep (se 1 (by rfl) ⟨3444602, by rfl⟩ : syracuseStep 4592803 = 6889205) B6889205
theorem B6123737 : Blo 2149435 6123737 := bstep (se 2 (by rfl) ⟨2296401, by rfl⟩ : syracuseStep 6123737 = 4592803) B4592803
theorem B4082491 : Blo 2149435 4082491 := bstep (se 1 (by rfl) ⟨3061868, by rfl⟩ : syracuseStep 4082491 = 6123737) B6123737
theorem B5443321 : Blo 2149435 5443321 := bstep (se 2 (by rfl) ⟨2041245, by rfl⟩ : syracuseStep 5443321 = 4082491) B4082491
theorem B7257761 : Blo 2149435 7257761 := bstep (se 2 (by rfl) ⟨2721660, by rfl⟩ : syracuseStep 7257761 = 5443321) B5443321
theorem B4838507 : Blo 2149435 4838507 := bstep (se 1 (by rfl) ⟨3628880, by rfl⟩ : syracuseStep 4838507 = 7257761) B7257761
theorem B3225671 : Blo 2149435 3225671 := bstep (se 1 (by rfl) ⟨2419253, by rfl⟩ : syracuseStep 3225671 = 4838507) B4838507
theorem B2150447 : Blo 2149435 2150447 := bstep (se 1 (by rfl) ⟨1612835, by rfl⟩ : syracuseStep 2150447 = 3225671) B3225671
theorem B3225677 : Blo 2149435 3225677 := bbase (se 3 (by rfl) ⟨604814, by rfl⟩ : syracuseStep 3225677 = 1209629) (by norm_num)
theorem B2150451 : Blo 2149435 2150451 := bstep (se 1 (by rfl) ⟨1612838, by rfl⟩ : syracuseStep 2150451 = 3225677) B3225677
theorem B4838525 : Blo 2149435 4838525 := bbase (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) (by norm_num)
theorem B3225683 : Blo 2149435 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B2150455 : Blo 2149435 2150455 := bstep (se 1 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 2150455 = 3225683) B3225683
theorem B3628901 : Blo 2149435 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B2419267 : Blo 2149435 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B3225689 : Blo 2149435 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B2150459 : Blo 2149435 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B4592837 : Blo 2149435 4592837 := bbase (se 4 (by rfl) ⟨430578, by rfl⟩ : syracuseStep 4592837 = 861157) (by norm_num)
theorem B3061891 : Blo 2149435 3061891 := bstep (se 1 (by rfl) ⟨2296418, by rfl⟩ : syracuseStep 3061891 = 4592837) B4592837
theorem B16330085 : Blo 2149435 16330085 := bstep (se 4 (by rfl) ⟨1530945, by rfl⟩ : syracuseStep 16330085 = 3061891) B3061891
theorem B10886723 : Blo 2149435 10886723 := bstep (se 1 (by rfl) ⟨8165042, by rfl⟩ : syracuseStep 10886723 = 16330085) B16330085
theorem B7257815 : Blo 2149435 7257815 := bstep (se 1 (by rfl) ⟨5443361, by rfl⟩ : syracuseStep 7257815 = 10886723) B10886723
theorem B4838543 : Blo 2149435 4838543 := bstep (se 1 (by rfl) ⟨3628907, by rfl⟩ : syracuseStep 4838543 = 7257815) B7257815
theorem B3225695 : Blo 2149435 3225695 := bstep (se 1 (by rfl) ⟨2419271, by rfl⟩ : syracuseStep 3225695 = 4838543) B4838543
theorem B2150463 : Blo 2149435 2150463 := bstep (se 1 (by rfl) ⟨1612847, by rfl⟩ : syracuseStep 2150463 = 3225695) B3225695
theorem B3225701 : Blo 2149435 3225701 := bbase (se 4 (by rfl) ⟨302409, by rfl⟩ : syracuseStep 3225701 = 604819) (by norm_num)
theorem B2150467 : Blo 2149435 2150467 := bstep (se 1 (by rfl) ⟨1612850, by rfl⟩ : syracuseStep 2150467 = 3225701) B3225701
theorem B10333925 : Blo 2149435 10333925 := bbase (se 4 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 10333925 = 1937611) (by norm_num)
theorem B6889283 : Blo 2149435 6889283 := bstep (se 1 (by rfl) ⟨5166962, by rfl⟩ : syracuseStep 6889283 = 10333925) B10333925
theorem B4592855 : Blo 2149435 4592855 := bstep (se 1 (by rfl) ⟨3444641, by rfl⟩ : syracuseStep 4592855 = 6889283) B6889283
theorem B3061903 : Blo 2149435 3061903 := bstep (se 1 (by rfl) ⟨2296427, by rfl⟩ : syracuseStep 3061903 = 4592855) B4592855
theorem B4082537 : Blo 2149435 4082537 := bstep (se 2 (by rfl) ⟨1530951, by rfl⟩ : syracuseStep 4082537 = 3061903) B3061903
theorem B2721691 : Blo 2149435 2721691 := bstep (se 1 (by rfl) ⟨2041268, by rfl⟩ : syracuseStep 2721691 = 4082537) B4082537
theorem B3628921 : Blo 2149435 3628921 := bstep (se 2 (by rfl) ⟨1360845, by rfl⟩ : syracuseStep 3628921 = 2721691) B2721691
theorem B4838561 : Blo 2149435 4838561 := bstep (se 2 (by rfl) ⟨1814460, by rfl⟩ : syracuseStep 4838561 = 3628921) B3628921
theorem B3225707 : Blo 2149435 3225707 := bstep (se 1 (by rfl) ⟨2419280, by rfl⟩ : syracuseStep 3225707 = 4838561) B4838561
theorem B2150471 : Blo 2149435 2150471 := bstep (se 1 (by rfl) ⟨1612853, by rfl⟩ : syracuseStep 2150471 = 3225707) B3225707
theorem B2419285 : Blo 2149435 2419285 := bbase (se 8 (by rfl) ⟨14175, by rfl⟩ : syracuseStep 2419285 = 28351) (by norm_num)
theorem B3225713 : Blo 2149435 3225713 := bstep (se 2 (by rfl) ⟨1209642, by rfl⟩ : syracuseStep 3225713 = 2419285) B2419285
theorem B2150475 : Blo 2149435 2150475 := bstep (se 1 (by rfl) ⟨1612856, by rfl⟩ : syracuseStep 2150475 = 3225713) B3225713
theorem B2721701 : Blo 2149435 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B7257869 : Blo 2149435 7257869 := bstep (se 3 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 7257869 = 2721701) B2721701
theorem B4838579 : Blo 2149435 4838579 := bstep (se 1 (by rfl) ⟨3628934, by rfl⟩ : syracuseStep 4838579 = 7257869) B7257869
theorem B3225719 : Blo 2149435 3225719 := bstep (se 1 (by rfl) ⟨2419289, by rfl⟩ : syracuseStep 3225719 = 4838579) B4838579
theorem B2150479 : Blo 2149435 2150479 := bstep (se 1 (by rfl) ⟨1612859, by rfl⟩ : syracuseStep 2150479 = 3225719) B3225719
theorem B3225725 : Blo 2149435 3225725 := bbase (se 3 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 3225725 = 1209647) (by norm_num)
theorem B2150483 : Blo 2149435 2150483 := bstep (se 1 (by rfl) ⟨1612862, by rfl⟩ : syracuseStep 2150483 = 3225725) B3225725
theorem B4838597 : Blo 2149435 4838597 := bbase (se 4 (by rfl) ⟨453618, by rfl⟩ : syracuseStep 4838597 = 907237) (by norm_num)
theorem B3225731 : Blo 2149435 3225731 := bstep (se 1 (by rfl) ⟨2419298, by rfl⟩ : syracuseStep 3225731 = 4838597) B4838597
theorem B2150487 : Blo 2149435 2150487 := bstep (se 1 (by rfl) ⟨1612865, by rfl⟩ : syracuseStep 2150487 = 3225731) B3225731
theorem B2583505 : Blo 2149435 2583505 := bbase (se 2 (by rfl) ⟨968814, by rfl⟩ : syracuseStep 2583505 = 1937629) (by norm_num)
theorem B13778693 : Blo 2149435 13778693 := bstep (se 4 (by rfl) ⟨1291752, by rfl⟩ : syracuseStep 13778693 = 2583505) B2583505
theorem B9185795 : Blo 2149435 9185795 := bstep (se 1 (by rfl) ⟨6889346, by rfl⟩ : syracuseStep 9185795 = 13778693) B13778693
theorem B6123863 : Blo 2149435 6123863 := bstep (se 1 (by rfl) ⟨4592897, by rfl⟩ : syracuseStep 6123863 = 9185795) B9185795
theorem B4082575 : Blo 2149435 4082575 := bstep (se 1 (by rfl) ⟨3061931, by rfl⟩ : syracuseStep 4082575 = 6123863) B6123863
theorem B5443433 : Blo 2149435 5443433 := bstep (se 2 (by rfl) ⟨2041287, by rfl⟩ : syracuseStep 5443433 = 4082575) B4082575
theorem B3628955 : Blo 2149435 3628955 := bstep (se 1 (by rfl) ⟨2721716, by rfl⟩ : syracuseStep 3628955 = 5443433) B5443433
theorem B2419303 : Blo 2149435 2419303 := bstep (se 1 (by rfl) ⟨1814477, by rfl⟩ : syracuseStep 2419303 = 3628955) B3628955
theorem B3225737 : Blo 2149435 3225737 := bstep (se 2 (by rfl) ⟨1209651, by rfl⟩ : syracuseStep 3225737 = 2419303) B2419303
theorem B2150491 : Blo 2149435 2150491 := bstep (se 1 (by rfl) ⟨1612868, by rfl⟩ : syracuseStep 2150491 = 3225737) B3225737
theorem B10886885 : Blo 2149435 10886885 := bbase (se 4 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 10886885 = 2041291) (by norm_num)
theorem B7257923 : Blo 2149435 7257923 := bstep (se 1 (by rfl) ⟨5443442, by rfl⟩ : syracuseStep 7257923 = 10886885) B10886885
theorem B4838615 : Blo 2149435 4838615 := bstep (se 1 (by rfl) ⟨3628961, by rfl⟩ : syracuseStep 4838615 = 7257923) B7257923
theorem B3225743 : Blo 2149435 3225743 := bstep (se 1 (by rfl) ⟨2419307, by rfl⟩ : syracuseStep 3225743 = 4838615) B4838615
theorem B2150495 : Blo 2149435 2150495 := bstep (se 1 (by rfl) ⟨1612871, by rfl⟩ : syracuseStep 2150495 = 3225743) B3225743
theorem B3225749 : Blo 2149435 3225749 := bbase (se 6 (by rfl) ⟨75603, by rfl⟩ : syracuseStep 3225749 = 151207) (by norm_num)
theorem B2150499 : Blo 2149435 2150499 := bstep (se 1 (by rfl) ⟨1612874, by rfl⟩ : syracuseStep 2150499 = 3225749) B3225749
theorem B9185845 : Blo 2149435 9185845 := bbase (se 5 (by rfl) ⟨430586, by rfl⟩ : syracuseStep 9185845 = 861173) (by norm_num)
theorem B12247793 : Blo 2149435 12247793 := bstep (se 2 (by rfl) ⟨4592922, by rfl⟩ : syracuseStep 12247793 = 9185845) B9185845
theorem B8165195 : Blo 2149435 8165195 := bstep (se 1 (by rfl) ⟨6123896, by rfl⟩ : syracuseStep 8165195 = 12247793) B12247793
theorem B5443463 : Blo 2149435 5443463 := bstep (se 1 (by rfl) ⟨4082597, by rfl⟩ : syracuseStep 5443463 = 8165195) B8165195
theorem B3628975 : Blo 2149435 3628975 := bstep (se 1 (by rfl) ⟨2721731, by rfl⟩ : syracuseStep 3628975 = 5443463) B5443463
theorem B4838633 : Blo 2149435 4838633 := bstep (se 2 (by rfl) ⟨1814487, by rfl⟩ : syracuseStep 4838633 = 3628975) B3628975
theorem B3225755 : Blo 2149435 3225755 := bstep (se 1 (by rfl) ⟨2419316, by rfl⟩ : syracuseStep 3225755 = 4838633) B4838633
theorem B2150503 : Blo 2149435 2150503 := bstep (se 1 (by rfl) ⟨1612877, by rfl⟩ : syracuseStep 2150503 = 3225755) B3225755
theorem B2419321 : Blo 2149435 2419321 := bbase (se 2 (by rfl) ⟨907245, by rfl⟩ : syracuseStep 2419321 = 1814491) (by norm_num)
theorem B3225761 : Blo 2149435 3225761 := bstep (se 2 (by rfl) ⟨1209660, by rfl⟩ : syracuseStep 3225761 = 2419321) B2419321
theorem B2150507 : Blo 2149435 2150507 := bstep (se 1 (by rfl) ⟨1612880, by rfl⟩ : syracuseStep 2150507 = 3225761) B3225761
theorem B3875293 : Blo 2149435 3875293 := bbase (se 3 (by rfl) ⟨726617, by rfl⟩ : syracuseStep 3875293 = 1453235) (by norm_num)
theorem B20668229 : Blo 2149435 20668229 := bstep (se 4 (by rfl) ⟨1937646, by rfl⟩ : syracuseStep 20668229 = 3875293) B3875293
theorem B13778819 : Blo 2149435 13778819 := bstep (se 1 (by rfl) ⟨10334114, by rfl⟩ : syracuseStep 13778819 = 20668229) B20668229
theorem B9185879 : Blo 2149435 9185879 := bstep (se 1 (by rfl) ⟨6889409, by rfl⟩ : syracuseStep 9185879 = 13778819) B13778819
theorem B6123919 : Blo 2149435 6123919 := bstep (se 1 (by rfl) ⟨4592939, by rfl⟩ : syracuseStep 6123919 = 9185879) B9185879
theorem B8165225 : Blo 2149435 8165225 := bstep (se 2 (by rfl) ⟨3061959, by rfl⟩ : syracuseStep 8165225 = 6123919) B6123919
theorem B5443483 : Blo 2149435 5443483 := bstep (se 1 (by rfl) ⟨4082612, by rfl⟩ : syracuseStep 5443483 = 8165225) B8165225
theorem B7257977 : Blo 2149435 7257977 := bstep (se 2 (by rfl) ⟨2721741, by rfl⟩ : syracuseStep 7257977 = 5443483) B5443483
theorem B4838651 : Blo 2149435 4838651 := bstep (se 1 (by rfl) ⟨3628988, by rfl⟩ : syracuseStep 4838651 = 7257977) B7257977
theorem B3225767 : Blo 2149435 3225767 := bstep (se 1 (by rfl) ⟨2419325, by rfl⟩ : syracuseStep 3225767 = 4838651) B4838651
theorem B2150511 : Blo 2149435 2150511 := bstep (se 1 (by rfl) ⟨1612883, by rfl⟩ : syracuseStep 2150511 = 3225767) B3225767
theorem B3225773 : Blo 2149435 3225773 := bbase (se 3 (by rfl) ⟨604832, by rfl⟩ : syracuseStep 3225773 = 1209665) (by norm_num)
theorem B2150515 : Blo 2149435 2150515 := bstep (se 1 (by rfl) ⟨1612886, by rfl⟩ : syracuseStep 2150515 = 3225773) B3225773
theorem B4838669 : Blo 2149435 4838669 := bbase (se 3 (by rfl) ⟨907250, by rfl⟩ : syracuseStep 4838669 = 1814501) (by norm_num)
theorem B3225779 : Blo 2149435 3225779 := bstep (se 1 (by rfl) ⟨2419334, by rfl⟩ : syracuseStep 3225779 = 4838669) B4838669
theorem B2150519 : Blo 2149435 2150519 := bstep (se 1 (by rfl) ⟨1612889, by rfl⟩ : syracuseStep 2150519 = 3225779) B3225779
theorem B2721757 : Blo 2149435 2721757 := bbase (se 3 (by rfl) ⟨510329, by rfl⟩ : syracuseStep 2721757 = 1020659) (by norm_num)
theorem B3629009 : Blo 2149435 3629009 := bstep (se 2 (by rfl) ⟨1360878, by rfl⟩ : syracuseStep 3629009 = 2721757) B2721757
theorem B2419339 : Blo 2149435 2419339 := bstep (se 1 (by rfl) ⟨1814504, by rfl⟩ : syracuseStep 2419339 = 3629009) B3629009
theorem B3225785 : Blo 2149435 3225785 := bstep (se 2 (by rfl) ⟨1209669, by rfl⟩ : syracuseStep 3225785 = 2419339) B2419339
theorem B2150523 : Blo 2149435 2150523 := bstep (se 1 (by rfl) ⟨1612892, by rfl⟩ : syracuseStep 2150523 = 3225785) B3225785
theorem B18371893 : Blo 2149435 18371893 := bbase (se 5 (by rfl) ⟨861182, by rfl⟩ : syracuseStep 18371893 = 1722365) (by norm_num)
theorem B24495857 : Blo 2149435 24495857 := bstep (se 2 (by rfl) ⟨9185946, by rfl⟩ : syracuseStep 24495857 = 18371893) B18371893
theorem B16330571 : Blo 2149435 16330571 := bstep (se 1 (by rfl) ⟨12247928, by rfl⟩ : syracuseStep 16330571 = 24495857) B24495857
theorem B10887047 : Blo 2149435 10887047 := bstep (se 1 (by rfl) ⟨8165285, by rfl⟩ : syracuseStep 10887047 = 16330571) B16330571
theorem B7258031 : Blo 2149435 7258031 := bstep (se 1 (by rfl) ⟨5443523, by rfl⟩ : syracuseStep 7258031 = 10887047) B10887047
theorem B4838687 : Blo 2149435 4838687 := bstep (se 1 (by rfl) ⟨3629015, by rfl⟩ : syracuseStep 4838687 = 7258031) B7258031
theorem B3225791 : Blo 2149435 3225791 := bstep (se 1 (by rfl) ⟨2419343, by rfl⟩ : syracuseStep 3225791 = 4838687) B4838687
theorem B2150527 : Blo 2149435 2150527 := bstep (se 1 (by rfl) ⟨1612895, by rfl⟩ : syracuseStep 2150527 = 3225791) B3225791
theorem B3225797 : Blo 2149435 3225797 := bbase (se 4 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 3225797 = 604837) (by norm_num)
theorem B2150531 : Blo 2149435 2150531 := bstep (se 1 (by rfl) ⟨1612898, by rfl⟩ : syracuseStep 2150531 = 3225797) B3225797
theorem B3629029 : Blo 2149435 3629029 := bbase (se 4 (by rfl) ⟨340221, by rfl⟩ : syracuseStep 3629029 = 680443) (by norm_num)
theorem B4838705 : Blo 2149435 4838705 := bstep (se 2 (by rfl) ⟨1814514, by rfl⟩ : syracuseStep 4838705 = 3629029) B3629029
theorem B3225803 : Blo 2149435 3225803 := bstep (se 1 (by rfl) ⟨2419352, by rfl⟩ : syracuseStep 3225803 = 4838705) B4838705
theorem B2150535 : Blo 2149435 2150535 := bstep (se 1 (by rfl) ⟨1612901, by rfl⟩ : syracuseStep 2150535 = 3225803) B3225803
theorem B2419357 : Blo 2149435 2419357 := bbase (se 3 (by rfl) ⟨453629, by rfl⟩ : syracuseStep 2419357 = 907259) (by norm_num)
theorem B3225809 : Blo 2149435 3225809 := bstep (se 2 (by rfl) ⟨1209678, by rfl⟩ : syracuseStep 3225809 = 2419357) B2419357
theorem B2150539 : Blo 2149435 2150539 := bstep (se 1 (by rfl) ⟨1612904, by rfl⟩ : syracuseStep 2150539 = 3225809) B3225809
theorem B7258085 : Blo 2149435 7258085 := bbase (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) (by norm_num)
theorem B4838723 : Blo 2149435 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B3225815 : Blo 2149435 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B2150543 : Blo 2149435 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B3225821 : Blo 2149435 3225821 := bbase (se 3 (by rfl) ⟨604841, by rfl⟩ : syracuseStep 3225821 = 1209683) (by norm_num)
theorem B2150547 : Blo 2149435 2150547 := bstep (se 1 (by rfl) ⟨1612910, by rfl⟩ : syracuseStep 2150547 = 3225821) B3225821
theorem B4838741 : Blo 2149435 4838741 := bbase (se 15 (by rfl) ⟨221, by rfl⟩ : syracuseStep 4838741 = 443) (by norm_num)
theorem B3225827 : Blo 2149435 3225827 := bstep (se 1 (by rfl) ⟨2419370, by rfl⟩ : syracuseStep 3225827 = 4838741) B4838741
theorem B2150551 : Blo 2149435 2150551 := bstep (se 1 (by rfl) ⟨1612913, by rfl⟩ : syracuseStep 2150551 = 3225827) B3225827
theorem B2296517 : Blo 2149435 2296517 := bbase (se 4 (by rfl) ⟨215298, by rfl⟩ : syracuseStep 2296517 = 430597) (by norm_num)
theorem B6124045 : Blo 2149435 6124045 := bstep (se 3 (by rfl) ⟨1148258, by rfl⟩ : syracuseStep 6124045 = 2296517) B2296517
theorem B8165393 : Blo 2149435 8165393 := bstep (se 2 (by rfl) ⟨3062022, by rfl⟩ : syracuseStep 8165393 = 6124045) B6124045
theorem B5443595 : Blo 2149435 5443595 := bstep (se 1 (by rfl) ⟨4082696, by rfl⟩ : syracuseStep 5443595 = 8165393) B8165393
theorem B3629063 : Blo 2149435 3629063 := bstep (se 1 (by rfl) ⟨2721797, by rfl⟩ : syracuseStep 3629063 = 5443595) B5443595
theorem B2419375 : Blo 2149435 2419375 := bstep (se 1 (by rfl) ⟨1814531, by rfl⟩ : syracuseStep 2419375 = 3629063) B3629063
theorem B3225833 : Blo 2149435 3225833 := bstep (se 2 (by rfl) ⟨1209687, by rfl⟩ : syracuseStep 3225833 = 2419375) B2419375
theorem B2150555 : Blo 2149435 2150555 := bstep (se 1 (by rfl) ⟨1612916, by rfl⟩ : syracuseStep 2150555 = 3225833) B3225833
theorem B3103805 : Blo 2149435 3103805 := bbase (se 3 (by rfl) ⟨581963, by rfl⟩ : syracuseStep 3103805 = 1163927) (by norm_num)
theorem B8276813 : Blo 2149435 8276813 := bstep (se 3 (by rfl) ⟨1551902, by rfl⟩ : syracuseStep 8276813 = 3103805) B3103805
theorem B5517875 : Blo 2149435 5517875 := bstep (se 1 (by rfl) ⟨4138406, by rfl⟩ : syracuseStep 5517875 = 8276813) B8276813
theorem B3678583 : Blo 2149435 3678583 := bstep (se 1 (by rfl) ⟨2758937, by rfl⟩ : syracuseStep 3678583 = 5517875) B5517875
theorem B4904777 : Blo 2149435 4904777 := bstep (se 2 (by rfl) ⟨1839291, by rfl⟩ : syracuseStep 4904777 = 3678583) B3678583
theorem B13079405 : Blo 2149435 13079405 := bstep (se 3 (by rfl) ⟨2452388, by rfl⟩ : syracuseStep 13079405 = 4904777) B4904777
theorem B34878413 : Blo 2149435 34878413 := bstep (se 3 (by rfl) ⟨6539702, by rfl⟩ : syracuseStep 34878413 = 13079405) B13079405
theorem B23252275 : Blo 2149435 23252275 := bstep (se 1 (by rfl) ⟨17439206, by rfl⟩ : syracuseStep 23252275 = 34878413) B34878413
theorem B31003033 : Blo 2149435 31003033 := bstep (se 2 (by rfl) ⟨11626137, by rfl⟩ : syracuseStep 31003033 = 23252275) B23252275
theorem B41337377 : Blo 2149435 41337377 := bstep (se 2 (by rfl) ⟨15501516, by rfl⟩ : syracuseStep 41337377 = 31003033) B31003033
theorem B27558251 : Blo 2149435 27558251 := bstep (se 1 (by rfl) ⟨20668688, by rfl⟩ : syracuseStep 27558251 = 41337377) B41337377
theorem B18372167 : Blo 2149435 18372167 := bstep (se 1 (by rfl) ⟨13779125, by rfl⟩ : syracuseStep 18372167 = 27558251) B27558251
theorem B12248111 : Blo 2149435 12248111 := bstep (se 1 (by rfl) ⟨9186083, by rfl⟩ : syracuseStep 12248111 = 18372167) B18372167
theorem B8165407 : Blo 2149435 8165407 := bstep (se 1 (by rfl) ⟨6124055, by rfl⟩ : syracuseStep 8165407 = 12248111) B12248111
theorem B10887209 : Blo 2149435 10887209 := bstep (se 2 (by rfl) ⟨4082703, by rfl⟩ : syracuseStep 10887209 = 8165407) B8165407
theorem B7258139 : Blo 2149435 7258139 := bstep (se 1 (by rfl) ⟨5443604, by rfl⟩ : syracuseStep 7258139 = 10887209) B10887209
theorem B4838759 : Blo 2149435 4838759 := bstep (se 1 (by rfl) ⟨3629069, by rfl⟩ : syracuseStep 4838759 = 7258139) B7258139
theorem B3225839 : Blo 2149435 3225839 := bstep (se 1 (by rfl) ⟨2419379, by rfl⟩ : syracuseStep 3225839 = 4838759) B4838759
theorem B2150559 : Blo 2149435 2150559 := bstep (se 1 (by rfl) ⟨1612919, by rfl⟩ : syracuseStep 2150559 = 3225839) B3225839
theorem B3225845 : Blo 2149435 3225845 := bbase (se 5 (by rfl) ⟨151211, by rfl⟩ : syracuseStep 3225845 = 302423) (by norm_num)
theorem B2150563 : Blo 2149435 2150563 := bstep (se 1 (by rfl) ⟨1612922, by rfl⟩ : syracuseStep 2150563 = 3225845) B3225845
theorem B14714389 : Blo 2149435 14714389 := bbase (se 6 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 14714389 = 689737) (by norm_num)
theorem B19619185 : Blo 2149435 19619185 := bstep (se 2 (by rfl) ⟨7357194, by rfl⟩ : syracuseStep 19619185 = 14714389) B14714389
theorem B26158913 : Blo 2149435 26158913 := bstep (se 2 (by rfl) ⟨9809592, by rfl⟩ : syracuseStep 26158913 = 19619185) B19619185
theorem B17439275 : Blo 2149435 17439275 := bstep (se 1 (by rfl) ⟨13079456, by rfl⟩ : syracuseStep 17439275 = 26158913) B26158913
theorem B11626183 : Blo 2149435 11626183 := bstep (se 1 (by rfl) ⟨8719637, by rfl⟩ : syracuseStep 11626183 = 17439275) B17439275
theorem B15501577 : Blo 2149435 15501577 := bstep (se 2 (by rfl) ⟨5813091, by rfl⟩ : syracuseStep 15501577 = 11626183) B11626183
theorem B20668769 : Blo 2149435 20668769 := bstep (se 2 (by rfl) ⟨7750788, by rfl⟩ : syracuseStep 20668769 = 15501577) B15501577
theorem B13779179 : Blo 2149435 13779179 := bstep (se 1 (by rfl) ⟨10334384, by rfl⟩ : syracuseStep 13779179 = 20668769) B20668769
theorem B9186119 : Blo 2149435 9186119 := bstep (se 1 (by rfl) ⟨6889589, by rfl⟩ : syracuseStep 9186119 = 13779179) B13779179
theorem B6124079 : Blo 2149435 6124079 := bstep (se 1 (by rfl) ⟨4593059, by rfl⟩ : syracuseStep 6124079 = 9186119) B9186119
theorem B4082719 : Blo 2149435 4082719 := bstep (se 1 (by rfl) ⟨3062039, by rfl⟩ : syracuseStep 4082719 = 6124079) B6124079
theorem B5443625 : Blo 2149435 5443625 := bstep (se 2 (by rfl) ⟨2041359, by rfl⟩ : syracuseStep 5443625 = 4082719) B4082719
theorem B3629083 : Blo 2149435 3629083 := bstep (se 1 (by rfl) ⟨2721812, by rfl⟩ : syracuseStep 3629083 = 5443625) B5443625
theorem B4838777 : Blo 2149435 4838777 := bstep (se 2 (by rfl) ⟨1814541, by rfl⟩ : syracuseStep 4838777 = 3629083) B3629083
theorem B3225851 : Blo 2149435 3225851 := bstep (se 1 (by rfl) ⟨2419388, by rfl⟩ : syracuseStep 3225851 = 4838777) B4838777
theorem B2150567 : Blo 2149435 2150567 := bstep (se 1 (by rfl) ⟨1612925, by rfl⟩ : syracuseStep 2150567 = 3225851) B3225851
theorem B2419393 : Blo 2149435 2419393 := bbase (se 2 (by rfl) ⟨907272, by rfl⟩ : syracuseStep 2419393 = 1814545) (by norm_num)
theorem B3225857 : Blo 2149435 3225857 := bstep (se 2 (by rfl) ⟨1209696, by rfl⟩ : syracuseStep 3225857 = 2419393) B2419393
theorem B2150571 : Blo 2149435 2150571 := bstep (se 1 (by rfl) ⟨1612928, by rfl⟩ : syracuseStep 2150571 = 3225857) B3225857
theorem B5443645 : Blo 2149435 5443645 := bbase (se 3 (by rfl) ⟨1020683, by rfl⟩ : syracuseStep 5443645 = 2041367) (by norm_num)
theorem B7258193 : Blo 2149435 7258193 := bstep (se 2 (by rfl) ⟨2721822, by rfl⟩ : syracuseStep 7258193 = 5443645) B5443645
theorem B4838795 : Blo 2149435 4838795 := bstep (se 1 (by rfl) ⟨3629096, by rfl⟩ : syracuseStep 4838795 = 7258193) B7258193
theorem B3225863 : Blo 2149435 3225863 := bstep (se 1 (by rfl) ⟨2419397, by rfl⟩ : syracuseStep 3225863 = 4838795) B4838795
theorem B2150575 : Blo 2149435 2150575 := bstep (se 1 (by rfl) ⟨1612931, by rfl⟩ : syracuseStep 2150575 = 3225863) B3225863
theorem B3225869 : Blo 2149435 3225869 := bbase (se 3 (by rfl) ⟨604850, by rfl⟩ : syracuseStep 3225869 = 1209701) (by norm_num)
theorem B2150579 : Blo 2149435 2150579 := bstep (se 1 (by rfl) ⟨1612934, by rfl⟩ : syracuseStep 2150579 = 3225869) B3225869
theorem B4838813 : Blo 2149435 4838813 := bbase (se 3 (by rfl) ⟨907277, by rfl⟩ : syracuseStep 4838813 = 1814555) (by norm_num)
theorem B3225875 : Blo 2149435 3225875 := bstep (se 1 (by rfl) ⟨2419406, by rfl⟩ : syracuseStep 3225875 = 4838813) B4838813
theorem B2150583 : Blo 2149435 2150583 := bstep (se 1 (by rfl) ⟨1612937, by rfl⟩ : syracuseStep 2150583 = 3225875) B3225875
theorem B3629117 : Blo 2149435 3629117 := bbase (se 3 (by rfl) ⟨680459, by rfl⟩ : syracuseStep 3629117 = 1360919) (by norm_num)
theorem B2419411 : Blo 2149435 2419411 := bstep (se 1 (by rfl) ⟨1814558, by rfl⟩ : syracuseStep 2419411 = 3629117) B3629117
theorem B3225881 : Blo 2149435 3225881 := bstep (se 2 (by rfl) ⟨1209705, by rfl⟩ : syracuseStep 3225881 = 2419411) B2419411
theorem B2150587 : Blo 2149435 2150587 := bstep (se 1 (by rfl) ⟨1612940, by rfl⟩ : syracuseStep 2150587 = 3225881) B3225881
theorem B2583625 : Blo 2149435 2583625 := bbase (se 2 (by rfl) ⟨968859, by rfl⟩ : syracuseStep 2583625 = 1937719) (by norm_num)
theorem B3444833 : Blo 2149435 3444833 := bstep (se 2 (by rfl) ⟨1291812, by rfl⟩ : syracuseStep 3444833 = 2583625) B2583625
theorem B2296555 : Blo 2149435 2296555 := bstep (se 1 (by rfl) ⟨1722416, by rfl⟩ : syracuseStep 2296555 = 3444833) B3444833
theorem B12248293 : Blo 2149435 12248293 := bstep (se 4 (by rfl) ⟨1148277, by rfl⟩ : syracuseStep 12248293 = 2296555) B2296555
theorem B16331057 : Blo 2149435 16331057 := bstep (se 2 (by rfl) ⟨6124146, by rfl⟩ : syracuseStep 16331057 = 12248293) B12248293
theorem B10887371 : Blo 2149435 10887371 := bstep (se 1 (by rfl) ⟨8165528, by rfl⟩ : syracuseStep 10887371 = 16331057) B16331057
theorem B7258247 : Blo 2149435 7258247 := bstep (se 1 (by rfl) ⟨5443685, by rfl⟩ : syracuseStep 7258247 = 10887371) B10887371
theorem B4838831 : Blo 2149435 4838831 := bstep (se 1 (by rfl) ⟨3629123, by rfl⟩ : syracuseStep 4838831 = 7258247) B7258247
theorem B3225887 : Blo 2149435 3225887 := bstep (se 1 (by rfl) ⟨2419415, by rfl⟩ : syracuseStep 3225887 = 4838831) B4838831
theorem B2150591 : Blo 2149435 2150591 := bstep (se 1 (by rfl) ⟨1612943, by rfl⟩ : syracuseStep 2150591 = 3225887) B3225887
theorem B3225893 : Blo 2149435 3225893 := bbase (se 4 (by rfl) ⟨302427, by rfl⟩ : syracuseStep 3225893 = 604855) (by norm_num)
theorem B2150595 : Blo 2149435 2150595 := bstep (se 1 (by rfl) ⟨1612946, by rfl⟩ : syracuseStep 2150595 = 3225893) B3225893
theorem B2721853 : Blo 2149435 2721853 := bbase (se 3 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 2721853 = 1020695) (by norm_num)
theorem B3629137 : Blo 2149435 3629137 := bstep (se 2 (by rfl) ⟨1360926, by rfl⟩ : syracuseStep 3629137 = 2721853) B2721853
theorem B4838849 : Blo 2149435 4838849 := bstep (se 2 (by rfl) ⟨1814568, by rfl⟩ : syracuseStep 4838849 = 3629137) B3629137
theorem B3225899 : Blo 2149435 3225899 := bstep (se 1 (by rfl) ⟨2419424, by rfl⟩ : syracuseStep 3225899 = 4838849) B4838849
theorem B2150599 : Blo 2149435 2150599 := bstep (se 1 (by rfl) ⟨1612949, by rfl⟩ : syracuseStep 2150599 = 3225899) B3225899
theorem B2419429 : Blo 2149435 2419429 := bbase (se 4 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 2419429 = 453643) (by norm_num)
theorem B3225905 : Blo 2149435 3225905 := bstep (se 2 (by rfl) ⟨1209714, by rfl⟩ : syracuseStep 3225905 = 2419429) B2419429
theorem B2150603 : Blo 2149435 2150603 := bstep (se 1 (by rfl) ⟨1612952, by rfl⟩ : syracuseStep 2150603 = 3225905) B3225905
theorem B4359901 : Blo 2149435 4359901 := bbase (se 3 (by rfl) ⟨817481, by rfl⟩ : syracuseStep 4359901 = 1634963) (by norm_num)
theorem B5813201 : Blo 2149435 5813201 := bstep (se 2 (by rfl) ⟨2179950, by rfl⟩ : syracuseStep 5813201 = 4359901) B4359901
theorem B3875467 : Blo 2149435 3875467 := bstep (se 1 (by rfl) ⟨2906600, by rfl⟩ : syracuseStep 3875467 = 5813201) B5813201
theorem B5167289 : Blo 2149435 5167289 := bstep (se 2 (by rfl) ⟨1937733, by rfl⟩ : syracuseStep 5167289 = 3875467) B3875467
theorem B3444859 : Blo 2149435 3444859 := bstep (se 1 (by rfl) ⟨2583644, by rfl⟩ : syracuseStep 3444859 = 5167289) B5167289
theorem B4593145 : Blo 2149435 4593145 := bstep (se 2 (by rfl) ⟨1722429, by rfl⟩ : syracuseStep 4593145 = 3444859) B3444859
theorem B6124193 : Blo 2149435 6124193 := bstep (se 2 (by rfl) ⟨2296572, by rfl⟩ : syracuseStep 6124193 = 4593145) B4593145
theorem B4082795 : Blo 2149435 4082795 := bstep (se 1 (by rfl) ⟨3062096, by rfl⟩ : syracuseStep 4082795 = 6124193) B6124193
theorem B2721863 : Blo 2149435 2721863 := bstep (se 1 (by rfl) ⟨2041397, by rfl⟩ : syracuseStep 2721863 = 4082795) B4082795
theorem B7258301 : Blo 2149435 7258301 := bstep (se 3 (by rfl) ⟨1360931, by rfl⟩ : syracuseStep 7258301 = 2721863) B2721863
theorem B4838867 : Blo 2149435 4838867 := bstep (se 1 (by rfl) ⟨3629150, by rfl⟩ : syracuseStep 4838867 = 7258301) B7258301
theorem B3225911 : Blo 2149435 3225911 := bstep (se 1 (by rfl) ⟨2419433, by rfl⟩ : syracuseStep 3225911 = 4838867) B4838867
theorem B2150607 : Blo 2149435 2150607 := bstep (se 1 (by rfl) ⟨1612955, by rfl⟩ : syracuseStep 2150607 = 3225911) B3225911
theorem B3225917 : Blo 2149435 3225917 := bbase (se 3 (by rfl) ⟨604859, by rfl⟩ : syracuseStep 3225917 = 1209719) (by norm_num)
theorem B2150611 : Blo 2149435 2150611 := bstep (se 1 (by rfl) ⟨1612958, by rfl⟩ : syracuseStep 2150611 = 3225917) B3225917
theorem B4838885 : Blo 2149435 4838885 := bbase (se 4 (by rfl) ⟨453645, by rfl⟩ : syracuseStep 4838885 = 907291) (by norm_num)
theorem B3225923 : Blo 2149435 3225923 := bstep (se 1 (by rfl) ⟨2419442, by rfl⟩ : syracuseStep 3225923 = 4838885) B4838885
theorem B2150615 : Blo 2149435 2150615 := bstep (se 1 (by rfl) ⟨1612961, by rfl⟩ : syracuseStep 2150615 = 3225923) B3225923
theorem B5443757 : Blo 2149435 5443757 := bbase (se 3 (by rfl) ⟨1020704, by rfl⟩ : syracuseStep 5443757 = 2041409) (by norm_num)
theorem B3629171 : Blo 2149435 3629171 := bstep (se 1 (by rfl) ⟨2721878, by rfl⟩ : syracuseStep 3629171 = 5443757) B5443757
theorem B2419447 : Blo 2149435 2419447 := bstep (se 1 (by rfl) ⟨1814585, by rfl⟩ : syracuseStep 2419447 = 3629171) B3629171
theorem B3225929 : Blo 2149435 3225929 := bstep (se 2 (by rfl) ⟨1209723, by rfl⟩ : syracuseStep 3225929 = 2419447) B2419447
theorem B2150619 : Blo 2149435 2150619 := bstep (se 1 (by rfl) ⟨1612964, by rfl⟩ : syracuseStep 2150619 = 3225929) B3225929
theorem B8277061 : Blo 2149435 8277061 := bbase (se 4 (by rfl) ⟨775974, by rfl⟩ : syracuseStep 8277061 = 1551949) (by norm_num)
theorem B11036081 : Blo 2149435 11036081 := bstep (se 2 (by rfl) ⟨4138530, by rfl⟩ : syracuseStep 11036081 = 8277061) B8277061
theorem B7357387 : Blo 2149435 7357387 := bstep (se 1 (by rfl) ⟨5518040, by rfl⟩ : syracuseStep 7357387 = 11036081) B11036081
theorem B9809849 : Blo 2149435 9809849 := bstep (se 2 (by rfl) ⟨3678693, by rfl⟩ : syracuseStep 9809849 = 7357387) B7357387
theorem B26159597 : Blo 2149435 26159597 := bstep (se 3 (by rfl) ⟨4904924, by rfl⟩ : syracuseStep 26159597 = 9809849) B9809849
theorem B17439731 : Blo 2149435 17439731 := bstep (se 1 (by rfl) ⟨13079798, by rfl⟩ : syracuseStep 17439731 = 26159597) B26159597
theorem B11626487 : Blo 2149435 11626487 := bstep (se 1 (by rfl) ⟨8719865, by rfl⟩ : syracuseStep 11626487 = 17439731) B17439731
theorem B7750991 : Blo 2149435 7750991 := bstep (se 1 (by rfl) ⟨5813243, by rfl⟩ : syracuseStep 7750991 = 11626487) B11626487
theorem B5167327 : Blo 2149435 5167327 := bstep (se 1 (by rfl) ⟨3875495, by rfl⟩ : syracuseStep 5167327 = 7750991) B7750991
theorem B6889769 : Blo 2149435 6889769 := bstep (se 2 (by rfl) ⟨2583663, by rfl⟩ : syracuseStep 6889769 = 5167327) B5167327
theorem B4593179 : Blo 2149435 4593179 := bstep (se 1 (by rfl) ⟨3444884, by rfl⟩ : syracuseStep 4593179 = 6889769) B6889769
theorem B3062119 : Blo 2149435 3062119 := bstep (se 1 (by rfl) ⟨2296589, by rfl⟩ : syracuseStep 3062119 = 4593179) B4593179
theorem B4082825 : Blo 2149435 4082825 := bstep (se 2 (by rfl) ⟨1531059, by rfl⟩ : syracuseStep 4082825 = 3062119) B3062119
theorem B10887533 : Blo 2149435 10887533 := bstep (se 3 (by rfl) ⟨2041412, by rfl⟩ : syracuseStep 10887533 = 4082825) B4082825
theorem B7258355 : Blo 2149435 7258355 := bstep (se 1 (by rfl) ⟨5443766, by rfl⟩ : syracuseStep 7258355 = 10887533) B10887533
theorem B4838903 : Blo 2149435 4838903 := bstep (se 1 (by rfl) ⟨3629177, by rfl⟩ : syracuseStep 4838903 = 7258355) B7258355
theorem B3225935 : Blo 2149435 3225935 := bstep (se 1 (by rfl) ⟨2419451, by rfl⟩ : syracuseStep 3225935 = 4838903) B4838903
theorem B2150623 : Blo 2149435 2150623 := bstep (se 1 (by rfl) ⟨1612967, by rfl⟩ : syracuseStep 2150623 = 3225935) B3225935
theorem B3225941 : Blo 2149435 3225941 := bbase (se 10 (by rfl) ⟨4725, by rfl⟩ : syracuseStep 3225941 = 9451) (by norm_num)
theorem B2150627 : Blo 2149435 2150627 := bstep (se 1 (by rfl) ⟨1612970, by rfl⟩ : syracuseStep 2150627 = 3225941) B3225941
theorem B6124261 : Blo 2149435 6124261 := bbase (se 4 (by rfl) ⟨574149, by rfl⟩ : syracuseStep 6124261 = 1148299) (by norm_num)
theorem B8165681 : Blo 2149435 8165681 := bstep (se 2 (by rfl) ⟨3062130, by rfl⟩ : syracuseStep 8165681 = 6124261) B6124261
theorem B5443787 : Blo 2149435 5443787 := bstep (se 1 (by rfl) ⟨4082840, by rfl⟩ : syracuseStep 5443787 = 8165681) B8165681
theorem B3629191 : Blo 2149435 3629191 := bstep (se 1 (by rfl) ⟨2721893, by rfl⟩ : syracuseStep 3629191 = 5443787) B5443787
theorem B4838921 : Blo 2149435 4838921 := bstep (se 2 (by rfl) ⟨1814595, by rfl⟩ : syracuseStep 4838921 = 3629191) B3629191
theorem B3225947 : Blo 2149435 3225947 := bstep (se 1 (by rfl) ⟨2419460, by rfl⟩ : syracuseStep 3225947 = 4838921) B4838921
theorem B2150631 : Blo 2149435 2150631 := bstep (se 1 (by rfl) ⟨1612973, by rfl⟩ : syracuseStep 2150631 = 3225947) B3225947
theorem B2419465 : Blo 2149435 2419465 := bbase (se 2 (by rfl) ⟨907299, by rfl⟩ : syracuseStep 2419465 = 1814599) (by norm_num)
theorem B3225953 : Blo 2149435 3225953 := bstep (se 2 (by rfl) ⟨1209732, by rfl⟩ : syracuseStep 3225953 = 2419465) B2419465
theorem B2150635 : Blo 2149435 2150635 := bstep (se 1 (by rfl) ⟨1612976, by rfl⟩ : syracuseStep 2150635 = 3225953) B3225953
theorem B13079893 : Blo 2149435 13079893 := bbase (se 14 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 13079893 = 2395) (by norm_num)
theorem B17439857 : Blo 2149435 17439857 := bstep (se 2 (by rfl) ⟨6539946, by rfl⟩ : syracuseStep 17439857 = 13079893) B13079893
theorem B11626571 : Blo 2149435 11626571 := bstep (se 1 (by rfl) ⟨8719928, by rfl⟩ : syracuseStep 11626571 = 17439857) B17439857
theorem B7751047 : Blo 2149435 7751047 := bstep (se 1 (by rfl) ⟨5813285, by rfl⟩ : syracuseStep 7751047 = 11626571) B11626571
theorem B10334729 : Blo 2149435 10334729 := bstep (se 2 (by rfl) ⟨3875523, by rfl⟩ : syracuseStep 10334729 = 7751047) B7751047
theorem B27559277 : Blo 2149435 27559277 := bstep (se 3 (by rfl) ⟨5167364, by rfl⟩ : syracuseStep 27559277 = 10334729) B10334729
theorem B18372851 : Blo 2149435 18372851 := bstep (se 1 (by rfl) ⟨13779638, by rfl⟩ : syracuseStep 18372851 = 27559277) B27559277
theorem B12248567 : Blo 2149435 12248567 := bstep (se 1 (by rfl) ⟨9186425, by rfl⟩ : syracuseStep 12248567 = 18372851) B18372851
theorem B8165711 : Blo 2149435 8165711 := bstep (se 1 (by rfl) ⟨6124283, by rfl⟩ : syracuseStep 8165711 = 12248567) B12248567
theorem B5443807 : Blo 2149435 5443807 := bstep (se 1 (by rfl) ⟨4082855, by rfl⟩ : syracuseStep 5443807 = 8165711) B8165711
theorem B7258409 : Blo 2149435 7258409 := bstep (se 2 (by rfl) ⟨2721903, by rfl⟩ : syracuseStep 7258409 = 5443807) B5443807
theorem B4838939 : Blo 2149435 4838939 := bstep (se 1 (by rfl) ⟨3629204, by rfl⟩ : syracuseStep 4838939 = 7258409) B7258409
theorem B3225959 : Blo 2149435 3225959 := bstep (se 1 (by rfl) ⟨2419469, by rfl⟩ : syracuseStep 3225959 = 4838939) B4838939
theorem B2150639 : Blo 2149435 2150639 := bstep (se 1 (by rfl) ⟨1612979, by rfl⟩ : syracuseStep 2150639 = 3225959) B3225959
theorem B3225965 : Blo 2149435 3225965 := bbase (se 3 (by rfl) ⟨604868, by rfl⟩ : syracuseStep 3225965 = 1209737) (by norm_num)
theorem B2150643 : Blo 2149435 2150643 := bstep (se 1 (by rfl) ⟨1612982, by rfl⟩ : syracuseStep 2150643 = 3225965) B3225965
theorem B4838957 : Blo 2149435 4838957 := bbase (se 3 (by rfl) ⟨907304, by rfl⟩ : syracuseStep 4838957 = 1814609) (by norm_num)
theorem B3225971 : Blo 2149435 3225971 := bstep (se 1 (by rfl) ⟨2419478, by rfl⟩ : syracuseStep 3225971 = 4838957) B4838957
theorem B2150647 : Blo 2149435 2150647 := bstep (se 1 (by rfl) ⟨1612985, by rfl⟩ : syracuseStep 2150647 = 3225971) B3225971
theorem B6207877 : Blo 2149435 6207877 := bbase (se 4 (by rfl) ⟨581988, by rfl⟩ : syracuseStep 6207877 = 1163977) (by norm_num)
theorem B8277169 : Blo 2149435 8277169 := bstep (se 2 (by rfl) ⟨3103938, by rfl⟩ : syracuseStep 8277169 = 6207877) B6207877
theorem B11036225 : Blo 2149435 11036225 := bstep (se 2 (by rfl) ⟨4138584, by rfl⟩ : syracuseStep 11036225 = 8277169) B8277169
theorem B7357483 : Blo 2149435 7357483 := bstep (se 1 (by rfl) ⟨5518112, by rfl⟩ : syracuseStep 7357483 = 11036225) B11036225
theorem B9809977 : Blo 2149435 9809977 := bstep (se 2 (by rfl) ⟨3678741, by rfl⟩ : syracuseStep 9809977 = 7357483) B7357483
theorem B13079969 : Blo 2149435 13079969 := bstep (se 2 (by rfl) ⟨4904988, by rfl⟩ : syracuseStep 13079969 = 9809977) B9809977
theorem B8719979 : Blo 2149435 8719979 := bstep (se 1 (by rfl) ⟨6539984, by rfl⟩ : syracuseStep 8719979 = 13079969) B13079969
theorem B23253277 : Blo 2149435 23253277 := bstep (se 3 (by rfl) ⟨4359989, by rfl⟩ : syracuseStep 23253277 = 8719979) B8719979
theorem B31004369 : Blo 2149435 31004369 := bstep (se 2 (by rfl) ⟨11626638, by rfl⟩ : syracuseStep 31004369 = 23253277) B23253277
theorem B20669579 : Blo 2149435 20669579 := bstep (se 1 (by rfl) ⟨15502184, by rfl⟩ : syracuseStep 20669579 = 31004369) B31004369
theorem B13779719 : Blo 2149435 13779719 := bstep (se 1 (by rfl) ⟨10334789, by rfl⟩ : syracuseStep 13779719 = 20669579) B20669579
theorem B9186479 : Blo 2149435 9186479 := bstep (se 1 (by rfl) ⟨6889859, by rfl⟩ : syracuseStep 9186479 = 13779719) B13779719
theorem B6124319 : Blo 2149435 6124319 := bstep (se 1 (by rfl) ⟨4593239, by rfl⟩ : syracuseStep 6124319 = 9186479) B9186479
theorem B4082879 : Blo 2149435 4082879 := bstep (se 1 (by rfl) ⟨3062159, by rfl⟩ : syracuseStep 4082879 = 6124319) B6124319
theorem B2721919 : Blo 2149435 2721919 := bstep (se 1 (by rfl) ⟨2041439, by rfl⟩ : syracuseStep 2721919 = 4082879) B4082879
theorem B3629225 : Blo 2149435 3629225 := bstep (se 2 (by rfl) ⟨1360959, by rfl⟩ : syracuseStep 3629225 = 2721919) B2721919
theorem B2419483 : Blo 2149435 2419483 := bstep (se 1 (by rfl) ⟨1814612, by rfl⟩ : syracuseStep 2419483 = 3629225) B3629225
theorem B3225977 : Blo 2149435 3225977 := bstep (se 2 (by rfl) ⟨1209741, by rfl⟩ : syracuseStep 3225977 = 2419483) B2419483
theorem B2150651 : Blo 2149435 2150651 := bstep (se 1 (by rfl) ⟨1612988, by rfl⟩ : syracuseStep 2150651 = 3225977) B3225977
theorem B4359997 : Blo 2149435 4359997 := bbase (se 3 (by rfl) ⟨817499, by rfl⟩ : syracuseStep 4359997 = 1634999) (by norm_num)
theorem B5813329 : Blo 2149435 5813329 := bstep (se 2 (by rfl) ⟨2179998, by rfl⟩ : syracuseStep 5813329 = 4359997) B4359997
theorem B7751105 : Blo 2149435 7751105 := bstep (se 2 (by rfl) ⟨2906664, by rfl⟩ : syracuseStep 7751105 = 5813329) B5813329
theorem B5167403 : Blo 2149435 5167403 := bstep (se 1 (by rfl) ⟨3875552, by rfl⟩ : syracuseStep 5167403 = 7751105) B7751105
theorem B3444935 : Blo 2149435 3444935 := bstep (se 1 (by rfl) ⟨2583701, by rfl⟩ : syracuseStep 3444935 = 5167403) B5167403
theorem B36745973 : Blo 2149435 36745973 := bstep (se 5 (by rfl) ⟨1722467, by rfl⟩ : syracuseStep 36745973 = 3444935) B3444935
theorem B24497315 : Blo 2149435 24497315 := bstep (se 1 (by rfl) ⟨18372986, by rfl⟩ : syracuseStep 24497315 = 36745973) B36745973
theorem B16331543 : Blo 2149435 16331543 := bstep (se 1 (by rfl) ⟨12248657, by rfl⟩ : syracuseStep 16331543 = 24497315) B24497315
theorem B10887695 : Blo 2149435 10887695 := bstep (se 1 (by rfl) ⟨8165771, by rfl⟩ : syracuseStep 10887695 = 16331543) B16331543
theorem B7258463 : Blo 2149435 7258463 := bstep (se 1 (by rfl) ⟨5443847, by rfl⟩ : syracuseStep 7258463 = 10887695) B10887695
theorem B4838975 : Blo 2149435 4838975 := bstep (se 1 (by rfl) ⟨3629231, by rfl⟩ : syracuseStep 4838975 = 7258463) B7258463
theorem B3225983 : Blo 2149435 3225983 := bstep (se 1 (by rfl) ⟨2419487, by rfl⟩ : syracuseStep 3225983 = 4838975) B4838975
theorem B2150655 : Blo 2149435 2150655 := bstep (se 1 (by rfl) ⟨1612991, by rfl⟩ : syracuseStep 2150655 = 3225983) B3225983
theorem B3225989 : Blo 2149435 3225989 := bbase (se 4 (by rfl) ⟨302436, by rfl⟩ : syracuseStep 3225989 = 604873) (by norm_num)
theorem B2150659 : Blo 2149435 2150659 := bstep (se 1 (by rfl) ⟨1612994, by rfl⟩ : syracuseStep 2150659 = 3225989) B3225989
theorem B3629245 : Blo 2149435 3629245 := bbase (se 3 (by rfl) ⟨680483, by rfl⟩ : syracuseStep 3629245 = 1360967) (by norm_num)
theorem B4838993 : Blo 2149435 4838993 := bstep (se 2 (by rfl) ⟨1814622, by rfl⟩ : syracuseStep 4838993 = 3629245) B3629245
theorem B3225995 : Blo 2149435 3225995 := bstep (se 1 (by rfl) ⟨2419496, by rfl⟩ : syracuseStep 3225995 = 4838993) B4838993
theorem B2150663 : Blo 2149435 2150663 := bstep (se 1 (by rfl) ⟨1612997, by rfl⟩ : syracuseStep 2150663 = 3225995) B3225995
theorem B2419501 : Blo 2149435 2419501 := bbase (se 3 (by rfl) ⟨453656, by rfl⟩ : syracuseStep 2419501 = 907313) (by norm_num)
theorem B3226001 : Blo 2149435 3226001 := bstep (se 2 (by rfl) ⟨1209750, by rfl⟩ : syracuseStep 3226001 = 2419501) B2419501
theorem B2150667 : Blo 2149435 2150667 := bstep (se 1 (by rfl) ⟨1613000, by rfl⟩ : syracuseStep 2150667 = 3226001) B3226001
theorem B7258517 : Blo 2149435 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B4839011 : Blo 2149435 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B3226007 : Blo 2149435 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B2150671 : Blo 2149435 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B3226013 : Blo 2149435 3226013 := bbase (se 3 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 3226013 = 1209755) (by norm_num)
theorem B2150675 : Blo 2149435 2150675 := bstep (se 1 (by rfl) ⟨1613006, by rfl⟩ : syracuseStep 2150675 = 3226013) B3226013
theorem B4839029 : Blo 2149435 4839029 := bbase (se 5 (by rfl) ⟨226829, by rfl⟩ : syracuseStep 4839029 = 453659) (by norm_num)
theorem B3226019 : Blo 2149435 3226019 := bstep (se 1 (by rfl) ⟨2419514, by rfl⟩ : syracuseStep 3226019 = 4839029) B4839029
theorem B2150679 : Blo 2149435 2150679 := bstep (se 1 (by rfl) ⟨1613009, by rfl⟩ : syracuseStep 2150679 = 3226019) B3226019
theorem B19620245 : Blo 2149435 19620245 := bbase (se 6 (by rfl) ⟨459849, by rfl⟩ : syracuseStep 19620245 = 919699) (by norm_num)
theorem B13080163 : Blo 2149435 13080163 := bstep (se 1 (by rfl) ⟨9810122, by rfl⟩ : syracuseStep 13080163 = 19620245) B19620245
theorem B17440217 : Blo 2149435 17440217 := bstep (se 2 (by rfl) ⟨6540081, by rfl⟩ : syracuseStep 17440217 = 13080163) B13080163
theorem B11626811 : Blo 2149435 11626811 := bstep (se 1 (by rfl) ⟨8720108, by rfl⟩ : syracuseStep 11626811 = 17440217) B17440217
theorem B7751207 : Blo 2149435 7751207 := bstep (se 1 (by rfl) ⟨5813405, by rfl⟩ : syracuseStep 7751207 = 11626811) B11626811
theorem B5167471 : Blo 2149435 5167471 := bstep (se 1 (by rfl) ⟨3875603, by rfl⟩ : syracuseStep 5167471 = 7751207) B7751207
theorem B6889961 : Blo 2149435 6889961 := bstep (se 2 (by rfl) ⟨2583735, by rfl⟩ : syracuseStep 6889961 = 5167471) B5167471
theorem B18373229 : Blo 2149435 18373229 := bstep (se 3 (by rfl) ⟨3444980, by rfl⟩ : syracuseStep 18373229 = 6889961) B6889961
theorem B12248819 : Blo 2149435 12248819 := bstep (se 1 (by rfl) ⟨9186614, by rfl⟩ : syracuseStep 12248819 = 18373229) B18373229
theorem B8165879 : Blo 2149435 8165879 := bstep (se 1 (by rfl) ⟨6124409, by rfl⟩ : syracuseStep 8165879 = 12248819) B12248819
theorem B5443919 : Blo 2149435 5443919 := bstep (se 1 (by rfl) ⟨4082939, by rfl⟩ : syracuseStep 5443919 = 8165879) B8165879
theorem B3629279 : Blo 2149435 3629279 := bstep (se 1 (by rfl) ⟨2721959, by rfl⟩ : syracuseStep 3629279 = 5443919) B5443919
theorem B2419519 : Blo 2149435 2419519 := bstep (se 1 (by rfl) ⟨1814639, by rfl⟩ : syracuseStep 2419519 = 3629279) B3629279
theorem B3226025 : Blo 2149435 3226025 := bstep (se 2 (by rfl) ⟨1209759, by rfl⟩ : syracuseStep 3226025 = 2419519) B2419519
theorem B2150683 : Blo 2149435 2150683 := bstep (se 1 (by rfl) ⟨1613012, by rfl⟩ : syracuseStep 2150683 = 3226025) B3226025
theorem B8165893 : Blo 2149435 8165893 := bbase (se 4 (by rfl) ⟨765552, by rfl⟩ : syracuseStep 8165893 = 1531105) (by norm_num)
theorem B10887857 : Blo 2149435 10887857 := bstep (se 2 (by rfl) ⟨4082946, by rfl⟩ : syracuseStep 10887857 = 8165893) B8165893
theorem B7258571 : Blo 2149435 7258571 := bstep (se 1 (by rfl) ⟨5443928, by rfl⟩ : syracuseStep 7258571 = 10887857) B10887857
theorem B4839047 : Blo 2149435 4839047 := bstep (se 1 (by rfl) ⟨3629285, by rfl⟩ : syracuseStep 4839047 = 7258571) B7258571
theorem B3226031 : Blo 2149435 3226031 := bstep (se 1 (by rfl) ⟨2419523, by rfl⟩ : syracuseStep 3226031 = 4839047) B4839047
theorem B2150687 : Blo 2149435 2150687 := bstep (se 1 (by rfl) ⟨1613015, by rfl⟩ : syracuseStep 2150687 = 3226031) B3226031
theorem B3226037 : Blo 2149435 3226037 := bbase (se 5 (by rfl) ⟨151220, by rfl⟩ : syracuseStep 3226037 = 302441) (by norm_num)
theorem B2150691 : Blo 2149435 2150691 := bstep (se 1 (by rfl) ⟨1613018, by rfl⟩ : syracuseStep 2150691 = 3226037) B3226037
theorem B5443949 : Blo 2149435 5443949 := bbase (se 3 (by rfl) ⟨1020740, by rfl⟩ : syracuseStep 5443949 = 2041481) (by norm_num)
theorem B3629299 : Blo 2149435 3629299 := bstep (se 1 (by rfl) ⟨2721974, by rfl⟩ : syracuseStep 3629299 = 5443949) B5443949
theorem B4839065 : Blo 2149435 4839065 := bstep (se 2 (by rfl) ⟨1814649, by rfl⟩ : syracuseStep 4839065 = 3629299) B3629299
theorem B3226043 : Blo 2149435 3226043 := bstep (se 1 (by rfl) ⟨2419532, by rfl⟩ : syracuseStep 3226043 = 4839065) B4839065
theorem B2150695 : Blo 2149435 2150695 := bstep (se 1 (by rfl) ⟨1613021, by rfl⟩ : syracuseStep 2150695 = 3226043) B3226043
theorem B2419537 : Blo 2149435 2419537 := bbase (se 2 (by rfl) ⟨907326, by rfl⟩ : syracuseStep 2419537 = 1814653) (by norm_num)
theorem B3226049 : Blo 2149435 3226049 := bstep (se 2 (by rfl) ⟨1209768, by rfl⟩ : syracuseStep 3226049 = 2419537) B2419537
theorem B2150699 : Blo 2149435 2150699 := bstep (se 1 (by rfl) ⟨1613024, by rfl⟩ : syracuseStep 2150699 = 3226049) B3226049
theorem B3445013 : Blo 2149435 3445013 := bbase (se 6 (by rfl) ⟨80742, by rfl⟩ : syracuseStep 3445013 = 161485) (by norm_num)
theorem B2296675 : Blo 2149435 2296675 := bstep (se 1 (by rfl) ⟨1722506, by rfl⟩ : syracuseStep 2296675 = 3445013) B3445013
theorem B3062233 : Blo 2149435 3062233 := bstep (se 2 (by rfl) ⟨1148337, by rfl⟩ : syracuseStep 3062233 = 2296675) B2296675
theorem B4082977 : Blo 2149435 4082977 := bstep (se 2 (by rfl) ⟨1531116, by rfl⟩ : syracuseStep 4082977 = 3062233) B3062233
theorem B5443969 : Blo 2149435 5443969 := bstep (se 2 (by rfl) ⟨2041488, by rfl⟩ : syracuseStep 5443969 = 4082977) B4082977
theorem B7258625 : Blo 2149435 7258625 := bstep (se 2 (by rfl) ⟨2721984, by rfl⟩ : syracuseStep 7258625 = 5443969) B5443969
theorem B4839083 : Blo 2149435 4839083 := bstep (se 1 (by rfl) ⟨3629312, by rfl⟩ : syracuseStep 4839083 = 7258625) B7258625
theorem B3226055 : Blo 2149435 3226055 := bstep (se 1 (by rfl) ⟨2419541, by rfl⟩ : syracuseStep 3226055 = 4839083) B4839083
theorem B2150703 : Blo 2149435 2150703 := bstep (se 1 (by rfl) ⟨1613027, by rfl⟩ : syracuseStep 2150703 = 3226055) B3226055
theorem B3226061 : Blo 2149435 3226061 := bbase (se 3 (by rfl) ⟨604886, by rfl⟩ : syracuseStep 3226061 = 1209773) (by norm_num)
theorem B2150707 : Blo 2149435 2150707 := bstep (se 1 (by rfl) ⟨1613030, by rfl⟩ : syracuseStep 2150707 = 3226061) B3226061
theorem B4839101 : Blo 2149435 4839101 := bbase (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) (by norm_num)
theorem B3226067 : Blo 2149435 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B2150711 : Blo 2149435 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B3629333 : Blo 2149435 3629333 := bbase (se 6 (by rfl) ⟨85062, by rfl⟩ : syracuseStep 3629333 = 170125) (by norm_num)
theorem B2419555 : Blo 2149435 2419555 := bstep (se 1 (by rfl) ⟨1814666, by rfl⟩ : syracuseStep 2419555 = 3629333) B3629333
theorem B3226073 : Blo 2149435 3226073 := bstep (se 2 (by rfl) ⟨1209777, by rfl⟩ : syracuseStep 3226073 = 2419555) B2419555
theorem B2150715 : Blo 2149435 2150715 := bstep (se 1 (by rfl) ⟨1613036, by rfl⟩ : syracuseStep 2150715 = 3226073) B3226073
theorem B22073141 : Blo 2149435 22073141 := bbase (se 5 (by rfl) ⟨1034678, by rfl⟩ : syracuseStep 22073141 = 2069357) (by norm_num)
theorem B14715427 : Blo 2149435 14715427 := bstep (se 1 (by rfl) ⟨11036570, by rfl⟩ : syracuseStep 14715427 = 22073141) B22073141
theorem B19620569 : Blo 2149435 19620569 := bstep (se 2 (by rfl) ⟨7357713, by rfl⟩ : syracuseStep 19620569 = 14715427) B14715427
theorem B13080379 : Blo 2149435 13080379 := bstep (se 1 (by rfl) ⟨9810284, by rfl⟩ : syracuseStep 13080379 = 19620569) B19620569
theorem B17440505 : Blo 2149435 17440505 := bstep (se 2 (by rfl) ⟨6540189, by rfl⟩ : syracuseStep 17440505 = 13080379) B13080379
theorem B11627003 : Blo 2149435 11627003 := bstep (se 1 (by rfl) ⟨8720252, by rfl⟩ : syracuseStep 11627003 = 17440505) B17440505
theorem B31005341 : Blo 2149435 31005341 := bstep (se 3 (by rfl) ⟨5813501, by rfl⟩ : syracuseStep 31005341 = 11627003) B11627003
theorem B20670227 : Blo 2149435 20670227 := bstep (se 1 (by rfl) ⟨15502670, by rfl⟩ : syracuseStep 20670227 = 31005341) B31005341
theorem B13780151 : Blo 2149435 13780151 := bstep (se 1 (by rfl) ⟨10335113, by rfl⟩ : syracuseStep 13780151 = 20670227) B20670227
theorem B9186767 : Blo 2149435 9186767 := bstep (se 1 (by rfl) ⟨6890075, by rfl⟩ : syracuseStep 9186767 = 13780151) B13780151
theorem B6124511 : Blo 2149435 6124511 := bstep (se 1 (by rfl) ⟨4593383, by rfl⟩ : syracuseStep 6124511 = 9186767) B9186767
theorem B16332029 : Blo 2149435 16332029 := bstep (se 3 (by rfl) ⟨3062255, by rfl⟩ : syracuseStep 16332029 = 6124511) B6124511
theorem B10888019 : Blo 2149435 10888019 := bstep (se 1 (by rfl) ⟨8166014, by rfl⟩ : syracuseStep 10888019 = 16332029) B16332029
theorem B7258679 : Blo 2149435 7258679 := bstep (se 1 (by rfl) ⟨5444009, by rfl⟩ : syracuseStep 7258679 = 10888019) B10888019
theorem B4839119 : Blo 2149435 4839119 := bstep (se 1 (by rfl) ⟨3629339, by rfl⟩ : syracuseStep 4839119 = 7258679) B7258679
theorem B3226079 : Blo 2149435 3226079 := bstep (se 1 (by rfl) ⟨2419559, by rfl⟩ : syracuseStep 3226079 = 4839119) B4839119
theorem B2150719 : Blo 2149435 2150719 := bstep (se 1 (by rfl) ⟨1613039, by rfl⟩ : syracuseStep 2150719 = 3226079) B3226079
theorem B3226085 : Blo 2149435 3226085 := bbase (se 4 (by rfl) ⟨302445, by rfl⟩ : syracuseStep 3226085 = 604891) (by norm_num)
theorem B2150723 : Blo 2149435 2150723 := bstep (se 1 (by rfl) ⟨1613042, by rfl⟩ : syracuseStep 2150723 = 3226085) B3226085
theorem B5813525 : Blo 2149435 5813525 := bbase (se 6 (by rfl) ⟨136254, by rfl⟩ : syracuseStep 5813525 = 272509) (by norm_num)
theorem B3875683 : Blo 2149435 3875683 := bstep (se 1 (by rfl) ⟨2906762, by rfl⟩ : syracuseStep 3875683 = 5813525) B5813525
theorem B5167577 : Blo 2149435 5167577 := bstep (se 2 (by rfl) ⟨1937841, by rfl⟩ : syracuseStep 5167577 = 3875683) B3875683
theorem B13780205 : Blo 2149435 13780205 := bstep (se 3 (by rfl) ⟨2583788, by rfl⟩ : syracuseStep 13780205 = 5167577) B5167577
theorem B9186803 : Blo 2149435 9186803 := bstep (se 1 (by rfl) ⟨6890102, by rfl⟩ : syracuseStep 9186803 = 13780205) B13780205
theorem B6124535 : Blo 2149435 6124535 := bstep (se 1 (by rfl) ⟨4593401, by rfl⟩ : syracuseStep 6124535 = 9186803) B9186803
theorem B4083023 : Blo 2149435 4083023 := bstep (se 1 (by rfl) ⟨3062267, by rfl⟩ : syracuseStep 4083023 = 6124535) B6124535
theorem B2722015 : Blo 2149435 2722015 := bstep (se 1 (by rfl) ⟨2041511, by rfl⟩ : syracuseStep 2722015 = 4083023) B4083023
theorem B3629353 : Blo 2149435 3629353 := bstep (se 2 (by rfl) ⟨1361007, by rfl⟩ : syracuseStep 3629353 = 2722015) B2722015
theorem B4839137 : Blo 2149435 4839137 := bstep (se 2 (by rfl) ⟨1814676, by rfl⟩ : syracuseStep 4839137 = 3629353) B3629353
theorem B3226091 : Blo 2149435 3226091 := bstep (se 1 (by rfl) ⟨2419568, by rfl⟩ : syracuseStep 3226091 = 4839137) B4839137
theorem B2150727 : Blo 2149435 2150727 := bstep (se 1 (by rfl) ⟨1613045, by rfl⟩ : syracuseStep 2150727 = 3226091) B3226091
theorem B2419573 : Blo 2149435 2419573 := bbase (se 5 (by rfl) ⟨113417, by rfl⟩ : syracuseStep 2419573 = 226835) (by norm_num)
theorem B3226097 : Blo 2149435 3226097 := bstep (se 2 (by rfl) ⟨1209786, by rfl⟩ : syracuseStep 3226097 = 2419573) B2419573
theorem B2150731 : Blo 2149435 2150731 := bstep (se 1 (by rfl) ⟨1613048, by rfl⟩ : syracuseStep 2150731 = 3226097) B3226097
theorem B2722025 : Blo 2149435 2722025 := bbase (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) (by norm_num)
theorem B7258733 : Blo 2149435 7258733 := bstep (se 3 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 7258733 = 2722025) B2722025
theorem B4839155 : Blo 2149435 4839155 := bstep (se 1 (by rfl) ⟨3629366, by rfl⟩ : syracuseStep 4839155 = 7258733) B7258733
theorem B3226103 : Blo 2149435 3226103 := bstep (se 1 (by rfl) ⟨2419577, by rfl⟩ : syracuseStep 3226103 = 4839155) B4839155
theorem B2150735 : Blo 2149435 2150735 := bstep (se 1 (by rfl) ⟨1613051, by rfl⟩ : syracuseStep 2150735 = 3226103) B3226103
theorem B3226109 : Blo 2149435 3226109 := bbase (se 3 (by rfl) ⟨604895, by rfl⟩ : syracuseStep 3226109 = 1209791) (by norm_num)
theorem B2150739 : Blo 2149435 2150739 := bstep (se 1 (by rfl) ⟨1613054, by rfl⟩ : syracuseStep 2150739 = 3226109) B3226109
theorem B4839173 : Blo 2149435 4839173 := bbase (se 4 (by rfl) ⟨453672, by rfl⟩ : syracuseStep 4839173 = 907345) (by norm_num)
theorem B3226115 : Blo 2149435 3226115 := bstep (se 1 (by rfl) ⟨2419586, by rfl⟩ : syracuseStep 3226115 = 4839173) B4839173
theorem B2150743 : Blo 2149435 2150743 := bstep (se 1 (by rfl) ⟨1613057, by rfl⟩ : syracuseStep 2150743 = 3226115) B3226115
theorem B4083061 : Blo 2149435 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B5444081 : Blo 2149435 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B3629387 : Blo 2149435 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B2419591 : Blo 2149435 2419591 := bstep (se 1 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 2419591 = 3629387) B3629387
theorem B3226121 : Blo 2149435 3226121 := bstep (se 2 (by rfl) ⟨1209795, by rfl⟩ : syracuseStep 3226121 = 2419591) B2419591
theorem B2150747 : Blo 2149435 2150747 := bstep (se 1 (by rfl) ⟨1613060, by rfl⟩ : syracuseStep 2150747 = 3226121) B3226121
theorem B10888181 : Blo 2149435 10888181 := bbase (se 5 (by rfl) ⟨510383, by rfl⟩ : syracuseStep 10888181 = 1020767) (by norm_num)
theorem B7258787 : Blo 2149435 7258787 := bstep (se 1 (by rfl) ⟨5444090, by rfl⟩ : syracuseStep 7258787 = 10888181) B10888181
theorem B4839191 : Blo 2149435 4839191 := bstep (se 1 (by rfl) ⟨3629393, by rfl⟩ : syracuseStep 4839191 = 7258787) B7258787
theorem B3226127 : Blo 2149435 3226127 := bstep (se 1 (by rfl) ⟨2419595, by rfl⟩ : syracuseStep 3226127 = 4839191) B4839191
theorem B2150751 : Blo 2149435 2150751 := bstep (se 1 (by rfl) ⟨1613063, by rfl⟩ : syracuseStep 2150751 = 3226127) B3226127
theorem B3226133 : Blo 2149435 3226133 := bbase (se 6 (by rfl) ⟨75612, by rfl⟩ : syracuseStep 3226133 = 151225) (by norm_num)
theorem B2150755 : Blo 2149435 2150755 := bstep (se 1 (by rfl) ⟨1613066, by rfl⟩ : syracuseStep 2150755 = 3226133) B3226133
theorem B18373877 : Blo 2149435 18373877 := bbase (se 5 (by rfl) ⟨861275, by rfl⟩ : syracuseStep 18373877 = 1722551) (by norm_num)
theorem B12249251 : Blo 2149435 12249251 := bstep (se 1 (by rfl) ⟨9186938, by rfl⟩ : syracuseStep 12249251 = 18373877) B18373877
theorem B8166167 : Blo 2149435 8166167 := bstep (se 1 (by rfl) ⟨6124625, by rfl⟩ : syracuseStep 8166167 = 12249251) B12249251
theorem B5444111 : Blo 2149435 5444111 := bstep (se 1 (by rfl) ⟨4083083, by rfl⟩ : syracuseStep 5444111 = 8166167) B8166167
theorem B3629407 : Blo 2149435 3629407 := bstep (se 1 (by rfl) ⟨2722055, by rfl⟩ : syracuseStep 3629407 = 5444111) B5444111
theorem B4839209 : Blo 2149435 4839209 := bstep (se 2 (by rfl) ⟨1814703, by rfl⟩ : syracuseStep 4839209 = 3629407) B3629407
theorem B3226139 : Blo 2149435 3226139 := bstep (se 1 (by rfl) ⟨2419604, by rfl⟩ : syracuseStep 3226139 = 4839209) B4839209
theorem B2150759 : Blo 2149435 2150759 := bstep (se 1 (by rfl) ⟨1613069, by rfl⟩ : syracuseStep 2150759 = 3226139) B3226139
theorem B2419609 : Blo 2149435 2419609 := bbase (se 2 (by rfl) ⟨907353, by rfl⟩ : syracuseStep 2419609 = 1814707) (by norm_num)
theorem B3226145 : Blo 2149435 3226145 := bstep (se 2 (by rfl) ⟨1209804, by rfl⟩ : syracuseStep 3226145 = 2419609) B2419609
theorem B2150763 : Blo 2149435 2150763 := bstep (se 1 (by rfl) ⟨1613072, by rfl⟩ : syracuseStep 2150763 = 3226145) B3226145
theorem B8166197 : Blo 2149435 8166197 := bbase (se 5 (by rfl) ⟨382790, by rfl⟩ : syracuseStep 8166197 = 765581) (by norm_num)
theorem B5444131 : Blo 2149435 5444131 := bstep (se 1 (by rfl) ⟨4083098, by rfl⟩ : syracuseStep 5444131 = 8166197) B8166197
theorem B7258841 : Blo 2149435 7258841 := bstep (se 2 (by rfl) ⟨2722065, by rfl⟩ : syracuseStep 7258841 = 5444131) B5444131
theorem B4839227 : Blo 2149435 4839227 := bstep (se 1 (by rfl) ⟨3629420, by rfl⟩ : syracuseStep 4839227 = 7258841) B7258841
theorem B3226151 : Blo 2149435 3226151 := bstep (se 1 (by rfl) ⟨2419613, by rfl⟩ : syracuseStep 3226151 = 4839227) B4839227
theorem B2150767 : Blo 2149435 2150767 := bstep (se 1 (by rfl) ⟨1613075, by rfl⟩ : syracuseStep 2150767 = 3226151) B3226151
theorem B3226157 : Blo 2149435 3226157 := bbase (se 3 (by rfl) ⟨604904, by rfl⟩ : syracuseStep 3226157 = 1209809) (by norm_num)
theorem B2150771 : Blo 2149435 2150771 := bstep (se 1 (by rfl) ⟨1613078, by rfl⟩ : syracuseStep 2150771 = 3226157) B3226157
theorem B4839245 : Blo 2149435 4839245 := bbase (se 3 (by rfl) ⟨907358, by rfl⟩ : syracuseStep 4839245 = 1814717) (by norm_num)
theorem B3226163 : Blo 2149435 3226163 := bstep (se 1 (by rfl) ⟨2419622, by rfl⟩ : syracuseStep 3226163 = 4839245) B4839245
theorem B2150775 : Blo 2149435 2150775 := bstep (se 1 (by rfl) ⟨1613081, by rfl⟩ : syracuseStep 2150775 = 3226163) B3226163
theorem B2722081 : Blo 2149435 2722081 := bbase (se 2 (by rfl) ⟨1020780, by rfl⟩ : syracuseStep 2722081 = 2041561) (by norm_num)
theorem B3629441 : Blo 2149435 3629441 := bstep (se 2 (by rfl) ⟨1361040, by rfl⟩ : syracuseStep 3629441 = 2722081) B2722081
theorem B2419627 : Blo 2149435 2419627 := bstep (se 1 (by rfl) ⟨1814720, by rfl⟩ : syracuseStep 2419627 = 3629441) B3629441
theorem B3226169 : Blo 2149435 3226169 := bstep (se 2 (by rfl) ⟨1209813, by rfl⟩ : syracuseStep 3226169 = 2419627) B2419627
theorem B2150779 : Blo 2149435 2150779 := bstep (se 1 (by rfl) ⟨1613084, by rfl⟩ : syracuseStep 2150779 = 3226169) B3226169
theorem B24498773 : Blo 2149435 24498773 := bbase (se 8 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 24498773 = 287095) (by norm_num)
theorem B16332515 : Blo 2149435 16332515 := bstep (se 1 (by rfl) ⟨12249386, by rfl⟩ : syracuseStep 16332515 = 24498773) B24498773
theorem B10888343 : Blo 2149435 10888343 := bstep (se 1 (by rfl) ⟨8166257, by rfl⟩ : syracuseStep 10888343 = 16332515) B16332515
theorem B7258895 : Blo 2149435 7258895 := bstep (se 1 (by rfl) ⟨5444171, by rfl⟩ : syracuseStep 7258895 = 10888343) B10888343
theorem B4839263 : Blo 2149435 4839263 := bstep (se 1 (by rfl) ⟨3629447, by rfl⟩ : syracuseStep 4839263 = 7258895) B7258895
theorem B3226175 : Blo 2149435 3226175 := bstep (se 1 (by rfl) ⟨2419631, by rfl⟩ : syracuseStep 3226175 = 4839263) B4839263
theorem B2150783 : Blo 2149435 2150783 := bstep (se 1 (by rfl) ⟨1613087, by rfl⟩ : syracuseStep 2150783 = 3226175) B3226175
theorem B3226181 : Blo 2149435 3226181 := bbase (se 4 (by rfl) ⟨302454, by rfl⟩ : syracuseStep 3226181 = 604909) (by norm_num)
theorem B2150787 : Blo 2149435 2150787 := bstep (se 1 (by rfl) ⟨1613090, by rfl⟩ : syracuseStep 2150787 = 3226181) B3226181
theorem B3629461 : Blo 2149435 3629461 := bbase (se 6 (by rfl) ⟨85065, by rfl⟩ : syracuseStep 3629461 = 170131) (by norm_num)
theorem B4839281 : Blo 2149435 4839281 := bstep (se 2 (by rfl) ⟨1814730, by rfl⟩ : syracuseStep 4839281 = 3629461) B3629461
theorem B3226187 : Blo 2149435 3226187 := bstep (se 1 (by rfl) ⟨2419640, by rfl⟩ : syracuseStep 3226187 = 4839281) B4839281
theorem B2150791 : Blo 2149435 2150791 := bstep (se 1 (by rfl) ⟨1613093, by rfl⟩ : syracuseStep 2150791 = 3226187) B3226187
theorem B2419645 : Blo 2149435 2419645 := bbase (se 3 (by rfl) ⟨453683, by rfl⟩ : syracuseStep 2419645 = 907367) (by norm_num)
theorem B3226193 : Blo 2149435 3226193 := bstep (se 2 (by rfl) ⟨1209822, by rfl⟩ : syracuseStep 3226193 = 2419645) B2419645
theorem B2150795 : Blo 2149435 2150795 := bstep (se 1 (by rfl) ⟨1613096, by rfl⟩ : syracuseStep 2150795 = 3226193) B3226193
theorem B7258949 : Blo 2149435 7258949 := bbase (se 4 (by rfl) ⟨680526, by rfl⟩ : syracuseStep 7258949 = 1361053) (by norm_num)
theorem B4839299 : Blo 2149435 4839299 := bstep (se 1 (by rfl) ⟨3629474, by rfl⟩ : syracuseStep 4839299 = 7258949) B7258949
theorem B3226199 : Blo 2149435 3226199 := bstep (se 1 (by rfl) ⟨2419649, by rfl⟩ : syracuseStep 3226199 = 4839299) B4839299
theorem B2150799 : Blo 2149435 2150799 := bstep (se 1 (by rfl) ⟨1613099, by rfl⟩ : syracuseStep 2150799 = 3226199) B3226199
theorem B3226205 : Blo 2149435 3226205 := bbase (se 3 (by rfl) ⟨604913, by rfl⟩ : syracuseStep 3226205 = 1209827) (by norm_num)
theorem B2150803 : Blo 2149435 2150803 := bstep (se 1 (by rfl) ⟨1613102, by rfl⟩ : syracuseStep 2150803 = 3226205) B3226205
theorem B4839317 : Blo 2149435 4839317 := bbase (se 6 (by rfl) ⟨113421, by rfl⟩ : syracuseStep 4839317 = 226843) (by norm_num)
theorem B3226211 : Blo 2149435 3226211 := bstep (se 1 (by rfl) ⟨2419658, by rfl⟩ : syracuseStep 3226211 = 4839317) B4839317
theorem B2150807 : Blo 2149435 2150807 := bstep (se 1 (by rfl) ⟨1613105, by rfl⟩ : syracuseStep 2150807 = 3226211) B3226211
theorem B4593581 : Blo 2149435 4593581 := bbase (se 3 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 4593581 = 1722593) (by norm_num)
theorem B3062387 : Blo 2149435 3062387 := bstep (se 1 (by rfl) ⟨2296790, by rfl⟩ : syracuseStep 3062387 = 4593581) B4593581
theorem B8166365 : Blo 2149435 8166365 := bstep (se 3 (by rfl) ⟨1531193, by rfl⟩ : syracuseStep 8166365 = 3062387) B3062387
theorem B5444243 : Blo 2149435 5444243 := bstep (se 1 (by rfl) ⟨4083182, by rfl⟩ : syracuseStep 5444243 = 8166365) B8166365
theorem B3629495 : Blo 2149435 3629495 := bstep (se 1 (by rfl) ⟨2722121, by rfl⟩ : syracuseStep 3629495 = 5444243) B5444243
theorem B2419663 : Blo 2149435 2419663 := bstep (se 1 (by rfl) ⟨1814747, by rfl⟩ : syracuseStep 2419663 = 3629495) B3629495
theorem B3226217 : Blo 2149435 3226217 := bstep (se 2 (by rfl) ⟨1209831, by rfl⟩ : syracuseStep 3226217 = 2419663) B2419663
theorem B2150811 : Blo 2149435 2150811 := bstep (se 1 (by rfl) ⟨1613108, by rfl⟩ : syracuseStep 2150811 = 3226217) B3226217
theorem B2452681 : Blo 2149435 2452681 := bbase (se 2 (by rfl) ⟨919755, by rfl⟩ : syracuseStep 2452681 = 1839511) (by norm_num)
theorem B3270241 : Blo 2149435 3270241 := bstep (se 2 (by rfl) ⟨1226340, by rfl⟩ : syracuseStep 3270241 = 2452681) B2452681
theorem B4360321 : Blo 2149435 4360321 := bstep (se 2 (by rfl) ⟨1635120, by rfl⟩ : syracuseStep 4360321 = 3270241) B3270241
theorem B23255045 : Blo 2149435 23255045 := bstep (se 4 (by rfl) ⟨2180160, by rfl⟩ : syracuseStep 23255045 = 4360321) B4360321
theorem B15503363 : Blo 2149435 15503363 := bstep (se 1 (by rfl) ⟨11627522, by rfl⟩ : syracuseStep 15503363 = 23255045) B23255045
theorem B10335575 : Blo 2149435 10335575 := bstep (se 1 (by rfl) ⟨7751681, by rfl⟩ : syracuseStep 10335575 = 15503363) B15503363
theorem B6890383 : Blo 2149435 6890383 := bstep (se 1 (by rfl) ⟨5167787, by rfl⟩ : syracuseStep 6890383 = 10335575) B10335575
theorem B9187177 : Blo 2149435 9187177 := bstep (se 2 (by rfl) ⟨3445191, by rfl⟩ : syracuseStep 9187177 = 6890383) B6890383
theorem B12249569 : Blo 2149435 12249569 := bstep (se 2 (by rfl) ⟨4593588, by rfl⟩ : syracuseStep 12249569 = 9187177) B9187177
theorem B8166379 : Blo 2149435 8166379 := bstep (se 1 (by rfl) ⟨6124784, by rfl⟩ : syracuseStep 8166379 = 12249569) B12249569
theorem B10888505 : Blo 2149435 10888505 := bstep (se 2 (by rfl) ⟨4083189, by rfl⟩ : syracuseStep 10888505 = 8166379) B8166379
theorem B7259003 : Blo 2149435 7259003 := bstep (se 1 (by rfl) ⟨5444252, by rfl⟩ : syracuseStep 7259003 = 10888505) B10888505
theorem B4839335 : Blo 2149435 4839335 := bstep (se 1 (by rfl) ⟨3629501, by rfl⟩ : syracuseStep 4839335 = 7259003) B7259003
theorem B3226223 : Blo 2149435 3226223 := bstep (se 1 (by rfl) ⟨2419667, by rfl⟩ : syracuseStep 3226223 = 4839335) B4839335
theorem B2150815 : Blo 2149435 2150815 := bstep (se 1 (by rfl) ⟨1613111, by rfl⟩ : syracuseStep 2150815 = 3226223) B3226223
theorem B3226229 : Blo 2149435 3226229 := bbase (se 5 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 3226229 = 302459) (by norm_num)
theorem B2150819 : Blo 2149435 2150819 := bstep (se 1 (by rfl) ⟨1613114, by rfl⟩ : syracuseStep 2150819 = 3226229) B3226229
theorem B4083205 : Blo 2149435 4083205 := bbase (se 4 (by rfl) ⟨382800, by rfl⟩ : syracuseStep 4083205 = 765601) (by norm_num)
theorem B5444273 : Blo 2149435 5444273 := bstep (se 2 (by rfl) ⟨2041602, by rfl⟩ : syracuseStep 5444273 = 4083205) B4083205
theorem B3629515 : Blo 2149435 3629515 := bstep (se 1 (by rfl) ⟨2722136, by rfl⟩ : syracuseStep 3629515 = 5444273) B5444273
theorem B4839353 : Blo 2149435 4839353 := bstep (se 2 (by rfl) ⟨1814757, by rfl⟩ : syracuseStep 4839353 = 3629515) B3629515
theorem B3226235 : Blo 2149435 3226235 := bstep (se 1 (by rfl) ⟨2419676, by rfl⟩ : syracuseStep 3226235 = 4839353) B4839353
theorem B2150823 : Blo 2149435 2150823 := bstep (se 1 (by rfl) ⟨1613117, by rfl⟩ : syracuseStep 2150823 = 3226235) B3226235
theorem B2419681 : Blo 2149435 2419681 := bbase (se 2 (by rfl) ⟨907380, by rfl⟩ : syracuseStep 2419681 = 1814761) (by norm_num)
theorem B3226241 : Blo 2149435 3226241 := bstep (se 2 (by rfl) ⟨1209840, by rfl⟩ : syracuseStep 3226241 = 2419681) B2419681
theorem B2150827 : Blo 2149435 2150827 := bstep (se 1 (by rfl) ⟨1613120, by rfl⟩ : syracuseStep 2150827 = 3226241) B3226241
theorem B5444293 : Blo 2149435 5444293 := bbase (se 4 (by rfl) ⟨510402, by rfl⟩ : syracuseStep 5444293 = 1020805) (by norm_num)
theorem B7259057 : Blo 2149435 7259057 := bstep (se 2 (by rfl) ⟨2722146, by rfl⟩ : syracuseStep 7259057 = 5444293) B5444293
theorem B4839371 : Blo 2149435 4839371 := bstep (se 1 (by rfl) ⟨3629528, by rfl⟩ : syracuseStep 4839371 = 7259057) B7259057
theorem B3226247 : Blo 2149435 3226247 := bstep (se 1 (by rfl) ⟨2419685, by rfl⟩ : syracuseStep 3226247 = 4839371) B4839371
theorem B2150831 : Blo 2149435 2150831 := bstep (se 1 (by rfl) ⟨1613123, by rfl⟩ : syracuseStep 2150831 = 3226247) B3226247
theorem B3226253 : Blo 2149435 3226253 := bbase (se 3 (by rfl) ⟨604922, by rfl⟩ : syracuseStep 3226253 = 1209845) (by norm_num)
theorem B2150835 : Blo 2149435 2150835 := bstep (se 1 (by rfl) ⟨1613126, by rfl⟩ : syracuseStep 2150835 = 3226253) B3226253
theorem B4839389 : Blo 2149435 4839389 := bbase (se 3 (by rfl) ⟨907385, by rfl⟩ : syracuseStep 4839389 = 1814771) (by norm_num)
theorem B3226259 : Blo 2149435 3226259 := bstep (se 1 (by rfl) ⟨2419694, by rfl⟩ : syracuseStep 3226259 = 4839389) B4839389
theorem B2150839 : Blo 2149435 2150839 := bstep (se 1 (by rfl) ⟨1613129, by rfl⟩ : syracuseStep 2150839 = 3226259) B3226259
theorem B3629549 : Blo 2149435 3629549 := bbase (se 3 (by rfl) ⟨680540, by rfl⟩ : syracuseStep 3629549 = 1361081) (by norm_num)
theorem B2419699 : Blo 2149435 2419699 := bstep (se 1 (by rfl) ⟨1814774, by rfl⟩ : syracuseStep 2419699 = 3629549) B3629549
theorem B3226265 : Blo 2149435 3226265 := bstep (se 2 (by rfl) ⟨1209849, by rfl⟩ : syracuseStep 3226265 = 2419699) B2419699
theorem B2150843 : Blo 2149435 2150843 := bstep (se 1 (by rfl) ⟨1613132, by rfl⟩ : syracuseStep 2150843 = 3226265) B3226265
theorem B27561941 : Blo 2149435 27561941 := bbase (se 7 (by rfl) ⟨322991, by rfl⟩ : syracuseStep 27561941 = 645983) (by norm_num)
theorem B18374627 : Blo 2149435 18374627 := bstep (se 1 (by rfl) ⟨13780970, by rfl⟩ : syracuseStep 18374627 = 27561941) B27561941
theorem B12249751 : Blo 2149435 12249751 := bstep (se 1 (by rfl) ⟨9187313, by rfl⟩ : syracuseStep 12249751 = 18374627) B18374627
theorem B16333001 : Blo 2149435 16333001 := bstep (se 2 (by rfl) ⟨6124875, by rfl⟩ : syracuseStep 16333001 = 12249751) B12249751
theorem B10888667 : Blo 2149435 10888667 := bstep (se 1 (by rfl) ⟨8166500, by rfl⟩ : syracuseStep 10888667 = 16333001) B16333001
theorem B7259111 : Blo 2149435 7259111 := bstep (se 1 (by rfl) ⟨5444333, by rfl⟩ : syracuseStep 7259111 = 10888667) B10888667
theorem B4839407 : Blo 2149435 4839407 := bstep (se 1 (by rfl) ⟨3629555, by rfl⟩ : syracuseStep 4839407 = 7259111) B7259111
theorem B3226271 : Blo 2149435 3226271 := bstep (se 1 (by rfl) ⟨2419703, by rfl⟩ : syracuseStep 3226271 = 4839407) B4839407
theorem B2150847 : Blo 2149435 2150847 := bstep (se 1 (by rfl) ⟨1613135, by rfl⟩ : syracuseStep 2150847 = 3226271) B3226271
theorem B3226277 : Blo 2149435 3226277 := bbase (se 4 (by rfl) ⟨302463, by rfl⟩ : syracuseStep 3226277 = 604927) (by norm_num)
theorem B2150851 : Blo 2149435 2150851 := bstep (se 1 (by rfl) ⟨1613138, by rfl⟩ : syracuseStep 2150851 = 3226277) B3226277
theorem B2722177 : Blo 2149435 2722177 := bbase (se 2 (by rfl) ⟨1020816, by rfl⟩ : syracuseStep 2722177 = 2041633) (by norm_num)
theorem B3629569 : Blo 2149435 3629569 := bstep (se 2 (by rfl) ⟨1361088, by rfl⟩ : syracuseStep 3629569 = 2722177) B2722177
theorem B4839425 : Blo 2149435 4839425 := bstep (se 2 (by rfl) ⟨1814784, by rfl⟩ : syracuseStep 4839425 = 3629569) B3629569
theorem B3226283 : Blo 2149435 3226283 := bstep (se 1 (by rfl) ⟨2419712, by rfl⟩ : syracuseStep 3226283 = 4839425) B4839425
theorem B2150855 : Blo 2149435 2150855 := bstep (se 1 (by rfl) ⟨1613141, by rfl⟩ : syracuseStep 2150855 = 3226283) B3226283
theorem B2419717 : Blo 2149435 2419717 := bbase (se 4 (by rfl) ⟨226848, by rfl⟩ : syracuseStep 2419717 = 453697) (by norm_num)
theorem B3226289 : Blo 2149435 3226289 := bstep (se 2 (by rfl) ⟨1209858, by rfl⟩ : syracuseStep 3226289 = 2419717) B2419717
theorem B2150859 : Blo 2149435 2150859 := bstep (se 1 (by rfl) ⟨1613144, by rfl⟩ : syracuseStep 2150859 = 3226289) B3226289
theorem B3062461 : Blo 2149435 3062461 := bbase (se 3 (by rfl) ⟨574211, by rfl⟩ : syracuseStep 3062461 = 1148423) (by norm_num)
theorem B4083281 : Blo 2149435 4083281 := bstep (se 2 (by rfl) ⟨1531230, by rfl⟩ : syracuseStep 4083281 = 3062461) B3062461
theorem B2722187 : Blo 2149435 2722187 := bstep (se 1 (by rfl) ⟨2041640, by rfl⟩ : syracuseStep 2722187 = 4083281) B4083281
theorem B7259165 : Blo 2149435 7259165 := bstep (se 3 (by rfl) ⟨1361093, by rfl⟩ : syracuseStep 7259165 = 2722187) B2722187
theorem B4839443 : Blo 2149435 4839443 := bstep (se 1 (by rfl) ⟨3629582, by rfl⟩ : syracuseStep 4839443 = 7259165) B7259165
theorem B3226295 : Blo 2149435 3226295 := bstep (se 1 (by rfl) ⟨2419721, by rfl⟩ : syracuseStep 3226295 = 4839443) B4839443
theorem B2150863 : Blo 2149435 2150863 := bstep (se 1 (by rfl) ⟨1613147, by rfl⟩ : syracuseStep 2150863 = 3226295) B3226295
theorem B3226301 : Blo 2149435 3226301 := bbase (se 3 (by rfl) ⟨604931, by rfl⟩ : syracuseStep 3226301 = 1209863) (by norm_num)
theorem B2150867 : Blo 2149435 2150867 := bstep (se 1 (by rfl) ⟨1613150, by rfl⟩ : syracuseStep 2150867 = 3226301) B3226301
theorem B4839461 : Blo 2149435 4839461 := bbase (se 4 (by rfl) ⟨453699, by rfl⟩ : syracuseStep 4839461 = 907399) (by norm_num)
theorem B3226307 : Blo 2149435 3226307 := bstep (se 1 (by rfl) ⟨2419730, by rfl⟩ : syracuseStep 3226307 = 4839461) B4839461
theorem B2150871 : Blo 2149435 2150871 := bstep (se 1 (by rfl) ⟨1613153, by rfl⟩ : syracuseStep 2150871 = 3226307) B3226307
theorem B5444405 : Blo 2149435 5444405 := bbase (se 5 (by rfl) ⟨255206, by rfl⟩ : syracuseStep 5444405 = 510413) (by norm_num)
theorem B3629603 : Blo 2149435 3629603 := bstep (se 1 (by rfl) ⟨2722202, by rfl⟩ : syracuseStep 3629603 = 5444405) B5444405
theorem B2419735 : Blo 2149435 2419735 := bstep (se 1 (by rfl) ⟨1814801, by rfl⟩ : syracuseStep 2419735 = 3629603) B3629603
theorem B3226313 : Blo 2149435 3226313 := bstep (se 2 (by rfl) ⟨1209867, by rfl⟩ : syracuseStep 3226313 = 2419735) B2419735
theorem B2150875 : Blo 2149435 2150875 := bstep (se 1 (by rfl) ⟨1613156, by rfl⟩ : syracuseStep 2150875 = 3226313) B3226313
theorem B6540677 : Blo 2149435 6540677 := bbase (se 4 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 6540677 = 1226377) (by norm_num)
theorem B4360451 : Blo 2149435 4360451 := bstep (se 1 (by rfl) ⟨3270338, by rfl⟩ : syracuseStep 4360451 = 6540677) B6540677
theorem B11627869 : Blo 2149435 11627869 := bstep (se 3 (by rfl) ⟨2180225, by rfl⟩ : syracuseStep 11627869 = 4360451) B4360451
theorem B15503825 : Blo 2149435 15503825 := bstep (se 2 (by rfl) ⟨5813934, by rfl⟩ : syracuseStep 15503825 = 11627869) B11627869
theorem B10335883 : Blo 2149435 10335883 := bstep (se 1 (by rfl) ⟨7751912, by rfl⟩ : syracuseStep 10335883 = 15503825) B15503825
theorem B13781177 : Blo 2149435 13781177 := bstep (se 2 (by rfl) ⟨5167941, by rfl⟩ : syracuseStep 13781177 = 10335883) B10335883
theorem B9187451 : Blo 2149435 9187451 := bstep (se 1 (by rfl) ⟨6890588, by rfl⟩ : syracuseStep 9187451 = 13781177) B13781177
theorem B6124967 : Blo 2149435 6124967 := bstep (se 1 (by rfl) ⟨4593725, by rfl⟩ : syracuseStep 6124967 = 9187451) B9187451
theorem B4083311 : Blo 2149435 4083311 := bstep (se 1 (by rfl) ⟨3062483, by rfl⟩ : syracuseStep 4083311 = 6124967) B6124967
theorem B10888829 : Blo 2149435 10888829 := bstep (se 3 (by rfl) ⟨2041655, by rfl⟩ : syracuseStep 10888829 = 4083311) B4083311
theorem B7259219 : Blo 2149435 7259219 := bstep (se 1 (by rfl) ⟨5444414, by rfl⟩ : syracuseStep 7259219 = 10888829) B10888829
theorem B4839479 : Blo 2149435 4839479 := bstep (se 1 (by rfl) ⟨3629609, by rfl⟩ : syracuseStep 4839479 = 7259219) B7259219
theorem B3226319 : Blo 2149435 3226319 := bstep (se 1 (by rfl) ⟨2419739, by rfl⟩ : syracuseStep 3226319 = 4839479) B4839479
theorem B2150879 : Blo 2149435 2150879 := bstep (se 1 (by rfl) ⟨1613159, by rfl⟩ : syracuseStep 2150879 = 3226319) B3226319
theorem B3226325 : Blo 2149435 3226325 := bbase (se 7 (by rfl) ⟨37808, by rfl⟩ : syracuseStep 3226325 = 75617) (by norm_num)
theorem B2150883 : Blo 2149435 2150883 := bstep (se 1 (by rfl) ⟨1613162, by rfl⟩ : syracuseStep 2150883 = 3226325) B3226325
theorem B5813957 : Blo 2149435 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B15503885 : Blo 2149435 15503885 := bstep (se 3 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 15503885 = 5813957) B5813957
theorem B10335923 : Blo 2149435 10335923 := bstep (se 1 (by rfl) ⟨7751942, by rfl⟩ : syracuseStep 10335923 = 15503885) B15503885
theorem B6890615 : Blo 2149435 6890615 := bstep (se 1 (by rfl) ⟨5167961, by rfl⟩ : syracuseStep 6890615 = 10335923) B10335923
theorem B4593743 : Blo 2149435 4593743 := bstep (se 1 (by rfl) ⟨3445307, by rfl⟩ : syracuseStep 4593743 = 6890615) B6890615
theorem B3062495 : Blo 2149435 3062495 := bstep (se 1 (by rfl) ⟨2296871, by rfl⟩ : syracuseStep 3062495 = 4593743) B4593743
theorem B8166653 : Blo 2149435 8166653 := bstep (se 3 (by rfl) ⟨1531247, by rfl⟩ : syracuseStep 8166653 = 3062495) B3062495
theorem B5444435 : Blo 2149435 5444435 := bstep (se 1 (by rfl) ⟨4083326, by rfl⟩ : syracuseStep 5444435 = 8166653) B8166653
theorem B3629623 : Blo 2149435 3629623 := bstep (se 1 (by rfl) ⟨2722217, by rfl⟩ : syracuseStep 3629623 = 5444435) B5444435
theorem B4839497 : Blo 2149435 4839497 := bstep (se 2 (by rfl) ⟨1814811, by rfl⟩ : syracuseStep 4839497 = 3629623) B3629623
theorem B3226331 : Blo 2149435 3226331 := bstep (se 1 (by rfl) ⟨2419748, by rfl⟩ : syracuseStep 3226331 = 4839497) B4839497
theorem B2150887 : Blo 2149435 2150887 := bstep (se 1 (by rfl) ⟨1613165, by rfl⟩ : syracuseStep 2150887 = 3226331) B3226331
theorem B2419753 : Blo 2149435 2419753 := bbase (se 2 (by rfl) ⟨907407, by rfl⟩ : syracuseStep 2419753 = 1814815) (by norm_num)
theorem B3226337 : Blo 2149435 3226337 := bstep (se 2 (by rfl) ⟨1209876, by rfl⟩ : syracuseStep 3226337 = 2419753) B2419753
theorem B2150891 : Blo 2149435 2150891 := bstep (se 1 (by rfl) ⟨1613168, by rfl⟩ : syracuseStep 2150891 = 3226337) B3226337
theorem B9312869 : Blo 2149435 9312869 := bbase (se 4 (by rfl) ⟨873081, by rfl⟩ : syracuseStep 9312869 = 1746163) (by norm_num)
theorem B6208579 : Blo 2149435 6208579 := bstep (se 1 (by rfl) ⟨4656434, by rfl⟩ : syracuseStep 6208579 = 9312869) B9312869
theorem B33112421 : Blo 2149435 33112421 := bstep (se 4 (by rfl) ⟨3104289, by rfl⟩ : syracuseStep 33112421 = 6208579) B6208579
theorem B22074947 : Blo 2149435 22074947 := bstep (se 1 (by rfl) ⟨16556210, by rfl⟩ : syracuseStep 22074947 = 33112421) B33112421
theorem B14716631 : Blo 2149435 14716631 := bstep (se 1 (by rfl) ⟨11037473, by rfl⟩ : syracuseStep 14716631 = 22074947) B22074947
theorem B9811087 : Blo 2149435 9811087 := bstep (se 1 (by rfl) ⟨7358315, by rfl⟩ : syracuseStep 9811087 = 14716631) B14716631
theorem B52325797 : Blo 2149435 52325797 := bstep (se 4 (by rfl) ⟨4905543, by rfl⟩ : syracuseStep 52325797 = 9811087) B9811087
theorem B69767729 : Blo 2149435 69767729 := bstep (se 2 (by rfl) ⟨26162898, by rfl⟩ : syracuseStep 69767729 = 52325797) B52325797
theorem B46511819 : Blo 2149435 46511819 := bstep (se 1 (by rfl) ⟨34883864, by rfl⟩ : syracuseStep 46511819 = 69767729) B69767729
theorem B31007879 : Blo 2149435 31007879 := bstep (se 1 (by rfl) ⟨23255909, by rfl⟩ : syracuseStep 31007879 = 46511819) B46511819
theorem B20671919 : Blo 2149435 20671919 := bstep (se 1 (by rfl) ⟨15503939, by rfl⟩ : syracuseStep 20671919 = 31007879) B31007879
theorem B13781279 : Blo 2149435 13781279 := bstep (se 1 (by rfl) ⟨10335959, by rfl⟩ : syracuseStep 13781279 = 20671919) B20671919
theorem B9187519 : Blo 2149435 9187519 := bstep (se 1 (by rfl) ⟨6890639, by rfl⟩ : syracuseStep 9187519 = 13781279) B13781279
theorem B12250025 : Blo 2149435 12250025 := bstep (se 2 (by rfl) ⟨4593759, by rfl⟩ : syracuseStep 12250025 = 9187519) B9187519
theorem B8166683 : Blo 2149435 8166683 := bstep (se 1 (by rfl) ⟨6125012, by rfl⟩ : syracuseStep 8166683 = 12250025) B12250025
theorem B5444455 : Blo 2149435 5444455 := bstep (se 1 (by rfl) ⟨4083341, by rfl⟩ : syracuseStep 5444455 = 8166683) B8166683
theorem B7259273 : Blo 2149435 7259273 := bstep (se 2 (by rfl) ⟨2722227, by rfl⟩ : syracuseStep 7259273 = 5444455) B5444455
theorem B4839515 : Blo 2149435 4839515 := bstep (se 1 (by rfl) ⟨3629636, by rfl⟩ : syracuseStep 4839515 = 7259273) B7259273
theorem B3226343 : Blo 2149435 3226343 := bstep (se 1 (by rfl) ⟨2419757, by rfl⟩ : syracuseStep 3226343 = 4839515) B4839515
theorem B2150895 : Blo 2149435 2150895 := bstep (se 1 (by rfl) ⟨1613171, by rfl⟩ : syracuseStep 2150895 = 3226343) B3226343
theorem B3226349 : Blo 2149435 3226349 := bbase (se 3 (by rfl) ⟨604940, by rfl⟩ : syracuseStep 3226349 = 1209881) (by norm_num)
theorem B2150899 : Blo 2149435 2150899 := bstep (se 1 (by rfl) ⟨1613174, by rfl⟩ : syracuseStep 2150899 = 3226349) B3226349
theorem B4839533 : Blo 2149435 4839533 := bbase (se 3 (by rfl) ⟨907412, by rfl⟩ : syracuseStep 4839533 = 1814825) (by norm_num)
theorem B3226355 : Blo 2149435 3226355 := bstep (se 1 (by rfl) ⟨2419766, by rfl⟩ : syracuseStep 3226355 = 4839533) B4839533
theorem B2150903 : Blo 2149435 2150903 := bstep (se 1 (by rfl) ⟨1613177, by rfl⟩ : syracuseStep 2150903 = 3226355) B3226355
theorem B4083365 : Blo 2149435 4083365 := bbase (se 4 (by rfl) ⟨382815, by rfl⟩ : syracuseStep 4083365 = 765631) (by norm_num)
theorem B2722243 : Blo 2149435 2722243 := bstep (se 1 (by rfl) ⟨2041682, by rfl⟩ : syracuseStep 2722243 = 4083365) B4083365
theorem B3629657 : Blo 2149435 3629657 := bstep (se 2 (by rfl) ⟨1361121, by rfl⟩ : syracuseStep 3629657 = 2722243) B2722243
theorem B2419771 : Blo 2149435 2419771 := bstep (se 1 (by rfl) ⟨1814828, by rfl⟩ : syracuseStep 2419771 = 3629657) B3629657
theorem B3226361 : Blo 2149435 3226361 := bstep (se 2 (by rfl) ⟨1209885, by rfl⟩ : syracuseStep 3226361 = 2419771) B2419771
theorem B2150907 : Blo 2149435 2150907 := bstep (se 1 (by rfl) ⟨1613180, by rfl⟩ : syracuseStep 2150907 = 3226361) B3226361
theorem B15504053 : Blo 2149435 15504053 := bbase (se 5 (by rfl) ⟨726752, by rfl⟩ : syracuseStep 15504053 = 1453505) (by norm_num)
theorem B41344141 : Blo 2149435 41344141 := bstep (se 3 (by rfl) ⟨7752026, by rfl⟩ : syracuseStep 41344141 = 15504053) B15504053
theorem B55125521 : Blo 2149435 55125521 := bstep (se 2 (by rfl) ⟨20672070, by rfl⟩ : syracuseStep 55125521 = 41344141) B41344141
theorem B36750347 : Blo 2149435 36750347 := bstep (se 1 (by rfl) ⟨27562760, by rfl⟩ : syracuseStep 36750347 = 55125521) B55125521
theorem B24500231 : Blo 2149435 24500231 := bstep (se 1 (by rfl) ⟨18375173, by rfl⟩ : syracuseStep 24500231 = 36750347) B36750347
theorem B16333487 : Blo 2149435 16333487 := bstep (se 1 (by rfl) ⟨12250115, by rfl⟩ : syracuseStep 16333487 = 24500231) B24500231
theorem B10888991 : Blo 2149435 10888991 := bstep (se 1 (by rfl) ⟨8166743, by rfl⟩ : syracuseStep 10888991 = 16333487) B16333487
theorem B7259327 : Blo 2149435 7259327 := bstep (se 1 (by rfl) ⟨5444495, by rfl⟩ : syracuseStep 7259327 = 10888991) B10888991
theorem B4839551 : Blo 2149435 4839551 := bstep (se 1 (by rfl) ⟨3629663, by rfl⟩ : syracuseStep 4839551 = 7259327) B7259327
theorem B3226367 : Blo 2149435 3226367 := bstep (se 1 (by rfl) ⟨2419775, by rfl⟩ : syracuseStep 3226367 = 4839551) B4839551
theorem B2150911 : Blo 2149435 2150911 := bstep (se 1 (by rfl) ⟨1613183, by rfl⟩ : syracuseStep 2150911 = 3226367) B3226367
theorem B3226373 : Blo 2149435 3226373 := bbase (se 4 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 3226373 = 604945) (by norm_num)
theorem B2150915 : Blo 2149435 2150915 := bstep (se 1 (by rfl) ⟨1613186, by rfl⟩ : syracuseStep 2150915 = 3226373) B3226373
theorem B3629677 : Blo 2149435 3629677 := bbase (se 3 (by rfl) ⟨680564, by rfl⟩ : syracuseStep 3629677 = 1361129) (by norm_num)
theorem B4839569 : Blo 2149435 4839569 := bstep (se 2 (by rfl) ⟨1814838, by rfl⟩ : syracuseStep 4839569 = 3629677) B3629677
theorem B3226379 : Blo 2149435 3226379 := bstep (se 1 (by rfl) ⟨2419784, by rfl⟩ : syracuseStep 3226379 = 4839569) B4839569
theorem B2150919 : Blo 2149435 2150919 := bstep (se 1 (by rfl) ⟨1613189, by rfl⟩ : syracuseStep 2150919 = 3226379) B3226379
theorem B2419789 : Blo 2149435 2419789 := bbase (se 3 (by rfl) ⟨453710, by rfl⟩ : syracuseStep 2419789 = 907421) (by norm_num)
theorem B3226385 : Blo 2149435 3226385 := bstep (se 2 (by rfl) ⟨1209894, by rfl⟩ : syracuseStep 3226385 = 2419789) B2419789
theorem B2150923 : Blo 2149435 2150923 := bstep (se 1 (by rfl) ⟨1613192, by rfl⟩ : syracuseStep 2150923 = 3226385) B3226385
theorem B7259381 : Blo 2149435 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B4839587 : Blo 2149435 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B3226391 : Blo 2149435 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B2150927 : Blo 2149435 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B3226397 : Blo 2149435 3226397 := bbase (se 3 (by rfl) ⟨604949, by rfl⟩ : syracuseStep 3226397 = 1209899) (by norm_num)
theorem B2150931 : Blo 2149435 2150931 := bstep (se 1 (by rfl) ⟨1613198, by rfl⟩ : syracuseStep 2150931 = 3226397) B3226397
theorem B4839605 : Blo 2149435 4839605 := bbase (se 5 (by rfl) ⟨226856, by rfl⟩ : syracuseStep 4839605 = 453713) (by norm_num)
theorem B3226403 : Blo 2149435 3226403 := bstep (se 1 (by rfl) ⟨2419802, by rfl⟩ : syracuseStep 3226403 = 4839605) B4839605
theorem B2150935 : Blo 2149435 2150935 := bstep (se 1 (by rfl) ⟨1613201, by rfl⟩ : syracuseStep 2150935 = 3226403) B3226403
theorem B4656533 : Blo 2149435 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B12417421 : Blo 2149435 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B16556561 : Blo 2149435 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B11037707 : Blo 2149435 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B7358471 : Blo 2149435 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B4905647 : Blo 2149435 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B3270431 : Blo 2149435 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B2180287 : Blo 2149435 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B11628197 : Blo 2149435 11628197 := bstep (se 4 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 11628197 = 2180287) B2180287
theorem B7752131 : Blo 2149435 7752131 := bstep (se 1 (by rfl) ⟨5814098, by rfl⟩ : syracuseStep 7752131 = 11628197) B11628197
theorem B5168087 : Blo 2149435 5168087 := bstep (se 1 (by rfl) ⟨3876065, by rfl⟩ : syracuseStep 5168087 = 7752131) B7752131
theorem B3445391 : Blo 2149435 3445391 := bstep (se 1 (by rfl) ⟨2584043, by rfl⟩ : syracuseStep 3445391 = 5168087) B5168087
theorem B2296927 : Blo 2149435 2296927 := bstep (se 1 (by rfl) ⟨1722695, by rfl⟩ : syracuseStep 2296927 = 3445391) B3445391
theorem B12250277 : Blo 2149435 12250277 := bstep (se 4 (by rfl) ⟨1148463, by rfl⟩ : syracuseStep 12250277 = 2296927) B2296927
theorem B8166851 : Blo 2149435 8166851 := bstep (se 1 (by rfl) ⟨6125138, by rfl⟩ : syracuseStep 8166851 = 12250277) B12250277
theorem B5444567 : Blo 2149435 5444567 := bstep (se 1 (by rfl) ⟨4083425, by rfl⟩ : syracuseStep 5444567 = 8166851) B8166851
theorem B3629711 : Blo 2149435 3629711 := bstep (se 1 (by rfl) ⟨2722283, by rfl⟩ : syracuseStep 3629711 = 5444567) B5444567
theorem B2419807 : Blo 2149435 2419807 := bstep (se 1 (by rfl) ⟨1814855, by rfl⟩ : syracuseStep 2419807 = 3629711) B3629711
theorem B3226409 : Blo 2149435 3226409 := bstep (se 2 (by rfl) ⟨1209903, by rfl⟩ : syracuseStep 3226409 = 2419807) B2419807
theorem B2150939 : Blo 2149435 2150939 := bstep (se 1 (by rfl) ⟨1613204, by rfl⟩ : syracuseStep 2150939 = 3226409) B3226409
theorem B3445397 : Blo 2149435 3445397 := bbase (se 6 (by rfl) ⟨80751, by rfl⟩ : syracuseStep 3445397 = 161503) (by norm_num)
theorem B2296931 : Blo 2149435 2296931 := bstep (se 1 (by rfl) ⟨1722698, by rfl⟩ : syracuseStep 2296931 = 3445397) B3445397
theorem B6125149 : Blo 2149435 6125149 := bstep (se 3 (by rfl) ⟨1148465, by rfl⟩ : syracuseStep 6125149 = 2296931) B2296931
theorem B8166865 : Blo 2149435 8166865 := bstep (se 2 (by rfl) ⟨3062574, by rfl⟩ : syracuseStep 8166865 = 6125149) B6125149
theorem B10889153 : Blo 2149435 10889153 := bstep (se 2 (by rfl) ⟨4083432, by rfl⟩ : syracuseStep 10889153 = 8166865) B8166865
theorem B7259435 : Blo 2149435 7259435 := bstep (se 1 (by rfl) ⟨5444576, by rfl⟩ : syracuseStep 7259435 = 10889153) B10889153
theorem B4839623 : Blo 2149435 4839623 := bstep (se 1 (by rfl) ⟨3629717, by rfl⟩ : syracuseStep 4839623 = 7259435) B7259435
theorem B3226415 : Blo 2149435 3226415 := bstep (se 1 (by rfl) ⟨2419811, by rfl⟩ : syracuseStep 3226415 = 4839623) B4839623
theorem B2150943 : Blo 2149435 2150943 := bstep (se 1 (by rfl) ⟨1613207, by rfl⟩ : syracuseStep 2150943 = 3226415) B3226415
theorem B3226421 : Blo 2149435 3226421 := bbase (se 5 (by rfl) ⟨151238, by rfl⟩ : syracuseStep 3226421 = 302477) (by norm_num)
theorem B2150947 : Blo 2149435 2150947 := bstep (se 1 (by rfl) ⟨1613210, by rfl⟩ : syracuseStep 2150947 = 3226421) B3226421
theorem B5444597 : Blo 2149435 5444597 := bbase (se 5 (by rfl) ⟨255215, by rfl⟩ : syracuseStep 5444597 = 510431) (by norm_num)
theorem B3629731 : Blo 2149435 3629731 := bstep (se 1 (by rfl) ⟨2722298, by rfl⟩ : syracuseStep 3629731 = 5444597) B5444597
theorem B4839641 : Blo 2149435 4839641 := bstep (se 2 (by rfl) ⟨1814865, by rfl⟩ : syracuseStep 4839641 = 3629731) B3629731
theorem B3226427 : Blo 2149435 3226427 := bstep (se 1 (by rfl) ⟨2419820, by rfl⟩ : syracuseStep 3226427 = 4839641) B4839641
theorem B2150951 : Blo 2149435 2150951 := bstep (se 1 (by rfl) ⟨1613213, by rfl⟩ : syracuseStep 2150951 = 3226427) B3226427
theorem B2419825 : Blo 2149435 2419825 := bbase (se 2 (by rfl) ⟨907434, by rfl⟩ : syracuseStep 2419825 = 1814869) (by norm_num)
theorem B3226433 : Blo 2149435 3226433 := bstep (se 2 (by rfl) ⟨1209912, by rfl⟩ : syracuseStep 3226433 = 2419825) B2419825
theorem B2150955 : Blo 2149435 2150955 := bstep (se 1 (by rfl) ⟨1613216, by rfl⟩ : syracuseStep 2150955 = 3226433) B3226433
theorem B3876101 : Blo 2149435 3876101 := bbase (se 4 (by rfl) ⟨363384, by rfl⟩ : syracuseStep 3876101 = 726769) (by norm_num)
theorem B2584067 : Blo 2149435 2584067 := bstep (se 1 (by rfl) ⟨1938050, by rfl⟩ : syracuseStep 2584067 = 3876101) B3876101
theorem B6890845 : Blo 2149435 6890845 := bstep (se 3 (by rfl) ⟨1292033, by rfl⟩ : syracuseStep 6890845 = 2584067) B2584067
theorem B9187793 : Blo 2149435 9187793 := bstep (se 2 (by rfl) ⟨3445422, by rfl⟩ : syracuseStep 9187793 = 6890845) B6890845
theorem B6125195 : Blo 2149435 6125195 := bstep (se 1 (by rfl) ⟨4593896, by rfl⟩ : syracuseStep 6125195 = 9187793) B9187793
theorem B4083463 : Blo 2149435 4083463 := bstep (se 1 (by rfl) ⟨3062597, by rfl⟩ : syracuseStep 4083463 = 6125195) B6125195
theorem B5444617 : Blo 2149435 5444617 := bstep (se 2 (by rfl) ⟨2041731, by rfl⟩ : syracuseStep 5444617 = 4083463) B4083463
theorem B7259489 : Blo 2149435 7259489 := bstep (se 2 (by rfl) ⟨2722308, by rfl⟩ : syracuseStep 7259489 = 5444617) B5444617
theorem B4839659 : Blo 2149435 4839659 := bstep (se 1 (by rfl) ⟨3629744, by rfl⟩ : syracuseStep 4839659 = 7259489) B7259489
theorem B3226439 : Blo 2149435 3226439 := bstep (se 1 (by rfl) ⟨2419829, by rfl⟩ : syracuseStep 3226439 = 4839659) B4839659
theorem B2150959 : Blo 2149435 2150959 := bstep (se 1 (by rfl) ⟨1613219, by rfl⟩ : syracuseStep 2150959 = 3226439) B3226439
theorem B3226445 : Blo 2149435 3226445 := bbase (se 3 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 3226445 = 1209917) (by norm_num)
theorem B2150963 : Blo 2149435 2150963 := bstep (se 1 (by rfl) ⟨1613222, by rfl⟩ : syracuseStep 2150963 = 3226445) B3226445
theorem B4839677 : Blo 2149435 4839677 := bbase (se 3 (by rfl) ⟨907439, by rfl⟩ : syracuseStep 4839677 = 1814879) (by norm_num)
theorem B3226451 : Blo 2149435 3226451 := bstep (se 1 (by rfl) ⟨2419838, by rfl⟩ : syracuseStep 3226451 = 4839677) B4839677
theorem B2150967 : Blo 2149435 2150967 := bstep (se 1 (by rfl) ⟨1613225, by rfl⟩ : syracuseStep 2150967 = 3226451) B3226451
theorem B3629765 : Blo 2149435 3629765 := bbase (se 4 (by rfl) ⟨340290, by rfl⟩ : syracuseStep 3629765 = 680581) (by norm_num)
theorem B2419843 : Blo 2149435 2419843 := bstep (se 1 (by rfl) ⟨1814882, by rfl⟩ : syracuseStep 2419843 = 3629765) B3629765
theorem B3226457 : Blo 2149435 3226457 := bstep (se 2 (by rfl) ⟨1209921, by rfl⟩ : syracuseStep 3226457 = 2419843) B2419843
theorem B2150971 : Blo 2149435 2150971 := bstep (se 1 (by rfl) ⟨1613228, by rfl⟩ : syracuseStep 2150971 = 3226457) B3226457
theorem B16333973 : Blo 2149435 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B10889315 : Blo 2149435 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B7259543 : Blo 2149435 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B4839695 : Blo 2149435 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B3226463 : Blo 2149435 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B2150975 : Blo 2149435 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B3226469 : Blo 2149435 3226469 := bbase (se 4 (by rfl) ⟨302481, by rfl⟩ : syracuseStep 3226469 = 604963) (by norm_num)
theorem B2150979 : Blo 2149435 2150979 := bstep (se 1 (by rfl) ⟨1613234, by rfl⟩ : syracuseStep 2150979 = 3226469) B3226469
theorem B4083509 : Blo 2149435 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B2722339 : Blo 2149435 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B3629785 : Blo 2149435 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B4839713 : Blo 2149435 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B3226475 : Blo 2149435 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B2150983 : Blo 2149435 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B2419861 : Blo 2149435 2419861 := bbase (se 6 (by rfl) ⟨56715, by rfl⟩ : syracuseStep 2419861 = 113431) (by norm_num)
theorem B3226481 : Blo 2149435 3226481 := bstep (se 2 (by rfl) ⟨1209930, by rfl⟩ : syracuseStep 3226481 = 2419861) B2419861
theorem B2150987 : Blo 2149435 2150987 := bstep (se 1 (by rfl) ⟨1613240, by rfl⟩ : syracuseStep 2150987 = 3226481) B3226481
theorem B2722349 : Blo 2149435 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B7259597 : Blo 2149435 7259597 := bstep (se 3 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 7259597 = 2722349) B2722349
theorem B4839731 : Blo 2149435 4839731 := bstep (se 1 (by rfl) ⟨3629798, by rfl⟩ : syracuseStep 4839731 = 7259597) B7259597
theorem B3226487 : Blo 2149435 3226487 := bstep (se 1 (by rfl) ⟨2419865, by rfl⟩ : syracuseStep 3226487 = 4839731) B4839731
theorem B2150991 : Blo 2149435 2150991 := bstep (se 1 (by rfl) ⟨1613243, by rfl⟩ : syracuseStep 2150991 = 3226487) B3226487
theorem B3226493 : Blo 2149435 3226493 := bbase (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) (by norm_num)
theorem B2150995 : Blo 2149435 2150995 := bstep (se 1 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 2150995 = 3226493) B3226493
theorem B4839749 : Blo 2149435 4839749 := bbase (se 4 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 4839749 = 907453) (by norm_num)
theorem B3226499 : Blo 2149435 3226499 := bstep (se 1 (by rfl) ⟨2419874, by rfl⟩ : syracuseStep 3226499 = 4839749) B4839749
theorem B2150999 : Blo 2149435 2150999 := bstep (se 1 (by rfl) ⟨1613249, by rfl⟩ : syracuseStep 2150999 = 3226499) B3226499
theorem B2797157 : Blo 2149435 2797157 := bbase (se 4 (by rfl) ⟨262233, by rfl⟩ : syracuseStep 2797157 = 524467) (by norm_num)
theorem B7459085 : Blo 2149435 7459085 := bstep (se 3 (by rfl) ⟨1398578, by rfl⟩ : syracuseStep 7459085 = 2797157) B2797157
theorem B19890893 : Blo 2149435 19890893 := bstep (se 3 (by rfl) ⟨3729542, by rfl⟩ : syracuseStep 19890893 = 7459085) B7459085
theorem B13260595 : Blo 2149435 13260595 := bstep (se 1 (by rfl) ⟨9945446, by rfl⟩ : syracuseStep 13260595 = 19890893) B19890893
theorem B17680793 : Blo 2149435 17680793 := bstep (se 2 (by rfl) ⟨6630297, by rfl⟩ : syracuseStep 17680793 = 13260595) B13260595
theorem B188595125 : Blo 2149435 188595125 := bstep (se 5 (by rfl) ⟨8840396, by rfl⟩ : syracuseStep 188595125 = 17680793) B17680793
theorem B125730083 : Blo 2149435 125730083 := bstep (se 1 (by rfl) ⟨94297562, by rfl⟩ : syracuseStep 125730083 = 188595125) B188595125
theorem B335280221 : Blo 2149435 335280221 := bstep (se 3 (by rfl) ⟨62865041, by rfl⟩ : syracuseStep 335280221 = 125730083) B125730083
theorem B223520147 : Blo 2149435 223520147 := bstep (se 1 (by rfl) ⟨167640110, by rfl⟩ : syracuseStep 223520147 = 335280221) B335280221
theorem B149013431 : Blo 2149435 149013431 := bstep (se 1 (by rfl) ⟨111760073, by rfl⟩ : syracuseStep 149013431 = 223520147) B223520147
theorem B99342287 : Blo 2149435 99342287 := bstep (se 1 (by rfl) ⟨74506715, by rfl⟩ : syracuseStep 99342287 = 149013431) B149013431
theorem B66228191 : Blo 2149435 66228191 := bstep (se 1 (by rfl) ⟨49671143, by rfl⟩ : syracuseStep 66228191 = 99342287) B99342287
theorem B44152127 : Blo 2149435 44152127 := bstep (se 1 (by rfl) ⟨33114095, by rfl⟩ : syracuseStep 44152127 = 66228191) B66228191
theorem B29434751 : Blo 2149435 29434751 := bstep (se 1 (by rfl) ⟨22076063, by rfl⟩ : syracuseStep 29434751 = 44152127) B44152127
theorem B19623167 : Blo 2149435 19623167 := bstep (se 1 (by rfl) ⟨14717375, by rfl⟩ : syracuseStep 19623167 = 29434751) B29434751
theorem B13082111 : Blo 2149435 13082111 := bstep (se 1 (by rfl) ⟨9811583, by rfl⟩ : syracuseStep 13082111 = 19623167) B19623167
theorem B8721407 : Blo 2149435 8721407 := bstep (se 1 (by rfl) ⟨6541055, by rfl⟩ : syracuseStep 8721407 = 13082111) B13082111
theorem B5814271 : Blo 2149435 5814271 := bstep (se 1 (by rfl) ⟨4360703, by rfl⟩ : syracuseStep 5814271 = 8721407) B8721407
theorem B7752361 : Blo 2149435 7752361 := bstep (se 2 (by rfl) ⟨2907135, by rfl⟩ : syracuseStep 7752361 = 5814271) B5814271
theorem B10336481 : Blo 2149435 10336481 := bstep (se 2 (by rfl) ⟨3876180, by rfl⟩ : syracuseStep 10336481 = 7752361) B7752361
theorem B6890987 : Blo 2149435 6890987 := bstep (se 1 (by rfl) ⟨5168240, by rfl⟩ : syracuseStep 6890987 = 10336481) B10336481
theorem B4593991 : Blo 2149435 4593991 := bstep (se 1 (by rfl) ⟨3445493, by rfl⟩ : syracuseStep 4593991 = 6890987) B6890987
theorem B6125321 : Blo 2149435 6125321 := bstep (se 2 (by rfl) ⟨2296995, by rfl⟩ : syracuseStep 6125321 = 4593991) B4593991
theorem B4083547 : Blo 2149435 4083547 := bstep (se 1 (by rfl) ⟨3062660, by rfl⟩ : syracuseStep 4083547 = 6125321) B6125321
theorem B5444729 : Blo 2149435 5444729 := bstep (se 2 (by rfl) ⟨2041773, by rfl⟩ : syracuseStep 5444729 = 4083547) B4083547
theorem B3629819 : Blo 2149435 3629819 := bstep (se 1 (by rfl) ⟨2722364, by rfl⟩ : syracuseStep 3629819 = 5444729) B5444729
theorem B2419879 : Blo 2149435 2419879 := bstep (se 1 (by rfl) ⟨1814909, by rfl⟩ : syracuseStep 2419879 = 3629819) B3629819
theorem B3226505 : Blo 2149435 3226505 := bstep (se 2 (by rfl) ⟨1209939, by rfl⟩ : syracuseStep 3226505 = 2419879) B2419879
theorem B2151003 : Blo 2149435 2151003 := bstep (se 1 (by rfl) ⟨1613252, by rfl⟩ : syracuseStep 2151003 = 3226505) B3226505
theorem B10889477 : Blo 2149435 10889477 := bbase (se 4 (by rfl) ⟨1020888, by rfl⟩ : syracuseStep 10889477 = 2041777) (by norm_num)
theorem B7259651 : Blo 2149435 7259651 := bstep (se 1 (by rfl) ⟨5444738, by rfl⟩ : syracuseStep 7259651 = 10889477) B10889477
theorem B4839767 : Blo 2149435 4839767 := bstep (se 1 (by rfl) ⟨3629825, by rfl⟩ : syracuseStep 4839767 = 7259651) B7259651
theorem B3226511 : Blo 2149435 3226511 := bstep (se 1 (by rfl) ⟨2419883, by rfl⟩ : syracuseStep 3226511 = 4839767) B4839767
theorem B2151007 : Blo 2149435 2151007 := bstep (se 1 (by rfl) ⟨1613255, by rfl⟩ : syracuseStep 2151007 = 3226511) B3226511
theorem B3226517 : Blo 2149435 3226517 := bbase (se 6 (by rfl) ⟨75621, by rfl⟩ : syracuseStep 3226517 = 151243) (by norm_num)
theorem B2151011 : Blo 2149435 2151011 := bstep (se 1 (by rfl) ⟨1613258, by rfl⟩ : syracuseStep 2151011 = 3226517) B3226517
theorem B12250709 : Blo 2149435 12250709 := bbase (se 8 (by rfl) ⟨71781, by rfl⟩ : syracuseStep 12250709 = 143563) (by norm_num)
theorem B8167139 : Blo 2149435 8167139 := bstep (se 1 (by rfl) ⟨6125354, by rfl⟩ : syracuseStep 8167139 = 12250709) B12250709
theorem B5444759 : Blo 2149435 5444759 := bstep (se 1 (by rfl) ⟨4083569, by rfl⟩ : syracuseStep 5444759 = 8167139) B8167139
theorem B3629839 : Blo 2149435 3629839 := bstep (se 1 (by rfl) ⟨2722379, by rfl⟩ : syracuseStep 3629839 = 5444759) B5444759
theorem B4839785 : Blo 2149435 4839785 := bstep (se 2 (by rfl) ⟨1814919, by rfl⟩ : syracuseStep 4839785 = 3629839) B3629839
theorem B3226523 : Blo 2149435 3226523 := bstep (se 1 (by rfl) ⟨2419892, by rfl⟩ : syracuseStep 3226523 = 4839785) B4839785
theorem B2151015 : Blo 2149435 2151015 := bstep (se 1 (by rfl) ⟨1613261, by rfl⟩ : syracuseStep 2151015 = 3226523) B3226523
theorem B2419897 : Blo 2149435 2419897 := bbase (se 2 (by rfl) ⟨907461, by rfl⟩ : syracuseStep 2419897 = 1814923) (by norm_num)
theorem B3226529 : Blo 2149435 3226529 := bstep (se 2 (by rfl) ⟨1209948, by rfl⟩ : syracuseStep 3226529 = 2419897) B2419897
theorem B2151019 : Blo 2149435 2151019 := bstep (se 1 (by rfl) ⟨1613264, by rfl⟩ : syracuseStep 2151019 = 3226529) B3226529
theorem B3445525 : Blo 2149435 3445525 := bbase (se 6 (by rfl) ⟨80754, by rfl⟩ : syracuseStep 3445525 = 161509) (by norm_num)
theorem B4594033 : Blo 2149435 4594033 := bstep (se 2 (by rfl) ⟨1722762, by rfl⟩ : syracuseStep 4594033 = 3445525) B3445525
theorem B6125377 : Blo 2149435 6125377 := bstep (se 2 (by rfl) ⟨2297016, by rfl⟩ : syracuseStep 6125377 = 4594033) B4594033
theorem B8167169 : Blo 2149435 8167169 := bstep (se 2 (by rfl) ⟨3062688, by rfl⟩ : syracuseStep 8167169 = 6125377) B6125377
theorem B5444779 : Blo 2149435 5444779 := bstep (se 1 (by rfl) ⟨4083584, by rfl⟩ : syracuseStep 5444779 = 8167169) B8167169
theorem B7259705 : Blo 2149435 7259705 := bstep (se 2 (by rfl) ⟨2722389, by rfl⟩ : syracuseStep 7259705 = 5444779) B5444779
theorem B4839803 : Blo 2149435 4839803 := bstep (se 1 (by rfl) ⟨3629852, by rfl⟩ : syracuseStep 4839803 = 7259705) B7259705
theorem B3226535 : Blo 2149435 3226535 := bstep (se 1 (by rfl) ⟨2419901, by rfl⟩ : syracuseStep 3226535 = 4839803) B4839803
theorem B2151023 : Blo 2149435 2151023 := bstep (se 1 (by rfl) ⟨1613267, by rfl⟩ : syracuseStep 2151023 = 3226535) B3226535
theorem B3226541 : Blo 2149435 3226541 := bbase (se 3 (by rfl) ⟨604976, by rfl⟩ : syracuseStep 3226541 = 1209953) (by norm_num)
theorem B2151027 : Blo 2149435 2151027 := bstep (se 1 (by rfl) ⟨1613270, by rfl⟩ : syracuseStep 2151027 = 3226541) B3226541
theorem B4839821 : Blo 2149435 4839821 := bbase (se 3 (by rfl) ⟨907466, by rfl⟩ : syracuseStep 4839821 = 1814933) (by norm_num)
theorem B3226547 : Blo 2149435 3226547 := bstep (se 1 (by rfl) ⟨2419910, by rfl⟩ : syracuseStep 3226547 = 4839821) B4839821
theorem B2151031 : Blo 2149435 2151031 := bstep (se 1 (by rfl) ⟨1613273, by rfl⟩ : syracuseStep 2151031 = 3226547) B3226547
theorem B2722405 : Blo 2149435 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B3629873 : Blo 2149435 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B2419915 : Blo 2149435 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B3226553 : Blo 2149435 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B2151035 : Blo 2149435 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B20673301 : Blo 2149435 20673301 := bbase (se 6 (by rfl) ⟨484530, by rfl⟩ : syracuseStep 20673301 = 969061) (by norm_num)
theorem B27564401 : Blo 2149435 27564401 := bstep (se 2 (by rfl) ⟨10336650, by rfl⟩ : syracuseStep 27564401 = 20673301) B20673301
theorem B18376267 : Blo 2149435 18376267 := bstep (se 1 (by rfl) ⟨13782200, by rfl⟩ : syracuseStep 18376267 = 27564401) B27564401
theorem B24501689 : Blo 2149435 24501689 := bstep (se 2 (by rfl) ⟨9188133, by rfl⟩ : syracuseStep 24501689 = 18376267) B18376267
theorem B16334459 : Blo 2149435 16334459 := bstep (se 1 (by rfl) ⟨12250844, by rfl⟩ : syracuseStep 16334459 = 24501689) B24501689
theorem B10889639 : Blo 2149435 10889639 := bstep (se 1 (by rfl) ⟨8167229, by rfl⟩ : syracuseStep 10889639 = 16334459) B16334459
theorem B7259759 : Blo 2149435 7259759 := bstep (se 1 (by rfl) ⟨5444819, by rfl⟩ : syracuseStep 7259759 = 10889639) B10889639
theorem B4839839 : Blo 2149435 4839839 := bstep (se 1 (by rfl) ⟨3629879, by rfl⟩ : syracuseStep 4839839 = 7259759) B7259759
theorem B3226559 : Blo 2149435 3226559 := bstep (se 1 (by rfl) ⟨2419919, by rfl⟩ : syracuseStep 3226559 = 4839839) B4839839
theorem B2151039 : Blo 2149435 2151039 := bstep (se 1 (by rfl) ⟨1613279, by rfl⟩ : syracuseStep 2151039 = 3226559) B3226559
theorem B3226565 : Blo 2149435 3226565 := bbase (se 4 (by rfl) ⟨302490, by rfl⟩ : syracuseStep 3226565 = 604981) (by norm_num)
theorem B2151043 : Blo 2149435 2151043 := bstep (se 1 (by rfl) ⟨1613282, by rfl⟩ : syracuseStep 2151043 = 3226565) B3226565
theorem B3629893 : Blo 2149435 3629893 := bbase (se 4 (by rfl) ⟨340302, by rfl⟩ : syracuseStep 3629893 = 680605) (by norm_num)
theorem B4839857 : Blo 2149435 4839857 := bstep (se 2 (by rfl) ⟨1814946, by rfl⟩ : syracuseStep 4839857 = 3629893) B3629893
theorem B3226571 : Blo 2149435 3226571 := bstep (se 1 (by rfl) ⟨2419928, by rfl⟩ : syracuseStep 3226571 = 4839857) B4839857
theorem B2151047 : Blo 2149435 2151047 := bstep (se 1 (by rfl) ⟨1613285, by rfl⟩ : syracuseStep 2151047 = 3226571) B3226571
theorem B2419933 : Blo 2149435 2419933 := bbase (se 3 (by rfl) ⟨453737, by rfl⟩ : syracuseStep 2419933 = 907475) (by norm_num)
theorem B3226577 : Blo 2149435 3226577 := bstep (se 2 (by rfl) ⟨1209966, by rfl⟩ : syracuseStep 3226577 = 2419933) B2419933
theorem B2151051 : Blo 2149435 2151051 := bstep (se 1 (by rfl) ⟨1613288, by rfl⟩ : syracuseStep 2151051 = 3226577) B3226577
theorem B7259813 : Blo 2149435 7259813 := bbase (se 4 (by rfl) ⟨680607, by rfl⟩ : syracuseStep 7259813 = 1361215) (by norm_num)
theorem B4839875 : Blo 2149435 4839875 := bstep (se 1 (by rfl) ⟨3629906, by rfl⟩ : syracuseStep 4839875 = 7259813) B7259813
theorem B3226583 : Blo 2149435 3226583 := bstep (se 1 (by rfl) ⟨2419937, by rfl⟩ : syracuseStep 3226583 = 4839875) B4839875
theorem B2151055 : Blo 2149435 2151055 := bstep (se 1 (by rfl) ⟨1613291, by rfl⟩ : syracuseStep 2151055 = 3226583) B3226583
theorem B3226589 : Blo 2149435 3226589 := bbase (se 3 (by rfl) ⟨604985, by rfl⟩ : syracuseStep 3226589 = 1209971) (by norm_num)
theorem B2151059 : Blo 2149435 2151059 := bstep (se 1 (by rfl) ⟨1613294, by rfl⟩ : syracuseStep 2151059 = 3226589) B3226589
theorem B4839893 : Blo 2149435 4839893 := bbase (se 7 (by rfl) ⟨56717, by rfl⟩ : syracuseStep 4839893 = 113435) (by norm_num)
theorem B3226595 : Blo 2149435 3226595 := bstep (se 1 (by rfl) ⟨2419946, by rfl⟩ : syracuseStep 3226595 = 4839893) B4839893
theorem B2151063 : Blo 2149435 2151063 := bstep (se 1 (by rfl) ⟨1613297, by rfl⟩ : syracuseStep 2151063 = 3226595) B3226595
theorem B6209077 : Blo 2149435 6209077 := bbase (se 5 (by rfl) ⟨291050, by rfl⟩ : syracuseStep 6209077 = 582101) (by norm_num)
theorem B8278769 : Blo 2149435 8278769 := bstep (se 2 (by rfl) ⟨3104538, by rfl⟩ : syracuseStep 8278769 = 6209077) B6209077
theorem B5519179 : Blo 2149435 5519179 := bstep (se 1 (by rfl) ⟨4139384, by rfl⟩ : syracuseStep 5519179 = 8278769) B8278769
theorem B7358905 : Blo 2149435 7358905 := bstep (se 2 (by rfl) ⟨2759589, by rfl⟩ : syracuseStep 7358905 = 5519179) B5519179
theorem B9811873 : Blo 2149435 9811873 := bstep (se 2 (by rfl) ⟨3679452, by rfl⟩ : syracuseStep 9811873 = 7358905) B7358905
theorem B52329989 : Blo 2149435 52329989 := bstep (se 4 (by rfl) ⟨4905936, by rfl⟩ : syracuseStep 52329989 = 9811873) B9811873
theorem B34886659 : Blo 2149435 34886659 := bstep (se 1 (by rfl) ⟨26164994, by rfl⟩ : syracuseStep 34886659 = 52329989) B52329989
theorem B46515545 : Blo 2149435 46515545 := bstep (se 2 (by rfl) ⟨17443329, by rfl⟩ : syracuseStep 46515545 = 34886659) B34886659
theorem B31010363 : Blo 2149435 31010363 := bstep (se 1 (by rfl) ⟨23257772, by rfl⟩ : syracuseStep 31010363 = 46515545) B46515545
theorem B20673575 : Blo 2149435 20673575 := bstep (se 1 (by rfl) ⟨15505181, by rfl⟩ : syracuseStep 20673575 = 31010363) B31010363
theorem B13782383 : Blo 2149435 13782383 := bstep (se 1 (by rfl) ⟨10336787, by rfl⟩ : syracuseStep 13782383 = 20673575) B20673575
theorem B9188255 : Blo 2149435 9188255 := bstep (se 1 (by rfl) ⟨6891191, by rfl⟩ : syracuseStep 9188255 = 13782383) B13782383
theorem B6125503 : Blo 2149435 6125503 := bstep (se 1 (by rfl) ⟨4594127, by rfl⟩ : syracuseStep 6125503 = 9188255) B9188255
theorem B8167337 : Blo 2149435 8167337 := bstep (se 2 (by rfl) ⟨3062751, by rfl⟩ : syracuseStep 8167337 = 6125503) B6125503
theorem B5444891 : Blo 2149435 5444891 := bstep (se 1 (by rfl) ⟨4083668, by rfl⟩ : syracuseStep 5444891 = 8167337) B8167337
theorem B3629927 : Blo 2149435 3629927 := bstep (se 1 (by rfl) ⟨2722445, by rfl⟩ : syracuseStep 3629927 = 5444891) B5444891
theorem B2419951 : Blo 2149435 2419951 := bstep (se 1 (by rfl) ⟨1814963, by rfl⟩ : syracuseStep 2419951 = 3629927) B3629927
theorem B3226601 : Blo 2149435 3226601 := bstep (se 2 (by rfl) ⟨1209975, by rfl⟩ : syracuseStep 3226601 = 2419951) B2419951
theorem B2151067 : Blo 2149435 2151067 := bstep (se 1 (by rfl) ⟨1613300, by rfl⟩ : syracuseStep 2151067 = 3226601) B3226601
theorem B10336805 : Blo 2149435 10336805 := bbase (se 4 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 10336805 = 1938151) (by norm_num)
theorem B6891203 : Blo 2149435 6891203 := bstep (se 1 (by rfl) ⟨5168402, by rfl⟩ : syracuseStep 6891203 = 10336805) B10336805
theorem B18376541 : Blo 2149435 18376541 := bstep (se 3 (by rfl) ⟨3445601, by rfl⟩ : syracuseStep 18376541 = 6891203) B6891203
theorem B12251027 : Blo 2149435 12251027 := bstep (se 1 (by rfl) ⟨9188270, by rfl⟩ : syracuseStep 12251027 = 18376541) B18376541
theorem B8167351 : Blo 2149435 8167351 := bstep (se 1 (by rfl) ⟨6125513, by rfl⟩ : syracuseStep 8167351 = 12251027) B12251027
theorem B10889801 : Blo 2149435 10889801 := bstep (se 2 (by rfl) ⟨4083675, by rfl⟩ : syracuseStep 10889801 = 8167351) B8167351
theorem B7259867 : Blo 2149435 7259867 := bstep (se 1 (by rfl) ⟨5444900, by rfl⟩ : syracuseStep 7259867 = 10889801) B10889801
theorem B4839911 : Blo 2149435 4839911 := bstep (se 1 (by rfl) ⟨3629933, by rfl⟩ : syracuseStep 4839911 = 7259867) B7259867
theorem B3226607 : Blo 2149435 3226607 := bstep (se 1 (by rfl) ⟨2419955, by rfl⟩ : syracuseStep 3226607 = 4839911) B4839911
theorem B2151071 : Blo 2149435 2151071 := bstep (se 1 (by rfl) ⟨1613303, by rfl⟩ : syracuseStep 2151071 = 3226607) B3226607
theorem B3226613 : Blo 2149435 3226613 := bbase (se 5 (by rfl) ⟨151247, by rfl⟩ : syracuseStep 3226613 = 302495) (by norm_num)
theorem B2151075 : Blo 2149435 2151075 := bstep (se 1 (by rfl) ⟨1613306, by rfl⟩ : syracuseStep 2151075 = 3226613) B3226613
theorem B4905965 : Blo 2149435 4905965 := bbase (se 3 (by rfl) ⟨919868, by rfl⟩ : syracuseStep 4905965 = 1839737) (by norm_num)
theorem B13082573 : Blo 2149435 13082573 := bstep (se 3 (by rfl) ⟨2452982, by rfl⟩ : syracuseStep 13082573 = 4905965) B4905965
theorem B8721715 : Blo 2149435 8721715 := bstep (se 1 (by rfl) ⟨6541286, by rfl⟩ : syracuseStep 8721715 = 13082573) B13082573
theorem B11628953 : Blo 2149435 11628953 := bstep (se 2 (by rfl) ⟨4360857, by rfl⟩ : syracuseStep 11628953 = 8721715) B8721715
theorem B7752635 : Blo 2149435 7752635 := bstep (se 1 (by rfl) ⟨5814476, by rfl⟩ : syracuseStep 7752635 = 11628953) B11628953
theorem B5168423 : Blo 2149435 5168423 := bstep (se 1 (by rfl) ⟨3876317, by rfl⟩ : syracuseStep 5168423 = 7752635) B7752635
theorem B3445615 : Blo 2149435 3445615 := bstep (se 1 (by rfl) ⟨2584211, by rfl⟩ : syracuseStep 3445615 = 5168423) B5168423
theorem B4594153 : Blo 2149435 4594153 := bstep (se 2 (by rfl) ⟨1722807, by rfl⟩ : syracuseStep 4594153 = 3445615) B3445615
theorem B6125537 : Blo 2149435 6125537 := bstep (se 2 (by rfl) ⟨2297076, by rfl⟩ : syracuseStep 6125537 = 4594153) B4594153
theorem B4083691 : Blo 2149435 4083691 := bstep (se 1 (by rfl) ⟨3062768, by rfl⟩ : syracuseStep 4083691 = 6125537) B6125537
theorem B5444921 : Blo 2149435 5444921 := bstep (se 2 (by rfl) ⟨2041845, by rfl⟩ : syracuseStep 5444921 = 4083691) B4083691
theorem B3629947 : Blo 2149435 3629947 := bstep (se 1 (by rfl) ⟨2722460, by rfl⟩ : syracuseStep 3629947 = 5444921) B5444921
theorem B4839929 : Blo 2149435 4839929 := bstep (se 2 (by rfl) ⟨1814973, by rfl⟩ : syracuseStep 4839929 = 3629947) B3629947
theorem B3226619 : Blo 2149435 3226619 := bstep (se 1 (by rfl) ⟨2419964, by rfl⟩ : syracuseStep 3226619 = 4839929) B4839929
theorem B2151079 : Blo 2149435 2151079 := bstep (se 1 (by rfl) ⟨1613309, by rfl⟩ : syracuseStep 2151079 = 3226619) B3226619
theorem B2419969 : Blo 2149435 2419969 := bbase (se 2 (by rfl) ⟨907488, by rfl⟩ : syracuseStep 2419969 = 1814977) (by norm_num)
theorem B3226625 : Blo 2149435 3226625 := bstep (se 2 (by rfl) ⟨1209984, by rfl⟩ : syracuseStep 3226625 = 2419969) B2419969
theorem B2151083 : Blo 2149435 2151083 := bstep (se 1 (by rfl) ⟨1613312, by rfl⟩ : syracuseStep 2151083 = 3226625) B3226625
theorem B5444941 : Blo 2149435 5444941 := bbase (se 3 (by rfl) ⟨1020926, by rfl⟩ : syracuseStep 5444941 = 2041853) (by norm_num)
theorem B7259921 : Blo 2149435 7259921 := bstep (se 2 (by rfl) ⟨2722470, by rfl⟩ : syracuseStep 7259921 = 5444941) B5444941
theorem B4839947 : Blo 2149435 4839947 := bstep (se 1 (by rfl) ⟨3629960, by rfl⟩ : syracuseStep 4839947 = 7259921) B7259921
theorem B3226631 : Blo 2149435 3226631 := bstep (se 1 (by rfl) ⟨2419973, by rfl⟩ : syracuseStep 3226631 = 4839947) B4839947
theorem B2151087 : Blo 2149435 2151087 := bstep (se 1 (by rfl) ⟨1613315, by rfl⟩ : syracuseStep 2151087 = 3226631) B3226631
theorem B3226637 : Blo 2149435 3226637 := bbase (se 3 (by rfl) ⟨604994, by rfl⟩ : syracuseStep 3226637 = 1209989) (by norm_num)
theorem B2151091 : Blo 2149435 2151091 := bstep (se 1 (by rfl) ⟨1613318, by rfl⟩ : syracuseStep 2151091 = 3226637) B3226637
theorem B4839965 : Blo 2149435 4839965 := bbase (se 3 (by rfl) ⟨907493, by rfl⟩ : syracuseStep 4839965 = 1814987) (by norm_num)
theorem B3226643 : Blo 2149435 3226643 := bstep (se 1 (by rfl) ⟨2419982, by rfl⟩ : syracuseStep 3226643 = 4839965) B4839965
theorem B2151095 : Blo 2149435 2151095 := bstep (se 1 (by rfl) ⟨1613321, by rfl⟩ : syracuseStep 2151095 = 3226643) B3226643
theorem B3629981 : Blo 2149435 3629981 := bbase (se 3 (by rfl) ⟨680621, by rfl⟩ : syracuseStep 3629981 = 1361243) (by norm_num)
theorem B2419987 : Blo 2149435 2419987 := bstep (se 1 (by rfl) ⟨1814990, by rfl⟩ : syracuseStep 2419987 = 3629981) B3629981
theorem B3226649 : Blo 2149435 3226649 := bstep (se 2 (by rfl) ⟨1209993, by rfl⟩ : syracuseStep 3226649 = 2419987) B2419987
theorem B2151099 : Blo 2149435 2151099 := bstep (se 1 (by rfl) ⟨1613324, by rfl⟩ : syracuseStep 2151099 = 3226649) B3226649
theorem B2453009 : Blo 2149435 2453009 := bbase (se 2 (by rfl) ⟨919878, by rfl⟩ : syracuseStep 2453009 = 1839757) (by norm_num)
theorem B26165429 : Blo 2149435 26165429 := bstep (se 5 (by rfl) ⟨1226504, by rfl⟩ : syracuseStep 26165429 = 2453009) B2453009
theorem B17443619 : Blo 2149435 17443619 := bstep (se 1 (by rfl) ⟨13082714, by rfl⟩ : syracuseStep 17443619 = 26165429) B26165429
theorem B11629079 : Blo 2149435 11629079 := bstep (se 1 (by rfl) ⟨8721809, by rfl⟩ : syracuseStep 11629079 = 17443619) B17443619
theorem B7752719 : Blo 2149435 7752719 := bstep (se 1 (by rfl) ⟨5814539, by rfl⟩ : syracuseStep 7752719 = 11629079) B11629079
theorem B20673917 : Blo 2149435 20673917 := bstep (se 3 (by rfl) ⟨3876359, by rfl⟩ : syracuseStep 20673917 = 7752719) B7752719
theorem B13782611 : Blo 2149435 13782611 := bstep (se 1 (by rfl) ⟨10336958, by rfl⟩ : syracuseStep 13782611 = 20673917) B20673917
theorem B9188407 : Blo 2149435 9188407 := bstep (se 1 (by rfl) ⟨6891305, by rfl⟩ : syracuseStep 9188407 = 13782611) B13782611
theorem B12251209 : Blo 2149435 12251209 := bstep (se 2 (by rfl) ⟨4594203, by rfl⟩ : syracuseStep 12251209 = 9188407) B9188407
theorem B16334945 : Blo 2149435 16334945 := bstep (se 2 (by rfl) ⟨6125604, by rfl⟩ : syracuseStep 16334945 = 12251209) B12251209
theorem B10889963 : Blo 2149435 10889963 := bstep (se 1 (by rfl) ⟨8167472, by rfl⟩ : syracuseStep 10889963 = 16334945) B16334945
theorem B7259975 : Blo 2149435 7259975 := bstep (se 1 (by rfl) ⟨5444981, by rfl⟩ : syracuseStep 7259975 = 10889963) B10889963
theorem B4839983 : Blo 2149435 4839983 := bstep (se 1 (by rfl) ⟨3629987, by rfl⟩ : syracuseStep 4839983 = 7259975) B7259975
theorem B3226655 : Blo 2149435 3226655 := bstep (se 1 (by rfl) ⟨2419991, by rfl⟩ : syracuseStep 3226655 = 4839983) B4839983
theorem B2151103 : Blo 2149435 2151103 := bstep (se 1 (by rfl) ⟨1613327, by rfl⟩ : syracuseStep 2151103 = 3226655) B3226655
theorem B3226661 : Blo 2149435 3226661 := bbase (se 4 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 3226661 = 604999) (by norm_num)
theorem B2151107 : Blo 2149435 2151107 := bstep (se 1 (by rfl) ⟨1613330, by rfl⟩ : syracuseStep 2151107 = 3226661) B3226661
theorem B2722501 : Blo 2149435 2722501 := bbase (se 4 (by rfl) ⟨255234, by rfl⟩ : syracuseStep 2722501 = 510469) (by norm_num)
theorem B3630001 : Blo 2149435 3630001 := bstep (se 2 (by rfl) ⟨1361250, by rfl⟩ : syracuseStep 3630001 = 2722501) B2722501
theorem B4840001 : Blo 2149435 4840001 := bstep (se 2 (by rfl) ⟨1815000, by rfl⟩ : syracuseStep 4840001 = 3630001) B3630001
theorem B3226667 : Blo 2149435 3226667 := bstep (se 1 (by rfl) ⟨2420000, by rfl⟩ : syracuseStep 3226667 = 4840001) B4840001
theorem B2151111 : Blo 2149435 2151111 := bstep (se 1 (by rfl) ⟨1613333, by rfl⟩ : syracuseStep 2151111 = 3226667) B3226667
theorem B2420005 : Blo 2149435 2420005 := bbase (se 4 (by rfl) ⟨226875, by rfl⟩ : syracuseStep 2420005 = 453751) (by norm_num)
theorem B3226673 : Blo 2149435 3226673 := bstep (se 2 (by rfl) ⟨1210002, by rfl⟩ : syracuseStep 3226673 = 2420005) B2420005
theorem B2151115 : Blo 2149435 2151115 := bstep (se 1 (by rfl) ⟨1613336, by rfl⟩ : syracuseStep 2151115 = 3226673) B3226673
theorem B8721877 : Blo 2149435 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B11629169 : Blo 2149435 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B7752779 : Blo 2149435 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B5168519 : Blo 2149435 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B3445679 : Blo 2149435 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B9188477 : Blo 2149435 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B6125651 : Blo 2149435 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B4083767 : Blo 2149435 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B2722511 : Blo 2149435 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B7260029 : Blo 2149435 7260029 := bstep (se 3 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 7260029 = 2722511) B2722511
theorem B4840019 : Blo 2149435 4840019 := bstep (se 1 (by rfl) ⟨3630014, by rfl⟩ : syracuseStep 4840019 = 7260029) B7260029
theorem B3226679 : Blo 2149435 3226679 := bstep (se 1 (by rfl) ⟨2420009, by rfl⟩ : syracuseStep 3226679 = 4840019) B4840019
theorem B2151119 : Blo 2149435 2151119 := bstep (se 1 (by rfl) ⟨1613339, by rfl⟩ : syracuseStep 2151119 = 3226679) B3226679
theorem B3226685 : Blo 2149435 3226685 := bbase (se 3 (by rfl) ⟨605003, by rfl⟩ : syracuseStep 3226685 = 1210007) (by norm_num)
theorem B2151123 : Blo 2149435 2151123 := bstep (se 1 (by rfl) ⟨1613342, by rfl⟩ : syracuseStep 2151123 = 3226685) B3226685
theorem B4840037 : Blo 2149435 4840037 := bbase (se 4 (by rfl) ⟨453753, by rfl⟩ : syracuseStep 4840037 = 907507) (by norm_num)
theorem B3226691 : Blo 2149435 3226691 := bstep (se 1 (by rfl) ⟨2420018, by rfl⟩ : syracuseStep 3226691 = 4840037) B4840037
theorem B2151127 : Blo 2149435 2151127 := bstep (se 1 (by rfl) ⟨1613345, by rfl⟩ : syracuseStep 2151127 = 3226691) B3226691
theorem B5445053 : Blo 2149435 5445053 := bbase (se 3 (by rfl) ⟨1020947, by rfl⟩ : syracuseStep 5445053 = 2041895) (by norm_num)
theorem B3630035 : Blo 2149435 3630035 := bstep (se 1 (by rfl) ⟨2722526, by rfl⟩ : syracuseStep 3630035 = 5445053) B5445053
theorem B2420023 : Blo 2149435 2420023 := bstep (se 1 (by rfl) ⟨1815017, by rfl⟩ : syracuseStep 2420023 = 3630035) B3630035
theorem B3226697 : Blo 2149435 3226697 := bstep (se 2 (by rfl) ⟨1210011, by rfl⟩ : syracuseStep 3226697 = 2420023) B2420023
theorem B2151131 : Blo 2149435 2151131 := bstep (se 1 (by rfl) ⟨1613348, by rfl⟩ : syracuseStep 2151131 = 3226697) B3226697
theorem B4083797 : Blo 2149435 4083797 := bbase (se 8 (by rfl) ⟨23928, by rfl⟩ : syracuseStep 4083797 = 47857) (by norm_num)
theorem B10890125 : Blo 2149435 10890125 := bstep (se 3 (by rfl) ⟨2041898, by rfl⟩ : syracuseStep 10890125 = 4083797) B4083797
theorem B7260083 : Blo 2149435 7260083 := bstep (se 1 (by rfl) ⟨5445062, by rfl⟩ : syracuseStep 7260083 = 10890125) B10890125
theorem B4840055 : Blo 2149435 4840055 := bstep (se 1 (by rfl) ⟨3630041, by rfl⟩ : syracuseStep 4840055 = 7260083) B7260083
theorem B3226703 : Blo 2149435 3226703 := bstep (se 1 (by rfl) ⟨2420027, by rfl⟩ : syracuseStep 3226703 = 4840055) B4840055
theorem B2151135 : Blo 2149435 2151135 := bstep (se 1 (by rfl) ⟨1613351, by rfl⟩ : syracuseStep 2151135 = 3226703) B3226703
theorem B3226709 : Blo 2149435 3226709 := bbase (se 8 (by rfl) ⟨18906, by rfl⟩ : syracuseStep 3226709 = 37813) (by norm_num)
theorem B2151139 : Blo 2149435 2151139 := bstep (se 1 (by rfl) ⟨1613354, by rfl⟩ : syracuseStep 2151139 = 3226709) B3226709
theorem B13782869 : Blo 2149435 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B9188579 : Blo 2149435 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B6125719 : Blo 2149435 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B8167625 : Blo 2149435 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B5445083 : Blo 2149435 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B3630055 : Blo 2149435 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B4840073 : Blo 2149435 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B3226715 : Blo 2149435 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B2151143 : Blo 2149435 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B2420041 : Blo 2149435 2420041 := bbase (se 2 (by rfl) ⟨907515, by rfl⟩ : syracuseStep 2420041 = 1815031) (by norm_num)
theorem B3226721 : Blo 2149435 3226721 := bstep (se 2 (by rfl) ⟨1210020, by rfl⟩ : syracuseStep 3226721 = 2420041) B2420041
theorem B2151147 : Blo 2149435 2151147 := bstep (se 1 (by rfl) ⟨1613360, by rfl⟩ : syracuseStep 2151147 = 3226721) B3226721
theorem B2180501 : Blo 2149435 2180501 := bbase (se 6 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 2180501 = 102211) (by norm_num)
theorem B23258677 : Blo 2149435 23258677 := bstep (se 5 (by rfl) ⟨1090250, by rfl⟩ : syracuseStep 23258677 = 2180501) B2180501
theorem B31011569 : Blo 2149435 31011569 := bstep (se 2 (by rfl) ⟨11629338, by rfl⟩ : syracuseStep 31011569 = 23258677) B23258677
theorem B20674379 : Blo 2149435 20674379 := bstep (se 1 (by rfl) ⟨15505784, by rfl⟩ : syracuseStep 20674379 = 31011569) B31011569
theorem B13782919 : Blo 2149435 13782919 := bstep (se 1 (by rfl) ⟨10337189, by rfl⟩ : syracuseStep 13782919 = 20674379) B20674379
theorem B18377225 : Blo 2149435 18377225 := bstep (se 2 (by rfl) ⟨6891459, by rfl⟩ : syracuseStep 18377225 = 13782919) B13782919
theorem B12251483 : Blo 2149435 12251483 := bstep (se 1 (by rfl) ⟨9188612, by rfl⟩ : syracuseStep 12251483 = 18377225) B18377225
theorem B8167655 : Blo 2149435 8167655 := bstep (se 1 (by rfl) ⟨6125741, by rfl⟩ : syracuseStep 8167655 = 12251483) B12251483
theorem B5445103 : Blo 2149435 5445103 := bstep (se 1 (by rfl) ⟨4083827, by rfl⟩ : syracuseStep 5445103 = 8167655) B8167655
theorem B7260137 : Blo 2149435 7260137 := bstep (se 2 (by rfl) ⟨2722551, by rfl⟩ : syracuseStep 7260137 = 5445103) B5445103
theorem B4840091 : Blo 2149435 4840091 := bstep (se 1 (by rfl) ⟨3630068, by rfl⟩ : syracuseStep 4840091 = 7260137) B7260137
theorem B3226727 : Blo 2149435 3226727 := bstep (se 1 (by rfl) ⟨2420045, by rfl⟩ : syracuseStep 3226727 = 4840091) B4840091
theorem B2151151 : Blo 2149435 2151151 := bstep (se 1 (by rfl) ⟨1613363, by rfl⟩ : syracuseStep 2151151 = 3226727) B3226727
theorem B3226733 : Blo 2149435 3226733 := bbase (se 3 (by rfl) ⟨605012, by rfl⟩ : syracuseStep 3226733 = 1210025) (by norm_num)
theorem B2151155 : Blo 2149435 2151155 := bstep (se 1 (by rfl) ⟨1613366, by rfl⟩ : syracuseStep 2151155 = 3226733) B3226733
theorem B4840109 : Blo 2149435 4840109 := bbase (se 3 (by rfl) ⟨907520, by rfl⟩ : syracuseStep 4840109 = 1815041) (by norm_num)
theorem B3226739 : Blo 2149435 3226739 := bstep (se 1 (by rfl) ⟨2420054, by rfl⟩ : syracuseStep 3226739 = 4840109) B4840109
theorem B2151159 : Blo 2149435 2151159 := bstep (se 1 (by rfl) ⟨1613369, by rfl⟩ : syracuseStep 2151159 = 3226739) B3226739
theorem B4594333 : Blo 2149435 4594333 := bbase (se 3 (by rfl) ⟨861437, by rfl⟩ : syracuseStep 4594333 = 1722875) (by norm_num)
theorem B6125777 : Blo 2149435 6125777 := bstep (se 2 (by rfl) ⟨2297166, by rfl⟩ : syracuseStep 6125777 = 4594333) B4594333
theorem B4083851 : Blo 2149435 4083851 := bstep (se 1 (by rfl) ⟨3062888, by rfl⟩ : syracuseStep 4083851 = 6125777) B6125777
theorem B2722567 : Blo 2149435 2722567 := bstep (se 1 (by rfl) ⟨2041925, by rfl⟩ : syracuseStep 2722567 = 4083851) B4083851
theorem B3630089 : Blo 2149435 3630089 := bstep (se 2 (by rfl) ⟨1361283, by rfl⟩ : syracuseStep 3630089 = 2722567) B2722567
theorem B2420059 : Blo 2149435 2420059 := bstep (se 1 (by rfl) ⟨1815044, by rfl⟩ : syracuseStep 2420059 = 3630089) B3630089
theorem B3226745 : Blo 2149435 3226745 := bstep (se 2 (by rfl) ⟨1210029, by rfl⟩ : syracuseStep 3226745 = 2420059) B2420059
theorem B2151163 : Blo 2149435 2151163 := bstep (se 1 (by rfl) ⟨1613372, by rfl⟩ : syracuseStep 2151163 = 3226745) B3226745
theorem B31011797 : Blo 2149435 31011797 := bbase (se 7 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 31011797 = 726839) (by norm_num)
theorem B20674531 : Blo 2149435 20674531 := bstep (se 1 (by rfl) ⟨15505898, by rfl⟩ : syracuseStep 20674531 = 31011797) B31011797
theorem B27566041 : Blo 2149435 27566041 := bstep (se 2 (by rfl) ⟨10337265, by rfl⟩ : syracuseStep 27566041 = 20674531) B20674531
theorem B36754721 : Blo 2149435 36754721 := bstep (se 2 (by rfl) ⟨13783020, by rfl⟩ : syracuseStep 36754721 = 27566041) B27566041
theorem B24503147 : Blo 2149435 24503147 := bstep (se 1 (by rfl) ⟨18377360, by rfl⟩ : syracuseStep 24503147 = 36754721) B36754721
theorem B16335431 : Blo 2149435 16335431 := bstep (se 1 (by rfl) ⟨12251573, by rfl⟩ : syracuseStep 16335431 = 24503147) B24503147
theorem B10890287 : Blo 2149435 10890287 := bstep (se 1 (by rfl) ⟨8167715, by rfl⟩ : syracuseStep 10890287 = 16335431) B16335431
theorem B7260191 : Blo 2149435 7260191 := bstep (se 1 (by rfl) ⟨5445143, by rfl⟩ : syracuseStep 7260191 = 10890287) B10890287
theorem B4840127 : Blo 2149435 4840127 := bstep (se 1 (by rfl) ⟨3630095, by rfl⟩ : syracuseStep 4840127 = 7260191) B7260191
theorem B3226751 : Blo 2149435 3226751 := bstep (se 1 (by rfl) ⟨2420063, by rfl⟩ : syracuseStep 3226751 = 4840127) B4840127
theorem B2151167 : Blo 2149435 2151167 := bstep (se 1 (by rfl) ⟨1613375, by rfl⟩ : syracuseStep 2151167 = 3226751) B3226751
theorem B3226757 : Blo 2149435 3226757 := bbase (se 4 (by rfl) ⟨302508, by rfl⟩ : syracuseStep 3226757 = 605017) (by norm_num)
theorem B2151171 : Blo 2149435 2151171 := bstep (se 1 (by rfl) ⟨1613378, by rfl⟩ : syracuseStep 2151171 = 3226757) B3226757
theorem B3630109 : Blo 2149435 3630109 := bbase (se 3 (by rfl) ⟨680645, by rfl⟩ : syracuseStep 3630109 = 1361291) (by norm_num)
theorem B4840145 : Blo 2149435 4840145 := bstep (se 2 (by rfl) ⟨1815054, by rfl⟩ : syracuseStep 4840145 = 3630109) B3630109
theorem B3226763 : Blo 2149435 3226763 := bstep (se 1 (by rfl) ⟨2420072, by rfl⟩ : syracuseStep 3226763 = 4840145) B4840145
theorem B2151175 : Blo 2149435 2151175 := bstep (se 1 (by rfl) ⟨1613381, by rfl⟩ : syracuseStep 2151175 = 3226763) B3226763
theorem B2420077 : Blo 2149435 2420077 := bbase (se 3 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 2420077 = 907529) (by norm_num)
theorem B3226769 : Blo 2149435 3226769 := bstep (se 2 (by rfl) ⟨1210038, by rfl⟩ : syracuseStep 3226769 = 2420077) B2420077
theorem B2151179 : Blo 2149435 2151179 := bstep (se 1 (by rfl) ⟨1613384, by rfl⟩ : syracuseStep 2151179 = 3226769) B3226769
theorem B7260245 : Blo 2149435 7260245 := bbase (se 8 (by rfl) ⟨42540, by rfl⟩ : syracuseStep 7260245 = 85081) (by norm_num)
theorem B4840163 : Blo 2149435 4840163 := bstep (se 1 (by rfl) ⟨3630122, by rfl⟩ : syracuseStep 4840163 = 7260245) B7260245
theorem B3226775 : Blo 2149435 3226775 := bstep (se 1 (by rfl) ⟨2420081, by rfl⟩ : syracuseStep 3226775 = 4840163) B4840163
theorem B2151183 : Blo 2149435 2151183 := bstep (se 1 (by rfl) ⟨1613387, by rfl⟩ : syracuseStep 2151183 = 3226775) B3226775
theorem B3226781 : Blo 2149435 3226781 := bbase (se 3 (by rfl) ⟨605021, by rfl⟩ : syracuseStep 3226781 = 1210043) (by norm_num)
theorem B2151187 : Blo 2149435 2151187 := bstep (se 1 (by rfl) ⟨1613390, by rfl⟩ : syracuseStep 2151187 = 3226781) B3226781
theorem B4840181 : Blo 2149435 4840181 := bbase (se 5 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 4840181 = 453767) (by norm_num)
theorem B3226787 : Blo 2149435 3226787 := bstep (se 1 (by rfl) ⟨2420090, by rfl⟩ : syracuseStep 3226787 = 4840181) B4840181
theorem B2151191 : Blo 2149435 2151191 := bstep (se 1 (by rfl) ⟨1613393, by rfl⟩ : syracuseStep 2151191 = 3226787) B3226787
theorem B5168701 : Blo 2149435 5168701 := bbase (se 3 (by rfl) ⟨969131, by rfl⟩ : syracuseStep 5168701 = 1938263) (by norm_num)
theorem B27566405 : Blo 2149435 27566405 := bstep (se 4 (by rfl) ⟨2584350, by rfl⟩ : syracuseStep 27566405 = 5168701) B5168701
theorem B18377603 : Blo 2149435 18377603 := bstep (se 1 (by rfl) ⟨13783202, by rfl⟩ : syracuseStep 18377603 = 27566405) B27566405
theorem B12251735 : Blo 2149435 12251735 := bstep (se 1 (by rfl) ⟨9188801, by rfl⟩ : syracuseStep 12251735 = 18377603) B18377603
theorem B8167823 : Blo 2149435 8167823 := bstep (se 1 (by rfl) ⟨6125867, by rfl⟩ : syracuseStep 8167823 = 12251735) B12251735
theorem B5445215 : Blo 2149435 5445215 := bstep (se 1 (by rfl) ⟨4083911, by rfl⟩ : syracuseStep 5445215 = 8167823) B8167823
theorem B3630143 : Blo 2149435 3630143 := bstep (se 1 (by rfl) ⟨2722607, by rfl⟩ : syracuseStep 3630143 = 5445215) B5445215
theorem B2420095 : Blo 2149435 2420095 := bstep (se 1 (by rfl) ⟨1815071, by rfl⟩ : syracuseStep 2420095 = 3630143) B3630143
theorem B3226793 : Blo 2149435 3226793 := bstep (se 2 (by rfl) ⟨1210047, by rfl⟩ : syracuseStep 3226793 = 2420095) B2420095
theorem B2151195 : Blo 2149435 2151195 := bstep (se 1 (by rfl) ⟨1613396, by rfl⟩ : syracuseStep 2151195 = 3226793) B3226793
theorem B5748533 : Blo 2149435 5748533 := bbase (se 5 (by rfl) ⟨269462, by rfl⟩ : syracuseStep 5748533 = 538925) (by norm_num)
theorem B3832355 : Blo 2149435 3832355 := bstep (se 1 (by rfl) ⟨2874266, by rfl⟩ : syracuseStep 3832355 = 5748533) B5748533
theorem B2554903 : Blo 2149435 2554903 := bstep (se 1 (by rfl) ⟨1916177, by rfl⟩ : syracuseStep 2554903 = 3832355) B3832355
theorem B3406537 : Blo 2149435 3406537 := bstep (se 2 (by rfl) ⟨1277451, by rfl⟩ : syracuseStep 3406537 = 2554903) B2554903
theorem B4542049 : Blo 2149435 4542049 := bstep (se 2 (by rfl) ⟨1703268, by rfl⟩ : syracuseStep 4542049 = 3406537) B3406537
theorem B6056065 : Blo 2149435 6056065 := bstep (se 2 (by rfl) ⟨2271024, by rfl⟩ : syracuseStep 6056065 = 4542049) B4542049
theorem B32299013 : Blo 2149435 32299013 := bstep (se 4 (by rfl) ⟨3028032, by rfl⟩ : syracuseStep 32299013 = 6056065) B6056065
theorem B21532675 : Blo 2149435 21532675 := bstep (se 1 (by rfl) ⟨16149506, by rfl⟩ : syracuseStep 21532675 = 32299013) B32299013
theorem B28710233 : Blo 2149435 28710233 := bstep (se 2 (by rfl) ⟨10766337, by rfl⟩ : syracuseStep 28710233 = 21532675) B21532675
theorem B19140155 : Blo 2149435 19140155 := bstep (se 1 (by rfl) ⟨14355116, by rfl⟩ : syracuseStep 19140155 = 28710233) B28710233
theorem B12760103 : Blo 2149435 12760103 := bstep (se 1 (by rfl) ⟨9570077, by rfl⟩ : syracuseStep 12760103 = 19140155) B19140155
theorem B34026941 : Blo 2149435 34026941 := bstep (se 3 (by rfl) ⟨6380051, by rfl⟩ : syracuseStep 34026941 = 12760103) B12760103
theorem B22684627 : Blo 2149435 22684627 := bstep (se 1 (by rfl) ⟨17013470, by rfl⟩ : syracuseStep 22684627 = 34026941) B34026941
theorem B30246169 : Blo 2149435 30246169 := bstep (se 2 (by rfl) ⟨11342313, by rfl⟩ : syracuseStep 30246169 = 22684627) B22684627
theorem B40328225 : Blo 2149435 40328225 := bstep (se 2 (by rfl) ⟨15123084, by rfl⟩ : syracuseStep 40328225 = 30246169) B30246169
theorem B26885483 : Blo 2149435 26885483 := bstep (se 1 (by rfl) ⟨20164112, by rfl⟩ : syracuseStep 26885483 = 40328225) B40328225
theorem B17923655 : Blo 2149435 17923655 := bstep (se 1 (by rfl) ⟨13442741, by rfl⟩ : syracuseStep 17923655 = 26885483) B26885483
theorem B11949103 : Blo 2149435 11949103 := bstep (se 1 (by rfl) ⟨8961827, by rfl⟩ : syracuseStep 11949103 = 17923655) B17923655
theorem B15932137 : Blo 2149435 15932137 := bstep (se 2 (by rfl) ⟨5974551, by rfl⟩ : syracuseStep 15932137 = 11949103) B11949103
theorem B21242849 : Blo 2149435 21242849 := bstep (se 2 (by rfl) ⟨7966068, by rfl⟩ : syracuseStep 21242849 = 15932137) B15932137
theorem B226590389 : Blo 2149435 226590389 := bstep (se 5 (by rfl) ⟨10621424, by rfl⟩ : syracuseStep 226590389 = 21242849) B21242849
theorem B151060259 : Blo 2149435 151060259 := bstep (se 1 (by rfl) ⟨113295194, by rfl⟩ : syracuseStep 151060259 = 226590389) B226590389
theorem B402827357 : Blo 2149435 402827357 := bstep (se 3 (by rfl) ⟨75530129, by rfl⟩ : syracuseStep 402827357 = 151060259) B151060259
theorem B268551571 : Blo 2149435 268551571 := bstep (se 1 (by rfl) ⟨201413678, by rfl⟩ : syracuseStep 268551571 = 402827357) B402827357
theorem B358068761 : Blo 2149435 358068761 := bstep (se 2 (by rfl) ⟨134275785, by rfl⟩ : syracuseStep 358068761 = 268551571) B268551571
theorem B238712507 : Blo 2149435 238712507 := bstep (se 1 (by rfl) ⟨179034380, by rfl⟩ : syracuseStep 238712507 = 358068761) B358068761
theorem B159141671 : Blo 2149435 159141671 := bstep (se 1 (by rfl) ⟨119356253, by rfl⟩ : syracuseStep 159141671 = 238712507) B238712507
theorem B106094447 : Blo 2149435 106094447 := bstep (se 1 (by rfl) ⟨79570835, by rfl⟩ : syracuseStep 106094447 = 159141671) B159141671
theorem B70729631 : Blo 2149435 70729631 := bstep (se 1 (by rfl) ⟨53047223, by rfl⟩ : syracuseStep 70729631 = 106094447) B106094447
theorem B47153087 : Blo 2149435 47153087 := bstep (se 1 (by rfl) ⟨35364815, by rfl⟩ : syracuseStep 47153087 = 70729631) B70729631
theorem B31435391 : Blo 2149435 31435391 := bstep (se 1 (by rfl) ⟨23576543, by rfl⟩ : syracuseStep 31435391 = 47153087) B47153087
theorem B20956927 : Blo 2149435 20956927 := bstep (se 1 (by rfl) ⟨15717695, by rfl⟩ : syracuseStep 20956927 = 31435391) B31435391
theorem B27942569 : Blo 2149435 27942569 := bstep (se 2 (by rfl) ⟨10478463, by rfl⟩ : syracuseStep 27942569 = 20956927) B20956927
theorem B18628379 : Blo 2149435 18628379 := bstep (se 1 (by rfl) ⟨13971284, by rfl⟩ : syracuseStep 18628379 = 27942569) B27942569
theorem B12418919 : Blo 2149435 12418919 := bstep (se 1 (by rfl) ⟨9314189, by rfl⟩ : syracuseStep 12418919 = 18628379) B18628379
theorem B8279279 : Blo 2149435 8279279 := bstep (se 1 (by rfl) ⟨6209459, by rfl⟩ : syracuseStep 8279279 = 12418919) B12418919
theorem B5519519 : Blo 2149435 5519519 := bstep (se 1 (by rfl) ⟨4139639, by rfl⟩ : syracuseStep 5519519 = 8279279) B8279279
theorem B3679679 : Blo 2149435 3679679 := bstep (se 1 (by rfl) ⟨2759759, by rfl⟩ : syracuseStep 3679679 = 5519519) B5519519
theorem B9812477 : Blo 2149435 9812477 := bstep (se 3 (by rfl) ⟨1839839, by rfl⟩ : syracuseStep 9812477 = 3679679) B3679679
theorem B6541651 : Blo 2149435 6541651 := bstep (se 1 (by rfl) ⟨4906238, by rfl⟩ : syracuseStep 6541651 = 9812477) B9812477
theorem B8722201 : Blo 2149435 8722201 := bstep (se 2 (by rfl) ⟨3270825, by rfl⟩ : syracuseStep 8722201 = 6541651) B6541651
theorem B11629601 : Blo 2149435 11629601 := bstep (se 2 (by rfl) ⟨4361100, by rfl⟩ : syracuseStep 11629601 = 8722201) B8722201
theorem B7753067 : Blo 2149435 7753067 := bstep (se 1 (by rfl) ⟨5814800, by rfl⟩ : syracuseStep 7753067 = 11629601) B11629601
theorem B5168711 : Blo 2149435 5168711 := bstep (se 1 (by rfl) ⟨3876533, by rfl⟩ : syracuseStep 5168711 = 7753067) B7753067
theorem B3445807 : Blo 2149435 3445807 := bstep (se 1 (by rfl) ⟨2584355, by rfl⟩ : syracuseStep 3445807 = 5168711) B5168711
theorem B4594409 : Blo 2149435 4594409 := bstep (se 2 (by rfl) ⟨1722903, by rfl⟩ : syracuseStep 4594409 = 3445807) B3445807
theorem B3062939 : Blo 2149435 3062939 := bstep (se 1 (by rfl) ⟨2297204, by rfl⟩ : syracuseStep 3062939 = 4594409) B4594409
theorem B8167837 : Blo 2149435 8167837 := bstep (se 3 (by rfl) ⟨1531469, by rfl⟩ : syracuseStep 8167837 = 3062939) B3062939
theorem B10890449 : Blo 2149435 10890449 := bstep (se 2 (by rfl) ⟨4083918, by rfl⟩ : syracuseStep 10890449 = 8167837) B8167837
theorem B7260299 : Blo 2149435 7260299 := bstep (se 1 (by rfl) ⟨5445224, by rfl⟩ : syracuseStep 7260299 = 10890449) B10890449
theorem B4840199 : Blo 2149435 4840199 := bstep (se 1 (by rfl) ⟨3630149, by rfl⟩ : syracuseStep 4840199 = 7260299) B7260299
theorem B3226799 : Blo 2149435 3226799 := bstep (se 1 (by rfl) ⟨2420099, by rfl⟩ : syracuseStep 3226799 = 4840199) B4840199
theorem B2151199 : Blo 2149435 2151199 := bstep (se 1 (by rfl) ⟨1613399, by rfl⟩ : syracuseStep 2151199 = 3226799) B3226799
theorem B3226805 : Blo 2149435 3226805 := bbase (se 5 (by rfl) ⟨151256, by rfl⟩ : syracuseStep 3226805 = 302513) (by norm_num)
theorem B2151203 : Blo 2149435 2151203 := bstep (se 1 (by rfl) ⟨1613402, by rfl⟩ : syracuseStep 2151203 = 3226805) B3226805
theorem B5445245 : Blo 2149435 5445245 := bbase (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) (by norm_num)
theorem B3630163 : Blo 2149435 3630163 := bstep (se 1 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 3630163 = 5445245) B5445245
theorem B4840217 : Blo 2149435 4840217 := bstep (se 2 (by rfl) ⟨1815081, by rfl⟩ : syracuseStep 4840217 = 3630163) B3630163
theorem B3226811 : Blo 2149435 3226811 := bstep (se 1 (by rfl) ⟨2420108, by rfl⟩ : syracuseStep 3226811 = 4840217) B4840217
theorem B2151207 : Blo 2149435 2151207 := bstep (se 1 (by rfl) ⟨1613405, by rfl⟩ : syracuseStep 2151207 = 3226811) B3226811
theorem B2420113 : Blo 2149435 2420113 := bbase (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) (by norm_num)
theorem B3226817 : Blo 2149435 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B2151211 : Blo 2149435 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B4083949 : Blo 2149435 4083949 := bbase (se 3 (by rfl) ⟨765740, by rfl⟩ : syracuseStep 4083949 = 1531481) (by norm_num)
theorem B5445265 : Blo 2149435 5445265 := bstep (se 2 (by rfl) ⟨2041974, by rfl⟩ : syracuseStep 5445265 = 4083949) B4083949
theorem B7260353 : Blo 2149435 7260353 := bstep (se 2 (by rfl) ⟨2722632, by rfl⟩ : syracuseStep 7260353 = 5445265) B5445265
theorem B4840235 : Blo 2149435 4840235 := bstep (se 1 (by rfl) ⟨3630176, by rfl⟩ : syracuseStep 4840235 = 7260353) B7260353
theorem B3226823 : Blo 2149435 3226823 := bstep (se 1 (by rfl) ⟨2420117, by rfl⟩ : syracuseStep 3226823 = 4840235) B4840235
theorem B2151215 : Blo 2149435 2151215 := bstep (se 1 (by rfl) ⟨1613411, by rfl⟩ : syracuseStep 2151215 = 3226823) B3226823
theorem B3226829 : Blo 2149435 3226829 := bbase (se 3 (by rfl) ⟨605030, by rfl⟩ : syracuseStep 3226829 = 1210061) (by norm_num)
theorem B2151219 : Blo 2149435 2151219 := bstep (se 1 (by rfl) ⟨1613414, by rfl⟩ : syracuseStep 2151219 = 3226829) B3226829
theorem B4840253 : Blo 2149435 4840253 := bbase (se 3 (by rfl) ⟨907547, by rfl⟩ : syracuseStep 4840253 = 1815095) (by norm_num)
theorem B3226835 : Blo 2149435 3226835 := bstep (se 1 (by rfl) ⟨2420126, by rfl⟩ : syracuseStep 3226835 = 4840253) B4840253
theorem B2151223 : Blo 2149435 2151223 := bstep (se 1 (by rfl) ⟨1613417, by rfl⟩ : syracuseStep 2151223 = 3226835) B3226835
theorem B3630197 : Blo 2149435 3630197 := bbase (se 5 (by rfl) ⟨170165, by rfl⟩ : syracuseStep 3630197 = 340331) (by norm_num)
theorem B2420131 : Blo 2149435 2420131 := bstep (se 1 (by rfl) ⟨1815098, by rfl⟩ : syracuseStep 2420131 = 3630197) B3630197
theorem B3226841 : Blo 2149435 3226841 := bstep (se 2 (by rfl) ⟨1210065, by rfl⟩ : syracuseStep 3226841 = 2420131) B2420131
theorem B2151227 : Blo 2149435 2151227 := bstep (se 1 (by rfl) ⟨1613420, by rfl⟩ : syracuseStep 2151227 = 3226841) B3226841
theorem B4594477 : Blo 2149435 4594477 := bbase (se 3 (by rfl) ⟨861464, by rfl⟩ : syracuseStep 4594477 = 1722929) (by norm_num)
theorem B6125969 : Blo 2149435 6125969 := bstep (se 2 (by rfl) ⟨2297238, by rfl⟩ : syracuseStep 6125969 = 4594477) B4594477
theorem B16335917 : Blo 2149435 16335917 := bstep (se 3 (by rfl) ⟨3062984, by rfl⟩ : syracuseStep 16335917 = 6125969) B6125969
theorem B10890611 : Blo 2149435 10890611 := bstep (se 1 (by rfl) ⟨8167958, by rfl⟩ : syracuseStep 10890611 = 16335917) B16335917
theorem B7260407 : Blo 2149435 7260407 := bstep (se 1 (by rfl) ⟨5445305, by rfl⟩ : syracuseStep 7260407 = 10890611) B10890611
theorem B4840271 : Blo 2149435 4840271 := bstep (se 1 (by rfl) ⟨3630203, by rfl⟩ : syracuseStep 4840271 = 7260407) B7260407
theorem B3226847 : Blo 2149435 3226847 := bstep (se 1 (by rfl) ⟨2420135, by rfl⟩ : syracuseStep 3226847 = 4840271) B4840271
theorem B2151231 : Blo 2149435 2151231 := bstep (se 1 (by rfl) ⟨1613423, by rfl⟩ : syracuseStep 2151231 = 3226847) B3226847
theorem B3226853 : Blo 2149435 3226853 := bbase (se 4 (by rfl) ⟨302517, by rfl⟩ : syracuseStep 3226853 = 605035) (by norm_num)
theorem B2151235 : Blo 2149435 2151235 := bstep (se 1 (by rfl) ⟨1613426, by rfl⟩ : syracuseStep 2151235 = 3226853) B3226853
theorem B5519621 : Blo 2149435 5519621 := bbase (se 4 (by rfl) ⟨517464, by rfl⟩ : syracuseStep 5519621 = 1034929) (by norm_num)
theorem B14718989 : Blo 2149435 14718989 := bstep (se 3 (by rfl) ⟨2759810, by rfl⟩ : syracuseStep 14718989 = 5519621) B5519621
theorem B9812659 : Blo 2149435 9812659 := bstep (se 1 (by rfl) ⟨7359494, by rfl⟩ : syracuseStep 9812659 = 14718989) B14718989
theorem B13083545 : Blo 2149435 13083545 := bstep (se 2 (by rfl) ⟨4906329, by rfl⟩ : syracuseStep 13083545 = 9812659) B9812659
theorem B34889453 : Blo 2149435 34889453 := bstep (se 3 (by rfl) ⟨6541772, by rfl⟩ : syracuseStep 34889453 = 13083545) B13083545
theorem B23259635 : Blo 2149435 23259635 := bstep (se 1 (by rfl) ⟨17444726, by rfl⟩ : syracuseStep 23259635 = 34889453) B34889453
theorem B15506423 : Blo 2149435 15506423 := bstep (se 1 (by rfl) ⟨11629817, by rfl⟩ : syracuseStep 15506423 = 23259635) B23259635
theorem B10337615 : Blo 2149435 10337615 := bstep (se 1 (by rfl) ⟨7753211, by rfl⟩ : syracuseStep 10337615 = 15506423) B15506423
theorem B6891743 : Blo 2149435 6891743 := bstep (se 1 (by rfl) ⟨5168807, by rfl⟩ : syracuseStep 6891743 = 10337615) B10337615
theorem B4594495 : Blo 2149435 4594495 := bstep (se 1 (by rfl) ⟨3445871, by rfl⟩ : syracuseStep 4594495 = 6891743) B6891743
theorem B6125993 : Blo 2149435 6125993 := bstep (se 2 (by rfl) ⟨2297247, by rfl⟩ : syracuseStep 6125993 = 4594495) B4594495
theorem B4083995 : Blo 2149435 4083995 := bstep (se 1 (by rfl) ⟨3062996, by rfl⟩ : syracuseStep 4083995 = 6125993) B6125993
theorem B2722663 : Blo 2149435 2722663 := bstep (se 1 (by rfl) ⟨2041997, by rfl⟩ : syracuseStep 2722663 = 4083995) B4083995
theorem B3630217 : Blo 2149435 3630217 := bstep (se 2 (by rfl) ⟨1361331, by rfl⟩ : syracuseStep 3630217 = 2722663) B2722663
theorem B4840289 : Blo 2149435 4840289 := bstep (se 2 (by rfl) ⟨1815108, by rfl⟩ : syracuseStep 4840289 = 3630217) B3630217
theorem B3226859 : Blo 2149435 3226859 := bstep (se 1 (by rfl) ⟨2420144, by rfl⟩ : syracuseStep 3226859 = 4840289) B4840289
theorem B2151239 : Blo 2149435 2151239 := bstep (se 1 (by rfl) ⟨1613429, by rfl⟩ : syracuseStep 2151239 = 3226859) B3226859
theorem B2420149 : Blo 2149435 2420149 := bbase (se 5 (by rfl) ⟨113444, by rfl⟩ : syracuseStep 2420149 = 226889) (by norm_num)
theorem B3226865 : Blo 2149435 3226865 := bstep (se 2 (by rfl) ⟨1210074, by rfl⟩ : syracuseStep 3226865 = 2420149) B2420149
theorem B2151243 : Blo 2149435 2151243 := bstep (se 1 (by rfl) ⟨1613432, by rfl⟩ : syracuseStep 2151243 = 3226865) B3226865
theorem B2722673 : Blo 2149435 2722673 := bbase (se 2 (by rfl) ⟨1021002, by rfl⟩ : syracuseStep 2722673 = 2042005) (by norm_num)
theorem B7260461 : Blo 2149435 7260461 := bstep (se 3 (by rfl) ⟨1361336, by rfl⟩ : syracuseStep 7260461 = 2722673) B2722673
theorem B4840307 : Blo 2149435 4840307 := bstep (se 1 (by rfl) ⟨3630230, by rfl⟩ : syracuseStep 4840307 = 7260461) B7260461
theorem B3226871 : Blo 2149435 3226871 := bstep (se 1 (by rfl) ⟨2420153, by rfl⟩ : syracuseStep 3226871 = 4840307) B4840307
theorem B2151247 : Blo 2149435 2151247 := bstep (se 1 (by rfl) ⟨1613435, by rfl⟩ : syracuseStep 2151247 = 3226871) B3226871
theorem B3226877 : Blo 2149435 3226877 := bbase (se 3 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 3226877 = 1210079) (by norm_num)
theorem B2151251 : Blo 2149435 2151251 := bstep (se 1 (by rfl) ⟨1613438, by rfl⟩ : syracuseStep 2151251 = 3226877) B3226877
theorem B4840325 : Blo 2149435 4840325 := bbase (se 4 (by rfl) ⟨453780, by rfl⟩ : syracuseStep 4840325 = 907561) (by norm_num)
theorem B3226883 : Blo 2149435 3226883 := bstep (se 1 (by rfl) ⟨2420162, by rfl⟩ : syracuseStep 3226883 = 4840325) B4840325
theorem B2151255 : Blo 2149435 2151255 := bstep (se 1 (by rfl) ⟨1613441, by rfl⟩ : syracuseStep 2151255 = 3226883) B3226883
theorem B2297269 : Blo 2149435 2297269 := bbase (se 5 (by rfl) ⟨107684, by rfl⟩ : syracuseStep 2297269 = 215369) (by norm_num)
theorem B3063025 : Blo 2149435 3063025 := bstep (se 2 (by rfl) ⟨1148634, by rfl⟩ : syracuseStep 3063025 = 2297269) B2297269
theorem B4084033 : Blo 2149435 4084033 := bstep (se 2 (by rfl) ⟨1531512, by rfl⟩ : syracuseStep 4084033 = 3063025) B3063025
theorem B5445377 : Blo 2149435 5445377 := bstep (se 2 (by rfl) ⟨2042016, by rfl⟩ : syracuseStep 5445377 = 4084033) B4084033
theorem B3630251 : Blo 2149435 3630251 := bstep (se 1 (by rfl) ⟨2722688, by rfl⟩ : syracuseStep 3630251 = 5445377) B5445377
theorem B2420167 : Blo 2149435 2420167 := bstep (se 1 (by rfl) ⟨1815125, by rfl⟩ : syracuseStep 2420167 = 3630251) B3630251
theorem B3226889 : Blo 2149435 3226889 := bstep (se 2 (by rfl) ⟨1210083, by rfl⟩ : syracuseStep 3226889 = 2420167) B2420167
theorem B2151259 : Blo 2149435 2151259 := bstep (se 1 (by rfl) ⟨1613444, by rfl⟩ : syracuseStep 2151259 = 3226889) B3226889
theorem B10890773 : Blo 2149435 10890773 := bbase (se 6 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 10890773 = 510505) (by norm_num)
theorem B7260515 : Blo 2149435 7260515 := bstep (se 1 (by rfl) ⟨5445386, by rfl⟩ : syracuseStep 7260515 = 10890773) B10890773
theorem B4840343 : Blo 2149435 4840343 := bstep (se 1 (by rfl) ⟨3630257, by rfl⟩ : syracuseStep 4840343 = 7260515) B7260515
theorem B3226895 : Blo 2149435 3226895 := bstep (se 1 (by rfl) ⟨2420171, by rfl⟩ : syracuseStep 3226895 = 4840343) B4840343
theorem B2151263 : Blo 2149435 2151263 := bstep (se 1 (by rfl) ⟨1613447, by rfl⟩ : syracuseStep 2151263 = 3226895) B3226895
theorem B3226901 : Blo 2149435 3226901 := bbase (se 6 (by rfl) ⟨75630, by rfl⟩ : syracuseStep 3226901 = 151261) (by norm_num)
theorem B2151267 : Blo 2149435 2151267 := bstep (se 1 (by rfl) ⟨1613450, by rfl⟩ : syracuseStep 2151267 = 3226901) B3226901
theorem B7359605 : Blo 2149435 7359605 := bbase (se 5 (by rfl) ⟨344981, by rfl⟩ : syracuseStep 7359605 = 689963) (by norm_num)
theorem B4906403 : Blo 2149435 4906403 := bstep (se 1 (by rfl) ⟨3679802, by rfl⟩ : syracuseStep 4906403 = 7359605) B7359605
theorem B3270935 : Blo 2149435 3270935 := bstep (se 1 (by rfl) ⟨2453201, by rfl⟩ : syracuseStep 3270935 = 4906403) B4906403
theorem B2180623 : Blo 2149435 2180623 := bstep (se 1 (by rfl) ⟨1635467, by rfl⟩ : syracuseStep 2180623 = 3270935) B3270935
theorem B2907497 : Blo 2149435 2907497 := bstep (se 2 (by rfl) ⟨1090311, by rfl⟩ : syracuseStep 2907497 = 2180623) B2180623
theorem B7753325 : Blo 2149435 7753325 := bstep (se 3 (by rfl) ⟨1453748, by rfl⟩ : syracuseStep 7753325 = 2907497) B2907497
theorem B20675533 : Blo 2149435 20675533 := bstep (se 3 (by rfl) ⟨3876662, by rfl⟩ : syracuseStep 20675533 = 7753325) B7753325
theorem B27567377 : Blo 2149435 27567377 := bstep (se 2 (by rfl) ⟨10337766, by rfl⟩ : syracuseStep 27567377 = 20675533) B20675533
theorem B18378251 : Blo 2149435 18378251 := bstep (se 1 (by rfl) ⟨13783688, by rfl⟩ : syracuseStep 18378251 = 27567377) B27567377
theorem B12252167 : Blo 2149435 12252167 := bstep (se 1 (by rfl) ⟨9189125, by rfl⟩ : syracuseStep 12252167 = 18378251) B18378251
theorem B8168111 : Blo 2149435 8168111 := bstep (se 1 (by rfl) ⟨6126083, by rfl⟩ : syracuseStep 8168111 = 12252167) B12252167
theorem B5445407 : Blo 2149435 5445407 := bstep (se 1 (by rfl) ⟨4084055, by rfl⟩ : syracuseStep 5445407 = 8168111) B8168111
theorem B3630271 : Blo 2149435 3630271 := bstep (se 1 (by rfl) ⟨2722703, by rfl⟩ : syracuseStep 3630271 = 5445407) B5445407
theorem B4840361 : Blo 2149435 4840361 := bstep (se 2 (by rfl) ⟨1815135, by rfl⟩ : syracuseStep 4840361 = 3630271) B3630271
theorem B3226907 : Blo 2149435 3226907 := bstep (se 1 (by rfl) ⟨2420180, by rfl⟩ : syracuseStep 3226907 = 4840361) B4840361
theorem B2151271 : Blo 2149435 2151271 := bstep (se 1 (by rfl) ⟨1613453, by rfl⟩ : syracuseStep 2151271 = 3226907) B3226907
theorem B2420185 : Blo 2149435 2420185 := bbase (se 2 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 2420185 = 1815139) (by norm_num)
theorem B3226913 : Blo 2149435 3226913 := bstep (se 2 (by rfl) ⟨1210092, by rfl⟩ : syracuseStep 3226913 = 2420185) B2420185
theorem B2151275 : Blo 2149435 2151275 := bstep (se 1 (by rfl) ⟨1613456, by rfl⟩ : syracuseStep 2151275 = 3226913) B3226913
theorem B3063053 : Blo 2149435 3063053 := bbase (se 3 (by rfl) ⟨574322, by rfl⟩ : syracuseStep 3063053 = 1148645) (by norm_num)
theorem B8168141 : Blo 2149435 8168141 := bstep (se 3 (by rfl) ⟨1531526, by rfl⟩ : syracuseStep 8168141 = 3063053) B3063053
theorem B5445427 : Blo 2149435 5445427 := bstep (se 1 (by rfl) ⟨4084070, by rfl⟩ : syracuseStep 5445427 = 8168141) B8168141
theorem B7260569 : Blo 2149435 7260569 := bstep (se 2 (by rfl) ⟨2722713, by rfl⟩ : syracuseStep 7260569 = 5445427) B5445427
theorem B4840379 : Blo 2149435 4840379 := bstep (se 1 (by rfl) ⟨3630284, by rfl⟩ : syracuseStep 4840379 = 7260569) B7260569
theorem B3226919 : Blo 2149435 3226919 := bstep (se 1 (by rfl) ⟨2420189, by rfl⟩ : syracuseStep 3226919 = 4840379) B4840379
theorem B2151279 : Blo 2149435 2151279 := bstep (se 1 (by rfl) ⟨1613459, by rfl⟩ : syracuseStep 2151279 = 3226919) B3226919
theorem B3226925 : Blo 2149435 3226925 := bbase (se 3 (by rfl) ⟨605048, by rfl⟩ : syracuseStep 3226925 = 1210097) (by norm_num)
theorem B2151283 : Blo 2149435 2151283 := bstep (se 1 (by rfl) ⟨1613462, by rfl⟩ : syracuseStep 2151283 = 3226925) B3226925
theorem B4840397 : Blo 2149435 4840397 := bbase (se 3 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 4840397 = 1815149) (by norm_num)
theorem B3226931 : Blo 2149435 3226931 := bstep (se 1 (by rfl) ⟨2420198, by rfl⟩ : syracuseStep 3226931 = 4840397) B4840397
theorem B2151287 : Blo 2149435 2151287 := bstep (se 1 (by rfl) ⟨1613465, by rfl⟩ : syracuseStep 2151287 = 3226931) B3226931
theorem B2722729 : Blo 2149435 2722729 := bbase (se 2 (by rfl) ⟨1021023, by rfl⟩ : syracuseStep 2722729 = 2042047) (by norm_num)
theorem B3630305 : Blo 2149435 3630305 := bstep (se 2 (by rfl) ⟨1361364, by rfl⟩ : syracuseStep 3630305 = 2722729) B2722729
theorem B2420203 : Blo 2149435 2420203 := bstep (se 1 (by rfl) ⟨1815152, by rfl⟩ : syracuseStep 2420203 = 3630305) B3630305
theorem B3226937 : Blo 2149435 3226937 := bstep (se 2 (by rfl) ⟨1210101, by rfl⟩ : syracuseStep 3226937 = 2420203) B2420203
theorem B2151291 : Blo 2149435 2151291 := bstep (se 1 (by rfl) ⟨1613468, by rfl⟩ : syracuseStep 2151291 = 3226937) B3226937
theorem B5519765 : Blo 2149435 5519765 := bbase (se 6 (by rfl) ⟨129369, by rfl⟩ : syracuseStep 5519765 = 258739) (by norm_num)
theorem B3679843 : Blo 2149435 3679843 := bstep (se 1 (by rfl) ⟨2759882, by rfl⟩ : syracuseStep 3679843 = 5519765) B5519765
theorem B4906457 : Blo 2149435 4906457 := bstep (se 2 (by rfl) ⟨1839921, by rfl⟩ : syracuseStep 4906457 = 3679843) B3679843
theorem B3270971 : Blo 2149435 3270971 := bstep (se 1 (by rfl) ⟨2453228, by rfl⟩ : syracuseStep 3270971 = 4906457) B4906457
theorem B2180647 : Blo 2149435 2180647 := bstep (se 1 (by rfl) ⟨1635485, by rfl⟩ : syracuseStep 2180647 = 3270971) B3270971
theorem B11630117 : Blo 2149435 11630117 := bstep (se 4 (by rfl) ⟨1090323, by rfl⟩ : syracuseStep 11630117 = 2180647) B2180647
theorem B7753411 : Blo 2149435 7753411 := bstep (se 1 (by rfl) ⟨5815058, by rfl⟩ : syracuseStep 7753411 = 11630117) B11630117
theorem B10337881 : Blo 2149435 10337881 := bstep (se 2 (by rfl) ⟨3876705, by rfl⟩ : syracuseStep 10337881 = 7753411) B7753411
theorem B13783841 : Blo 2149435 13783841 := bstep (se 2 (by rfl) ⟨5168940, by rfl⟩ : syracuseStep 13783841 = 10337881) B10337881
theorem B9189227 : Blo 2149435 9189227 := bstep (se 1 (by rfl) ⟨6891920, by rfl⟩ : syracuseStep 9189227 = 13783841) B13783841
theorem B24504605 : Blo 2149435 24504605 := bstep (se 3 (by rfl) ⟨4594613, by rfl⟩ : syracuseStep 24504605 = 9189227) B9189227
theorem B16336403 : Blo 2149435 16336403 := bstep (se 1 (by rfl) ⟨12252302, by rfl⟩ : syracuseStep 16336403 = 24504605) B24504605
theorem B10890935 : Blo 2149435 10890935 := bstep (se 1 (by rfl) ⟨8168201, by rfl⟩ : syracuseStep 10890935 = 16336403) B16336403
theorem B7260623 : Blo 2149435 7260623 := bstep (se 1 (by rfl) ⟨5445467, by rfl⟩ : syracuseStep 7260623 = 10890935) B10890935
theorem B4840415 : Blo 2149435 4840415 := bstep (se 1 (by rfl) ⟨3630311, by rfl⟩ : syracuseStep 4840415 = 7260623) B7260623
theorem B3226943 : Blo 2149435 3226943 := bstep (se 1 (by rfl) ⟨2420207, by rfl⟩ : syracuseStep 3226943 = 4840415) B4840415
theorem B2151295 : Blo 2149435 2151295 := bstep (se 1 (by rfl) ⟨1613471, by rfl⟩ : syracuseStep 2151295 = 3226943) B3226943
theorem B3226949 : Blo 2149435 3226949 := bbase (se 4 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 3226949 = 605053) (by norm_num)
theorem B2151299 : Blo 2149435 2151299 := bstep (se 1 (by rfl) ⟨1613474, by rfl⟩ : syracuseStep 2151299 = 3226949) B3226949
theorem B3630325 : Blo 2149435 3630325 := bbase (se 5 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 3630325 = 340343) (by norm_num)
theorem B4840433 : Blo 2149435 4840433 := bstep (se 2 (by rfl) ⟨1815162, by rfl⟩ : syracuseStep 4840433 = 3630325) B3630325
theorem B3226955 : Blo 2149435 3226955 := bstep (se 1 (by rfl) ⟨2420216, by rfl⟩ : syracuseStep 3226955 = 4840433) B4840433
theorem B2151303 : Blo 2149435 2151303 := bstep (se 1 (by rfl) ⟨1613477, by rfl⟩ : syracuseStep 2151303 = 3226955) B3226955
theorem B2420221 : Blo 2149435 2420221 := bbase (se 3 (by rfl) ⟨453791, by rfl⟩ : syracuseStep 2420221 = 907583) (by norm_num)
theorem B3226961 : Blo 2149435 3226961 := bstep (se 2 (by rfl) ⟨1210110, by rfl⟩ : syracuseStep 3226961 = 2420221) B2420221
theorem B2151307 : Blo 2149435 2151307 := bstep (se 1 (by rfl) ⟨1613480, by rfl⟩ : syracuseStep 2151307 = 3226961) B3226961
theorem B7260677 : Blo 2149435 7260677 := bbase (se 4 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 7260677 = 1361377) (by norm_num)
theorem B4840451 : Blo 2149435 4840451 := bstep (se 1 (by rfl) ⟨3630338, by rfl⟩ : syracuseStep 4840451 = 7260677) B7260677
theorem B3226967 : Blo 2149435 3226967 := bstep (se 1 (by rfl) ⟨2420225, by rfl⟩ : syracuseStep 3226967 = 4840451) B4840451
theorem B2151311 : Blo 2149435 2151311 := bstep (se 1 (by rfl) ⟨1613483, by rfl⟩ : syracuseStep 2151311 = 3226967) B3226967
theorem B3226973 : Blo 2149435 3226973 := bbase (se 3 (by rfl) ⟨605057, by rfl⟩ : syracuseStep 3226973 = 1210115) (by norm_num)
theorem B2151315 : Blo 2149435 2151315 := bstep (se 1 (by rfl) ⟨1613486, by rfl⟩ : syracuseStep 2151315 = 3226973) B3226973
theorem B4840469 : Blo 2149435 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B3226979 : Blo 2149435 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B2151319 : Blo 2149435 2151319 := bstep (se 1 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 2151319 = 3226979) B3226979
theorem B8168309 : Blo 2149435 8168309 := bbase (se 5 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 8168309 = 765779) (by norm_num)
theorem B5445539 : Blo 2149435 5445539 := bstep (se 1 (by rfl) ⟨4084154, by rfl⟩ : syracuseStep 5445539 = 8168309) B8168309
theorem B3630359 : Blo 2149435 3630359 := bstep (se 1 (by rfl) ⟨2722769, by rfl⟩ : syracuseStep 3630359 = 5445539) B5445539
theorem B2420239 : Blo 2149435 2420239 := bstep (se 1 (by rfl) ⟨1815179, by rfl⟩ : syracuseStep 2420239 = 3630359) B3630359
theorem B3226985 : Blo 2149435 3226985 := bstep (se 2 (by rfl) ⟨1210119, by rfl⟩ : syracuseStep 3226985 = 2420239) B2420239
theorem B2151323 : Blo 2149435 2151323 := bstep (se 1 (by rfl) ⟨1613492, by rfl⟩ : syracuseStep 2151323 = 3226985) B3226985
theorem B2297341 : Blo 2149435 2297341 := bbase (se 3 (by rfl) ⟨430751, by rfl⟩ : syracuseStep 2297341 = 861503) (by norm_num)
theorem B12252485 : Blo 2149435 12252485 := bstep (se 4 (by rfl) ⟨1148670, by rfl⟩ : syracuseStep 12252485 = 2297341) B2297341
theorem B8168323 : Blo 2149435 8168323 := bstep (se 1 (by rfl) ⟨6126242, by rfl⟩ : syracuseStep 8168323 = 12252485) B12252485
theorem B10891097 : Blo 2149435 10891097 := bstep (se 2 (by rfl) ⟨4084161, by rfl⟩ : syracuseStep 10891097 = 8168323) B8168323
theorem B7260731 : Blo 2149435 7260731 := bstep (se 1 (by rfl) ⟨5445548, by rfl⟩ : syracuseStep 7260731 = 10891097) B10891097
theorem B4840487 : Blo 2149435 4840487 := bstep (se 1 (by rfl) ⟨3630365, by rfl⟩ : syracuseStep 4840487 = 7260731) B7260731
theorem B3226991 : Blo 2149435 3226991 := bstep (se 1 (by rfl) ⟨2420243, by rfl⟩ : syracuseStep 3226991 = 4840487) B4840487
theorem B2151327 : Blo 2149435 2151327 := bstep (se 1 (by rfl) ⟨1613495, by rfl⟩ : syracuseStep 2151327 = 3226991) B3226991
theorem B3226997 : Blo 2149435 3226997 := bbase (se 5 (by rfl) ⟨151265, by rfl⟩ : syracuseStep 3226997 = 302531) (by norm_num)
theorem B2151331 : Blo 2149435 2151331 := bstep (se 1 (by rfl) ⟨1613498, by rfl⟩ : syracuseStep 2151331 = 3226997) B3226997
theorem B3063133 : Blo 2149435 3063133 := bbase (se 3 (by rfl) ⟨574337, by rfl⟩ : syracuseStep 3063133 = 1148675) (by norm_num)
theorem B4084177 : Blo 2149435 4084177 := bstep (se 2 (by rfl) ⟨1531566, by rfl⟩ : syracuseStep 4084177 = 3063133) B3063133
theorem B5445569 : Blo 2149435 5445569 := bstep (se 2 (by rfl) ⟨2042088, by rfl⟩ : syracuseStep 5445569 = 4084177) B4084177
theorem B3630379 : Blo 2149435 3630379 := bstep (se 1 (by rfl) ⟨2722784, by rfl⟩ : syracuseStep 3630379 = 5445569) B5445569
theorem B4840505 : Blo 2149435 4840505 := bstep (se 2 (by rfl) ⟨1815189, by rfl⟩ : syracuseStep 4840505 = 3630379) B3630379
theorem B3227003 : Blo 2149435 3227003 := bstep (se 1 (by rfl) ⟨2420252, by rfl⟩ : syracuseStep 3227003 = 4840505) B4840505
theorem B2151335 : Blo 2149435 2151335 := bstep (se 1 (by rfl) ⟨1613501, by rfl⟩ : syracuseStep 2151335 = 3227003) B3227003
theorem B2420257 : Blo 2149435 2420257 := bbase (se 2 (by rfl) ⟨907596, by rfl⟩ : syracuseStep 2420257 = 1815193) (by norm_num)
theorem B3227009 : Blo 2149435 3227009 := bstep (se 2 (by rfl) ⟨1210128, by rfl⟩ : syracuseStep 3227009 = 2420257) B2420257
theorem B2151339 : Blo 2149435 2151339 := bstep (se 1 (by rfl) ⟨1613504, by rfl⟩ : syracuseStep 2151339 = 3227009) B3227009
theorem B5445589 : Blo 2149435 5445589 := bbase (se 7 (by rfl) ⟨63815, by rfl⟩ : syracuseStep 5445589 = 127631) (by norm_num)
theorem B7260785 : Blo 2149435 7260785 := bstep (se 2 (by rfl) ⟨2722794, by rfl⟩ : syracuseStep 7260785 = 5445589) B5445589
theorem B4840523 : Blo 2149435 4840523 := bstep (se 1 (by rfl) ⟨3630392, by rfl⟩ : syracuseStep 4840523 = 7260785) B7260785
theorem B3227015 : Blo 2149435 3227015 := bstep (se 1 (by rfl) ⟨2420261, by rfl⟩ : syracuseStep 3227015 = 4840523) B4840523
theorem B2151343 : Blo 2149435 2151343 := bstep (se 1 (by rfl) ⟨1613507, by rfl⟩ : syracuseStep 2151343 = 3227015) B3227015
theorem B3227021 : Blo 2149435 3227021 := bbase (se 3 (by rfl) ⟨605066, by rfl⟩ : syracuseStep 3227021 = 1210133) (by norm_num)
theorem B2151347 : Blo 2149435 2151347 := bstep (se 1 (by rfl) ⟨1613510, by rfl⟩ : syracuseStep 2151347 = 3227021) B3227021
theorem B4840541 : Blo 2149435 4840541 := bbase (se 3 (by rfl) ⟨907601, by rfl⟩ : syracuseStep 4840541 = 1815203) (by norm_num)
theorem B3227027 : Blo 2149435 3227027 := bstep (se 1 (by rfl) ⟨2420270, by rfl⟩ : syracuseStep 3227027 = 4840541) B4840541
theorem B2151351 : Blo 2149435 2151351 := bstep (se 1 (by rfl) ⟨1613513, by rfl⟩ : syracuseStep 2151351 = 3227027) B3227027
theorem B3630413 : Blo 2149435 3630413 := bbase (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) (by norm_num)
theorem B2420275 : Blo 2149435 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B3227033 : Blo 2149435 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B2151355 : Blo 2149435 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B7859429 : Blo 2149435 7859429 := bbase (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) (by norm_num)
theorem B5239619 : Blo 2149435 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B3493079 : Blo 2149435 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B37259509 : Blo 2149435 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B49679345 : Blo 2149435 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B33119563 : Blo 2149435 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B44159417 : Blo 2149435 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B29439611 : Blo 2149435 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B19626407 : Blo 2149435 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B13084271 : Blo 2149435 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B8722847 : Blo 2149435 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B23260925 : Blo 2149435 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B15507283 : Blo 2149435 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B20676377 : Blo 2149435 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B13784251 : Blo 2149435 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B18379001 : Blo 2149435 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B12252667 : Blo 2149435 12252667 := bstep (se 1 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 12252667 = 18379001) B18379001
theorem B16336889 : Blo 2149435 16336889 := bstep (se 2 (by rfl) ⟨6126333, by rfl⟩ : syracuseStep 16336889 = 12252667) B12252667
theorem B10891259 : Blo 2149435 10891259 := bstep (se 1 (by rfl) ⟨8168444, by rfl⟩ : syracuseStep 10891259 = 16336889) B16336889
theorem B7260839 : Blo 2149435 7260839 := bstep (se 1 (by rfl) ⟨5445629, by rfl⟩ : syracuseStep 7260839 = 10891259) B10891259
theorem B4840559 : Blo 2149435 4840559 := bstep (se 1 (by rfl) ⟨3630419, by rfl⟩ : syracuseStep 4840559 = 7260839) B7260839
theorem B3227039 : Blo 2149435 3227039 := bstep (se 1 (by rfl) ⟨2420279, by rfl⟩ : syracuseStep 3227039 = 4840559) B4840559
theorem B2151359 : Blo 2149435 2151359 := bstep (se 1 (by rfl) ⟨1613519, by rfl⟩ : syracuseStep 2151359 = 3227039) B3227039
theorem B3227045 : Blo 2149435 3227045 := bbase (se 4 (by rfl) ⟨302535, by rfl⟩ : syracuseStep 3227045 = 605071) (by norm_num)
theorem B2151363 : Blo 2149435 2151363 := bstep (se 1 (by rfl) ⟨1613522, by rfl⟩ : syracuseStep 2151363 = 3227045) B3227045
theorem B2722825 : Blo 2149435 2722825 := bbase (se 2 (by rfl) ⟨1021059, by rfl⟩ : syracuseStep 2722825 = 2042119) (by norm_num)
theorem B3630433 : Blo 2149435 3630433 := bstep (se 2 (by rfl) ⟨1361412, by rfl⟩ : syracuseStep 3630433 = 2722825) B2722825
theorem B4840577 : Blo 2149435 4840577 := bstep (se 2 (by rfl) ⟨1815216, by rfl⟩ : syracuseStep 4840577 = 3630433) B3630433
theorem B3227051 : Blo 2149435 3227051 := bstep (se 1 (by rfl) ⟨2420288, by rfl⟩ : syracuseStep 3227051 = 4840577) B4840577
theorem B2151367 : Blo 2149435 2151367 := bstep (se 1 (by rfl) ⟨1613525, by rfl⟩ : syracuseStep 2151367 = 3227051) B3227051
theorem B2420293 : Blo 2149435 2420293 := bbase (se 4 (by rfl) ⟨226902, by rfl⟩ : syracuseStep 2420293 = 453805) (by norm_num)
theorem B3227057 : Blo 2149435 3227057 := bstep (se 2 (by rfl) ⟨1210146, by rfl⟩ : syracuseStep 3227057 = 2420293) B2420293
theorem B2151371 : Blo 2149435 2151371 := bstep (se 1 (by rfl) ⟨1613528, by rfl⟩ : syracuseStep 2151371 = 3227057) B3227057
theorem B4084253 : Blo 2149435 4084253 := bbase (se 3 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 4084253 = 1531595) (by norm_num)
theorem B2722835 : Blo 2149435 2722835 := bstep (se 1 (by rfl) ⟨2042126, by rfl⟩ : syracuseStep 2722835 = 4084253) B4084253
theorem B7260893 : Blo 2149435 7260893 := bstep (se 3 (by rfl) ⟨1361417, by rfl⟩ : syracuseStep 7260893 = 2722835) B2722835
theorem B4840595 : Blo 2149435 4840595 := bstep (se 1 (by rfl) ⟨3630446, by rfl⟩ : syracuseStep 4840595 = 7260893) B7260893
theorem B3227063 : Blo 2149435 3227063 := bstep (se 1 (by rfl) ⟨2420297, by rfl⟩ : syracuseStep 3227063 = 4840595) B4840595
theorem B2151375 : Blo 2149435 2151375 := bstep (se 1 (by rfl) ⟨1613531, by rfl⟩ : syracuseStep 2151375 = 3227063) B3227063
theorem B3227069 : Blo 2149435 3227069 := bbase (se 3 (by rfl) ⟨605075, by rfl⟩ : syracuseStep 3227069 = 1210151) (by norm_num)
theorem B2151379 : Blo 2149435 2151379 := bstep (se 1 (by rfl) ⟨1613534, by rfl⟩ : syracuseStep 2151379 = 3227069) B3227069
theorem B4840613 : Blo 2149435 4840613 := bbase (se 4 (by rfl) ⟨453807, by rfl⟩ : syracuseStep 4840613 = 907615) (by norm_num)
theorem B3227075 : Blo 2149435 3227075 := bstep (se 1 (by rfl) ⟨2420306, by rfl⟩ : syracuseStep 3227075 = 4840613) B4840613
theorem B2151383 : Blo 2149435 2151383 := bstep (se 1 (by rfl) ⟨1613537, by rfl⟩ : syracuseStep 2151383 = 3227075) B3227075
theorem B5445701 : Blo 2149435 5445701 := bbase (se 4 (by rfl) ⟨510534, by rfl⟩ : syracuseStep 5445701 = 1021069) (by norm_num)
theorem B3630467 : Blo 2149435 3630467 := bstep (se 1 (by rfl) ⟨2722850, by rfl⟩ : syracuseStep 3630467 = 5445701) B5445701
theorem B2420311 : Blo 2149435 2420311 := bstep (se 1 (by rfl) ⟨1815233, by rfl⟩ : syracuseStep 2420311 = 3630467) B3630467
theorem B3227081 : Blo 2149435 3227081 := bstep (se 2 (by rfl) ⟨1210155, by rfl⟩ : syracuseStep 3227081 = 2420311) B2420311
theorem B2151387 : Blo 2149435 2151387 := bstep (se 1 (by rfl) ⟨1613540, by rfl⟩ : syracuseStep 2151387 = 3227081) B3227081
theorem B6892229 : Blo 2149435 6892229 := bbase (se 4 (by rfl) ⟨646146, by rfl⟩ : syracuseStep 6892229 = 1292293) (by norm_num)
theorem B4594819 : Blo 2149435 4594819 := bstep (se 1 (by rfl) ⟨3446114, by rfl⟩ : syracuseStep 4594819 = 6892229) B6892229
theorem B6126425 : Blo 2149435 6126425 := bstep (se 2 (by rfl) ⟨2297409, by rfl⟩ : syracuseStep 6126425 = 4594819) B4594819
theorem B4084283 : Blo 2149435 4084283 := bstep (se 1 (by rfl) ⟨3063212, by rfl⟩ : syracuseStep 4084283 = 6126425) B6126425
theorem B10891421 : Blo 2149435 10891421 := bstep (se 3 (by rfl) ⟨2042141, by rfl⟩ : syracuseStep 10891421 = 4084283) B4084283
theorem B7260947 : Blo 2149435 7260947 := bstep (se 1 (by rfl) ⟨5445710, by rfl⟩ : syracuseStep 7260947 = 10891421) B10891421
theorem B4840631 : Blo 2149435 4840631 := bstep (se 1 (by rfl) ⟨3630473, by rfl⟩ : syracuseStep 4840631 = 7260947) B7260947
theorem B3227087 : Blo 2149435 3227087 := bstep (se 1 (by rfl) ⟨2420315, by rfl⟩ : syracuseStep 3227087 = 4840631) B4840631
theorem B2151391 : Blo 2149435 2151391 := bstep (se 1 (by rfl) ⟨1613543, by rfl⟩ : syracuseStep 2151391 = 3227087) B3227087
theorem B3227093 : Blo 2149435 3227093 := bbase (se 7 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 3227093 = 75635) (by norm_num)
theorem B2151395 : Blo 2149435 2151395 := bstep (se 1 (by rfl) ⟨1613546, by rfl⟩ : syracuseStep 2151395 = 3227093) B3227093
theorem B8168597 : Blo 2149435 8168597 := bbase (se 6 (by rfl) ⟨191451, by rfl⟩ : syracuseStep 8168597 = 382903) (by norm_num)
theorem B5445731 : Blo 2149435 5445731 := bstep (se 1 (by rfl) ⟨4084298, by rfl⟩ : syracuseStep 5445731 = 8168597) B8168597
theorem B3630487 : Blo 2149435 3630487 := bstep (se 1 (by rfl) ⟨2722865, by rfl⟩ : syracuseStep 3630487 = 5445731) B5445731
theorem B4840649 : Blo 2149435 4840649 := bstep (se 2 (by rfl) ⟨1815243, by rfl⟩ : syracuseStep 4840649 = 3630487) B3630487
theorem B3227099 : Blo 2149435 3227099 := bstep (se 1 (by rfl) ⟨2420324, by rfl⟩ : syracuseStep 3227099 = 4840649) B4840649
theorem B2151399 : Blo 2149435 2151399 := bstep (se 1 (by rfl) ⟨1613549, by rfl⟩ : syracuseStep 2151399 = 3227099) B3227099
theorem B2420329 : Blo 2149435 2420329 := bbase (se 2 (by rfl) ⟨907623, by rfl⟩ : syracuseStep 2420329 = 1815247) (by norm_num)
theorem B3227105 : Blo 2149435 3227105 := bstep (se 2 (by rfl) ⟨1210164, by rfl⟩ : syracuseStep 3227105 = 2420329) B2420329
theorem B2151403 : Blo 2149435 2151403 := bstep (se 1 (by rfl) ⟨1613552, by rfl⟩ : syracuseStep 2151403 = 3227105) B3227105
theorem B4594853 : Blo 2149435 4594853 := bbase (se 4 (by rfl) ⟨430767, by rfl⟩ : syracuseStep 4594853 = 861535) (by norm_num)
theorem B12252941 : Blo 2149435 12252941 := bstep (se 3 (by rfl) ⟨2297426, by rfl⟩ : syracuseStep 12252941 = 4594853) B4594853
theorem B8168627 : Blo 2149435 8168627 := bstep (se 1 (by rfl) ⟨6126470, by rfl⟩ : syracuseStep 8168627 = 12252941) B12252941
theorem B5445751 : Blo 2149435 5445751 := bstep (se 1 (by rfl) ⟨4084313, by rfl⟩ : syracuseStep 5445751 = 8168627) B8168627
theorem B7261001 : Blo 2149435 7261001 := bstep (se 2 (by rfl) ⟨2722875, by rfl⟩ : syracuseStep 7261001 = 5445751) B5445751
theorem B4840667 : Blo 2149435 4840667 := bstep (se 1 (by rfl) ⟨3630500, by rfl⟩ : syracuseStep 4840667 = 7261001) B7261001
theorem B3227111 : Blo 2149435 3227111 := bstep (se 1 (by rfl) ⟨2420333, by rfl⟩ : syracuseStep 3227111 = 4840667) B4840667
theorem B2151407 : Blo 2149435 2151407 := bstep (se 1 (by rfl) ⟨1613555, by rfl⟩ : syracuseStep 2151407 = 3227111) B3227111
theorem B3227117 : Blo 2149435 3227117 := bbase (se 3 (by rfl) ⟨605084, by rfl⟩ : syracuseStep 3227117 = 1210169) (by norm_num)
theorem B2151411 : Blo 2149435 2151411 := bstep (se 1 (by rfl) ⟨1613558, by rfl⟩ : syracuseStep 2151411 = 3227117) B3227117
theorem B4840685 : Blo 2149435 4840685 := bbase (se 3 (by rfl) ⟨907628, by rfl⟩ : syracuseStep 4840685 = 1815257) (by norm_num)
theorem B3227123 : Blo 2149435 3227123 := bstep (se 1 (by rfl) ⟨2420342, by rfl⟩ : syracuseStep 3227123 = 4840685) B4840685
theorem B2151415 : Blo 2149435 2151415 := bstep (se 1 (by rfl) ⟨1613561, by rfl⟩ : syracuseStep 2151415 = 3227123) B3227123
theorem B3063253 : Blo 2149435 3063253 := bbase (se 7 (by rfl) ⟨35897, by rfl⟩ : syracuseStep 3063253 = 71795) (by norm_num)
theorem B4084337 : Blo 2149435 4084337 := bstep (se 2 (by rfl) ⟨1531626, by rfl⟩ : syracuseStep 4084337 = 3063253) B3063253
theorem B2722891 : Blo 2149435 2722891 := bstep (se 1 (by rfl) ⟨2042168, by rfl⟩ : syracuseStep 2722891 = 4084337) B4084337
theorem B3630521 : Blo 2149435 3630521 := bstep (se 2 (by rfl) ⟨1361445, by rfl⟩ : syracuseStep 3630521 = 2722891) B2722891
theorem B2420347 : Blo 2149435 2420347 := bstep (se 1 (by rfl) ⟨1815260, by rfl⟩ : syracuseStep 2420347 = 3630521) B3630521
theorem B3227129 : Blo 2149435 3227129 := bstep (se 2 (by rfl) ⟨1210173, by rfl⟩ : syracuseStep 3227129 = 2420347) B2420347
theorem B2151419 : Blo 2149435 2151419 := bstep (se 1 (by rfl) ⟨1613564, by rfl⟩ : syracuseStep 2151419 = 3227129) B3227129
theorem B11040181 : Blo 2149435 11040181 := bbase (se 5 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 11040181 = 1035017) (by norm_num)
theorem B235523861 : Blo 2149435 235523861 := bstep (se 6 (by rfl) ⟨5520090, by rfl⟩ : syracuseStep 235523861 = 11040181) B11040181
theorem B157015907 : Blo 2149435 157015907 := bstep (se 1 (by rfl) ⟨117761930, by rfl⟩ : syracuseStep 157015907 = 235523861) B235523861
theorem B104677271 : Blo 2149435 104677271 := bstep (se 1 (by rfl) ⟨78507953, by rfl⟩ : syracuseStep 104677271 = 157015907) B157015907
theorem B69784847 : Blo 2149435 69784847 := bstep (se 1 (by rfl) ⟨52338635, by rfl⟩ : syracuseStep 69784847 = 104677271) B104677271
theorem B46523231 : Blo 2149435 46523231 := bstep (se 1 (by rfl) ⟨34892423, by rfl⟩ : syracuseStep 46523231 = 69784847) B69784847
theorem B31015487 : Blo 2149435 31015487 := bstep (se 1 (by rfl) ⟨23261615, by rfl⟩ : syracuseStep 31015487 = 46523231) B46523231
theorem B82707965 : Blo 2149435 82707965 := bstep (se 3 (by rfl) ⟨15507743, by rfl⟩ : syracuseStep 82707965 = 31015487) B31015487
theorem B55138643 : Blo 2149435 55138643 := bstep (se 1 (by rfl) ⟨41353982, by rfl⟩ : syracuseStep 55138643 = 82707965) B82707965
theorem B36759095 : Blo 2149435 36759095 := bstep (se 1 (by rfl) ⟨27569321, by rfl⟩ : syracuseStep 36759095 = 55138643) B55138643
theorem B24506063 : Blo 2149435 24506063 := bstep (se 1 (by rfl) ⟨18379547, by rfl⟩ : syracuseStep 24506063 = 36759095) B36759095
theorem B16337375 : Blo 2149435 16337375 := bstep (se 1 (by rfl) ⟨12253031, by rfl⟩ : syracuseStep 16337375 = 24506063) B24506063
theorem B10891583 : Blo 2149435 10891583 := bstep (se 1 (by rfl) ⟨8168687, by rfl⟩ : syracuseStep 10891583 = 16337375) B16337375
theorem B7261055 : Blo 2149435 7261055 := bstep (se 1 (by rfl) ⟨5445791, by rfl⟩ : syracuseStep 7261055 = 10891583) B10891583
theorem B4840703 : Blo 2149435 4840703 := bstep (se 1 (by rfl) ⟨3630527, by rfl⟩ : syracuseStep 4840703 = 7261055) B7261055
theorem B3227135 : Blo 2149435 3227135 := bstep (se 1 (by rfl) ⟨2420351, by rfl⟩ : syracuseStep 3227135 = 4840703) B4840703
theorem B2151423 : Blo 2149435 2151423 := bstep (se 1 (by rfl) ⟨1613567, by rfl⟩ : syracuseStep 2151423 = 3227135) B3227135
theorem B3227141 : Blo 2149435 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B2151427 : Blo 2149435 2151427 := bstep (se 1 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 2151427 = 3227141) B3227141
theorem B3630541 : Blo 2149435 3630541 := bbase (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) (by norm_num)
theorem B4840721 : Blo 2149435 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B3227147 : Blo 2149435 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B2151431 : Blo 2149435 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B2420365 : Blo 2149435 2420365 := bbase (se 3 (by rfl) ⟨453818, by rfl⟩ : syracuseStep 2420365 = 907637) (by norm_num)
theorem B3227153 : Blo 2149435 3227153 := bstep (se 2 (by rfl) ⟨1210182, by rfl⟩ : syracuseStep 3227153 = 2420365) B2420365
theorem B2151435 : Blo 2149435 2151435 := bstep (se 1 (by rfl) ⟨1613576, by rfl⟩ : syracuseStep 2151435 = 3227153) B3227153
theorem C0 (j : ℕ) (h1 : 537358 ≤ j) (h2 : j ≤ 537858) : Blo 2149435 (4 * j + 3) := by
  interval_cases j
  · exact B2149435
  · exact B2149439
  · exact B2149443
  · exact B2149447
  · exact B2149451
  · exact B2149455
  · exact B2149459
  · exact B2149463
  · exact B2149467
  · exact B2149471
  · exact B2149475
  · exact B2149479
  · exact B2149483
  · exact B2149487
  · exact B2149491
  · exact B2149495
  · exact B2149499
  · exact B2149503
  · exact B2149507
  · exact B2149511
  · exact B2149515
  · exact B2149519
  · exact B2149523
  · exact B2149527
  · exact B2149531
  · exact B2149535
  · exact B2149539
  · exact B2149543
  · exact B2149547
  · exact B2149551
  · exact B2149555
  · exact B2149559
  · exact B2149563
  · exact B2149567
  · exact B2149571
  · exact B2149575
  · exact B2149579
  · exact B2149583
  · exact B2149587
  · exact B2149591
  · exact B2149595
  · exact B2149599
  · exact B2149603
  · exact B2149607
  · exact B2149611
  · exact B2149615
  · exact B2149619
  · exact B2149623
  · exact B2149627
  · exact B2149631
  · exact B2149635
  · exact B2149639
  · exact B2149643
  · exact B2149647
  · exact B2149651
  · exact B2149655
  · exact B2149659
  · exact B2149663
  · exact B2149667
  · exact B2149671
  · exact B2149675
  · exact B2149679
  · exact B2149683
  · exact B2149687
  · exact B2149691
  · exact B2149695
  · exact B2149699
  · exact B2149703
  · exact B2149707
  · exact B2149711
  · exact B2149715
  · exact B2149719
  · exact B2149723
  · exact B2149727
  · exact B2149731
  · exact B2149735
  · exact B2149739
  · exact B2149743
  · exact B2149747
  · exact B2149751
  · exact B2149755
  · exact B2149759
  · exact B2149763
  · exact B2149767
  · exact B2149771
  · exact B2149775
  · exact B2149779
  · exact B2149783
  · exact B2149787
  · exact B2149791
  · exact B2149795
  · exact B2149799
  · exact B2149803
  · exact B2149807
  · exact B2149811
  · exact B2149815
  · exact B2149819
  · exact B2149823
  · exact B2149827
  · exact B2149831
  · exact B2149835
  · exact B2149839
  · exact B2149843
  · exact B2149847
  · exact B2149851
  · exact B2149855
  · exact B2149859
  · exact B2149863
  · exact B2149867
  · exact B2149871
  · exact B2149875
  · exact B2149879
  · exact B2149883
  · exact B2149887
  · exact B2149891
  · exact B2149895
  · exact B2149899
  · exact B2149903
  · exact B2149907
  · exact B2149911
  · exact B2149915
  · exact B2149919
  · exact B2149923
  · exact B2149927
  · exact B2149931
  · exact B2149935
  · exact B2149939
  · exact B2149943
  · exact B2149947
  · exact B2149951
  · exact B2149955
  · exact B2149959
  · exact B2149963
  · exact B2149967
  · exact B2149971
  · exact B2149975
  · exact B2149979
  · exact B2149983
  · exact B2149987
  · exact B2149991
  · exact B2149995
  · exact B2149999
  · exact B2150003
  · exact B2150007
  · exact B2150011
  · exact B2150015
  · exact B2150019
  · exact B2150023
  · exact B2150027
  · exact B2150031
  · exact B2150035
  · exact B2150039
  · exact B2150043
  · exact B2150047
  · exact B2150051
  · exact B2150055
  · exact B2150059
  · exact B2150063
  · exact B2150067
  · exact B2150071
  · exact B2150075
  · exact B2150079
  · exact B2150083
  · exact B2150087
  · exact B2150091
  · exact B2150095
  · exact B2150099
  · exact B2150103
  · exact B2150107
  · exact B2150111
  · exact B2150115
  · exact B2150119
  · exact B2150123
  · exact B2150127
  · exact B2150131
  · exact B2150135
  · exact B2150139
  · exact B2150143
  · exact B2150147
  · exact B2150151
  · exact B2150155
  · exact B2150159
  · exact B2150163
  · exact B2150167
  · exact B2150171
  · exact B2150175
  · exact B2150179
  · exact B2150183
  · exact B2150187
  · exact B2150191
  · exact B2150195
  · exact B2150199
  · exact B2150203
  · exact B2150207
  · exact B2150211
  · exact B2150215
  · exact B2150219
  · exact B2150223
  · exact B2150227
  · exact B2150231
  · exact B2150235
  · exact B2150239
  · exact B2150243
  · exact B2150247
  · exact B2150251
  · exact B2150255
  · exact B2150259
  · exact B2150263
  · exact B2150267
  · exact B2150271
  · exact B2150275
  · exact B2150279
  · exact B2150283
  · exact B2150287
  · exact B2150291
  · exact B2150295
  · exact B2150299
  · exact B2150303
  · exact B2150307
  · exact B2150311
  · exact B2150315
  · exact B2150319
  · exact B2150323
  · exact B2150327
  · exact B2150331
  · exact B2150335
  · exact B2150339
  · exact B2150343
  · exact B2150347
  · exact B2150351
  · exact B2150355
  · exact B2150359
  · exact B2150363
  · exact B2150367
  · exact B2150371
  · exact B2150375
  · exact B2150379
  · exact B2150383
  · exact B2150387
  · exact B2150391
  · exact B2150395
  · exact B2150399
  · exact B2150403
  · exact B2150407
  · exact B2150411
  · exact B2150415
  · exact B2150419
  · exact B2150423
  · exact B2150427
  · exact B2150431
  · exact B2150435
  · exact B2150439
  · exact B2150443
  · exact B2150447
  · exact B2150451
  · exact B2150455
  · exact B2150459
  · exact B2150463
  · exact B2150467
  · exact B2150471
  · exact B2150475
  · exact B2150479
  · exact B2150483
  · exact B2150487
  · exact B2150491
  · exact B2150495
  · exact B2150499
  · exact B2150503
  · exact B2150507
  · exact B2150511
  · exact B2150515
  · exact B2150519
  · exact B2150523
  · exact B2150527
  · exact B2150531
  · exact B2150535
  · exact B2150539
  · exact B2150543
  · exact B2150547
  · exact B2150551
  · exact B2150555
  · exact B2150559
  · exact B2150563
  · exact B2150567
  · exact B2150571
  · exact B2150575
  · exact B2150579
  · exact B2150583
  · exact B2150587
  · exact B2150591
  · exact B2150595
  · exact B2150599
  · exact B2150603
  · exact B2150607
  · exact B2150611
  · exact B2150615
  · exact B2150619
  · exact B2150623
  · exact B2150627
  · exact B2150631
  · exact B2150635
  · exact B2150639
  · exact B2150643
  · exact B2150647
  · exact B2150651
  · exact B2150655
  · exact B2150659
  · exact B2150663
  · exact B2150667
  · exact B2150671
  · exact B2150675
  · exact B2150679
  · exact B2150683
  · exact B2150687
  · exact B2150691
  · exact B2150695
  · exact B2150699
  · exact B2150703
  · exact B2150707
  · exact B2150711
  · exact B2150715
  · exact B2150719
  · exact B2150723
  · exact B2150727
  · exact B2150731
  · exact B2150735
  · exact B2150739
  · exact B2150743
  · exact B2150747
  · exact B2150751
  · exact B2150755
  · exact B2150759
  · exact B2150763
  · exact B2150767
  · exact B2150771
  · exact B2150775
  · exact B2150779
  · exact B2150783
  · exact B2150787
  · exact B2150791
  · exact B2150795
  · exact B2150799
  · exact B2150803
  · exact B2150807
  · exact B2150811
  · exact B2150815
  · exact B2150819
  · exact B2150823
  · exact B2150827
  · exact B2150831
  · exact B2150835
  · exact B2150839
  · exact B2150843
  · exact B2150847
  · exact B2150851
  · exact B2150855
  · exact B2150859
  · exact B2150863
  · exact B2150867
  · exact B2150871
  · exact B2150875
  · exact B2150879
  · exact B2150883
  · exact B2150887
  · exact B2150891
  · exact B2150895
  · exact B2150899
  · exact B2150903
  · exact B2150907
  · exact B2150911
  · exact B2150915
  · exact B2150919
  · exact B2150923
  · exact B2150927
  · exact B2150931
  · exact B2150935
  · exact B2150939
  · exact B2150943
  · exact B2150947
  · exact B2150951
  · exact B2150955
  · exact B2150959
  · exact B2150963
  · exact B2150967
  · exact B2150971
  · exact B2150975
  · exact B2150979
  · exact B2150983
  · exact B2150987
  · exact B2150991
  · exact B2150995
  · exact B2150999
  · exact B2151003
  · exact B2151007
  · exact B2151011
  · exact B2151015
  · exact B2151019
  · exact B2151023
  · exact B2151027
  · exact B2151031
  · exact B2151035
  · exact B2151039
  · exact B2151043
  · exact B2151047
  · exact B2151051
  · exact B2151055
  · exact B2151059
  · exact B2151063
  · exact B2151067
  · exact B2151071
  · exact B2151075
  · exact B2151079
  · exact B2151083
  · exact B2151087
  · exact B2151091
  · exact B2151095
  · exact B2151099
  · exact B2151103
  · exact B2151107
  · exact B2151111
  · exact B2151115
  · exact B2151119
  · exact B2151123
  · exact B2151127
  · exact B2151131
  · exact B2151135
  · exact B2151139
  · exact B2151143
  · exact B2151147
  · exact B2151151
  · exact B2151155
  · exact B2151159
  · exact B2151163
  · exact B2151167
  · exact B2151171
  · exact B2151175
  · exact B2151179
  · exact B2151183
  · exact B2151187
  · exact B2151191
  · exact B2151195
  · exact B2151199
  · exact B2151203
  · exact B2151207
  · exact B2151211
  · exact B2151215
  · exact B2151219
  · exact B2151223
  · exact B2151227
  · exact B2151231
  · exact B2151235
  · exact B2151239
  · exact B2151243
  · exact B2151247
  · exact B2151251
  · exact B2151255
  · exact B2151259
  · exact B2151263
  · exact B2151267
  · exact B2151271
  · exact B2151275
  · exact B2151279
  · exact B2151283
  · exact B2151287
  · exact B2151291
  · exact B2151295
  · exact B2151299
  · exact B2151303
  · exact B2151307
  · exact B2151311
  · exact B2151315
  · exact B2151319
  · exact B2151323
  · exact B2151327
  · exact B2151331
  · exact B2151335
  · exact B2151339
  · exact B2151343
  · exact B2151347
  · exact B2151351
  · exact B2151355
  · exact B2151359
  · exact B2151363
  · exact B2151367
  · exact B2151371
  · exact B2151375
  · exact B2151379
  · exact B2151383
  · exact B2151387
  · exact B2151391
  · exact B2151395
  · exact B2151399
  · exact B2151403
  · exact B2151407
  · exact B2151411
  · exact B2151415
  · exact B2151419
  · exact B2151423
  · exact B2151427
  · exact B2151431
  · exact B2151435
theorem solution (m : ℕ) (hlo : 2149435 ≤ m) (hhi : m ≤ 2151435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 537358 ≤ j := by omega
    have hj2 : j ≤ 537858 := by omega
    have hb : Blo 2149435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
