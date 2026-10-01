-- Prove2me | solution 1 for syracuse_descends_range_1901435_1903435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:51.722835+00:00
-- url     : https://prove2.me/submissions/1d41f8bd-44f5-43f3-9513-9e333a64309e

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

theorem B2406505 : Blo 1901435 2406505 := bbase (se 2 (by rfl) ⟨902439, by rfl⟩ : syracuseStep 2406505 = 1804879) (by norm_num)
theorem B3208673 : Blo 1901435 3208673 := bstep (se 2 (by rfl) ⟨1203252, by rfl⟩ : syracuseStep 3208673 = 2406505) B2406505
theorem B2139115 : Blo 1901435 2139115 := bstep (se 1 (by rfl) ⟨1604336, by rfl⟩ : syracuseStep 2139115 = 3208673) B3208673
theorem B2852153 : Blo 1901435 2852153 := bstep (se 2 (by rfl) ⟨1069557, by rfl⟩ : syracuseStep 2852153 = 2139115) B2139115
theorem B1901435 : Blo 1901435 1901435 := bstep (se 1 (by rfl) ⟨1426076, by rfl⟩ : syracuseStep 1901435 = 2852153) B2852153
theorem B3854765 : Blo 1901435 3854765 := bbase (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) (by norm_num)
theorem B2569843 : Blo 1901435 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B3426457 : Blo 1901435 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B4568609 : Blo 1901435 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B12182957 : Blo 1901435 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B8121971 : Blo 1901435 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B21658589 : Blo 1901435 21658589 := bstep (se 3 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 21658589 = 8121971) B8121971
theorem B14439059 : Blo 1901435 14439059 := bstep (se 1 (by rfl) ⟨10829294, by rfl⟩ : syracuseStep 14439059 = 21658589) B21658589
theorem B9626039 : Blo 1901435 9626039 := bstep (se 1 (by rfl) ⟨7219529, by rfl⟩ : syracuseStep 9626039 = 14439059) B14439059
theorem B6417359 : Blo 1901435 6417359 := bstep (se 1 (by rfl) ⟨4813019, by rfl⟩ : syracuseStep 6417359 = 9626039) B9626039
theorem B4278239 : Blo 1901435 4278239 := bstep (se 1 (by rfl) ⟨3208679, by rfl⟩ : syracuseStep 4278239 = 6417359) B6417359
theorem B2852159 : Blo 1901435 2852159 := bstep (se 1 (by rfl) ⟨2139119, by rfl⟩ : syracuseStep 2852159 = 4278239) B4278239
theorem B1901439 : Blo 1901435 1901439 := bstep (se 1 (by rfl) ⟨1426079, by rfl⟩ : syracuseStep 1901439 = 2852159) B2852159
theorem B2852165 : Blo 1901435 2852165 := bbase (se 4 (by rfl) ⟨267390, by rfl⟩ : syracuseStep 2852165 = 534781) (by norm_num)
theorem B1901443 : Blo 1901435 1901443 := bstep (se 1 (by rfl) ⟨1426082, by rfl⟩ : syracuseStep 1901443 = 2852165) B2852165
theorem B3208693 : Blo 1901435 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B4278257 : Blo 1901435 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B2852171 : Blo 1901435 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B1901447 : Blo 1901435 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B2139133 : Blo 1901435 2139133 := bbase (se 3 (by rfl) ⟨401087, by rfl⟩ : syracuseStep 2139133 = 802175) (by norm_num)
theorem B2852177 : Blo 1901435 2852177 := bstep (se 2 (by rfl) ⟨1069566, by rfl⟩ : syracuseStep 2852177 = 2139133) B2139133
theorem B1901451 : Blo 1901435 1901451 := bstep (se 1 (by rfl) ⟨1426088, by rfl⟩ : syracuseStep 1901451 = 2852177) B2852177
theorem B6417413 : Blo 1901435 6417413 := bbase (se 4 (by rfl) ⟨601632, by rfl⟩ : syracuseStep 6417413 = 1203265) (by norm_num)
theorem B4278275 : Blo 1901435 4278275 := bstep (se 1 (by rfl) ⟨3208706, by rfl⟩ : syracuseStep 4278275 = 6417413) B6417413
theorem B2852183 : Blo 1901435 2852183 := bstep (se 1 (by rfl) ⟨2139137, by rfl⟩ : syracuseStep 2852183 = 4278275) B4278275
theorem B1901455 : Blo 1901435 1901455 := bstep (se 1 (by rfl) ⟨1426091, by rfl⟩ : syracuseStep 1901455 = 2852183) B2852183
theorem B2852189 : Blo 1901435 2852189 := bbase (se 3 (by rfl) ⟨534785, by rfl⟩ : syracuseStep 2852189 = 1069571) (by norm_num)
theorem B1901459 : Blo 1901435 1901459 := bstep (se 1 (by rfl) ⟨1426094, by rfl⟩ : syracuseStep 1901459 = 2852189) B2852189
theorem B4278293 : Blo 1901435 4278293 := bbase (se 6 (by rfl) ⟨100272, by rfl⟩ : syracuseStep 4278293 = 200545) (by norm_num)
theorem B2852195 : Blo 1901435 2852195 := bstep (se 1 (by rfl) ⟨2139146, by rfl⟩ : syracuseStep 2852195 = 4278293) B4278293
theorem B1901463 : Blo 1901435 1901463 := bstep (se 1 (by rfl) ⟨1426097, by rfl⟩ : syracuseStep 1901463 = 2852195) B2852195
theorem B7219637 : Blo 1901435 7219637 := bbase (se 5 (by rfl) ⟨338420, by rfl⟩ : syracuseStep 7219637 = 676841) (by norm_num)
theorem B4813091 : Blo 1901435 4813091 := bstep (se 1 (by rfl) ⟨3609818, by rfl⟩ : syracuseStep 4813091 = 7219637) B7219637
theorem B3208727 : Blo 1901435 3208727 := bstep (se 1 (by rfl) ⟨2406545, by rfl⟩ : syracuseStep 3208727 = 4813091) B4813091
theorem B2139151 : Blo 1901435 2139151 := bstep (se 1 (by rfl) ⟨1604363, by rfl⟩ : syracuseStep 2139151 = 3208727) B3208727
theorem B2852201 : Blo 1901435 2852201 := bstep (se 2 (by rfl) ⟨1069575, by rfl⟩ : syracuseStep 2852201 = 2139151) B2139151
theorem B1901467 : Blo 1901435 1901467 := bstep (se 1 (by rfl) ⟨1426100, by rfl⟩ : syracuseStep 1901467 = 2852201) B2852201
theorem B2439385 : Blo 1901435 2439385 := bbase (se 2 (by rfl) ⟨914769, by rfl⟩ : syracuseStep 2439385 = 1829539) (by norm_num)
theorem B13010053 : Blo 1901435 13010053 := bstep (se 4 (by rfl) ⟨1219692, by rfl⟩ : syracuseStep 13010053 = 2439385) B2439385
theorem B17346737 : Blo 1901435 17346737 := bstep (se 2 (by rfl) ⟨6505026, by rfl⟩ : syracuseStep 17346737 = 13010053) B13010053
theorem B11564491 : Blo 1901435 11564491 := bstep (se 1 (by rfl) ⟨8673368, by rfl⟩ : syracuseStep 11564491 = 17346737) B17346737
theorem B15419321 : Blo 1901435 15419321 := bstep (se 2 (by rfl) ⟨5782245, by rfl⟩ : syracuseStep 15419321 = 11564491) B11564491
theorem B10279547 : Blo 1901435 10279547 := bstep (se 1 (by rfl) ⟨7709660, by rfl⟩ : syracuseStep 10279547 = 15419321) B15419321
theorem B6853031 : Blo 1901435 6853031 := bstep (se 1 (by rfl) ⟨5139773, by rfl⟩ : syracuseStep 6853031 = 10279547) B10279547
theorem B4568687 : Blo 1901435 4568687 := bstep (se 1 (by rfl) ⟨3426515, by rfl⟩ : syracuseStep 4568687 = 6853031) B6853031
theorem B3045791 : Blo 1901435 3045791 := bstep (se 1 (by rfl) ⟨2284343, by rfl⟩ : syracuseStep 3045791 = 4568687) B4568687
theorem B2030527 : Blo 1901435 2030527 := bstep (se 1 (by rfl) ⟨1522895, by rfl⟩ : syracuseStep 2030527 = 3045791) B3045791
theorem B10829477 : Blo 1901435 10829477 := bstep (se 4 (by rfl) ⟨1015263, by rfl⟩ : syracuseStep 10829477 = 2030527) B2030527
theorem B7219651 : Blo 1901435 7219651 := bstep (se 1 (by rfl) ⟨5414738, by rfl⟩ : syracuseStep 7219651 = 10829477) B10829477
theorem B9626201 : Blo 1901435 9626201 := bstep (se 2 (by rfl) ⟨3609825, by rfl⟩ : syracuseStep 9626201 = 7219651) B7219651
theorem B6417467 : Blo 1901435 6417467 := bstep (se 1 (by rfl) ⟨4813100, by rfl⟩ : syracuseStep 6417467 = 9626201) B9626201
theorem B4278311 : Blo 1901435 4278311 := bstep (se 1 (by rfl) ⟨3208733, by rfl⟩ : syracuseStep 4278311 = 6417467) B6417467
theorem B2852207 : Blo 1901435 2852207 := bstep (se 1 (by rfl) ⟨2139155, by rfl⟩ : syracuseStep 2852207 = 4278311) B4278311
theorem B1901471 : Blo 1901435 1901471 := bstep (se 1 (by rfl) ⟨1426103, by rfl⟩ : syracuseStep 1901471 = 2852207) B2852207
theorem B2852213 : Blo 1901435 2852213 := bbase (se 5 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 2852213 = 267395) (by norm_num)
theorem B1901475 : Blo 1901435 1901475 := bstep (se 1 (by rfl) ⟨1426106, by rfl⟩ : syracuseStep 1901475 = 2852213) B2852213
theorem B2707381 : Blo 1901435 2707381 := bbase (se 5 (by rfl) ⟨126908, by rfl⟩ : syracuseStep 2707381 = 253817) (by norm_num)
theorem B3609841 : Blo 1901435 3609841 := bstep (se 2 (by rfl) ⟨1353690, by rfl⟩ : syracuseStep 3609841 = 2707381) B2707381
theorem B4813121 : Blo 1901435 4813121 := bstep (se 2 (by rfl) ⟨1804920, by rfl⟩ : syracuseStep 4813121 = 3609841) B3609841
theorem B3208747 : Blo 1901435 3208747 := bstep (se 1 (by rfl) ⟨2406560, by rfl⟩ : syracuseStep 3208747 = 4813121) B4813121
theorem B4278329 : Blo 1901435 4278329 := bstep (se 2 (by rfl) ⟨1604373, by rfl⟩ : syracuseStep 4278329 = 3208747) B3208747
theorem B2852219 : Blo 1901435 2852219 := bstep (se 1 (by rfl) ⟨2139164, by rfl⟩ : syracuseStep 2852219 = 4278329) B4278329
theorem B1901479 : Blo 1901435 1901479 := bstep (se 1 (by rfl) ⟨1426109, by rfl⟩ : syracuseStep 1901479 = 2852219) B2852219
theorem B2139169 : Blo 1901435 2139169 := bbase (se 2 (by rfl) ⟨802188, by rfl⟩ : syracuseStep 2139169 = 1604377) (by norm_num)
theorem B2852225 : Blo 1901435 2852225 := bstep (se 2 (by rfl) ⟨1069584, by rfl⟩ : syracuseStep 2852225 = 2139169) B2139169
theorem B1901483 : Blo 1901435 1901483 := bstep (se 1 (by rfl) ⟨1426112, by rfl⟩ : syracuseStep 1901483 = 2852225) B2852225
theorem B4813141 : Blo 1901435 4813141 := bbase (se 10 (by rfl) ⟨7050, by rfl⟩ : syracuseStep 4813141 = 14101) (by norm_num)
theorem B6417521 : Blo 1901435 6417521 := bstep (se 2 (by rfl) ⟨2406570, by rfl⟩ : syracuseStep 6417521 = 4813141) B4813141
theorem B4278347 : Blo 1901435 4278347 := bstep (se 1 (by rfl) ⟨3208760, by rfl⟩ : syracuseStep 4278347 = 6417521) B6417521
theorem B2852231 : Blo 1901435 2852231 := bstep (se 1 (by rfl) ⟨2139173, by rfl⟩ : syracuseStep 2852231 = 4278347) B4278347
theorem B1901487 : Blo 1901435 1901487 := bstep (se 1 (by rfl) ⟨1426115, by rfl⟩ : syracuseStep 1901487 = 2852231) B2852231
theorem B2852237 : Blo 1901435 2852237 := bbase (se 3 (by rfl) ⟨534794, by rfl⟩ : syracuseStep 2852237 = 1069589) (by norm_num)
theorem B1901491 : Blo 1901435 1901491 := bstep (se 1 (by rfl) ⟨1426118, by rfl⟩ : syracuseStep 1901491 = 2852237) B2852237
theorem B4278365 : Blo 1901435 4278365 := bbase (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) (by norm_num)
theorem B2852243 : Blo 1901435 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B1901495 : Blo 1901435 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B3208781 : Blo 1901435 3208781 := bbase (se 3 (by rfl) ⟨601646, by rfl⟩ : syracuseStep 3208781 = 1203293) (by norm_num)
theorem B2139187 : Blo 1901435 2139187 := bstep (se 1 (by rfl) ⟨1604390, by rfl⟩ : syracuseStep 2139187 = 3208781) B3208781
theorem B2852249 : Blo 1901435 2852249 := bstep (se 2 (by rfl) ⟨1069593, by rfl⟩ : syracuseStep 2852249 = 2139187) B2139187
theorem B1901499 : Blo 1901435 1901499 := bstep (se 1 (by rfl) ⟨1426124, by rfl⟩ : syracuseStep 1901499 = 2852249) B2852249
theorem B6946645 : Blo 1901435 6946645 := bbase (se 9 (by rfl) ⟨20351, by rfl⟩ : syracuseStep 6946645 = 40703) (by norm_num)
theorem B9262193 : Blo 1901435 9262193 := bstep (se 2 (by rfl) ⟨3473322, by rfl⟩ : syracuseStep 9262193 = 6946645) B6946645
theorem B24699181 : Blo 1901435 24699181 := bstep (se 3 (by rfl) ⟨4631096, by rfl⟩ : syracuseStep 24699181 = 9262193) B9262193
theorem B32932241 : Blo 1901435 32932241 := bstep (se 2 (by rfl) ⟨12349590, by rfl⟩ : syracuseStep 32932241 = 24699181) B24699181
theorem B21954827 : Blo 1901435 21954827 := bstep (se 1 (by rfl) ⟨16466120, by rfl⟩ : syracuseStep 21954827 = 32932241) B32932241
theorem B14636551 : Blo 1901435 14636551 := bstep (se 1 (by rfl) ⟨10977413, by rfl⟩ : syracuseStep 14636551 = 21954827) B21954827
theorem B19515401 : Blo 1901435 19515401 := bstep (se 2 (by rfl) ⟨7318275, by rfl⟩ : syracuseStep 19515401 = 14636551) B14636551
theorem B13010267 : Blo 1901435 13010267 := bstep (se 1 (by rfl) ⟨9757700, by rfl⟩ : syracuseStep 13010267 = 19515401) B19515401
theorem B34694045 : Blo 1901435 34694045 := bstep (se 3 (by rfl) ⟨6505133, by rfl⟩ : syracuseStep 34694045 = 13010267) B13010267
theorem B23129363 : Blo 1901435 23129363 := bstep (se 1 (by rfl) ⟨17347022, by rfl⟩ : syracuseStep 23129363 = 34694045) B34694045
theorem B15419575 : Blo 1901435 15419575 := bstep (se 1 (by rfl) ⟨11564681, by rfl⟩ : syracuseStep 15419575 = 23129363) B23129363
theorem B20559433 : Blo 1901435 20559433 := bstep (se 2 (by rfl) ⟨7709787, by rfl⟩ : syracuseStep 20559433 = 15419575) B15419575
theorem B27412577 : Blo 1901435 27412577 := bstep (se 2 (by rfl) ⟨10279716, by rfl⟩ : syracuseStep 27412577 = 20559433) B20559433
theorem B18275051 : Blo 1901435 18275051 := bstep (se 1 (by rfl) ⟨13706288, by rfl⟩ : syracuseStep 18275051 = 27412577) B27412577
theorem B12183367 : Blo 1901435 12183367 := bstep (se 1 (by rfl) ⟨9137525, by rfl⟩ : syracuseStep 12183367 = 18275051) B18275051
theorem B16244489 : Blo 1901435 16244489 := bstep (se 2 (by rfl) ⟨6091683, by rfl⟩ : syracuseStep 16244489 = 12183367) B12183367
theorem B10829659 : Blo 1901435 10829659 := bstep (se 1 (by rfl) ⟨8122244, by rfl⟩ : syracuseStep 10829659 = 16244489) B16244489
theorem B14439545 : Blo 1901435 14439545 := bstep (se 2 (by rfl) ⟨5414829, by rfl⟩ : syracuseStep 14439545 = 10829659) B10829659
theorem B9626363 : Blo 1901435 9626363 := bstep (se 1 (by rfl) ⟨7219772, by rfl⟩ : syracuseStep 9626363 = 14439545) B14439545
theorem B6417575 : Blo 1901435 6417575 := bstep (se 1 (by rfl) ⟨4813181, by rfl⟩ : syracuseStep 6417575 = 9626363) B9626363
theorem B4278383 : Blo 1901435 4278383 := bstep (se 1 (by rfl) ⟨3208787, by rfl⟩ : syracuseStep 4278383 = 6417575) B6417575
theorem B2852255 : Blo 1901435 2852255 := bstep (se 1 (by rfl) ⟨2139191, by rfl⟩ : syracuseStep 2852255 = 4278383) B4278383
theorem B1901503 : Blo 1901435 1901503 := bstep (se 1 (by rfl) ⟨1426127, by rfl⟩ : syracuseStep 1901503 = 2852255) B2852255
theorem B2852261 : Blo 1901435 2852261 := bbase (se 4 (by rfl) ⟨267399, by rfl⟩ : syracuseStep 2852261 = 534799) (by norm_num)
theorem B1901507 : Blo 1901435 1901507 := bstep (se 1 (by rfl) ⟨1426130, by rfl⟩ : syracuseStep 1901507 = 2852261) B2852261
theorem B2406601 : Blo 1901435 2406601 := bbase (se 2 (by rfl) ⟨902475, by rfl⟩ : syracuseStep 2406601 = 1804951) (by norm_num)
theorem B3208801 : Blo 1901435 3208801 := bstep (se 2 (by rfl) ⟨1203300, by rfl⟩ : syracuseStep 3208801 = 2406601) B2406601
theorem B4278401 : Blo 1901435 4278401 := bstep (se 2 (by rfl) ⟨1604400, by rfl⟩ : syracuseStep 4278401 = 3208801) B3208801
theorem B2852267 : Blo 1901435 2852267 := bstep (se 1 (by rfl) ⟨2139200, by rfl⟩ : syracuseStep 2852267 = 4278401) B4278401
theorem B1901511 : Blo 1901435 1901511 := bstep (se 1 (by rfl) ⟨1426133, by rfl⟩ : syracuseStep 1901511 = 2852267) B2852267
theorem B2139205 : Blo 1901435 2139205 := bbase (se 4 (by rfl) ⟨200550, by rfl⟩ : syracuseStep 2139205 = 401101) (by norm_num)
theorem B2852273 : Blo 1901435 2852273 := bstep (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) B2139205
theorem B1901515 : Blo 1901435 1901515 := bstep (se 1 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 1901515 = 2852273) B2852273
theorem B3609917 : Blo 1901435 3609917 := bbase (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) (by norm_num)
theorem B2406611 : Blo 1901435 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B6417629 : Blo 1901435 6417629 := bstep (se 3 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 6417629 = 2406611) B2406611
theorem B4278419 : Blo 1901435 4278419 := bstep (se 1 (by rfl) ⟨3208814, by rfl⟩ : syracuseStep 4278419 = 6417629) B6417629
theorem B2852279 : Blo 1901435 2852279 := bstep (se 1 (by rfl) ⟨2139209, by rfl⟩ : syracuseStep 2852279 = 4278419) B4278419
theorem B1901519 : Blo 1901435 1901519 := bstep (se 1 (by rfl) ⟨1426139, by rfl⟩ : syracuseStep 1901519 = 2852279) B2852279
theorem B2852285 : Blo 1901435 2852285 := bbase (se 3 (by rfl) ⟨534803, by rfl⟩ : syracuseStep 2852285 = 1069607) (by norm_num)
theorem B1901523 : Blo 1901435 1901523 := bstep (se 1 (by rfl) ⟨1426142, by rfl⟩ : syracuseStep 1901523 = 2852285) B2852285
theorem B4278437 : Blo 1901435 4278437 := bbase (se 4 (by rfl) ⟨401103, by rfl⟩ : syracuseStep 4278437 = 802207) (by norm_num)
theorem B2852291 : Blo 1901435 2852291 := bstep (se 1 (by rfl) ⟨2139218, by rfl⟩ : syracuseStep 2852291 = 4278437) B4278437
theorem B1901527 : Blo 1901435 1901527 := bstep (se 1 (by rfl) ⟨1426145, by rfl⟩ : syracuseStep 1901527 = 2852291) B2852291
theorem B4813253 : Blo 1901435 4813253 := bbase (se 4 (by rfl) ⟨451242, by rfl⟩ : syracuseStep 4813253 = 902485) (by norm_num)
theorem B3208835 : Blo 1901435 3208835 := bstep (se 1 (by rfl) ⟨2406626, by rfl⟩ : syracuseStep 3208835 = 4813253) B4813253
theorem B2139223 : Blo 1901435 2139223 := bstep (se 1 (by rfl) ⟨1604417, by rfl⟩ : syracuseStep 2139223 = 3208835) B3208835
theorem B2852297 : Blo 1901435 2852297 := bstep (se 2 (by rfl) ⟨1069611, by rfl⟩ : syracuseStep 2852297 = 2139223) B2139223
theorem B1901531 : Blo 1901435 1901531 := bstep (se 1 (by rfl) ⟨1426148, by rfl⟩ : syracuseStep 1901531 = 2852297) B2852297
theorem B2569973 : Blo 1901435 2569973 := bbase (se 5 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 2569973 = 240935) (by norm_num)
theorem B6853261 : Blo 1901435 6853261 := bstep (se 3 (by rfl) ⟨1284986, by rfl⟩ : syracuseStep 6853261 = 2569973) B2569973
theorem B9137681 : Blo 1901435 9137681 := bstep (se 2 (by rfl) ⟨3426630, by rfl⟩ : syracuseStep 9137681 = 6853261) B6853261
theorem B6091787 : Blo 1901435 6091787 := bstep (se 1 (by rfl) ⟨4568840, by rfl⟩ : syracuseStep 6091787 = 9137681) B9137681
theorem B4061191 : Blo 1901435 4061191 := bstep (se 1 (by rfl) ⟨3045893, by rfl⟩ : syracuseStep 4061191 = 6091787) B6091787
theorem B5414921 : Blo 1901435 5414921 := bstep (se 2 (by rfl) ⟨2030595, by rfl⟩ : syracuseStep 5414921 = 4061191) B4061191
theorem B3609947 : Blo 1901435 3609947 := bstep (se 1 (by rfl) ⟨2707460, by rfl⟩ : syracuseStep 3609947 = 5414921) B5414921
theorem B9626525 : Blo 1901435 9626525 := bstep (se 3 (by rfl) ⟨1804973, by rfl⟩ : syracuseStep 9626525 = 3609947) B3609947
theorem B6417683 : Blo 1901435 6417683 := bstep (se 1 (by rfl) ⟨4813262, by rfl⟩ : syracuseStep 6417683 = 9626525) B9626525
theorem B4278455 : Blo 1901435 4278455 := bstep (se 1 (by rfl) ⟨3208841, by rfl⟩ : syracuseStep 4278455 = 6417683) B6417683
theorem B2852303 : Blo 1901435 2852303 := bstep (se 1 (by rfl) ⟨2139227, by rfl⟩ : syracuseStep 2852303 = 4278455) B4278455
theorem B1901535 : Blo 1901435 1901535 := bstep (se 1 (by rfl) ⟨1426151, by rfl⟩ : syracuseStep 1901535 = 2852303) B2852303
theorem B2852309 : Blo 1901435 2852309 := bbase (se 7 (by rfl) ⟨33425, by rfl⟩ : syracuseStep 2852309 = 66851) (by norm_num)
theorem B1901539 : Blo 1901435 1901539 := bstep (se 1 (by rfl) ⟨1426154, by rfl⟩ : syracuseStep 1901539 = 2852309) B2852309
theorem B7219925 : Blo 1901435 7219925 := bbase (se 7 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 7219925 = 169217) (by norm_num)
theorem B4813283 : Blo 1901435 4813283 := bstep (se 1 (by rfl) ⟨3609962, by rfl⟩ : syracuseStep 4813283 = 7219925) B7219925
theorem B3208855 : Blo 1901435 3208855 := bstep (se 1 (by rfl) ⟨2406641, by rfl⟩ : syracuseStep 3208855 = 4813283) B4813283
theorem B4278473 : Blo 1901435 4278473 := bstep (se 2 (by rfl) ⟨1604427, by rfl⟩ : syracuseStep 4278473 = 3208855) B3208855
theorem B2852315 : Blo 1901435 2852315 := bstep (se 1 (by rfl) ⟨2139236, by rfl⟩ : syracuseStep 2852315 = 4278473) B4278473
theorem B1901543 : Blo 1901435 1901543 := bstep (se 1 (by rfl) ⟨1426157, by rfl⟩ : syracuseStep 1901543 = 2852315) B2852315
theorem B2139241 : Blo 1901435 2139241 := bbase (se 2 (by rfl) ⟨802215, by rfl⟩ : syracuseStep 2139241 = 1604431) (by norm_num)
theorem B2852321 : Blo 1901435 2852321 := bstep (se 2 (by rfl) ⟨1069620, by rfl⟩ : syracuseStep 2852321 = 2139241) B2139241
theorem B1901547 : Blo 1901435 1901547 := bstep (se 1 (by rfl) ⟨1426160, by rfl⟩ : syracuseStep 1901547 = 2852321) B2852321
theorem B8673733 : Blo 1901435 8673733 := bbase (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) (by norm_num)
theorem B11564977 : Blo 1901435 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B15419969 : Blo 1901435 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B10279979 : Blo 1901435 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B6853319 : Blo 1901435 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B4568879 : Blo 1901435 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B3045919 : Blo 1901435 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B4061225 : Blo 1901435 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B10829933 : Blo 1901435 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B7219955 : Blo 1901435 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B4813303 : Blo 1901435 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B6417737 : Blo 1901435 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B4278491 : Blo 1901435 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B2852327 : Blo 1901435 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B1901551 : Blo 1901435 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B2852333 : Blo 1901435 2852333 := bbase (se 3 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 2852333 = 1069625) (by norm_num)
theorem B1901555 : Blo 1901435 1901555 := bstep (se 1 (by rfl) ⟨1426166, by rfl⟩ : syracuseStep 1901555 = 2852333) B2852333
theorem B4278509 : Blo 1901435 4278509 := bbase (se 3 (by rfl) ⟨802220, by rfl⟩ : syracuseStep 4278509 = 1604441) (by norm_num)
theorem B2852339 : Blo 1901435 2852339 := bstep (se 1 (by rfl) ⟨2139254, by rfl⟩ : syracuseStep 2852339 = 4278509) B4278509
theorem B1901559 : Blo 1901435 1901559 := bstep (se 1 (by rfl) ⟨1426169, by rfl⟩ : syracuseStep 1901559 = 2852339) B2852339
theorem B2707501 : Blo 1901435 2707501 := bbase (se 3 (by rfl) ⟨507656, by rfl⟩ : syracuseStep 2707501 = 1015313) (by norm_num)
theorem B3610001 : Blo 1901435 3610001 := bstep (se 2 (by rfl) ⟨1353750, by rfl⟩ : syracuseStep 3610001 = 2707501) B2707501
theorem B2406667 : Blo 1901435 2406667 := bstep (se 1 (by rfl) ⟨1805000, by rfl⟩ : syracuseStep 2406667 = 3610001) B3610001
theorem B3208889 : Blo 1901435 3208889 := bstep (se 2 (by rfl) ⟨1203333, by rfl⟩ : syracuseStep 3208889 = 2406667) B2406667
theorem B2139259 : Blo 1901435 2139259 := bstep (se 1 (by rfl) ⟨1604444, by rfl⟩ : syracuseStep 2139259 = 3208889) B3208889
theorem B2852345 : Blo 1901435 2852345 := bstep (se 2 (by rfl) ⟨1069629, by rfl⟩ : syracuseStep 2852345 = 2139259) B2139259
theorem B1901563 : Blo 1901435 1901563 := bstep (se 1 (by rfl) ⟨1426172, by rfl⟩ : syracuseStep 1901563 = 2852345) B2852345
theorem B3659261 : Blo 1901435 3659261 := bbase (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) (by norm_num)
theorem B39032117 : Blo 1901435 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B26021411 : Blo 1901435 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B17347607 : Blo 1901435 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B11565071 : Blo 1901435 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B7710047 : Blo 1901435 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B5140031 : Blo 1901435 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B13706749 : Blo 1901435 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B73102661 : Blo 1901435 73102661 := bstep (se 4 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 73102661 = 13706749) B13706749
theorem B48735107 : Blo 1901435 48735107 := bstep (se 1 (by rfl) ⟨36551330, by rfl⟩ : syracuseStep 48735107 = 73102661) B73102661
theorem B32490071 : Blo 1901435 32490071 := bstep (se 1 (by rfl) ⟨24367553, by rfl⟩ : syracuseStep 32490071 = 48735107) B48735107
theorem B21660047 : Blo 1901435 21660047 := bstep (se 1 (by rfl) ⟨16245035, by rfl⟩ : syracuseStep 21660047 = 32490071) B32490071
theorem B14440031 : Blo 1901435 14440031 := bstep (se 1 (by rfl) ⟨10830023, by rfl⟩ : syracuseStep 14440031 = 21660047) B21660047
theorem B9626687 : Blo 1901435 9626687 := bstep (se 1 (by rfl) ⟨7220015, by rfl⟩ : syracuseStep 9626687 = 14440031) B14440031
theorem B6417791 : Blo 1901435 6417791 := bstep (se 1 (by rfl) ⟨4813343, by rfl⟩ : syracuseStep 6417791 = 9626687) B9626687
theorem B4278527 : Blo 1901435 4278527 := bstep (se 1 (by rfl) ⟨3208895, by rfl⟩ : syracuseStep 4278527 = 6417791) B6417791
theorem B2852351 : Blo 1901435 2852351 := bstep (se 1 (by rfl) ⟨2139263, by rfl⟩ : syracuseStep 2852351 = 4278527) B4278527
theorem B1901567 : Blo 1901435 1901567 := bstep (se 1 (by rfl) ⟨1426175, by rfl⟩ : syracuseStep 1901567 = 2852351) B2852351
theorem B2852357 : Blo 1901435 2852357 := bbase (se 4 (by rfl) ⟨267408, by rfl⟩ : syracuseStep 2852357 = 534817) (by norm_num)
theorem B1901571 : Blo 1901435 1901571 := bstep (se 1 (by rfl) ⟨1426178, by rfl⟩ : syracuseStep 1901571 = 2852357) B2852357
theorem B3208909 : Blo 1901435 3208909 := bbase (se 3 (by rfl) ⟨601670, by rfl⟩ : syracuseStep 3208909 = 1203341) (by norm_num)
theorem B4278545 : Blo 1901435 4278545 := bstep (se 2 (by rfl) ⟨1604454, by rfl⟩ : syracuseStep 4278545 = 3208909) B3208909
theorem B2852363 : Blo 1901435 2852363 := bstep (se 1 (by rfl) ⟨2139272, by rfl⟩ : syracuseStep 2852363 = 4278545) B4278545
theorem B1901575 : Blo 1901435 1901575 := bstep (se 1 (by rfl) ⟨1426181, by rfl⟩ : syracuseStep 1901575 = 2852363) B2852363
theorem B2139277 : Blo 1901435 2139277 := bbase (se 3 (by rfl) ⟨401114, by rfl⟩ : syracuseStep 2139277 = 802229) (by norm_num)
theorem B2852369 : Blo 1901435 2852369 := bstep (se 2 (by rfl) ⟨1069638, by rfl⟩ : syracuseStep 2852369 = 2139277) B2139277
theorem B1901579 : Blo 1901435 1901579 := bstep (se 1 (by rfl) ⟨1426184, by rfl⟩ : syracuseStep 1901579 = 2852369) B2852369
theorem B6417845 : Blo 1901435 6417845 := bbase (se 5 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 6417845 = 601673) (by norm_num)
theorem B4278563 : Blo 1901435 4278563 := bstep (se 1 (by rfl) ⟨3208922, by rfl⟩ : syracuseStep 4278563 = 6417845) B6417845
theorem B2852375 : Blo 1901435 2852375 := bstep (se 1 (by rfl) ⟨2139281, by rfl⟩ : syracuseStep 2852375 = 4278563) B4278563
theorem B1901583 : Blo 1901435 1901583 := bstep (se 1 (by rfl) ⟨1426187, by rfl⟩ : syracuseStep 1901583 = 2852375) B2852375
theorem B2852381 : Blo 1901435 2852381 := bbase (se 3 (by rfl) ⟨534821, by rfl⟩ : syracuseStep 2852381 = 1069643) (by norm_num)
theorem B1901587 : Blo 1901435 1901587 := bstep (se 1 (by rfl) ⟨1426190, by rfl⟩ : syracuseStep 1901587 = 2852381) B2852381
theorem B4278581 : Blo 1901435 4278581 := bbase (se 5 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 4278581 = 401117) (by norm_num)
theorem B2852387 : Blo 1901435 2852387 := bstep (se 1 (by rfl) ⟨2139290, by rfl⟩ : syracuseStep 2852387 = 4278581) B4278581
theorem B1901591 : Blo 1901435 1901591 := bstep (se 1 (by rfl) ⟨1426193, by rfl⟩ : syracuseStep 1901591 = 2852387) B2852387
theorem B27413909 : Blo 1901435 27413909 := bbase (se 6 (by rfl) ⟨642513, by rfl⟩ : syracuseStep 27413909 = 1285027) (by norm_num)
theorem B18275939 : Blo 1901435 18275939 := bstep (se 1 (by rfl) ⟨13706954, by rfl⟩ : syracuseStep 18275939 = 27413909) B27413909
theorem B12183959 : Blo 1901435 12183959 := bstep (se 1 (by rfl) ⟨9137969, by rfl⟩ : syracuseStep 12183959 = 18275939) B18275939
theorem B8122639 : Blo 1901435 8122639 := bstep (se 1 (by rfl) ⟨6091979, by rfl⟩ : syracuseStep 8122639 = 12183959) B12183959
theorem B10830185 : Blo 1901435 10830185 := bstep (se 2 (by rfl) ⟨4061319, by rfl⟩ : syracuseStep 10830185 = 8122639) B8122639
theorem B7220123 : Blo 1901435 7220123 := bstep (se 1 (by rfl) ⟨5415092, by rfl⟩ : syracuseStep 7220123 = 10830185) B10830185
theorem B4813415 : Blo 1901435 4813415 := bstep (se 1 (by rfl) ⟨3610061, by rfl⟩ : syracuseStep 4813415 = 7220123) B7220123
theorem B3208943 : Blo 1901435 3208943 := bstep (se 1 (by rfl) ⟨2406707, by rfl⟩ : syracuseStep 3208943 = 4813415) B4813415
theorem B2139295 : Blo 1901435 2139295 := bstep (se 1 (by rfl) ⟨1604471, by rfl⟩ : syracuseStep 2139295 = 3208943) B3208943
theorem B2852393 : Blo 1901435 2852393 := bstep (se 2 (by rfl) ⟨1069647, by rfl⟩ : syracuseStep 2852393 = 2139295) B2139295
theorem B1901595 : Blo 1901435 1901595 := bstep (se 1 (by rfl) ⟨1426196, by rfl⟩ : syracuseStep 1901595 = 2852393) B2852393
theorem B6175109 : Blo 1901435 6175109 := bbase (se 4 (by rfl) ⟨578916, by rfl⟩ : syracuseStep 6175109 = 1157833) (by norm_num)
theorem B4116739 : Blo 1901435 4116739 := bstep (se 1 (by rfl) ⟨3087554, by rfl⟩ : syracuseStep 4116739 = 6175109) B6175109
theorem B5488985 : Blo 1901435 5488985 := bstep (se 2 (by rfl) ⟨2058369, by rfl⟩ : syracuseStep 5488985 = 4116739) B4116739
theorem B14637293 : Blo 1901435 14637293 := bstep (se 3 (by rfl) ⟨2744492, by rfl⟩ : syracuseStep 14637293 = 5488985) B5488985
theorem B9758195 : Blo 1901435 9758195 := bstep (se 1 (by rfl) ⟨7318646, by rfl⟩ : syracuseStep 9758195 = 14637293) B14637293
theorem B6505463 : Blo 1901435 6505463 := bstep (se 1 (by rfl) ⟨4879097, by rfl⟩ : syracuseStep 6505463 = 9758195) B9758195
theorem B4336975 : Blo 1901435 4336975 := bstep (se 1 (by rfl) ⟨3252731, by rfl⟩ : syracuseStep 4336975 = 6505463) B6505463
theorem B5782633 : Blo 1901435 5782633 := bstep (se 2 (by rfl) ⟨2168487, by rfl⟩ : syracuseStep 5782633 = 4336975) B4336975
theorem B30840709 : Blo 1901435 30840709 := bstep (se 4 (by rfl) ⟨2891316, by rfl⟩ : syracuseStep 30840709 = 5782633) B5782633
theorem B41120945 : Blo 1901435 41120945 := bstep (se 2 (by rfl) ⟨15420354, by rfl⟩ : syracuseStep 41120945 = 30840709) B30840709
theorem B27413963 : Blo 1901435 27413963 := bstep (se 1 (by rfl) ⟨20560472, by rfl⟩ : syracuseStep 27413963 = 41120945) B41120945
theorem B18275975 : Blo 1901435 18275975 := bstep (se 1 (by rfl) ⟨13706981, by rfl⟩ : syracuseStep 18275975 = 27413963) B27413963
theorem B12183983 : Blo 1901435 12183983 := bstep (se 1 (by rfl) ⟨9137987, by rfl⟩ : syracuseStep 12183983 = 18275975) B18275975
theorem B8122655 : Blo 1901435 8122655 := bstep (se 1 (by rfl) ⟨6091991, by rfl⟩ : syracuseStep 8122655 = 12183983) B12183983
theorem B5415103 : Blo 1901435 5415103 := bstep (se 1 (by rfl) ⟨4061327, by rfl⟩ : syracuseStep 5415103 = 8122655) B8122655
theorem B7220137 : Blo 1901435 7220137 := bstep (se 2 (by rfl) ⟨2707551, by rfl⟩ : syracuseStep 7220137 = 5415103) B5415103
theorem B9626849 : Blo 1901435 9626849 := bstep (se 2 (by rfl) ⟨3610068, by rfl⟩ : syracuseStep 9626849 = 7220137) B7220137
theorem B6417899 : Blo 1901435 6417899 := bstep (se 1 (by rfl) ⟨4813424, by rfl⟩ : syracuseStep 6417899 = 9626849) B9626849
theorem B4278599 : Blo 1901435 4278599 := bstep (se 1 (by rfl) ⟨3208949, by rfl⟩ : syracuseStep 4278599 = 6417899) B6417899
theorem B2852399 : Blo 1901435 2852399 := bstep (se 1 (by rfl) ⟨2139299, by rfl⟩ : syracuseStep 2852399 = 4278599) B4278599
theorem B1901599 : Blo 1901435 1901599 := bstep (se 1 (by rfl) ⟨1426199, by rfl⟩ : syracuseStep 1901599 = 2852399) B2852399
theorem B2852405 : Blo 1901435 2852405 := bbase (se 5 (by rfl) ⟨133706, by rfl⟩ : syracuseStep 2852405 = 267413) (by norm_num)
theorem B1901603 : Blo 1901435 1901603 := bstep (se 1 (by rfl) ⟨1426202, by rfl⟩ : syracuseStep 1901603 = 2852405) B2852405
theorem B4813445 : Blo 1901435 4813445 := bbase (se 4 (by rfl) ⟨451260, by rfl⟩ : syracuseStep 4813445 = 902521) (by norm_num)
theorem B3208963 : Blo 1901435 3208963 := bstep (se 1 (by rfl) ⟨2406722, by rfl⟩ : syracuseStep 3208963 = 4813445) B4813445
theorem B4278617 : Blo 1901435 4278617 := bstep (se 2 (by rfl) ⟨1604481, by rfl⟩ : syracuseStep 4278617 = 3208963) B3208963
theorem B2852411 : Blo 1901435 2852411 := bstep (se 1 (by rfl) ⟨2139308, by rfl⟩ : syracuseStep 2852411 = 4278617) B4278617
theorem B1901607 : Blo 1901435 1901607 := bstep (se 1 (by rfl) ⟨1426205, by rfl⟩ : syracuseStep 1901607 = 2852411) B2852411
theorem B2139313 : Blo 1901435 2139313 := bbase (se 2 (by rfl) ⟨802242, by rfl⟩ : syracuseStep 2139313 = 1604485) (by norm_num)
theorem B2852417 : Blo 1901435 2852417 := bstep (se 2 (by rfl) ⟨1069656, by rfl⟩ : syracuseStep 2852417 = 2139313) B2139313
theorem B1901611 : Blo 1901435 1901611 := bstep (se 1 (by rfl) ⟨1426208, by rfl⟩ : syracuseStep 1901611 = 2852417) B2852417
theorem B2030681 : Blo 1901435 2030681 := bbase (se 2 (by rfl) ⟨761505, by rfl⟩ : syracuseStep 2030681 = 1523011) (by norm_num)
theorem B5415149 : Blo 1901435 5415149 := bstep (se 3 (by rfl) ⟨1015340, by rfl⟩ : syracuseStep 5415149 = 2030681) B2030681
theorem B3610099 : Blo 1901435 3610099 := bstep (se 1 (by rfl) ⟨2707574, by rfl⟩ : syracuseStep 3610099 = 5415149) B5415149
theorem B4813465 : Blo 1901435 4813465 := bstep (se 2 (by rfl) ⟨1805049, by rfl⟩ : syracuseStep 4813465 = 3610099) B3610099
theorem B6417953 : Blo 1901435 6417953 := bstep (se 2 (by rfl) ⟨2406732, by rfl⟩ : syracuseStep 6417953 = 4813465) B4813465
theorem B4278635 : Blo 1901435 4278635 := bstep (se 1 (by rfl) ⟨3208976, by rfl⟩ : syracuseStep 4278635 = 6417953) B6417953
theorem B2852423 : Blo 1901435 2852423 := bstep (se 1 (by rfl) ⟨2139317, by rfl⟩ : syracuseStep 2852423 = 4278635) B4278635
theorem B1901615 : Blo 1901435 1901615 := bstep (se 1 (by rfl) ⟨1426211, by rfl⟩ : syracuseStep 1901615 = 2852423) B2852423
theorem B2852429 : Blo 1901435 2852429 := bbase (se 3 (by rfl) ⟨534830, by rfl⟩ : syracuseStep 2852429 = 1069661) (by norm_num)
theorem B1901619 : Blo 1901435 1901619 := bstep (se 1 (by rfl) ⟨1426214, by rfl⟩ : syracuseStep 1901619 = 2852429) B2852429
theorem B4278653 : Blo 1901435 4278653 := bbase (se 3 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 4278653 = 1604495) (by norm_num)
theorem B2852435 : Blo 1901435 2852435 := bstep (se 1 (by rfl) ⟨2139326, by rfl⟩ : syracuseStep 2852435 = 4278653) B4278653
theorem B1901623 : Blo 1901435 1901623 := bstep (se 1 (by rfl) ⟨1426217, by rfl⟩ : syracuseStep 1901623 = 2852435) B2852435
theorem B3208997 : Blo 1901435 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B2139331 : Blo 1901435 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B2852441 : Blo 1901435 2852441 := bstep (se 2 (by rfl) ⟨1069665, by rfl⟩ : syracuseStep 2852441 = 2139331) B2139331
theorem B1901627 : Blo 1901435 1901627 := bstep (se 1 (by rfl) ⟨1426220, by rfl⟩ : syracuseStep 1901627 = 2852441) B2852441
theorem B2707597 : Blo 1901435 2707597 := bbase (se 3 (by rfl) ⟨507674, by rfl⟩ : syracuseStep 2707597 = 1015349) (by norm_num)
theorem B14440517 : Blo 1901435 14440517 := bstep (se 4 (by rfl) ⟨1353798, by rfl⟩ : syracuseStep 14440517 = 2707597) B2707597
theorem B9627011 : Blo 1901435 9627011 := bstep (se 1 (by rfl) ⟨7220258, by rfl⟩ : syracuseStep 9627011 = 14440517) B14440517
theorem B6418007 : Blo 1901435 6418007 := bstep (se 1 (by rfl) ⟨4813505, by rfl⟩ : syracuseStep 6418007 = 9627011) B9627011
theorem B4278671 : Blo 1901435 4278671 := bstep (se 1 (by rfl) ⟨3209003, by rfl⟩ : syracuseStep 4278671 = 6418007) B6418007
theorem B2852447 : Blo 1901435 2852447 := bstep (se 1 (by rfl) ⟨2139335, by rfl⟩ : syracuseStep 2852447 = 4278671) B4278671
theorem B1901631 : Blo 1901435 1901631 := bstep (se 1 (by rfl) ⟨1426223, by rfl⟩ : syracuseStep 1901631 = 2852447) B2852447
theorem B2852453 : Blo 1901435 2852453 := bbase (se 4 (by rfl) ⟨267417, by rfl⟩ : syracuseStep 2852453 = 534835) (by norm_num)
theorem B1901635 : Blo 1901435 1901635 := bstep (se 1 (by rfl) ⟨1426226, by rfl⟩ : syracuseStep 1901635 = 2852453) B2852453
theorem B3046061 : Blo 1901435 3046061 := bbase (se 3 (by rfl) ⟨571136, by rfl⟩ : syracuseStep 3046061 = 1142273) (by norm_num)
theorem B2030707 : Blo 1901435 2030707 := bstep (se 1 (by rfl) ⟨1523030, by rfl⟩ : syracuseStep 2030707 = 3046061) B3046061
theorem B2707609 : Blo 1901435 2707609 := bstep (se 2 (by rfl) ⟨1015353, by rfl⟩ : syracuseStep 2707609 = 2030707) B2030707
theorem B3610145 : Blo 1901435 3610145 := bstep (se 2 (by rfl) ⟨1353804, by rfl⟩ : syracuseStep 3610145 = 2707609) B2707609
theorem B2406763 : Blo 1901435 2406763 := bstep (se 1 (by rfl) ⟨1805072, by rfl⟩ : syracuseStep 2406763 = 3610145) B3610145
theorem B3209017 : Blo 1901435 3209017 := bstep (se 2 (by rfl) ⟨1203381, by rfl⟩ : syracuseStep 3209017 = 2406763) B2406763
theorem B4278689 : Blo 1901435 4278689 := bstep (se 2 (by rfl) ⟨1604508, by rfl⟩ : syracuseStep 4278689 = 3209017) B3209017
theorem B2852459 : Blo 1901435 2852459 := bstep (se 1 (by rfl) ⟨2139344, by rfl⟩ : syracuseStep 2852459 = 4278689) B4278689
theorem B1901639 : Blo 1901435 1901639 := bstep (se 1 (by rfl) ⟨1426229, by rfl⟩ : syracuseStep 1901639 = 2852459) B2852459
theorem B2139349 : Blo 1901435 2139349 := bbase (se 7 (by rfl) ⟨25070, by rfl⟩ : syracuseStep 2139349 = 50141) (by norm_num)
theorem B2852465 : Blo 1901435 2852465 := bstep (se 2 (by rfl) ⟨1069674, by rfl⟩ : syracuseStep 2852465 = 2139349) B2139349
theorem B1901643 : Blo 1901435 1901643 := bstep (se 1 (by rfl) ⟨1426232, by rfl⟩ : syracuseStep 1901643 = 2852465) B2852465
theorem B2406773 : Blo 1901435 2406773 := bbase (se 5 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 2406773 = 225635) (by norm_num)
theorem B6418061 : Blo 1901435 6418061 := bstep (se 3 (by rfl) ⟨1203386, by rfl⟩ : syracuseStep 6418061 = 2406773) B2406773
theorem B4278707 : Blo 1901435 4278707 := bstep (se 1 (by rfl) ⟨3209030, by rfl⟩ : syracuseStep 4278707 = 6418061) B6418061
theorem B2852471 : Blo 1901435 2852471 := bstep (se 1 (by rfl) ⟨2139353, by rfl⟩ : syracuseStep 2852471 = 4278707) B4278707
theorem B1901647 : Blo 1901435 1901647 := bstep (se 1 (by rfl) ⟨1426235, by rfl⟩ : syracuseStep 1901647 = 2852471) B2852471
theorem B2852477 : Blo 1901435 2852477 := bbase (se 3 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 2852477 = 1069679) (by norm_num)
theorem B1901651 : Blo 1901435 1901651 := bstep (se 1 (by rfl) ⟨1426238, by rfl⟩ : syracuseStep 1901651 = 2852477) B2852477
theorem B4278725 : Blo 1901435 4278725 := bbase (se 4 (by rfl) ⟨401130, by rfl⟩ : syracuseStep 4278725 = 802261) (by norm_num)
theorem B2852483 : Blo 1901435 2852483 := bstep (se 1 (by rfl) ⟨2139362, by rfl⟩ : syracuseStep 2852483 = 4278725) B4278725
theorem B1901655 : Blo 1901435 1901655 := bstep (se 1 (by rfl) ⟨1426241, by rfl⟩ : syracuseStep 1901655 = 2852483) B2852483
theorem B2570141 : Blo 1901435 2570141 := bbase (se 3 (by rfl) ⟨481901, by rfl⟩ : syracuseStep 2570141 = 963803) (by norm_num)
theorem B6853709 : Blo 1901435 6853709 := bstep (se 3 (by rfl) ⟨1285070, by rfl⟩ : syracuseStep 6853709 = 2570141) B2570141
theorem B4569139 : Blo 1901435 4569139 := bstep (se 1 (by rfl) ⟨3426854, by rfl⟩ : syracuseStep 4569139 = 6853709) B6853709
theorem B6092185 : Blo 1901435 6092185 := bstep (se 2 (by rfl) ⟨2284569, by rfl⟩ : syracuseStep 6092185 = 4569139) B4569139
theorem B8122913 : Blo 1901435 8122913 := bstep (se 2 (by rfl) ⟨3046092, by rfl⟩ : syracuseStep 8122913 = 6092185) B6092185
theorem B5415275 : Blo 1901435 5415275 := bstep (se 1 (by rfl) ⟨4061456, by rfl⟩ : syracuseStep 5415275 = 8122913) B8122913
theorem B3610183 : Blo 1901435 3610183 := bstep (se 1 (by rfl) ⟨2707637, by rfl⟩ : syracuseStep 3610183 = 5415275) B5415275
theorem B4813577 : Blo 1901435 4813577 := bstep (se 2 (by rfl) ⟨1805091, by rfl⟩ : syracuseStep 4813577 = 3610183) B3610183
theorem B3209051 : Blo 1901435 3209051 := bstep (se 1 (by rfl) ⟨2406788, by rfl⟩ : syracuseStep 3209051 = 4813577) B4813577
theorem B2139367 : Blo 1901435 2139367 := bstep (se 1 (by rfl) ⟨1604525, by rfl⟩ : syracuseStep 2139367 = 3209051) B3209051
theorem B2852489 : Blo 1901435 2852489 := bstep (se 2 (by rfl) ⟨1069683, by rfl⟩ : syracuseStep 2852489 = 2139367) B2139367
theorem B1901659 : Blo 1901435 1901659 := bstep (se 1 (by rfl) ⟨1426244, by rfl⟩ : syracuseStep 1901659 = 2852489) B2852489
theorem B9627173 : Blo 1901435 9627173 := bbase (se 4 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 9627173 = 1805095) (by norm_num)
theorem B6418115 : Blo 1901435 6418115 := bstep (se 1 (by rfl) ⟨4813586, by rfl⟩ : syracuseStep 6418115 = 9627173) B9627173
theorem B4278743 : Blo 1901435 4278743 := bstep (se 1 (by rfl) ⟨3209057, by rfl⟩ : syracuseStep 4278743 = 6418115) B6418115
theorem B2852495 : Blo 1901435 2852495 := bstep (se 1 (by rfl) ⟨2139371, by rfl⟩ : syracuseStep 2852495 = 4278743) B4278743
theorem B1901663 : Blo 1901435 1901663 := bstep (se 1 (by rfl) ⟨1426247, by rfl⟩ : syracuseStep 1901663 = 2852495) B2852495
theorem B2852501 : Blo 1901435 2852501 := bbase (se 6 (by rfl) ⟨66855, by rfl⟩ : syracuseStep 2852501 = 133711) (by norm_num)
theorem B1901667 : Blo 1901435 1901667 := bstep (se 1 (by rfl) ⟨1426250, by rfl⟩ : syracuseStep 1901667 = 2852501) B2852501
theorem B5782853 : Blo 1901435 5782853 := bbase (se 4 (by rfl) ⟨542142, by rfl⟩ : syracuseStep 5782853 = 1084285) (by norm_num)
theorem B15420941 : Blo 1901435 15420941 := bstep (se 3 (by rfl) ⟨2891426, by rfl⟩ : syracuseStep 15420941 = 5782853) B5782853
theorem B10280627 : Blo 1901435 10280627 := bstep (se 1 (by rfl) ⟨7710470, by rfl⟩ : syracuseStep 10280627 = 15420941) B15420941
theorem B6853751 : Blo 1901435 6853751 := bstep (se 1 (by rfl) ⟨5140313, by rfl⟩ : syracuseStep 6853751 = 10280627) B10280627
theorem B4569167 : Blo 1901435 4569167 := bstep (se 1 (by rfl) ⟨3426875, by rfl⟩ : syracuseStep 4569167 = 6853751) B6853751
theorem B12184445 : Blo 1901435 12184445 := bstep (se 3 (by rfl) ⟨2284583, by rfl⟩ : syracuseStep 12184445 = 4569167) B4569167
theorem B8122963 : Blo 1901435 8122963 := bstep (se 1 (by rfl) ⟨6092222, by rfl⟩ : syracuseStep 8122963 = 12184445) B12184445
theorem B10830617 : Blo 1901435 10830617 := bstep (se 2 (by rfl) ⟨4061481, by rfl⟩ : syracuseStep 10830617 = 8122963) B8122963
theorem B7220411 : Blo 1901435 7220411 := bstep (se 1 (by rfl) ⟨5415308, by rfl⟩ : syracuseStep 7220411 = 10830617) B10830617
theorem B4813607 : Blo 1901435 4813607 := bstep (se 1 (by rfl) ⟨3610205, by rfl⟩ : syracuseStep 4813607 = 7220411) B7220411
theorem B3209071 : Blo 1901435 3209071 := bstep (se 1 (by rfl) ⟨2406803, by rfl⟩ : syracuseStep 3209071 = 4813607) B4813607
theorem B4278761 : Blo 1901435 4278761 := bstep (se 2 (by rfl) ⟨1604535, by rfl⟩ : syracuseStep 4278761 = 3209071) B3209071
theorem B2852507 : Blo 1901435 2852507 := bstep (se 1 (by rfl) ⟨2139380, by rfl⟩ : syracuseStep 2852507 = 4278761) B4278761
theorem B1901671 : Blo 1901435 1901671 := bstep (se 1 (by rfl) ⟨1426253, by rfl⟩ : syracuseStep 1901671 = 2852507) B2852507
theorem B2139385 : Blo 1901435 2139385 := bbase (se 2 (by rfl) ⟨802269, by rfl⟩ : syracuseStep 2139385 = 1604539) (by norm_num)
theorem B2852513 : Blo 1901435 2852513 := bstep (se 2 (by rfl) ⟨1069692, by rfl⟩ : syracuseStep 2852513 = 2139385) B2139385
theorem B1901675 : Blo 1901435 1901675 := bstep (se 1 (by rfl) ⟨1426256, by rfl⟩ : syracuseStep 1901675 = 2852513) B2852513
theorem B8122997 : Blo 1901435 8122997 := bbase (se 5 (by rfl) ⟨380765, by rfl⟩ : syracuseStep 8122997 = 761531) (by norm_num)
theorem B5415331 : Blo 1901435 5415331 := bstep (se 1 (by rfl) ⟨4061498, by rfl⟩ : syracuseStep 5415331 = 8122997) B8122997
theorem B7220441 : Blo 1901435 7220441 := bstep (se 2 (by rfl) ⟨2707665, by rfl⟩ : syracuseStep 7220441 = 5415331) B5415331
theorem B4813627 : Blo 1901435 4813627 := bstep (se 1 (by rfl) ⟨3610220, by rfl⟩ : syracuseStep 4813627 = 7220441) B7220441
theorem B6418169 : Blo 1901435 6418169 := bstep (se 2 (by rfl) ⟨2406813, by rfl⟩ : syracuseStep 6418169 = 4813627) B4813627
theorem B4278779 : Blo 1901435 4278779 := bstep (se 1 (by rfl) ⟨3209084, by rfl⟩ : syracuseStep 4278779 = 6418169) B6418169
theorem B2852519 : Blo 1901435 2852519 := bstep (se 1 (by rfl) ⟨2139389, by rfl⟩ : syracuseStep 2852519 = 4278779) B4278779
theorem B1901679 : Blo 1901435 1901679 := bstep (se 1 (by rfl) ⟨1426259, by rfl⟩ : syracuseStep 1901679 = 2852519) B2852519
theorem B2852525 : Blo 1901435 2852525 := bbase (se 3 (by rfl) ⟨534848, by rfl⟩ : syracuseStep 2852525 = 1069697) (by norm_num)
theorem B1901683 : Blo 1901435 1901683 := bstep (se 1 (by rfl) ⟨1426262, by rfl⟩ : syracuseStep 1901683 = 2852525) B2852525
theorem B4278797 : Blo 1901435 4278797 := bbase (se 3 (by rfl) ⟨802274, by rfl⟩ : syracuseStep 4278797 = 1604549) (by norm_num)
theorem B2852531 : Blo 1901435 2852531 := bstep (se 1 (by rfl) ⟨2139398, by rfl⟩ : syracuseStep 2852531 = 4278797) B4278797
theorem B1901687 : Blo 1901435 1901687 := bstep (se 1 (by rfl) ⟨1426265, by rfl⟩ : syracuseStep 1901687 = 2852531) B2852531
theorem B2406829 : Blo 1901435 2406829 := bbase (se 3 (by rfl) ⟨451280, by rfl⟩ : syracuseStep 2406829 = 902561) (by norm_num)
theorem B3209105 : Blo 1901435 3209105 := bstep (se 2 (by rfl) ⟨1203414, by rfl⟩ : syracuseStep 3209105 = 2406829) B2406829
theorem B2139403 : Blo 1901435 2139403 := bstep (se 1 (by rfl) ⟨1604552, by rfl⟩ : syracuseStep 2139403 = 3209105) B3209105
theorem B2852537 : Blo 1901435 2852537 := bstep (se 2 (by rfl) ⟨1069701, by rfl⟩ : syracuseStep 2852537 = 2139403) B2139403
theorem B1901691 : Blo 1901435 1901691 := bstep (se 1 (by rfl) ⟨1426268, by rfl⟩ : syracuseStep 1901691 = 2852537) B2852537
theorem B12184597 : Blo 1901435 12184597 := bbase (se 6 (by rfl) ⟨285576, by rfl⟩ : syracuseStep 12184597 = 571153) (by norm_num)
theorem B16246129 : Blo 1901435 16246129 := bstep (se 2 (by rfl) ⟨6092298, by rfl⟩ : syracuseStep 16246129 = 12184597) B12184597
theorem B21661505 : Blo 1901435 21661505 := bstep (se 2 (by rfl) ⟨8123064, by rfl⟩ : syracuseStep 21661505 = 16246129) B16246129
theorem B14441003 : Blo 1901435 14441003 := bstep (se 1 (by rfl) ⟨10830752, by rfl⟩ : syracuseStep 14441003 = 21661505) B21661505
theorem B9627335 : Blo 1901435 9627335 := bstep (se 1 (by rfl) ⟨7220501, by rfl⟩ : syracuseStep 9627335 = 14441003) B14441003
theorem B6418223 : Blo 1901435 6418223 := bstep (se 1 (by rfl) ⟨4813667, by rfl⟩ : syracuseStep 6418223 = 9627335) B9627335
theorem B4278815 : Blo 1901435 4278815 := bstep (se 1 (by rfl) ⟨3209111, by rfl⟩ : syracuseStep 4278815 = 6418223) B6418223
theorem B2852543 : Blo 1901435 2852543 := bstep (se 1 (by rfl) ⟨2139407, by rfl⟩ : syracuseStep 2852543 = 4278815) B4278815
theorem B1901695 : Blo 1901435 1901695 := bstep (se 1 (by rfl) ⟨1426271, by rfl⟩ : syracuseStep 1901695 = 2852543) B2852543
theorem B2852549 : Blo 1901435 2852549 := bbase (se 4 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 2852549 = 534853) (by norm_num)
theorem B1901699 : Blo 1901435 1901699 := bstep (se 1 (by rfl) ⟨1426274, by rfl⟩ : syracuseStep 1901699 = 2852549) B2852549
theorem B3209125 : Blo 1901435 3209125 := bbase (se 4 (by rfl) ⟨300855, by rfl⟩ : syracuseStep 3209125 = 601711) (by norm_num)
theorem B4278833 : Blo 1901435 4278833 := bstep (se 2 (by rfl) ⟨1604562, by rfl⟩ : syracuseStep 4278833 = 3209125) B3209125
theorem B2852555 : Blo 1901435 2852555 := bstep (se 1 (by rfl) ⟨2139416, by rfl⟩ : syracuseStep 2852555 = 4278833) B4278833
theorem B1901703 : Blo 1901435 1901703 := bstep (se 1 (by rfl) ⟨1426277, by rfl⟩ : syracuseStep 1901703 = 2852555) B2852555
theorem B2139421 : Blo 1901435 2139421 := bbase (se 3 (by rfl) ⟨401141, by rfl⟩ : syracuseStep 2139421 = 802283) (by norm_num)
theorem B2852561 : Blo 1901435 2852561 := bstep (se 2 (by rfl) ⟨1069710, by rfl⟩ : syracuseStep 2852561 = 2139421) B2139421
theorem B1901707 : Blo 1901435 1901707 := bstep (se 1 (by rfl) ⟨1426280, by rfl⟩ : syracuseStep 1901707 = 2852561) B2852561
theorem B6418277 : Blo 1901435 6418277 := bbase (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) (by norm_num)
theorem B4278851 : Blo 1901435 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B2852567 : Blo 1901435 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B1901711 : Blo 1901435 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B2852573 : Blo 1901435 2852573 := bbase (se 3 (by rfl) ⟨534857, by rfl⟩ : syracuseStep 2852573 = 1069715) (by norm_num)
theorem B1901715 : Blo 1901435 1901715 := bstep (se 1 (by rfl) ⟨1426286, by rfl⟩ : syracuseStep 1901715 = 2852573) B2852573
theorem B4278869 : Blo 1901435 4278869 := bbase (se 8 (by rfl) ⟨25071, by rfl⟩ : syracuseStep 4278869 = 50143) (by norm_num)
theorem B2852579 : Blo 1901435 2852579 := bstep (se 1 (by rfl) ⟨2139434, by rfl⟩ : syracuseStep 2852579 = 4278869) B4278869
theorem B1901719 : Blo 1901435 1901719 := bstep (se 1 (by rfl) ⟨1426289, by rfl⟩ : syracuseStep 1901719 = 2852579) B2852579
theorem B4569293 : Blo 1901435 4569293 := bbase (se 3 (by rfl) ⟨856742, by rfl⟩ : syracuseStep 4569293 = 1713485) (by norm_num)
theorem B3046195 : Blo 1901435 3046195 := bstep (se 1 (by rfl) ⟨2284646, by rfl⟩ : syracuseStep 3046195 = 4569293) B4569293
theorem B4061593 : Blo 1901435 4061593 := bstep (se 2 (by rfl) ⟨1523097, by rfl⟩ : syracuseStep 4061593 = 3046195) B3046195
theorem B5415457 : Blo 1901435 5415457 := bstep (se 2 (by rfl) ⟨2030796, by rfl⟩ : syracuseStep 5415457 = 4061593) B4061593
theorem B7220609 : Blo 1901435 7220609 := bstep (se 2 (by rfl) ⟨2707728, by rfl⟩ : syracuseStep 7220609 = 5415457) B5415457
theorem B4813739 : Blo 1901435 4813739 := bstep (se 1 (by rfl) ⟨3610304, by rfl⟩ : syracuseStep 4813739 = 7220609) B7220609
theorem B3209159 : Blo 1901435 3209159 := bstep (se 1 (by rfl) ⟨2406869, by rfl⟩ : syracuseStep 3209159 = 4813739) B4813739
theorem B2139439 : Blo 1901435 2139439 := bstep (se 1 (by rfl) ⟨1604579, by rfl⟩ : syracuseStep 2139439 = 3209159) B3209159
theorem B2852585 : Blo 1901435 2852585 := bstep (se 2 (by rfl) ⟨1069719, by rfl⟩ : syracuseStep 2852585 = 2139439) B2139439
theorem B1901723 : Blo 1901435 1901723 := bstep (se 1 (by rfl) ⟨1426292, by rfl⟩ : syracuseStep 1901723 = 2852585) B2852585
theorem B4569301 : Blo 1901435 4569301 := bbase (se 7 (by rfl) ⟨53546, by rfl⟩ : syracuseStep 4569301 = 107093) (by norm_num)
theorem B24369605 : Blo 1901435 24369605 := bstep (se 4 (by rfl) ⟨2284650, by rfl⟩ : syracuseStep 24369605 = 4569301) B4569301
theorem B16246403 : Blo 1901435 16246403 := bstep (se 1 (by rfl) ⟨12184802, by rfl⟩ : syracuseStep 16246403 = 24369605) B24369605
theorem B10830935 : Blo 1901435 10830935 := bstep (se 1 (by rfl) ⟨8123201, by rfl⟩ : syracuseStep 10830935 = 16246403) B16246403
theorem B7220623 : Blo 1901435 7220623 := bstep (se 1 (by rfl) ⟨5415467, by rfl⟩ : syracuseStep 7220623 = 10830935) B10830935
theorem B9627497 : Blo 1901435 9627497 := bstep (se 2 (by rfl) ⟨3610311, by rfl⟩ : syracuseStep 9627497 = 7220623) B7220623
theorem B6418331 : Blo 1901435 6418331 := bstep (se 1 (by rfl) ⟨4813748, by rfl⟩ : syracuseStep 6418331 = 9627497) B9627497
theorem B4278887 : Blo 1901435 4278887 := bstep (se 1 (by rfl) ⟨3209165, by rfl⟩ : syracuseStep 4278887 = 6418331) B6418331
theorem B2852591 : Blo 1901435 2852591 := bstep (se 1 (by rfl) ⟨2139443, by rfl⟩ : syracuseStep 2852591 = 4278887) B4278887
theorem B1901727 : Blo 1901435 1901727 := bstep (se 1 (by rfl) ⟨1426295, by rfl⟩ : syracuseStep 1901727 = 2852591) B2852591
theorem B2852597 : Blo 1901435 2852597 := bbase (se 5 (by rfl) ⟨133715, by rfl⟩ : syracuseStep 2852597 = 267431) (by norm_num)
theorem B1901731 : Blo 1901435 1901731 := bstep (se 1 (by rfl) ⟨1426298, by rfl⟩ : syracuseStep 1901731 = 2852597) B2852597
theorem B8123237 : Blo 1901435 8123237 := bbase (se 4 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 8123237 = 1523107) (by norm_num)
theorem B5415491 : Blo 1901435 5415491 := bstep (se 1 (by rfl) ⟨4061618, by rfl⟩ : syracuseStep 5415491 = 8123237) B8123237
theorem B3610327 : Blo 1901435 3610327 := bstep (se 1 (by rfl) ⟨2707745, by rfl⟩ : syracuseStep 3610327 = 5415491) B5415491
theorem B4813769 : Blo 1901435 4813769 := bstep (se 2 (by rfl) ⟨1805163, by rfl⟩ : syracuseStep 4813769 = 3610327) B3610327
theorem B3209179 : Blo 1901435 3209179 := bstep (se 1 (by rfl) ⟨2406884, by rfl⟩ : syracuseStep 3209179 = 4813769) B4813769
theorem B4278905 : Blo 1901435 4278905 := bstep (se 2 (by rfl) ⟨1604589, by rfl⟩ : syracuseStep 4278905 = 3209179) B3209179
theorem B2852603 : Blo 1901435 2852603 := bstep (se 1 (by rfl) ⟨2139452, by rfl⟩ : syracuseStep 2852603 = 4278905) B4278905
theorem B1901735 : Blo 1901435 1901735 := bstep (se 1 (by rfl) ⟨1426301, by rfl⟩ : syracuseStep 1901735 = 2852603) B2852603
theorem B2139457 : Blo 1901435 2139457 := bbase (se 2 (by rfl) ⟨802296, by rfl⟩ : syracuseStep 2139457 = 1604593) (by norm_num)
theorem B2852609 : Blo 1901435 2852609 := bstep (se 2 (by rfl) ⟨1069728, by rfl⟩ : syracuseStep 2852609 = 2139457) B2139457
theorem B1901739 : Blo 1901435 1901739 := bstep (se 1 (by rfl) ⟨1426304, by rfl⟩ : syracuseStep 1901739 = 2852609) B2852609
theorem B4813789 : Blo 1901435 4813789 := bbase (se 3 (by rfl) ⟨902585, by rfl⟩ : syracuseStep 4813789 = 1805171) (by norm_num)
theorem B6418385 : Blo 1901435 6418385 := bstep (se 2 (by rfl) ⟨2406894, by rfl⟩ : syracuseStep 6418385 = 4813789) B4813789
theorem B4278923 : Blo 1901435 4278923 := bstep (se 1 (by rfl) ⟨3209192, by rfl⟩ : syracuseStep 4278923 = 6418385) B6418385
theorem B2852615 : Blo 1901435 2852615 := bstep (se 1 (by rfl) ⟨2139461, by rfl⟩ : syracuseStep 2852615 = 4278923) B4278923
theorem B1901743 : Blo 1901435 1901743 := bstep (se 1 (by rfl) ⟨1426307, by rfl⟩ : syracuseStep 1901743 = 2852615) B2852615
theorem B2852621 : Blo 1901435 2852621 := bbase (se 3 (by rfl) ⟨534866, by rfl⟩ : syracuseStep 2852621 = 1069733) (by norm_num)
theorem B1901747 : Blo 1901435 1901747 := bstep (se 1 (by rfl) ⟨1426310, by rfl⟩ : syracuseStep 1901747 = 2852621) B2852621
theorem B4278941 : Blo 1901435 4278941 := bbase (se 3 (by rfl) ⟨802301, by rfl⟩ : syracuseStep 4278941 = 1604603) (by norm_num)
theorem B2852627 : Blo 1901435 2852627 := bstep (se 1 (by rfl) ⟨2139470, by rfl⟩ : syracuseStep 2852627 = 4278941) B4278941
theorem B1901751 : Blo 1901435 1901751 := bstep (se 1 (by rfl) ⟨1426313, by rfl⟩ : syracuseStep 1901751 = 2852627) B2852627
theorem B3209213 : Blo 1901435 3209213 := bbase (se 3 (by rfl) ⟨601727, by rfl⟩ : syracuseStep 3209213 = 1203455) (by norm_num)
theorem B2139475 : Blo 1901435 2139475 := bstep (se 1 (by rfl) ⟨1604606, by rfl⟩ : syracuseStep 2139475 = 3209213) B3209213
theorem B2852633 : Blo 1901435 2852633 := bstep (se 2 (by rfl) ⟨1069737, by rfl⟩ : syracuseStep 2852633 = 2139475) B2139475
theorem B1901755 : Blo 1901435 1901755 := bstep (se 1 (by rfl) ⟨1426316, by rfl⟩ : syracuseStep 1901755 = 2852633) B2852633
theorem B4061669 : Blo 1901435 4061669 := bbase (se 4 (by rfl) ⟨380781, by rfl⟩ : syracuseStep 4061669 = 761563) (by norm_num)
theorem B10831117 : Blo 1901435 10831117 := bstep (se 3 (by rfl) ⟨2030834, by rfl⟩ : syracuseStep 10831117 = 4061669) B4061669
theorem B14441489 : Blo 1901435 14441489 := bstep (se 2 (by rfl) ⟨5415558, by rfl⟩ : syracuseStep 14441489 = 10831117) B10831117
theorem B9627659 : Blo 1901435 9627659 := bstep (se 1 (by rfl) ⟨7220744, by rfl⟩ : syracuseStep 9627659 = 14441489) B14441489
theorem B6418439 : Blo 1901435 6418439 := bstep (se 1 (by rfl) ⟨4813829, by rfl⟩ : syracuseStep 6418439 = 9627659) B9627659
theorem B4278959 : Blo 1901435 4278959 := bstep (se 1 (by rfl) ⟨3209219, by rfl⟩ : syracuseStep 4278959 = 6418439) B6418439
theorem B2852639 : Blo 1901435 2852639 := bstep (se 1 (by rfl) ⟨2139479, by rfl⟩ : syracuseStep 2852639 = 4278959) B4278959
theorem B1901759 : Blo 1901435 1901759 := bstep (se 1 (by rfl) ⟨1426319, by rfl⟩ : syracuseStep 1901759 = 2852639) B2852639
theorem B2852645 : Blo 1901435 2852645 := bbase (se 4 (by rfl) ⟨267435, by rfl⟩ : syracuseStep 2852645 = 534871) (by norm_num)
theorem B1901763 : Blo 1901435 1901763 := bstep (se 1 (by rfl) ⟨1426322, by rfl⟩ : syracuseStep 1901763 = 2852645) B2852645
theorem B2406925 : Blo 1901435 2406925 := bbase (se 3 (by rfl) ⟨451298, by rfl⟩ : syracuseStep 2406925 = 902597) (by norm_num)
theorem B3209233 : Blo 1901435 3209233 := bstep (se 2 (by rfl) ⟨1203462, by rfl⟩ : syracuseStep 3209233 = 2406925) B2406925
theorem B4278977 : Blo 1901435 4278977 := bstep (se 2 (by rfl) ⟨1604616, by rfl⟩ : syracuseStep 4278977 = 3209233) B3209233
theorem B2852651 : Blo 1901435 2852651 := bstep (se 1 (by rfl) ⟨2139488, by rfl⟩ : syracuseStep 2852651 = 4278977) B4278977
theorem B1901767 : Blo 1901435 1901767 := bstep (se 1 (by rfl) ⟨1426325, by rfl⟩ : syracuseStep 1901767 = 2852651) B2852651
theorem B2139493 : Blo 1901435 2139493 := bbase (se 4 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 2139493 = 401155) (by norm_num)
theorem B2852657 : Blo 1901435 2852657 := bstep (se 2 (by rfl) ⟨1069746, by rfl⟩ : syracuseStep 2852657 = 2139493) B2139493
theorem B1901771 : Blo 1901435 1901771 := bstep (se 1 (by rfl) ⟨1426328, by rfl⟩ : syracuseStep 1901771 = 2852657) B2852657
theorem B5415605 : Blo 1901435 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B3610403 : Blo 1901435 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B2406935 : Blo 1901435 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B6418493 : Blo 1901435 6418493 := bstep (se 3 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 6418493 = 2406935) B2406935
theorem B4278995 : Blo 1901435 4278995 := bstep (se 1 (by rfl) ⟨3209246, by rfl⟩ : syracuseStep 4278995 = 6418493) B6418493
theorem B2852663 : Blo 1901435 2852663 := bstep (se 1 (by rfl) ⟨2139497, by rfl⟩ : syracuseStep 2852663 = 4278995) B4278995
theorem B1901775 : Blo 1901435 1901775 := bstep (se 1 (by rfl) ⟨1426331, by rfl⟩ : syracuseStep 1901775 = 2852663) B2852663
theorem B2852669 : Blo 1901435 2852669 := bbase (se 3 (by rfl) ⟨534875, by rfl⟩ : syracuseStep 2852669 = 1069751) (by norm_num)
theorem B1901779 : Blo 1901435 1901779 := bstep (se 1 (by rfl) ⟨1426334, by rfl⟩ : syracuseStep 1901779 = 2852669) B2852669
theorem B4279013 : Blo 1901435 4279013 := bbase (se 4 (by rfl) ⟨401157, by rfl⟩ : syracuseStep 4279013 = 802315) (by norm_num)
theorem B2852675 : Blo 1901435 2852675 := bstep (se 1 (by rfl) ⟨2139506, by rfl⟩ : syracuseStep 2852675 = 4279013) B4279013
theorem B1901783 : Blo 1901435 1901783 := bstep (se 1 (by rfl) ⟨1426337, by rfl⟩ : syracuseStep 1901783 = 2852675) B2852675
theorem B4813901 : Blo 1901435 4813901 := bbase (se 3 (by rfl) ⟨902606, by rfl⟩ : syracuseStep 4813901 = 1805213) (by norm_num)
theorem B3209267 : Blo 1901435 3209267 := bstep (se 1 (by rfl) ⟨2406950, by rfl⟩ : syracuseStep 3209267 = 4813901) B4813901
theorem B2139511 : Blo 1901435 2139511 := bstep (se 1 (by rfl) ⟨1604633, by rfl⟩ : syracuseStep 2139511 = 3209267) B3209267
theorem B2852681 : Blo 1901435 2852681 := bstep (se 2 (by rfl) ⟨1069755, by rfl⟩ : syracuseStep 2852681 = 2139511) B2139511
theorem B1901787 : Blo 1901435 1901787 := bstep (se 1 (by rfl) ⟨1426340, by rfl⟩ : syracuseStep 1901787 = 2852681) B2852681
theorem B2030869 : Blo 1901435 2030869 := bbase (se 6 (by rfl) ⟨47598, by rfl⟩ : syracuseStep 2030869 = 95197) (by norm_num)
theorem B2707825 : Blo 1901435 2707825 := bstep (se 2 (by rfl) ⟨1015434, by rfl⟩ : syracuseStep 2707825 = 2030869) B2030869
theorem B3610433 : Blo 1901435 3610433 := bstep (se 2 (by rfl) ⟨1353912, by rfl⟩ : syracuseStep 3610433 = 2707825) B2707825
theorem B9627821 : Blo 1901435 9627821 := bstep (se 3 (by rfl) ⟨1805216, by rfl⟩ : syracuseStep 9627821 = 3610433) B3610433
theorem B6418547 : Blo 1901435 6418547 := bstep (se 1 (by rfl) ⟨4813910, by rfl⟩ : syracuseStep 6418547 = 9627821) B9627821
theorem B4279031 : Blo 1901435 4279031 := bstep (se 1 (by rfl) ⟨3209273, by rfl⟩ : syracuseStep 4279031 = 6418547) B6418547
theorem B2852687 : Blo 1901435 2852687 := bstep (se 1 (by rfl) ⟨2139515, by rfl⟩ : syracuseStep 2852687 = 4279031) B4279031
theorem B1901791 : Blo 1901435 1901791 := bstep (se 1 (by rfl) ⟨1426343, by rfl⟩ : syracuseStep 1901791 = 2852687) B2852687
theorem B2852693 : Blo 1901435 2852693 := bbase (se 9 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 2852693 = 16715) (by norm_num)
theorem B1901795 : Blo 1901435 1901795 := bstep (se 1 (by rfl) ⟨1426346, by rfl⟩ : syracuseStep 1901795 = 2852693) B2852693
theorem B6854213 : Blo 1901435 6854213 := bbase (se 4 (by rfl) ⟨642582, by rfl⟩ : syracuseStep 6854213 = 1285165) (by norm_num)
theorem B4569475 : Blo 1901435 4569475 := bstep (se 1 (by rfl) ⟨3427106, by rfl⟩ : syracuseStep 4569475 = 6854213) B6854213
theorem B6092633 : Blo 1901435 6092633 := bstep (se 2 (by rfl) ⟨2284737, by rfl⟩ : syracuseStep 6092633 = 4569475) B4569475
theorem B4061755 : Blo 1901435 4061755 := bstep (se 1 (by rfl) ⟨3046316, by rfl⟩ : syracuseStep 4061755 = 6092633) B6092633
theorem B5415673 : Blo 1901435 5415673 := bstep (se 2 (by rfl) ⟨2030877, by rfl⟩ : syracuseStep 5415673 = 4061755) B4061755
theorem B7220897 : Blo 1901435 7220897 := bstep (se 2 (by rfl) ⟨2707836, by rfl⟩ : syracuseStep 7220897 = 5415673) B5415673
theorem B4813931 : Blo 1901435 4813931 := bstep (se 1 (by rfl) ⟨3610448, by rfl⟩ : syracuseStep 4813931 = 7220897) B7220897
theorem B3209287 : Blo 1901435 3209287 := bstep (se 1 (by rfl) ⟨2406965, by rfl⟩ : syracuseStep 3209287 = 4813931) B4813931
theorem B4279049 : Blo 1901435 4279049 := bstep (se 2 (by rfl) ⟨1604643, by rfl⟩ : syracuseStep 4279049 = 3209287) B3209287
theorem B2852699 : Blo 1901435 2852699 := bstep (se 1 (by rfl) ⟨2139524, by rfl⟩ : syracuseStep 2852699 = 4279049) B4279049
theorem B1901799 : Blo 1901435 1901799 := bstep (se 1 (by rfl) ⟨1426349, by rfl⟩ : syracuseStep 1901799 = 2852699) B2852699
theorem B2139529 : Blo 1901435 2139529 := bbase (se 2 (by rfl) ⟨802323, by rfl⟩ : syracuseStep 2139529 = 1604647) (by norm_num)
theorem B2852705 : Blo 1901435 2852705 := bstep (se 2 (by rfl) ⟨1069764, by rfl⟩ : syracuseStep 2852705 = 2139529) B2139529
theorem B1901803 : Blo 1901435 1901803 := bstep (se 1 (by rfl) ⟨1426352, by rfl⟩ : syracuseStep 1901803 = 2852705) B2852705
theorem B16468757 : Blo 1901435 16468757 := bbase (se 6 (by rfl) ⟨385986, by rfl⟩ : syracuseStep 16468757 = 771973) (by norm_num)
theorem B10979171 : Blo 1901435 10979171 := bstep (se 1 (by rfl) ⟨8234378, by rfl⟩ : syracuseStep 10979171 = 16468757) B16468757
theorem B7319447 : Blo 1901435 7319447 := bstep (se 1 (by rfl) ⟨5489585, by rfl⟩ : syracuseStep 7319447 = 10979171) B10979171
theorem B4879631 : Blo 1901435 4879631 := bstep (se 1 (by rfl) ⟨3659723, by rfl⟩ : syracuseStep 4879631 = 7319447) B7319447
theorem B3253087 : Blo 1901435 3253087 := bstep (se 1 (by rfl) ⟨2439815, by rfl⟩ : syracuseStep 3253087 = 4879631) B4879631
theorem B4337449 : Blo 1901435 4337449 := bstep (se 2 (by rfl) ⟨1626543, by rfl⟩ : syracuseStep 4337449 = 3253087) B3253087
theorem B23133061 : Blo 1901435 23133061 := bstep (se 4 (by rfl) ⟨2168724, by rfl⟩ : syracuseStep 23133061 = 4337449) B4337449
theorem B30844081 : Blo 1901435 30844081 := bstep (se 2 (by rfl) ⟨11566530, by rfl⟩ : syracuseStep 30844081 = 23133061) B23133061
theorem B41125441 : Blo 1901435 41125441 := bstep (se 2 (by rfl) ⟨15422040, by rfl⟩ : syracuseStep 41125441 = 30844081) B30844081
theorem B54833921 : Blo 1901435 54833921 := bstep (se 2 (by rfl) ⟨20562720, by rfl⟩ : syracuseStep 54833921 = 41125441) B41125441
theorem B36555947 : Blo 1901435 36555947 := bstep (se 1 (by rfl) ⟨27416960, by rfl⟩ : syracuseStep 36555947 = 54833921) B54833921
theorem B24370631 : Blo 1901435 24370631 := bstep (se 1 (by rfl) ⟨18277973, by rfl⟩ : syracuseStep 24370631 = 36555947) B36555947
theorem B16247087 : Blo 1901435 16247087 := bstep (se 1 (by rfl) ⟨12185315, by rfl⟩ : syracuseStep 16247087 = 24370631) B24370631
theorem B10831391 : Blo 1901435 10831391 := bstep (se 1 (by rfl) ⟨8123543, by rfl⟩ : syracuseStep 10831391 = 16247087) B16247087
theorem B7220927 : Blo 1901435 7220927 := bstep (se 1 (by rfl) ⟨5415695, by rfl⟩ : syracuseStep 7220927 = 10831391) B10831391
theorem B4813951 : Blo 1901435 4813951 := bstep (se 1 (by rfl) ⟨3610463, by rfl⟩ : syracuseStep 4813951 = 7220927) B7220927
theorem B6418601 : Blo 1901435 6418601 := bstep (se 2 (by rfl) ⟨2406975, by rfl⟩ : syracuseStep 6418601 = 4813951) B4813951
theorem B4279067 : Blo 1901435 4279067 := bstep (se 1 (by rfl) ⟨3209300, by rfl⟩ : syracuseStep 4279067 = 6418601) B6418601
theorem B2852711 : Blo 1901435 2852711 := bstep (se 1 (by rfl) ⟨2139533, by rfl⟩ : syracuseStep 2852711 = 4279067) B4279067
theorem B1901807 : Blo 1901435 1901807 := bstep (se 1 (by rfl) ⟨1426355, by rfl⟩ : syracuseStep 1901807 = 2852711) B2852711
theorem B2852717 : Blo 1901435 2852717 := bbase (se 3 (by rfl) ⟨534884, by rfl⟩ : syracuseStep 2852717 = 1069769) (by norm_num)
theorem B1901811 : Blo 1901435 1901811 := bstep (se 1 (by rfl) ⟨1426358, by rfl⟩ : syracuseStep 1901811 = 2852717) B2852717
theorem B4279085 : Blo 1901435 4279085 := bbase (se 3 (by rfl) ⟨802328, by rfl⟩ : syracuseStep 4279085 = 1604657) (by norm_num)
theorem B2852723 : Blo 1901435 2852723 := bstep (se 1 (by rfl) ⟨2139542, by rfl⟩ : syracuseStep 2852723 = 4279085) B4279085
theorem B1901815 : Blo 1901435 1901815 := bstep (se 1 (by rfl) ⟨1426361, by rfl⟩ : syracuseStep 1901815 = 2852723) B2852723
theorem B3046349 : Blo 1901435 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B8123597 : Blo 1901435 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B5415731 : Blo 1901435 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B3610487 : Blo 1901435 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B2406991 : Blo 1901435 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B3209321 : Blo 1901435 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B2139547 : Blo 1901435 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B2852729 : Blo 1901435 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B1901819 : Blo 1901435 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B5564533 : Blo 1901435 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B7419377 : Blo 1901435 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B19785005 : Blo 1901435 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B13190003 : Blo 1901435 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B8793335 : Blo 1901435 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B5862223 : Blo 1901435 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B7816297 : Blo 1901435 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B10421729 : Blo 1901435 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B6947819 : Blo 1901435 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B4631879 : Blo 1901435 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B3087919 : Blo 1901435 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B4117225 : Blo 1901435 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B5489633 : Blo 1901435 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B3659755 : Blo 1901435 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B4879673 : Blo 1901435 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B3253115 : Blo 1901435 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B2168743 : Blo 1901435 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B2891657 : Blo 1901435 2891657 := bstep (se 2 (by rfl) ⟨1084371, by rfl⟩ : syracuseStep 2891657 = 2168743) B2168743
theorem B7711085 : Blo 1901435 7711085 := bstep (se 3 (by rfl) ⟨1445828, by rfl⟩ : syracuseStep 7711085 = 2891657) B2891657
theorem B20562893 : Blo 1901435 20562893 := bstep (se 3 (by rfl) ⟨3855542, by rfl⟩ : syracuseStep 20562893 = 7711085) B7711085
theorem B13708595 : Blo 1901435 13708595 := bstep (se 1 (by rfl) ⟨10281446, by rfl⟩ : syracuseStep 13708595 = 20562893) B20562893
theorem B9139063 : Blo 1901435 9139063 := bstep (se 1 (by rfl) ⟨6854297, by rfl⟩ : syracuseStep 9139063 = 13708595) B13708595
theorem B12185417 : Blo 1901435 12185417 := bstep (se 2 (by rfl) ⟨4569531, by rfl⟩ : syracuseStep 12185417 = 9139063) B9139063
theorem B32494445 : Blo 1901435 32494445 := bstep (se 3 (by rfl) ⟨6092708, by rfl⟩ : syracuseStep 32494445 = 12185417) B12185417
theorem B21662963 : Blo 1901435 21662963 := bstep (se 1 (by rfl) ⟨16247222, by rfl⟩ : syracuseStep 21662963 = 32494445) B32494445
theorem B14441975 : Blo 1901435 14441975 := bstep (se 1 (by rfl) ⟨10831481, by rfl⟩ : syracuseStep 14441975 = 21662963) B21662963
theorem B9627983 : Blo 1901435 9627983 := bstep (se 1 (by rfl) ⟨7220987, by rfl⟩ : syracuseStep 9627983 = 14441975) B14441975
theorem B6418655 : Blo 1901435 6418655 := bstep (se 1 (by rfl) ⟨4813991, by rfl⟩ : syracuseStep 6418655 = 9627983) B9627983
theorem B4279103 : Blo 1901435 4279103 := bstep (se 1 (by rfl) ⟨3209327, by rfl⟩ : syracuseStep 4279103 = 6418655) B6418655
theorem B2852735 : Blo 1901435 2852735 := bstep (se 1 (by rfl) ⟨2139551, by rfl⟩ : syracuseStep 2852735 = 4279103) B4279103
theorem B1901823 : Blo 1901435 1901823 := bstep (se 1 (by rfl) ⟨1426367, by rfl⟩ : syracuseStep 1901823 = 2852735) B2852735
theorem B2852741 : Blo 1901435 2852741 := bbase (se 4 (by rfl) ⟨267444, by rfl⟩ : syracuseStep 2852741 = 534889) (by norm_num)
theorem B1901827 : Blo 1901435 1901827 := bstep (se 1 (by rfl) ⟨1426370, by rfl⟩ : syracuseStep 1901827 = 2852741) B2852741
theorem B3209341 : Blo 1901435 3209341 := bbase (se 3 (by rfl) ⟨601751, by rfl⟩ : syracuseStep 3209341 = 1203503) (by norm_num)
theorem B4279121 : Blo 1901435 4279121 := bstep (se 2 (by rfl) ⟨1604670, by rfl⟩ : syracuseStep 4279121 = 3209341) B3209341
theorem B2852747 : Blo 1901435 2852747 := bstep (se 1 (by rfl) ⟨2139560, by rfl⟩ : syracuseStep 2852747 = 4279121) B4279121
theorem B1901831 : Blo 1901435 1901831 := bstep (se 1 (by rfl) ⟨1426373, by rfl⟩ : syracuseStep 1901831 = 2852747) B2852747
theorem B2139565 : Blo 1901435 2139565 := bbase (se 3 (by rfl) ⟨401168, by rfl⟩ : syracuseStep 2139565 = 802337) (by norm_num)
theorem B2852753 : Blo 1901435 2852753 := bstep (se 2 (by rfl) ⟨1069782, by rfl⟩ : syracuseStep 2852753 = 2139565) B2139565
theorem B1901835 : Blo 1901435 1901835 := bstep (se 1 (by rfl) ⟨1426376, by rfl⟩ : syracuseStep 1901835 = 2852753) B2852753
theorem B6418709 : Blo 1901435 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B4279139 : Blo 1901435 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B2852759 : Blo 1901435 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B1901839 : Blo 1901435 1901839 := bstep (se 1 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 1901839 = 2852759) B2852759
theorem B2852765 : Blo 1901435 2852765 := bbase (se 3 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 2852765 = 1069787) (by norm_num)
theorem B1901843 : Blo 1901435 1901843 := bstep (se 1 (by rfl) ⟨1426382, by rfl⟩ : syracuseStep 1901843 = 2852765) B2852765
theorem B4279157 : Blo 1901435 4279157 := bbase (se 5 (by rfl) ⟨200585, by rfl⟩ : syracuseStep 4279157 = 401171) (by norm_num)
theorem B2852771 : Blo 1901435 2852771 := bstep (se 1 (by rfl) ⟨2139578, by rfl⟩ : syracuseStep 2852771 = 4279157) B4279157
theorem B1901847 : Blo 1901435 1901847 := bstep (se 1 (by rfl) ⟨1426385, by rfl⟩ : syracuseStep 1901847 = 2852771) B2852771
theorem B7042709 : Blo 1901435 7042709 := bbase (se 6 (by rfl) ⟨165063, by rfl⟩ : syracuseStep 7042709 = 330127) (by norm_num)
theorem B18780557 : Blo 1901435 18780557 := bstep (se 3 (by rfl) ⟨3521354, by rfl⟩ : syracuseStep 18780557 = 7042709) B7042709
theorem B50081485 : Blo 1901435 50081485 := bstep (se 3 (by rfl) ⟨9390278, by rfl⟩ : syracuseStep 50081485 = 18780557) B18780557
theorem B66775313 : Blo 1901435 66775313 := bstep (se 2 (by rfl) ⟨25040742, by rfl⟩ : syracuseStep 66775313 = 50081485) B50081485
theorem B44516875 : Blo 1901435 44516875 := bstep (se 1 (by rfl) ⟨33387656, by rfl⟩ : syracuseStep 44516875 = 66775313) B66775313
theorem B59355833 : Blo 1901435 59355833 := bstep (se 2 (by rfl) ⟨22258437, by rfl⟩ : syracuseStep 59355833 = 44516875) B44516875
theorem B633128885 : Blo 1901435 633128885 := bstep (se 5 (by rfl) ⟨29677916, by rfl⟩ : syracuseStep 633128885 = 59355833) B59355833
theorem B422085923 : Blo 1901435 422085923 := bstep (se 1 (by rfl) ⟨316564442, by rfl⟩ : syracuseStep 422085923 = 633128885) B633128885
theorem B281390615 : Blo 1901435 281390615 := bstep (se 1 (by rfl) ⟨211042961, by rfl⟩ : syracuseStep 281390615 = 422085923) B422085923
theorem B187593743 : Blo 1901435 187593743 := bstep (se 1 (by rfl) ⟨140695307, by rfl⟩ : syracuseStep 187593743 = 281390615) B281390615
theorem B500249981 : Blo 1901435 500249981 := bstep (se 3 (by rfl) ⟨93796871, by rfl⟩ : syracuseStep 500249981 = 187593743) B187593743
theorem B333499987 : Blo 1901435 333499987 := bstep (se 1 (by rfl) ⟨250124990, by rfl⟩ : syracuseStep 333499987 = 500249981) B500249981
theorem B1778666597 : Blo 1901435 1778666597 := bstep (se 4 (by rfl) ⟨166749993, by rfl⟩ : syracuseStep 1778666597 = 333499987) B333499987
theorem B1185777731 : Blo 1901435 1185777731 := bstep (se 1 (by rfl) ⟨889333298, by rfl⟩ : syracuseStep 1185777731 = 1778666597) B1778666597
theorem B790518487 : Blo 1901435 790518487 := bstep (se 1 (by rfl) ⟨592888865, by rfl⟩ : syracuseStep 790518487 = 1185777731) B1185777731
theorem B1054024649 : Blo 1901435 1054024649 := bstep (se 2 (by rfl) ⟨395259243, by rfl⟩ : syracuseStep 1054024649 = 790518487) B790518487
theorem B702683099 : Blo 1901435 702683099 := bstep (se 1 (by rfl) ⟨527012324, by rfl⟩ : syracuseStep 702683099 = 1054024649) B1054024649
theorem B468455399 : Blo 1901435 468455399 := bstep (se 1 (by rfl) ⟨351341549, by rfl⟩ : syracuseStep 468455399 = 702683099) B702683099
theorem B312303599 : Blo 1901435 312303599 := bstep (se 1 (by rfl) ⟨234227699, by rfl⟩ : syracuseStep 312303599 = 468455399) B468455399
theorem B208202399 : Blo 1901435 208202399 := bstep (se 1 (by rfl) ⟨156151799, by rfl⟩ : syracuseStep 208202399 = 312303599) B312303599
theorem B138801599 : Blo 1901435 138801599 := bstep (se 1 (by rfl) ⟨104101199, by rfl⟩ : syracuseStep 138801599 = 208202399) B208202399
theorem B92534399 : Blo 1901435 92534399 := bstep (se 1 (by rfl) ⟨69400799, by rfl⟩ : syracuseStep 92534399 = 138801599) B138801599
theorem B61689599 : Blo 1901435 61689599 := bstep (se 1 (by rfl) ⟨46267199, by rfl⟩ : syracuseStep 61689599 = 92534399) B92534399
theorem B41126399 : Blo 1901435 41126399 := bstep (se 1 (by rfl) ⟨30844799, by rfl⟩ : syracuseStep 41126399 = 61689599) B61689599
theorem B27417599 : Blo 1901435 27417599 := bstep (se 1 (by rfl) ⟨20563199, by rfl⟩ : syracuseStep 27417599 = 41126399) B41126399
theorem B18278399 : Blo 1901435 18278399 := bstep (se 1 (by rfl) ⟨13708799, by rfl⟩ : syracuseStep 18278399 = 27417599) B27417599
theorem B12185599 : Blo 1901435 12185599 := bstep (se 1 (by rfl) ⟨9139199, by rfl⟩ : syracuseStep 12185599 = 18278399) B18278399
theorem B16247465 : Blo 1901435 16247465 := bstep (se 2 (by rfl) ⟨6092799, by rfl⟩ : syracuseStep 16247465 = 12185599) B12185599
theorem B10831643 : Blo 1901435 10831643 := bstep (se 1 (by rfl) ⟨8123732, by rfl⟩ : syracuseStep 10831643 = 16247465) B16247465
theorem B7221095 : Blo 1901435 7221095 := bstep (se 1 (by rfl) ⟨5415821, by rfl⟩ : syracuseStep 7221095 = 10831643) B10831643
theorem B4814063 : Blo 1901435 4814063 := bstep (se 1 (by rfl) ⟨3610547, by rfl⟩ : syracuseStep 4814063 = 7221095) B7221095
theorem B3209375 : Blo 1901435 3209375 := bstep (se 1 (by rfl) ⟨2407031, by rfl⟩ : syracuseStep 3209375 = 4814063) B4814063
theorem B2139583 : Blo 1901435 2139583 := bstep (se 1 (by rfl) ⟨1604687, by rfl⟩ : syracuseStep 2139583 = 3209375) B3209375
theorem B2852777 : Blo 1901435 2852777 := bstep (se 2 (by rfl) ⟨1069791, by rfl⟩ : syracuseStep 2852777 = 2139583) B2139583
theorem B1901851 : Blo 1901435 1901851 := bstep (se 1 (by rfl) ⟨1426388, by rfl⟩ : syracuseStep 1901851 = 2852777) B2852777
theorem B7221109 : Blo 1901435 7221109 := bbase (se 5 (by rfl) ⟨338489, by rfl⟩ : syracuseStep 7221109 = 676979) (by norm_num)
theorem B9628145 : Blo 1901435 9628145 := bstep (se 2 (by rfl) ⟨3610554, by rfl⟩ : syracuseStep 9628145 = 7221109) B7221109
theorem B6418763 : Blo 1901435 6418763 := bstep (se 1 (by rfl) ⟨4814072, by rfl⟩ : syracuseStep 6418763 = 9628145) B9628145
theorem B4279175 : Blo 1901435 4279175 := bstep (se 1 (by rfl) ⟨3209381, by rfl⟩ : syracuseStep 4279175 = 6418763) B6418763
theorem B2852783 : Blo 1901435 2852783 := bstep (se 1 (by rfl) ⟨2139587, by rfl⟩ : syracuseStep 2852783 = 4279175) B4279175
theorem B1901855 : Blo 1901435 1901855 := bstep (se 1 (by rfl) ⟨1426391, by rfl⟩ : syracuseStep 1901855 = 2852783) B2852783
theorem B2852789 : Blo 1901435 2852789 := bbase (se 5 (by rfl) ⟨133724, by rfl⟩ : syracuseStep 2852789 = 267449) (by norm_num)
theorem B1901859 : Blo 1901435 1901859 := bstep (se 1 (by rfl) ⟨1426394, by rfl⟩ : syracuseStep 1901859 = 2852789) B2852789
theorem B4814093 : Blo 1901435 4814093 := bbase (se 3 (by rfl) ⟨902642, by rfl⟩ : syracuseStep 4814093 = 1805285) (by norm_num)
theorem B3209395 : Blo 1901435 3209395 := bstep (se 1 (by rfl) ⟨2407046, by rfl⟩ : syracuseStep 3209395 = 4814093) B4814093
theorem B4279193 : Blo 1901435 4279193 := bstep (se 2 (by rfl) ⟨1604697, by rfl⟩ : syracuseStep 4279193 = 3209395) B3209395
theorem B2852795 : Blo 1901435 2852795 := bstep (se 1 (by rfl) ⟨2139596, by rfl⟩ : syracuseStep 2852795 = 4279193) B4279193
theorem B1901863 : Blo 1901435 1901863 := bstep (se 1 (by rfl) ⟨1426397, by rfl⟩ : syracuseStep 1901863 = 2852795) B2852795
theorem B2139601 : Blo 1901435 2139601 := bbase (se 2 (by rfl) ⟨802350, by rfl⟩ : syracuseStep 2139601 = 1604701) (by norm_num)
theorem B2852801 : Blo 1901435 2852801 := bstep (se 2 (by rfl) ⟨1069800, by rfl⟩ : syracuseStep 2852801 = 2139601) B2139601
theorem B1901867 : Blo 1901435 1901867 := bstep (se 1 (by rfl) ⟨1426400, by rfl⟩ : syracuseStep 1901867 = 2852801) B2852801
theorem B4061909 : Blo 1901435 4061909 := bbase (se 7 (by rfl) ⟨47600, by rfl⟩ : syracuseStep 4061909 = 95201) (by norm_num)
theorem B2707939 : Blo 1901435 2707939 := bstep (se 1 (by rfl) ⟨2030954, by rfl⟩ : syracuseStep 2707939 = 4061909) B4061909
theorem B3610585 : Blo 1901435 3610585 := bstep (se 2 (by rfl) ⟨1353969, by rfl⟩ : syracuseStep 3610585 = 2707939) B2707939
theorem B4814113 : Blo 1901435 4814113 := bstep (se 2 (by rfl) ⟨1805292, by rfl⟩ : syracuseStep 4814113 = 3610585) B3610585
theorem B6418817 : Blo 1901435 6418817 := bstep (se 2 (by rfl) ⟨2407056, by rfl⟩ : syracuseStep 6418817 = 4814113) B4814113
theorem B4279211 : Blo 1901435 4279211 := bstep (se 1 (by rfl) ⟨3209408, by rfl⟩ : syracuseStep 4279211 = 6418817) B6418817
theorem B2852807 : Blo 1901435 2852807 := bstep (se 1 (by rfl) ⟨2139605, by rfl⟩ : syracuseStep 2852807 = 4279211) B4279211
theorem B1901871 : Blo 1901435 1901871 := bstep (se 1 (by rfl) ⟨1426403, by rfl⟩ : syracuseStep 1901871 = 2852807) B2852807
theorem B2852813 : Blo 1901435 2852813 := bbase (se 3 (by rfl) ⟨534902, by rfl⟩ : syracuseStep 2852813 = 1069805) (by norm_num)
theorem B1901875 : Blo 1901435 1901875 := bstep (se 1 (by rfl) ⟨1426406, by rfl⟩ : syracuseStep 1901875 = 2852813) B2852813
theorem B4279229 : Blo 1901435 4279229 := bbase (se 3 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 4279229 = 1604711) (by norm_num)
theorem B2852819 : Blo 1901435 2852819 := bstep (se 1 (by rfl) ⟨2139614, by rfl⟩ : syracuseStep 2852819 = 4279229) B4279229
theorem B1901879 : Blo 1901435 1901879 := bstep (se 1 (by rfl) ⟨1426409, by rfl⟩ : syracuseStep 1901879 = 2852819) B2852819
theorem B3209429 : Blo 1901435 3209429 := bbase (se 7 (by rfl) ⟨37610, by rfl⟩ : syracuseStep 3209429 = 75221) (by norm_num)
theorem B2139619 : Blo 1901435 2139619 := bstep (se 1 (by rfl) ⟨1604714, by rfl⟩ : syracuseStep 2139619 = 3209429) B3209429
theorem B2852825 : Blo 1901435 2852825 := bstep (se 2 (by rfl) ⟨1069809, by rfl⟩ : syracuseStep 2852825 = 2139619) B2139619
theorem B1901883 : Blo 1901435 1901883 := bstep (se 1 (by rfl) ⟨1426412, by rfl⟩ : syracuseStep 1901883 = 2852825) B2852825
theorem B1927837 : Blo 1901435 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B2570449 : Blo 1901435 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B3427265 : Blo 1901435 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B2284843 : Blo 1901435 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B3046457 : Blo 1901435 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B8123885 : Blo 1901435 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B5415923 : Blo 1901435 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B14442461 : Blo 1901435 14442461 := bstep (se 3 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 14442461 = 5415923) B5415923
theorem B9628307 : Blo 1901435 9628307 := bstep (se 1 (by rfl) ⟨7221230, by rfl⟩ : syracuseStep 9628307 = 14442461) B14442461
theorem B6418871 : Blo 1901435 6418871 := bstep (se 1 (by rfl) ⟨4814153, by rfl⟩ : syracuseStep 6418871 = 9628307) B9628307
theorem B4279247 : Blo 1901435 4279247 := bstep (se 1 (by rfl) ⟨3209435, by rfl⟩ : syracuseStep 4279247 = 6418871) B6418871
theorem B2852831 : Blo 1901435 2852831 := bstep (se 1 (by rfl) ⟨2139623, by rfl⟩ : syracuseStep 2852831 = 4279247) B4279247
theorem B1901887 : Blo 1901435 1901887 := bstep (se 1 (by rfl) ⟨1426415, by rfl⟩ : syracuseStep 1901887 = 2852831) B2852831
theorem B2852837 : Blo 1901435 2852837 := bbase (se 4 (by rfl) ⟨267453, by rfl⟩ : syracuseStep 2852837 = 534907) (by norm_num)
theorem B1901891 : Blo 1901435 1901891 := bstep (se 1 (by rfl) ⟨1426418, by rfl⟩ : syracuseStep 1901891 = 2852837) B2852837
theorem B2284853 : Blo 1901435 2284853 := bbase (se 5 (by rfl) ⟨107102, by rfl⟩ : syracuseStep 2284853 = 214205) (by norm_num)
theorem B6092941 : Blo 1901435 6092941 := bstep (se 3 (by rfl) ⟨1142426, by rfl⟩ : syracuseStep 6092941 = 2284853) B2284853
theorem B8123921 : Blo 1901435 8123921 := bstep (se 2 (by rfl) ⟨3046470, by rfl⟩ : syracuseStep 8123921 = 6092941) B6092941
theorem B5415947 : Blo 1901435 5415947 := bstep (se 1 (by rfl) ⟨4061960, by rfl⟩ : syracuseStep 5415947 = 8123921) B8123921
theorem B3610631 : Blo 1901435 3610631 := bstep (se 1 (by rfl) ⟨2707973, by rfl⟩ : syracuseStep 3610631 = 5415947) B5415947
theorem B2407087 : Blo 1901435 2407087 := bstep (se 1 (by rfl) ⟨1805315, by rfl⟩ : syracuseStep 2407087 = 3610631) B3610631
theorem B3209449 : Blo 1901435 3209449 := bstep (se 2 (by rfl) ⟨1203543, by rfl⟩ : syracuseStep 3209449 = 2407087) B2407087
theorem B4279265 : Blo 1901435 4279265 := bstep (se 2 (by rfl) ⟨1604724, by rfl⟩ : syracuseStep 4279265 = 3209449) B3209449
theorem B2852843 : Blo 1901435 2852843 := bstep (se 1 (by rfl) ⟨2139632, by rfl⟩ : syracuseStep 2852843 = 4279265) B4279265
theorem B1901895 : Blo 1901435 1901895 := bstep (se 1 (by rfl) ⟨1426421, by rfl⟩ : syracuseStep 1901895 = 2852843) B2852843
theorem B2139637 : Blo 1901435 2139637 := bbase (se 5 (by rfl) ⟨100295, by rfl⟩ : syracuseStep 2139637 = 200591) (by norm_num)
theorem B2852849 : Blo 1901435 2852849 := bstep (se 2 (by rfl) ⟨1069818, by rfl⟩ : syracuseStep 2852849 = 2139637) B2139637
theorem B1901899 : Blo 1901435 1901899 := bstep (se 1 (by rfl) ⟨1426424, by rfl⟩ : syracuseStep 1901899 = 2852849) B2852849
theorem B2407097 : Blo 1901435 2407097 := bbase (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) (by norm_num)
theorem B6418925 : Blo 1901435 6418925 := bstep (se 3 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 6418925 = 2407097) B2407097
theorem B4279283 : Blo 1901435 4279283 := bstep (se 1 (by rfl) ⟨3209462, by rfl⟩ : syracuseStep 4279283 = 6418925) B6418925
theorem B2852855 : Blo 1901435 2852855 := bstep (se 1 (by rfl) ⟨2139641, by rfl⟩ : syracuseStep 2852855 = 4279283) B4279283
theorem B1901903 : Blo 1901435 1901903 := bstep (se 1 (by rfl) ⟨1426427, by rfl⟩ : syracuseStep 1901903 = 2852855) B2852855
theorem B2852861 : Blo 1901435 2852861 := bbase (se 3 (by rfl) ⟨534911, by rfl⟩ : syracuseStep 2852861 = 1069823) (by norm_num)
theorem B1901907 : Blo 1901435 1901907 := bstep (se 1 (by rfl) ⟨1426430, by rfl⟩ : syracuseStep 1901907 = 2852861) B2852861
theorem B4279301 : Blo 1901435 4279301 := bbase (se 4 (by rfl) ⟨401184, by rfl⟩ : syracuseStep 4279301 = 802369) (by norm_num)
theorem B2852867 : Blo 1901435 2852867 := bstep (se 1 (by rfl) ⟨2139650, by rfl⟩ : syracuseStep 2852867 = 4279301) B4279301
theorem B1901911 : Blo 1901435 1901911 := bstep (se 1 (by rfl) ⟨1426433, by rfl⟩ : syracuseStep 1901911 = 2852867) B2852867
theorem B3610669 : Blo 1901435 3610669 := bbase (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) (by norm_num)
theorem B4814225 : Blo 1901435 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B3209483 : Blo 1901435 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B2139655 : Blo 1901435 2139655 := bstep (se 1 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 2139655 = 3209483) B3209483
theorem B2852873 : Blo 1901435 2852873 := bstep (se 2 (by rfl) ⟨1069827, by rfl⟩ : syracuseStep 2852873 = 2139655) B2139655
theorem B1901915 : Blo 1901435 1901915 := bstep (se 1 (by rfl) ⟨1426436, by rfl⟩ : syracuseStep 1901915 = 2852873) B2852873
theorem B9628469 : Blo 1901435 9628469 := bbase (se 5 (by rfl) ⟨451334, by rfl⟩ : syracuseStep 9628469 = 902669) (by norm_num)
theorem B6418979 : Blo 1901435 6418979 := bstep (se 1 (by rfl) ⟨4814234, by rfl⟩ : syracuseStep 6418979 = 9628469) B9628469
theorem B4279319 : Blo 1901435 4279319 := bstep (se 1 (by rfl) ⟨3209489, by rfl⟩ : syracuseStep 4279319 = 6418979) B6418979
theorem B2852879 : Blo 1901435 2852879 := bstep (se 1 (by rfl) ⟨2139659, by rfl⟩ : syracuseStep 2852879 = 4279319) B4279319
theorem B1901919 : Blo 1901435 1901919 := bstep (se 1 (by rfl) ⟨1426439, by rfl⟩ : syracuseStep 1901919 = 2852879) B2852879
theorem B2852885 : Blo 1901435 2852885 := bbase (se 6 (by rfl) ⟨66864, by rfl⟩ : syracuseStep 2852885 = 133729) (by norm_num)
theorem B1901923 : Blo 1901435 1901923 := bstep (se 1 (by rfl) ⟨1426442, by rfl⟩ : syracuseStep 1901923 = 2852885) B2852885
theorem B4337725 : Blo 1901435 4337725 := bbase (se 3 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 4337725 = 1626647) (by norm_num)
theorem B5783633 : Blo 1901435 5783633 := bstep (se 2 (by rfl) ⟨2168862, by rfl⟩ : syracuseStep 5783633 = 4337725) B4337725
theorem B3855755 : Blo 1901435 3855755 := bstep (se 1 (by rfl) ⟨2891816, by rfl⟩ : syracuseStep 3855755 = 5783633) B5783633
theorem B2570503 : Blo 1901435 2570503 := bstep (se 1 (by rfl) ⟨1927877, by rfl⟩ : syracuseStep 2570503 = 3855755) B3855755
theorem B3427337 : Blo 1901435 3427337 := bstep (se 2 (by rfl) ⟨1285251, by rfl⟩ : syracuseStep 3427337 = 2570503) B2570503
theorem B2284891 : Blo 1901435 2284891 := bstep (se 1 (by rfl) ⟨1713668, by rfl⟩ : syracuseStep 2284891 = 3427337) B3427337
theorem B12186085 : Blo 1901435 12186085 := bstep (se 4 (by rfl) ⟨1142445, by rfl⟩ : syracuseStep 12186085 = 2284891) B2284891
theorem B16248113 : Blo 1901435 16248113 := bstep (se 2 (by rfl) ⟨6093042, by rfl⟩ : syracuseStep 16248113 = 12186085) B12186085
theorem B10832075 : Blo 1901435 10832075 := bstep (se 1 (by rfl) ⟨8124056, by rfl⟩ : syracuseStep 10832075 = 16248113) B16248113
theorem B7221383 : Blo 1901435 7221383 := bstep (se 1 (by rfl) ⟨5416037, by rfl⟩ : syracuseStep 7221383 = 10832075) B10832075
theorem B4814255 : Blo 1901435 4814255 := bstep (se 1 (by rfl) ⟨3610691, by rfl⟩ : syracuseStep 4814255 = 7221383) B7221383
theorem B3209503 : Blo 1901435 3209503 := bstep (se 1 (by rfl) ⟨2407127, by rfl⟩ : syracuseStep 3209503 = 4814255) B4814255
theorem B4279337 : Blo 1901435 4279337 := bstep (se 2 (by rfl) ⟨1604751, by rfl⟩ : syracuseStep 4279337 = 3209503) B3209503
theorem B2852891 : Blo 1901435 2852891 := bstep (se 1 (by rfl) ⟨2139668, by rfl⟩ : syracuseStep 2852891 = 4279337) B4279337
theorem B1901927 : Blo 1901435 1901927 := bstep (se 1 (by rfl) ⟨1426445, by rfl⟩ : syracuseStep 1901927 = 2852891) B2852891
theorem B2139673 : Blo 1901435 2139673 := bbase (se 2 (by rfl) ⟨802377, by rfl⟩ : syracuseStep 2139673 = 1604755) (by norm_num)
theorem B2852897 : Blo 1901435 2852897 := bstep (se 2 (by rfl) ⟨1069836, by rfl⟩ : syracuseStep 2852897 = 2139673) B2139673
theorem B1901931 : Blo 1901435 1901931 := bstep (se 1 (by rfl) ⟨1426448, by rfl⟩ : syracuseStep 1901931 = 2852897) B2852897
theorem B7221413 : Blo 1901435 7221413 := bbase (se 4 (by rfl) ⟨677007, by rfl⟩ : syracuseStep 7221413 = 1354015) (by norm_num)
theorem B4814275 : Blo 1901435 4814275 := bstep (se 1 (by rfl) ⟨3610706, by rfl⟩ : syracuseStep 4814275 = 7221413) B7221413
theorem B6419033 : Blo 1901435 6419033 := bstep (se 2 (by rfl) ⟨2407137, by rfl⟩ : syracuseStep 6419033 = 4814275) B4814275
theorem B4279355 : Blo 1901435 4279355 := bstep (se 1 (by rfl) ⟨3209516, by rfl⟩ : syracuseStep 4279355 = 6419033) B6419033
theorem B2852903 : Blo 1901435 2852903 := bstep (se 1 (by rfl) ⟨2139677, by rfl⟩ : syracuseStep 2852903 = 4279355) B4279355
theorem B1901935 : Blo 1901435 1901935 := bstep (se 1 (by rfl) ⟨1426451, by rfl⟩ : syracuseStep 1901935 = 2852903) B2852903
theorem B2852909 : Blo 1901435 2852909 := bbase (se 3 (by rfl) ⟨534920, by rfl⟩ : syracuseStep 2852909 = 1069841) (by norm_num)
theorem B1901939 : Blo 1901435 1901939 := bstep (se 1 (by rfl) ⟨1426454, by rfl⟩ : syracuseStep 1901939 = 2852909) B2852909
theorem B4279373 : Blo 1901435 4279373 := bbase (se 3 (by rfl) ⟨802382, by rfl⟩ : syracuseStep 4279373 = 1604765) (by norm_num)
theorem B2852915 : Blo 1901435 2852915 := bstep (se 1 (by rfl) ⟨2139686, by rfl⟩ : syracuseStep 2852915 = 4279373) B4279373
theorem B1901943 : Blo 1901435 1901943 := bstep (se 1 (by rfl) ⟨1426457, by rfl⟩ : syracuseStep 1901943 = 2852915) B2852915
theorem B2407153 : Blo 1901435 2407153 := bbase (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) (by norm_num)
theorem B3209537 : Blo 1901435 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B2139691 : Blo 1901435 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B2852921 : Blo 1901435 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B1901947 : Blo 1901435 1901947 := bstep (se 1 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 1901947 = 2852921) B2852921
theorem B12352501 : Blo 1901435 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B16470001 : Blo 1901435 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B21960001 : Blo 1901435 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B29280001 : Blo 1901435 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B39040001 : Blo 1901435 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B26026667 : Blo 1901435 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B17351111 : Blo 1901435 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B46269629 : Blo 1901435 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B30846419 : Blo 1901435 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B20564279 : Blo 1901435 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B13709519 : Blo 1901435 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B9139679 : Blo 1901435 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B6093119 : Blo 1901435 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B4062079 : Blo 1901435 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B21664421 : Blo 1901435 21664421 := bstep (se 4 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 21664421 = 4062079) B4062079
theorem B14442947 : Blo 1901435 14442947 := bstep (se 1 (by rfl) ⟨10832210, by rfl⟩ : syracuseStep 14442947 = 21664421) B21664421
theorem B9628631 : Blo 1901435 9628631 := bstep (se 1 (by rfl) ⟨7221473, by rfl⟩ : syracuseStep 9628631 = 14442947) B14442947
theorem B6419087 : Blo 1901435 6419087 := bstep (se 1 (by rfl) ⟨4814315, by rfl⟩ : syracuseStep 6419087 = 9628631) B9628631
theorem B4279391 : Blo 1901435 4279391 := bstep (se 1 (by rfl) ⟨3209543, by rfl⟩ : syracuseStep 4279391 = 6419087) B6419087
theorem B2852927 : Blo 1901435 2852927 := bstep (se 1 (by rfl) ⟨2139695, by rfl⟩ : syracuseStep 2852927 = 4279391) B4279391
theorem B1901951 : Blo 1901435 1901951 := bstep (se 1 (by rfl) ⟨1426463, by rfl⟩ : syracuseStep 1901951 = 2852927) B2852927
theorem B2852933 : Blo 1901435 2852933 := bbase (se 4 (by rfl) ⟨267462, by rfl⟩ : syracuseStep 2852933 = 534925) (by norm_num)
theorem B1901955 : Blo 1901435 1901955 := bstep (se 1 (by rfl) ⟨1426466, by rfl⟩ : syracuseStep 1901955 = 2852933) B2852933
theorem B3209557 : Blo 1901435 3209557 := bbase (se 10 (by rfl) ⟨4701, by rfl⟩ : syracuseStep 3209557 = 9403) (by norm_num)
theorem B4279409 : Blo 1901435 4279409 := bstep (se 2 (by rfl) ⟨1604778, by rfl⟩ : syracuseStep 4279409 = 3209557) B3209557
theorem B2852939 : Blo 1901435 2852939 := bstep (se 1 (by rfl) ⟨2139704, by rfl⟩ : syracuseStep 2852939 = 4279409) B4279409
theorem B1901959 : Blo 1901435 1901959 := bstep (se 1 (by rfl) ⟨1426469, by rfl⟩ : syracuseStep 1901959 = 2852939) B2852939
theorem B2139709 : Blo 1901435 2139709 := bbase (se 3 (by rfl) ⟨401195, by rfl⟩ : syracuseStep 2139709 = 802391) (by norm_num)
theorem B2852945 : Blo 1901435 2852945 := bstep (se 2 (by rfl) ⟨1069854, by rfl⟩ : syracuseStep 2852945 = 2139709) B2139709
theorem B1901963 : Blo 1901435 1901963 := bstep (se 1 (by rfl) ⟨1426472, by rfl⟩ : syracuseStep 1901963 = 2852945) B2852945
theorem B6419141 : Blo 1901435 6419141 := bbase (se 4 (by rfl) ⟨601794, by rfl⟩ : syracuseStep 6419141 = 1203589) (by norm_num)
theorem B4279427 : Blo 1901435 4279427 := bstep (se 1 (by rfl) ⟨3209570, by rfl⟩ : syracuseStep 4279427 = 6419141) B6419141
theorem B2852951 : Blo 1901435 2852951 := bstep (se 1 (by rfl) ⟨2139713, by rfl⟩ : syracuseStep 2852951 = 4279427) B4279427
theorem B1901967 : Blo 1901435 1901967 := bstep (se 1 (by rfl) ⟨1426475, by rfl⟩ : syracuseStep 1901967 = 2852951) B2852951
theorem B2852957 : Blo 1901435 2852957 := bbase (se 3 (by rfl) ⟨534929, by rfl⟩ : syracuseStep 2852957 = 1069859) (by norm_num)
theorem B1901971 : Blo 1901435 1901971 := bstep (se 1 (by rfl) ⟨1426478, by rfl⟩ : syracuseStep 1901971 = 2852957) B2852957
theorem B4279445 : Blo 1901435 4279445 := bbase (se 6 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 4279445 = 200599) (by norm_num)
theorem B2852963 : Blo 1901435 2852963 := bstep (se 1 (by rfl) ⟨2139722, by rfl⟩ : syracuseStep 2852963 = 4279445) B4279445
theorem B1901975 : Blo 1901435 1901975 := bstep (se 1 (by rfl) ⟨1426481, by rfl⟩ : syracuseStep 1901975 = 2852963) B2852963
theorem B2708093 : Blo 1901435 2708093 := bbase (se 3 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 2708093 = 1015535) (by norm_num)
theorem B7221581 : Blo 1901435 7221581 := bstep (se 3 (by rfl) ⟨1354046, by rfl⟩ : syracuseStep 7221581 = 2708093) B2708093
theorem B4814387 : Blo 1901435 4814387 := bstep (se 1 (by rfl) ⟨3610790, by rfl⟩ : syracuseStep 4814387 = 7221581) B7221581
theorem B3209591 : Blo 1901435 3209591 := bstep (se 1 (by rfl) ⟨2407193, by rfl⟩ : syracuseStep 3209591 = 4814387) B4814387
theorem B2139727 : Blo 1901435 2139727 := bstep (se 1 (by rfl) ⟨1604795, by rfl⟩ : syracuseStep 2139727 = 3209591) B3209591
theorem B2852969 : Blo 1901435 2852969 := bstep (se 2 (by rfl) ⟨1069863, by rfl⟩ : syracuseStep 2852969 = 2139727) B2139727
theorem B1901979 : Blo 1901435 1901979 := bstep (se 1 (by rfl) ⟨1426484, by rfl⟩ : syracuseStep 1901979 = 2852969) B2852969
theorem B13709749 : Blo 1901435 13709749 := bbase (se 5 (by rfl) ⟨642644, by rfl⟩ : syracuseStep 13709749 = 1285289) (by norm_num)
theorem B18279665 : Blo 1901435 18279665 := bstep (se 2 (by rfl) ⟨6854874, by rfl⟩ : syracuseStep 18279665 = 13709749) B13709749
theorem B12186443 : Blo 1901435 12186443 := bstep (se 1 (by rfl) ⟨9139832, by rfl⟩ : syracuseStep 12186443 = 18279665) B18279665
theorem B8124295 : Blo 1901435 8124295 := bstep (se 1 (by rfl) ⟨6093221, by rfl⟩ : syracuseStep 8124295 = 12186443) B12186443
theorem B10832393 : Blo 1901435 10832393 := bstep (se 2 (by rfl) ⟨4062147, by rfl⟩ : syracuseStep 10832393 = 8124295) B8124295
theorem B7221595 : Blo 1901435 7221595 := bstep (se 1 (by rfl) ⟨5416196, by rfl⟩ : syracuseStep 7221595 = 10832393) B10832393
theorem B9628793 : Blo 1901435 9628793 := bstep (se 2 (by rfl) ⟨3610797, by rfl⟩ : syracuseStep 9628793 = 7221595) B7221595
theorem B6419195 : Blo 1901435 6419195 := bstep (se 1 (by rfl) ⟨4814396, by rfl⟩ : syracuseStep 6419195 = 9628793) B9628793
theorem B4279463 : Blo 1901435 4279463 := bstep (se 1 (by rfl) ⟨3209597, by rfl⟩ : syracuseStep 4279463 = 6419195) B6419195
theorem B2852975 : Blo 1901435 2852975 := bstep (se 1 (by rfl) ⟨2139731, by rfl⟩ : syracuseStep 2852975 = 4279463) B4279463
theorem B1901983 : Blo 1901435 1901983 := bstep (se 1 (by rfl) ⟨1426487, by rfl⟩ : syracuseStep 1901983 = 2852975) B2852975
theorem B2852981 : Blo 1901435 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B1901987 : Blo 1901435 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B3610813 : Blo 1901435 3610813 := bbase (se 3 (by rfl) ⟨677027, by rfl⟩ : syracuseStep 3610813 = 1354055) (by norm_num)
theorem B4814417 : Blo 1901435 4814417 := bstep (se 2 (by rfl) ⟨1805406, by rfl⟩ : syracuseStep 4814417 = 3610813) B3610813
theorem B3209611 : Blo 1901435 3209611 := bstep (se 1 (by rfl) ⟨2407208, by rfl⟩ : syracuseStep 3209611 = 4814417) B4814417
theorem B4279481 : Blo 1901435 4279481 := bstep (se 2 (by rfl) ⟨1604805, by rfl⟩ : syracuseStep 4279481 = 3209611) B3209611
theorem B2852987 : Blo 1901435 2852987 := bstep (se 1 (by rfl) ⟨2139740, by rfl⟩ : syracuseStep 2852987 = 4279481) B4279481
theorem B1901991 : Blo 1901435 1901991 := bstep (se 1 (by rfl) ⟨1426493, by rfl⟩ : syracuseStep 1901991 = 2852987) B2852987
theorem B2139745 : Blo 1901435 2139745 := bbase (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) (by norm_num)
theorem B2852993 : Blo 1901435 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B1901995 : Blo 1901435 1901995 := bstep (se 1 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 1901995 = 2852993) B2852993
theorem B4814437 : Blo 1901435 4814437 := bbase (se 4 (by rfl) ⟨451353, by rfl⟩ : syracuseStep 4814437 = 902707) (by norm_num)
theorem B6419249 : Blo 1901435 6419249 := bstep (se 2 (by rfl) ⟨2407218, by rfl⟩ : syracuseStep 6419249 = 4814437) B4814437
theorem B4279499 : Blo 1901435 4279499 := bstep (se 1 (by rfl) ⟨3209624, by rfl⟩ : syracuseStep 4279499 = 6419249) B6419249
theorem B2852999 : Blo 1901435 2852999 := bstep (se 1 (by rfl) ⟨2139749, by rfl⟩ : syracuseStep 2852999 = 4279499) B4279499
theorem B1901999 : Blo 1901435 1901999 := bstep (se 1 (by rfl) ⟨1426499, by rfl⟩ : syracuseStep 1901999 = 2852999) B2852999
theorem B2853005 : Blo 1901435 2853005 := bbase (se 3 (by rfl) ⟨534938, by rfl⟩ : syracuseStep 2853005 = 1069877) (by norm_num)
theorem B1902003 : Blo 1901435 1902003 := bstep (se 1 (by rfl) ⟨1426502, by rfl⟩ : syracuseStep 1902003 = 2853005) B2853005
theorem B4279517 : Blo 1901435 4279517 := bbase (se 3 (by rfl) ⟨802409, by rfl⟩ : syracuseStep 4279517 = 1604819) (by norm_num)
theorem B2853011 : Blo 1901435 2853011 := bstep (se 1 (by rfl) ⟨2139758, by rfl⟩ : syracuseStep 2853011 = 4279517) B4279517
theorem B1902007 : Blo 1901435 1902007 := bstep (se 1 (by rfl) ⟨1426505, by rfl⟩ : syracuseStep 1902007 = 2853011) B2853011
theorem B3209645 : Blo 1901435 3209645 := bbase (se 3 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 3209645 = 1203617) (by norm_num)
theorem B2139763 : Blo 1901435 2139763 := bstep (se 1 (by rfl) ⟨1604822, by rfl⟩ : syracuseStep 2139763 = 3209645) B3209645
theorem B2853017 : Blo 1901435 2853017 := bstep (se 2 (by rfl) ⟨1069881, by rfl⟩ : syracuseStep 2853017 = 2139763) B2139763
theorem B1902011 : Blo 1901435 1902011 := bstep (se 1 (by rfl) ⟨1426508, by rfl⟩ : syracuseStep 1902011 = 2853017) B2853017
theorem B10422773 : Blo 1901435 10422773 := bbase (se 5 (by rfl) ⟨488567, by rfl⟩ : syracuseStep 10422773 = 977135) (by norm_num)
theorem B6948515 : Blo 1901435 6948515 := bstep (se 1 (by rfl) ⟨5211386, by rfl⟩ : syracuseStep 6948515 = 10422773) B10422773
theorem B18529373 : Blo 1901435 18529373 := bstep (se 3 (by rfl) ⟨3474257, by rfl⟩ : syracuseStep 18529373 = 6948515) B6948515
theorem B12352915 : Blo 1901435 12352915 := bstep (se 1 (by rfl) ⟨9264686, by rfl⟩ : syracuseStep 12352915 = 18529373) B18529373
theorem B16470553 : Blo 1901435 16470553 := bstep (se 2 (by rfl) ⟨6176457, by rfl⟩ : syracuseStep 16470553 = 12352915) B12352915
theorem B21960737 : Blo 1901435 21960737 := bstep (se 2 (by rfl) ⟨8235276, by rfl⟩ : syracuseStep 21960737 = 16470553) B16470553
theorem B14640491 : Blo 1901435 14640491 := bstep (se 1 (by rfl) ⟨10980368, by rfl⟩ : syracuseStep 14640491 = 21960737) B21960737
theorem B9760327 : Blo 1901435 9760327 := bstep (se 1 (by rfl) ⟨7320245, by rfl⟩ : syracuseStep 9760327 = 14640491) B14640491
theorem B52055077 : Blo 1901435 52055077 := bstep (se 4 (by rfl) ⟨4880163, by rfl⟩ : syracuseStep 52055077 = 9760327) B9760327
theorem B69406769 : Blo 1901435 69406769 := bstep (se 2 (by rfl) ⟨26027538, by rfl⟩ : syracuseStep 69406769 = 52055077) B52055077
theorem B46271179 : Blo 1901435 46271179 := bstep (se 1 (by rfl) ⟨34703384, by rfl⟩ : syracuseStep 46271179 = 69406769) B69406769
theorem B61694905 : Blo 1901435 61694905 := bstep (se 2 (by rfl) ⟨23135589, by rfl⟩ : syracuseStep 61694905 = 46271179) B46271179
theorem B82259873 : Blo 1901435 82259873 := bstep (se 2 (by rfl) ⟨30847452, by rfl⟩ : syracuseStep 82259873 = 61694905) B61694905
theorem B54839915 : Blo 1901435 54839915 := bstep (se 1 (by rfl) ⟨41129936, by rfl⟩ : syracuseStep 54839915 = 82259873) B82259873
theorem B36559943 : Blo 1901435 36559943 := bstep (se 1 (by rfl) ⟨27419957, by rfl⟩ : syracuseStep 36559943 = 54839915) B54839915
theorem B24373295 : Blo 1901435 24373295 := bstep (se 1 (by rfl) ⟨18279971, by rfl⟩ : syracuseStep 24373295 = 36559943) B36559943
theorem B16248863 : Blo 1901435 16248863 := bstep (se 1 (by rfl) ⟨12186647, by rfl⟩ : syracuseStep 16248863 = 24373295) B24373295
theorem B10832575 : Blo 1901435 10832575 := bstep (se 1 (by rfl) ⟨8124431, by rfl⟩ : syracuseStep 10832575 = 16248863) B16248863
theorem B14443433 : Blo 1901435 14443433 := bstep (se 2 (by rfl) ⟨5416287, by rfl⟩ : syracuseStep 14443433 = 10832575) B10832575
theorem B9628955 : Blo 1901435 9628955 := bstep (se 1 (by rfl) ⟨7221716, by rfl⟩ : syracuseStep 9628955 = 14443433) B14443433
theorem B6419303 : Blo 1901435 6419303 := bstep (se 1 (by rfl) ⟨4814477, by rfl⟩ : syracuseStep 6419303 = 9628955) B9628955
theorem B4279535 : Blo 1901435 4279535 := bstep (se 1 (by rfl) ⟨3209651, by rfl⟩ : syracuseStep 4279535 = 6419303) B6419303
theorem B2853023 : Blo 1901435 2853023 := bstep (se 1 (by rfl) ⟨2139767, by rfl⟩ : syracuseStep 2853023 = 4279535) B4279535
theorem B1902015 : Blo 1901435 1902015 := bstep (se 1 (by rfl) ⟨1426511, by rfl⟩ : syracuseStep 1902015 = 2853023) B2853023
theorem B2853029 : Blo 1901435 2853029 := bbase (se 4 (by rfl) ⟨267471, by rfl⟩ : syracuseStep 2853029 = 534943) (by norm_num)
theorem B1902019 : Blo 1901435 1902019 := bstep (se 1 (by rfl) ⟨1426514, by rfl⟩ : syracuseStep 1902019 = 2853029) B2853029
theorem B2407249 : Blo 1901435 2407249 := bbase (se 2 (by rfl) ⟨902718, by rfl⟩ : syracuseStep 2407249 = 1805437) (by norm_num)
theorem B3209665 : Blo 1901435 3209665 := bstep (se 2 (by rfl) ⟨1203624, by rfl⟩ : syracuseStep 3209665 = 2407249) B2407249
theorem B4279553 : Blo 1901435 4279553 := bstep (se 2 (by rfl) ⟨1604832, by rfl⟩ : syracuseStep 4279553 = 3209665) B3209665
theorem B2853035 : Blo 1901435 2853035 := bstep (se 1 (by rfl) ⟨2139776, by rfl⟩ : syracuseStep 2853035 = 4279553) B4279553
theorem B1902023 : Blo 1901435 1902023 := bstep (se 1 (by rfl) ⟨1426517, by rfl⟩ : syracuseStep 1902023 = 2853035) B2853035
theorem B2139781 : Blo 1901435 2139781 := bbase (se 4 (by rfl) ⟨200604, by rfl⟩ : syracuseStep 2139781 = 401209) (by norm_num)
theorem B2853041 : Blo 1901435 2853041 := bstep (se 2 (by rfl) ⟨1069890, by rfl⟩ : syracuseStep 2853041 = 2139781) B2139781
theorem B1902027 : Blo 1901435 1902027 := bstep (se 1 (by rfl) ⟨1426520, by rfl⟩ : syracuseStep 1902027 = 2853041) B2853041
theorem B3427525 : Blo 1901435 3427525 := bbase (se 4 (by rfl) ⟨321330, by rfl⟩ : syracuseStep 3427525 = 642661) (by norm_num)
theorem B4570033 : Blo 1901435 4570033 := bstep (se 2 (by rfl) ⟨1713762, by rfl⟩ : syracuseStep 4570033 = 3427525) B3427525
theorem B6093377 : Blo 1901435 6093377 := bstep (se 2 (by rfl) ⟨2285016, by rfl⟩ : syracuseStep 6093377 = 4570033) B4570033
theorem B4062251 : Blo 1901435 4062251 := bstep (se 1 (by rfl) ⟨3046688, by rfl⟩ : syracuseStep 4062251 = 6093377) B6093377
theorem B2708167 : Blo 1901435 2708167 := bstep (se 1 (by rfl) ⟨2031125, by rfl⟩ : syracuseStep 2708167 = 4062251) B4062251
theorem B3610889 : Blo 1901435 3610889 := bstep (se 2 (by rfl) ⟨1354083, by rfl⟩ : syracuseStep 3610889 = 2708167) B2708167
theorem B2407259 : Blo 1901435 2407259 := bstep (se 1 (by rfl) ⟨1805444, by rfl⟩ : syracuseStep 2407259 = 3610889) B3610889
theorem B6419357 : Blo 1901435 6419357 := bstep (se 3 (by rfl) ⟨1203629, by rfl⟩ : syracuseStep 6419357 = 2407259) B2407259
theorem B4279571 : Blo 1901435 4279571 := bstep (se 1 (by rfl) ⟨3209678, by rfl⟩ : syracuseStep 4279571 = 6419357) B6419357
theorem B2853047 : Blo 1901435 2853047 := bstep (se 1 (by rfl) ⟨2139785, by rfl⟩ : syracuseStep 2853047 = 4279571) B4279571
theorem B1902031 : Blo 1901435 1902031 := bstep (se 1 (by rfl) ⟨1426523, by rfl⟩ : syracuseStep 1902031 = 2853047) B2853047
theorem B2853053 : Blo 1901435 2853053 := bbase (se 3 (by rfl) ⟨534947, by rfl⟩ : syracuseStep 2853053 = 1069895) (by norm_num)
theorem B1902035 : Blo 1901435 1902035 := bstep (se 1 (by rfl) ⟨1426526, by rfl⟩ : syracuseStep 1902035 = 2853053) B2853053
theorem B4279589 : Blo 1901435 4279589 := bbase (se 4 (by rfl) ⟨401211, by rfl⟩ : syracuseStep 4279589 = 802423) (by norm_num)
theorem B2853059 : Blo 1901435 2853059 := bstep (se 1 (by rfl) ⟨2139794, by rfl⟩ : syracuseStep 2853059 = 4279589) B4279589
theorem B1902039 : Blo 1901435 1902039 := bstep (se 1 (by rfl) ⟨1426529, by rfl⟩ : syracuseStep 1902039 = 2853059) B2853059
theorem B4814549 : Blo 1901435 4814549 := bbase (se 7 (by rfl) ⟨56420, by rfl⟩ : syracuseStep 4814549 = 112841) (by norm_num)
theorem B3209699 : Blo 1901435 3209699 := bstep (se 1 (by rfl) ⟨2407274, by rfl⟩ : syracuseStep 3209699 = 4814549) B4814549
theorem B2139799 : Blo 1901435 2139799 := bstep (se 1 (by rfl) ⟨1604849, by rfl⟩ : syracuseStep 2139799 = 3209699) B3209699
theorem B2853065 : Blo 1901435 2853065 := bstep (se 2 (by rfl) ⟨1069899, by rfl⟩ : syracuseStep 2853065 = 2139799) B2139799
theorem B1902043 : Blo 1901435 1902043 := bstep (se 1 (by rfl) ⟨1426532, by rfl⟩ : syracuseStep 1902043 = 2853065) B2853065
theorem B2198593 : Blo 1901435 2198593 := bbase (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) (by norm_num)
theorem B11725829 : Blo 1901435 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B7817219 : Blo 1901435 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B5211479 : Blo 1901435 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B13897277 : Blo 1901435 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B9264851 : Blo 1901435 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B6176567 : Blo 1901435 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B4117711 : Blo 1901435 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B5490281 : Blo 1901435 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B14640749 : Blo 1901435 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B9760499 : Blo 1901435 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B6506999 : Blo 1901435 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B4337999 : Blo 1901435 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B2891999 : Blo 1901435 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B1927999 : Blo 1901435 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B2570665 : Blo 1901435 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B3427553 : Blo 1901435 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B9140141 : Blo 1901435 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B6093427 : Blo 1901435 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B8124569 : Blo 1901435 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B5416379 : Blo 1901435 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B3610919 : Blo 1901435 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B9629117 : Blo 1901435 9629117 := bstep (se 3 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 9629117 = 3610919) B3610919
theorem B6419411 : Blo 1901435 6419411 := bstep (se 1 (by rfl) ⟨4814558, by rfl⟩ : syracuseStep 6419411 = 9629117) B9629117
theorem B4279607 : Blo 1901435 4279607 := bstep (se 1 (by rfl) ⟨3209705, by rfl⟩ : syracuseStep 4279607 = 6419411) B6419411
theorem B2853071 : Blo 1901435 2853071 := bstep (se 1 (by rfl) ⟨2139803, by rfl⟩ : syracuseStep 2853071 = 4279607) B4279607
theorem B1902047 : Blo 1901435 1902047 := bstep (se 1 (by rfl) ⟨1426535, by rfl⟩ : syracuseStep 1902047 = 2853071) B2853071
theorem B2853077 : Blo 1901435 2853077 := bbase (se 7 (by rfl) ⟨33434, by rfl⟩ : syracuseStep 2853077 = 66869) (by norm_num)
theorem B1902051 : Blo 1901435 1902051 := bstep (se 1 (by rfl) ⟨1426538, by rfl⟩ : syracuseStep 1902051 = 2853077) B2853077
theorem B4759717 : Blo 1901435 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B6346289 : Blo 1901435 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B4230859 : Blo 1901435 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B5641145 : Blo 1901435 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B3760763 : Blo 1901435 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B10028701 : Blo 1901435 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B13371601 : Blo 1901435 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B17828801 : Blo 1901435 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B11885867 : Blo 1901435 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B7923911 : Blo 1901435 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B21130429 : Blo 1901435 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B28173905 : Blo 1901435 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B18782603 : Blo 1901435 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B12521735 : Blo 1901435 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B8347823 : Blo 1901435 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B5565215 : Blo 1901435 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B3710143 : Blo 1901435 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B19787429 : Blo 1901435 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B13191619 : Blo 1901435 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B17588825 : Blo 1901435 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B11725883 : Blo 1901435 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B7817255 : Blo 1901435 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B5211503 : Blo 1901435 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B3474335 : Blo 1901435 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B2316223 : Blo 1901435 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B3088297 : Blo 1901435 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B4117729 : Blo 1901435 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B5490305 : Blo 1901435 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B3660203 : Blo 1901435 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B2440135 : Blo 1901435 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B13014053 : Blo 1901435 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B8676035 : Blo 1901435 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B5784023 : Blo 1901435 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B3856015 : Blo 1901435 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B5141353 : Blo 1901435 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B6855137 : Blo 1901435 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B4570091 : Blo 1901435 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B3046727 : Blo 1901435 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B2031151 : Blo 1901435 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B2708201 : Blo 1901435 2708201 := bstep (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) B2031151
theorem B7221869 : Blo 1901435 7221869 := bstep (se 3 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 7221869 = 2708201) B2708201
theorem B4814579 : Blo 1901435 4814579 := bstep (se 1 (by rfl) ⟨3610934, by rfl⟩ : syracuseStep 4814579 = 7221869) B7221869
theorem B3209719 : Blo 1901435 3209719 := bstep (se 1 (by rfl) ⟨2407289, by rfl⟩ : syracuseStep 3209719 = 4814579) B4814579
theorem B4279625 : Blo 1901435 4279625 := bstep (se 2 (by rfl) ⟨1604859, by rfl⟩ : syracuseStep 4279625 = 3209719) B3209719
theorem B2853083 : Blo 1901435 2853083 := bstep (se 1 (by rfl) ⟨2139812, by rfl⟩ : syracuseStep 2853083 = 4279625) B4279625
theorem B1902055 : Blo 1901435 1902055 := bstep (se 1 (by rfl) ⟨1426541, by rfl⟩ : syracuseStep 1902055 = 2853083) B2853083
theorem B2139817 : Blo 1901435 2139817 := bbase (se 2 (by rfl) ⟨802431, by rfl⟩ : syracuseStep 2139817 = 1604863) (by norm_num)
theorem B2853089 : Blo 1901435 2853089 := bstep (se 2 (by rfl) ⟨1069908, by rfl⟩ : syracuseStep 2853089 = 2139817) B2139817
theorem B1902059 : Blo 1901435 1902059 := bstep (se 1 (by rfl) ⟨1426544, by rfl⟩ : syracuseStep 1902059 = 2853089) B2853089
theorem B4570109 : Blo 1901435 4570109 := bbase (se 3 (by rfl) ⟨856895, by rfl⟩ : syracuseStep 4570109 = 1713791) (by norm_num)
theorem B3046739 : Blo 1901435 3046739 := bstep (se 1 (by rfl) ⟨2285054, by rfl⟩ : syracuseStep 3046739 = 4570109) B4570109
theorem B8124637 : Blo 1901435 8124637 := bstep (se 3 (by rfl) ⟨1523369, by rfl⟩ : syracuseStep 8124637 = 3046739) B3046739
theorem B10832849 : Blo 1901435 10832849 := bstep (se 2 (by rfl) ⟨4062318, by rfl⟩ : syracuseStep 10832849 = 8124637) B8124637
theorem B7221899 : Blo 1901435 7221899 := bstep (se 1 (by rfl) ⟨5416424, by rfl⟩ : syracuseStep 7221899 = 10832849) B10832849
theorem B4814599 : Blo 1901435 4814599 := bstep (se 1 (by rfl) ⟨3610949, by rfl⟩ : syracuseStep 4814599 = 7221899) B7221899
theorem B6419465 : Blo 1901435 6419465 := bstep (se 2 (by rfl) ⟨2407299, by rfl⟩ : syracuseStep 6419465 = 4814599) B4814599
theorem B4279643 : Blo 1901435 4279643 := bstep (se 1 (by rfl) ⟨3209732, by rfl⟩ : syracuseStep 4279643 = 6419465) B6419465
theorem B2853095 : Blo 1901435 2853095 := bstep (se 1 (by rfl) ⟨2139821, by rfl⟩ : syracuseStep 2853095 = 4279643) B4279643
theorem B1902063 : Blo 1901435 1902063 := bstep (se 1 (by rfl) ⟨1426547, by rfl⟩ : syracuseStep 1902063 = 2853095) B2853095
theorem B2853101 : Blo 1901435 2853101 := bbase (se 3 (by rfl) ⟨534956, by rfl⟩ : syracuseStep 2853101 = 1069913) (by norm_num)
theorem B1902067 : Blo 1901435 1902067 := bstep (se 1 (by rfl) ⟨1426550, by rfl⟩ : syracuseStep 1902067 = 2853101) B2853101
theorem B4279661 : Blo 1901435 4279661 := bbase (se 3 (by rfl) ⟨802436, by rfl⟩ : syracuseStep 4279661 = 1604873) (by norm_num)
theorem B2853107 : Blo 1901435 2853107 := bstep (se 1 (by rfl) ⟨2139830, by rfl⟩ : syracuseStep 2853107 = 4279661) B4279661
theorem B1902071 : Blo 1901435 1902071 := bstep (se 1 (by rfl) ⟨1426553, by rfl⟩ : syracuseStep 1902071 = 2853107) B2853107
theorem B3610973 : Blo 1901435 3610973 := bbase (se 3 (by rfl) ⟨677057, by rfl⟩ : syracuseStep 3610973 = 1354115) (by norm_num)
theorem B2407315 : Blo 1901435 2407315 := bstep (se 1 (by rfl) ⟨1805486, by rfl⟩ : syracuseStep 2407315 = 3610973) B3610973
theorem B3209753 : Blo 1901435 3209753 := bstep (se 2 (by rfl) ⟨1203657, by rfl⟩ : syracuseStep 3209753 = 2407315) B2407315
theorem B2139835 : Blo 1901435 2139835 := bstep (se 1 (by rfl) ⟨1604876, by rfl⟩ : syracuseStep 2139835 = 3209753) B3209753
theorem B2853113 : Blo 1901435 2853113 := bstep (se 2 (by rfl) ⟨1069917, by rfl⟩ : syracuseStep 2853113 = 2139835) B2139835
theorem B1902075 : Blo 1901435 1902075 := bstep (se 1 (by rfl) ⟨1426556, by rfl⟩ : syracuseStep 1902075 = 2853113) B2853113
theorem B9140293 : Blo 1901435 9140293 := bbase (se 4 (by rfl) ⟨856902, by rfl⟩ : syracuseStep 9140293 = 1713805) (by norm_num)
theorem B48748229 : Blo 1901435 48748229 := bstep (se 4 (by rfl) ⟨4570146, by rfl⟩ : syracuseStep 48748229 = 9140293) B9140293
theorem B32498819 : Blo 1901435 32498819 := bstep (se 1 (by rfl) ⟨24374114, by rfl⟩ : syracuseStep 32498819 = 48748229) B48748229
theorem B21665879 : Blo 1901435 21665879 := bstep (se 1 (by rfl) ⟨16249409, by rfl⟩ : syracuseStep 21665879 = 32498819) B32498819
theorem B14443919 : Blo 1901435 14443919 := bstep (se 1 (by rfl) ⟨10832939, by rfl⟩ : syracuseStep 14443919 = 21665879) B21665879
theorem B9629279 : Blo 1901435 9629279 := bstep (se 1 (by rfl) ⟨7221959, by rfl⟩ : syracuseStep 9629279 = 14443919) B14443919
theorem B6419519 : Blo 1901435 6419519 := bstep (se 1 (by rfl) ⟨4814639, by rfl⟩ : syracuseStep 6419519 = 9629279) B9629279
theorem B4279679 : Blo 1901435 4279679 := bstep (se 1 (by rfl) ⟨3209759, by rfl⟩ : syracuseStep 4279679 = 6419519) B6419519
theorem B2853119 : Blo 1901435 2853119 := bstep (se 1 (by rfl) ⟨2139839, by rfl⟩ : syracuseStep 2853119 = 4279679) B4279679
theorem B1902079 : Blo 1901435 1902079 := bstep (se 1 (by rfl) ⟨1426559, by rfl⟩ : syracuseStep 1902079 = 2853119) B2853119
theorem B2853125 : Blo 1901435 2853125 := bbase (se 4 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 2853125 = 534961) (by norm_num)
theorem B1902083 : Blo 1901435 1902083 := bstep (se 1 (by rfl) ⟨1426562, by rfl⟩ : syracuseStep 1902083 = 2853125) B2853125
theorem B3209773 : Blo 1901435 3209773 := bbase (se 3 (by rfl) ⟨601832, by rfl⟩ : syracuseStep 3209773 = 1203665) (by norm_num)
theorem B4279697 : Blo 1901435 4279697 := bstep (se 2 (by rfl) ⟨1604886, by rfl⟩ : syracuseStep 4279697 = 3209773) B3209773
theorem B2853131 : Blo 1901435 2853131 := bstep (se 1 (by rfl) ⟨2139848, by rfl⟩ : syracuseStep 2853131 = 4279697) B4279697
theorem B1902087 : Blo 1901435 1902087 := bstep (se 1 (by rfl) ⟨1426565, by rfl⟩ : syracuseStep 1902087 = 2853131) B2853131
theorem B2139853 : Blo 1901435 2139853 := bbase (se 3 (by rfl) ⟨401222, by rfl⟩ : syracuseStep 2139853 = 802445) (by norm_num)
theorem B2853137 : Blo 1901435 2853137 := bstep (se 2 (by rfl) ⟨1069926, by rfl⟩ : syracuseStep 2853137 = 2139853) B2139853
theorem B1902091 : Blo 1901435 1902091 := bstep (se 1 (by rfl) ⟨1426568, by rfl⟩ : syracuseStep 1902091 = 2853137) B2853137
theorem B6419573 : Blo 1901435 6419573 := bbase (se 5 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 6419573 = 601835) (by norm_num)
theorem B4279715 : Blo 1901435 4279715 := bstep (se 1 (by rfl) ⟨3209786, by rfl⟩ : syracuseStep 4279715 = 6419573) B6419573
theorem B2853143 : Blo 1901435 2853143 := bstep (se 1 (by rfl) ⟨2139857, by rfl⟩ : syracuseStep 2853143 = 4279715) B4279715
theorem B1902095 : Blo 1901435 1902095 := bstep (se 1 (by rfl) ⟨1426571, by rfl⟩ : syracuseStep 1902095 = 2853143) B2853143
theorem B2853149 : Blo 1901435 2853149 := bbase (se 3 (by rfl) ⟨534965, by rfl⟩ : syracuseStep 2853149 = 1069931) (by norm_num)
theorem B1902099 : Blo 1901435 1902099 := bstep (se 1 (by rfl) ⟨1426574, by rfl⟩ : syracuseStep 1902099 = 2853149) B2853149
theorem B4279733 : Blo 1901435 4279733 := bbase (se 5 (by rfl) ⟨200612, by rfl⟩ : syracuseStep 4279733 = 401225) (by norm_num)
theorem B2853155 : Blo 1901435 2853155 := bstep (se 1 (by rfl) ⟨2139866, by rfl⟩ : syracuseStep 2853155 = 4279733) B4279733
theorem B1902103 : Blo 1901435 1902103 := bstep (se 1 (by rfl) ⟨1426577, by rfl⟩ : syracuseStep 1902103 = 2853155) B2853155
theorem B4062413 : Blo 1901435 4062413 := bbase (se 3 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 4062413 = 1523405) (by norm_num)
theorem B10833101 : Blo 1901435 10833101 := bstep (se 3 (by rfl) ⟨2031206, by rfl⟩ : syracuseStep 10833101 = 4062413) B4062413
theorem B7222067 : Blo 1901435 7222067 := bstep (se 1 (by rfl) ⟨5416550, by rfl⟩ : syracuseStep 7222067 = 10833101) B10833101
theorem B4814711 : Blo 1901435 4814711 := bstep (se 1 (by rfl) ⟨3611033, by rfl⟩ : syracuseStep 4814711 = 7222067) B7222067
theorem B3209807 : Blo 1901435 3209807 := bstep (se 1 (by rfl) ⟨2407355, by rfl⟩ : syracuseStep 3209807 = 4814711) B4814711
theorem B2139871 : Blo 1901435 2139871 := bstep (se 1 (by rfl) ⟨1604903, by rfl⟩ : syracuseStep 2139871 = 3209807) B3209807
theorem B2853161 : Blo 1901435 2853161 := bstep (se 2 (by rfl) ⟨1069935, by rfl⟩ : syracuseStep 2853161 = 2139871) B2139871
theorem B1902107 : Blo 1901435 1902107 := bstep (se 1 (by rfl) ⟨1426580, by rfl⟩ : syracuseStep 1902107 = 2853161) B2853161
theorem B4062421 : Blo 1901435 4062421 := bbase (se 7 (by rfl) ⟨47606, by rfl⟩ : syracuseStep 4062421 = 95213) (by norm_num)
theorem B5416561 : Blo 1901435 5416561 := bstep (se 2 (by rfl) ⟨2031210, by rfl⟩ : syracuseStep 5416561 = 4062421) B4062421
theorem B7222081 : Blo 1901435 7222081 := bstep (se 2 (by rfl) ⟨2708280, by rfl⟩ : syracuseStep 7222081 = 5416561) B5416561
theorem B9629441 : Blo 1901435 9629441 := bstep (se 2 (by rfl) ⟨3611040, by rfl⟩ : syracuseStep 9629441 = 7222081) B7222081
theorem B6419627 : Blo 1901435 6419627 := bstep (se 1 (by rfl) ⟨4814720, by rfl⟩ : syracuseStep 6419627 = 9629441) B9629441
theorem B4279751 : Blo 1901435 4279751 := bstep (se 1 (by rfl) ⟨3209813, by rfl⟩ : syracuseStep 4279751 = 6419627) B6419627
theorem B2853167 : Blo 1901435 2853167 := bstep (se 1 (by rfl) ⟨2139875, by rfl⟩ : syracuseStep 2853167 = 4279751) B4279751
theorem B1902111 : Blo 1901435 1902111 := bstep (se 1 (by rfl) ⟨1426583, by rfl⟩ : syracuseStep 1902111 = 2853167) B2853167
theorem B2853173 : Blo 1901435 2853173 := bbase (se 5 (by rfl) ⟨133742, by rfl⟩ : syracuseStep 2853173 = 267485) (by norm_num)
theorem B1902115 : Blo 1901435 1902115 := bstep (se 1 (by rfl) ⟨1426586, by rfl⟩ : syracuseStep 1902115 = 2853173) B2853173
theorem B4814741 : Blo 1901435 4814741 := bbase (se 6 (by rfl) ⟨112845, by rfl⟩ : syracuseStep 4814741 = 225691) (by norm_num)
theorem B3209827 : Blo 1901435 3209827 := bstep (se 1 (by rfl) ⟨2407370, by rfl⟩ : syracuseStep 3209827 = 4814741) B4814741
theorem B4279769 : Blo 1901435 4279769 := bstep (se 2 (by rfl) ⟨1604913, by rfl⟩ : syracuseStep 4279769 = 3209827) B3209827
theorem B2853179 : Blo 1901435 2853179 := bstep (se 1 (by rfl) ⟨2139884, by rfl⟩ : syracuseStep 2853179 = 4279769) B4279769
theorem B1902119 : Blo 1901435 1902119 := bstep (se 1 (by rfl) ⟨1426589, by rfl⟩ : syracuseStep 1902119 = 2853179) B2853179
theorem B2139889 : Blo 1901435 2139889 := bbase (se 2 (by rfl) ⟨802458, by rfl⟩ : syracuseStep 2139889 = 1604917) (by norm_num)
theorem B2853185 : Blo 1901435 2853185 := bstep (se 2 (by rfl) ⟨1069944, by rfl⟩ : syracuseStep 2853185 = 2139889) B2139889
theorem B1902123 : Blo 1901435 1902123 := bstep (se 1 (by rfl) ⟨1426592, by rfl⟩ : syracuseStep 1902123 = 2853185) B2853185
theorem B3569917 : Blo 1901435 3569917 := bbase (se 3 (by rfl) ⟨669359, by rfl⟩ : syracuseStep 3569917 = 1338719) (by norm_num)
theorem B4759889 : Blo 1901435 4759889 := bstep (se 2 (by rfl) ⟨1784958, by rfl⟩ : syracuseStep 4759889 = 3569917) B3569917
theorem B12693037 : Blo 1901435 12693037 := bstep (se 3 (by rfl) ⟨2379944, by rfl⟩ : syracuseStep 12693037 = 4759889) B4759889
theorem B16924049 : Blo 1901435 16924049 := bstep (se 2 (by rfl) ⟨6346518, by rfl⟩ : syracuseStep 16924049 = 12693037) B12693037
theorem B11282699 : Blo 1901435 11282699 := bstep (se 1 (by rfl) ⟨8462024, by rfl⟩ : syracuseStep 11282699 = 16924049) B16924049
theorem B30087197 : Blo 1901435 30087197 := bstep (se 3 (by rfl) ⟨5641349, by rfl⟩ : syracuseStep 30087197 = 11282699) B11282699
theorem B20058131 : Blo 1901435 20058131 := bstep (se 1 (by rfl) ⟨15043598, by rfl⟩ : syracuseStep 20058131 = 30087197) B30087197
theorem B53488349 : Blo 1901435 53488349 := bstep (se 3 (by rfl) ⟨10029065, by rfl⟩ : syracuseStep 53488349 = 20058131) B20058131
theorem B35658899 : Blo 1901435 35658899 := bstep (se 1 (by rfl) ⟨26744174, by rfl⟩ : syracuseStep 35658899 = 53488349) B53488349
theorem B23772599 : Blo 1901435 23772599 := bstep (se 1 (by rfl) ⟨17829449, by rfl⟩ : syracuseStep 23772599 = 35658899) B35658899
theorem B15848399 : Blo 1901435 15848399 := bstep (se 1 (by rfl) ⟨11886299, by rfl⟩ : syracuseStep 15848399 = 23772599) B23772599
theorem B10565599 : Blo 1901435 10565599 := bstep (se 1 (by rfl) ⟨7924199, by rfl⟩ : syracuseStep 10565599 = 15848399) B15848399
theorem B14087465 : Blo 1901435 14087465 := bstep (se 2 (by rfl) ⟨5282799, by rfl⟩ : syracuseStep 14087465 = 10565599) B10565599
theorem B9391643 : Blo 1901435 9391643 := bstep (se 1 (by rfl) ⟨7043732, by rfl⟩ : syracuseStep 9391643 = 14087465) B14087465
theorem B6261095 : Blo 1901435 6261095 := bstep (se 1 (by rfl) ⟨4695821, by rfl⟩ : syracuseStep 6261095 = 9391643) B9391643
theorem B16696253 : Blo 1901435 16696253 := bstep (se 3 (by rfl) ⟨3130547, by rfl⟩ : syracuseStep 16696253 = 6261095) B6261095
theorem B44523341 : Blo 1901435 44523341 := bstep (se 3 (by rfl) ⟨8348126, by rfl⟩ : syracuseStep 44523341 = 16696253) B16696253
theorem B29682227 : Blo 1901435 29682227 := bstep (se 1 (by rfl) ⟨22261670, by rfl⟩ : syracuseStep 29682227 = 44523341) B44523341
theorem B19788151 : Blo 1901435 19788151 := bstep (se 1 (by rfl) ⟨14841113, by rfl⟩ : syracuseStep 19788151 = 29682227) B29682227
theorem B26384201 : Blo 1901435 26384201 := bstep (se 2 (by rfl) ⟨9894075, by rfl⟩ : syracuseStep 26384201 = 19788151) B19788151
theorem B17589467 : Blo 1901435 17589467 := bstep (se 1 (by rfl) ⟨13192100, by rfl⟩ : syracuseStep 17589467 = 26384201) B26384201
theorem B11726311 : Blo 1901435 11726311 := bstep (se 1 (by rfl) ⟨8794733, by rfl⟩ : syracuseStep 11726311 = 17589467) B17589467
theorem B15635081 : Blo 1901435 15635081 := bstep (se 2 (by rfl) ⟨5863155, by rfl⟩ : syracuseStep 15635081 = 11726311) B11726311
theorem B41693549 : Blo 1901435 41693549 := bstep (se 3 (by rfl) ⟨7817540, by rfl⟩ : syracuseStep 41693549 = 15635081) B15635081
theorem B111182797 : Blo 1901435 111182797 := bstep (se 3 (by rfl) ⟨20846774, by rfl⟩ : syracuseStep 111182797 = 41693549) B41693549
theorem B148243729 : Blo 1901435 148243729 := bstep (se 2 (by rfl) ⟨55591398, by rfl⟩ : syracuseStep 148243729 = 111182797) B111182797
theorem B197658305 : Blo 1901435 197658305 := bstep (se 2 (by rfl) ⟨74121864, by rfl⟩ : syracuseStep 197658305 = 148243729) B148243729
theorem B131772203 : Blo 1901435 131772203 := bstep (se 1 (by rfl) ⟨98829152, by rfl⟩ : syracuseStep 131772203 = 197658305) B197658305
theorem B87848135 : Blo 1901435 87848135 := bstep (se 1 (by rfl) ⟨65886101, by rfl⟩ : syracuseStep 87848135 = 131772203) B131772203
theorem B58565423 : Blo 1901435 58565423 := bstep (se 1 (by rfl) ⟨43924067, by rfl⟩ : syracuseStep 58565423 = 87848135) B87848135
theorem B39043615 : Blo 1901435 39043615 := bstep (se 1 (by rfl) ⟨29282711, by rfl⟩ : syracuseStep 39043615 = 58565423) B58565423
theorem B52058153 : Blo 1901435 52058153 := bstep (se 2 (by rfl) ⟨19521807, by rfl⟩ : syracuseStep 52058153 = 39043615) B39043615
theorem B34705435 : Blo 1901435 34705435 := bstep (se 1 (by rfl) ⟨26029076, by rfl⟩ : syracuseStep 34705435 = 52058153) B52058153
theorem B46273913 : Blo 1901435 46273913 := bstep (se 2 (by rfl) ⟨17352717, by rfl⟩ : syracuseStep 46273913 = 34705435) B34705435
theorem B30849275 : Blo 1901435 30849275 := bstep (se 1 (by rfl) ⟨23136956, by rfl⟩ : syracuseStep 30849275 = 46273913) B46273913
theorem B20566183 : Blo 1901435 20566183 := bstep (se 1 (by rfl) ⟨15424637, by rfl⟩ : syracuseStep 20566183 = 30849275) B30849275
theorem B27421577 : Blo 1901435 27421577 := bstep (se 2 (by rfl) ⟨10283091, by rfl⟩ : syracuseStep 27421577 = 20566183) B20566183
theorem B18281051 : Blo 1901435 18281051 := bstep (se 1 (by rfl) ⟨13710788, by rfl⟩ : syracuseStep 18281051 = 27421577) B27421577
theorem B12187367 : Blo 1901435 12187367 := bstep (se 1 (by rfl) ⟨9140525, by rfl⟩ : syracuseStep 12187367 = 18281051) B18281051
theorem B8124911 : Blo 1901435 8124911 := bstep (se 1 (by rfl) ⟨6093683, by rfl⟩ : syracuseStep 8124911 = 12187367) B12187367
theorem B5416607 : Blo 1901435 5416607 := bstep (se 1 (by rfl) ⟨4062455, by rfl⟩ : syracuseStep 5416607 = 8124911) B8124911
theorem B3611071 : Blo 1901435 3611071 := bstep (se 1 (by rfl) ⟨2708303, by rfl⟩ : syracuseStep 3611071 = 5416607) B5416607
theorem B4814761 : Blo 1901435 4814761 := bstep (se 2 (by rfl) ⟨1805535, by rfl⟩ : syracuseStep 4814761 = 3611071) B3611071
theorem B6419681 : Blo 1901435 6419681 := bstep (se 2 (by rfl) ⟨2407380, by rfl⟩ : syracuseStep 6419681 = 4814761) B4814761
theorem B4279787 : Blo 1901435 4279787 := bstep (se 1 (by rfl) ⟨3209840, by rfl⟩ : syracuseStep 4279787 = 6419681) B6419681
theorem B2853191 : Blo 1901435 2853191 := bstep (se 1 (by rfl) ⟨2139893, by rfl⟩ : syracuseStep 2853191 = 4279787) B4279787
theorem B1902127 : Blo 1901435 1902127 := bstep (se 1 (by rfl) ⟨1426595, by rfl⟩ : syracuseStep 1902127 = 2853191) B2853191
theorem B2853197 : Blo 1901435 2853197 := bbase (se 3 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 2853197 = 1069949) (by norm_num)
theorem B1902131 : Blo 1901435 1902131 := bstep (se 1 (by rfl) ⟨1426598, by rfl⟩ : syracuseStep 1902131 = 2853197) B2853197
theorem B4279805 : Blo 1901435 4279805 := bbase (se 3 (by rfl) ⟨802463, by rfl⟩ : syracuseStep 4279805 = 1604927) (by norm_num)
theorem B2853203 : Blo 1901435 2853203 := bstep (se 1 (by rfl) ⟨2139902, by rfl⟩ : syracuseStep 2853203 = 4279805) B4279805
theorem B1902135 : Blo 1901435 1902135 := bstep (se 1 (by rfl) ⟨1426601, by rfl⟩ : syracuseStep 1902135 = 2853203) B2853203
theorem B3209861 : Blo 1901435 3209861 := bbase (se 4 (by rfl) ⟨300924, by rfl⟩ : syracuseStep 3209861 = 601849) (by norm_num)
theorem B2139907 : Blo 1901435 2139907 := bstep (se 1 (by rfl) ⟨1604930, by rfl⟩ : syracuseStep 2139907 = 3209861) B3209861
theorem B2853209 : Blo 1901435 2853209 := bstep (se 2 (by rfl) ⟨1069953, by rfl⟩ : syracuseStep 2853209 = 2139907) B2139907
theorem B1902139 : Blo 1901435 1902139 := bstep (se 1 (by rfl) ⟨1426604, by rfl⟩ : syracuseStep 1902139 = 2853209) B2853209
theorem B14444405 : Blo 1901435 14444405 := bbase (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) (by norm_num)
theorem B9629603 : Blo 1901435 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B6419735 : Blo 1901435 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B4279823 : Blo 1901435 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B2853215 : Blo 1901435 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B1902143 : Blo 1901435 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B2853221 : Blo 1901435 2853221 := bbase (se 4 (by rfl) ⟨267489, by rfl⟩ : syracuseStep 2853221 = 534979) (by norm_num)
theorem B1902147 : Blo 1901435 1902147 := bstep (se 1 (by rfl) ⟨1426610, by rfl⟩ : syracuseStep 1902147 = 2853221) B2853221
theorem B3611117 : Blo 1901435 3611117 := bbase (se 3 (by rfl) ⟨677084, by rfl⟩ : syracuseStep 3611117 = 1354169) (by norm_num)
theorem B2407411 : Blo 1901435 2407411 := bstep (se 1 (by rfl) ⟨1805558, by rfl⟩ : syracuseStep 2407411 = 3611117) B3611117
theorem B3209881 : Blo 1901435 3209881 := bstep (se 2 (by rfl) ⟨1203705, by rfl⟩ : syracuseStep 3209881 = 2407411) B2407411
theorem B4279841 : Blo 1901435 4279841 := bstep (se 2 (by rfl) ⟨1604940, by rfl⟩ : syracuseStep 4279841 = 3209881) B3209881
theorem B2853227 : Blo 1901435 2853227 := bstep (se 1 (by rfl) ⟨2139920, by rfl⟩ : syracuseStep 2853227 = 4279841) B4279841
theorem B1902151 : Blo 1901435 1902151 := bstep (se 1 (by rfl) ⟨1426613, by rfl⟩ : syracuseStep 1902151 = 2853227) B2853227
theorem B2139925 : Blo 1901435 2139925 := bbase (se 6 (by rfl) ⟨50154, by rfl⟩ : syracuseStep 2139925 = 100309) (by norm_num)
theorem B2853233 : Blo 1901435 2853233 := bstep (se 2 (by rfl) ⟨1069962, by rfl⟩ : syracuseStep 2853233 = 2139925) B2139925
theorem B1902155 : Blo 1901435 1902155 := bstep (se 1 (by rfl) ⟨1426616, by rfl⟩ : syracuseStep 1902155 = 2853233) B2853233
theorem B2407421 : Blo 1901435 2407421 := bbase (se 3 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 2407421 = 902783) (by norm_num)
theorem B6419789 : Blo 1901435 6419789 := bstep (se 3 (by rfl) ⟨1203710, by rfl⟩ : syracuseStep 6419789 = 2407421) B2407421
theorem B4279859 : Blo 1901435 4279859 := bstep (se 1 (by rfl) ⟨3209894, by rfl⟩ : syracuseStep 4279859 = 6419789) B6419789
theorem B2853239 : Blo 1901435 2853239 := bstep (se 1 (by rfl) ⟨2139929, by rfl⟩ : syracuseStep 2853239 = 4279859) B4279859
theorem B1902159 : Blo 1901435 1902159 := bstep (se 1 (by rfl) ⟨1426619, by rfl⟩ : syracuseStep 1902159 = 2853239) B2853239
theorem B2853245 : Blo 1901435 2853245 := bbase (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) (by norm_num)
theorem B1902163 : Blo 1901435 1902163 := bstep (se 1 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 1902163 = 2853245) B2853245
theorem B4279877 : Blo 1901435 4279877 := bbase (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) (by norm_num)
theorem B2853251 : Blo 1901435 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B1902167 : Blo 1901435 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B2285185 : Blo 1901435 2285185 := bbase (se 2 (by rfl) ⟨856944, by rfl⟩ : syracuseStep 2285185 = 1713889) (by norm_num)
theorem B3046913 : Blo 1901435 3046913 := bstep (se 2 (by rfl) ⟨1142592, by rfl⟩ : syracuseStep 3046913 = 2285185) B2285185
theorem B2031275 : Blo 1901435 2031275 := bstep (se 1 (by rfl) ⟨1523456, by rfl⟩ : syracuseStep 2031275 = 3046913) B3046913
theorem B5416733 : Blo 1901435 5416733 := bstep (se 3 (by rfl) ⟨1015637, by rfl⟩ : syracuseStep 5416733 = 2031275) B2031275
theorem B3611155 : Blo 1901435 3611155 := bstep (se 1 (by rfl) ⟨2708366, by rfl⟩ : syracuseStep 3611155 = 5416733) B5416733
theorem B4814873 : Blo 1901435 4814873 := bstep (se 2 (by rfl) ⟨1805577, by rfl⟩ : syracuseStep 4814873 = 3611155) B3611155
theorem B3209915 : Blo 1901435 3209915 := bstep (se 1 (by rfl) ⟨2407436, by rfl⟩ : syracuseStep 3209915 = 4814873) B4814873
theorem B2139943 : Blo 1901435 2139943 := bstep (se 1 (by rfl) ⟨1604957, by rfl⟩ : syracuseStep 2139943 = 3209915) B3209915
theorem B2853257 : Blo 1901435 2853257 := bstep (se 2 (by rfl) ⟨1069971, by rfl⟩ : syracuseStep 2853257 = 2139943) B2139943
theorem B1902171 : Blo 1901435 1902171 := bstep (se 1 (by rfl) ⟨1426628, by rfl⟩ : syracuseStep 1902171 = 2853257) B2853257
theorem B9629765 : Blo 1901435 9629765 := bbase (se 4 (by rfl) ⟨902790, by rfl⟩ : syracuseStep 9629765 = 1805581) (by norm_num)
theorem B6419843 : Blo 1901435 6419843 := bstep (se 1 (by rfl) ⟨4814882, by rfl⟩ : syracuseStep 6419843 = 9629765) B9629765
theorem B4279895 : Blo 1901435 4279895 := bstep (se 1 (by rfl) ⟨3209921, by rfl⟩ : syracuseStep 4279895 = 6419843) B6419843
theorem B2853263 : Blo 1901435 2853263 := bstep (se 1 (by rfl) ⟨2139947, by rfl⟩ : syracuseStep 2853263 = 4279895) B4279895
theorem B1902175 : Blo 1901435 1902175 := bstep (se 1 (by rfl) ⟨1426631, by rfl⟩ : syracuseStep 1902175 = 2853263) B2853263
theorem B2853269 : Blo 1901435 2853269 := bbase (se 6 (by rfl) ⟨66873, by rfl⟩ : syracuseStep 2853269 = 133747) (by norm_num)
theorem B1902179 : Blo 1901435 1902179 := bstep (se 1 (by rfl) ⟨1426634, by rfl⟩ : syracuseStep 1902179 = 2853269) B2853269
theorem B2892205 : Blo 1901435 2892205 := bbase (se 3 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 2892205 = 1084577) (by norm_num)
theorem B15425093 : Blo 1901435 15425093 := bstep (se 4 (by rfl) ⟨1446102, by rfl⟩ : syracuseStep 15425093 = 2892205) B2892205
theorem B10283395 : Blo 1901435 10283395 := bstep (se 1 (by rfl) ⟨7712546, by rfl⟩ : syracuseStep 10283395 = 15425093) B15425093
theorem B13711193 : Blo 1901435 13711193 := bstep (se 2 (by rfl) ⟨5141697, by rfl⟩ : syracuseStep 13711193 = 10283395) B10283395
theorem B9140795 : Blo 1901435 9140795 := bstep (se 1 (by rfl) ⟨6855596, by rfl⟩ : syracuseStep 9140795 = 13711193) B13711193
theorem B6093863 : Blo 1901435 6093863 := bstep (se 1 (by rfl) ⟨4570397, by rfl⟩ : syracuseStep 6093863 = 9140795) B9140795
theorem B4062575 : Blo 1901435 4062575 := bstep (se 1 (by rfl) ⟨3046931, by rfl⟩ : syracuseStep 4062575 = 6093863) B6093863
theorem B10833533 : Blo 1901435 10833533 := bstep (se 3 (by rfl) ⟨2031287, by rfl⟩ : syracuseStep 10833533 = 4062575) B4062575
theorem B7222355 : Blo 1901435 7222355 := bstep (se 1 (by rfl) ⟨5416766, by rfl⟩ : syracuseStep 7222355 = 10833533) B10833533
theorem B4814903 : Blo 1901435 4814903 := bstep (se 1 (by rfl) ⟨3611177, by rfl⟩ : syracuseStep 4814903 = 7222355) B7222355
theorem B3209935 : Blo 1901435 3209935 := bstep (se 1 (by rfl) ⟨2407451, by rfl⟩ : syracuseStep 3209935 = 4814903) B4814903
theorem B4279913 : Blo 1901435 4279913 := bstep (se 2 (by rfl) ⟨1604967, by rfl⟩ : syracuseStep 4279913 = 3209935) B3209935
theorem B2853275 : Blo 1901435 2853275 := bstep (se 1 (by rfl) ⟨2139956, by rfl⟩ : syracuseStep 2853275 = 4279913) B4279913
theorem B1902183 : Blo 1901435 1902183 := bstep (se 1 (by rfl) ⟨1426637, by rfl⟩ : syracuseStep 1902183 = 2853275) B2853275
theorem B2139961 : Blo 1901435 2139961 := bbase (se 2 (by rfl) ⟨802485, by rfl⟩ : syracuseStep 2139961 = 1604971) (by norm_num)
theorem B2853281 : Blo 1901435 2853281 := bstep (se 2 (by rfl) ⟨1069980, by rfl⟩ : syracuseStep 2853281 = 2139961) B2139961
theorem B1902187 : Blo 1901435 1902187 := bstep (se 1 (by rfl) ⟨1426640, by rfl⟩ : syracuseStep 1902187 = 2853281) B2853281
theorem B5416789 : Blo 1901435 5416789 := bbase (se 9 (by rfl) ⟨15869, by rfl⟩ : syracuseStep 5416789 = 31739) (by norm_num)
theorem B7222385 : Blo 1901435 7222385 := bstep (se 2 (by rfl) ⟨2708394, by rfl⟩ : syracuseStep 7222385 = 5416789) B5416789
theorem B4814923 : Blo 1901435 4814923 := bstep (se 1 (by rfl) ⟨3611192, by rfl⟩ : syracuseStep 4814923 = 7222385) B7222385
theorem B6419897 : Blo 1901435 6419897 := bstep (se 2 (by rfl) ⟨2407461, by rfl⟩ : syracuseStep 6419897 = 4814923) B4814923
theorem B4279931 : Blo 1901435 4279931 := bstep (se 1 (by rfl) ⟨3209948, by rfl⟩ : syracuseStep 4279931 = 6419897) B6419897
theorem B2853287 : Blo 1901435 2853287 := bstep (se 1 (by rfl) ⟨2139965, by rfl⟩ : syracuseStep 2853287 = 4279931) B4279931
theorem B1902191 : Blo 1901435 1902191 := bstep (se 1 (by rfl) ⟨1426643, by rfl⟩ : syracuseStep 1902191 = 2853287) B2853287
theorem B2853293 : Blo 1901435 2853293 := bbase (se 3 (by rfl) ⟨534992, by rfl⟩ : syracuseStep 2853293 = 1069985) (by norm_num)
theorem B1902195 : Blo 1901435 1902195 := bstep (se 1 (by rfl) ⟨1426646, by rfl⟩ : syracuseStep 1902195 = 2853293) B2853293
theorem B4279949 : Blo 1901435 4279949 := bbase (se 3 (by rfl) ⟨802490, by rfl⟩ : syracuseStep 4279949 = 1604981) (by norm_num)
theorem B2853299 : Blo 1901435 2853299 := bstep (se 1 (by rfl) ⟨2139974, by rfl⟩ : syracuseStep 2853299 = 4279949) B4279949
theorem B1902199 : Blo 1901435 1902199 := bstep (se 1 (by rfl) ⟨1426649, by rfl⟩ : syracuseStep 1902199 = 2853299) B2853299
theorem B2407477 : Blo 1901435 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B3209969 : Blo 1901435 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B2139979 : Blo 1901435 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B2853305 : Blo 1901435 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B1902203 : Blo 1901435 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B2169181 : Blo 1901435 2169181 := bbase (se 3 (by rfl) ⟨406721, by rfl⟩ : syracuseStep 2169181 = 813443) (by norm_num)
theorem B2892241 : Blo 1901435 2892241 := bstep (se 2 (by rfl) ⟨1084590, by rfl⟩ : syracuseStep 2892241 = 2169181) B2169181
theorem B3856321 : Blo 1901435 3856321 := bstep (se 2 (by rfl) ⟨1446120, by rfl⟩ : syracuseStep 3856321 = 2892241) B2892241
theorem B5141761 : Blo 1901435 5141761 := bstep (se 2 (by rfl) ⟨1928160, by rfl⟩ : syracuseStep 5141761 = 3856321) B3856321
theorem B27422725 : Blo 1901435 27422725 := bstep (se 4 (by rfl) ⟨2570880, by rfl⟩ : syracuseStep 27422725 = 5141761) B5141761
theorem B36563633 : Blo 1901435 36563633 := bstep (se 2 (by rfl) ⟨13711362, by rfl⟩ : syracuseStep 36563633 = 27422725) B27422725
theorem B24375755 : Blo 1901435 24375755 := bstep (se 1 (by rfl) ⟨18281816, by rfl⟩ : syracuseStep 24375755 = 36563633) B36563633
theorem B16250503 : Blo 1901435 16250503 := bstep (se 1 (by rfl) ⟨12187877, by rfl⟩ : syracuseStep 16250503 = 24375755) B24375755
theorem B21667337 : Blo 1901435 21667337 := bstep (se 2 (by rfl) ⟨8125251, by rfl⟩ : syracuseStep 21667337 = 16250503) B16250503
theorem B14444891 : Blo 1901435 14444891 := bstep (se 1 (by rfl) ⟨10833668, by rfl⟩ : syracuseStep 14444891 = 21667337) B21667337
theorem B9629927 : Blo 1901435 9629927 := bstep (se 1 (by rfl) ⟨7222445, by rfl⟩ : syracuseStep 9629927 = 14444891) B14444891
theorem B6419951 : Blo 1901435 6419951 := bstep (se 1 (by rfl) ⟨4814963, by rfl⟩ : syracuseStep 6419951 = 9629927) B9629927
theorem B4279967 : Blo 1901435 4279967 := bstep (se 1 (by rfl) ⟨3209975, by rfl⟩ : syracuseStep 4279967 = 6419951) B6419951
theorem B2853311 : Blo 1901435 2853311 := bstep (se 1 (by rfl) ⟨2139983, by rfl⟩ : syracuseStep 2853311 = 4279967) B4279967
theorem B1902207 : Blo 1901435 1902207 := bstep (se 1 (by rfl) ⟨1426655, by rfl⟩ : syracuseStep 1902207 = 2853311) B2853311
theorem B2853317 : Blo 1901435 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B1902211 : Blo 1901435 1902211 := bstep (se 1 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 1902211 = 2853317) B2853317
theorem B3209989 : Blo 1901435 3209989 := bbase (se 4 (by rfl) ⟨300936, by rfl⟩ : syracuseStep 3209989 = 601873) (by norm_num)
theorem B4279985 : Blo 1901435 4279985 := bstep (se 2 (by rfl) ⟨1604994, by rfl⟩ : syracuseStep 4279985 = 3209989) B3209989
theorem B2853323 : Blo 1901435 2853323 := bstep (se 1 (by rfl) ⟨2139992, by rfl⟩ : syracuseStep 2853323 = 4279985) B4279985
theorem B1902215 : Blo 1901435 1902215 := bstep (se 1 (by rfl) ⟨1426661, by rfl⟩ : syracuseStep 1902215 = 2853323) B2853323
theorem B2139997 : Blo 1901435 2139997 := bbase (se 3 (by rfl) ⟨401249, by rfl⟩ : syracuseStep 2139997 = 802499) (by norm_num)
theorem B2853329 : Blo 1901435 2853329 := bstep (se 2 (by rfl) ⟨1069998, by rfl⟩ : syracuseStep 2853329 = 2139997) B2139997
theorem B1902219 : Blo 1901435 1902219 := bstep (se 1 (by rfl) ⟨1426664, by rfl⟩ : syracuseStep 1902219 = 2853329) B2853329
theorem B6420005 : Blo 1901435 6420005 := bbase (se 4 (by rfl) ⟨601875, by rfl⟩ : syracuseStep 6420005 = 1203751) (by norm_num)
theorem B4280003 : Blo 1901435 4280003 := bstep (se 1 (by rfl) ⟨3210002, by rfl⟩ : syracuseStep 4280003 = 6420005) B6420005
theorem B2853335 : Blo 1901435 2853335 := bstep (se 1 (by rfl) ⟨2140001, by rfl⟩ : syracuseStep 2853335 = 4280003) B4280003
theorem B1902223 : Blo 1901435 1902223 := bstep (se 1 (by rfl) ⟨1426667, by rfl⟩ : syracuseStep 1902223 = 2853335) B2853335
theorem B2853341 : Blo 1901435 2853341 := bbase (se 3 (by rfl) ⟨535001, by rfl⟩ : syracuseStep 2853341 = 1070003) (by norm_num)
theorem B1902227 : Blo 1901435 1902227 := bstep (se 1 (by rfl) ⟨1426670, by rfl⟩ : syracuseStep 1902227 = 2853341) B2853341
theorem B4280021 : Blo 1901435 4280021 := bbase (se 7 (by rfl) ⟨50156, by rfl⟩ : syracuseStep 4280021 = 100313) (by norm_num)
theorem B2853347 : Blo 1901435 2853347 := bstep (se 1 (by rfl) ⟨2140010, by rfl⟩ : syracuseStep 2853347 = 4280021) B4280021
theorem B1902231 : Blo 1901435 1902231 := bstep (se 1 (by rfl) ⟨1426673, by rfl⟩ : syracuseStep 1902231 = 2853347) B2853347
theorem B9265765 : Blo 1901435 9265765 := bbase (se 4 (by rfl) ⟨868665, by rfl⟩ : syracuseStep 9265765 = 1737331) (by norm_num)
theorem B12354353 : Blo 1901435 12354353 := bstep (se 2 (by rfl) ⟨4632882, by rfl⟩ : syracuseStep 12354353 = 9265765) B9265765
theorem B8236235 : Blo 1901435 8236235 := bstep (se 1 (by rfl) ⟨6177176, by rfl⟩ : syracuseStep 8236235 = 12354353) B12354353
theorem B5490823 : Blo 1901435 5490823 := bstep (se 1 (by rfl) ⟨4118117, by rfl⟩ : syracuseStep 5490823 = 8236235) B8236235
theorem B7321097 : Blo 1901435 7321097 := bstep (se 2 (by rfl) ⟨2745411, by rfl⟩ : syracuseStep 7321097 = 5490823) B5490823
theorem B4880731 : Blo 1901435 4880731 := bstep (se 1 (by rfl) ⟨3660548, by rfl⟩ : syracuseStep 4880731 = 7321097) B7321097
theorem B6507641 : Blo 1901435 6507641 := bstep (se 2 (by rfl) ⟨2440365, by rfl⟩ : syracuseStep 6507641 = 4880731) B4880731
theorem B17353709 : Blo 1901435 17353709 := bstep (se 3 (by rfl) ⟨3253820, by rfl⟩ : syracuseStep 17353709 = 6507641) B6507641
theorem B11569139 : Blo 1901435 11569139 := bstep (se 1 (by rfl) ⟨8676854, by rfl⟩ : syracuseStep 11569139 = 17353709) B17353709
theorem B7712759 : Blo 1901435 7712759 := bstep (se 1 (by rfl) ⟨5784569, by rfl⟩ : syracuseStep 7712759 = 11569139) B11569139
theorem B5141839 : Blo 1901435 5141839 := bstep (se 1 (by rfl) ⟨3856379, by rfl⟩ : syracuseStep 5141839 = 7712759) B7712759
theorem B6855785 : Blo 1901435 6855785 := bstep (se 2 (by rfl) ⟨2570919, by rfl⟩ : syracuseStep 6855785 = 5141839) B5141839
theorem B4570523 : Blo 1901435 4570523 := bstep (se 1 (by rfl) ⟨3427892, by rfl⟩ : syracuseStep 4570523 = 6855785) B6855785
theorem B3047015 : Blo 1901435 3047015 := bstep (se 1 (by rfl) ⟨2285261, by rfl⟩ : syracuseStep 3047015 = 4570523) B4570523
theorem B8125373 : Blo 1901435 8125373 := bstep (se 3 (by rfl) ⟨1523507, by rfl⟩ : syracuseStep 8125373 = 3047015) B3047015
theorem B5416915 : Blo 1901435 5416915 := bstep (se 1 (by rfl) ⟨4062686, by rfl⟩ : syracuseStep 5416915 = 8125373) B8125373
theorem B7222553 : Blo 1901435 7222553 := bstep (se 2 (by rfl) ⟨2708457, by rfl⟩ : syracuseStep 7222553 = 5416915) B5416915
theorem B4815035 : Blo 1901435 4815035 := bstep (se 1 (by rfl) ⟨3611276, by rfl⟩ : syracuseStep 4815035 = 7222553) B7222553
theorem B3210023 : Blo 1901435 3210023 := bstep (se 1 (by rfl) ⟨2407517, by rfl⟩ : syracuseStep 3210023 = 4815035) B4815035
theorem B2140015 : Blo 1901435 2140015 := bstep (se 1 (by rfl) ⟨1605011, by rfl⟩ : syracuseStep 2140015 = 3210023) B3210023
theorem B2853353 : Blo 1901435 2853353 := bstep (se 2 (by rfl) ⟨1070007, by rfl⟩ : syracuseStep 2853353 = 2140015) B2140015
theorem B1902235 : Blo 1901435 1902235 := bstep (se 1 (by rfl) ⟨1426676, by rfl⟩ : syracuseStep 1902235 = 2853353) B2853353
theorem B6855797 : Blo 1901435 6855797 := bbase (se 5 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 6855797 = 642731) (by norm_num)
theorem B18282125 : Blo 1901435 18282125 := bstep (se 3 (by rfl) ⟨3427898, by rfl⟩ : syracuseStep 18282125 = 6855797) B6855797
theorem B12188083 : Blo 1901435 12188083 := bstep (se 1 (by rfl) ⟨9141062, by rfl⟩ : syracuseStep 12188083 = 18282125) B18282125
theorem B16250777 : Blo 1901435 16250777 := bstep (se 2 (by rfl) ⟨6094041, by rfl⟩ : syracuseStep 16250777 = 12188083) B12188083
theorem B10833851 : Blo 1901435 10833851 := bstep (se 1 (by rfl) ⟨8125388, by rfl⟩ : syracuseStep 10833851 = 16250777) B16250777
theorem B7222567 : Blo 1901435 7222567 := bstep (se 1 (by rfl) ⟨5416925, by rfl⟩ : syracuseStep 7222567 = 10833851) B10833851
theorem B9630089 : Blo 1901435 9630089 := bstep (se 2 (by rfl) ⟨3611283, by rfl⟩ : syracuseStep 9630089 = 7222567) B7222567
theorem B6420059 : Blo 1901435 6420059 := bstep (se 1 (by rfl) ⟨4815044, by rfl⟩ : syracuseStep 6420059 = 9630089) B9630089
theorem B4280039 : Blo 1901435 4280039 := bstep (se 1 (by rfl) ⟨3210029, by rfl⟩ : syracuseStep 4280039 = 6420059) B6420059
theorem B2853359 : Blo 1901435 2853359 := bstep (se 1 (by rfl) ⟨2140019, by rfl⟩ : syracuseStep 2853359 = 4280039) B4280039
theorem B1902239 : Blo 1901435 1902239 := bstep (se 1 (by rfl) ⟨1426679, by rfl⟩ : syracuseStep 1902239 = 2853359) B2853359
theorem B2853365 : Blo 1901435 2853365 := bbase (se 5 (by rfl) ⟨133751, by rfl⟩ : syracuseStep 2853365 = 267503) (by norm_num)
theorem B1902243 : Blo 1901435 1902243 := bstep (se 1 (by rfl) ⟨1426682, by rfl⟩ : syracuseStep 1902243 = 2853365) B2853365
theorem B5416949 : Blo 1901435 5416949 := bbase (se 5 (by rfl) ⟨253919, by rfl⟩ : syracuseStep 5416949 = 507839) (by norm_num)
theorem B3611299 : Blo 1901435 3611299 := bstep (se 1 (by rfl) ⟨2708474, by rfl⟩ : syracuseStep 3611299 = 5416949) B5416949
theorem B4815065 : Blo 1901435 4815065 := bstep (se 2 (by rfl) ⟨1805649, by rfl⟩ : syracuseStep 4815065 = 3611299) B3611299
theorem B3210043 : Blo 1901435 3210043 := bstep (se 1 (by rfl) ⟨2407532, by rfl⟩ : syracuseStep 3210043 = 4815065) B4815065
theorem B4280057 : Blo 1901435 4280057 := bstep (se 2 (by rfl) ⟨1605021, by rfl⟩ : syracuseStep 4280057 = 3210043) B3210043
theorem B2853371 : Blo 1901435 2853371 := bstep (se 1 (by rfl) ⟨2140028, by rfl⟩ : syracuseStep 2853371 = 4280057) B4280057
theorem B1902247 : Blo 1901435 1902247 := bstep (se 1 (by rfl) ⟨1426685, by rfl⟩ : syracuseStep 1902247 = 2853371) B2853371
theorem B2140033 : Blo 1901435 2140033 := bbase (se 2 (by rfl) ⟨802512, by rfl⟩ : syracuseStep 2140033 = 1605025) (by norm_num)
theorem B2853377 : Blo 1901435 2853377 := bstep (se 2 (by rfl) ⟨1070016, by rfl⟩ : syracuseStep 2853377 = 2140033) B2140033
theorem B1902251 : Blo 1901435 1902251 := bstep (se 1 (by rfl) ⟨1426688, by rfl⟩ : syracuseStep 1902251 = 2853377) B2853377
theorem B4815085 : Blo 1901435 4815085 := bbase (se 3 (by rfl) ⟨902828, by rfl⟩ : syracuseStep 4815085 = 1805657) (by norm_num)
theorem B6420113 : Blo 1901435 6420113 := bstep (se 2 (by rfl) ⟨2407542, by rfl⟩ : syracuseStep 6420113 = 4815085) B4815085
theorem B4280075 : Blo 1901435 4280075 := bstep (se 1 (by rfl) ⟨3210056, by rfl⟩ : syracuseStep 4280075 = 6420113) B6420113
theorem B2853383 : Blo 1901435 2853383 := bstep (se 1 (by rfl) ⟨2140037, by rfl⟩ : syracuseStep 2853383 = 4280075) B4280075
theorem B1902255 : Blo 1901435 1902255 := bstep (se 1 (by rfl) ⟨1426691, by rfl⟩ : syracuseStep 1902255 = 2853383) B2853383
theorem B2853389 : Blo 1901435 2853389 := bbase (se 3 (by rfl) ⟨535010, by rfl⟩ : syracuseStep 2853389 = 1070021) (by norm_num)
theorem B1902259 : Blo 1901435 1902259 := bstep (se 1 (by rfl) ⟨1426694, by rfl⟩ : syracuseStep 1902259 = 2853389) B2853389
theorem B4280093 : Blo 1901435 4280093 := bbase (se 3 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 4280093 = 1605035) (by norm_num)
theorem B2853395 : Blo 1901435 2853395 := bstep (se 1 (by rfl) ⟨2140046, by rfl⟩ : syracuseStep 2853395 = 4280093) B4280093
theorem B1902263 : Blo 1901435 1902263 := bstep (se 1 (by rfl) ⟨1426697, by rfl⟩ : syracuseStep 1902263 = 2853395) B2853395
theorem B3210077 : Blo 1901435 3210077 := bbase (se 3 (by rfl) ⟨601889, by rfl⟩ : syracuseStep 3210077 = 1203779) (by norm_num)
theorem B2140051 : Blo 1901435 2140051 := bstep (se 1 (by rfl) ⟨1605038, by rfl⟩ : syracuseStep 2140051 = 3210077) B3210077
theorem B2853401 : Blo 1901435 2853401 := bstep (se 2 (by rfl) ⟨1070025, by rfl⟩ : syracuseStep 2853401 = 2140051) B2140051
theorem B1902267 : Blo 1901435 1902267 := bstep (se 1 (by rfl) ⟨1426700, by rfl⟩ : syracuseStep 1902267 = 2853401) B2853401
theorem B8125525 : Blo 1901435 8125525 := bbase (se 8 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 8125525 = 95221) (by norm_num)
theorem B10834033 : Blo 1901435 10834033 := bstep (se 2 (by rfl) ⟨4062762, by rfl⟩ : syracuseStep 10834033 = 8125525) B8125525
theorem B14445377 : Blo 1901435 14445377 := bstep (se 2 (by rfl) ⟨5417016, by rfl⟩ : syracuseStep 14445377 = 10834033) B10834033
theorem B9630251 : Blo 1901435 9630251 := bstep (se 1 (by rfl) ⟨7222688, by rfl⟩ : syracuseStep 9630251 = 14445377) B14445377
theorem B6420167 : Blo 1901435 6420167 := bstep (se 1 (by rfl) ⟨4815125, by rfl⟩ : syracuseStep 6420167 = 9630251) B9630251
theorem B4280111 : Blo 1901435 4280111 := bstep (se 1 (by rfl) ⟨3210083, by rfl⟩ : syracuseStep 4280111 = 6420167) B6420167
theorem B2853407 : Blo 1901435 2853407 := bstep (se 1 (by rfl) ⟨2140055, by rfl⟩ : syracuseStep 2853407 = 4280111) B4280111
theorem B1902271 : Blo 1901435 1902271 := bstep (se 1 (by rfl) ⟨1426703, by rfl⟩ : syracuseStep 1902271 = 2853407) B2853407
theorem B2853413 : Blo 1901435 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B1902275 : Blo 1901435 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B2407573 : Blo 1901435 2407573 := bbase (se 6 (by rfl) ⟨56427, by rfl⟩ : syracuseStep 2407573 = 112855) (by norm_num)
theorem B3210097 : Blo 1901435 3210097 := bstep (se 2 (by rfl) ⟨1203786, by rfl⟩ : syracuseStep 3210097 = 2407573) B2407573
theorem B4280129 : Blo 1901435 4280129 := bstep (se 2 (by rfl) ⟨1605048, by rfl⟩ : syracuseStep 4280129 = 3210097) B3210097
theorem B2853419 : Blo 1901435 2853419 := bstep (se 1 (by rfl) ⟨2140064, by rfl⟩ : syracuseStep 2853419 = 4280129) B4280129
theorem B1902279 : Blo 1901435 1902279 := bstep (se 1 (by rfl) ⟨1426709, by rfl⟩ : syracuseStep 1902279 = 2853419) B2853419
theorem B2140069 : Blo 1901435 2140069 := bbase (se 4 (by rfl) ⟨200631, by rfl⟩ : syracuseStep 2140069 = 401263) (by norm_num)
theorem B2853425 : Blo 1901435 2853425 := bstep (se 2 (by rfl) ⟨1070034, by rfl⟩ : syracuseStep 2853425 = 2140069) B2140069
theorem B1902283 : Blo 1901435 1902283 := bstep (se 1 (by rfl) ⟨1426712, by rfl⟩ : syracuseStep 1902283 = 2853425) B2853425
theorem B2198869 : Blo 1901435 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B46909205 : Blo 1901435 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B31272803 : Blo 1901435 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B20848535 : Blo 1901435 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B13899023 : Blo 1901435 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B9266015 : Blo 1901435 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B24709373 : Blo 1901435 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B16472915 : Blo 1901435 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B10981943 : Blo 1901435 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B7321295 : Blo 1901435 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B4880863 : Blo 1901435 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B26031269 : Blo 1901435 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B17354179 : Blo 1901435 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B23138905 : Blo 1901435 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B30851873 : Blo 1901435 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B20567915 : Blo 1901435 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B13711943 : Blo 1901435 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B9141295 : Blo 1901435 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B12188393 : Blo 1901435 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B8125595 : Blo 1901435 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B5417063 : Blo 1901435 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B3611375 : Blo 1901435 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B2407583 : Blo 1901435 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B6420221 : Blo 1901435 6420221 := bstep (se 3 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 6420221 = 2407583) B2407583
theorem B4280147 : Blo 1901435 4280147 := bstep (se 1 (by rfl) ⟨3210110, by rfl⟩ : syracuseStep 4280147 = 6420221) B6420221
theorem B2853431 : Blo 1901435 2853431 := bstep (se 1 (by rfl) ⟨2140073, by rfl⟩ : syracuseStep 2853431 = 4280147) B4280147
theorem B1902287 : Blo 1901435 1902287 := bstep (se 1 (by rfl) ⟨1426715, by rfl⟩ : syracuseStep 1902287 = 2853431) B2853431
theorem B2853437 : Blo 1901435 2853437 := bbase (se 3 (by rfl) ⟨535019, by rfl⟩ : syracuseStep 2853437 = 1070039) (by norm_num)
theorem B1902291 : Blo 1901435 1902291 := bstep (se 1 (by rfl) ⟨1426718, by rfl⟩ : syracuseStep 1902291 = 2853437) B2853437
theorem B4280165 : Blo 1901435 4280165 := bbase (se 4 (by rfl) ⟨401265, by rfl⟩ : syracuseStep 4280165 = 802531) (by norm_num)
theorem B2853443 : Blo 1901435 2853443 := bstep (se 1 (by rfl) ⟨2140082, by rfl⟩ : syracuseStep 2853443 = 4280165) B4280165
theorem B1902295 : Blo 1901435 1902295 := bstep (se 1 (by rfl) ⟨1426721, by rfl⟩ : syracuseStep 1902295 = 2853443) B2853443
theorem B4815197 : Blo 1901435 4815197 := bbase (se 3 (by rfl) ⟨902849, by rfl⟩ : syracuseStep 4815197 = 1805699) (by norm_num)
theorem B3210131 : Blo 1901435 3210131 := bstep (se 1 (by rfl) ⟨2407598, by rfl⟩ : syracuseStep 3210131 = 4815197) B4815197
theorem B2140087 : Blo 1901435 2140087 := bstep (se 1 (by rfl) ⟨1605065, by rfl⟩ : syracuseStep 2140087 = 3210131) B3210131
theorem B2853449 : Blo 1901435 2853449 := bstep (se 2 (by rfl) ⟨1070043, by rfl⟩ : syracuseStep 2853449 = 2140087) B2140087
theorem B1902299 : Blo 1901435 1902299 := bstep (se 1 (by rfl) ⟨1426724, by rfl⟩ : syracuseStep 1902299 = 2853449) B2853449
theorem B3611405 : Blo 1901435 3611405 := bbase (se 3 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 3611405 = 1354277) (by norm_num)
theorem B9630413 : Blo 1901435 9630413 := bstep (se 3 (by rfl) ⟨1805702, by rfl⟩ : syracuseStep 9630413 = 3611405) B3611405
theorem B6420275 : Blo 1901435 6420275 := bstep (se 1 (by rfl) ⟨4815206, by rfl⟩ : syracuseStep 6420275 = 9630413) B9630413
theorem B4280183 : Blo 1901435 4280183 := bstep (se 1 (by rfl) ⟨3210137, by rfl⟩ : syracuseStep 4280183 = 6420275) B6420275
theorem B2853455 : Blo 1901435 2853455 := bstep (se 1 (by rfl) ⟨2140091, by rfl⟩ : syracuseStep 2853455 = 4280183) B4280183
theorem B1902303 : Blo 1901435 1902303 := bstep (se 1 (by rfl) ⟨1426727, by rfl⟩ : syracuseStep 1902303 = 2853455) B2853455
theorem B2853461 : Blo 1901435 2853461 := bbase (se 8 (by rfl) ⟨16719, by rfl⟩ : syracuseStep 2853461 = 33439) (by norm_num)
theorem B1902307 : Blo 1901435 1902307 := bstep (se 1 (by rfl) ⟨1426730, by rfl⟩ : syracuseStep 1902307 = 2853461) B2853461
theorem B3428029 : Blo 1901435 3428029 := bbase (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) (by norm_num)
theorem B4570705 : Blo 1901435 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B6094273 : Blo 1901435 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B8125697 : Blo 1901435 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B5417131 : Blo 1901435 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B7222841 : Blo 1901435 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B4815227 : Blo 1901435 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B3210151 : Blo 1901435 3210151 := bstep (se 1 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 3210151 = 4815227) B4815227
theorem B4280201 : Blo 1901435 4280201 := bstep (se 2 (by rfl) ⟨1605075, by rfl⟩ : syracuseStep 4280201 = 3210151) B3210151
theorem B2853467 : Blo 1901435 2853467 := bstep (se 1 (by rfl) ⟨2140100, by rfl⟩ : syracuseStep 2853467 = 4280201) B4280201
theorem B1902311 : Blo 1901435 1902311 := bstep (se 1 (by rfl) ⟨1426733, by rfl⟩ : syracuseStep 1902311 = 2853467) B2853467
theorem B2140105 : Blo 1901435 2140105 := bbase (se 2 (by rfl) ⟨802539, by rfl⟩ : syracuseStep 2140105 = 1605079) (by norm_num)
theorem B2853473 : Blo 1901435 2853473 := bstep (se 2 (by rfl) ⟨1070052, by rfl⟩ : syracuseStep 2853473 = 2140105) B2140105
theorem B1902315 : Blo 1901435 1902315 := bstep (se 1 (by rfl) ⟨1426736, by rfl⟩ : syracuseStep 1902315 = 2853473) B2853473
theorem B3047149 : Blo 1901435 3047149 := bbase (se 3 (by rfl) ⟨571340, by rfl⟩ : syracuseStep 3047149 = 1142681) (by norm_num)
theorem B16251461 : Blo 1901435 16251461 := bstep (se 4 (by rfl) ⟨1523574, by rfl⟩ : syracuseStep 16251461 = 3047149) B3047149
theorem B10834307 : Blo 1901435 10834307 := bstep (se 1 (by rfl) ⟨8125730, by rfl⟩ : syracuseStep 10834307 = 16251461) B16251461
theorem B7222871 : Blo 1901435 7222871 := bstep (se 1 (by rfl) ⟨5417153, by rfl⟩ : syracuseStep 7222871 = 10834307) B10834307
theorem B4815247 : Blo 1901435 4815247 := bstep (se 1 (by rfl) ⟨3611435, by rfl⟩ : syracuseStep 4815247 = 7222871) B7222871
theorem B6420329 : Blo 1901435 6420329 := bstep (se 2 (by rfl) ⟨2407623, by rfl⟩ : syracuseStep 6420329 = 4815247) B4815247
theorem B4280219 : Blo 1901435 4280219 := bstep (se 1 (by rfl) ⟨3210164, by rfl⟩ : syracuseStep 4280219 = 6420329) B6420329
theorem B2853479 : Blo 1901435 2853479 := bstep (se 1 (by rfl) ⟨2140109, by rfl⟩ : syracuseStep 2853479 = 4280219) B4280219
theorem B1902319 : Blo 1901435 1902319 := bstep (se 1 (by rfl) ⟨1426739, by rfl⟩ : syracuseStep 1902319 = 2853479) B2853479
theorem B2853485 : Blo 1901435 2853485 := bbase (se 3 (by rfl) ⟨535028, by rfl⟩ : syracuseStep 2853485 = 1070057) (by norm_num)
theorem B1902323 : Blo 1901435 1902323 := bstep (se 1 (by rfl) ⟨1426742, by rfl⟩ : syracuseStep 1902323 = 2853485) B2853485
theorem B4280237 : Blo 1901435 4280237 := bbase (se 3 (by rfl) ⟨802544, by rfl⟩ : syracuseStep 4280237 = 1605089) (by norm_num)
theorem B2853491 : Blo 1901435 2853491 := bstep (se 1 (by rfl) ⟨2140118, by rfl⟩ : syracuseStep 2853491 = 4280237) B4280237
theorem B1902327 : Blo 1901435 1902327 := bstep (se 1 (by rfl) ⟨1426745, by rfl⟩ : syracuseStep 1902327 = 2853491) B2853491
theorem B5417189 : Blo 1901435 5417189 := bbase (se 4 (by rfl) ⟨507861, by rfl⟩ : syracuseStep 5417189 = 1015723) (by norm_num)
theorem B3611459 : Blo 1901435 3611459 := bstep (se 1 (by rfl) ⟨2708594, by rfl⟩ : syracuseStep 3611459 = 5417189) B5417189
theorem B2407639 : Blo 1901435 2407639 := bstep (se 1 (by rfl) ⟨1805729, by rfl⟩ : syracuseStep 2407639 = 3611459) B3611459
theorem B3210185 : Blo 1901435 3210185 := bstep (se 2 (by rfl) ⟨1203819, by rfl⟩ : syracuseStep 3210185 = 2407639) B2407639
theorem B2140123 : Blo 1901435 2140123 := bstep (se 1 (by rfl) ⟨1605092, by rfl⟩ : syracuseStep 2140123 = 3210185) B3210185
theorem B2853497 : Blo 1901435 2853497 := bstep (se 2 (by rfl) ⟨1070061, by rfl⟩ : syracuseStep 2853497 = 2140123) B2140123
theorem B1902331 : Blo 1901435 1902331 := bstep (se 1 (by rfl) ⟨1426748, by rfl⟩ : syracuseStep 1902331 = 2853497) B2853497
theorem B5491109 : Blo 1901435 5491109 := bbase (se 4 (by rfl) ⟨514791, by rfl⟩ : syracuseStep 5491109 = 1029583) (by norm_num)
theorem B14642957 : Blo 1901435 14642957 := bstep (se 3 (by rfl) ⟨2745554, by rfl⟩ : syracuseStep 14642957 = 5491109) B5491109
theorem B9761971 : Blo 1901435 9761971 := bstep (se 1 (by rfl) ⟨7321478, by rfl⟩ : syracuseStep 9761971 = 14642957) B14642957
theorem B13015961 : Blo 1901435 13015961 := bstep (se 2 (by rfl) ⟨4880985, by rfl⟩ : syracuseStep 13015961 = 9761971) B9761971
theorem B8677307 : Blo 1901435 8677307 := bstep (se 1 (by rfl) ⟨6507980, by rfl⟩ : syracuseStep 8677307 = 13015961) B13015961
theorem B5784871 : Blo 1901435 5784871 := bstep (se 1 (by rfl) ⟨4338653, by rfl⟩ : syracuseStep 5784871 = 8677307) B8677307
theorem B7713161 : Blo 1901435 7713161 := bstep (se 2 (by rfl) ⟨2892435, by rfl⟩ : syracuseStep 7713161 = 5784871) B5784871
theorem B5142107 : Blo 1901435 5142107 := bstep (se 1 (by rfl) ⟨3856580, by rfl⟩ : syracuseStep 5142107 = 7713161) B7713161
theorem B13712285 : Blo 1901435 13712285 := bstep (se 3 (by rfl) ⟨2571053, by rfl⟩ : syracuseStep 13712285 = 5142107) B5142107
theorem B36566093 : Blo 1901435 36566093 := bstep (se 3 (by rfl) ⟨6856142, by rfl⟩ : syracuseStep 36566093 = 13712285) B13712285
theorem B24377395 : Blo 1901435 24377395 := bstep (se 1 (by rfl) ⟨18283046, by rfl⟩ : syracuseStep 24377395 = 36566093) B36566093
theorem B32503193 : Blo 1901435 32503193 := bstep (se 2 (by rfl) ⟨12188697, by rfl⟩ : syracuseStep 32503193 = 24377395) B24377395
theorem B21668795 : Blo 1901435 21668795 := bstep (se 1 (by rfl) ⟨16251596, by rfl⟩ : syracuseStep 21668795 = 32503193) B32503193
theorem B14445863 : Blo 1901435 14445863 := bstep (se 1 (by rfl) ⟨10834397, by rfl⟩ : syracuseStep 14445863 = 21668795) B21668795
theorem B9630575 : Blo 1901435 9630575 := bstep (se 1 (by rfl) ⟨7222931, by rfl⟩ : syracuseStep 9630575 = 14445863) B14445863
theorem B6420383 : Blo 1901435 6420383 := bstep (se 1 (by rfl) ⟨4815287, by rfl⟩ : syracuseStep 6420383 = 9630575) B9630575
theorem B4280255 : Blo 1901435 4280255 := bstep (se 1 (by rfl) ⟨3210191, by rfl⟩ : syracuseStep 4280255 = 6420383) B6420383
theorem B2853503 : Blo 1901435 2853503 := bstep (se 1 (by rfl) ⟨2140127, by rfl⟩ : syracuseStep 2853503 = 4280255) B4280255
theorem B1902335 : Blo 1901435 1902335 := bstep (se 1 (by rfl) ⟨1426751, by rfl⟩ : syracuseStep 1902335 = 2853503) B2853503
theorem B2853509 : Blo 1901435 2853509 := bbase (se 4 (by rfl) ⟨267516, by rfl⟩ : syracuseStep 2853509 = 535033) (by norm_num)
theorem B1902339 : Blo 1901435 1902339 := bstep (se 1 (by rfl) ⟨1426754, by rfl⟩ : syracuseStep 1902339 = 2853509) B2853509
theorem B3210205 : Blo 1901435 3210205 := bbase (se 3 (by rfl) ⟨601913, by rfl⟩ : syracuseStep 3210205 = 1203827) (by norm_num)
theorem B4280273 : Blo 1901435 4280273 := bstep (se 2 (by rfl) ⟨1605102, by rfl⟩ : syracuseStep 4280273 = 3210205) B3210205
theorem B2853515 : Blo 1901435 2853515 := bstep (se 1 (by rfl) ⟨2140136, by rfl⟩ : syracuseStep 2853515 = 4280273) B4280273
theorem B1902343 : Blo 1901435 1902343 := bstep (se 1 (by rfl) ⟨1426757, by rfl⟩ : syracuseStep 1902343 = 2853515) B2853515
theorem B2140141 : Blo 1901435 2140141 := bbase (se 3 (by rfl) ⟨401276, by rfl⟩ : syracuseStep 2140141 = 802553) (by norm_num)
theorem B2853521 : Blo 1901435 2853521 := bstep (se 2 (by rfl) ⟨1070070, by rfl⟩ : syracuseStep 2853521 = 2140141) B2140141
theorem B1902347 : Blo 1901435 1902347 := bstep (se 1 (by rfl) ⟨1426760, by rfl⟩ : syracuseStep 1902347 = 2853521) B2853521
theorem B6420437 : Blo 1901435 6420437 := bbase (se 7 (by rfl) ⟨75239, by rfl⟩ : syracuseStep 6420437 = 150479) (by norm_num)
theorem B4280291 : Blo 1901435 4280291 := bstep (se 1 (by rfl) ⟨3210218, by rfl⟩ : syracuseStep 4280291 = 6420437) B6420437
theorem B2853527 : Blo 1901435 2853527 := bstep (se 1 (by rfl) ⟨2140145, by rfl⟩ : syracuseStep 2853527 = 4280291) B4280291
theorem B1902351 : Blo 1901435 1902351 := bstep (se 1 (by rfl) ⟨1426763, by rfl⟩ : syracuseStep 1902351 = 2853527) B2853527
theorem B2853533 : Blo 1901435 2853533 := bbase (se 3 (by rfl) ⟨535037, by rfl⟩ : syracuseStep 2853533 = 1070075) (by norm_num)
theorem B1902355 : Blo 1901435 1902355 := bstep (se 1 (by rfl) ⟨1426766, by rfl⟩ : syracuseStep 1902355 = 2853533) B2853533
theorem B4280309 : Blo 1901435 4280309 := bbase (se 5 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 4280309 = 401279) (by norm_num)
theorem B2853539 : Blo 1901435 2853539 := bstep (se 1 (by rfl) ⟨2140154, by rfl⟩ : syracuseStep 2853539 = 4280309) B4280309
theorem B1902359 : Blo 1901435 1902359 := bstep (se 1 (by rfl) ⟨1426769, by rfl⟩ : syracuseStep 1902359 = 2853539) B2853539
theorem B6261877 : Blo 1901435 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B8349169 : Blo 1901435 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B11132225 : Blo 1901435 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B7421483 : Blo 1901435 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B4947655 : Blo 1901435 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B6596873 : Blo 1901435 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B4397915 : Blo 1901435 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B11727773 : Blo 1901435 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B7818515 : Blo 1901435 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B5212343 : Blo 1901435 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B3474895 : Blo 1901435 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B4633193 : Blo 1901435 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B3088795 : Blo 1901435 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B4118393 : Blo 1901435 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2745595 : Blo 1901435 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B3660793 : Blo 1901435 3660793 := bstep (se 2 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 3660793 = 2745595) B2745595
theorem B19524229 : Blo 1901435 19524229 := bstep (se 4 (by rfl) ⟨1830396, by rfl⟩ : syracuseStep 19524229 = 3660793) B3660793
theorem B104129221 : Blo 1901435 104129221 := bstep (se 4 (by rfl) ⟨9762114, by rfl⟩ : syracuseStep 104129221 = 19524229) B19524229
theorem B138838961 : Blo 1901435 138838961 := bstep (se 2 (by rfl) ⟨52064610, by rfl⟩ : syracuseStep 138838961 = 104129221) B104129221
theorem B92559307 : Blo 1901435 92559307 := bstep (se 1 (by rfl) ⟨69419480, by rfl⟩ : syracuseStep 92559307 = 138838961) B138838961
theorem B123412409 : Blo 1901435 123412409 := bstep (se 2 (by rfl) ⟨46279653, by rfl⟩ : syracuseStep 123412409 = 92559307) B92559307
theorem B82274939 : Blo 1901435 82274939 := bstep (se 1 (by rfl) ⟨61706204, by rfl⟩ : syracuseStep 82274939 = 123412409) B123412409
theorem B54849959 : Blo 1901435 54849959 := bstep (se 1 (by rfl) ⟨41137469, by rfl⟩ : syracuseStep 54849959 = 82274939) B82274939
theorem B36566639 : Blo 1901435 36566639 := bstep (se 1 (by rfl) ⟨27424979, by rfl⟩ : syracuseStep 36566639 = 54849959) B54849959
theorem B24377759 : Blo 1901435 24377759 := bstep (se 1 (by rfl) ⟨18283319, by rfl⟩ : syracuseStep 24377759 = 36566639) B36566639
theorem B16251839 : Blo 1901435 16251839 := bstep (se 1 (by rfl) ⟨12188879, by rfl⟩ : syracuseStep 16251839 = 24377759) B24377759
theorem B10834559 : Blo 1901435 10834559 := bstep (se 1 (by rfl) ⟨8125919, by rfl⟩ : syracuseStep 10834559 = 16251839) B16251839
theorem B7223039 : Blo 1901435 7223039 := bstep (se 1 (by rfl) ⟨5417279, by rfl⟩ : syracuseStep 7223039 = 10834559) B10834559
theorem B4815359 : Blo 1901435 4815359 := bstep (se 1 (by rfl) ⟨3611519, by rfl⟩ : syracuseStep 4815359 = 7223039) B7223039
theorem B3210239 : Blo 1901435 3210239 := bstep (se 1 (by rfl) ⟨2407679, by rfl⟩ : syracuseStep 3210239 = 4815359) B4815359
theorem B2140159 : Blo 1901435 2140159 := bstep (se 1 (by rfl) ⟨1605119, by rfl⟩ : syracuseStep 2140159 = 3210239) B3210239
theorem B2853545 : Blo 1901435 2853545 := bstep (se 2 (by rfl) ⟨1070079, by rfl⟩ : syracuseStep 2853545 = 2140159) B2140159
theorem B1902363 : Blo 1901435 1902363 := bstep (se 1 (by rfl) ⟨1426772, by rfl⟩ : syracuseStep 1902363 = 2853545) B2853545
theorem B2708645 : Blo 1901435 2708645 := bbase (se 4 (by rfl) ⟨253935, by rfl⟩ : syracuseStep 2708645 = 507871) (by norm_num)
theorem B7223053 : Blo 1901435 7223053 := bstep (se 3 (by rfl) ⟨1354322, by rfl⟩ : syracuseStep 7223053 = 2708645) B2708645
theorem B9630737 : Blo 1901435 9630737 := bstep (se 2 (by rfl) ⟨3611526, by rfl⟩ : syracuseStep 9630737 = 7223053) B7223053
theorem B6420491 : Blo 1901435 6420491 := bstep (se 1 (by rfl) ⟨4815368, by rfl⟩ : syracuseStep 6420491 = 9630737) B9630737
theorem B4280327 : Blo 1901435 4280327 := bstep (se 1 (by rfl) ⟨3210245, by rfl⟩ : syracuseStep 4280327 = 6420491) B6420491
theorem B2853551 : Blo 1901435 2853551 := bstep (se 1 (by rfl) ⟨2140163, by rfl⟩ : syracuseStep 2853551 = 4280327) B4280327
theorem B1902367 : Blo 1901435 1902367 := bstep (se 1 (by rfl) ⟨1426775, by rfl⟩ : syracuseStep 1902367 = 2853551) B2853551
theorem B2853557 : Blo 1901435 2853557 := bbase (se 5 (by rfl) ⟨133760, by rfl⟩ : syracuseStep 2853557 = 267521) (by norm_num)
theorem B1902371 : Blo 1901435 1902371 := bstep (se 1 (by rfl) ⟨1426778, by rfl⟩ : syracuseStep 1902371 = 2853557) B2853557
theorem B4815389 : Blo 1901435 4815389 := bbase (se 3 (by rfl) ⟨902885, by rfl⟩ : syracuseStep 4815389 = 1805771) (by norm_num)
theorem B3210259 : Blo 1901435 3210259 := bstep (se 1 (by rfl) ⟨2407694, by rfl⟩ : syracuseStep 3210259 = 4815389) B4815389
theorem B4280345 : Blo 1901435 4280345 := bstep (se 2 (by rfl) ⟨1605129, by rfl⟩ : syracuseStep 4280345 = 3210259) B3210259
theorem B2853563 : Blo 1901435 2853563 := bstep (se 1 (by rfl) ⟨2140172, by rfl⟩ : syracuseStep 2853563 = 4280345) B4280345
theorem B1902375 : Blo 1901435 1902375 := bstep (se 1 (by rfl) ⟨1426781, by rfl⟩ : syracuseStep 1902375 = 2853563) B2853563
theorem B2140177 : Blo 1901435 2140177 := bbase (se 2 (by rfl) ⟨802566, by rfl⟩ : syracuseStep 2140177 = 1605133) (by norm_num)
theorem B2853569 : Blo 1901435 2853569 := bstep (se 2 (by rfl) ⟨1070088, by rfl⟩ : syracuseStep 2853569 = 2140177) B2140177
theorem B1902379 : Blo 1901435 1902379 := bstep (se 1 (by rfl) ⟨1426784, by rfl⟩ : syracuseStep 1902379 = 2853569) B2853569
theorem B3611557 : Blo 1901435 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B4815409 : Blo 1901435 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B6420545 : Blo 1901435 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B4280363 : Blo 1901435 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B2853575 : Blo 1901435 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B1902383 : Blo 1901435 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B2853581 : Blo 1901435 2853581 := bbase (se 3 (by rfl) ⟨535046, by rfl⟩ : syracuseStep 2853581 = 1070093) (by norm_num)
theorem B1902387 : Blo 1901435 1902387 := bstep (se 1 (by rfl) ⟨1426790, by rfl⟩ : syracuseStep 1902387 = 2853581) B2853581
theorem B4280381 : Blo 1901435 4280381 := bbase (se 3 (by rfl) ⟨802571, by rfl⟩ : syracuseStep 4280381 = 1605143) (by norm_num)
theorem B2853587 : Blo 1901435 2853587 := bstep (se 1 (by rfl) ⟨2140190, by rfl⟩ : syracuseStep 2853587 = 4280381) B4280381
theorem B1902391 : Blo 1901435 1902391 := bstep (se 1 (by rfl) ⟨1426793, by rfl⟩ : syracuseStep 1902391 = 2853587) B2853587
theorem B3210293 : Blo 1901435 3210293 := bbase (se 5 (by rfl) ⟨150482, by rfl⟩ : syracuseStep 3210293 = 300965) (by norm_num)
theorem B2140195 : Blo 1901435 2140195 := bstep (se 1 (by rfl) ⟨1605146, by rfl⟩ : syracuseStep 2140195 = 3210293) B3210293
theorem B2853593 : Blo 1901435 2853593 := bstep (se 2 (by rfl) ⟨1070097, by rfl⟩ : syracuseStep 2853593 = 2140195) B2140195
theorem B1902395 : Blo 1901435 1902395 := bstep (se 1 (by rfl) ⟨1426796, by rfl⟩ : syracuseStep 1902395 = 2853593) B2853593
theorem B5417381 : Blo 1901435 5417381 := bbase (se 4 (by rfl) ⟨507879, by rfl⟩ : syracuseStep 5417381 = 1015759) (by norm_num)
theorem B14446349 : Blo 1901435 14446349 := bstep (se 3 (by rfl) ⟨2708690, by rfl⟩ : syracuseStep 14446349 = 5417381) B5417381
theorem B9630899 : Blo 1901435 9630899 := bstep (se 1 (by rfl) ⟨7223174, by rfl⟩ : syracuseStep 9630899 = 14446349) B14446349
theorem B6420599 : Blo 1901435 6420599 := bstep (se 1 (by rfl) ⟨4815449, by rfl⟩ : syracuseStep 6420599 = 9630899) B9630899
theorem B4280399 : Blo 1901435 4280399 := bstep (se 1 (by rfl) ⟨3210299, by rfl⟩ : syracuseStep 4280399 = 6420599) B6420599
theorem B2853599 : Blo 1901435 2853599 := bstep (se 1 (by rfl) ⟨2140199, by rfl⟩ : syracuseStep 2853599 = 4280399) B4280399
theorem B1902399 : Blo 1901435 1902399 := bstep (se 1 (by rfl) ⟨1426799, by rfl⟩ : syracuseStep 1902399 = 2853599) B2853599
theorem B2853605 : Blo 1901435 2853605 := bbase (se 4 (by rfl) ⟨267525, by rfl⟩ : syracuseStep 2853605 = 535051) (by norm_num)
theorem B1902403 : Blo 1901435 1902403 := bstep (se 1 (by rfl) ⟨1426802, by rfl⟩ : syracuseStep 1902403 = 2853605) B2853605
theorem B4338821 : Blo 1901435 4338821 := bbase (se 4 (by rfl) ⟨406764, by rfl⟩ : syracuseStep 4338821 = 813529) (by norm_num)
theorem B2892547 : Blo 1901435 2892547 := bstep (se 1 (by rfl) ⟨2169410, by rfl⟩ : syracuseStep 2892547 = 4338821) B4338821
theorem B3856729 : Blo 1901435 3856729 := bstep (se 2 (by rfl) ⟨1446273, by rfl⟩ : syracuseStep 3856729 = 2892547) B2892547
theorem B5142305 : Blo 1901435 5142305 := bstep (se 2 (by rfl) ⟨1928364, by rfl⟩ : syracuseStep 5142305 = 3856729) B3856729
theorem B3428203 : Blo 1901435 3428203 := bstep (se 1 (by rfl) ⟨2571152, by rfl⟩ : syracuseStep 3428203 = 5142305) B5142305
theorem B4570937 : Blo 1901435 4570937 := bstep (se 2 (by rfl) ⟨1714101, by rfl⟩ : syracuseStep 4570937 = 3428203) B3428203
theorem B3047291 : Blo 1901435 3047291 := bstep (se 1 (by rfl) ⟨2285468, by rfl⟩ : syracuseStep 3047291 = 4570937) B4570937
theorem B2031527 : Blo 1901435 2031527 := bstep (se 1 (by rfl) ⟨1523645, by rfl⟩ : syracuseStep 2031527 = 3047291) B3047291
theorem B5417405 : Blo 1901435 5417405 := bstep (se 3 (by rfl) ⟨1015763, by rfl⟩ : syracuseStep 5417405 = 2031527) B2031527
theorem B3611603 : Blo 1901435 3611603 := bstep (se 1 (by rfl) ⟨2708702, by rfl⟩ : syracuseStep 3611603 = 5417405) B5417405
theorem B2407735 : Blo 1901435 2407735 := bstep (se 1 (by rfl) ⟨1805801, by rfl⟩ : syracuseStep 2407735 = 3611603) B3611603
theorem B3210313 : Blo 1901435 3210313 := bstep (se 2 (by rfl) ⟨1203867, by rfl⟩ : syracuseStep 3210313 = 2407735) B2407735
theorem B4280417 : Blo 1901435 4280417 := bstep (se 2 (by rfl) ⟨1605156, by rfl⟩ : syracuseStep 4280417 = 3210313) B3210313
theorem B2853611 : Blo 1901435 2853611 := bstep (se 1 (by rfl) ⟨2140208, by rfl⟩ : syracuseStep 2853611 = 4280417) B4280417
theorem B1902407 : Blo 1901435 1902407 := bstep (se 1 (by rfl) ⟨1426805, by rfl⟩ : syracuseStep 1902407 = 2853611) B2853611
theorem B2140213 : Blo 1901435 2140213 := bbase (se 5 (by rfl) ⟨100322, by rfl⟩ : syracuseStep 2140213 = 200645) (by norm_num)
theorem B2853617 : Blo 1901435 2853617 := bstep (se 2 (by rfl) ⟨1070106, by rfl⟩ : syracuseStep 2853617 = 2140213) B2140213
theorem B1902411 : Blo 1901435 1902411 := bstep (se 1 (by rfl) ⟨1426808, by rfl⟩ : syracuseStep 1902411 = 2853617) B2853617
theorem B2407745 : Blo 1901435 2407745 := bbase (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) (by norm_num)
theorem B6420653 : Blo 1901435 6420653 := bstep (se 3 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 6420653 = 2407745) B2407745
theorem B4280435 : Blo 1901435 4280435 := bstep (se 1 (by rfl) ⟨3210326, by rfl⟩ : syracuseStep 4280435 = 6420653) B6420653
theorem B2853623 : Blo 1901435 2853623 := bstep (se 1 (by rfl) ⟨2140217, by rfl⟩ : syracuseStep 2853623 = 4280435) B4280435
theorem B1902415 : Blo 1901435 1902415 := bstep (se 1 (by rfl) ⟨1426811, by rfl⟩ : syracuseStep 1902415 = 2853623) B2853623
theorem B2853629 : Blo 1901435 2853629 := bbase (se 3 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 2853629 = 1070111) (by norm_num)
theorem B1902419 : Blo 1901435 1902419 := bstep (se 1 (by rfl) ⟨1426814, by rfl⟩ : syracuseStep 1902419 = 2853629) B2853629
theorem B4280453 : Blo 1901435 4280453 := bbase (se 4 (by rfl) ⟨401292, by rfl⟩ : syracuseStep 4280453 = 802585) (by norm_num)
theorem B2853635 : Blo 1901435 2853635 := bstep (se 1 (by rfl) ⟨2140226, by rfl⟩ : syracuseStep 2853635 = 4280453) B4280453
theorem B1902423 : Blo 1901435 1902423 := bstep (se 1 (by rfl) ⟨1426817, by rfl⟩ : syracuseStep 1902423 = 2853635) B2853635
theorem B2169433 : Blo 1901435 2169433 := bbase (se 2 (by rfl) ⟨813537, by rfl⟩ : syracuseStep 2169433 = 1627075) (by norm_num)
theorem B11570309 : Blo 1901435 11570309 := bstep (se 4 (by rfl) ⟨1084716, by rfl⟩ : syracuseStep 11570309 = 2169433) B2169433
theorem B7713539 : Blo 1901435 7713539 := bstep (se 1 (by rfl) ⟨5785154, by rfl⟩ : syracuseStep 7713539 = 11570309) B11570309
theorem B5142359 : Blo 1901435 5142359 := bstep (se 1 (by rfl) ⟨3856769, by rfl⟩ : syracuseStep 5142359 = 7713539) B7713539
theorem B3428239 : Blo 1901435 3428239 := bstep (se 1 (by rfl) ⟨2571179, by rfl⟩ : syracuseStep 3428239 = 5142359) B5142359
theorem B4570985 : Blo 1901435 4570985 := bstep (se 2 (by rfl) ⟨1714119, by rfl⟩ : syracuseStep 4570985 = 3428239) B3428239
theorem B3047323 : Blo 1901435 3047323 := bstep (se 1 (by rfl) ⟨2285492, by rfl⟩ : syracuseStep 3047323 = 4570985) B4570985
theorem B4063097 : Blo 1901435 4063097 := bstep (se 2 (by rfl) ⟨1523661, by rfl⟩ : syracuseStep 4063097 = 3047323) B3047323
theorem B2708731 : Blo 1901435 2708731 := bstep (se 1 (by rfl) ⟨2031548, by rfl⟩ : syracuseStep 2708731 = 4063097) B4063097
theorem B3611641 : Blo 1901435 3611641 := bstep (se 2 (by rfl) ⟨1354365, by rfl⟩ : syracuseStep 3611641 = 2708731) B2708731
theorem B4815521 : Blo 1901435 4815521 := bstep (se 2 (by rfl) ⟨1805820, by rfl⟩ : syracuseStep 4815521 = 3611641) B3611641
theorem B3210347 : Blo 1901435 3210347 := bstep (se 1 (by rfl) ⟨2407760, by rfl⟩ : syracuseStep 3210347 = 4815521) B4815521
theorem B2140231 : Blo 1901435 2140231 := bstep (se 1 (by rfl) ⟨1605173, by rfl⟩ : syracuseStep 2140231 = 3210347) B3210347
theorem B2853641 : Blo 1901435 2853641 := bstep (se 2 (by rfl) ⟨1070115, by rfl⟩ : syracuseStep 2853641 = 2140231) B2140231
theorem B1902427 : Blo 1901435 1902427 := bstep (se 1 (by rfl) ⟨1426820, by rfl⟩ : syracuseStep 1902427 = 2853641) B2853641
theorem B9631061 : Blo 1901435 9631061 := bbase (se 13 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 9631061 = 3527) (by norm_num)
theorem B6420707 : Blo 1901435 6420707 := bstep (se 1 (by rfl) ⟨4815530, by rfl⟩ : syracuseStep 6420707 = 9631061) B9631061
theorem B4280471 : Blo 1901435 4280471 := bstep (se 1 (by rfl) ⟨3210353, by rfl⟩ : syracuseStep 4280471 = 6420707) B6420707
theorem B2853647 : Blo 1901435 2853647 := bstep (se 1 (by rfl) ⟨2140235, by rfl⟩ : syracuseStep 2853647 = 4280471) B4280471
theorem B1902431 : Blo 1901435 1902431 := bstep (se 1 (by rfl) ⟨1426823, by rfl⟩ : syracuseStep 1902431 = 2853647) B2853647
theorem B2853653 : Blo 1901435 2853653 := bbase (se 6 (by rfl) ⟨66882, by rfl⟩ : syracuseStep 2853653 = 133765) (by norm_num)
theorem B1902435 : Blo 1901435 1902435 := bstep (se 1 (by rfl) ⟨1426826, by rfl⟩ : syracuseStep 1902435 = 2853653) B2853653
theorem B4118557 : Blo 1901435 4118557 := bbase (se 3 (by rfl) ⟨772229, by rfl⟩ : syracuseStep 4118557 = 1544459) (by norm_num)
theorem B5491409 : Blo 1901435 5491409 := bstep (se 2 (by rfl) ⟨2059278, by rfl⟩ : syracuseStep 5491409 = 4118557) B4118557
theorem B14643757 : Blo 1901435 14643757 := bstep (se 3 (by rfl) ⟨2745704, by rfl⟩ : syracuseStep 14643757 = 5491409) B5491409
theorem B19525009 : Blo 1901435 19525009 := bstep (se 2 (by rfl) ⟨7321878, by rfl⟩ : syracuseStep 19525009 = 14643757) B14643757
theorem B26033345 : Blo 1901435 26033345 := bstep (se 2 (by rfl) ⟨9762504, by rfl⟩ : syracuseStep 26033345 = 19525009) B19525009
theorem B17355563 : Blo 1901435 17355563 := bstep (se 1 (by rfl) ⟨13016672, by rfl⟩ : syracuseStep 17355563 = 26033345) B26033345
theorem B11570375 : Blo 1901435 11570375 := bstep (se 1 (by rfl) ⟨8677781, by rfl⟩ : syracuseStep 11570375 = 17355563) B17355563
theorem B30854333 : Blo 1901435 30854333 := bstep (se 3 (by rfl) ⟨5785187, by rfl⟩ : syracuseStep 30854333 = 11570375) B11570375
theorem B20569555 : Blo 1901435 20569555 := bstep (se 1 (by rfl) ⟨15427166, by rfl⟩ : syracuseStep 20569555 = 30854333) B30854333
theorem B27426073 : Blo 1901435 27426073 := bstep (se 2 (by rfl) ⟨10284777, by rfl⟩ : syracuseStep 27426073 = 20569555) B20569555
theorem B36568097 : Blo 1901435 36568097 := bstep (se 2 (by rfl) ⟨13713036, by rfl⟩ : syracuseStep 36568097 = 27426073) B27426073
theorem B24378731 : Blo 1901435 24378731 := bstep (se 1 (by rfl) ⟨18284048, by rfl⟩ : syracuseStep 24378731 = 36568097) B36568097
theorem B16252487 : Blo 1901435 16252487 := bstep (se 1 (by rfl) ⟨12189365, by rfl⟩ : syracuseStep 16252487 = 24378731) B24378731
theorem B10834991 : Blo 1901435 10834991 := bstep (se 1 (by rfl) ⟨8126243, by rfl⟩ : syracuseStep 10834991 = 16252487) B16252487
theorem B7223327 : Blo 1901435 7223327 := bstep (se 1 (by rfl) ⟨5417495, by rfl⟩ : syracuseStep 7223327 = 10834991) B10834991
theorem B4815551 : Blo 1901435 4815551 := bstep (se 1 (by rfl) ⟨3611663, by rfl⟩ : syracuseStep 4815551 = 7223327) B7223327
theorem B3210367 : Blo 1901435 3210367 := bstep (se 1 (by rfl) ⟨2407775, by rfl⟩ : syracuseStep 3210367 = 4815551) B4815551
theorem B4280489 : Blo 1901435 4280489 := bstep (se 2 (by rfl) ⟨1605183, by rfl⟩ : syracuseStep 4280489 = 3210367) B3210367
theorem B2853659 : Blo 1901435 2853659 := bstep (se 1 (by rfl) ⟨2140244, by rfl⟩ : syracuseStep 2853659 = 4280489) B4280489
theorem B1902439 : Blo 1901435 1902439 := bstep (se 1 (by rfl) ⟨1426829, by rfl⟩ : syracuseStep 1902439 = 2853659) B2853659
theorem B2140249 : Blo 1901435 2140249 := bbase (se 2 (by rfl) ⟨802593, by rfl⟩ : syracuseStep 2140249 = 1605187) (by norm_num)
theorem B2853665 : Blo 1901435 2853665 := bstep (se 2 (by rfl) ⟨1070124, by rfl⟩ : syracuseStep 2853665 = 2140249) B2140249
theorem B1902443 : Blo 1901435 1902443 := bstep (se 1 (by rfl) ⟨1426832, by rfl⟩ : syracuseStep 1902443 = 2853665) B2853665
theorem B6094709 : Blo 1901435 6094709 := bbase (se 5 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 6094709 = 571379) (by norm_num)
theorem B4063139 : Blo 1901435 4063139 := bstep (se 1 (by rfl) ⟨3047354, by rfl⟩ : syracuseStep 4063139 = 6094709) B6094709
theorem B2708759 : Blo 1901435 2708759 := bstep (se 1 (by rfl) ⟨2031569, by rfl⟩ : syracuseStep 2708759 = 4063139) B4063139
theorem B7223357 : Blo 1901435 7223357 := bstep (se 3 (by rfl) ⟨1354379, by rfl⟩ : syracuseStep 7223357 = 2708759) B2708759
theorem B4815571 : Blo 1901435 4815571 := bstep (se 1 (by rfl) ⟨3611678, by rfl⟩ : syracuseStep 4815571 = 7223357) B7223357
theorem B6420761 : Blo 1901435 6420761 := bstep (se 2 (by rfl) ⟨2407785, by rfl⟩ : syracuseStep 6420761 = 4815571) B4815571
theorem B4280507 : Blo 1901435 4280507 := bstep (se 1 (by rfl) ⟨3210380, by rfl⟩ : syracuseStep 4280507 = 6420761) B6420761
theorem B2853671 : Blo 1901435 2853671 := bstep (se 1 (by rfl) ⟨2140253, by rfl⟩ : syracuseStep 2853671 = 4280507) B4280507
theorem B1902447 : Blo 1901435 1902447 := bstep (se 1 (by rfl) ⟨1426835, by rfl⟩ : syracuseStep 1902447 = 2853671) B2853671
theorem B2853677 : Blo 1901435 2853677 := bbase (se 3 (by rfl) ⟨535064, by rfl⟩ : syracuseStep 2853677 = 1070129) (by norm_num)
theorem B1902451 : Blo 1901435 1902451 := bstep (se 1 (by rfl) ⟨1426838, by rfl⟩ : syracuseStep 1902451 = 2853677) B2853677
theorem B4280525 : Blo 1901435 4280525 := bbase (se 3 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 4280525 = 1605197) (by norm_num)
theorem B2853683 : Blo 1901435 2853683 := bstep (se 1 (by rfl) ⟨2140262, by rfl⟩ : syracuseStep 2853683 = 4280525) B4280525
theorem B1902455 : Blo 1901435 1902455 := bstep (se 1 (by rfl) ⟨1426841, by rfl⟩ : syracuseStep 1902455 = 2853683) B2853683
theorem B2407801 : Blo 1901435 2407801 := bbase (se 2 (by rfl) ⟨902925, by rfl⟩ : syracuseStep 2407801 = 1805851) (by norm_num)
theorem B3210401 : Blo 1901435 3210401 := bstep (se 2 (by rfl) ⟨1203900, by rfl⟩ : syracuseStep 3210401 = 2407801) B2407801
theorem B2140267 : Blo 1901435 2140267 := bstep (se 1 (by rfl) ⟨1605200, by rfl⟩ : syracuseStep 2140267 = 3210401) B3210401
theorem B2853689 : Blo 1901435 2853689 := bstep (se 2 (by rfl) ⟨1070133, by rfl⟩ : syracuseStep 2853689 = 2140267) B2140267
theorem B1902459 : Blo 1901435 1902459 := bstep (se 1 (by rfl) ⟨1426844, by rfl⟩ : syracuseStep 1902459 = 2853689) B2853689
theorem B2440657 : Blo 1901435 2440657 := bbase (se 2 (by rfl) ⟨915246, by rfl⟩ : syracuseStep 2440657 = 1830493) (by norm_num)
theorem B13016837 : Blo 1901435 13016837 := bstep (se 4 (by rfl) ⟨1220328, by rfl⟩ : syracuseStep 13016837 = 2440657) B2440657
theorem B8677891 : Blo 1901435 8677891 := bstep (se 1 (by rfl) ⟨6508418, by rfl⟩ : syracuseStep 8677891 = 13016837) B13016837
theorem B11570521 : Blo 1901435 11570521 := bstep (se 2 (by rfl) ⟨4338945, by rfl⟩ : syracuseStep 11570521 = 8677891) B8677891
theorem B15427361 : Blo 1901435 15427361 := bstep (se 2 (by rfl) ⟨5785260, by rfl⟩ : syracuseStep 15427361 = 11570521) B11570521
theorem B10284907 : Blo 1901435 10284907 := bstep (se 1 (by rfl) ⟨7713680, by rfl⟩ : syracuseStep 10284907 = 15427361) B15427361
theorem B13713209 : Blo 1901435 13713209 := bstep (se 2 (by rfl) ⟨5142453, by rfl⟩ : syracuseStep 13713209 = 10284907) B10284907
theorem B9142139 : Blo 1901435 9142139 := bstep (se 1 (by rfl) ⟨6856604, by rfl⟩ : syracuseStep 9142139 = 13713209) B13713209
theorem B6094759 : Blo 1901435 6094759 := bstep (se 1 (by rfl) ⟨4571069, by rfl⟩ : syracuseStep 6094759 = 9142139) B9142139
theorem B8126345 : Blo 1901435 8126345 := bstep (se 2 (by rfl) ⟨3047379, by rfl⟩ : syracuseStep 8126345 = 6094759) B6094759
theorem B21670253 : Blo 1901435 21670253 := bstep (se 3 (by rfl) ⟨4063172, by rfl⟩ : syracuseStep 21670253 = 8126345) B8126345
theorem B14446835 : Blo 1901435 14446835 := bstep (se 1 (by rfl) ⟨10835126, by rfl⟩ : syracuseStep 14446835 = 21670253) B21670253
theorem B9631223 : Blo 1901435 9631223 := bstep (se 1 (by rfl) ⟨7223417, by rfl⟩ : syracuseStep 9631223 = 14446835) B14446835
theorem B6420815 : Blo 1901435 6420815 := bstep (se 1 (by rfl) ⟨4815611, by rfl⟩ : syracuseStep 6420815 = 9631223) B9631223
theorem B4280543 : Blo 1901435 4280543 := bstep (se 1 (by rfl) ⟨3210407, by rfl⟩ : syracuseStep 4280543 = 6420815) B6420815
theorem B2853695 : Blo 1901435 2853695 := bstep (se 1 (by rfl) ⟨2140271, by rfl⟩ : syracuseStep 2853695 = 4280543) B4280543
theorem B1902463 : Blo 1901435 1902463 := bstep (se 1 (by rfl) ⟨1426847, by rfl⟩ : syracuseStep 1902463 = 2853695) B2853695
theorem B2853701 : Blo 1901435 2853701 := bbase (se 4 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 2853701 = 535069) (by norm_num)
theorem B1902467 : Blo 1901435 1902467 := bstep (se 1 (by rfl) ⟨1426850, by rfl⟩ : syracuseStep 1902467 = 2853701) B2853701
theorem B3210421 : Blo 1901435 3210421 := bbase (se 5 (by rfl) ⟨150488, by rfl⟩ : syracuseStep 3210421 = 300977) (by norm_num)
theorem B4280561 : Blo 1901435 4280561 := bstep (se 2 (by rfl) ⟨1605210, by rfl⟩ : syracuseStep 4280561 = 3210421) B3210421
theorem B2853707 : Blo 1901435 2853707 := bstep (se 1 (by rfl) ⟨2140280, by rfl⟩ : syracuseStep 2853707 = 4280561) B4280561
theorem B1902471 : Blo 1901435 1902471 := bstep (se 1 (by rfl) ⟨1426853, by rfl⟩ : syracuseStep 1902471 = 2853707) B2853707
theorem B2140285 : Blo 1901435 2140285 := bbase (se 3 (by rfl) ⟨401303, by rfl⟩ : syracuseStep 2140285 = 802607) (by norm_num)
theorem B2853713 : Blo 1901435 2853713 := bstep (se 2 (by rfl) ⟨1070142, by rfl⟩ : syracuseStep 2853713 = 2140285) B2140285
theorem B1902475 : Blo 1901435 1902475 := bstep (se 1 (by rfl) ⟨1426856, by rfl⟩ : syracuseStep 1902475 = 2853713) B2853713
theorem B6420869 : Blo 1901435 6420869 := bbase (se 4 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 6420869 = 1203913) (by norm_num)
theorem B4280579 : Blo 1901435 4280579 := bstep (se 1 (by rfl) ⟨3210434, by rfl⟩ : syracuseStep 4280579 = 6420869) B6420869
theorem B2853719 : Blo 1901435 2853719 := bstep (se 1 (by rfl) ⟨2140289, by rfl⟩ : syracuseStep 2853719 = 4280579) B4280579
theorem B1902479 : Blo 1901435 1902479 := bstep (se 1 (by rfl) ⟨1426859, by rfl⟩ : syracuseStep 1902479 = 2853719) B2853719
theorem B2853725 : Blo 1901435 2853725 := bbase (se 3 (by rfl) ⟨535073, by rfl⟩ : syracuseStep 2853725 = 1070147) (by norm_num)
theorem B1902483 : Blo 1901435 1902483 := bstep (se 1 (by rfl) ⟨1426862, by rfl⟩ : syracuseStep 1902483 = 2853725) B2853725
theorem B4280597 : Blo 1901435 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B2853731 : Blo 1901435 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B1902487 : Blo 1901435 1902487 := bstep (se 1 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 1902487 = 2853731) B2853731
theorem B7223525 : Blo 1901435 7223525 := bbase (se 4 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 7223525 = 1354411) (by norm_num)
theorem B4815683 : Blo 1901435 4815683 := bstep (se 1 (by rfl) ⟨3611762, by rfl⟩ : syracuseStep 4815683 = 7223525) B7223525
theorem B3210455 : Blo 1901435 3210455 := bstep (se 1 (by rfl) ⟨2407841, by rfl⟩ : syracuseStep 3210455 = 4815683) B4815683
theorem B2140303 : Blo 1901435 2140303 := bstep (se 1 (by rfl) ⟨1605227, by rfl⟩ : syracuseStep 2140303 = 3210455) B3210455
theorem B2853737 : Blo 1901435 2853737 := bstep (se 2 (by rfl) ⟨1070151, by rfl⟩ : syracuseStep 2853737 = 2140303) B2140303
theorem B1902491 : Blo 1901435 1902491 := bstep (se 1 (by rfl) ⟨1426868, by rfl⟩ : syracuseStep 1902491 = 2853737) B2853737
theorem B1928453 : Blo 1901435 1928453 := bbase (se 4 (by rfl) ⟨180792, by rfl⟩ : syracuseStep 1928453 = 361585) (by norm_num)
theorem B5142541 : Blo 1901435 5142541 := bstep (se 3 (by rfl) ⟨964226, by rfl⟩ : syracuseStep 5142541 = 1928453) B1928453
theorem B6856721 : Blo 1901435 6856721 := bstep (se 2 (by rfl) ⟨2571270, by rfl⟩ : syracuseStep 6856721 = 5142541) B5142541
theorem B4571147 : Blo 1901435 4571147 := bstep (se 1 (by rfl) ⟨3428360, by rfl⟩ : syracuseStep 4571147 = 6856721) B6856721
theorem B3047431 : Blo 1901435 3047431 := bstep (se 1 (by rfl) ⟨2285573, by rfl⟩ : syracuseStep 3047431 = 4571147) B4571147
theorem B4063241 : Blo 1901435 4063241 := bstep (se 2 (by rfl) ⟨1523715, by rfl⟩ : syracuseStep 4063241 = 3047431) B3047431
theorem B10835309 : Blo 1901435 10835309 := bstep (se 3 (by rfl) ⟨2031620, by rfl⟩ : syracuseStep 10835309 = 4063241) B4063241
theorem B7223539 : Blo 1901435 7223539 := bstep (se 1 (by rfl) ⟨5417654, by rfl⟩ : syracuseStep 7223539 = 10835309) B10835309
theorem B9631385 : Blo 1901435 9631385 := bstep (se 2 (by rfl) ⟨3611769, by rfl⟩ : syracuseStep 9631385 = 7223539) B7223539
theorem B6420923 : Blo 1901435 6420923 := bstep (se 1 (by rfl) ⟨4815692, by rfl⟩ : syracuseStep 6420923 = 9631385) B9631385
theorem B4280615 : Blo 1901435 4280615 := bstep (se 1 (by rfl) ⟨3210461, by rfl⟩ : syracuseStep 4280615 = 6420923) B6420923
theorem B2853743 : Blo 1901435 2853743 := bstep (se 1 (by rfl) ⟨2140307, by rfl⟩ : syracuseStep 2853743 = 4280615) B4280615
theorem B1902495 : Blo 1901435 1902495 := bstep (se 1 (by rfl) ⟨1426871, by rfl⟩ : syracuseStep 1902495 = 2853743) B2853743
theorem B2853749 : Blo 1901435 2853749 := bbase (se 5 (by rfl) ⟨133769, by rfl⟩ : syracuseStep 2853749 = 267539) (by norm_num)
theorem B1902499 : Blo 1901435 1902499 := bstep (se 1 (by rfl) ⟨1426874, by rfl⟩ : syracuseStep 1902499 = 2853749) B2853749
theorem B3711013 : Blo 1901435 3711013 := bbase (se 4 (by rfl) ⟨347907, by rfl⟩ : syracuseStep 3711013 = 695815) (by norm_num)
theorem B19792069 : Blo 1901435 19792069 := bstep (se 4 (by rfl) ⟨1855506, by rfl⟩ : syracuseStep 19792069 = 3711013) B3711013
theorem B105557701 : Blo 1901435 105557701 := bstep (se 4 (by rfl) ⟨9896034, by rfl⟩ : syracuseStep 105557701 = 19792069) B19792069
theorem B140743601 : Blo 1901435 140743601 := bstep (se 2 (by rfl) ⟨52778850, by rfl⟩ : syracuseStep 140743601 = 105557701) B105557701
theorem B93829067 : Blo 1901435 93829067 := bstep (se 1 (by rfl) ⟨70371800, by rfl⟩ : syracuseStep 93829067 = 140743601) B140743601
theorem B62552711 : Blo 1901435 62552711 := bstep (se 1 (by rfl) ⟨46914533, by rfl⟩ : syracuseStep 62552711 = 93829067) B93829067
theorem B41701807 : Blo 1901435 41701807 := bstep (se 1 (by rfl) ⟨31276355, by rfl⟩ : syracuseStep 41701807 = 62552711) B62552711
theorem B55602409 : Blo 1901435 55602409 := bstep (se 2 (by rfl) ⟨20850903, by rfl⟩ : syracuseStep 55602409 = 41701807) B41701807
theorem B74136545 : Blo 1901435 74136545 := bstep (se 2 (by rfl) ⟨27801204, by rfl⟩ : syracuseStep 74136545 = 55602409) B55602409
theorem B49424363 : Blo 1901435 49424363 := bstep (se 1 (by rfl) ⟨37068272, by rfl⟩ : syracuseStep 49424363 = 74136545) B74136545
theorem B32949575 : Blo 1901435 32949575 := bstep (se 1 (by rfl) ⟨24712181, by rfl⟩ : syracuseStep 32949575 = 49424363) B49424363
theorem B21966383 : Blo 1901435 21966383 := bstep (se 1 (by rfl) ⟨16474787, by rfl⟩ : syracuseStep 21966383 = 32949575) B32949575
theorem B14644255 : Blo 1901435 14644255 := bstep (se 1 (by rfl) ⟨10983191, by rfl⟩ : syracuseStep 14644255 = 21966383) B21966383
theorem B19525673 : Blo 1901435 19525673 := bstep (se 2 (by rfl) ⟨7322127, by rfl⟩ : syracuseStep 19525673 = 14644255) B14644255
theorem B13017115 : Blo 1901435 13017115 := bstep (se 1 (by rfl) ⟨9762836, by rfl⟩ : syracuseStep 13017115 = 19525673) B19525673
theorem B17356153 : Blo 1901435 17356153 := bstep (se 2 (by rfl) ⟨6508557, by rfl⟩ : syracuseStep 17356153 = 13017115) B13017115
theorem B23141537 : Blo 1901435 23141537 := bstep (se 2 (by rfl) ⟨8678076, by rfl⟩ : syracuseStep 23141537 = 17356153) B17356153
theorem B15427691 : Blo 1901435 15427691 := bstep (se 1 (by rfl) ⟨11570768, by rfl⟩ : syracuseStep 15427691 = 23141537) B23141537
theorem B10285127 : Blo 1901435 10285127 := bstep (se 1 (by rfl) ⟨7713845, by rfl⟩ : syracuseStep 10285127 = 15427691) B15427691
theorem B6856751 : Blo 1901435 6856751 := bstep (se 1 (by rfl) ⟨5142563, by rfl⟩ : syracuseStep 6856751 = 10285127) B10285127
theorem B4571167 : Blo 1901435 4571167 := bstep (se 1 (by rfl) ⟨3428375, by rfl⟩ : syracuseStep 4571167 = 6856751) B6856751
theorem B6094889 : Blo 1901435 6094889 := bstep (se 2 (by rfl) ⟨2285583, by rfl⟩ : syracuseStep 6094889 = 4571167) B4571167
theorem B4063259 : Blo 1901435 4063259 := bstep (se 1 (by rfl) ⟨3047444, by rfl⟩ : syracuseStep 4063259 = 6094889) B6094889
theorem B2708839 : Blo 1901435 2708839 := bstep (se 1 (by rfl) ⟨2031629, by rfl⟩ : syracuseStep 2708839 = 4063259) B4063259
theorem B3611785 : Blo 1901435 3611785 := bstep (se 2 (by rfl) ⟨1354419, by rfl⟩ : syracuseStep 3611785 = 2708839) B2708839
theorem B4815713 : Blo 1901435 4815713 := bstep (se 2 (by rfl) ⟨1805892, by rfl⟩ : syracuseStep 4815713 = 3611785) B3611785
theorem B3210475 : Blo 1901435 3210475 := bstep (se 1 (by rfl) ⟨2407856, by rfl⟩ : syracuseStep 3210475 = 4815713) B4815713
theorem B4280633 : Blo 1901435 4280633 := bstep (se 2 (by rfl) ⟨1605237, by rfl⟩ : syracuseStep 4280633 = 3210475) B3210475
theorem B2853755 : Blo 1901435 2853755 := bstep (se 1 (by rfl) ⟨2140316, by rfl⟩ : syracuseStep 2853755 = 4280633) B4280633
theorem B1902503 : Blo 1901435 1902503 := bstep (se 1 (by rfl) ⟨1426877, by rfl⟩ : syracuseStep 1902503 = 2853755) B2853755
theorem B2140321 : Blo 1901435 2140321 := bbase (se 2 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 2140321 = 1605241) (by norm_num)
theorem B2853761 : Blo 1901435 2853761 := bstep (se 2 (by rfl) ⟨1070160, by rfl⟩ : syracuseStep 2853761 = 2140321) B2140321
theorem B1902507 : Blo 1901435 1902507 := bstep (se 1 (by rfl) ⟨1426880, by rfl⟩ : syracuseStep 1902507 = 2853761) B2853761
theorem B4815733 : Blo 1901435 4815733 := bbase (se 5 (by rfl) ⟨225737, by rfl⟩ : syracuseStep 4815733 = 451475) (by norm_num)
theorem B6420977 : Blo 1901435 6420977 := bstep (se 2 (by rfl) ⟨2407866, by rfl⟩ : syracuseStep 6420977 = 4815733) B4815733
theorem B4280651 : Blo 1901435 4280651 := bstep (se 1 (by rfl) ⟨3210488, by rfl⟩ : syracuseStep 4280651 = 6420977) B6420977
theorem B2853767 : Blo 1901435 2853767 := bstep (se 1 (by rfl) ⟨2140325, by rfl⟩ : syracuseStep 2853767 = 4280651) B4280651
theorem B1902511 : Blo 1901435 1902511 := bstep (se 1 (by rfl) ⟨1426883, by rfl⟩ : syracuseStep 1902511 = 2853767) B2853767
theorem B2853773 : Blo 1901435 2853773 := bbase (se 3 (by rfl) ⟨535082, by rfl⟩ : syracuseStep 2853773 = 1070165) (by norm_num)
theorem B1902515 : Blo 1901435 1902515 := bstep (se 1 (by rfl) ⟨1426886, by rfl⟩ : syracuseStep 1902515 = 2853773) B2853773
theorem B4280669 : Blo 1901435 4280669 := bbase (se 3 (by rfl) ⟨802625, by rfl⟩ : syracuseStep 4280669 = 1605251) (by norm_num)
theorem B2853779 : Blo 1901435 2853779 := bstep (se 1 (by rfl) ⟨2140334, by rfl⟩ : syracuseStep 2853779 = 4280669) B4280669
theorem B1902519 : Blo 1901435 1902519 := bstep (se 1 (by rfl) ⟨1426889, by rfl⟩ : syracuseStep 1902519 = 2853779) B2853779
theorem B3210509 : Blo 1901435 3210509 := bbase (se 3 (by rfl) ⟨601970, by rfl⟩ : syracuseStep 3210509 = 1203941) (by norm_num)
theorem B2140339 : Blo 1901435 2140339 := bstep (se 1 (by rfl) ⟨1605254, by rfl⟩ : syracuseStep 2140339 = 3210509) B3210509
theorem B2853785 : Blo 1901435 2853785 := bstep (se 2 (by rfl) ⟨1070169, by rfl⟩ : syracuseStep 2853785 = 2140339) B2140339
theorem B1902523 : Blo 1901435 1902523 := bstep (se 1 (by rfl) ⟨1426892, by rfl⟩ : syracuseStep 1902523 = 2853785) B2853785
theorem B16253237 : Blo 1901435 16253237 := bbase (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) (by norm_num)
theorem B10835491 : Blo 1901435 10835491 := bstep (se 1 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 10835491 = 16253237) B16253237
theorem B14447321 : Blo 1901435 14447321 := bstep (se 2 (by rfl) ⟨5417745, by rfl⟩ : syracuseStep 14447321 = 10835491) B10835491
theorem B9631547 : Blo 1901435 9631547 := bstep (se 1 (by rfl) ⟨7223660, by rfl⟩ : syracuseStep 9631547 = 14447321) B14447321
theorem B6421031 : Blo 1901435 6421031 := bstep (se 1 (by rfl) ⟨4815773, by rfl⟩ : syracuseStep 6421031 = 9631547) B9631547
theorem B4280687 : Blo 1901435 4280687 := bstep (se 1 (by rfl) ⟨3210515, by rfl⟩ : syracuseStep 4280687 = 6421031) B6421031
theorem B2853791 : Blo 1901435 2853791 := bstep (se 1 (by rfl) ⟨2140343, by rfl⟩ : syracuseStep 2853791 = 4280687) B4280687
theorem B1902527 : Blo 1901435 1902527 := bstep (se 1 (by rfl) ⟨1426895, by rfl⟩ : syracuseStep 1902527 = 2853791) B2853791
theorem B2853797 : Blo 1901435 2853797 := bbase (se 4 (by rfl) ⟨267543, by rfl⟩ : syracuseStep 2853797 = 535087) (by norm_num)
theorem B1902531 : Blo 1901435 1902531 := bstep (se 1 (by rfl) ⟨1426898, by rfl⟩ : syracuseStep 1902531 = 2853797) B2853797
theorem B2407897 : Blo 1901435 2407897 := bbase (se 2 (by rfl) ⟨902961, by rfl⟩ : syracuseStep 2407897 = 1805923) (by norm_num)
theorem B3210529 : Blo 1901435 3210529 := bstep (se 2 (by rfl) ⟨1203948, by rfl⟩ : syracuseStep 3210529 = 2407897) B2407897
theorem B4280705 : Blo 1901435 4280705 := bstep (se 2 (by rfl) ⟨1605264, by rfl⟩ : syracuseStep 4280705 = 3210529) B3210529
theorem B2853803 : Blo 1901435 2853803 := bstep (se 1 (by rfl) ⟨2140352, by rfl⟩ : syracuseStep 2853803 = 4280705) B4280705
theorem B1902535 : Blo 1901435 1902535 := bstep (se 1 (by rfl) ⟨1426901, by rfl⟩ : syracuseStep 1902535 = 2853803) B2853803
theorem B2140357 : Blo 1901435 2140357 := bbase (se 4 (by rfl) ⟨200658, by rfl⟩ : syracuseStep 2140357 = 401317) (by norm_num)
theorem B2853809 : Blo 1901435 2853809 := bstep (se 2 (by rfl) ⟨1070178, by rfl⟩ : syracuseStep 2853809 = 2140357) B2140357
theorem B1902539 : Blo 1901435 1902539 := bstep (se 1 (by rfl) ⟨1426904, by rfl⟩ : syracuseStep 1902539 = 2853809) B2853809
theorem B3611861 : Blo 1901435 3611861 := bbase (se 7 (by rfl) ⟨42326, by rfl⟩ : syracuseStep 3611861 = 84653) (by norm_num)
theorem B2407907 : Blo 1901435 2407907 := bstep (se 1 (by rfl) ⟨1805930, by rfl⟩ : syracuseStep 2407907 = 3611861) B3611861
theorem B6421085 : Blo 1901435 6421085 := bstep (se 3 (by rfl) ⟨1203953, by rfl⟩ : syracuseStep 6421085 = 2407907) B2407907
theorem B4280723 : Blo 1901435 4280723 := bstep (se 1 (by rfl) ⟨3210542, by rfl⟩ : syracuseStep 4280723 = 6421085) B6421085
theorem B2853815 : Blo 1901435 2853815 := bstep (se 1 (by rfl) ⟨2140361, by rfl⟩ : syracuseStep 2853815 = 4280723) B4280723
theorem B1902543 : Blo 1901435 1902543 := bstep (se 1 (by rfl) ⟨1426907, by rfl⟩ : syracuseStep 1902543 = 2853815) B2853815
theorem B2853821 : Blo 1901435 2853821 := bbase (se 3 (by rfl) ⟨535091, by rfl⟩ : syracuseStep 2853821 = 1070183) (by norm_num)
theorem B1902547 : Blo 1901435 1902547 := bstep (se 1 (by rfl) ⟨1426910, by rfl⟩ : syracuseStep 1902547 = 2853821) B2853821
theorem B4280741 : Blo 1901435 4280741 := bbase (se 4 (by rfl) ⟨401319, by rfl⟩ : syracuseStep 4280741 = 802639) (by norm_num)
theorem B2853827 : Blo 1901435 2853827 := bstep (se 1 (by rfl) ⟨2140370, by rfl⟩ : syracuseStep 2853827 = 4280741) B4280741
theorem B1902551 : Blo 1901435 1902551 := bstep (se 1 (by rfl) ⟨1426913, by rfl⟩ : syracuseStep 1902551 = 2853827) B2853827
theorem B4815845 : Blo 1901435 4815845 := bbase (se 4 (by rfl) ⟨451485, by rfl⟩ : syracuseStep 4815845 = 902971) (by norm_num)
theorem B3210563 : Blo 1901435 3210563 := bstep (se 1 (by rfl) ⟨2407922, by rfl⟩ : syracuseStep 3210563 = 4815845) B4815845
theorem B2140375 : Blo 1901435 2140375 := bstep (se 1 (by rfl) ⟨1605281, by rfl⟩ : syracuseStep 2140375 = 3210563) B3210563
theorem B2853833 : Blo 1901435 2853833 := bstep (se 2 (by rfl) ⟨1070187, by rfl⟩ : syracuseStep 2853833 = 2140375) B2140375
theorem B1902555 : Blo 1901435 1902555 := bstep (se 1 (by rfl) ⟨1426916, by rfl⟩ : syracuseStep 1902555 = 2853833) B2853833
theorem B2031689 : Blo 1901435 2031689 := bbase (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) (by norm_num)
theorem B5417837 : Blo 1901435 5417837 := bstep (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) B2031689
theorem B3611891 : Blo 1901435 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B9631709 : Blo 1901435 9631709 := bstep (se 3 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 9631709 = 3611891) B3611891
theorem B6421139 : Blo 1901435 6421139 := bstep (se 1 (by rfl) ⟨4815854, by rfl⟩ : syracuseStep 6421139 = 9631709) B9631709
theorem B4280759 : Blo 1901435 4280759 := bstep (se 1 (by rfl) ⟨3210569, by rfl⟩ : syracuseStep 4280759 = 6421139) B6421139
theorem B2853839 : Blo 1901435 2853839 := bstep (se 1 (by rfl) ⟨2140379, by rfl⟩ : syracuseStep 2853839 = 4280759) B4280759
theorem B1902559 : Blo 1901435 1902559 := bstep (se 1 (by rfl) ⟨1426919, by rfl⟩ : syracuseStep 1902559 = 2853839) B2853839
theorem B2853845 : Blo 1901435 2853845 := bbase (se 7 (by rfl) ⟨33443, by rfl⟩ : syracuseStep 2853845 = 66887) (by norm_num)
theorem B1902563 : Blo 1901435 1902563 := bstep (se 1 (by rfl) ⟨1426922, by rfl⟩ : syracuseStep 1902563 = 2853845) B2853845
theorem B7223813 : Blo 1901435 7223813 := bbase (se 4 (by rfl) ⟨677232, by rfl⟩ : syracuseStep 7223813 = 1354465) (by norm_num)
theorem B4815875 : Blo 1901435 4815875 := bstep (se 1 (by rfl) ⟨3611906, by rfl⟩ : syracuseStep 4815875 = 7223813) B7223813
theorem B3210583 : Blo 1901435 3210583 := bstep (se 1 (by rfl) ⟨2407937, by rfl⟩ : syracuseStep 3210583 = 4815875) B4815875
theorem B4280777 : Blo 1901435 4280777 := bstep (se 2 (by rfl) ⟨1605291, by rfl⟩ : syracuseStep 4280777 = 3210583) B3210583
theorem B2853851 : Blo 1901435 2853851 := bstep (se 1 (by rfl) ⟨2140388, by rfl⟩ : syracuseStep 2853851 = 4280777) B4280777
theorem B1902567 : Blo 1901435 1902567 := bstep (se 1 (by rfl) ⟨1426925, by rfl⟩ : syracuseStep 1902567 = 2853851) B2853851
theorem B2140393 : Blo 1901435 2140393 := bbase (se 2 (by rfl) ⟨802647, by rfl⟩ : syracuseStep 2140393 = 1605295) (by norm_num)
theorem B2853857 : Blo 1901435 2853857 := bstep (se 2 (by rfl) ⟨1070196, by rfl⟩ : syracuseStep 2853857 = 2140393) B2140393
theorem B1902571 : Blo 1901435 1902571 := bstep (se 1 (by rfl) ⟨1426928, by rfl⟩ : syracuseStep 1902571 = 2853857) B2853857
theorem B10835765 : Blo 1901435 10835765 := bbase (se 5 (by rfl) ⟨507926, by rfl⟩ : syracuseStep 10835765 = 1015853) (by norm_num)
theorem B7223843 : Blo 1901435 7223843 := bstep (se 1 (by rfl) ⟨5417882, by rfl⟩ : syracuseStep 7223843 = 10835765) B10835765
theorem B4815895 : Blo 1901435 4815895 := bstep (se 1 (by rfl) ⟨3611921, by rfl⟩ : syracuseStep 4815895 = 7223843) B7223843
theorem B6421193 : Blo 1901435 6421193 := bstep (se 2 (by rfl) ⟨2407947, by rfl⟩ : syracuseStep 6421193 = 4815895) B4815895
theorem B4280795 : Blo 1901435 4280795 := bstep (se 1 (by rfl) ⟨3210596, by rfl⟩ : syracuseStep 4280795 = 6421193) B6421193
theorem B2853863 : Blo 1901435 2853863 := bstep (se 1 (by rfl) ⟨2140397, by rfl⟩ : syracuseStep 2853863 = 4280795) B4280795
theorem B1902575 : Blo 1901435 1902575 := bstep (se 1 (by rfl) ⟨1426931, by rfl⟩ : syracuseStep 1902575 = 2853863) B2853863
theorem B2853869 : Blo 1901435 2853869 := bbase (se 3 (by rfl) ⟨535100, by rfl⟩ : syracuseStep 2853869 = 1070201) (by norm_num)
theorem B1902579 : Blo 1901435 1902579 := bstep (se 1 (by rfl) ⟨1426934, by rfl⟩ : syracuseStep 1902579 = 2853869) B2853869
theorem B4280813 : Blo 1901435 4280813 := bbase (se 3 (by rfl) ⟨802652, by rfl⟩ : syracuseStep 4280813 = 1605305) (by norm_num)
theorem B2853875 : Blo 1901435 2853875 := bstep (se 1 (by rfl) ⟨2140406, by rfl⟩ : syracuseStep 2853875 = 4280813) B4280813
theorem B1902583 : Blo 1901435 1902583 := bstep (se 1 (by rfl) ⟨1426937, by rfl⟩ : syracuseStep 1902583 = 2853875) B2853875
theorem B7322453 : Blo 1901435 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B4881635 : Blo 1901435 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B3254423 : Blo 1901435 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B8678461 : Blo 1901435 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B11571281 : Blo 1901435 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B7714187 : Blo 1901435 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B5142791 : Blo 1901435 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B13714109 : Blo 1901435 13714109 := bstep (se 3 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 13714109 = 5142791) B5142791
theorem B9142739 : Blo 1901435 9142739 := bstep (se 1 (by rfl) ⟨6857054, by rfl⟩ : syracuseStep 9142739 = 13714109) B13714109
theorem B6095159 : Blo 1901435 6095159 := bstep (se 1 (by rfl) ⟨4571369, by rfl⟩ : syracuseStep 6095159 = 9142739) B9142739
theorem B4063439 : Blo 1901435 4063439 := bstep (se 1 (by rfl) ⟨3047579, by rfl⟩ : syracuseStep 4063439 = 6095159) B6095159
theorem B2708959 : Blo 1901435 2708959 := bstep (se 1 (by rfl) ⟨2031719, by rfl⟩ : syracuseStep 2708959 = 4063439) B4063439
theorem B3611945 : Blo 1901435 3611945 := bstep (se 2 (by rfl) ⟨1354479, by rfl⟩ : syracuseStep 3611945 = 2708959) B2708959
theorem B2407963 : Blo 1901435 2407963 := bstep (se 1 (by rfl) ⟨1805972, by rfl⟩ : syracuseStep 2407963 = 3611945) B3611945
theorem B3210617 : Blo 1901435 3210617 := bstep (se 2 (by rfl) ⟨1203981, by rfl⟩ : syracuseStep 3210617 = 2407963) B2407963
theorem B2140411 : Blo 1901435 2140411 := bstep (se 1 (by rfl) ⟨1605308, by rfl⟩ : syracuseStep 2140411 = 3210617) B3210617
theorem B2853881 : Blo 1901435 2853881 := bstep (se 2 (by rfl) ⟨1070205, by rfl⟩ : syracuseStep 2853881 = 2140411) B2140411
theorem B1902587 : Blo 1901435 1902587 := bstep (se 1 (by rfl) ⟨1426940, by rfl⟩ : syracuseStep 1902587 = 2853881) B2853881
theorem B9267493 : Blo 1901435 9267493 := bbase (se 4 (by rfl) ⟨868827, by rfl⟩ : syracuseStep 9267493 = 1737655) (by norm_num)
theorem B12356657 : Blo 1901435 12356657 := bstep (se 2 (by rfl) ⟨4633746, by rfl⟩ : syracuseStep 12356657 = 9267493) B9267493
theorem B8237771 : Blo 1901435 8237771 := bstep (se 1 (by rfl) ⟨6178328, by rfl⟩ : syracuseStep 8237771 = 12356657) B12356657
theorem B5491847 : Blo 1901435 5491847 := bstep (se 1 (by rfl) ⟨4118885, by rfl⟩ : syracuseStep 5491847 = 8237771) B8237771
theorem B14644925 : Blo 1901435 14644925 := bstep (se 3 (by rfl) ⟨2745923, by rfl⟩ : syracuseStep 14644925 = 5491847) B5491847
theorem B9763283 : Blo 1901435 9763283 := bstep (se 1 (by rfl) ⟨7322462, by rfl⟩ : syracuseStep 9763283 = 14644925) B14644925
theorem B6508855 : Blo 1901435 6508855 := bstep (se 1 (by rfl) ⟨4881641, by rfl⟩ : syracuseStep 6508855 = 9763283) B9763283
theorem B34713893 : Blo 1901435 34713893 := bstep (se 4 (by rfl) ⟨3254427, by rfl⟩ : syracuseStep 34713893 = 6508855) B6508855
theorem B23142595 : Blo 1901435 23142595 := bstep (se 1 (by rfl) ⟨17356946, by rfl⟩ : syracuseStep 23142595 = 34713893) B34713893
theorem B30856793 : Blo 1901435 30856793 := bstep (se 2 (by rfl) ⟨11571297, by rfl⟩ : syracuseStep 30856793 = 23142595) B23142595
theorem B82284781 : Blo 1901435 82284781 := bstep (se 3 (by rfl) ⟨15428396, by rfl⟩ : syracuseStep 82284781 = 30856793) B30856793
theorem B109713041 : Blo 1901435 109713041 := bstep (se 2 (by rfl) ⟨41142390, by rfl⟩ : syracuseStep 109713041 = 82284781) B82284781
theorem B73142027 : Blo 1901435 73142027 := bstep (se 1 (by rfl) ⟨54856520, by rfl⟩ : syracuseStep 73142027 = 109713041) B109713041
theorem B48761351 : Blo 1901435 48761351 := bstep (se 1 (by rfl) ⟨36571013, by rfl⟩ : syracuseStep 48761351 = 73142027) B73142027
theorem B32507567 : Blo 1901435 32507567 := bstep (se 1 (by rfl) ⟨24380675, by rfl⟩ : syracuseStep 32507567 = 48761351) B48761351
theorem B21671711 : Blo 1901435 21671711 := bstep (se 1 (by rfl) ⟨16253783, by rfl⟩ : syracuseStep 21671711 = 32507567) B32507567
theorem B14447807 : Blo 1901435 14447807 := bstep (se 1 (by rfl) ⟨10835855, by rfl⟩ : syracuseStep 14447807 = 21671711) B21671711
theorem B9631871 : Blo 1901435 9631871 := bstep (se 1 (by rfl) ⟨7223903, by rfl⟩ : syracuseStep 9631871 = 14447807) B14447807
theorem B6421247 : Blo 1901435 6421247 := bstep (se 1 (by rfl) ⟨4815935, by rfl⟩ : syracuseStep 6421247 = 9631871) B9631871
theorem B4280831 : Blo 1901435 4280831 := bstep (se 1 (by rfl) ⟨3210623, by rfl⟩ : syracuseStep 4280831 = 6421247) B6421247
theorem B2853887 : Blo 1901435 2853887 := bstep (se 1 (by rfl) ⟨2140415, by rfl⟩ : syracuseStep 2853887 = 4280831) B4280831
theorem B1902591 : Blo 1901435 1902591 := bstep (se 1 (by rfl) ⟨1426943, by rfl⟩ : syracuseStep 1902591 = 2853887) B2853887
theorem B2853893 : Blo 1901435 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B1902595 : Blo 1901435 1902595 := bstep (se 1 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 1902595 = 2853893) B2853893
theorem B3210637 : Blo 1901435 3210637 := bbase (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) (by norm_num)
theorem B4280849 : Blo 1901435 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B2853899 : Blo 1901435 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B1902599 : Blo 1901435 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B2140429 : Blo 1901435 2140429 := bbase (se 3 (by rfl) ⟨401330, by rfl⟩ : syracuseStep 2140429 = 802661) (by norm_num)
theorem B2853905 : Blo 1901435 2853905 := bstep (se 2 (by rfl) ⟨1070214, by rfl⟩ : syracuseStep 2853905 = 2140429) B2140429
theorem B1902603 : Blo 1901435 1902603 := bstep (se 1 (by rfl) ⟨1426952, by rfl⟩ : syracuseStep 1902603 = 2853905) B2853905
theorem B6421301 : Blo 1901435 6421301 := bbase (se 5 (by rfl) ⟨300998, by rfl⟩ : syracuseStep 6421301 = 601997) (by norm_num)
theorem B4280867 : Blo 1901435 4280867 := bstep (se 1 (by rfl) ⟨3210650, by rfl⟩ : syracuseStep 4280867 = 6421301) B6421301
theorem B2853911 : Blo 1901435 2853911 := bstep (se 1 (by rfl) ⟨2140433, by rfl⟩ : syracuseStep 2853911 = 4280867) B4280867
theorem B1902607 : Blo 1901435 1902607 := bstep (se 1 (by rfl) ⟨1426955, by rfl⟩ : syracuseStep 1902607 = 2853911) B2853911
theorem B2853917 : Blo 1901435 2853917 := bbase (se 3 (by rfl) ⟨535109, by rfl⟩ : syracuseStep 2853917 = 1070219) (by norm_num)
theorem B1902611 : Blo 1901435 1902611 := bstep (se 1 (by rfl) ⟨1426958, by rfl⟩ : syracuseStep 1902611 = 2853917) B2853917
theorem B4280885 : Blo 1901435 4280885 := bbase (se 5 (by rfl) ⟨200666, by rfl⟩ : syracuseStep 4280885 = 401333) (by norm_num)
theorem B2853923 : Blo 1901435 2853923 := bstep (se 1 (by rfl) ⟨2140442, by rfl⟩ : syracuseStep 2853923 = 4280885) B4280885
theorem B1902615 : Blo 1901435 1902615 := bstep (se 1 (by rfl) ⟨1426961, by rfl⟩ : syracuseStep 1902615 = 2853923) B2853923
theorem B8127013 : Blo 1901435 8127013 := bbase (se 4 (by rfl) ⟨761907, by rfl⟩ : syracuseStep 8127013 = 1523815) (by norm_num)
theorem B10836017 : Blo 1901435 10836017 := bstep (se 2 (by rfl) ⟨4063506, by rfl⟩ : syracuseStep 10836017 = 8127013) B8127013
theorem B7224011 : Blo 1901435 7224011 := bstep (se 1 (by rfl) ⟨5418008, by rfl⟩ : syracuseStep 7224011 = 10836017) B10836017
theorem B4816007 : Blo 1901435 4816007 := bstep (se 1 (by rfl) ⟨3612005, by rfl⟩ : syracuseStep 4816007 = 7224011) B7224011
theorem B3210671 : Blo 1901435 3210671 := bstep (se 1 (by rfl) ⟨2408003, by rfl⟩ : syracuseStep 3210671 = 4816007) B4816007
theorem B2140447 : Blo 1901435 2140447 := bstep (se 1 (by rfl) ⟨1605335, by rfl⟩ : syracuseStep 2140447 = 3210671) B3210671
theorem B2853929 : Blo 1901435 2853929 := bstep (se 2 (by rfl) ⟨1070223, by rfl⟩ : syracuseStep 2853929 = 2140447) B2140447
theorem B1902619 : Blo 1901435 1902619 := bstep (se 1 (by rfl) ⟨1426964, by rfl⟩ : syracuseStep 1902619 = 2853929) B2853929
theorem B8127029 : Blo 1901435 8127029 := bbase (se 5 (by rfl) ⟨380954, by rfl⟩ : syracuseStep 8127029 = 761909) (by norm_num)
theorem B5418019 : Blo 1901435 5418019 := bstep (se 1 (by rfl) ⟨4063514, by rfl⟩ : syracuseStep 5418019 = 8127029) B8127029
theorem B7224025 : Blo 1901435 7224025 := bstep (se 2 (by rfl) ⟨2709009, by rfl⟩ : syracuseStep 7224025 = 5418019) B5418019
theorem B9632033 : Blo 1901435 9632033 := bstep (se 2 (by rfl) ⟨3612012, by rfl⟩ : syracuseStep 9632033 = 7224025) B7224025
theorem B6421355 : Blo 1901435 6421355 := bstep (se 1 (by rfl) ⟨4816016, by rfl⟩ : syracuseStep 6421355 = 9632033) B9632033
theorem B4280903 : Blo 1901435 4280903 := bstep (se 1 (by rfl) ⟨3210677, by rfl⟩ : syracuseStep 4280903 = 6421355) B6421355
theorem B2853935 : Blo 1901435 2853935 := bstep (se 1 (by rfl) ⟨2140451, by rfl⟩ : syracuseStep 2853935 = 4280903) B4280903
theorem B1902623 : Blo 1901435 1902623 := bstep (se 1 (by rfl) ⟨1426967, by rfl⟩ : syracuseStep 1902623 = 2853935) B2853935
theorem B2853941 : Blo 1901435 2853941 := bbase (se 5 (by rfl) ⟨133778, by rfl⟩ : syracuseStep 2853941 = 267557) (by norm_num)
theorem B1902627 : Blo 1901435 1902627 := bstep (se 1 (by rfl) ⟨1426970, by rfl⟩ : syracuseStep 1902627 = 2853941) B2853941
theorem B4816037 : Blo 1901435 4816037 := bbase (se 4 (by rfl) ⟨451503, by rfl⟩ : syracuseStep 4816037 = 903007) (by norm_num)
theorem B3210691 : Blo 1901435 3210691 := bstep (se 1 (by rfl) ⟨2408018, by rfl⟩ : syracuseStep 3210691 = 4816037) B4816037
theorem B4280921 : Blo 1901435 4280921 := bstep (se 2 (by rfl) ⟨1605345, by rfl⟩ : syracuseStep 4280921 = 3210691) B3210691
theorem B2853947 : Blo 1901435 2853947 := bstep (se 1 (by rfl) ⟨2140460, by rfl⟩ : syracuseStep 2853947 = 4280921) B4280921
theorem B1902631 : Blo 1901435 1902631 := bstep (se 1 (by rfl) ⟨1426973, by rfl⟩ : syracuseStep 1902631 = 2853947) B2853947
theorem B2140465 : Blo 1901435 2140465 := bbase (se 2 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 2140465 = 1605349) (by norm_num)
theorem B2853953 : Blo 1901435 2853953 := bstep (se 2 (by rfl) ⟨1070232, by rfl⟩ : syracuseStep 2853953 = 2140465) B2140465
theorem B1902635 : Blo 1901435 1902635 := bstep (se 1 (by rfl) ⟨1426976, by rfl⟩ : syracuseStep 1902635 = 2853953) B2853953
theorem B4063549 : Blo 1901435 4063549 := bbase (se 3 (by rfl) ⟨761915, by rfl⟩ : syracuseStep 4063549 = 1523831) (by norm_num)
theorem B5418065 : Blo 1901435 5418065 := bstep (se 2 (by rfl) ⟨2031774, by rfl⟩ : syracuseStep 5418065 = 4063549) B4063549
theorem B3612043 : Blo 1901435 3612043 := bstep (se 1 (by rfl) ⟨2709032, by rfl⟩ : syracuseStep 3612043 = 5418065) B5418065
theorem B4816057 : Blo 1901435 4816057 := bstep (se 2 (by rfl) ⟨1806021, by rfl⟩ : syracuseStep 4816057 = 3612043) B3612043
theorem B6421409 : Blo 1901435 6421409 := bstep (se 2 (by rfl) ⟨2408028, by rfl⟩ : syracuseStep 6421409 = 4816057) B4816057
theorem B4280939 : Blo 1901435 4280939 := bstep (se 1 (by rfl) ⟨3210704, by rfl⟩ : syracuseStep 4280939 = 6421409) B6421409
theorem B2853959 : Blo 1901435 2853959 := bstep (se 1 (by rfl) ⟨2140469, by rfl⟩ : syracuseStep 2853959 = 4280939) B4280939
theorem B1902639 : Blo 1901435 1902639 := bstep (se 1 (by rfl) ⟨1426979, by rfl⟩ : syracuseStep 1902639 = 2853959) B2853959
theorem B2853965 : Blo 1901435 2853965 := bbase (se 3 (by rfl) ⟨535118, by rfl⟩ : syracuseStep 2853965 = 1070237) (by norm_num)
theorem B1902643 : Blo 1901435 1902643 := bstep (se 1 (by rfl) ⟨1426982, by rfl⟩ : syracuseStep 1902643 = 2853965) B2853965
theorem B4280957 : Blo 1901435 4280957 := bbase (se 3 (by rfl) ⟨802679, by rfl⟩ : syracuseStep 4280957 = 1605359) (by norm_num)
theorem B2853971 : Blo 1901435 2853971 := bstep (se 1 (by rfl) ⟨2140478, by rfl⟩ : syracuseStep 2853971 = 4280957) B4280957
theorem B1902647 : Blo 1901435 1902647 := bstep (se 1 (by rfl) ⟨1426985, by rfl⟩ : syracuseStep 1902647 = 2853971) B2853971
theorem B3210725 : Blo 1901435 3210725 := bbase (se 4 (by rfl) ⟨301005, by rfl⟩ : syracuseStep 3210725 = 602011) (by norm_num)
theorem B2140483 : Blo 1901435 2140483 := bstep (se 1 (by rfl) ⟨1605362, by rfl⟩ : syracuseStep 2140483 = 3210725) B3210725
theorem B2853977 : Blo 1901435 2853977 := bstep (se 2 (by rfl) ⟨1070241, by rfl⟩ : syracuseStep 2853977 = 2140483) B2140483
theorem B1902651 : Blo 1901435 1902651 := bstep (se 1 (by rfl) ⟨1426988, by rfl⟩ : syracuseStep 1902651 = 2853977) B2853977
theorem B3661357 : Blo 1901435 3661357 := bbase (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) (by norm_num)
theorem B4881809 : Blo 1901435 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B3254539 : Blo 1901435 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B4339385 : Blo 1901435 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B2892923 : Blo 1901435 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B1928615 : Blo 1901435 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B20571893 : Blo 1901435 20571893 := bstep (se 5 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 20571893 = 1928615) B1928615
theorem B13714595 : Blo 1901435 13714595 := bstep (se 1 (by rfl) ⟨10285946, by rfl⟩ : syracuseStep 13714595 = 20571893) B20571893
theorem B9143063 : Blo 1901435 9143063 := bstep (se 1 (by rfl) ⟨6857297, by rfl⟩ : syracuseStep 9143063 = 13714595) B13714595
theorem B6095375 : Blo 1901435 6095375 := bstep (se 1 (by rfl) ⟨4571531, by rfl⟩ : syracuseStep 6095375 = 9143063) B9143063
theorem B4063583 : Blo 1901435 4063583 := bstep (se 1 (by rfl) ⟨3047687, by rfl⟩ : syracuseStep 4063583 = 6095375) B6095375
theorem B2709055 : Blo 1901435 2709055 := bstep (se 1 (by rfl) ⟨2031791, by rfl⟩ : syracuseStep 2709055 = 4063583) B4063583
theorem B14448293 : Blo 1901435 14448293 := bstep (se 4 (by rfl) ⟨1354527, by rfl⟩ : syracuseStep 14448293 = 2709055) B2709055
theorem B9632195 : Blo 1901435 9632195 := bstep (se 1 (by rfl) ⟨7224146, by rfl⟩ : syracuseStep 9632195 = 14448293) B14448293
theorem B6421463 : Blo 1901435 6421463 := bstep (se 1 (by rfl) ⟨4816097, by rfl⟩ : syracuseStep 6421463 = 9632195) B9632195
theorem B4280975 : Blo 1901435 4280975 := bstep (se 1 (by rfl) ⟨3210731, by rfl⟩ : syracuseStep 4280975 = 6421463) B6421463
theorem B2853983 : Blo 1901435 2853983 := bstep (se 1 (by rfl) ⟨2140487, by rfl⟩ : syracuseStep 2853983 = 4280975) B4280975
theorem B1902655 : Blo 1901435 1902655 := bstep (se 1 (by rfl) ⟨1426991, by rfl⟩ : syracuseStep 1902655 = 2853983) B2853983
theorem B2853989 : Blo 1901435 2853989 := bbase (se 4 (by rfl) ⟨267561, by rfl⟩ : syracuseStep 2853989 = 535123) (by norm_num)
theorem B1902659 : Blo 1901435 1902659 := bstep (se 1 (by rfl) ⟨1426994, by rfl⟩ : syracuseStep 1902659 = 2853989) B2853989
theorem B3047701 : Blo 1901435 3047701 := bbase (se 6 (by rfl) ⟨71430, by rfl⟩ : syracuseStep 3047701 = 142861) (by norm_num)
theorem B4063601 : Blo 1901435 4063601 := bstep (se 2 (by rfl) ⟨1523850, by rfl⟩ : syracuseStep 4063601 = 3047701) B3047701
theorem B2709067 : Blo 1901435 2709067 := bstep (se 1 (by rfl) ⟨2031800, by rfl⟩ : syracuseStep 2709067 = 4063601) B4063601
theorem B3612089 : Blo 1901435 3612089 := bstep (se 2 (by rfl) ⟨1354533, by rfl⟩ : syracuseStep 3612089 = 2709067) B2709067
theorem B2408059 : Blo 1901435 2408059 := bstep (se 1 (by rfl) ⟨1806044, by rfl⟩ : syracuseStep 2408059 = 3612089) B3612089
theorem B3210745 : Blo 1901435 3210745 := bstep (se 2 (by rfl) ⟨1204029, by rfl⟩ : syracuseStep 3210745 = 2408059) B2408059
theorem B4280993 : Blo 1901435 4280993 := bstep (se 2 (by rfl) ⟨1605372, by rfl⟩ : syracuseStep 4280993 = 3210745) B3210745
theorem B2853995 : Blo 1901435 2853995 := bstep (se 1 (by rfl) ⟨2140496, by rfl⟩ : syracuseStep 2853995 = 4280993) B4280993
theorem B1902663 : Blo 1901435 1902663 := bstep (se 1 (by rfl) ⟨1426997, by rfl⟩ : syracuseStep 1902663 = 2853995) B2853995
theorem B2140501 : Blo 1901435 2140501 := bbase (se 10 (by rfl) ⟨3135, by rfl⟩ : syracuseStep 2140501 = 6271) (by norm_num)
theorem B2854001 : Blo 1901435 2854001 := bstep (se 2 (by rfl) ⟨1070250, by rfl⟩ : syracuseStep 2854001 = 2140501) B2140501
theorem B1902667 : Blo 1901435 1902667 := bstep (se 1 (by rfl) ⟨1427000, by rfl⟩ : syracuseStep 1902667 = 2854001) B2854001
theorem B2408069 : Blo 1901435 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B6421517 : Blo 1901435 6421517 := bstep (se 3 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 6421517 = 2408069) B2408069
theorem B4281011 : Blo 1901435 4281011 := bstep (se 1 (by rfl) ⟨3210758, by rfl⟩ : syracuseStep 4281011 = 6421517) B6421517
theorem B2854007 : Blo 1901435 2854007 := bstep (se 1 (by rfl) ⟨2140505, by rfl⟩ : syracuseStep 2854007 = 4281011) B4281011
theorem B1902671 : Blo 1901435 1902671 := bstep (se 1 (by rfl) ⟨1427003, by rfl⟩ : syracuseStep 1902671 = 2854007) B2854007
theorem B2854013 : Blo 1901435 2854013 := bbase (se 3 (by rfl) ⟨535127, by rfl⟩ : syracuseStep 2854013 = 1070255) (by norm_num)
theorem B1902675 : Blo 1901435 1902675 := bstep (se 1 (by rfl) ⟨1427006, by rfl⟩ : syracuseStep 1902675 = 2854013) B2854013
theorem B4281029 : Blo 1901435 4281029 := bbase (se 4 (by rfl) ⟨401346, by rfl⟩ : syracuseStep 4281029 = 802693) (by norm_num)
theorem B2854019 : Blo 1901435 2854019 := bstep (se 1 (by rfl) ⟨2140514, by rfl⟩ : syracuseStep 2854019 = 4281029) B4281029
theorem B1902679 : Blo 1901435 1902679 := bstep (se 1 (by rfl) ⟨1427009, by rfl⟩ : syracuseStep 1902679 = 2854019) B2854019
theorem B6509173 : Blo 1901435 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B8678897 : Blo 1901435 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B5785931 : Blo 1901435 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B15429149 : Blo 1901435 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B10286099 : Blo 1901435 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B6857399 : Blo 1901435 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B18286397 : Blo 1901435 18286397 := bstep (se 3 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 18286397 = 6857399) B6857399
theorem B12190931 : Blo 1901435 12190931 := bstep (se 1 (by rfl) ⟨9143198, by rfl⟩ : syracuseStep 12190931 = 18286397) B18286397
theorem B8127287 : Blo 1901435 8127287 := bstep (se 1 (by rfl) ⟨6095465, by rfl⟩ : syracuseStep 8127287 = 12190931) B12190931
theorem B5418191 : Blo 1901435 5418191 := bstep (se 1 (by rfl) ⟨4063643, by rfl⟩ : syracuseStep 5418191 = 8127287) B8127287
theorem B3612127 : Blo 1901435 3612127 := bstep (se 1 (by rfl) ⟨2709095, by rfl⟩ : syracuseStep 3612127 = 5418191) B5418191
theorem B4816169 : Blo 1901435 4816169 := bstep (se 2 (by rfl) ⟨1806063, by rfl⟩ : syracuseStep 4816169 = 3612127) B3612127
theorem B3210779 : Blo 1901435 3210779 := bstep (se 1 (by rfl) ⟨2408084, by rfl⟩ : syracuseStep 3210779 = 4816169) B4816169
theorem B2140519 : Blo 1901435 2140519 := bstep (se 1 (by rfl) ⟨1605389, by rfl⟩ : syracuseStep 2140519 = 3210779) B3210779
theorem B2854025 : Blo 1901435 2854025 := bstep (se 2 (by rfl) ⟨1070259, by rfl⟩ : syracuseStep 2854025 = 2140519) B2140519
theorem B1902683 : Blo 1901435 1902683 := bstep (se 1 (by rfl) ⟨1427012, by rfl⟩ : syracuseStep 1902683 = 2854025) B2854025
theorem B9632357 : Blo 1901435 9632357 := bbase (se 4 (by rfl) ⟨903033, by rfl⟩ : syracuseStep 9632357 = 1806067) (by norm_num)
theorem B6421571 : Blo 1901435 6421571 := bstep (se 1 (by rfl) ⟨4816178, by rfl⟩ : syracuseStep 6421571 = 9632357) B9632357
theorem B4281047 : Blo 1901435 4281047 := bstep (se 1 (by rfl) ⟨3210785, by rfl⟩ : syracuseStep 4281047 = 6421571) B6421571
theorem B2854031 : Blo 1901435 2854031 := bstep (se 1 (by rfl) ⟨2140523, by rfl⟩ : syracuseStep 2854031 = 4281047) B4281047
theorem B1902687 : Blo 1901435 1902687 := bstep (se 1 (by rfl) ⟨1427015, by rfl⟩ : syracuseStep 1902687 = 2854031) B2854031
theorem B2854037 : Blo 1901435 2854037 := bbase (se 6 (by rfl) ⟨66891, by rfl⟩ : syracuseStep 2854037 = 133783) (by norm_num)
theorem B1902691 : Blo 1901435 1902691 := bstep (se 1 (by rfl) ⟨1427018, by rfl⟩ : syracuseStep 1902691 = 2854037) B2854037
theorem B21968597 : Blo 1901435 21968597 := bbase (se 7 (by rfl) ⟨257444, by rfl⟩ : syracuseStep 21968597 = 514889) (by norm_num)
theorem B14645731 : Blo 1901435 14645731 := bstep (se 1 (by rfl) ⟨10984298, by rfl⟩ : syracuseStep 14645731 = 21968597) B21968597
theorem B19527641 : Blo 1901435 19527641 := bstep (se 2 (by rfl) ⟨7322865, by rfl⟩ : syracuseStep 19527641 = 14645731) B14645731
theorem B13018427 : Blo 1901435 13018427 := bstep (se 1 (by rfl) ⟨9763820, by rfl⟩ : syracuseStep 13018427 = 19527641) B19527641
theorem B8678951 : Blo 1901435 8678951 := bstep (se 1 (by rfl) ⟨6509213, by rfl⟩ : syracuseStep 8678951 = 13018427) B13018427
theorem B5785967 : Blo 1901435 5785967 := bstep (se 1 (by rfl) ⟨4339475, by rfl⟩ : syracuseStep 5785967 = 8678951) B8678951
theorem B3857311 : Blo 1901435 3857311 := bstep (se 1 (by rfl) ⟨2892983, by rfl⟩ : syracuseStep 3857311 = 5785967) B5785967
theorem B20572325 : Blo 1901435 20572325 := bstep (se 4 (by rfl) ⟨1928655, by rfl⟩ : syracuseStep 20572325 = 3857311) B3857311
theorem B13714883 : Blo 1901435 13714883 := bstep (se 1 (by rfl) ⟨10286162, by rfl⟩ : syracuseStep 13714883 = 20572325) B20572325
theorem B9143255 : Blo 1901435 9143255 := bstep (se 1 (by rfl) ⟨6857441, by rfl⟩ : syracuseStep 9143255 = 13714883) B13714883
theorem B6095503 : Blo 1901435 6095503 := bstep (se 1 (by rfl) ⟨4571627, by rfl⟩ : syracuseStep 6095503 = 9143255) B9143255
theorem B8127337 : Blo 1901435 8127337 := bstep (se 2 (by rfl) ⟨3047751, by rfl⟩ : syracuseStep 8127337 = 6095503) B6095503
theorem B10836449 : Blo 1901435 10836449 := bstep (se 2 (by rfl) ⟨4063668, by rfl⟩ : syracuseStep 10836449 = 8127337) B8127337
theorem B7224299 : Blo 1901435 7224299 := bstep (se 1 (by rfl) ⟨5418224, by rfl⟩ : syracuseStep 7224299 = 10836449) B10836449
theorem B4816199 : Blo 1901435 4816199 := bstep (se 1 (by rfl) ⟨3612149, by rfl⟩ : syracuseStep 4816199 = 7224299) B7224299
theorem B3210799 : Blo 1901435 3210799 := bstep (se 1 (by rfl) ⟨2408099, by rfl⟩ : syracuseStep 3210799 = 4816199) B4816199
theorem B4281065 : Blo 1901435 4281065 := bstep (se 2 (by rfl) ⟨1605399, by rfl⟩ : syracuseStep 4281065 = 3210799) B3210799
theorem B2854043 : Blo 1901435 2854043 := bstep (se 1 (by rfl) ⟨2140532, by rfl⟩ : syracuseStep 2854043 = 4281065) B4281065
theorem B1902695 : Blo 1901435 1902695 := bstep (se 1 (by rfl) ⟨1427021, by rfl⟩ : syracuseStep 1902695 = 2854043) B2854043
theorem B2140537 : Blo 1901435 2140537 := bbase (se 2 (by rfl) ⟨802701, by rfl⟩ : syracuseStep 2140537 = 1605403) (by norm_num)
theorem B2854049 : Blo 1901435 2854049 := bstep (se 2 (by rfl) ⟨1070268, by rfl⟩ : syracuseStep 2854049 = 2140537) B2140537
theorem B1902699 : Blo 1901435 1902699 := bstep (se 1 (by rfl) ⟨1427024, by rfl⟩ : syracuseStep 1902699 = 2854049) B2854049
theorem B39055445 : Blo 1901435 39055445 := bbase (se 8 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 39055445 = 457681) (by norm_num)
theorem B26036963 : Blo 1901435 26036963 := bstep (se 1 (by rfl) ⟨19527722, by rfl⟩ : syracuseStep 26036963 = 39055445) B39055445
theorem B17357975 : Blo 1901435 17357975 := bstep (se 1 (by rfl) ⟨13018481, by rfl⟩ : syracuseStep 17357975 = 26036963) B26036963
theorem B11571983 : Blo 1901435 11571983 := bstep (se 1 (by rfl) ⟨8678987, by rfl⟩ : syracuseStep 11571983 = 17357975) B17357975
theorem B7714655 : Blo 1901435 7714655 := bstep (se 1 (by rfl) ⟨5785991, by rfl⟩ : syracuseStep 7714655 = 11571983) B11571983
theorem B5143103 : Blo 1901435 5143103 := bstep (se 1 (by rfl) ⟨3857327, by rfl⟩ : syracuseStep 5143103 = 7714655) B7714655
theorem B3428735 : Blo 1901435 3428735 := bstep (se 1 (by rfl) ⟨2571551, by rfl⟩ : syracuseStep 3428735 = 5143103) B5143103
theorem B9143293 : Blo 1901435 9143293 := bstep (se 3 (by rfl) ⟨1714367, by rfl⟩ : syracuseStep 9143293 = 3428735) B3428735
theorem B12191057 : Blo 1901435 12191057 := bstep (se 2 (by rfl) ⟨4571646, by rfl⟩ : syracuseStep 12191057 = 9143293) B9143293
theorem B8127371 : Blo 1901435 8127371 := bstep (se 1 (by rfl) ⟨6095528, by rfl⟩ : syracuseStep 8127371 = 12191057) B12191057
theorem B5418247 : Blo 1901435 5418247 := bstep (se 1 (by rfl) ⟨4063685, by rfl⟩ : syracuseStep 5418247 = 8127371) B8127371
theorem B7224329 : Blo 1901435 7224329 := bstep (se 2 (by rfl) ⟨2709123, by rfl⟩ : syracuseStep 7224329 = 5418247) B5418247
theorem B4816219 : Blo 1901435 4816219 := bstep (se 1 (by rfl) ⟨3612164, by rfl⟩ : syracuseStep 4816219 = 7224329) B7224329
theorem B6421625 : Blo 1901435 6421625 := bstep (se 2 (by rfl) ⟨2408109, by rfl⟩ : syracuseStep 6421625 = 4816219) B4816219
theorem B4281083 : Blo 1901435 4281083 := bstep (se 1 (by rfl) ⟨3210812, by rfl⟩ : syracuseStep 4281083 = 6421625) B6421625
theorem B2854055 : Blo 1901435 2854055 := bstep (se 1 (by rfl) ⟨2140541, by rfl⟩ : syracuseStep 2854055 = 4281083) B4281083
theorem B1902703 : Blo 1901435 1902703 := bstep (se 1 (by rfl) ⟨1427027, by rfl⟩ : syracuseStep 1902703 = 2854055) B2854055
theorem B2854061 : Blo 1901435 2854061 := bbase (se 3 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 2854061 = 1070273) (by norm_num)
theorem B1902707 : Blo 1901435 1902707 := bstep (se 1 (by rfl) ⟨1427030, by rfl⟩ : syracuseStep 1902707 = 2854061) B2854061
theorem B4281101 : Blo 1901435 4281101 := bbase (se 3 (by rfl) ⟨802706, by rfl⟩ : syracuseStep 4281101 = 1605413) (by norm_num)
theorem B2854067 : Blo 1901435 2854067 := bstep (se 1 (by rfl) ⟨2140550, by rfl⟩ : syracuseStep 2854067 = 4281101) B4281101
theorem B1902711 : Blo 1901435 1902711 := bstep (se 1 (by rfl) ⟨1427033, by rfl⟩ : syracuseStep 1902711 = 2854067) B2854067
theorem B2408125 : Blo 1901435 2408125 := bbase (se 3 (by rfl) ⟨451523, by rfl⟩ : syracuseStep 2408125 = 903047) (by norm_num)
theorem B3210833 : Blo 1901435 3210833 := bstep (se 2 (by rfl) ⟨1204062, by rfl⟩ : syracuseStep 3210833 = 2408125) B2408125
theorem B2140555 : Blo 1901435 2140555 := bstep (se 1 (by rfl) ⟨1605416, by rfl⟩ : syracuseStep 2140555 = 3210833) B3210833
theorem B2854073 : Blo 1901435 2854073 := bstep (se 2 (by rfl) ⟨1070277, by rfl⟩ : syracuseStep 2854073 = 2140555) B2140555
theorem B1902715 : Blo 1901435 1902715 := bstep (se 1 (by rfl) ⟨1427036, by rfl⟩ : syracuseStep 1902715 = 2854073) B2854073
theorem B2746109 : Blo 1901435 2746109 := bbase (se 3 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 2746109 = 1029791) (by norm_num)
theorem B7322957 : Blo 1901435 7322957 := bstep (se 3 (by rfl) ⟨1373054, by rfl⟩ : syracuseStep 7322957 = 2746109) B2746109
theorem B4881971 : Blo 1901435 4881971 := bstep (se 1 (by rfl) ⟨3661478, by rfl⟩ : syracuseStep 4881971 = 7322957) B7322957
theorem B13018589 : Blo 1901435 13018589 := bstep (se 3 (by rfl) ⟨2440985, by rfl⟩ : syracuseStep 13018589 = 4881971) B4881971
theorem B8679059 : Blo 1901435 8679059 := bstep (se 1 (by rfl) ⟨6509294, by rfl⟩ : syracuseStep 8679059 = 13018589) B13018589
theorem B5786039 : Blo 1901435 5786039 := bstep (se 1 (by rfl) ⟨4339529, by rfl⟩ : syracuseStep 5786039 = 8679059) B8679059
theorem B15429437 : Blo 1901435 15429437 := bstep (se 3 (by rfl) ⟨2893019, by rfl⟩ : syracuseStep 15429437 = 5786039) B5786039
theorem B10286291 : Blo 1901435 10286291 := bstep (se 1 (by rfl) ⟨7714718, by rfl⟩ : syracuseStep 10286291 = 15429437) B15429437
theorem B6857527 : Blo 1901435 6857527 := bstep (se 1 (by rfl) ⟨5143145, by rfl⟩ : syracuseStep 6857527 = 10286291) B10286291
theorem B9143369 : Blo 1901435 9143369 := bstep (se 2 (by rfl) ⟨3428763, by rfl⟩ : syracuseStep 9143369 = 6857527) B6857527
theorem B6095579 : Blo 1901435 6095579 := bstep (se 1 (by rfl) ⟨4571684, by rfl⟩ : syracuseStep 6095579 = 9143369) B9143369
theorem B16254877 : Blo 1901435 16254877 := bstep (se 3 (by rfl) ⟨3047789, by rfl⟩ : syracuseStep 16254877 = 6095579) B6095579
theorem B21673169 : Blo 1901435 21673169 := bstep (se 2 (by rfl) ⟨8127438, by rfl⟩ : syracuseStep 21673169 = 16254877) B16254877
theorem B14448779 : Blo 1901435 14448779 := bstep (se 1 (by rfl) ⟨10836584, by rfl⟩ : syracuseStep 14448779 = 21673169) B21673169
theorem B9632519 : Blo 1901435 9632519 := bstep (se 1 (by rfl) ⟨7224389, by rfl⟩ : syracuseStep 9632519 = 14448779) B14448779
theorem B6421679 : Blo 1901435 6421679 := bstep (se 1 (by rfl) ⟨4816259, by rfl⟩ : syracuseStep 6421679 = 9632519) B9632519
theorem B4281119 : Blo 1901435 4281119 := bstep (se 1 (by rfl) ⟨3210839, by rfl⟩ : syracuseStep 4281119 = 6421679) B6421679
theorem B2854079 : Blo 1901435 2854079 := bstep (se 1 (by rfl) ⟨2140559, by rfl⟩ : syracuseStep 2854079 = 4281119) B4281119
theorem B1902719 : Blo 1901435 1902719 := bstep (se 1 (by rfl) ⟨1427039, by rfl⟩ : syracuseStep 1902719 = 2854079) B2854079
theorem B2854085 : Blo 1901435 2854085 := bbase (se 4 (by rfl) ⟨267570, by rfl⟩ : syracuseStep 2854085 = 535141) (by norm_num)
theorem B1902723 : Blo 1901435 1902723 := bstep (se 1 (by rfl) ⟨1427042, by rfl⟩ : syracuseStep 1902723 = 2854085) B2854085
theorem B3210853 : Blo 1901435 3210853 := bbase (se 4 (by rfl) ⟨301017, by rfl⟩ : syracuseStep 3210853 = 602035) (by norm_num)
theorem B4281137 : Blo 1901435 4281137 := bstep (se 2 (by rfl) ⟨1605426, by rfl⟩ : syracuseStep 4281137 = 3210853) B3210853
theorem B2854091 : Blo 1901435 2854091 := bstep (se 1 (by rfl) ⟨2140568, by rfl⟩ : syracuseStep 2854091 = 4281137) B4281137
theorem B1902727 : Blo 1901435 1902727 := bstep (se 1 (by rfl) ⟨1427045, by rfl⟩ : syracuseStep 1902727 = 2854091) B2854091
theorem B2140573 : Blo 1901435 2140573 := bbase (se 3 (by rfl) ⟨401357, by rfl⟩ : syracuseStep 2140573 = 802715) (by norm_num)
theorem B2854097 : Blo 1901435 2854097 := bstep (se 2 (by rfl) ⟨1070286, by rfl⟩ : syracuseStep 2854097 = 2140573) B2140573
theorem B1902731 : Blo 1901435 1902731 := bstep (se 1 (by rfl) ⟨1427048, by rfl⟩ : syracuseStep 1902731 = 2854097) B2854097
theorem B6421733 : Blo 1901435 6421733 := bbase (se 4 (by rfl) ⟨602037, by rfl⟩ : syracuseStep 6421733 = 1204075) (by norm_num)
theorem B4281155 : Blo 1901435 4281155 := bstep (se 1 (by rfl) ⟨3210866, by rfl⟩ : syracuseStep 4281155 = 6421733) B6421733
theorem B2854103 : Blo 1901435 2854103 := bstep (se 1 (by rfl) ⟨2140577, by rfl⟩ : syracuseStep 2854103 = 4281155) B4281155
theorem B1902735 : Blo 1901435 1902735 := bstep (se 1 (by rfl) ⟨1427051, by rfl⟩ : syracuseStep 1902735 = 2854103) B2854103
theorem B2854109 : Blo 1901435 2854109 := bbase (se 3 (by rfl) ⟨535145, by rfl⟩ : syracuseStep 2854109 = 1070291) (by norm_num)
theorem B1902739 : Blo 1901435 1902739 := bstep (se 1 (by rfl) ⟨1427054, by rfl⟩ : syracuseStep 1902739 = 2854109) B2854109
theorem B4281173 : Blo 1901435 4281173 := bbase (se 9 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 4281173 = 25085) (by norm_num)
theorem B2854115 : Blo 1901435 2854115 := bstep (se 1 (by rfl) ⟨2140586, by rfl⟩ : syracuseStep 2854115 = 4281173) B4281173
theorem B1902743 : Blo 1901435 1902743 := bstep (se 1 (by rfl) ⟨1427057, by rfl⟩ : syracuseStep 1902743 = 2854115) B2854115
theorem B5418373 : Blo 1901435 5418373 := bbase (se 4 (by rfl) ⟨507972, by rfl⟩ : syracuseStep 5418373 = 1015945) (by norm_num)
theorem B7224497 : Blo 1901435 7224497 := bstep (se 2 (by rfl) ⟨2709186, by rfl⟩ : syracuseStep 7224497 = 5418373) B5418373
theorem B4816331 : Blo 1901435 4816331 := bstep (se 1 (by rfl) ⟨3612248, by rfl⟩ : syracuseStep 4816331 = 7224497) B7224497
theorem B3210887 : Blo 1901435 3210887 := bstep (se 1 (by rfl) ⟨2408165, by rfl⟩ : syracuseStep 3210887 = 4816331) B4816331
theorem B2140591 : Blo 1901435 2140591 := bstep (se 1 (by rfl) ⟨1605443, by rfl⟩ : syracuseStep 2140591 = 3210887) B3210887
theorem B2854121 : Blo 1901435 2854121 := bstep (se 2 (by rfl) ⟨1070295, by rfl⟩ : syracuseStep 2854121 = 2140591) B2140591
theorem B1902747 : Blo 1901435 1902747 := bstep (se 1 (by rfl) ⟨1427060, by rfl⟩ : syracuseStep 1902747 = 2854121) B2854121
theorem B26392853 : Blo 1901435 26392853 := bbase (se 6 (by rfl) ⟨618582, by rfl⟩ : syracuseStep 26392853 = 1237165) (by norm_num)
theorem B17595235 : Blo 1901435 17595235 := bstep (se 1 (by rfl) ⟨13196426, by rfl⟩ : syracuseStep 17595235 = 26392853) B26392853
theorem B93841253 : Blo 1901435 93841253 := bstep (se 4 (by rfl) ⟨8797617, by rfl⟩ : syracuseStep 93841253 = 17595235) B17595235
theorem B62560835 : Blo 1901435 62560835 := bstep (se 1 (by rfl) ⟨46920626, by rfl⟩ : syracuseStep 62560835 = 93841253) B93841253
theorem B41707223 : Blo 1901435 41707223 := bstep (se 1 (by rfl) ⟨31280417, by rfl⟩ : syracuseStep 41707223 = 62560835) B62560835
theorem B27804815 : Blo 1901435 27804815 := bstep (se 1 (by rfl) ⟨20853611, by rfl⟩ : syracuseStep 27804815 = 41707223) B41707223
theorem B18536543 : Blo 1901435 18536543 := bstep (se 1 (by rfl) ⟨13902407, by rfl⟩ : syracuseStep 18536543 = 27804815) B27804815
theorem B12357695 : Blo 1901435 12357695 := bstep (se 1 (by rfl) ⟨9268271, by rfl⟩ : syracuseStep 12357695 = 18536543) B18536543
theorem B32953853 : Blo 1901435 32953853 := bstep (se 3 (by rfl) ⟨6178847, by rfl⟩ : syracuseStep 32953853 = 12357695) B12357695
theorem B21969235 : Blo 1901435 21969235 := bstep (se 1 (by rfl) ⟨16476926, by rfl⟩ : syracuseStep 21969235 = 32953853) B32953853
theorem B117169253 : Blo 1901435 117169253 := bstep (se 4 (by rfl) ⟨10984617, by rfl⟩ : syracuseStep 117169253 = 21969235) B21969235
theorem B78112835 : Blo 1901435 78112835 := bstep (se 1 (by rfl) ⟨58584626, by rfl⟩ : syracuseStep 78112835 = 117169253) B117169253
theorem B52075223 : Blo 1901435 52075223 := bstep (se 1 (by rfl) ⟨39056417, by rfl⟩ : syracuseStep 52075223 = 78112835) B78112835
theorem B34716815 : Blo 1901435 34716815 := bstep (se 1 (by rfl) ⟨26037611, by rfl⟩ : syracuseStep 34716815 = 52075223) B52075223
theorem B23144543 : Blo 1901435 23144543 := bstep (se 1 (by rfl) ⟨17358407, by rfl⟩ : syracuseStep 23144543 = 34716815) B34716815
theorem B15429695 : Blo 1901435 15429695 := bstep (se 1 (by rfl) ⟨11572271, by rfl⟩ : syracuseStep 15429695 = 23144543) B23144543
theorem B41145853 : Blo 1901435 41145853 := bstep (se 3 (by rfl) ⟨7714847, by rfl⟩ : syracuseStep 41145853 = 15429695) B15429695
theorem B54861137 : Blo 1901435 54861137 := bstep (se 2 (by rfl) ⟨20572926, by rfl⟩ : syracuseStep 54861137 = 41145853) B41145853
theorem B36574091 : Blo 1901435 36574091 := bstep (se 1 (by rfl) ⟨27430568, by rfl⟩ : syracuseStep 36574091 = 54861137) B54861137
theorem B24382727 : Blo 1901435 24382727 := bstep (se 1 (by rfl) ⟨18287045, by rfl⟩ : syracuseStep 24382727 = 36574091) B36574091
theorem B16255151 : Blo 1901435 16255151 := bstep (se 1 (by rfl) ⟨12191363, by rfl⟩ : syracuseStep 16255151 = 24382727) B24382727
theorem B10836767 : Blo 1901435 10836767 := bstep (se 1 (by rfl) ⟨8127575, by rfl⟩ : syracuseStep 10836767 = 16255151) B16255151
theorem B7224511 : Blo 1901435 7224511 := bstep (se 1 (by rfl) ⟨5418383, by rfl⟩ : syracuseStep 7224511 = 10836767) B10836767
theorem B9632681 : Blo 1901435 9632681 := bstep (se 2 (by rfl) ⟨3612255, by rfl⟩ : syracuseStep 9632681 = 7224511) B7224511
theorem B6421787 : Blo 1901435 6421787 := bstep (se 1 (by rfl) ⟨4816340, by rfl⟩ : syracuseStep 6421787 = 9632681) B9632681
theorem B4281191 : Blo 1901435 4281191 := bstep (se 1 (by rfl) ⟨3210893, by rfl⟩ : syracuseStep 4281191 = 6421787) B6421787
theorem B2854127 : Blo 1901435 2854127 := bstep (se 1 (by rfl) ⟨2140595, by rfl⟩ : syracuseStep 2854127 = 4281191) B4281191
theorem B1902751 : Blo 1901435 1902751 := bstep (se 1 (by rfl) ⟨1427063, by rfl⟩ : syracuseStep 1902751 = 2854127) B2854127
theorem B2854133 : Blo 1901435 2854133 := bbase (se 5 (by rfl) ⟨133787, by rfl⟩ : syracuseStep 2854133 = 267575) (by norm_num)
theorem B1902755 : Blo 1901435 1902755 := bstep (se 1 (by rfl) ⟨1427066, by rfl⟩ : syracuseStep 1902755 = 2854133) B2854133
theorem B3254717 : Blo 1901435 3254717 := bbase (se 3 (by rfl) ⟨610259, by rfl⟩ : syracuseStep 3254717 = 1220519) (by norm_num)
theorem B2169811 : Blo 1901435 2169811 := bstep (se 1 (by rfl) ⟨1627358, by rfl⟩ : syracuseStep 2169811 = 3254717) B3254717
theorem B2893081 : Blo 1901435 2893081 := bstep (se 2 (by rfl) ⟨1084905, by rfl⟩ : syracuseStep 2893081 = 2169811) B2169811
theorem B3857441 : Blo 1901435 3857441 := bstep (se 2 (by rfl) ⟨1446540, by rfl⟩ : syracuseStep 3857441 = 2893081) B2893081
theorem B10286509 : Blo 1901435 10286509 := bstep (se 3 (by rfl) ⟨1928720, by rfl⟩ : syracuseStep 10286509 = 3857441) B3857441
theorem B13715345 : Blo 1901435 13715345 := bstep (se 2 (by rfl) ⟨5143254, by rfl⟩ : syracuseStep 13715345 = 10286509) B10286509
theorem B9143563 : Blo 1901435 9143563 := bstep (se 1 (by rfl) ⟨6857672, by rfl⟩ : syracuseStep 9143563 = 13715345) B13715345
theorem B12191417 : Blo 1901435 12191417 := bstep (se 2 (by rfl) ⟨4571781, by rfl⟩ : syracuseStep 12191417 = 9143563) B9143563
theorem B8127611 : Blo 1901435 8127611 := bstep (se 1 (by rfl) ⟨6095708, by rfl⟩ : syracuseStep 8127611 = 12191417) B12191417
theorem B5418407 : Blo 1901435 5418407 := bstep (se 1 (by rfl) ⟨4063805, by rfl⟩ : syracuseStep 5418407 = 8127611) B8127611
theorem B3612271 : Blo 1901435 3612271 := bstep (se 1 (by rfl) ⟨2709203, by rfl⟩ : syracuseStep 3612271 = 5418407) B5418407
theorem B4816361 : Blo 1901435 4816361 := bstep (se 2 (by rfl) ⟨1806135, by rfl⟩ : syracuseStep 4816361 = 3612271) B3612271
theorem B3210907 : Blo 1901435 3210907 := bstep (se 1 (by rfl) ⟨2408180, by rfl⟩ : syracuseStep 3210907 = 4816361) B4816361
theorem B4281209 : Blo 1901435 4281209 := bstep (se 2 (by rfl) ⟨1605453, by rfl⟩ : syracuseStep 4281209 = 3210907) B3210907
theorem B2854139 : Blo 1901435 2854139 := bstep (se 1 (by rfl) ⟨2140604, by rfl⟩ : syracuseStep 2854139 = 4281209) B4281209
theorem B1902759 : Blo 1901435 1902759 := bstep (se 1 (by rfl) ⟨1427069, by rfl⟩ : syracuseStep 1902759 = 2854139) B2854139
theorem B2140609 : Blo 1901435 2140609 := bbase (se 2 (by rfl) ⟨802728, by rfl⟩ : syracuseStep 2140609 = 1605457) (by norm_num)
theorem B2854145 : Blo 1901435 2854145 := bstep (se 2 (by rfl) ⟨1070304, by rfl⟩ : syracuseStep 2854145 = 2140609) B2140609
theorem B1902763 : Blo 1901435 1902763 := bstep (se 1 (by rfl) ⟨1427072, by rfl⟩ : syracuseStep 1902763 = 2854145) B2854145
theorem B4816381 : Blo 1901435 4816381 := bbase (se 3 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 4816381 = 1806143) (by norm_num)
theorem B6421841 : Blo 1901435 6421841 := bstep (se 2 (by rfl) ⟨2408190, by rfl⟩ : syracuseStep 6421841 = 4816381) B4816381
theorem B4281227 : Blo 1901435 4281227 := bstep (se 1 (by rfl) ⟨3210920, by rfl⟩ : syracuseStep 4281227 = 6421841) B6421841
theorem B2854151 : Blo 1901435 2854151 := bstep (se 1 (by rfl) ⟨2140613, by rfl⟩ : syracuseStep 2854151 = 4281227) B4281227
theorem B1902767 : Blo 1901435 1902767 := bstep (se 1 (by rfl) ⟨1427075, by rfl⟩ : syracuseStep 1902767 = 2854151) B2854151
theorem B2854157 : Blo 1901435 2854157 := bbase (se 3 (by rfl) ⟨535154, by rfl⟩ : syracuseStep 2854157 = 1070309) (by norm_num)
theorem B1902771 : Blo 1901435 1902771 := bstep (se 1 (by rfl) ⟨1427078, by rfl⟩ : syracuseStep 1902771 = 2854157) B2854157
theorem B4281245 : Blo 1901435 4281245 := bbase (se 3 (by rfl) ⟨802733, by rfl⟩ : syracuseStep 4281245 = 1605467) (by norm_num)
theorem B2854163 : Blo 1901435 2854163 := bstep (se 1 (by rfl) ⟨2140622, by rfl⟩ : syracuseStep 2854163 = 4281245) B4281245
theorem B1902775 : Blo 1901435 1902775 := bstep (se 1 (by rfl) ⟨1427081, by rfl⟩ : syracuseStep 1902775 = 2854163) B2854163
theorem B3210941 : Blo 1901435 3210941 := bbase (se 3 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 3210941 = 1204103) (by norm_num)
theorem B2140627 : Blo 1901435 2140627 := bstep (se 1 (by rfl) ⟨1605470, by rfl⟩ : syracuseStep 2140627 = 3210941) B3210941
theorem B2854169 : Blo 1901435 2854169 := bstep (se 2 (by rfl) ⟨1070313, by rfl⟩ : syracuseStep 2854169 = 2140627) B2140627
theorem B1902779 : Blo 1901435 1902779 := bstep (se 1 (by rfl) ⟨1427084, by rfl⟩ : syracuseStep 1902779 = 2854169) B2854169
theorem B10836949 : Blo 1901435 10836949 := bbase (se 7 (by rfl) ⟨126995, by rfl⟩ : syracuseStep 10836949 = 253991) (by norm_num)
theorem B14449265 : Blo 1901435 14449265 := bstep (se 2 (by rfl) ⟨5418474, by rfl⟩ : syracuseStep 14449265 = 10836949) B10836949
theorem B9632843 : Blo 1901435 9632843 := bstep (se 1 (by rfl) ⟨7224632, by rfl⟩ : syracuseStep 9632843 = 14449265) B14449265
theorem B6421895 : Blo 1901435 6421895 := bstep (se 1 (by rfl) ⟨4816421, by rfl⟩ : syracuseStep 6421895 = 9632843) B9632843
theorem B4281263 : Blo 1901435 4281263 := bstep (se 1 (by rfl) ⟨3210947, by rfl⟩ : syracuseStep 4281263 = 6421895) B6421895
theorem B2854175 : Blo 1901435 2854175 := bstep (se 1 (by rfl) ⟨2140631, by rfl⟩ : syracuseStep 2854175 = 4281263) B4281263
theorem B1902783 : Blo 1901435 1902783 := bstep (se 1 (by rfl) ⟨1427087, by rfl⟩ : syracuseStep 1902783 = 2854175) B2854175
theorem B2854181 : Blo 1901435 2854181 := bbase (se 4 (by rfl) ⟨267579, by rfl⟩ : syracuseStep 2854181 = 535159) (by norm_num)
theorem B1902787 : Blo 1901435 1902787 := bstep (se 1 (by rfl) ⟨1427090, by rfl⟩ : syracuseStep 1902787 = 2854181) B2854181
theorem B2408221 : Blo 1901435 2408221 := bbase (se 3 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 2408221 = 903083) (by norm_num)
theorem B3210961 : Blo 1901435 3210961 := bstep (se 2 (by rfl) ⟨1204110, by rfl⟩ : syracuseStep 3210961 = 2408221) B2408221
theorem B4281281 : Blo 1901435 4281281 := bstep (se 2 (by rfl) ⟨1605480, by rfl⟩ : syracuseStep 4281281 = 3210961) B3210961
theorem B2854187 : Blo 1901435 2854187 := bstep (se 1 (by rfl) ⟨2140640, by rfl⟩ : syracuseStep 2854187 = 4281281) B4281281
theorem B1902791 : Blo 1901435 1902791 := bstep (se 1 (by rfl) ⟨1427093, by rfl⟩ : syracuseStep 1902791 = 2854187) B2854187
theorem B2140645 : Blo 1901435 2140645 := bbase (se 4 (by rfl) ⟨200685, by rfl⟩ : syracuseStep 2140645 = 401371) (by norm_num)
theorem B2854193 : Blo 1901435 2854193 := bstep (se 2 (by rfl) ⟨1070322, by rfl⟩ : syracuseStep 2854193 = 2140645) B2140645
theorem B1902795 : Blo 1901435 1902795 := bstep (se 1 (by rfl) ⟨1427096, by rfl⟩ : syracuseStep 1902795 = 2854193) B2854193
theorem B3428909 : Blo 1901435 3428909 := bbase (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) (by norm_num)
theorem B2285939 : Blo 1901435 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B6095837 : Blo 1901435 6095837 := bstep (se 3 (by rfl) ⟨1142969, by rfl⟩ : syracuseStep 6095837 = 2285939) B2285939
theorem B4063891 : Blo 1901435 4063891 := bstep (se 1 (by rfl) ⟨3047918, by rfl⟩ : syracuseStep 4063891 = 6095837) B6095837
theorem B5418521 : Blo 1901435 5418521 := bstep (se 2 (by rfl) ⟨2031945, by rfl⟩ : syracuseStep 5418521 = 4063891) B4063891
theorem B3612347 : Blo 1901435 3612347 := bstep (se 1 (by rfl) ⟨2709260, by rfl⟩ : syracuseStep 3612347 = 5418521) B5418521
theorem B2408231 : Blo 1901435 2408231 := bstep (se 1 (by rfl) ⟨1806173, by rfl⟩ : syracuseStep 2408231 = 3612347) B3612347
theorem B6421949 : Blo 1901435 6421949 := bstep (se 3 (by rfl) ⟨1204115, by rfl⟩ : syracuseStep 6421949 = 2408231) B2408231
theorem B4281299 : Blo 1901435 4281299 := bstep (se 1 (by rfl) ⟨3210974, by rfl⟩ : syracuseStep 4281299 = 6421949) B6421949
theorem B2854199 : Blo 1901435 2854199 := bstep (se 1 (by rfl) ⟨2140649, by rfl⟩ : syracuseStep 2854199 = 4281299) B4281299
theorem B1902799 : Blo 1901435 1902799 := bstep (se 1 (by rfl) ⟨1427099, by rfl⟩ : syracuseStep 1902799 = 2854199) B2854199
theorem B2854205 : Blo 1901435 2854205 := bbase (se 3 (by rfl) ⟨535163, by rfl⟩ : syracuseStep 2854205 = 1070327) (by norm_num)
theorem B1902803 : Blo 1901435 1902803 := bstep (se 1 (by rfl) ⟨1427102, by rfl⟩ : syracuseStep 1902803 = 2854205) B2854205
theorem B4281317 : Blo 1901435 4281317 := bbase (se 4 (by rfl) ⟨401373, by rfl⟩ : syracuseStep 4281317 = 802747) (by norm_num)
theorem B2854211 : Blo 1901435 2854211 := bstep (se 1 (by rfl) ⟨2140658, by rfl⟩ : syracuseStep 2854211 = 4281317) B4281317
theorem B1902807 : Blo 1901435 1902807 := bstep (se 1 (by rfl) ⟨1427105, by rfl⟩ : syracuseStep 1902807 = 2854211) B2854211
theorem B4816493 : Blo 1901435 4816493 := bbase (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) (by norm_num)
theorem B3210995 : Blo 1901435 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B2140663 : Blo 1901435 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B2854217 : Blo 1901435 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B1902811 : Blo 1901435 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B4063925 : Blo 1901435 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B2709283 : Blo 1901435 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B3612377 : Blo 1901435 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B9633005 : Blo 1901435 9633005 := bstep (se 3 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 9633005 = 3612377) B3612377
theorem B6422003 : Blo 1901435 6422003 := bstep (se 1 (by rfl) ⟨4816502, by rfl⟩ : syracuseStep 6422003 = 9633005) B9633005
theorem B4281335 : Blo 1901435 4281335 := bstep (se 1 (by rfl) ⟨3211001, by rfl⟩ : syracuseStep 4281335 = 6422003) B6422003
theorem B2854223 : Blo 1901435 2854223 := bstep (se 1 (by rfl) ⟨2140667, by rfl⟩ : syracuseStep 2854223 = 4281335) B4281335
theorem B1902815 : Blo 1901435 1902815 := bstep (se 1 (by rfl) ⟨1427111, by rfl⟩ : syracuseStep 1902815 = 2854223) B2854223
theorem B2854229 : Blo 1901435 2854229 := bbase (se 11 (by rfl) ⟨2090, by rfl⟩ : syracuseStep 2854229 = 4181) (by norm_num)
theorem B1902819 : Blo 1901435 1902819 := bstep (se 1 (by rfl) ⟨1427114, by rfl⟩ : syracuseStep 1902819 = 2854229) B2854229
theorem B3047957 : Blo 1901435 3047957 := bbase (se 6 (by rfl) ⟨71436, by rfl⟩ : syracuseStep 3047957 = 142873) (by norm_num)
theorem B2031971 : Blo 1901435 2031971 := bstep (se 1 (by rfl) ⟨1523978, by rfl⟩ : syracuseStep 2031971 = 3047957) B3047957
theorem B5418589 : Blo 1901435 5418589 := bstep (se 3 (by rfl) ⟨1015985, by rfl⟩ : syracuseStep 5418589 = 2031971) B2031971
theorem B7224785 : Blo 1901435 7224785 := bstep (se 2 (by rfl) ⟨2709294, by rfl⟩ : syracuseStep 7224785 = 5418589) B5418589
theorem B4816523 : Blo 1901435 4816523 := bstep (se 1 (by rfl) ⟨3612392, by rfl⟩ : syracuseStep 4816523 = 7224785) B7224785
theorem B3211015 : Blo 1901435 3211015 := bstep (se 1 (by rfl) ⟨2408261, by rfl⟩ : syracuseStep 3211015 = 4816523) B4816523
theorem B4281353 : Blo 1901435 4281353 := bstep (se 2 (by rfl) ⟨1605507, by rfl⟩ : syracuseStep 4281353 = 3211015) B3211015
theorem B2854235 : Blo 1901435 2854235 := bstep (se 1 (by rfl) ⟨2140676, by rfl⟩ : syracuseStep 2854235 = 4281353) B4281353
theorem B1902823 : Blo 1901435 1902823 := bstep (se 1 (by rfl) ⟨1427117, by rfl⟩ : syracuseStep 1902823 = 2854235) B2854235
theorem B2140681 : Blo 1901435 2140681 := bbase (se 2 (by rfl) ⟨802755, by rfl⟩ : syracuseStep 2140681 = 1605511) (by norm_num)
theorem B2854241 : Blo 1901435 2854241 := bstep (se 2 (by rfl) ⟨1070340, by rfl⟩ : syracuseStep 2854241 = 2140681) B2140681
theorem B1902827 : Blo 1901435 1902827 := bstep (se 1 (by rfl) ⟨1427120, by rfl⟩ : syracuseStep 1902827 = 2854241) B2854241
theorem B2441129 : Blo 1901435 2441129 := bbase (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) (by norm_num)
theorem B6509677 : Blo 1901435 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B8679569 : Blo 1901435 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B23145517 : Blo 1901435 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B30860689 : Blo 1901435 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B41147585 : Blo 1901435 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B27431723 : Blo 1901435 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B18287815 : Blo 1901435 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B24383753 : Blo 1901435 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B16255835 : Blo 1901435 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B10837223 : Blo 1901435 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B7224815 : Blo 1901435 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B4816543 : Blo 1901435 4816543 := bstep (se 1 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 4816543 = 7224815) B7224815
theorem B6422057 : Blo 1901435 6422057 := bstep (se 2 (by rfl) ⟨2408271, by rfl⟩ : syracuseStep 6422057 = 4816543) B4816543
theorem B4281371 : Blo 1901435 4281371 := bstep (se 1 (by rfl) ⟨3211028, by rfl⟩ : syracuseStep 4281371 = 6422057) B6422057
theorem B2854247 : Blo 1901435 2854247 := bstep (se 1 (by rfl) ⟨2140685, by rfl⟩ : syracuseStep 2854247 = 4281371) B4281371
theorem B1902831 : Blo 1901435 1902831 := bstep (se 1 (by rfl) ⟨1427123, by rfl⟩ : syracuseStep 1902831 = 2854247) B2854247
theorem B2854253 : Blo 1901435 2854253 := bbase (se 3 (by rfl) ⟨535172, by rfl⟩ : syracuseStep 2854253 = 1070345) (by norm_num)
theorem B1902835 : Blo 1901435 1902835 := bstep (se 1 (by rfl) ⟨1427126, by rfl⟩ : syracuseStep 1902835 = 2854253) B2854253
theorem B4281389 : Blo 1901435 4281389 := bbase (se 3 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 4281389 = 1605521) (by norm_num)
theorem B2854259 : Blo 1901435 2854259 := bstep (se 1 (by rfl) ⟨2140694, by rfl⟩ : syracuseStep 2854259 = 4281389) B4281389
theorem B1902839 : Blo 1901435 1902839 := bstep (se 1 (by rfl) ⟨1427129, by rfl⟩ : syracuseStep 1902839 = 2854259) B2854259
theorem B12191957 : Blo 1901435 12191957 := bbase (se 7 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 12191957 = 285749) (by norm_num)
theorem B8127971 : Blo 1901435 8127971 := bstep (se 1 (by rfl) ⟨6095978, by rfl⟩ : syracuseStep 8127971 = 12191957) B12191957
theorem B5418647 : Blo 1901435 5418647 := bstep (se 1 (by rfl) ⟨4063985, by rfl⟩ : syracuseStep 5418647 = 8127971) B8127971
theorem B3612431 : Blo 1901435 3612431 := bstep (se 1 (by rfl) ⟨2709323, by rfl⟩ : syracuseStep 3612431 = 5418647) B5418647
theorem B2408287 : Blo 1901435 2408287 := bstep (se 1 (by rfl) ⟨1806215, by rfl⟩ : syracuseStep 2408287 = 3612431) B3612431
theorem B3211049 : Blo 1901435 3211049 := bstep (se 2 (by rfl) ⟨1204143, by rfl⟩ : syracuseStep 3211049 = 2408287) B2408287
theorem B2140699 : Blo 1901435 2140699 := bstep (se 1 (by rfl) ⟨1605524, by rfl⟩ : syracuseStep 2140699 = 3211049) B3211049
theorem B2854265 : Blo 1901435 2854265 := bstep (se 2 (by rfl) ⟨1070349, by rfl⟩ : syracuseStep 2854265 = 2140699) B2140699
theorem B1902843 : Blo 1901435 1902843 := bstep (se 1 (by rfl) ⟨1427132, by rfl⟩ : syracuseStep 1902843 = 2854265) B2854265
theorem B6095989 : Blo 1901435 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B32511941 : Blo 1901435 32511941 := bstep (se 4 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 32511941 = 6095989) B6095989
theorem B21674627 : Blo 1901435 21674627 := bstep (se 1 (by rfl) ⟨16255970, by rfl⟩ : syracuseStep 21674627 = 32511941) B32511941
theorem B14449751 : Blo 1901435 14449751 := bstep (se 1 (by rfl) ⟨10837313, by rfl⟩ : syracuseStep 14449751 = 21674627) B21674627
theorem B9633167 : Blo 1901435 9633167 := bstep (se 1 (by rfl) ⟨7224875, by rfl⟩ : syracuseStep 9633167 = 14449751) B14449751
theorem B6422111 : Blo 1901435 6422111 := bstep (se 1 (by rfl) ⟨4816583, by rfl⟩ : syracuseStep 6422111 = 9633167) B9633167
theorem B4281407 : Blo 1901435 4281407 := bstep (se 1 (by rfl) ⟨3211055, by rfl⟩ : syracuseStep 4281407 = 6422111) B6422111
theorem B2854271 : Blo 1901435 2854271 := bstep (se 1 (by rfl) ⟨2140703, by rfl⟩ : syracuseStep 2854271 = 4281407) B4281407
theorem B1902847 : Blo 1901435 1902847 := bstep (se 1 (by rfl) ⟨1427135, by rfl⟩ : syracuseStep 1902847 = 2854271) B2854271
theorem B2854277 : Blo 1901435 2854277 := bbase (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) (by norm_num)
theorem B1902851 : Blo 1901435 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B3211069 : Blo 1901435 3211069 := bbase (se 3 (by rfl) ⟨602075, by rfl⟩ : syracuseStep 3211069 = 1204151) (by norm_num)
theorem B4281425 : Blo 1901435 4281425 := bstep (se 2 (by rfl) ⟨1605534, by rfl⟩ : syracuseStep 4281425 = 3211069) B3211069
theorem B2854283 : Blo 1901435 2854283 := bstep (se 1 (by rfl) ⟨2140712, by rfl⟩ : syracuseStep 2854283 = 4281425) B4281425
theorem B1902855 : Blo 1901435 1902855 := bstep (se 1 (by rfl) ⟨1427141, by rfl⟩ : syracuseStep 1902855 = 2854283) B2854283
theorem B2140717 : Blo 1901435 2140717 := bbase (se 3 (by rfl) ⟨401384, by rfl⟩ : syracuseStep 2140717 = 802769) (by norm_num)
theorem B2854289 : Blo 1901435 2854289 := bstep (se 2 (by rfl) ⟨1070358, by rfl⟩ : syracuseStep 2854289 = 2140717) B2140717
theorem B1902859 : Blo 1901435 1902859 := bstep (se 1 (by rfl) ⟨1427144, by rfl⟩ : syracuseStep 1902859 = 2854289) B2854289
theorem B6422165 : Blo 1901435 6422165 := bbase (se 6 (by rfl) ⟨150519, by rfl⟩ : syracuseStep 6422165 = 301039) (by norm_num)
theorem B4281443 : Blo 1901435 4281443 := bstep (se 1 (by rfl) ⟨3211082, by rfl⟩ : syracuseStep 4281443 = 6422165) B6422165
theorem B2854295 : Blo 1901435 2854295 := bstep (se 1 (by rfl) ⟨2140721, by rfl⟩ : syracuseStep 2854295 = 4281443) B4281443
theorem B1902863 : Blo 1901435 1902863 := bstep (se 1 (by rfl) ⟨1427147, by rfl⟩ : syracuseStep 1902863 = 2854295) B2854295
theorem B2854301 : Blo 1901435 2854301 := bbase (se 3 (by rfl) ⟨535181, by rfl⟩ : syracuseStep 2854301 = 1070363) (by norm_num)
theorem B1902867 : Blo 1901435 1902867 := bstep (se 1 (by rfl) ⟨1427150, by rfl⟩ : syracuseStep 1902867 = 2854301) B2854301
theorem B4281461 : Blo 1901435 4281461 := bbase (se 5 (by rfl) ⟨200693, by rfl⟩ : syracuseStep 4281461 = 401387) (by norm_num)
theorem B2854307 : Blo 1901435 2854307 := bstep (se 1 (by rfl) ⟨2140730, by rfl⟩ : syracuseStep 2854307 = 4281461) B4281461
theorem B1902871 : Blo 1901435 1902871 := bstep (se 1 (by rfl) ⟨1427153, by rfl⟩ : syracuseStep 1902871 = 2854307) B2854307
theorem B16256213 : Blo 1901435 16256213 := bbase (se 7 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 16256213 = 381005) (by norm_num)
theorem B10837475 : Blo 1901435 10837475 := bstep (se 1 (by rfl) ⟨8128106, by rfl⟩ : syracuseStep 10837475 = 16256213) B16256213
theorem B7224983 : Blo 1901435 7224983 := bstep (se 1 (by rfl) ⟨5418737, by rfl⟩ : syracuseStep 7224983 = 10837475) B10837475
theorem B4816655 : Blo 1901435 4816655 := bstep (se 1 (by rfl) ⟨3612491, by rfl⟩ : syracuseStep 4816655 = 7224983) B7224983
theorem B3211103 : Blo 1901435 3211103 := bstep (se 1 (by rfl) ⟨2408327, by rfl⟩ : syracuseStep 3211103 = 4816655) B4816655
theorem B2140735 : Blo 1901435 2140735 := bstep (se 1 (by rfl) ⟨1605551, by rfl⟩ : syracuseStep 2140735 = 3211103) B3211103
theorem B2854313 : Blo 1901435 2854313 := bstep (se 2 (by rfl) ⟨1070367, by rfl⟩ : syracuseStep 2854313 = 2140735) B2140735
theorem B1902875 : Blo 1901435 1902875 := bstep (se 1 (by rfl) ⟨1427156, by rfl⟩ : syracuseStep 1902875 = 2854313) B2854313
theorem B7224997 : Blo 1901435 7224997 := bbase (se 4 (by rfl) ⟨677343, by rfl⟩ : syracuseStep 7224997 = 1354687) (by norm_num)
theorem B9633329 : Blo 1901435 9633329 := bstep (se 2 (by rfl) ⟨3612498, by rfl⟩ : syracuseStep 9633329 = 7224997) B7224997
theorem B6422219 : Blo 1901435 6422219 := bstep (se 1 (by rfl) ⟨4816664, by rfl⟩ : syracuseStep 6422219 = 9633329) B9633329
theorem B4281479 : Blo 1901435 4281479 := bstep (se 1 (by rfl) ⟨3211109, by rfl⟩ : syracuseStep 4281479 = 6422219) B6422219
theorem B2854319 : Blo 1901435 2854319 := bstep (se 1 (by rfl) ⟨2140739, by rfl⟩ : syracuseStep 2854319 = 4281479) B4281479
theorem B1902879 : Blo 1901435 1902879 := bstep (se 1 (by rfl) ⟨1427159, by rfl⟩ : syracuseStep 1902879 = 2854319) B2854319
theorem B2854325 : Blo 1901435 2854325 := bbase (se 5 (by rfl) ⟨133796, by rfl⟩ : syracuseStep 2854325 = 267593) (by norm_num)
theorem B1902883 : Blo 1901435 1902883 := bstep (se 1 (by rfl) ⟨1427162, by rfl⟩ : syracuseStep 1902883 = 2854325) B2854325
theorem B4816685 : Blo 1901435 4816685 := bbase (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) (by norm_num)
theorem B3211123 : Blo 1901435 3211123 := bstep (se 1 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 3211123 = 4816685) B4816685
theorem B4281497 : Blo 1901435 4281497 := bstep (se 2 (by rfl) ⟨1605561, by rfl⟩ : syracuseStep 4281497 = 3211123) B3211123
theorem B2854331 : Blo 1901435 2854331 := bstep (se 1 (by rfl) ⟨2140748, by rfl⟩ : syracuseStep 2854331 = 4281497) B4281497
theorem B1902887 : Blo 1901435 1902887 := bstep (se 1 (by rfl) ⟨1427165, by rfl⟩ : syracuseStep 1902887 = 2854331) B2854331
theorem B2140753 : Blo 1901435 2140753 := bbase (se 2 (by rfl) ⟨802782, by rfl⟩ : syracuseStep 2140753 = 1605565) (by norm_num)
theorem B2854337 : Blo 1901435 2854337 := bstep (se 2 (by rfl) ⟨1070376, by rfl⟩ : syracuseStep 2854337 = 2140753) B2140753
theorem B1902891 : Blo 1901435 1902891 := bstep (se 1 (by rfl) ⟨1427168, by rfl⟩ : syracuseStep 1902891 = 2854337) B2854337
theorem B2709397 : Blo 1901435 2709397 := bbase (se 6 (by rfl) ⟨63501, by rfl⟩ : syracuseStep 2709397 = 127003) (by norm_num)
theorem B3612529 : Blo 1901435 3612529 := bstep (se 2 (by rfl) ⟨1354698, by rfl⟩ : syracuseStep 3612529 = 2709397) B2709397
theorem B4816705 : Blo 1901435 4816705 := bstep (se 2 (by rfl) ⟨1806264, by rfl⟩ : syracuseStep 4816705 = 3612529) B3612529
theorem B6422273 : Blo 1901435 6422273 := bstep (se 2 (by rfl) ⟨2408352, by rfl⟩ : syracuseStep 6422273 = 4816705) B4816705
theorem B4281515 : Blo 1901435 4281515 := bstep (se 1 (by rfl) ⟨3211136, by rfl⟩ : syracuseStep 4281515 = 6422273) B6422273
theorem B2854343 : Blo 1901435 2854343 := bstep (se 1 (by rfl) ⟨2140757, by rfl⟩ : syracuseStep 2854343 = 4281515) B4281515
theorem B1902895 : Blo 1901435 1902895 := bstep (se 1 (by rfl) ⟨1427171, by rfl⟩ : syracuseStep 1902895 = 2854343) B2854343
theorem B2854349 : Blo 1901435 2854349 := bbase (se 3 (by rfl) ⟨535190, by rfl⟩ : syracuseStep 2854349 = 1070381) (by norm_num)
theorem B1902899 : Blo 1901435 1902899 := bstep (se 1 (by rfl) ⟨1427174, by rfl⟩ : syracuseStep 1902899 = 2854349) B2854349
theorem B4281533 : Blo 1901435 4281533 := bbase (se 3 (by rfl) ⟨802787, by rfl⟩ : syracuseStep 4281533 = 1605575) (by norm_num)
theorem B2854355 : Blo 1901435 2854355 := bstep (se 1 (by rfl) ⟨2140766, by rfl⟩ : syracuseStep 2854355 = 4281533) B4281533
theorem B1902903 : Blo 1901435 1902903 := bstep (se 1 (by rfl) ⟨1427177, by rfl⟩ : syracuseStep 1902903 = 2854355) B2854355
theorem B3211157 : Blo 1901435 3211157 := bbase (se 6 (by rfl) ⟨75261, by rfl⟩ : syracuseStep 3211157 = 150523) (by norm_num)
theorem B2140771 : Blo 1901435 2140771 := bstep (se 1 (by rfl) ⟨1605578, by rfl⟩ : syracuseStep 2140771 = 3211157) B3211157
theorem B2854361 : Blo 1901435 2854361 := bstep (se 2 (by rfl) ⟨1070385, by rfl⟩ : syracuseStep 2854361 = 2140771) B2140771
theorem B1902907 : Blo 1901435 1902907 := bstep (se 1 (by rfl) ⟨1427180, by rfl⟩ : syracuseStep 1902907 = 2854361) B2854361
theorem B2286073 : Blo 1901435 2286073 := bbase (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) (by norm_num)
theorem B12192389 : Blo 1901435 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B8128259 : Blo 1901435 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B5418839 : Blo 1901435 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B14450237 : Blo 1901435 14450237 := bstep (se 3 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 14450237 = 5418839) B5418839
theorem B9633491 : Blo 1901435 9633491 := bstep (se 1 (by rfl) ⟨7225118, by rfl⟩ : syracuseStep 9633491 = 14450237) B14450237
theorem B6422327 : Blo 1901435 6422327 := bstep (se 1 (by rfl) ⟨4816745, by rfl⟩ : syracuseStep 6422327 = 9633491) B9633491
theorem B4281551 : Blo 1901435 4281551 := bstep (se 1 (by rfl) ⟨3211163, by rfl⟩ : syracuseStep 4281551 = 6422327) B6422327
theorem B2854367 : Blo 1901435 2854367 := bstep (se 1 (by rfl) ⟨2140775, by rfl⟩ : syracuseStep 2854367 = 4281551) B4281551
theorem B1902911 : Blo 1901435 1902911 := bstep (se 1 (by rfl) ⟨1427183, by rfl⟩ : syracuseStep 1902911 = 2854367) B2854367
theorem B2854373 : Blo 1901435 2854373 := bbase (se 4 (by rfl) ⟨267597, by rfl⟩ : syracuseStep 2854373 = 535195) (by norm_num)
theorem B1902915 : Blo 1901435 1902915 := bstep (se 1 (by rfl) ⟨1427186, by rfl⟩ : syracuseStep 1902915 = 2854373) B2854373
theorem B8679973 : Blo 1901435 8679973 := bbase (se 4 (by rfl) ⟨813747, by rfl⟩ : syracuseStep 8679973 = 1627495) (by norm_num)
theorem B11573297 : Blo 1901435 11573297 := bstep (se 2 (by rfl) ⟨4339986, by rfl⟩ : syracuseStep 11573297 = 8679973) B8679973
theorem B7715531 : Blo 1901435 7715531 := bstep (se 1 (by rfl) ⟨5786648, by rfl⟩ : syracuseStep 7715531 = 11573297) B11573297
theorem B20574749 : Blo 1901435 20574749 := bstep (se 3 (by rfl) ⟨3857765, by rfl⟩ : syracuseStep 20574749 = 7715531) B7715531
theorem B13716499 : Blo 1901435 13716499 := bstep (se 1 (by rfl) ⟨10287374, by rfl⟩ : syracuseStep 13716499 = 20574749) B20574749
theorem B18288665 : Blo 1901435 18288665 := bstep (se 2 (by rfl) ⟨6858249, by rfl⟩ : syracuseStep 18288665 = 13716499) B13716499
theorem B12192443 : Blo 1901435 12192443 := bstep (se 1 (by rfl) ⟨9144332, by rfl⟩ : syracuseStep 12192443 = 18288665) B18288665
theorem B8128295 : Blo 1901435 8128295 := bstep (se 1 (by rfl) ⟨6096221, by rfl⟩ : syracuseStep 8128295 = 12192443) B12192443
theorem B5418863 : Blo 1901435 5418863 := bstep (se 1 (by rfl) ⟨4064147, by rfl⟩ : syracuseStep 5418863 = 8128295) B8128295
theorem B3612575 : Blo 1901435 3612575 := bstep (se 1 (by rfl) ⟨2709431, by rfl⟩ : syracuseStep 3612575 = 5418863) B5418863
theorem B2408383 : Blo 1901435 2408383 := bstep (se 1 (by rfl) ⟨1806287, by rfl⟩ : syracuseStep 2408383 = 3612575) B3612575
theorem B3211177 : Blo 1901435 3211177 := bstep (se 2 (by rfl) ⟨1204191, by rfl⟩ : syracuseStep 3211177 = 2408383) B2408383
theorem B4281569 : Blo 1901435 4281569 := bstep (se 2 (by rfl) ⟨1605588, by rfl⟩ : syracuseStep 4281569 = 3211177) B3211177
theorem B2854379 : Blo 1901435 2854379 := bstep (se 1 (by rfl) ⟨2140784, by rfl⟩ : syracuseStep 2854379 = 4281569) B4281569
theorem B1902919 : Blo 1901435 1902919 := bstep (se 1 (by rfl) ⟨1427189, by rfl⟩ : syracuseStep 1902919 = 2854379) B2854379
theorem B2140789 : Blo 1901435 2140789 := bbase (se 5 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 2140789 = 200699) (by norm_num)
theorem B2854385 : Blo 1901435 2854385 := bstep (se 2 (by rfl) ⟨1070394, by rfl⟩ : syracuseStep 2854385 = 2140789) B2140789
theorem B1902923 : Blo 1901435 1902923 := bstep (se 1 (by rfl) ⟨1427192, by rfl⟩ : syracuseStep 1902923 = 2854385) B2854385
theorem B2408393 : Blo 1901435 2408393 := bbase (se 2 (by rfl) ⟨903147, by rfl⟩ : syracuseStep 2408393 = 1806295) (by norm_num)
theorem B6422381 : Blo 1901435 6422381 := bstep (se 3 (by rfl) ⟨1204196, by rfl⟩ : syracuseStep 6422381 = 2408393) B2408393
theorem B4281587 : Blo 1901435 4281587 := bstep (se 1 (by rfl) ⟨3211190, by rfl⟩ : syracuseStep 4281587 = 6422381) B6422381
theorem B2854391 : Blo 1901435 2854391 := bstep (se 1 (by rfl) ⟨2140793, by rfl⟩ : syracuseStep 2854391 = 4281587) B4281587
theorem B1902927 : Blo 1901435 1902927 := bstep (se 1 (by rfl) ⟨1427195, by rfl⟩ : syracuseStep 1902927 = 2854391) B2854391
theorem B2854397 : Blo 1901435 2854397 := bbase (se 3 (by rfl) ⟨535199, by rfl⟩ : syracuseStep 2854397 = 1070399) (by norm_num)
theorem B1902931 : Blo 1901435 1902931 := bstep (se 1 (by rfl) ⟨1427198, by rfl⟩ : syracuseStep 1902931 = 2854397) B2854397
theorem B4281605 : Blo 1901435 4281605 := bbase (se 4 (by rfl) ⟨401400, by rfl⟩ : syracuseStep 4281605 = 802801) (by norm_num)
theorem B2854403 : Blo 1901435 2854403 := bstep (se 1 (by rfl) ⟨2140802, by rfl⟩ : syracuseStep 2854403 = 4281605) B4281605
theorem B1902935 : Blo 1901435 1902935 := bstep (se 1 (by rfl) ⟨1427201, by rfl⟩ : syracuseStep 1902935 = 2854403) B2854403
theorem B3612613 : Blo 1901435 3612613 := bbase (se 4 (by rfl) ⟨338682, by rfl⟩ : syracuseStep 3612613 = 677365) (by norm_num)
theorem B4816817 : Blo 1901435 4816817 := bstep (se 2 (by rfl) ⟨1806306, by rfl⟩ : syracuseStep 4816817 = 3612613) B3612613
theorem B3211211 : Blo 1901435 3211211 := bstep (se 1 (by rfl) ⟨2408408, by rfl⟩ : syracuseStep 3211211 = 4816817) B4816817
theorem B2140807 : Blo 1901435 2140807 := bstep (se 1 (by rfl) ⟨1605605, by rfl⟩ : syracuseStep 2140807 = 3211211) B3211211
theorem B2854409 : Blo 1901435 2854409 := bstep (se 2 (by rfl) ⟨1070403, by rfl⟩ : syracuseStep 2854409 = 2140807) B2140807
theorem B1902939 : Blo 1901435 1902939 := bstep (se 1 (by rfl) ⟨1427204, by rfl⟩ : syracuseStep 1902939 = 2854409) B2854409
theorem B9633653 : Blo 1901435 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B6422435 : Blo 1901435 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B4281623 : Blo 1901435 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B2854415 : Blo 1901435 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B1902943 : Blo 1901435 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B2854421 : Blo 1901435 2854421 := bbase (se 6 (by rfl) ⟨66900, by rfl⟩ : syracuseStep 2854421 = 133801) (by norm_num)
theorem B1902947 : Blo 1901435 1902947 := bstep (se 1 (by rfl) ⟨1427210, by rfl⟩ : syracuseStep 1902947 = 2854421) B2854421
theorem B9144485 : Blo 1901435 9144485 := bbase (se 4 (by rfl) ⟨857295, by rfl⟩ : syracuseStep 9144485 = 1714591) (by norm_num)
theorem B6096323 : Blo 1901435 6096323 := bstep (se 1 (by rfl) ⟨4572242, by rfl⟩ : syracuseStep 6096323 = 9144485) B9144485
theorem B16256861 : Blo 1901435 16256861 := bstep (se 3 (by rfl) ⟨3048161, by rfl⟩ : syracuseStep 16256861 = 6096323) B6096323
theorem B10837907 : Blo 1901435 10837907 := bstep (se 1 (by rfl) ⟨8128430, by rfl⟩ : syracuseStep 10837907 = 16256861) B16256861
theorem B7225271 : Blo 1901435 7225271 := bstep (se 1 (by rfl) ⟨5418953, by rfl⟩ : syracuseStep 7225271 = 10837907) B10837907
theorem B4816847 : Blo 1901435 4816847 := bstep (se 1 (by rfl) ⟨3612635, by rfl⟩ : syracuseStep 4816847 = 7225271) B7225271
theorem B3211231 : Blo 1901435 3211231 := bstep (se 1 (by rfl) ⟨2408423, by rfl⟩ : syracuseStep 3211231 = 4816847) B4816847
theorem B4281641 : Blo 1901435 4281641 := bstep (se 2 (by rfl) ⟨1605615, by rfl⟩ : syracuseStep 4281641 = 3211231) B3211231
theorem B2854427 : Blo 1901435 2854427 := bstep (se 1 (by rfl) ⟨2140820, by rfl⟩ : syracuseStep 2854427 = 4281641) B4281641
theorem B1902951 : Blo 1901435 1902951 := bstep (se 1 (by rfl) ⟨1427213, by rfl⟩ : syracuseStep 1902951 = 2854427) B2854427
theorem B2140825 : Blo 1901435 2140825 := bbase (se 2 (by rfl) ⟨802809, by rfl⟩ : syracuseStep 2140825 = 1605619) (by norm_num)
theorem B2854433 : Blo 1901435 2854433 := bstep (se 2 (by rfl) ⟨1070412, by rfl⟩ : syracuseStep 2854433 = 2140825) B2140825
theorem B1902955 : Blo 1901435 1902955 := bstep (se 1 (by rfl) ⟨1427216, by rfl⟩ : syracuseStep 1902955 = 2854433) B2854433
theorem B7225301 : Blo 1901435 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B4816867 : Blo 1901435 4816867 := bstep (se 1 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 4816867 = 7225301) B7225301
theorem B6422489 : Blo 1901435 6422489 := bstep (se 2 (by rfl) ⟨2408433, by rfl⟩ : syracuseStep 6422489 = 4816867) B4816867
theorem B4281659 : Blo 1901435 4281659 := bstep (se 1 (by rfl) ⟨3211244, by rfl⟩ : syracuseStep 4281659 = 6422489) B6422489
theorem B2854439 : Blo 1901435 2854439 := bstep (se 1 (by rfl) ⟨2140829, by rfl⟩ : syracuseStep 2854439 = 4281659) B4281659
theorem B1902959 : Blo 1901435 1902959 := bstep (se 1 (by rfl) ⟨1427219, by rfl⟩ : syracuseStep 1902959 = 2854439) B2854439
theorem B2854445 : Blo 1901435 2854445 := bbase (se 3 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 2854445 = 1070417) (by norm_num)
theorem B1902963 : Blo 1901435 1902963 := bstep (se 1 (by rfl) ⟨1427222, by rfl⟩ : syracuseStep 1902963 = 2854445) B2854445
theorem B4281677 : Blo 1901435 4281677 := bbase (se 3 (by rfl) ⟨802814, by rfl⟩ : syracuseStep 4281677 = 1605629) (by norm_num)
theorem B2854451 : Blo 1901435 2854451 := bstep (se 1 (by rfl) ⟨2140838, by rfl⟩ : syracuseStep 2854451 = 4281677) B4281677
theorem B1902967 : Blo 1901435 1902967 := bstep (se 1 (by rfl) ⟨1427225, by rfl⟩ : syracuseStep 1902967 = 2854451) B2854451
theorem B2408449 : Blo 1901435 2408449 := bbase (se 2 (by rfl) ⟨903168, by rfl⟩ : syracuseStep 2408449 = 1806337) (by norm_num)
theorem B3211265 : Blo 1901435 3211265 := bstep (se 2 (by rfl) ⟨1204224, by rfl⟩ : syracuseStep 3211265 = 2408449) B2408449
theorem B2140843 : Blo 1901435 2140843 := bstep (se 1 (by rfl) ⟨1605632, by rfl⟩ : syracuseStep 2140843 = 3211265) B3211265
theorem B2854457 : Blo 1901435 2854457 := bstep (se 2 (by rfl) ⟨1070421, by rfl⟩ : syracuseStep 2854457 = 2140843) B2140843
theorem B1902971 : Blo 1901435 1902971 := bstep (se 1 (by rfl) ⟨1427228, by rfl⟩ : syracuseStep 1902971 = 2854457) B2854457
theorem B2032133 : Blo 1901435 2032133 := bbase (se 4 (by rfl) ⟨190512, by rfl⟩ : syracuseStep 2032133 = 381025) (by norm_num)
theorem B21676085 : Blo 1901435 21676085 := bstep (se 5 (by rfl) ⟨1016066, by rfl⟩ : syracuseStep 21676085 = 2032133) B2032133
theorem B14450723 : Blo 1901435 14450723 := bstep (se 1 (by rfl) ⟨10838042, by rfl⟩ : syracuseStep 14450723 = 21676085) B21676085
theorem B9633815 : Blo 1901435 9633815 := bstep (se 1 (by rfl) ⟨7225361, by rfl⟩ : syracuseStep 9633815 = 14450723) B14450723
theorem B6422543 : Blo 1901435 6422543 := bstep (se 1 (by rfl) ⟨4816907, by rfl⟩ : syracuseStep 6422543 = 9633815) B9633815
theorem B4281695 : Blo 1901435 4281695 := bstep (se 1 (by rfl) ⟨3211271, by rfl⟩ : syracuseStep 4281695 = 6422543) B6422543
theorem B2854463 : Blo 1901435 2854463 := bstep (se 1 (by rfl) ⟨2140847, by rfl⟩ : syracuseStep 2854463 = 4281695) B4281695
theorem B1902975 : Blo 1901435 1902975 := bstep (se 1 (by rfl) ⟨1427231, by rfl⟩ : syracuseStep 1902975 = 2854463) B2854463
theorem B2854469 : Blo 1901435 2854469 := bbase (se 4 (by rfl) ⟨267606, by rfl⟩ : syracuseStep 2854469 = 535213) (by norm_num)
theorem B1902979 : Blo 1901435 1902979 := bstep (se 1 (by rfl) ⟨1427234, by rfl⟩ : syracuseStep 1902979 = 2854469) B2854469
theorem B3211285 : Blo 1901435 3211285 := bbase (se 6 (by rfl) ⟨75264, by rfl⟩ : syracuseStep 3211285 = 150529) (by norm_num)
theorem B4281713 : Blo 1901435 4281713 := bstep (se 2 (by rfl) ⟨1605642, by rfl⟩ : syracuseStep 4281713 = 3211285) B3211285
theorem B2854475 : Blo 1901435 2854475 := bstep (se 1 (by rfl) ⟨2140856, by rfl⟩ : syracuseStep 2854475 = 4281713) B4281713
theorem B1902983 : Blo 1901435 1902983 := bstep (se 1 (by rfl) ⟨1427237, by rfl⟩ : syracuseStep 1902983 = 2854475) B2854475
theorem B2140861 : Blo 1901435 2140861 := bbase (se 3 (by rfl) ⟨401411, by rfl⟩ : syracuseStep 2140861 = 802823) (by norm_num)
theorem B2854481 : Blo 1901435 2854481 := bstep (se 2 (by rfl) ⟨1070430, by rfl⟩ : syracuseStep 2854481 = 2140861) B2140861
theorem B1902987 : Blo 1901435 1902987 := bstep (se 1 (by rfl) ⟨1427240, by rfl⟩ : syracuseStep 1902987 = 2854481) B2854481
theorem B6422597 : Blo 1901435 6422597 := bbase (se 4 (by rfl) ⟨602118, by rfl⟩ : syracuseStep 6422597 = 1204237) (by norm_num)
theorem B4281731 : Blo 1901435 4281731 := bstep (se 1 (by rfl) ⟨3211298, by rfl⟩ : syracuseStep 4281731 = 6422597) B6422597
theorem B2854487 : Blo 1901435 2854487 := bstep (se 1 (by rfl) ⟨2140865, by rfl⟩ : syracuseStep 2854487 = 4281731) B4281731
theorem B1902991 : Blo 1901435 1902991 := bstep (se 1 (by rfl) ⟨1427243, by rfl⟩ : syracuseStep 1902991 = 2854487) B2854487
theorem B2854493 : Blo 1901435 2854493 := bbase (se 3 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 2854493 = 1070435) (by norm_num)
theorem B1902995 : Blo 1901435 1902995 := bstep (se 1 (by rfl) ⟨1427246, by rfl⟩ : syracuseStep 1902995 = 2854493) B2854493
theorem B4281749 : Blo 1901435 4281749 := bbase (se 6 (by rfl) ⟨100353, by rfl⟩ : syracuseStep 4281749 = 200707) (by norm_num)
theorem B2854499 : Blo 1901435 2854499 := bstep (se 1 (by rfl) ⟨2140874, by rfl⟩ : syracuseStep 2854499 = 4281749) B4281749
theorem B1902999 : Blo 1901435 1902999 := bstep (se 1 (by rfl) ⟨1427249, by rfl⟩ : syracuseStep 1902999 = 2854499) B2854499
theorem B4119781 : Blo 1901435 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B5493041 : Blo 1901435 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B3662027 : Blo 1901435 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B2441351 : Blo 1901435 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B6510269 : Blo 1901435 6510269 := bstep (se 3 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 6510269 = 2441351) B2441351
theorem B4340179 : Blo 1901435 4340179 := bstep (se 1 (by rfl) ⟨3255134, by rfl⟩ : syracuseStep 4340179 = 6510269) B6510269
theorem B5786905 : Blo 1901435 5786905 := bstep (se 2 (by rfl) ⟨2170089, by rfl⟩ : syracuseStep 5786905 = 4340179) B4340179
theorem B7715873 : Blo 1901435 7715873 := bstep (se 2 (by rfl) ⟨2893452, by rfl⟩ : syracuseStep 7715873 = 5786905) B5786905
theorem B5143915 : Blo 1901435 5143915 := bstep (se 1 (by rfl) ⟨3857936, by rfl⟩ : syracuseStep 5143915 = 7715873) B7715873
theorem B6858553 : Blo 1901435 6858553 := bstep (se 2 (by rfl) ⟨2571957, by rfl⟩ : syracuseStep 6858553 = 5143915) B5143915
theorem B9144737 : Blo 1901435 9144737 := bstep (se 2 (by rfl) ⟨3429276, by rfl⟩ : syracuseStep 9144737 = 6858553) B6858553
theorem B6096491 : Blo 1901435 6096491 := bstep (se 1 (by rfl) ⟨4572368, by rfl⟩ : syracuseStep 6096491 = 9144737) B9144737
theorem B4064327 : Blo 1901435 4064327 := bstep (se 1 (by rfl) ⟨3048245, by rfl⟩ : syracuseStep 4064327 = 6096491) B6096491
theorem B2709551 : Blo 1901435 2709551 := bstep (se 1 (by rfl) ⟨2032163, by rfl⟩ : syracuseStep 2709551 = 4064327) B4064327
theorem B7225469 : Blo 1901435 7225469 := bstep (se 3 (by rfl) ⟨1354775, by rfl⟩ : syracuseStep 7225469 = 2709551) B2709551
theorem B4816979 : Blo 1901435 4816979 := bstep (se 1 (by rfl) ⟨3612734, by rfl⟩ : syracuseStep 4816979 = 7225469) B7225469
theorem B3211319 : Blo 1901435 3211319 := bstep (se 1 (by rfl) ⟨2408489, by rfl⟩ : syracuseStep 3211319 = 4816979) B4816979
theorem B2140879 : Blo 1901435 2140879 := bstep (se 1 (by rfl) ⟨1605659, by rfl⟩ : syracuseStep 2140879 = 3211319) B3211319
theorem B2854505 : Blo 1901435 2854505 := bstep (se 2 (by rfl) ⟨1070439, by rfl⟩ : syracuseStep 2854505 = 2140879) B2140879
theorem B1903003 : Blo 1901435 1903003 := bstep (se 1 (by rfl) ⟨1427252, by rfl⟩ : syracuseStep 1903003 = 2854505) B2854505
theorem B5143925 : Blo 1901435 5143925 := bbase (se 5 (by rfl) ⟨241121, by rfl⟩ : syracuseStep 5143925 = 482243) (by norm_num)
theorem B3429283 : Blo 1901435 3429283 := bstep (se 1 (by rfl) ⟨2571962, by rfl⟩ : syracuseStep 3429283 = 5143925) B5143925
theorem B4572377 : Blo 1901435 4572377 := bstep (se 2 (by rfl) ⟨1714641, by rfl⟩ : syracuseStep 4572377 = 3429283) B3429283
theorem B3048251 : Blo 1901435 3048251 := bstep (se 1 (by rfl) ⟨2286188, by rfl⟩ : syracuseStep 3048251 = 4572377) B4572377
theorem B8128669 : Blo 1901435 8128669 := bstep (se 3 (by rfl) ⟨1524125, by rfl⟩ : syracuseStep 8128669 = 3048251) B3048251
theorem B10838225 : Blo 1901435 10838225 := bstep (se 2 (by rfl) ⟨4064334, by rfl⟩ : syracuseStep 10838225 = 8128669) B8128669
theorem B7225483 : Blo 1901435 7225483 := bstep (se 1 (by rfl) ⟨5419112, by rfl⟩ : syracuseStep 7225483 = 10838225) B10838225
theorem B9633977 : Blo 1901435 9633977 := bstep (se 2 (by rfl) ⟨3612741, by rfl⟩ : syracuseStep 9633977 = 7225483) B7225483
theorem B6422651 : Blo 1901435 6422651 := bstep (se 1 (by rfl) ⟨4816988, by rfl⟩ : syracuseStep 6422651 = 9633977) B9633977
theorem B4281767 : Blo 1901435 4281767 := bstep (se 1 (by rfl) ⟨3211325, by rfl⟩ : syracuseStep 4281767 = 6422651) B6422651
theorem B2854511 : Blo 1901435 2854511 := bstep (se 1 (by rfl) ⟨2140883, by rfl⟩ : syracuseStep 2854511 = 4281767) B4281767
theorem B1903007 : Blo 1901435 1903007 := bstep (se 1 (by rfl) ⟨1427255, by rfl⟩ : syracuseStep 1903007 = 2854511) B2854511
theorem B2854517 : Blo 1901435 2854517 := bbase (se 5 (by rfl) ⟨133805, by rfl⟩ : syracuseStep 2854517 = 267611) (by norm_num)
theorem B1903011 : Blo 1901435 1903011 := bstep (se 1 (by rfl) ⟨1427258, by rfl⟩ : syracuseStep 1903011 = 2854517) B2854517
theorem B3612757 : Blo 1901435 3612757 := bbase (se 8 (by rfl) ⟨21168, by rfl⟩ : syracuseStep 3612757 = 42337) (by norm_num)
theorem B4817009 : Blo 1901435 4817009 := bstep (se 2 (by rfl) ⟨1806378, by rfl⟩ : syracuseStep 4817009 = 3612757) B3612757
theorem B3211339 : Blo 1901435 3211339 := bstep (se 1 (by rfl) ⟨2408504, by rfl⟩ : syracuseStep 3211339 = 4817009) B4817009
theorem B4281785 : Blo 1901435 4281785 := bstep (se 2 (by rfl) ⟨1605669, by rfl⟩ : syracuseStep 4281785 = 3211339) B3211339
theorem B2854523 : Blo 1901435 2854523 := bstep (se 1 (by rfl) ⟨2140892, by rfl⟩ : syracuseStep 2854523 = 4281785) B4281785
theorem B1903015 : Blo 1901435 1903015 := bstep (se 1 (by rfl) ⟨1427261, by rfl⟩ : syracuseStep 1903015 = 2854523) B2854523
theorem B2140897 : Blo 1901435 2140897 := bbase (se 2 (by rfl) ⟨802836, by rfl⟩ : syracuseStep 2140897 = 1605673) (by norm_num)
theorem B2854529 : Blo 1901435 2854529 := bstep (se 2 (by rfl) ⟨1070448, by rfl⟩ : syracuseStep 2854529 = 2140897) B2140897
theorem B1903019 : Blo 1901435 1903019 := bstep (se 1 (by rfl) ⟨1427264, by rfl⟩ : syracuseStep 1903019 = 2854529) B2854529
theorem B4817029 : Blo 1901435 4817029 := bbase (se 4 (by rfl) ⟨451596, by rfl⟩ : syracuseStep 4817029 = 903193) (by norm_num)
theorem B6422705 : Blo 1901435 6422705 := bstep (se 2 (by rfl) ⟨2408514, by rfl⟩ : syracuseStep 6422705 = 4817029) B4817029
theorem B4281803 : Blo 1901435 4281803 := bstep (se 1 (by rfl) ⟨3211352, by rfl⟩ : syracuseStep 4281803 = 6422705) B6422705
theorem B2854535 : Blo 1901435 2854535 := bstep (se 1 (by rfl) ⟨2140901, by rfl⟩ : syracuseStep 2854535 = 4281803) B4281803
theorem B1903023 : Blo 1901435 1903023 := bstep (se 1 (by rfl) ⟨1427267, by rfl⟩ : syracuseStep 1903023 = 2854535) B2854535
theorem B2854541 : Blo 1901435 2854541 := bbase (se 3 (by rfl) ⟨535226, by rfl⟩ : syracuseStep 2854541 = 1070453) (by norm_num)
theorem B1903027 : Blo 1901435 1903027 := bstep (se 1 (by rfl) ⟨1427270, by rfl⟩ : syracuseStep 1903027 = 2854541) B2854541
theorem B4281821 : Blo 1901435 4281821 := bbase (se 3 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 4281821 = 1605683) (by norm_num)
theorem B2854547 : Blo 1901435 2854547 := bstep (se 1 (by rfl) ⟨2140910, by rfl⟩ : syracuseStep 2854547 = 4281821) B4281821
theorem B1903031 : Blo 1901435 1903031 := bstep (se 1 (by rfl) ⟨1427273, by rfl⟩ : syracuseStep 1903031 = 2854547) B2854547
theorem B3211373 : Blo 1901435 3211373 := bbase (se 3 (by rfl) ⟨602132, by rfl⟩ : syracuseStep 3211373 = 1204265) (by norm_num)
theorem B2140915 : Blo 1901435 2140915 := bstep (se 1 (by rfl) ⟨1605686, by rfl⟩ : syracuseStep 2140915 = 3211373) B3211373
theorem B2854553 : Blo 1901435 2854553 := bstep (se 2 (by rfl) ⟨1070457, by rfl⟩ : syracuseStep 2854553 = 2140915) B2140915
theorem B1903035 : Blo 1901435 1903035 := bstep (se 1 (by rfl) ⟨1427276, by rfl⟩ : syracuseStep 1903035 = 2854553) B2854553
theorem B18289813 : Blo 1901435 18289813 := bbase (se 6 (by rfl) ⟨428667, by rfl⟩ : syracuseStep 18289813 = 857335) (by norm_num)
theorem B24386417 : Blo 1901435 24386417 := bstep (se 2 (by rfl) ⟨9144906, by rfl⟩ : syracuseStep 24386417 = 18289813) B18289813
theorem B16257611 : Blo 1901435 16257611 := bstep (se 1 (by rfl) ⟨12193208, by rfl⟩ : syracuseStep 16257611 = 24386417) B24386417
theorem B10838407 : Blo 1901435 10838407 := bstep (se 1 (by rfl) ⟨8128805, by rfl⟩ : syracuseStep 10838407 = 16257611) B16257611
theorem B14451209 : Blo 1901435 14451209 := bstep (se 2 (by rfl) ⟨5419203, by rfl⟩ : syracuseStep 14451209 = 10838407) B10838407
theorem B9634139 : Blo 1901435 9634139 := bstep (se 1 (by rfl) ⟨7225604, by rfl⟩ : syracuseStep 9634139 = 14451209) B14451209
theorem B6422759 : Blo 1901435 6422759 := bstep (se 1 (by rfl) ⟨4817069, by rfl⟩ : syracuseStep 6422759 = 9634139) B9634139
theorem B4281839 : Blo 1901435 4281839 := bstep (se 1 (by rfl) ⟨3211379, by rfl⟩ : syracuseStep 4281839 = 6422759) B6422759
theorem B2854559 : Blo 1901435 2854559 := bstep (se 1 (by rfl) ⟨2140919, by rfl⟩ : syracuseStep 2854559 = 4281839) B4281839
theorem B1903039 : Blo 1901435 1903039 := bstep (se 1 (by rfl) ⟨1427279, by rfl⟩ : syracuseStep 1903039 = 2854559) B2854559
theorem B2854565 : Blo 1901435 2854565 := bbase (se 4 (by rfl) ⟨267615, by rfl⟩ : syracuseStep 2854565 = 535231) (by norm_num)
theorem B1903043 : Blo 1901435 1903043 := bstep (se 1 (by rfl) ⟨1427282, by rfl⟩ : syracuseStep 1903043 = 2854565) B2854565
theorem B2408545 : Blo 1901435 2408545 := bbase (se 2 (by rfl) ⟨903204, by rfl⟩ : syracuseStep 2408545 = 1806409) (by norm_num)
theorem B3211393 : Blo 1901435 3211393 := bstep (se 2 (by rfl) ⟨1204272, by rfl⟩ : syracuseStep 3211393 = 2408545) B2408545
theorem B4281857 : Blo 1901435 4281857 := bstep (se 2 (by rfl) ⟨1605696, by rfl⟩ : syracuseStep 4281857 = 3211393) B3211393
theorem B2854571 : Blo 1901435 2854571 := bstep (se 1 (by rfl) ⟨2140928, by rfl⟩ : syracuseStep 2854571 = 4281857) B4281857
theorem B1903047 : Blo 1901435 1903047 := bstep (se 1 (by rfl) ⟨1427285, by rfl⟩ : syracuseStep 1903047 = 2854571) B2854571
theorem B2140933 : Blo 1901435 2140933 := bbase (se 4 (by rfl) ⟨200712, by rfl⟩ : syracuseStep 2140933 = 401425) (by norm_num)
theorem B2854577 : Blo 1901435 2854577 := bstep (se 2 (by rfl) ⟨1070466, by rfl⟩ : syracuseStep 2854577 = 2140933) B2140933
theorem B1903051 : Blo 1901435 1903051 := bstep (se 1 (by rfl) ⟨1427288, by rfl⟩ : syracuseStep 1903051 = 2854577) B2854577
theorem B4882837 : Blo 1901435 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B6510449 : Blo 1901435 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B4340299 : Blo 1901435 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B5787065 : Blo 1901435 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B3858043 : Blo 1901435 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B5144057 : Blo 1901435 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B3429371 : Blo 1901435 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2286247 : Blo 1901435 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B3048329 : Blo 1901435 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2032219 : Blo 1901435 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B2709625 : Blo 1901435 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B3612833 : Blo 1901435 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B2408555 : Blo 1901435 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B6422813 : Blo 1901435 6422813 := bstep (se 3 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 6422813 = 2408555) B2408555
theorem B4281875 : Blo 1901435 4281875 := bstep (se 1 (by rfl) ⟨3211406, by rfl⟩ : syracuseStep 4281875 = 6422813) B6422813
theorem B2854583 : Blo 1901435 2854583 := bstep (se 1 (by rfl) ⟨2140937, by rfl⟩ : syracuseStep 2854583 = 4281875) B4281875
theorem B1903055 : Blo 1901435 1903055 := bstep (se 1 (by rfl) ⟨1427291, by rfl⟩ : syracuseStep 1903055 = 2854583) B2854583
theorem B2854589 : Blo 1901435 2854589 := bbase (se 3 (by rfl) ⟨535235, by rfl⟩ : syracuseStep 2854589 = 1070471) (by norm_num)
theorem B1903059 : Blo 1901435 1903059 := bstep (se 1 (by rfl) ⟨1427294, by rfl⟩ : syracuseStep 1903059 = 2854589) B2854589
theorem B4281893 : Blo 1901435 4281893 := bbase (se 4 (by rfl) ⟨401427, by rfl⟩ : syracuseStep 4281893 = 802855) (by norm_num)
theorem B2854595 : Blo 1901435 2854595 := bstep (se 1 (by rfl) ⟨2140946, by rfl⟩ : syracuseStep 2854595 = 4281893) B4281893
theorem B1903063 : Blo 1901435 1903063 := bstep (se 1 (by rfl) ⟨1427297, by rfl⟩ : syracuseStep 1903063 = 2854595) B2854595
theorem B4817141 : Blo 1901435 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B3211427 : Blo 1901435 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B2140951 : Blo 1901435 2140951 := bstep (se 1 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 2140951 = 3211427) B3211427
theorem B2854601 : Blo 1901435 2854601 := bstep (se 2 (by rfl) ⟨1070475, by rfl⟩ : syracuseStep 2854601 = 2140951) B2140951
theorem B1903067 : Blo 1901435 1903067 := bstep (se 1 (by rfl) ⟨1427300, by rfl⟩ : syracuseStep 1903067 = 2854601) B2854601
theorem B4340333 : Blo 1901435 4340333 := bbase (se 3 (by rfl) ⟨813812, by rfl⟩ : syracuseStep 4340333 = 1627625) (by norm_num)
theorem B2893555 : Blo 1901435 2893555 := bstep (se 1 (by rfl) ⟨2170166, by rfl⟩ : syracuseStep 2893555 = 4340333) B4340333
theorem B3858073 : Blo 1901435 3858073 := bstep (se 2 (by rfl) ⟨1446777, by rfl⟩ : syracuseStep 3858073 = 2893555) B2893555
theorem B20576389 : Blo 1901435 20576389 := bstep (se 4 (by rfl) ⟨1929036, by rfl⟩ : syracuseStep 20576389 = 3858073) B3858073
theorem B27435185 : Blo 1901435 27435185 := bstep (se 2 (by rfl) ⟨10288194, by rfl⟩ : syracuseStep 27435185 = 20576389) B20576389
theorem B18290123 : Blo 1901435 18290123 := bstep (se 1 (by rfl) ⟨13717592, by rfl⟩ : syracuseStep 18290123 = 27435185) B27435185
theorem B12193415 : Blo 1901435 12193415 := bstep (se 1 (by rfl) ⟨9145061, by rfl⟩ : syracuseStep 12193415 = 18290123) B18290123
theorem B8128943 : Blo 1901435 8128943 := bstep (se 1 (by rfl) ⟨6096707, by rfl⟩ : syracuseStep 8128943 = 12193415) B12193415
theorem B5419295 : Blo 1901435 5419295 := bstep (se 1 (by rfl) ⟨4064471, by rfl⟩ : syracuseStep 5419295 = 8128943) B8128943
theorem B3612863 : Blo 1901435 3612863 := bstep (se 1 (by rfl) ⟨2709647, by rfl⟩ : syracuseStep 3612863 = 5419295) B5419295
theorem B9634301 : Blo 1901435 9634301 := bstep (se 3 (by rfl) ⟨1806431, by rfl⟩ : syracuseStep 9634301 = 3612863) B3612863
theorem B6422867 : Blo 1901435 6422867 := bstep (se 1 (by rfl) ⟨4817150, by rfl⟩ : syracuseStep 6422867 = 9634301) B9634301
theorem B4281911 : Blo 1901435 4281911 := bstep (se 1 (by rfl) ⟨3211433, by rfl⟩ : syracuseStep 4281911 = 6422867) B6422867
theorem B2854607 : Blo 1901435 2854607 := bstep (se 1 (by rfl) ⟨2140955, by rfl⟩ : syracuseStep 2854607 = 4281911) B4281911
theorem B1903071 : Blo 1901435 1903071 := bstep (se 1 (by rfl) ⟨1427303, by rfl⟩ : syracuseStep 1903071 = 2854607) B2854607
theorem B2854613 : Blo 1901435 2854613 := bbase (se 7 (by rfl) ⟨33452, by rfl⟩ : syracuseStep 2854613 = 66905) (by norm_num)
theorem B1903075 : Blo 1901435 1903075 := bstep (se 1 (by rfl) ⟨1427306, by rfl⟩ : syracuseStep 1903075 = 2854613) B2854613
theorem B7716181 : Blo 1901435 7716181 := bbase (se 11 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 7716181 = 11303) (by norm_num)
theorem B10288241 : Blo 1901435 10288241 := bstep (se 2 (by rfl) ⟨3858090, by rfl⟩ : syracuseStep 10288241 = 7716181) B7716181
theorem B6858827 : Blo 1901435 6858827 := bstep (se 1 (by rfl) ⟨5144120, by rfl⟩ : syracuseStep 6858827 = 10288241) B10288241
theorem B4572551 : Blo 1901435 4572551 := bstep (se 1 (by rfl) ⟨3429413, by rfl⟩ : syracuseStep 4572551 = 6858827) B6858827
theorem B3048367 : Blo 1901435 3048367 := bstep (se 1 (by rfl) ⟨2286275, by rfl⟩ : syracuseStep 3048367 = 4572551) B4572551
theorem B4064489 : Blo 1901435 4064489 := bstep (se 2 (by rfl) ⟨1524183, by rfl⟩ : syracuseStep 4064489 = 3048367) B3048367
theorem B2709659 : Blo 1901435 2709659 := bstep (se 1 (by rfl) ⟨2032244, by rfl⟩ : syracuseStep 2709659 = 4064489) B4064489
theorem B7225757 : Blo 1901435 7225757 := bstep (se 3 (by rfl) ⟨1354829, by rfl⟩ : syracuseStep 7225757 = 2709659) B2709659
theorem B4817171 : Blo 1901435 4817171 := bstep (se 1 (by rfl) ⟨3612878, by rfl⟩ : syracuseStep 4817171 = 7225757) B7225757
theorem B3211447 : Blo 1901435 3211447 := bstep (se 1 (by rfl) ⟨2408585, by rfl⟩ : syracuseStep 3211447 = 4817171) B4817171
theorem B4281929 : Blo 1901435 4281929 := bstep (se 2 (by rfl) ⟨1605723, by rfl⟩ : syracuseStep 4281929 = 3211447) B3211447
theorem B2854619 : Blo 1901435 2854619 := bstep (se 1 (by rfl) ⟨2140964, by rfl⟩ : syracuseStep 2854619 = 4281929) B4281929
theorem B1903079 : Blo 1901435 1903079 := bstep (se 1 (by rfl) ⟨1427309, by rfl⟩ : syracuseStep 1903079 = 2854619) B2854619
theorem B2140969 : Blo 1901435 2140969 := bbase (se 2 (by rfl) ⟨802863, by rfl⟩ : syracuseStep 2140969 = 1605727) (by norm_num)
theorem B2854625 : Blo 1901435 2854625 := bstep (se 2 (by rfl) ⟨1070484, by rfl⟩ : syracuseStep 2854625 = 2140969) B2140969
theorem B1903083 : Blo 1901435 1903083 := bstep (se 1 (by rfl) ⟨1427312, by rfl⟩ : syracuseStep 1903083 = 2854625) B2854625
theorem B1929053 : Blo 1901435 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B5144141 : Blo 1901435 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B3429427 : Blo 1901435 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B4572569 : Blo 1901435 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B12193517 : Blo 1901435 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B8129011 : Blo 1901435 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B10838681 : Blo 1901435 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B7225787 : Blo 1901435 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B4817191 : Blo 1901435 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B6422921 : Blo 1901435 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B4281947 : Blo 1901435 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B2854631 : Blo 1901435 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B1903087 : Blo 1901435 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B2854637 : Blo 1901435 2854637 := bbase (se 3 (by rfl) ⟨535244, by rfl⟩ : syracuseStep 2854637 = 1070489) (by norm_num)
theorem B1903091 : Blo 1901435 1903091 := bstep (se 1 (by rfl) ⟨1427318, by rfl⟩ : syracuseStep 1903091 = 2854637) B2854637
theorem B4281965 : Blo 1901435 4281965 := bbase (se 3 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 4281965 = 1605737) (by norm_num)
theorem B2854643 : Blo 1901435 2854643 := bstep (se 1 (by rfl) ⟨2140982, by rfl⟩ : syracuseStep 2854643 = 4281965) B4281965
theorem B1903095 : Blo 1901435 1903095 := bstep (se 1 (by rfl) ⟨1427321, by rfl⟩ : syracuseStep 1903095 = 2854643) B2854643
theorem B3612917 : Blo 1901435 3612917 := bbase (se 5 (by rfl) ⟨169355, by rfl⟩ : syracuseStep 3612917 = 338711) (by norm_num)
theorem B2408611 : Blo 1901435 2408611 := bstep (se 1 (by rfl) ⟨1806458, by rfl⟩ : syracuseStep 2408611 = 3612917) B3612917
theorem B3211481 : Blo 1901435 3211481 := bstep (se 2 (by rfl) ⟨1204305, by rfl⟩ : syracuseStep 3211481 = 2408611) B2408611
theorem B2140987 : Blo 1901435 2140987 := bstep (se 1 (by rfl) ⟨1605740, by rfl⟩ : syracuseStep 2140987 = 3211481) B3211481
theorem B2854649 : Blo 1901435 2854649 := bstep (se 2 (by rfl) ⟨1070493, by rfl⟩ : syracuseStep 2854649 = 2140987) B2140987
theorem B1903099 : Blo 1901435 1903099 := bstep (se 1 (by rfl) ⟨1427324, by rfl⟩ : syracuseStep 1903099 = 2854649) B2854649
theorem B2059997 : Blo 1901435 2059997 := bbase (se 3 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 2059997 = 772499) (by norm_num)
theorem B5493325 : Blo 1901435 5493325 := bstep (se 3 (by rfl) ⟨1029998, by rfl⟩ : syracuseStep 5493325 = 2059997) B2059997
theorem B7324433 : Blo 1901435 7324433 := bstep (se 2 (by rfl) ⟨2746662, by rfl⟩ : syracuseStep 7324433 = 5493325) B5493325
theorem B4882955 : Blo 1901435 4882955 := bstep (se 1 (by rfl) ⟨3662216, by rfl⟩ : syracuseStep 4882955 = 7324433) B7324433
theorem B52084853 : Blo 1901435 52084853 := bstep (se 5 (by rfl) ⟨2441477, by rfl⟩ : syracuseStep 52084853 = 4882955) B4882955
theorem B34723235 : Blo 1901435 34723235 := bstep (se 1 (by rfl) ⟨26042426, by rfl⟩ : syracuseStep 34723235 = 52084853) B52084853
theorem B23148823 : Blo 1901435 23148823 := bstep (se 1 (by rfl) ⟨17361617, by rfl⟩ : syracuseStep 23148823 = 34723235) B34723235
theorem B30865097 : Blo 1901435 30865097 := bstep (se 2 (by rfl) ⟨11574411, by rfl⟩ : syracuseStep 30865097 = 23148823) B23148823
theorem B82306925 : Blo 1901435 82306925 := bstep (se 3 (by rfl) ⟨15432548, by rfl⟩ : syracuseStep 82306925 = 30865097) B30865097
theorem B54871283 : Blo 1901435 54871283 := bstep (se 1 (by rfl) ⟨41153462, by rfl⟩ : syracuseStep 54871283 = 82306925) B82306925
theorem B36580855 : Blo 1901435 36580855 := bstep (se 1 (by rfl) ⟨27435641, by rfl⟩ : syracuseStep 36580855 = 54871283) B54871283
theorem B48774473 : Blo 1901435 48774473 := bstep (se 2 (by rfl) ⟨18290427, by rfl⟩ : syracuseStep 48774473 = 36580855) B36580855
theorem B32516315 : Blo 1901435 32516315 := bstep (se 1 (by rfl) ⟨24387236, by rfl⟩ : syracuseStep 32516315 = 48774473) B48774473
theorem B21677543 : Blo 1901435 21677543 := bstep (se 1 (by rfl) ⟨16258157, by rfl⟩ : syracuseStep 21677543 = 32516315) B32516315
theorem B14451695 : Blo 1901435 14451695 := bstep (se 1 (by rfl) ⟨10838771, by rfl⟩ : syracuseStep 14451695 = 21677543) B21677543
theorem B9634463 : Blo 1901435 9634463 := bstep (se 1 (by rfl) ⟨7225847, by rfl⟩ : syracuseStep 9634463 = 14451695) B14451695
theorem B6422975 : Blo 1901435 6422975 := bstep (se 1 (by rfl) ⟨4817231, by rfl⟩ : syracuseStep 6422975 = 9634463) B9634463
theorem B4281983 : Blo 1901435 4281983 := bstep (se 1 (by rfl) ⟨3211487, by rfl⟩ : syracuseStep 4281983 = 6422975) B6422975
theorem B2854655 : Blo 1901435 2854655 := bstep (se 1 (by rfl) ⟨2140991, by rfl⟩ : syracuseStep 2854655 = 4281983) B4281983
theorem B1903103 : Blo 1901435 1903103 := bstep (se 1 (by rfl) ⟨1427327, by rfl⟩ : syracuseStep 1903103 = 2854655) B2854655
theorem B2854661 : Blo 1901435 2854661 := bbase (se 4 (by rfl) ⟨267624, by rfl⟩ : syracuseStep 2854661 = 535249) (by norm_num)
theorem B1903107 : Blo 1901435 1903107 := bstep (se 1 (by rfl) ⟨1427330, by rfl⟩ : syracuseStep 1903107 = 2854661) B2854661
theorem B3211501 : Blo 1901435 3211501 := bbase (se 3 (by rfl) ⟨602156, by rfl⟩ : syracuseStep 3211501 = 1204313) (by norm_num)
theorem B4282001 : Blo 1901435 4282001 := bstep (se 2 (by rfl) ⟨1605750, by rfl⟩ : syracuseStep 4282001 = 3211501) B3211501
theorem B2854667 : Blo 1901435 2854667 := bstep (se 1 (by rfl) ⟨2141000, by rfl⟩ : syracuseStep 2854667 = 4282001) B4282001
theorem B1903111 : Blo 1901435 1903111 := bstep (se 1 (by rfl) ⟨1427333, by rfl⟩ : syracuseStep 1903111 = 2854667) B2854667
theorem B2141005 : Blo 1901435 2141005 := bbase (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) (by norm_num)
theorem B2854673 : Blo 1901435 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B1903115 : Blo 1901435 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B6423029 : Blo 1901435 6423029 := bbase (se 5 (by rfl) ⟨301079, by rfl⟩ : syracuseStep 6423029 = 602159) (by norm_num)
theorem B4282019 : Blo 1901435 4282019 := bstep (se 1 (by rfl) ⟨3211514, by rfl⟩ : syracuseStep 4282019 = 6423029) B6423029
theorem B2854679 : Blo 1901435 2854679 := bstep (se 1 (by rfl) ⟨2141009, by rfl⟩ : syracuseStep 2854679 = 4282019) B4282019
theorem B1903119 : Blo 1901435 1903119 := bstep (se 1 (by rfl) ⟨1427339, by rfl⟩ : syracuseStep 1903119 = 2854679) B2854679
theorem B2854685 : Blo 1901435 2854685 := bbase (se 3 (by rfl) ⟨535253, by rfl⟩ : syracuseStep 2854685 = 1070507) (by norm_num)
theorem B1903123 : Blo 1901435 1903123 := bstep (se 1 (by rfl) ⟨1427342, by rfl⟩ : syracuseStep 1903123 = 2854685) B2854685
theorem B4282037 : Blo 1901435 4282037 := bbase (se 5 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 4282037 = 401441) (by norm_num)
theorem B2854691 : Blo 1901435 2854691 := bstep (se 1 (by rfl) ⟨2141018, by rfl⟩ : syracuseStep 2854691 = 4282037) B4282037
theorem B1903127 : Blo 1901435 1903127 := bstep (se 1 (by rfl) ⟨1427345, by rfl⟩ : syracuseStep 1903127 = 2854691) B2854691
theorem B10838933 : Blo 1901435 10838933 := bbase (se 6 (by rfl) ⟨254037, by rfl⟩ : syracuseStep 10838933 = 508075) (by norm_num)
theorem B7225955 : Blo 1901435 7225955 := bstep (se 1 (by rfl) ⟨5419466, by rfl⟩ : syracuseStep 7225955 = 10838933) B10838933
theorem B4817303 : Blo 1901435 4817303 := bstep (se 1 (by rfl) ⟨3612977, by rfl⟩ : syracuseStep 4817303 = 7225955) B7225955
theorem B3211535 : Blo 1901435 3211535 := bstep (se 1 (by rfl) ⟨2408651, by rfl⟩ : syracuseStep 3211535 = 4817303) B4817303
theorem B2141023 : Blo 1901435 2141023 := bstep (se 1 (by rfl) ⟨1605767, by rfl⟩ : syracuseStep 2141023 = 3211535) B3211535
theorem B2854697 : Blo 1901435 2854697 := bstep (se 2 (by rfl) ⟨1070511, by rfl⟩ : syracuseStep 2854697 = 2141023) B2141023
theorem B1903131 : Blo 1901435 1903131 := bstep (se 1 (by rfl) ⟨1427348, by rfl⟩ : syracuseStep 1903131 = 2854697) B2854697
theorem B5419477 : Blo 1901435 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B7225969 : Blo 1901435 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B9634625 : Blo 1901435 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B6423083 : Blo 1901435 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B4282055 : Blo 1901435 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B2854703 : Blo 1901435 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B1903135 : Blo 1901435 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B2854709 : Blo 1901435 2854709 := bbase (se 5 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 2854709 = 267629) (by norm_num)
theorem B1903139 : Blo 1901435 1903139 := bstep (se 1 (by rfl) ⟨1427354, by rfl⟩ : syracuseStep 1903139 = 2854709) B2854709
theorem B4817333 : Blo 1901435 4817333 := bbase (se 5 (by rfl) ⟨225812, by rfl⟩ : syracuseStep 4817333 = 451625) (by norm_num)
theorem B3211555 : Blo 1901435 3211555 := bstep (se 1 (by rfl) ⟨2408666, by rfl⟩ : syracuseStep 3211555 = 4817333) B4817333
theorem B4282073 : Blo 1901435 4282073 := bstep (se 2 (by rfl) ⟨1605777, by rfl⟩ : syracuseStep 4282073 = 3211555) B3211555
theorem B2854715 : Blo 1901435 2854715 := bstep (se 1 (by rfl) ⟨2141036, by rfl⟩ : syracuseStep 2854715 = 4282073) B4282073
theorem B1903143 : Blo 1901435 1903143 := bstep (se 1 (by rfl) ⟨1427357, by rfl⟩ : syracuseStep 1903143 = 2854715) B2854715
theorem B2141041 : Blo 1901435 2141041 := bbase (se 2 (by rfl) ⟨802890, by rfl⟩ : syracuseStep 2141041 = 1605781) (by norm_num)
theorem B2854721 : Blo 1901435 2854721 := bstep (se 2 (by rfl) ⟨1070520, by rfl⟩ : syracuseStep 2854721 = 2141041) B2141041
theorem B1903147 : Blo 1901435 1903147 := bstep (se 1 (by rfl) ⟨1427360, by rfl⟩ : syracuseStep 1903147 = 2854721) B2854721
theorem B8129285 : Blo 1901435 8129285 := bbase (se 4 (by rfl) ⟨762120, by rfl⟩ : syracuseStep 8129285 = 1524241) (by norm_num)
theorem B5419523 : Blo 1901435 5419523 := bstep (se 1 (by rfl) ⟨4064642, by rfl⟩ : syracuseStep 5419523 = 8129285) B8129285
theorem B3613015 : Blo 1901435 3613015 := bstep (se 1 (by rfl) ⟨2709761, by rfl⟩ : syracuseStep 3613015 = 5419523) B5419523
theorem B4817353 : Blo 1901435 4817353 := bstep (se 2 (by rfl) ⟨1806507, by rfl⟩ : syracuseStep 4817353 = 3613015) B3613015
theorem B6423137 : Blo 1901435 6423137 := bstep (se 2 (by rfl) ⟨2408676, by rfl⟩ : syracuseStep 6423137 = 4817353) B4817353
theorem B4282091 : Blo 1901435 4282091 := bstep (se 1 (by rfl) ⟨3211568, by rfl⟩ : syracuseStep 4282091 = 6423137) B6423137
theorem B2854727 : Blo 1901435 2854727 := bstep (se 1 (by rfl) ⟨2141045, by rfl⟩ : syracuseStep 2854727 = 4282091) B4282091
theorem B1903151 : Blo 1901435 1903151 := bstep (se 1 (by rfl) ⟨1427363, by rfl⟩ : syracuseStep 1903151 = 2854727) B2854727
theorem B2854733 : Blo 1901435 2854733 := bbase (se 3 (by rfl) ⟨535262, by rfl⟩ : syracuseStep 2854733 = 1070525) (by norm_num)
theorem B1903155 : Blo 1901435 1903155 := bstep (se 1 (by rfl) ⟨1427366, by rfl⟩ : syracuseStep 1903155 = 2854733) B2854733
theorem B4282109 : Blo 1901435 4282109 := bbase (se 3 (by rfl) ⟨802895, by rfl⟩ : syracuseStep 4282109 = 1605791) (by norm_num)
theorem B2854739 : Blo 1901435 2854739 := bstep (se 1 (by rfl) ⟨2141054, by rfl⟩ : syracuseStep 2854739 = 4282109) B4282109
theorem B1903159 : Blo 1901435 1903159 := bstep (se 1 (by rfl) ⟨1427369, by rfl⟩ : syracuseStep 1903159 = 2854739) B2854739
theorem B3211589 : Blo 1901435 3211589 := bbase (se 4 (by rfl) ⟨301086, by rfl⟩ : syracuseStep 3211589 = 602173) (by norm_num)
theorem B2141059 : Blo 1901435 2141059 := bstep (se 1 (by rfl) ⟨1605794, by rfl⟩ : syracuseStep 2141059 = 3211589) B3211589
theorem B2854745 : Blo 1901435 2854745 := bstep (se 2 (by rfl) ⟨1070529, by rfl⟩ : syracuseStep 2854745 = 2141059) B2141059
theorem B1903163 : Blo 1901435 1903163 := bstep (se 1 (by rfl) ⟨1427372, by rfl⟩ : syracuseStep 1903163 = 2854745) B2854745
theorem B14452181 : Blo 1901435 14452181 := bbase (se 7 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 14452181 = 338723) (by norm_num)
theorem B9634787 : Blo 1901435 9634787 := bstep (se 1 (by rfl) ⟨7226090, by rfl⟩ : syracuseStep 9634787 = 14452181) B14452181
theorem B6423191 : Blo 1901435 6423191 := bstep (se 1 (by rfl) ⟨4817393, by rfl⟩ : syracuseStep 6423191 = 9634787) B9634787
theorem B4282127 : Blo 1901435 4282127 := bstep (se 1 (by rfl) ⟨3211595, by rfl⟩ : syracuseStep 4282127 = 6423191) B6423191
theorem B2854751 : Blo 1901435 2854751 := bstep (se 1 (by rfl) ⟨2141063, by rfl⟩ : syracuseStep 2854751 = 4282127) B4282127
theorem B1903167 : Blo 1901435 1903167 := bstep (se 1 (by rfl) ⟨1427375, by rfl⟩ : syracuseStep 1903167 = 2854751) B2854751
theorem B2854757 : Blo 1901435 2854757 := bbase (se 4 (by rfl) ⟨267633, by rfl⟩ : syracuseStep 2854757 = 535267) (by norm_num)
theorem B1903171 : Blo 1901435 1903171 := bstep (se 1 (by rfl) ⟨1427378, by rfl⟩ : syracuseStep 1903171 = 2854757) B2854757
theorem B3613061 : Blo 1901435 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B2408707 : Blo 1901435 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B3211609 : Blo 1901435 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B4282145 : Blo 1901435 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B2854763 : Blo 1901435 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B1903175 : Blo 1901435 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B2141077 : Blo 1901435 2141077 := bbase (se 6 (by rfl) ⟨50181, by rfl⟩ : syracuseStep 2141077 = 100363) (by norm_num)
theorem B2854769 : Blo 1901435 2854769 := bstep (se 2 (by rfl) ⟨1070538, by rfl⟩ : syracuseStep 2854769 = 2141077) B2141077
theorem B1903179 : Blo 1901435 1903179 := bstep (se 1 (by rfl) ⟨1427384, by rfl⟩ : syracuseStep 1903179 = 2854769) B2854769
theorem B2408717 : Blo 1901435 2408717 := bbase (se 3 (by rfl) ⟨451634, by rfl⟩ : syracuseStep 2408717 = 903269) (by norm_num)
theorem B6423245 : Blo 1901435 6423245 := bstep (se 3 (by rfl) ⟨1204358, by rfl⟩ : syracuseStep 6423245 = 2408717) B2408717
theorem B4282163 : Blo 1901435 4282163 := bstep (se 1 (by rfl) ⟨3211622, by rfl⟩ : syracuseStep 4282163 = 6423245) B6423245
theorem B2854775 : Blo 1901435 2854775 := bstep (se 1 (by rfl) ⟨2141081, by rfl⟩ : syracuseStep 2854775 = 4282163) B4282163
theorem B1903183 : Blo 1901435 1903183 := bstep (se 1 (by rfl) ⟨1427387, by rfl⟩ : syracuseStep 1903183 = 2854775) B2854775
theorem B2854781 : Blo 1901435 2854781 := bbase (se 3 (by rfl) ⟨535271, by rfl⟩ : syracuseStep 2854781 = 1070543) (by norm_num)
theorem B1903187 : Blo 1901435 1903187 := bstep (se 1 (by rfl) ⟨1427390, by rfl⟩ : syracuseStep 1903187 = 2854781) B2854781
theorem B4282181 : Blo 1901435 4282181 := bbase (se 4 (by rfl) ⟨401454, by rfl⟩ : syracuseStep 4282181 = 802909) (by norm_num)
theorem B2854787 : Blo 1901435 2854787 := bstep (se 1 (by rfl) ⟨2141090, by rfl⟩ : syracuseStep 2854787 = 4282181) B4282181
theorem B1903191 : Blo 1901435 1903191 := bstep (se 1 (by rfl) ⟨1427393, by rfl⟩ : syracuseStep 1903191 = 2854787) B2854787
theorem B2170309 : Blo 1901435 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B2893745 : Blo 1901435 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B7716653 : Blo 1901435 7716653 := bstep (se 3 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 7716653 = 2893745) B2893745
theorem B5144435 : Blo 1901435 5144435 := bstep (se 1 (by rfl) ⟨3858326, by rfl⟩ : syracuseStep 5144435 = 7716653) B7716653
theorem B3429623 : Blo 1901435 3429623 := bstep (se 1 (by rfl) ⟨2572217, by rfl⟩ : syracuseStep 3429623 = 5144435) B5144435
theorem B2286415 : Blo 1901435 2286415 := bstep (se 1 (by rfl) ⟨1714811, by rfl⟩ : syracuseStep 2286415 = 3429623) B3429623
theorem B3048553 : Blo 1901435 3048553 := bstep (se 2 (by rfl) ⟨1143207, by rfl⟩ : syracuseStep 3048553 = 2286415) B2286415
theorem B4064737 : Blo 1901435 4064737 := bstep (se 2 (by rfl) ⟨1524276, by rfl⟩ : syracuseStep 4064737 = 3048553) B3048553
theorem B5419649 : Blo 1901435 5419649 := bstep (se 2 (by rfl) ⟨2032368, by rfl⟩ : syracuseStep 5419649 = 4064737) B4064737
theorem B3613099 : Blo 1901435 3613099 := bstep (se 1 (by rfl) ⟨2709824, by rfl⟩ : syracuseStep 3613099 = 5419649) B5419649
theorem B4817465 : Blo 1901435 4817465 := bstep (se 2 (by rfl) ⟨1806549, by rfl⟩ : syracuseStep 4817465 = 3613099) B3613099
theorem B3211643 : Blo 1901435 3211643 := bstep (se 1 (by rfl) ⟨2408732, by rfl⟩ : syracuseStep 3211643 = 4817465) B4817465
theorem B2141095 : Blo 1901435 2141095 := bstep (se 1 (by rfl) ⟨1605821, by rfl⟩ : syracuseStep 2141095 = 3211643) B3211643
theorem B2854793 : Blo 1901435 2854793 := bstep (se 2 (by rfl) ⟨1070547, by rfl⟩ : syracuseStep 2854793 = 2141095) B2141095
theorem B1903195 : Blo 1901435 1903195 := bstep (se 1 (by rfl) ⟨1427396, by rfl⟩ : syracuseStep 1903195 = 2854793) B2854793
theorem B9634949 : Blo 1901435 9634949 := bbase (se 4 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 9634949 = 1806553) (by norm_num)
theorem B6423299 : Blo 1901435 6423299 := bstep (se 1 (by rfl) ⟨4817474, by rfl⟩ : syracuseStep 6423299 = 9634949) B9634949
theorem B4282199 : Blo 1901435 4282199 := bstep (se 1 (by rfl) ⟨3211649, by rfl⟩ : syracuseStep 4282199 = 6423299) B6423299
theorem B2854799 : Blo 1901435 2854799 := bstep (se 1 (by rfl) ⟨2141099, by rfl⟩ : syracuseStep 2854799 = 4282199) B4282199
theorem B1903199 : Blo 1901435 1903199 := bstep (se 1 (by rfl) ⟨1427399, by rfl⟩ : syracuseStep 1903199 = 2854799) B2854799
theorem B2854805 : Blo 1901435 2854805 := bbase (se 6 (by rfl) ⟨66909, by rfl⟩ : syracuseStep 2854805 = 133819) (by norm_num)
theorem B1903203 : Blo 1901435 1903203 := bstep (se 1 (by rfl) ⟨1427402, by rfl⟩ : syracuseStep 1903203 = 2854805) B2854805
theorem B2032381 : Blo 1901435 2032381 := bbase (se 3 (by rfl) ⟨381071, by rfl⟩ : syracuseStep 2032381 = 762143) (by norm_num)
theorem B10839365 : Blo 1901435 10839365 := bstep (se 4 (by rfl) ⟨1016190, by rfl⟩ : syracuseStep 10839365 = 2032381) B2032381
theorem B7226243 : Blo 1901435 7226243 := bstep (se 1 (by rfl) ⟨5419682, by rfl⟩ : syracuseStep 7226243 = 10839365) B10839365
theorem B4817495 : Blo 1901435 4817495 := bstep (se 1 (by rfl) ⟨3613121, by rfl⟩ : syracuseStep 4817495 = 7226243) B7226243
theorem B3211663 : Blo 1901435 3211663 := bstep (se 1 (by rfl) ⟨2408747, by rfl⟩ : syracuseStep 3211663 = 4817495) B4817495
theorem B4282217 : Blo 1901435 4282217 := bstep (se 2 (by rfl) ⟨1605831, by rfl⟩ : syracuseStep 4282217 = 3211663) B3211663
theorem B2854811 : Blo 1901435 2854811 := bstep (se 1 (by rfl) ⟨2141108, by rfl⟩ : syracuseStep 2854811 = 4282217) B4282217
theorem B1903207 : Blo 1901435 1903207 := bstep (se 1 (by rfl) ⟨1427405, by rfl⟩ : syracuseStep 1903207 = 2854811) B2854811
theorem B2141113 : Blo 1901435 2141113 := bbase (se 2 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 2141113 = 1605835) (by norm_num)
theorem B2854817 : Blo 1901435 2854817 := bstep (se 2 (by rfl) ⟨1070556, by rfl⟩ : syracuseStep 2854817 = 2141113) B2141113
theorem B1903211 : Blo 1901435 1903211 := bstep (se 1 (by rfl) ⟨1427408, by rfl⟩ : syracuseStep 1903211 = 2854817) B2854817
theorem B4572877 : Blo 1901435 4572877 := bbase (se 3 (by rfl) ⟨857414, by rfl⟩ : syracuseStep 4572877 = 1714829) (by norm_num)
theorem B6097169 : Blo 1901435 6097169 := bstep (se 2 (by rfl) ⟨2286438, by rfl⟩ : syracuseStep 6097169 = 4572877) B4572877
theorem B4064779 : Blo 1901435 4064779 := bstep (se 1 (by rfl) ⟨3048584, by rfl⟩ : syracuseStep 4064779 = 6097169) B6097169
theorem B5419705 : Blo 1901435 5419705 := bstep (se 2 (by rfl) ⟨2032389, by rfl⟩ : syracuseStep 5419705 = 4064779) B4064779
theorem B7226273 : Blo 1901435 7226273 := bstep (se 2 (by rfl) ⟨2709852, by rfl⟩ : syracuseStep 7226273 = 5419705) B5419705
theorem B4817515 : Blo 1901435 4817515 := bstep (se 1 (by rfl) ⟨3613136, by rfl⟩ : syracuseStep 4817515 = 7226273) B7226273
theorem B6423353 : Blo 1901435 6423353 := bstep (se 2 (by rfl) ⟨2408757, by rfl⟩ : syracuseStep 6423353 = 4817515) B4817515
theorem B4282235 : Blo 1901435 4282235 := bstep (se 1 (by rfl) ⟨3211676, by rfl⟩ : syracuseStep 4282235 = 6423353) B6423353
theorem B2854823 : Blo 1901435 2854823 := bstep (se 1 (by rfl) ⟨2141117, by rfl⟩ : syracuseStep 2854823 = 4282235) B4282235
theorem B1903215 : Blo 1901435 1903215 := bstep (se 1 (by rfl) ⟨1427411, by rfl⟩ : syracuseStep 1903215 = 2854823) B2854823
theorem B2854829 : Blo 1901435 2854829 := bbase (se 3 (by rfl) ⟨535280, by rfl⟩ : syracuseStep 2854829 = 1070561) (by norm_num)
theorem B1903219 : Blo 1901435 1903219 := bstep (se 1 (by rfl) ⟨1427414, by rfl⟩ : syracuseStep 1903219 = 2854829) B2854829
theorem B4282253 : Blo 1901435 4282253 := bbase (se 3 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 4282253 = 1605845) (by norm_num)
theorem B2854835 : Blo 1901435 2854835 := bstep (se 1 (by rfl) ⟨2141126, by rfl⟩ : syracuseStep 2854835 = 4282253) B4282253
theorem B1903223 : Blo 1901435 1903223 := bstep (se 1 (by rfl) ⟨1427417, by rfl⟩ : syracuseStep 1903223 = 2854835) B2854835
theorem B2408773 : Blo 1901435 2408773 := bbase (se 4 (by rfl) ⟨225822, by rfl⟩ : syracuseStep 2408773 = 451645) (by norm_num)
theorem B3211697 : Blo 1901435 3211697 := bstep (se 2 (by rfl) ⟨1204386, by rfl⟩ : syracuseStep 3211697 = 2408773) B2408773
theorem B2141131 : Blo 1901435 2141131 := bstep (se 1 (by rfl) ⟨1605848, by rfl⟩ : syracuseStep 2141131 = 3211697) B3211697
theorem B2854841 : Blo 1901435 2854841 := bstep (se 2 (by rfl) ⟨1070565, by rfl⟩ : syracuseStep 2854841 = 2141131) B2141131
theorem B1903227 : Blo 1901435 1903227 := bstep (se 1 (by rfl) ⟨1427420, by rfl⟩ : syracuseStep 1903227 = 2854841) B2854841
theorem B9145829 : Blo 1901435 9145829 := bbase (se 4 (by rfl) ⟨857421, by rfl⟩ : syracuseStep 9145829 = 1714843) (by norm_num)
theorem B24388877 : Blo 1901435 24388877 := bstep (se 3 (by rfl) ⟨4572914, by rfl⟩ : syracuseStep 24388877 = 9145829) B9145829
theorem B16259251 : Blo 1901435 16259251 := bstep (se 1 (by rfl) ⟨12194438, by rfl⟩ : syracuseStep 16259251 = 24388877) B24388877
theorem B21679001 : Blo 1901435 21679001 := bstep (se 2 (by rfl) ⟨8129625, by rfl⟩ : syracuseStep 21679001 = 16259251) B16259251
theorem B14452667 : Blo 1901435 14452667 := bstep (se 1 (by rfl) ⟨10839500, by rfl⟩ : syracuseStep 14452667 = 21679001) B21679001
theorem B9635111 : Blo 1901435 9635111 := bstep (se 1 (by rfl) ⟨7226333, by rfl⟩ : syracuseStep 9635111 = 14452667) B14452667
theorem B6423407 : Blo 1901435 6423407 := bstep (se 1 (by rfl) ⟨4817555, by rfl⟩ : syracuseStep 6423407 = 9635111) B9635111
theorem B4282271 : Blo 1901435 4282271 := bstep (se 1 (by rfl) ⟨3211703, by rfl⟩ : syracuseStep 4282271 = 6423407) B6423407
theorem B2854847 : Blo 1901435 2854847 := bstep (se 1 (by rfl) ⟨2141135, by rfl⟩ : syracuseStep 2854847 = 4282271) B4282271
theorem B1903231 : Blo 1901435 1903231 := bstep (se 1 (by rfl) ⟨1427423, by rfl⟩ : syracuseStep 1903231 = 2854847) B2854847
theorem B2854853 : Blo 1901435 2854853 := bbase (se 4 (by rfl) ⟨267642, by rfl⟩ : syracuseStep 2854853 = 535285) (by norm_num)
theorem B1903235 : Blo 1901435 1903235 := bstep (se 1 (by rfl) ⟨1427426, by rfl⟩ : syracuseStep 1903235 = 2854853) B2854853
theorem B3211717 : Blo 1901435 3211717 := bbase (se 4 (by rfl) ⟨301098, by rfl⟩ : syracuseStep 3211717 = 602197) (by norm_num)
theorem B4282289 : Blo 1901435 4282289 := bstep (se 2 (by rfl) ⟨1605858, by rfl⟩ : syracuseStep 4282289 = 3211717) B3211717
theorem B2854859 : Blo 1901435 2854859 := bstep (se 1 (by rfl) ⟨2141144, by rfl⟩ : syracuseStep 2854859 = 4282289) B4282289
theorem B1903239 : Blo 1901435 1903239 := bstep (se 1 (by rfl) ⟨1427429, by rfl⟩ : syracuseStep 1903239 = 2854859) B2854859
theorem B2141149 : Blo 1901435 2141149 := bbase (se 3 (by rfl) ⟨401465, by rfl⟩ : syracuseStep 2141149 = 802931) (by norm_num)
theorem B2854865 : Blo 1901435 2854865 := bstep (se 2 (by rfl) ⟨1070574, by rfl⟩ : syracuseStep 2854865 = 2141149) B2141149
theorem B1903243 : Blo 1901435 1903243 := bstep (se 1 (by rfl) ⟨1427432, by rfl⟩ : syracuseStep 1903243 = 2854865) B2854865
theorem B6423461 : Blo 1901435 6423461 := bbase (se 4 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 6423461 = 1204399) (by norm_num)
theorem B4282307 : Blo 1901435 4282307 := bstep (se 1 (by rfl) ⟨3211730, by rfl⟩ : syracuseStep 4282307 = 6423461) B6423461
theorem B2854871 : Blo 1901435 2854871 := bstep (se 1 (by rfl) ⟨2141153, by rfl⟩ : syracuseStep 2854871 = 4282307) B4282307
theorem B1903247 : Blo 1901435 1903247 := bstep (se 1 (by rfl) ⟨1427435, by rfl⟩ : syracuseStep 1903247 = 2854871) B2854871
theorem B2854877 : Blo 1901435 2854877 := bbase (se 3 (by rfl) ⟨535289, by rfl⟩ : syracuseStep 2854877 = 1070579) (by norm_num)
theorem B1903251 : Blo 1901435 1903251 := bstep (se 1 (by rfl) ⟨1427438, by rfl⟩ : syracuseStep 1903251 = 2854877) B2854877
theorem B4282325 : Blo 1901435 4282325 := bbase (se 7 (by rfl) ⟨50183, by rfl⟩ : syracuseStep 4282325 = 100367) (by norm_num)
theorem B2854883 : Blo 1901435 2854883 := bstep (se 1 (by rfl) ⟨2141162, by rfl⟩ : syracuseStep 2854883 = 4282325) B4282325
theorem B1903255 : Blo 1901435 1903255 := bstep (se 1 (by rfl) ⟨1427441, by rfl⟩ : syracuseStep 1903255 = 2854883) B2854883
theorem B8681525 : Blo 1901435 8681525 := bbase (se 5 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 8681525 = 813893) (by norm_num)
theorem B5787683 : Blo 1901435 5787683 := bstep (se 1 (by rfl) ⟨4340762, by rfl⟩ : syracuseStep 5787683 = 8681525) B8681525
theorem B3858455 : Blo 1901435 3858455 := bstep (se 1 (by rfl) ⟨2893841, by rfl⟩ : syracuseStep 3858455 = 5787683) B5787683
theorem B10289213 : Blo 1901435 10289213 := bstep (se 3 (by rfl) ⟨1929227, by rfl⟩ : syracuseStep 10289213 = 3858455) B3858455
theorem B6859475 : Blo 1901435 6859475 := bstep (se 1 (by rfl) ⟨5144606, by rfl⟩ : syracuseStep 6859475 = 10289213) B10289213
theorem B4572983 : Blo 1901435 4572983 := bstep (se 1 (by rfl) ⟨3429737, by rfl⟩ : syracuseStep 4572983 = 6859475) B6859475
theorem B12194621 : Blo 1901435 12194621 := bstep (se 3 (by rfl) ⟨2286491, by rfl⟩ : syracuseStep 12194621 = 4572983) B4572983
theorem B8129747 : Blo 1901435 8129747 := bstep (se 1 (by rfl) ⟨6097310, by rfl⟩ : syracuseStep 8129747 = 12194621) B12194621
theorem B5419831 : Blo 1901435 5419831 := bstep (se 1 (by rfl) ⟨4064873, by rfl⟩ : syracuseStep 5419831 = 8129747) B8129747
theorem B7226441 : Blo 1901435 7226441 := bstep (se 2 (by rfl) ⟨2709915, by rfl⟩ : syracuseStep 7226441 = 5419831) B5419831
theorem B4817627 : Blo 1901435 4817627 := bstep (se 1 (by rfl) ⟨3613220, by rfl⟩ : syracuseStep 4817627 = 7226441) B7226441
theorem B3211751 : Blo 1901435 3211751 := bstep (se 1 (by rfl) ⟨2408813, by rfl⟩ : syracuseStep 3211751 = 4817627) B4817627
theorem B2141167 : Blo 1901435 2141167 := bstep (se 1 (by rfl) ⟨1605875, by rfl⟩ : syracuseStep 2141167 = 3211751) B3211751
theorem B2854889 : Blo 1901435 2854889 := bstep (se 2 (by rfl) ⟨1070583, by rfl⟩ : syracuseStep 2854889 = 2141167) B2141167
theorem B1903259 : Blo 1901435 1903259 := bstep (se 1 (by rfl) ⟨1427444, by rfl⟩ : syracuseStep 1903259 = 2854889) B2854889
theorem B3048661 : Blo 1901435 3048661 := bbase (se 7 (by rfl) ⟨35726, by rfl⟩ : syracuseStep 3048661 = 71453) (by norm_num)
theorem B16259525 : Blo 1901435 16259525 := bstep (se 4 (by rfl) ⟨1524330, by rfl⟩ : syracuseStep 16259525 = 3048661) B3048661
theorem B10839683 : Blo 1901435 10839683 := bstep (se 1 (by rfl) ⟨8129762, by rfl⟩ : syracuseStep 10839683 = 16259525) B16259525
theorem B7226455 : Blo 1901435 7226455 := bstep (se 1 (by rfl) ⟨5419841, by rfl⟩ : syracuseStep 7226455 = 10839683) B10839683
theorem B9635273 : Blo 1901435 9635273 := bstep (se 2 (by rfl) ⟨3613227, by rfl⟩ : syracuseStep 9635273 = 7226455) B7226455
theorem B6423515 : Blo 1901435 6423515 := bstep (se 1 (by rfl) ⟨4817636, by rfl⟩ : syracuseStep 6423515 = 9635273) B9635273
theorem B4282343 : Blo 1901435 4282343 := bstep (se 1 (by rfl) ⟨3211757, by rfl⟩ : syracuseStep 4282343 = 6423515) B6423515
theorem B2854895 : Blo 1901435 2854895 := bstep (se 1 (by rfl) ⟨2141171, by rfl⟩ : syracuseStep 2854895 = 4282343) B4282343
theorem B1903263 : Blo 1901435 1903263 := bstep (se 1 (by rfl) ⟨1427447, by rfl⟩ : syracuseStep 1903263 = 2854895) B2854895
theorem B2854901 : Blo 1901435 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B1903267 : Blo 1901435 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B6097349 : Blo 1901435 6097349 := bbase (se 4 (by rfl) ⟨571626, by rfl⟩ : syracuseStep 6097349 = 1143253) (by norm_num)
theorem B4064899 : Blo 1901435 4064899 := bstep (se 1 (by rfl) ⟨3048674, by rfl⟩ : syracuseStep 4064899 = 6097349) B6097349
theorem B5419865 : Blo 1901435 5419865 := bstep (se 2 (by rfl) ⟨2032449, by rfl⟩ : syracuseStep 5419865 = 4064899) B4064899
theorem B3613243 : Blo 1901435 3613243 := bstep (se 1 (by rfl) ⟨2709932, by rfl⟩ : syracuseStep 3613243 = 5419865) B5419865
theorem B4817657 : Blo 1901435 4817657 := bstep (se 2 (by rfl) ⟨1806621, by rfl⟩ : syracuseStep 4817657 = 3613243) B3613243
theorem B3211771 : Blo 1901435 3211771 := bstep (se 1 (by rfl) ⟨2408828, by rfl⟩ : syracuseStep 3211771 = 4817657) B4817657
theorem B4282361 : Blo 1901435 4282361 := bstep (se 2 (by rfl) ⟨1605885, by rfl⟩ : syracuseStep 4282361 = 3211771) B3211771
theorem B2854907 : Blo 1901435 2854907 := bstep (se 1 (by rfl) ⟨2141180, by rfl⟩ : syracuseStep 2854907 = 4282361) B4282361
theorem B1903271 : Blo 1901435 1903271 := bstep (se 1 (by rfl) ⟨1427453, by rfl⟩ : syracuseStep 1903271 = 2854907) B2854907
theorem B2141185 : Blo 1901435 2141185 := bbase (se 2 (by rfl) ⟨802944, by rfl⟩ : syracuseStep 2141185 = 1605889) (by norm_num)
theorem B2854913 : Blo 1901435 2854913 := bstep (se 2 (by rfl) ⟨1070592, by rfl⟩ : syracuseStep 2854913 = 2141185) B2141185
theorem B1903275 : Blo 1901435 1903275 := bstep (se 1 (by rfl) ⟨1427456, by rfl⟩ : syracuseStep 1903275 = 2854913) B2854913
theorem B4817677 : Blo 1901435 4817677 := bbase (se 3 (by rfl) ⟨903314, by rfl⟩ : syracuseStep 4817677 = 1806629) (by norm_num)
theorem B6423569 : Blo 1901435 6423569 := bstep (se 2 (by rfl) ⟨2408838, by rfl⟩ : syracuseStep 6423569 = 4817677) B4817677
theorem B4282379 : Blo 1901435 4282379 := bstep (se 1 (by rfl) ⟨3211784, by rfl⟩ : syracuseStep 4282379 = 6423569) B6423569
theorem B2854919 : Blo 1901435 2854919 := bstep (se 1 (by rfl) ⟨2141189, by rfl⟩ : syracuseStep 2854919 = 4282379) B4282379
theorem B1903279 : Blo 1901435 1903279 := bstep (se 1 (by rfl) ⟨1427459, by rfl⟩ : syracuseStep 1903279 = 2854919) B2854919
theorem B2854925 : Blo 1901435 2854925 := bbase (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) (by norm_num)
theorem B1903283 : Blo 1901435 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B4282397 : Blo 1901435 4282397 := bbase (se 3 (by rfl) ⟨802949, by rfl⟩ : syracuseStep 4282397 = 1605899) (by norm_num)
theorem B2854931 : Blo 1901435 2854931 := bstep (se 1 (by rfl) ⟨2141198, by rfl⟩ : syracuseStep 2854931 = 4282397) B4282397
theorem B1903287 : Blo 1901435 1903287 := bstep (se 1 (by rfl) ⟨1427465, by rfl⟩ : syracuseStep 1903287 = 2854931) B2854931
theorem B3211805 : Blo 1901435 3211805 := bbase (se 3 (by rfl) ⟨602213, by rfl⟩ : syracuseStep 3211805 = 1204427) (by norm_num)
theorem B2141203 : Blo 1901435 2141203 := bstep (se 1 (by rfl) ⟨1605902, by rfl⟩ : syracuseStep 2141203 = 3211805) B3211805
theorem B2854937 : Blo 1901435 2854937 := bstep (se 2 (by rfl) ⟨1070601, by rfl⟩ : syracuseStep 2854937 = 2141203) B2141203
theorem B1903291 : Blo 1901435 1903291 := bstep (se 1 (by rfl) ⟨1427468, by rfl⟩ : syracuseStep 1903291 = 2854937) B2854937
theorem B4582637 : Blo 1901435 4582637 := bbase (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) (by norm_num)
theorem B3055091 : Blo 1901435 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B8146909 : Blo 1901435 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B10862545 : Blo 1901435 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B14483393 : Blo 1901435 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B9655595 : Blo 1901435 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B6437063 : Blo 1901435 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B4291375 : Blo 1901435 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B5721833 : Blo 1901435 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B3814555 : Blo 1901435 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B5086073 : Blo 1901435 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B13562861 : Blo 1901435 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B36167629 : Blo 1901435 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B48223505 : Blo 1901435 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B32149003 : Blo 1901435 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B42865337 : Blo 1901435 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B28576891 : Blo 1901435 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B152410085 : Blo 1901435 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B101606723 : Blo 1901435 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B67737815 : Blo 1901435 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B45158543 : Blo 1901435 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B30105695 : Blo 1901435 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B80281853 : Blo 1901435 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B53521235 : Blo 1901435 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B35680823 : Blo 1901435 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B23787215 : Blo 1901435 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B15858143 : Blo 1901435 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B10572095 : Blo 1901435 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B7048063 : Blo 1901435 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B9397417 : Blo 1901435 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B12529889 : Blo 1901435 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B8353259 : Blo 1901435 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B5568839 : Blo 1901435 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B3712559 : Blo 1901435 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B9900157 : Blo 1901435 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B13200209 : Blo 1901435 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B8800139 : Blo 1901435 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B5866759 : Blo 1901435 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B7822345 : Blo 1901435 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1901435 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B6953195 : Blo 1901435 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B4635463 : Blo 1901435 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B6180617 : Blo 1901435 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B4120411 : Blo 1901435 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B5493881 : Blo 1901435 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1901435 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B19533797 : Blo 1901435 19533797 := bstep (se 4 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 19533797 = 3662587) B3662587
theorem B13022531 : Blo 1901435 13022531 := bstep (se 1 (by rfl) ⟨9766898, by rfl⟩ : syracuseStep 13022531 = 19533797) B19533797
theorem B8681687 : Blo 1901435 8681687 := bstep (se 1 (by rfl) ⟨6511265, by rfl⟩ : syracuseStep 8681687 = 13022531) B13022531
theorem B5787791 : Blo 1901435 5787791 := bstep (se 1 (by rfl) ⟨4340843, by rfl⟩ : syracuseStep 5787791 = 8681687) B8681687
theorem B3858527 : Blo 1901435 3858527 := bstep (se 1 (by rfl) ⟨2893895, by rfl⟩ : syracuseStep 3858527 = 5787791) B5787791
theorem B10289405 : Blo 1901435 10289405 := bstep (se 3 (by rfl) ⟨1929263, by rfl⟩ : syracuseStep 10289405 = 3858527) B3858527
theorem B6859603 : Blo 1901435 6859603 := bstep (se 1 (by rfl) ⟨5144702, by rfl⟩ : syracuseStep 6859603 = 10289405) B10289405
theorem B9146137 : Blo 1901435 9146137 := bstep (se 2 (by rfl) ⟨3429801, by rfl⟩ : syracuseStep 9146137 = 6859603) B6859603
theorem B12194849 : Blo 1901435 12194849 := bstep (se 2 (by rfl) ⟨4573068, by rfl⟩ : syracuseStep 12194849 = 9146137) B9146137
theorem B8129899 : Blo 1901435 8129899 := bstep (se 1 (by rfl) ⟨6097424, by rfl⟩ : syracuseStep 8129899 = 12194849) B12194849
theorem B10839865 : Blo 1901435 10839865 := bstep (se 2 (by rfl) ⟨4064949, by rfl⟩ : syracuseStep 10839865 = 8129899) B8129899
theorem B14453153 : Blo 1901435 14453153 := bstep (se 2 (by rfl) ⟨5419932, by rfl⟩ : syracuseStep 14453153 = 10839865) B10839865
theorem B9635435 : Blo 1901435 9635435 := bstep (se 1 (by rfl) ⟨7226576, by rfl⟩ : syracuseStep 9635435 = 14453153) B14453153
theorem B6423623 : Blo 1901435 6423623 := bstep (se 1 (by rfl) ⟨4817717, by rfl⟩ : syracuseStep 6423623 = 9635435) B9635435
theorem B4282415 : Blo 1901435 4282415 := bstep (se 1 (by rfl) ⟨3211811, by rfl⟩ : syracuseStep 4282415 = 6423623) B6423623
theorem B2854943 : Blo 1901435 2854943 := bstep (se 1 (by rfl) ⟨2141207, by rfl⟩ : syracuseStep 2854943 = 4282415) B4282415
theorem B1903295 : Blo 1901435 1903295 := bstep (se 1 (by rfl) ⟨1427471, by rfl⟩ : syracuseStep 1903295 = 2854943) B2854943
theorem B2854949 : Blo 1901435 2854949 := bbase (se 4 (by rfl) ⟨267651, by rfl⟩ : syracuseStep 2854949 = 535303) (by norm_num)
theorem B1903299 : Blo 1901435 1903299 := bstep (se 1 (by rfl) ⟨1427474, by rfl⟩ : syracuseStep 1903299 = 2854949) B2854949
theorem B2408869 : Blo 1901435 2408869 := bbase (se 4 (by rfl) ⟨225831, by rfl⟩ : syracuseStep 2408869 = 451663) (by norm_num)
theorem B3211825 : Blo 1901435 3211825 := bstep (se 2 (by rfl) ⟨1204434, by rfl⟩ : syracuseStep 3211825 = 2408869) B2408869
theorem B4282433 : Blo 1901435 4282433 := bstep (se 2 (by rfl) ⟨1605912, by rfl⟩ : syracuseStep 4282433 = 3211825) B3211825
theorem B2854955 : Blo 1901435 2854955 := bstep (se 1 (by rfl) ⟨2141216, by rfl⟩ : syracuseStep 2854955 = 4282433) B4282433
theorem B1903303 : Blo 1901435 1903303 := bstep (se 1 (by rfl) ⟨1427477, by rfl⟩ : syracuseStep 1903303 = 2854955) B2854955
theorem B2141221 : Blo 1901435 2141221 := bbase (se 4 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 2141221 = 401479) (by norm_num)
theorem B2854961 : Blo 1901435 2854961 := bstep (se 2 (by rfl) ⟨1070610, by rfl⟩ : syracuseStep 2854961 = 2141221) B2141221
theorem B1903307 : Blo 1901435 1903307 := bstep (se 1 (by rfl) ⟨1427480, by rfl⟩ : syracuseStep 1903307 = 2854961) B2854961
theorem B6097477 : Blo 1901435 6097477 := bbase (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) (by norm_num)
theorem B8129969 : Blo 1901435 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B5419979 : Blo 1901435 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B3613319 : Blo 1901435 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B2408879 : Blo 1901435 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B6423677 : Blo 1901435 6423677 := bstep (se 3 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 6423677 = 2408879) B2408879
theorem B4282451 : Blo 1901435 4282451 := bstep (se 1 (by rfl) ⟨3211838, by rfl⟩ : syracuseStep 4282451 = 6423677) B6423677
theorem B2854967 : Blo 1901435 2854967 := bstep (se 1 (by rfl) ⟨2141225, by rfl⟩ : syracuseStep 2854967 = 4282451) B4282451
theorem B1903311 : Blo 1901435 1903311 := bstep (se 1 (by rfl) ⟨1427483, by rfl⟩ : syracuseStep 1903311 = 2854967) B2854967
theorem B2854973 : Blo 1901435 2854973 := bbase (se 3 (by rfl) ⟨535307, by rfl⟩ : syracuseStep 2854973 = 1070615) (by norm_num)
theorem B1903315 : Blo 1901435 1903315 := bstep (se 1 (by rfl) ⟨1427486, by rfl⟩ : syracuseStep 1903315 = 2854973) B2854973
theorem B4282469 : Blo 1901435 4282469 := bbase (se 4 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 4282469 = 802963) (by norm_num)
theorem B2854979 : Blo 1901435 2854979 := bstep (se 1 (by rfl) ⟨2141234, by rfl⟩ : syracuseStep 2854979 = 4282469) B4282469
theorem B1903319 : Blo 1901435 1903319 := bstep (se 1 (by rfl) ⟨1427489, by rfl⟩ : syracuseStep 1903319 = 2854979) B2854979
theorem B4817789 : Blo 1901435 4817789 := bbase (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) (by norm_num)
theorem B3211859 : Blo 1901435 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B2141239 : Blo 1901435 2141239 := bstep (se 1 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 2141239 = 3211859) B3211859
theorem B2854985 : Blo 1901435 2854985 := bstep (se 2 (by rfl) ⟨1070619, by rfl⟩ : syracuseStep 2854985 = 2141239) B2141239
theorem B1903323 : Blo 1901435 1903323 := bstep (se 1 (by rfl) ⟨1427492, by rfl⟩ : syracuseStep 1903323 = 2854985) B2854985
theorem B3613349 : Blo 1901435 3613349 := bbase (se 4 (by rfl) ⟨338751, by rfl⟩ : syracuseStep 3613349 = 677503) (by norm_num)
theorem B9635597 : Blo 1901435 9635597 := bstep (se 3 (by rfl) ⟨1806674, by rfl⟩ : syracuseStep 9635597 = 3613349) B3613349
theorem B6423731 : Blo 1901435 6423731 := bstep (se 1 (by rfl) ⟨4817798, by rfl⟩ : syracuseStep 6423731 = 9635597) B9635597
theorem B4282487 : Blo 1901435 4282487 := bstep (se 1 (by rfl) ⟨3211865, by rfl⟩ : syracuseStep 4282487 = 6423731) B6423731
theorem B2854991 : Blo 1901435 2854991 := bstep (se 1 (by rfl) ⟨2141243, by rfl⟩ : syracuseStep 2854991 = 4282487) B4282487
theorem B1903327 : Blo 1901435 1903327 := bstep (se 1 (by rfl) ⟨1427495, by rfl⟩ : syracuseStep 1903327 = 2854991) B2854991
theorem B2854997 : Blo 1901435 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B1903331 : Blo 1901435 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B18292661 : Blo 1901435 18292661 := bbase (se 5 (by rfl) ⟨857468, by rfl⟩ : syracuseStep 18292661 = 1714937) (by norm_num)
theorem B12195107 : Blo 1901435 12195107 := bstep (se 1 (by rfl) ⟨9146330, by rfl⟩ : syracuseStep 12195107 = 18292661) B18292661
theorem B8130071 : Blo 1901435 8130071 := bstep (se 1 (by rfl) ⟨6097553, by rfl⟩ : syracuseStep 8130071 = 12195107) B12195107
theorem B5420047 : Blo 1901435 5420047 := bstep (se 1 (by rfl) ⟨4065035, by rfl⟩ : syracuseStep 5420047 = 8130071) B8130071
theorem B7226729 : Blo 1901435 7226729 := bstep (se 2 (by rfl) ⟨2710023, by rfl⟩ : syracuseStep 7226729 = 5420047) B5420047
theorem B4817819 : Blo 1901435 4817819 := bstep (se 1 (by rfl) ⟨3613364, by rfl⟩ : syracuseStep 4817819 = 7226729) B7226729
theorem B3211879 : Blo 1901435 3211879 := bstep (se 1 (by rfl) ⟨2408909, by rfl⟩ : syracuseStep 3211879 = 4817819) B4817819
theorem B4282505 : Blo 1901435 4282505 := bstep (se 2 (by rfl) ⟨1605939, by rfl⟩ : syracuseStep 4282505 = 3211879) B3211879
theorem B2855003 : Blo 1901435 2855003 := bstep (se 1 (by rfl) ⟨2141252, by rfl⟩ : syracuseStep 2855003 = 4282505) B4282505
theorem B1903335 : Blo 1901435 1903335 := bstep (se 1 (by rfl) ⟨1427501, by rfl⟩ : syracuseStep 1903335 = 2855003) B2855003
theorem B2141257 : Blo 1901435 2141257 := bbase (se 2 (by rfl) ⟨802971, by rfl⟩ : syracuseStep 2141257 = 1605943) (by norm_num)
theorem B2855009 : Blo 1901435 2855009 := bstep (se 2 (by rfl) ⟨1070628, by rfl⟩ : syracuseStep 2855009 = 2141257) B2141257
theorem B1903339 : Blo 1901435 1903339 := bstep (se 1 (by rfl) ⟨1427504, by rfl⟩ : syracuseStep 1903339 = 2855009) B2855009
theorem B12195157 : Blo 1901435 12195157 := bbase (se 14 (by rfl) ⟨1116, by rfl⟩ : syracuseStep 12195157 = 2233) (by norm_num)
theorem B16260209 : Blo 1901435 16260209 := bstep (se 2 (by rfl) ⟨6097578, by rfl⟩ : syracuseStep 16260209 = 12195157) B12195157
theorem B10840139 : Blo 1901435 10840139 := bstep (se 1 (by rfl) ⟨8130104, by rfl⟩ : syracuseStep 10840139 = 16260209) B16260209
theorem B7226759 : Blo 1901435 7226759 := bstep (se 1 (by rfl) ⟨5420069, by rfl⟩ : syracuseStep 7226759 = 10840139) B10840139
theorem B4817839 : Blo 1901435 4817839 := bstep (se 1 (by rfl) ⟨3613379, by rfl⟩ : syracuseStep 4817839 = 7226759) B7226759
theorem B6423785 : Blo 1901435 6423785 := bstep (se 2 (by rfl) ⟨2408919, by rfl⟩ : syracuseStep 6423785 = 4817839) B4817839
theorem B4282523 : Blo 1901435 4282523 := bstep (se 1 (by rfl) ⟨3211892, by rfl⟩ : syracuseStep 4282523 = 6423785) B6423785
theorem B2855015 : Blo 1901435 2855015 := bstep (se 1 (by rfl) ⟨2141261, by rfl⟩ : syracuseStep 2855015 = 4282523) B4282523
theorem B1903343 : Blo 1901435 1903343 := bstep (se 1 (by rfl) ⟨1427507, by rfl⟩ : syracuseStep 1903343 = 2855015) B2855015
theorem B2855021 : Blo 1901435 2855021 := bbase (se 3 (by rfl) ⟨535316, by rfl⟩ : syracuseStep 2855021 = 1070633) (by norm_num)
theorem B1903347 : Blo 1901435 1903347 := bstep (se 1 (by rfl) ⟨1427510, by rfl⟩ : syracuseStep 1903347 = 2855021) B2855021
theorem B4282541 : Blo 1901435 4282541 := bbase (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) (by norm_num)
theorem B2855027 : Blo 1901435 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B1903351 : Blo 1901435 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B7717301 : Blo 1901435 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B5144867 : Blo 1901435 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B3429911 : Blo 1901435 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B9146429 : Blo 1901435 9146429 := bstep (se 3 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 9146429 = 3429911) B3429911
theorem B6097619 : Blo 1901435 6097619 := bstep (se 1 (by rfl) ⟨4573214, by rfl⟩ : syracuseStep 6097619 = 9146429) B9146429
theorem B4065079 : Blo 1901435 4065079 := bstep (se 1 (by rfl) ⟨3048809, by rfl⟩ : syracuseStep 4065079 = 6097619) B6097619
theorem B5420105 : Blo 1901435 5420105 := bstep (se 2 (by rfl) ⟨2032539, by rfl⟩ : syracuseStep 5420105 = 4065079) B4065079
theorem B3613403 : Blo 1901435 3613403 := bstep (se 1 (by rfl) ⟨2710052, by rfl⟩ : syracuseStep 3613403 = 5420105) B5420105
theorem B2408935 : Blo 1901435 2408935 := bstep (se 1 (by rfl) ⟨1806701, by rfl⟩ : syracuseStep 2408935 = 3613403) B3613403
theorem B3211913 : Blo 1901435 3211913 := bstep (se 2 (by rfl) ⟨1204467, by rfl⟩ : syracuseStep 3211913 = 2408935) B2408935
theorem B2141275 : Blo 1901435 2141275 := bstep (se 1 (by rfl) ⟨1605956, by rfl⟩ : syracuseStep 2141275 = 3211913) B3211913
theorem B2855033 : Blo 1901435 2855033 := bstep (se 2 (by rfl) ⟨1070637, by rfl⟩ : syracuseStep 2855033 = 2141275) B2141275
theorem B1903355 : Blo 1901435 1903355 := bstep (se 1 (by rfl) ⟨1427516, by rfl⟩ : syracuseStep 1903355 = 2855033) B2855033
theorem B3429917 : Blo 1901435 3429917 := bbase (se 3 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 3429917 = 1286219) (by norm_num)
theorem B2286611 : Blo 1901435 2286611 := bstep (se 1 (by rfl) ⟨1714958, by rfl⟩ : syracuseStep 2286611 = 3429917) B3429917
theorem B24390517 : Blo 1901435 24390517 := bstep (se 5 (by rfl) ⟨1143305, by rfl⟩ : syracuseStep 24390517 = 2286611) B2286611
theorem B32520689 : Blo 1901435 32520689 := bstep (se 2 (by rfl) ⟨12195258, by rfl⟩ : syracuseStep 32520689 = 24390517) B24390517
theorem B21680459 : Blo 1901435 21680459 := bstep (se 1 (by rfl) ⟨16260344, by rfl⟩ : syracuseStep 21680459 = 32520689) B32520689
theorem B14453639 : Blo 1901435 14453639 := bstep (se 1 (by rfl) ⟨10840229, by rfl⟩ : syracuseStep 14453639 = 21680459) B21680459
theorem B9635759 : Blo 1901435 9635759 := bstep (se 1 (by rfl) ⟨7226819, by rfl⟩ : syracuseStep 9635759 = 14453639) B14453639
theorem B6423839 : Blo 1901435 6423839 := bstep (se 1 (by rfl) ⟨4817879, by rfl⟩ : syracuseStep 6423839 = 9635759) B9635759
theorem B4282559 : Blo 1901435 4282559 := bstep (se 1 (by rfl) ⟨3211919, by rfl⟩ : syracuseStep 4282559 = 6423839) B6423839
theorem B2855039 : Blo 1901435 2855039 := bstep (se 1 (by rfl) ⟨2141279, by rfl⟩ : syracuseStep 2855039 = 4282559) B4282559
theorem B1903359 : Blo 1901435 1903359 := bstep (se 1 (by rfl) ⟨1427519, by rfl⟩ : syracuseStep 1903359 = 2855039) B2855039
theorem B2855045 : Blo 1901435 2855045 := bbase (se 4 (by rfl) ⟨267660, by rfl⟩ : syracuseStep 2855045 = 535321) (by norm_num)
theorem B1903363 : Blo 1901435 1903363 := bstep (se 1 (by rfl) ⟨1427522, by rfl⟩ : syracuseStep 1903363 = 2855045) B2855045
theorem B3211933 : Blo 1901435 3211933 := bbase (se 3 (by rfl) ⟨602237, by rfl⟩ : syracuseStep 3211933 = 1204475) (by norm_num)
theorem B4282577 : Blo 1901435 4282577 := bstep (se 2 (by rfl) ⟨1605966, by rfl⟩ : syracuseStep 4282577 = 3211933) B3211933
theorem B2855051 : Blo 1901435 2855051 := bstep (se 1 (by rfl) ⟨2141288, by rfl⟩ : syracuseStep 2855051 = 4282577) B4282577
theorem B1903367 : Blo 1901435 1903367 := bstep (se 1 (by rfl) ⟨1427525, by rfl⟩ : syracuseStep 1903367 = 2855051) B2855051
theorem B2141293 : Blo 1901435 2141293 := bbase (se 3 (by rfl) ⟨401492, by rfl⟩ : syracuseStep 2141293 = 802985) (by norm_num)
theorem B2855057 : Blo 1901435 2855057 := bstep (se 2 (by rfl) ⟨1070646, by rfl⟩ : syracuseStep 2855057 = 2141293) B2141293
theorem B1903371 : Blo 1901435 1903371 := bstep (se 1 (by rfl) ⟨1427528, by rfl⟩ : syracuseStep 1903371 = 2855057) B2855057
theorem B6423893 : Blo 1901435 6423893 := bbase (se 12 (by rfl) ⟨2352, by rfl⟩ : syracuseStep 6423893 = 4705) (by norm_num)
theorem B4282595 : Blo 1901435 4282595 := bstep (se 1 (by rfl) ⟨3211946, by rfl⟩ : syracuseStep 4282595 = 6423893) B6423893
theorem B2855063 : Blo 1901435 2855063 := bstep (se 1 (by rfl) ⟨2141297, by rfl⟩ : syracuseStep 2855063 = 4282595) B4282595
theorem B1903375 : Blo 1901435 1903375 := bstep (se 1 (by rfl) ⟨1427531, by rfl⟩ : syracuseStep 1903375 = 2855063) B2855063
theorem B2855069 : Blo 1901435 2855069 := bbase (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) (by norm_num)
theorem B1903379 : Blo 1901435 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B4282613 : Blo 1901435 4282613 := bbase (se 5 (by rfl) ⟨200747, by rfl⟩ : syracuseStep 4282613 = 401495) (by norm_num)
theorem B2855075 : Blo 1901435 2855075 := bstep (se 1 (by rfl) ⟨2141306, by rfl⟩ : syracuseStep 2855075 = 4282613) B4282613
theorem B1903383 : Blo 1901435 1903383 := bstep (se 1 (by rfl) ⟨1427537, by rfl⟩ : syracuseStep 1903383 = 2855075) B2855075
theorem B12530485 : Blo 1901435 12530485 := bbase (se 5 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 12530485 = 1174733) (by norm_num)
theorem B16707313 : Blo 1901435 16707313 := bstep (se 2 (by rfl) ⟨6265242, by rfl⟩ : syracuseStep 16707313 = 12530485) B12530485
theorem B89105669 : Blo 1901435 89105669 := bstep (se 4 (by rfl) ⟨8353656, by rfl⟩ : syracuseStep 89105669 = 16707313) B16707313
theorem B59403779 : Blo 1901435 59403779 := bstep (se 1 (by rfl) ⟨44552834, by rfl⟩ : syracuseStep 59403779 = 89105669) B89105669
theorem B39602519 : Blo 1901435 39602519 := bstep (se 1 (by rfl) ⟨29701889, by rfl⟩ : syracuseStep 39602519 = 59403779) B59403779
theorem B26401679 : Blo 1901435 26401679 := bstep (se 1 (by rfl) ⟨19801259, by rfl⟩ : syracuseStep 26401679 = 39602519) B39602519
theorem B17601119 : Blo 1901435 17601119 := bstep (se 1 (by rfl) ⟨13200839, by rfl⟩ : syracuseStep 17601119 = 26401679) B26401679
theorem B11734079 : Blo 1901435 11734079 := bstep (se 1 (by rfl) ⟨8800559, by rfl⟩ : syracuseStep 11734079 = 17601119) B17601119
theorem B31290877 : Blo 1901435 31290877 := bstep (se 3 (by rfl) ⟨5867039, by rfl⟩ : syracuseStep 31290877 = 11734079) B11734079
theorem B41721169 : Blo 1901435 41721169 := bstep (se 2 (by rfl) ⟨15645438, by rfl⟩ : syracuseStep 41721169 = 31290877) B31290877
theorem B55628225 : Blo 1901435 55628225 := bstep (se 2 (by rfl) ⟨20860584, by rfl⟩ : syracuseStep 55628225 = 41721169) B41721169
theorem B37085483 : Blo 1901435 37085483 := bstep (se 1 (by rfl) ⟨27814112, by rfl⟩ : syracuseStep 37085483 = 55628225) B55628225
theorem B98894621 : Blo 1901435 98894621 := bstep (se 3 (by rfl) ⟨18542741, by rfl⟩ : syracuseStep 98894621 = 37085483) B37085483
theorem B65929747 : Blo 1901435 65929747 := bstep (se 1 (by rfl) ⟨49447310, by rfl⟩ : syracuseStep 65929747 = 98894621) B98894621
theorem B87906329 : Blo 1901435 87906329 := bstep (se 2 (by rfl) ⟨32964873, by rfl⟩ : syracuseStep 87906329 = 65929747) B65929747
theorem B58604219 : Blo 1901435 58604219 := bstep (se 1 (by rfl) ⟨43953164, by rfl⟩ : syracuseStep 58604219 = 87906329) B87906329
theorem B39069479 : Blo 1901435 39069479 := bstep (se 1 (by rfl) ⟨29302109, by rfl⟩ : syracuseStep 39069479 = 58604219) B58604219
theorem B104185277 : Blo 1901435 104185277 := bstep (se 3 (by rfl) ⟨19534739, by rfl⟩ : syracuseStep 104185277 = 39069479) B39069479
theorem B69456851 : Blo 1901435 69456851 := bstep (se 1 (by rfl) ⟨52092638, by rfl⟩ : syracuseStep 69456851 = 104185277) B104185277
theorem B46304567 : Blo 1901435 46304567 := bstep (se 1 (by rfl) ⟨34728425, by rfl⟩ : syracuseStep 46304567 = 69456851) B69456851
theorem B30869711 : Blo 1901435 30869711 := bstep (se 1 (by rfl) ⟨23152283, by rfl⟩ : syracuseStep 30869711 = 46304567) B46304567
theorem B20579807 : Blo 1901435 20579807 := bstep (se 1 (by rfl) ⟨15434855, by rfl⟩ : syracuseStep 20579807 = 30869711) B30869711
theorem B13719871 : Blo 1901435 13719871 := bstep (se 1 (by rfl) ⟨10289903, by rfl⟩ : syracuseStep 13719871 = 20579807) B20579807
theorem B18293161 : Blo 1901435 18293161 := bstep (se 2 (by rfl) ⟨6859935, by rfl⟩ : syracuseStep 18293161 = 13719871) B13719871
theorem B24390881 : Blo 1901435 24390881 := bstep (se 2 (by rfl) ⟨9146580, by rfl⟩ : syracuseStep 24390881 = 18293161) B18293161
theorem B16260587 : Blo 1901435 16260587 := bstep (se 1 (by rfl) ⟨12195440, by rfl⟩ : syracuseStep 16260587 = 24390881) B24390881
theorem B10840391 : Blo 1901435 10840391 := bstep (se 1 (by rfl) ⟨8130293, by rfl⟩ : syracuseStep 10840391 = 16260587) B16260587
theorem B7226927 : Blo 1901435 7226927 := bstep (se 1 (by rfl) ⟨5420195, by rfl⟩ : syracuseStep 7226927 = 10840391) B10840391
theorem B4817951 : Blo 1901435 4817951 := bstep (se 1 (by rfl) ⟨3613463, by rfl⟩ : syracuseStep 4817951 = 7226927) B7226927
theorem B3211967 : Blo 1901435 3211967 := bstep (se 1 (by rfl) ⟨2408975, by rfl⟩ : syracuseStep 3211967 = 4817951) B4817951
theorem B2141311 : Blo 1901435 2141311 := bstep (se 1 (by rfl) ⟨1605983, by rfl⟩ : syracuseStep 2141311 = 3211967) B3211967
theorem B2855081 : Blo 1901435 2855081 := bstep (se 2 (by rfl) ⟨1070655, by rfl⟩ : syracuseStep 2855081 = 2141311) B2141311
theorem B1903387 : Blo 1901435 1903387 := bstep (se 1 (by rfl) ⟨1427540, by rfl⟩ : syracuseStep 1903387 = 2855081) B2855081
theorem B6097733 : Blo 1901435 6097733 := bbase (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) (by norm_num)
theorem B4065155 : Blo 1901435 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B2710103 : Blo 1901435 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B7226941 : Blo 1901435 7226941 := bstep (se 3 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 7226941 = 2710103) B2710103
theorem B9635921 : Blo 1901435 9635921 := bstep (se 2 (by rfl) ⟨3613470, by rfl⟩ : syracuseStep 9635921 = 7226941) B7226941
theorem B6423947 : Blo 1901435 6423947 := bstep (se 1 (by rfl) ⟨4817960, by rfl⟩ : syracuseStep 6423947 = 9635921) B9635921
theorem B4282631 : Blo 1901435 4282631 := bstep (se 1 (by rfl) ⟨3211973, by rfl⟩ : syracuseStep 4282631 = 6423947) B6423947
theorem B2855087 : Blo 1901435 2855087 := bstep (se 1 (by rfl) ⟨2141315, by rfl⟩ : syracuseStep 2855087 = 4282631) B4282631
theorem B1903391 : Blo 1901435 1903391 := bstep (se 1 (by rfl) ⟨1427543, by rfl⟩ : syracuseStep 1903391 = 2855087) B2855087
theorem B2855093 : Blo 1901435 2855093 := bbase (se 5 (by rfl) ⟨133832, by rfl⟩ : syracuseStep 2855093 = 267665) (by norm_num)
theorem B1903395 : Blo 1901435 1903395 := bstep (se 1 (by rfl) ⟨1427546, by rfl⟩ : syracuseStep 1903395 = 2855093) B2855093
theorem B4817981 : Blo 1901435 4817981 := bbase (se 3 (by rfl) ⟨903371, by rfl⟩ : syracuseStep 4817981 = 1806743) (by norm_num)
theorem B3211987 : Blo 1901435 3211987 := bstep (se 1 (by rfl) ⟨2408990, by rfl⟩ : syracuseStep 3211987 = 4817981) B4817981
theorem B4282649 : Blo 1901435 4282649 := bstep (se 2 (by rfl) ⟨1605993, by rfl⟩ : syracuseStep 4282649 = 3211987) B3211987
theorem B2855099 : Blo 1901435 2855099 := bstep (se 1 (by rfl) ⟨2141324, by rfl⟩ : syracuseStep 2855099 = 4282649) B4282649
theorem B1903399 : Blo 1901435 1903399 := bstep (se 1 (by rfl) ⟨1427549, by rfl⟩ : syracuseStep 1903399 = 2855099) B2855099
theorem B2141329 : Blo 1901435 2141329 := bbase (se 2 (by rfl) ⟨802998, by rfl⟩ : syracuseStep 2141329 = 1605997) (by norm_num)
theorem B2855105 : Blo 1901435 2855105 := bstep (se 2 (by rfl) ⟨1070664, by rfl⟩ : syracuseStep 2855105 = 2141329) B2141329
theorem B1903403 : Blo 1901435 1903403 := bstep (se 1 (by rfl) ⟨1427552, by rfl⟩ : syracuseStep 1903403 = 2855105) B2855105
theorem B3613501 : Blo 1901435 3613501 := bbase (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) (by norm_num)
theorem B4818001 : Blo 1901435 4818001 := bstep (se 2 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 4818001 = 3613501) B3613501
theorem B6424001 : Blo 1901435 6424001 := bstep (se 2 (by rfl) ⟨2409000, by rfl⟩ : syracuseStep 6424001 = 4818001) B4818001
theorem B4282667 : Blo 1901435 4282667 := bstep (se 1 (by rfl) ⟨3212000, by rfl⟩ : syracuseStep 4282667 = 6424001) B6424001
theorem B2855111 : Blo 1901435 2855111 := bstep (se 1 (by rfl) ⟨2141333, by rfl⟩ : syracuseStep 2855111 = 4282667) B4282667
theorem B1903407 : Blo 1901435 1903407 := bstep (se 1 (by rfl) ⟨1427555, by rfl⟩ : syracuseStep 1903407 = 2855111) B2855111
theorem B2855117 : Blo 1901435 2855117 := bbase (se 3 (by rfl) ⟨535334, by rfl⟩ : syracuseStep 2855117 = 1070669) (by norm_num)
theorem B1903411 : Blo 1901435 1903411 := bstep (se 1 (by rfl) ⟨1427558, by rfl⟩ : syracuseStep 1903411 = 2855117) B2855117
theorem B4282685 : Blo 1901435 4282685 := bbase (se 3 (by rfl) ⟨803003, by rfl⟩ : syracuseStep 4282685 = 1606007) (by norm_num)
theorem B2855123 : Blo 1901435 2855123 := bstep (se 1 (by rfl) ⟨2141342, by rfl⟩ : syracuseStep 2855123 = 4282685) B4282685
theorem B1903415 : Blo 1901435 1903415 := bstep (se 1 (by rfl) ⟨1427561, by rfl⟩ : syracuseStep 1903415 = 2855123) B2855123
theorem B3212021 : Blo 1901435 3212021 := bbase (se 5 (by rfl) ⟨150563, by rfl⟩ : syracuseStep 3212021 = 301127) (by norm_num)
theorem B2141347 : Blo 1901435 2141347 := bstep (se 1 (by rfl) ⟨1606010, by rfl⟩ : syracuseStep 2141347 = 3212021) B3212021
theorem B2855129 : Blo 1901435 2855129 := bstep (se 2 (by rfl) ⟨1070673, by rfl⟩ : syracuseStep 2855129 = 2141347) B2141347
theorem B1903419 : Blo 1901435 1903419 := bstep (se 1 (by rfl) ⟨1427564, by rfl⟩ : syracuseStep 1903419 = 2855129) B2855129
theorem B5788181 : Blo 1901435 5788181 := bbase (se 6 (by rfl) ⟨135660, by rfl⟩ : syracuseStep 5788181 = 271321) (by norm_num)
theorem B3858787 : Blo 1901435 3858787 := bstep (se 1 (by rfl) ⟨2894090, by rfl⟩ : syracuseStep 3858787 = 5788181) B5788181
theorem B5145049 : Blo 1901435 5145049 := bstep (se 2 (by rfl) ⟨1929393, by rfl⟩ : syracuseStep 5145049 = 3858787) B3858787
theorem B6860065 : Blo 1901435 6860065 := bstep (se 2 (by rfl) ⟨2572524, by rfl⟩ : syracuseStep 6860065 = 5145049) B5145049
theorem B9146753 : Blo 1901435 9146753 := bstep (se 2 (by rfl) ⟨3430032, by rfl⟩ : syracuseStep 9146753 = 6860065) B6860065
theorem B6097835 : Blo 1901435 6097835 := bstep (se 1 (by rfl) ⟨4573376, by rfl⟩ : syracuseStep 6097835 = 9146753) B9146753
theorem B4065223 : Blo 1901435 4065223 := bstep (se 1 (by rfl) ⟨3048917, by rfl⟩ : syracuseStep 4065223 = 6097835) B6097835
theorem B5420297 : Blo 1901435 5420297 := bstep (se 2 (by rfl) ⟨2032611, by rfl⟩ : syracuseStep 5420297 = 4065223) B4065223
theorem B14454125 : Blo 1901435 14454125 := bstep (se 3 (by rfl) ⟨2710148, by rfl⟩ : syracuseStep 14454125 = 5420297) B5420297
theorem B9636083 : Blo 1901435 9636083 := bstep (se 1 (by rfl) ⟨7227062, by rfl⟩ : syracuseStep 9636083 = 14454125) B14454125
theorem B6424055 : Blo 1901435 6424055 := bstep (se 1 (by rfl) ⟨4818041, by rfl⟩ : syracuseStep 6424055 = 9636083) B9636083
theorem B4282703 : Blo 1901435 4282703 := bstep (se 1 (by rfl) ⟨3212027, by rfl⟩ : syracuseStep 4282703 = 6424055) B6424055
theorem B2855135 : Blo 1901435 2855135 := bstep (se 1 (by rfl) ⟨2141351, by rfl⟩ : syracuseStep 2855135 = 4282703) B4282703
theorem B1903423 : Blo 1901435 1903423 := bstep (se 1 (by rfl) ⟨1427567, by rfl⟩ : syracuseStep 1903423 = 2855135) B2855135
theorem B2855141 : Blo 1901435 2855141 := bbase (se 4 (by rfl) ⟨267669, by rfl⟩ : syracuseStep 2855141 = 535339) (by norm_num)
theorem B1903427 : Blo 1901435 1903427 := bstep (se 1 (by rfl) ⟨1427570, by rfl⟩ : syracuseStep 1903427 = 2855141) B2855141
theorem B4573397 : Blo 1901435 4573397 := bbase (se 7 (by rfl) ⟨53594, by rfl⟩ : syracuseStep 4573397 = 107189) (by norm_num)
theorem B3048931 : Blo 1901435 3048931 := bstep (se 1 (by rfl) ⟨2286698, by rfl⟩ : syracuseStep 3048931 = 4573397) B4573397
theorem B4065241 : Blo 1901435 4065241 := bstep (se 2 (by rfl) ⟨1524465, by rfl⟩ : syracuseStep 4065241 = 3048931) B3048931
theorem B5420321 : Blo 1901435 5420321 := bstep (se 2 (by rfl) ⟨2032620, by rfl⟩ : syracuseStep 5420321 = 4065241) B4065241
theorem B3613547 : Blo 1901435 3613547 := bstep (se 1 (by rfl) ⟨2710160, by rfl⟩ : syracuseStep 3613547 = 5420321) B5420321
theorem B2409031 : Blo 1901435 2409031 := bstep (se 1 (by rfl) ⟨1806773, by rfl⟩ : syracuseStep 2409031 = 3613547) B3613547
theorem B3212041 : Blo 1901435 3212041 := bstep (se 2 (by rfl) ⟨1204515, by rfl⟩ : syracuseStep 3212041 = 2409031) B2409031
theorem B4282721 : Blo 1901435 4282721 := bstep (se 2 (by rfl) ⟨1606020, by rfl⟩ : syracuseStep 4282721 = 3212041) B3212041
theorem B2855147 : Blo 1901435 2855147 := bstep (se 1 (by rfl) ⟨2141360, by rfl⟩ : syracuseStep 2855147 = 4282721) B4282721
theorem B1903431 : Blo 1901435 1903431 := bstep (se 1 (by rfl) ⟨1427573, by rfl⟩ : syracuseStep 1903431 = 2855147) B2855147
theorem B2141365 : Blo 1901435 2141365 := bbase (se 5 (by rfl) ⟨100376, by rfl⟩ : syracuseStep 2141365 = 200753) (by norm_num)
theorem B2855153 : Blo 1901435 2855153 := bstep (se 2 (by rfl) ⟨1070682, by rfl⟩ : syracuseStep 2855153 = 2141365) B2141365
theorem B1903435 : Blo 1901435 1903435 := bstep (se 1 (by rfl) ⟨1427576, by rfl⟩ : syracuseStep 1903435 = 2855153) B2855153
theorem C0 (j : ℕ) (h1 : 475358 ≤ j) (h2 : j ≤ 475858) : Blo 1901435 (4 * j + 3) := by
  interval_cases j
  · exact B1901435
  · exact B1901439
  · exact B1901443
  · exact B1901447
  · exact B1901451
  · exact B1901455
  · exact B1901459
  · exact B1901463
  · exact B1901467
  · exact B1901471
  · exact B1901475
  · exact B1901479
  · exact B1901483
  · exact B1901487
  · exact B1901491
  · exact B1901495
  · exact B1901499
  · exact B1901503
  · exact B1901507
  · exact B1901511
  · exact B1901515
  · exact B1901519
  · exact B1901523
  · exact B1901527
  · exact B1901531
  · exact B1901535
  · exact B1901539
  · exact B1901543
  · exact B1901547
  · exact B1901551
  · exact B1901555
  · exact B1901559
  · exact B1901563
  · exact B1901567
  · exact B1901571
  · exact B1901575
  · exact B1901579
  · exact B1901583
  · exact B1901587
  · exact B1901591
  · exact B1901595
  · exact B1901599
  · exact B1901603
  · exact B1901607
  · exact B1901611
  · exact B1901615
  · exact B1901619
  · exact B1901623
  · exact B1901627
  · exact B1901631
  · exact B1901635
  · exact B1901639
  · exact B1901643
  · exact B1901647
  · exact B1901651
  · exact B1901655
  · exact B1901659
  · exact B1901663
  · exact B1901667
  · exact B1901671
  · exact B1901675
  · exact B1901679
  · exact B1901683
  · exact B1901687
  · exact B1901691
  · exact B1901695
  · exact B1901699
  · exact B1901703
  · exact B1901707
  · exact B1901711
  · exact B1901715
  · exact B1901719
  · exact B1901723
  · exact B1901727
  · exact B1901731
  · exact B1901735
  · exact B1901739
  · exact B1901743
  · exact B1901747
  · exact B1901751
  · exact B1901755
  · exact B1901759
  · exact B1901763
  · exact B1901767
  · exact B1901771
  · exact B1901775
  · exact B1901779
  · exact B1901783
  · exact B1901787
  · exact B1901791
  · exact B1901795
  · exact B1901799
  · exact B1901803
  · exact B1901807
  · exact B1901811
  · exact B1901815
  · exact B1901819
  · exact B1901823
  · exact B1901827
  · exact B1901831
  · exact B1901835
  · exact B1901839
  · exact B1901843
  · exact B1901847
  · exact B1901851
  · exact B1901855
  · exact B1901859
  · exact B1901863
  · exact B1901867
  · exact B1901871
  · exact B1901875
  · exact B1901879
  · exact B1901883
  · exact B1901887
  · exact B1901891
  · exact B1901895
  · exact B1901899
  · exact B1901903
  · exact B1901907
  · exact B1901911
  · exact B1901915
  · exact B1901919
  · exact B1901923
  · exact B1901927
  · exact B1901931
  · exact B1901935
  · exact B1901939
  · exact B1901943
  · exact B1901947
  · exact B1901951
  · exact B1901955
  · exact B1901959
  · exact B1901963
  · exact B1901967
  · exact B1901971
  · exact B1901975
  · exact B1901979
  · exact B1901983
  · exact B1901987
  · exact B1901991
  · exact B1901995
  · exact B1901999
  · exact B1902003
  · exact B1902007
  · exact B1902011
  · exact B1902015
  · exact B1902019
  · exact B1902023
  · exact B1902027
  · exact B1902031
  · exact B1902035
  · exact B1902039
  · exact B1902043
  · exact B1902047
  · exact B1902051
  · exact B1902055
  · exact B1902059
  · exact B1902063
  · exact B1902067
  · exact B1902071
  · exact B1902075
  · exact B1902079
  · exact B1902083
  · exact B1902087
  · exact B1902091
  · exact B1902095
  · exact B1902099
  · exact B1902103
  · exact B1902107
  · exact B1902111
  · exact B1902115
  · exact B1902119
  · exact B1902123
  · exact B1902127
  · exact B1902131
  · exact B1902135
  · exact B1902139
  · exact B1902143
  · exact B1902147
  · exact B1902151
  · exact B1902155
  · exact B1902159
  · exact B1902163
  · exact B1902167
  · exact B1902171
  · exact B1902175
  · exact B1902179
  · exact B1902183
  · exact B1902187
  · exact B1902191
  · exact B1902195
  · exact B1902199
  · exact B1902203
  · exact B1902207
  · exact B1902211
  · exact B1902215
  · exact B1902219
  · exact B1902223
  · exact B1902227
  · exact B1902231
  · exact B1902235
  · exact B1902239
  · exact B1902243
  · exact B1902247
  · exact B1902251
  · exact B1902255
  · exact B1902259
  · exact B1902263
  · exact B1902267
  · exact B1902271
  · exact B1902275
  · exact B1902279
  · exact B1902283
  · exact B1902287
  · exact B1902291
  · exact B1902295
  · exact B1902299
  · exact B1902303
  · exact B1902307
  · exact B1902311
  · exact B1902315
  · exact B1902319
  · exact B1902323
  · exact B1902327
  · exact B1902331
  · exact B1902335
  · exact B1902339
  · exact B1902343
  · exact B1902347
  · exact B1902351
  · exact B1902355
  · exact B1902359
  · exact B1902363
  · exact B1902367
  · exact B1902371
  · exact B1902375
  · exact B1902379
  · exact B1902383
  · exact B1902387
  · exact B1902391
  · exact B1902395
  · exact B1902399
  · exact B1902403
  · exact B1902407
  · exact B1902411
  · exact B1902415
  · exact B1902419
  · exact B1902423
  · exact B1902427
  · exact B1902431
  · exact B1902435
  · exact B1902439
  · exact B1902443
  · exact B1902447
  · exact B1902451
  · exact B1902455
  · exact B1902459
  · exact B1902463
  · exact B1902467
  · exact B1902471
  · exact B1902475
  · exact B1902479
  · exact B1902483
  · exact B1902487
  · exact B1902491
  · exact B1902495
  · exact B1902499
  · exact B1902503
  · exact B1902507
  · exact B1902511
  · exact B1902515
  · exact B1902519
  · exact B1902523
  · exact B1902527
  · exact B1902531
  · exact B1902535
  · exact B1902539
  · exact B1902543
  · exact B1902547
  · exact B1902551
  · exact B1902555
  · exact B1902559
  · exact B1902563
  · exact B1902567
  · exact B1902571
  · exact B1902575
  · exact B1902579
  · exact B1902583
  · exact B1902587
  · exact B1902591
  · exact B1902595
  · exact B1902599
  · exact B1902603
  · exact B1902607
  · exact B1902611
  · exact B1902615
  · exact B1902619
  · exact B1902623
  · exact B1902627
  · exact B1902631
  · exact B1902635
  · exact B1902639
  · exact B1902643
  · exact B1902647
  · exact B1902651
  · exact B1902655
  · exact B1902659
  · exact B1902663
  · exact B1902667
  · exact B1902671
  · exact B1902675
  · exact B1902679
  · exact B1902683
  · exact B1902687
  · exact B1902691
  · exact B1902695
  · exact B1902699
  · exact B1902703
  · exact B1902707
  · exact B1902711
  · exact B1902715
  · exact B1902719
  · exact B1902723
  · exact B1902727
  · exact B1902731
  · exact B1902735
  · exact B1902739
  · exact B1902743
  · exact B1902747
  · exact B1902751
  · exact B1902755
  · exact B1902759
  · exact B1902763
  · exact B1902767
  · exact B1902771
  · exact B1902775
  · exact B1902779
  · exact B1902783
  · exact B1902787
  · exact B1902791
  · exact B1902795
  · exact B1902799
  · exact B1902803
  · exact B1902807
  · exact B1902811
  · exact B1902815
  · exact B1902819
  · exact B1902823
  · exact B1902827
  · exact B1902831
  · exact B1902835
  · exact B1902839
  · exact B1902843
  · exact B1902847
  · exact B1902851
  · exact B1902855
  · exact B1902859
  · exact B1902863
  · exact B1902867
  · exact B1902871
  · exact B1902875
  · exact B1902879
  · exact B1902883
  · exact B1902887
  · exact B1902891
  · exact B1902895
  · exact B1902899
  · exact B1902903
  · exact B1902907
  · exact B1902911
  · exact B1902915
  · exact B1902919
  · exact B1902923
  · exact B1902927
  · exact B1902931
  · exact B1902935
  · exact B1902939
  · exact B1902943
  · exact B1902947
  · exact B1902951
  · exact B1902955
  · exact B1902959
  · exact B1902963
  · exact B1902967
  · exact B1902971
  · exact B1902975
  · exact B1902979
  · exact B1902983
  · exact B1902987
  · exact B1902991
  · exact B1902995
  · exact B1902999
  · exact B1903003
  · exact B1903007
  · exact B1903011
  · exact B1903015
  · exact B1903019
  · exact B1903023
  · exact B1903027
  · exact B1903031
  · exact B1903035
  · exact B1903039
  · exact B1903043
  · exact B1903047
  · exact B1903051
  · exact B1903055
  · exact B1903059
  · exact B1903063
  · exact B1903067
  · exact B1903071
  · exact B1903075
  · exact B1903079
  · exact B1903083
  · exact B1903087
  · exact B1903091
  · exact B1903095
  · exact B1903099
  · exact B1903103
  · exact B1903107
  · exact B1903111
  · exact B1903115
  · exact B1903119
  · exact B1903123
  · exact B1903127
  · exact B1903131
  · exact B1903135
  · exact B1903139
  · exact B1903143
  · exact B1903147
  · exact B1903151
  · exact B1903155
  · exact B1903159
  · exact B1903163
  · exact B1903167
  · exact B1903171
  · exact B1903175
  · exact B1903179
  · exact B1903183
  · exact B1903187
  · exact B1903191
  · exact B1903195
  · exact B1903199
  · exact B1903203
  · exact B1903207
  · exact B1903211
  · exact B1903215
  · exact B1903219
  · exact B1903223
  · exact B1903227
  · exact B1903231
  · exact B1903235
  · exact B1903239
  · exact B1903243
  · exact B1903247
  · exact B1903251
  · exact B1903255
  · exact B1903259
  · exact B1903263
  · exact B1903267
  · exact B1903271
  · exact B1903275
  · exact B1903279
  · exact B1903283
  · exact B1903287
  · exact B1903291
  · exact B1903295
  · exact B1903299
  · exact B1903303
  · exact B1903307
  · exact B1903311
  · exact B1903315
  · exact B1903319
  · exact B1903323
  · exact B1903327
  · exact B1903331
  · exact B1903335
  · exact B1903339
  · exact B1903343
  · exact B1903347
  · exact B1903351
  · exact B1903355
  · exact B1903359
  · exact B1903363
  · exact B1903367
  · exact B1903371
  · exact B1903375
  · exact B1903379
  · exact B1903383
  · exact B1903387
  · exact B1903391
  · exact B1903395
  · exact B1903399
  · exact B1903403
  · exact B1903407
  · exact B1903411
  · exact B1903415
  · exact B1903419
  · exact B1903423
  · exact B1903427
  · exact B1903431
  · exact B1903435
theorem solution (m : ℕ) (hlo : 1901435 ≤ m) (hhi : m ≤ 1903435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 475358 ≤ j := by omega
    have hj2 : j ≤ 475858 := by omega
    have hb : Blo 1901435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
