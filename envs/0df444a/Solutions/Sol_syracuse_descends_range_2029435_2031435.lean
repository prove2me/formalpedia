-- Prove2me | solution 1 for syracuse_descends_range_2029435_2031435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:01.191429+00:00
-- url     : https://prove2.me/submissions/83f0fbc8-ca03-463d-b137-ff29fe735e87

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

theorem B2568505 : Blo 2029435 2568505 := bbase (se 2 (by rfl) ⟨963189, by rfl⟩ : syracuseStep 2568505 = 1926379) (by norm_num)
theorem B3424673 : Blo 2029435 3424673 := bstep (se 2 (by rfl) ⟨1284252, by rfl⟩ : syracuseStep 3424673 = 2568505) B2568505
theorem B2283115 : Blo 2029435 2283115 := bstep (se 1 (by rfl) ⟨1712336, by rfl⟩ : syracuseStep 2283115 = 3424673) B3424673
theorem B3044153 : Blo 2029435 3044153 := bstep (se 2 (by rfl) ⟨1141557, by rfl⟩ : syracuseStep 3044153 = 2283115) B2283115
theorem B2029435 : Blo 2029435 2029435 := bstep (se 1 (by rfl) ⟨1522076, by rfl⟩ : syracuseStep 2029435 = 3044153) B3044153
theorem B6501541 : Blo 2029435 6501541 := bbase (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) (by norm_num)
theorem B8668721 : Blo 2029435 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B23116589 : Blo 2029435 23116589 := bstep (se 3 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 23116589 = 8668721) B8668721
theorem B15411059 : Blo 2029435 15411059 := bstep (se 1 (by rfl) ⟨11558294, by rfl⟩ : syracuseStep 15411059 = 23116589) B23116589
theorem B10274039 : Blo 2029435 10274039 := bstep (se 1 (by rfl) ⟨7705529, by rfl⟩ : syracuseStep 10274039 = 15411059) B15411059
theorem B6849359 : Blo 2029435 6849359 := bstep (se 1 (by rfl) ⟨5137019, by rfl⟩ : syracuseStep 6849359 = 10274039) B10274039
theorem B4566239 : Blo 2029435 4566239 := bstep (se 1 (by rfl) ⟨3424679, by rfl⟩ : syracuseStep 4566239 = 6849359) B6849359
theorem B3044159 : Blo 2029435 3044159 := bstep (se 1 (by rfl) ⟨2283119, by rfl⟩ : syracuseStep 3044159 = 4566239) B4566239
theorem B2029439 : Blo 2029435 2029439 := bstep (se 1 (by rfl) ⟨1522079, by rfl⟩ : syracuseStep 2029439 = 3044159) B3044159
theorem B3044165 : Blo 2029435 3044165 := bbase (se 4 (by rfl) ⟨285390, by rfl⟩ : syracuseStep 3044165 = 570781) (by norm_num)
theorem B2029443 : Blo 2029435 2029443 := bstep (se 1 (by rfl) ⟨1522082, by rfl⟩ : syracuseStep 2029443 = 3044165) B3044165
theorem B3424693 : Blo 2029435 3424693 := bbase (se 5 (by rfl) ⟨160532, by rfl⟩ : syracuseStep 3424693 = 321065) (by norm_num)
theorem B4566257 : Blo 2029435 4566257 := bstep (se 2 (by rfl) ⟨1712346, by rfl⟩ : syracuseStep 4566257 = 3424693) B3424693
theorem B3044171 : Blo 2029435 3044171 := bstep (se 1 (by rfl) ⟨2283128, by rfl⟩ : syracuseStep 3044171 = 4566257) B4566257
theorem B2029447 : Blo 2029435 2029447 := bstep (se 1 (by rfl) ⟨1522085, by rfl⟩ : syracuseStep 2029447 = 3044171) B3044171
theorem B2283133 : Blo 2029435 2283133 := bbase (se 3 (by rfl) ⟨428087, by rfl⟩ : syracuseStep 2283133 = 856175) (by norm_num)
theorem B3044177 : Blo 2029435 3044177 := bstep (se 2 (by rfl) ⟨1141566, by rfl⟩ : syracuseStep 3044177 = 2283133) B2283133
theorem B2029451 : Blo 2029435 2029451 := bstep (se 1 (by rfl) ⟨1522088, by rfl⟩ : syracuseStep 2029451 = 3044177) B3044177
theorem B6849413 : Blo 2029435 6849413 := bbase (se 4 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 6849413 = 1284265) (by norm_num)
theorem B4566275 : Blo 2029435 4566275 := bstep (se 1 (by rfl) ⟨3424706, by rfl⟩ : syracuseStep 4566275 = 6849413) B6849413
theorem B3044183 : Blo 2029435 3044183 := bstep (se 1 (by rfl) ⟨2283137, by rfl⟩ : syracuseStep 3044183 = 4566275) B4566275
theorem B2029455 : Blo 2029435 2029455 := bstep (se 1 (by rfl) ⟨1522091, by rfl⟩ : syracuseStep 2029455 = 3044183) B3044183
theorem B3044189 : Blo 2029435 3044189 := bbase (se 3 (by rfl) ⟨570785, by rfl⟩ : syracuseStep 3044189 = 1141571) (by norm_num)
theorem B2029459 : Blo 2029435 2029459 := bstep (se 1 (by rfl) ⟨1522094, by rfl⟩ : syracuseStep 2029459 = 3044189) B3044189
theorem B4566293 : Blo 2029435 4566293 := bbase (se 6 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 4566293 = 214045) (by norm_num)
theorem B3044195 : Blo 2029435 3044195 := bstep (se 1 (by rfl) ⟨2283146, by rfl⟩ : syracuseStep 3044195 = 4566293) B4566293
theorem B2029463 : Blo 2029435 2029463 := bstep (se 1 (by rfl) ⟨1522097, by rfl⟩ : syracuseStep 2029463 = 3044195) B3044195
theorem B7705637 : Blo 2029435 7705637 := bbase (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) (by norm_num)
theorem B5137091 : Blo 2029435 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B3424727 : Blo 2029435 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B2283151 : Blo 2029435 2283151 := bstep (se 1 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 2283151 = 3424727) B3424727
theorem B3044201 : Blo 2029435 3044201 := bstep (se 2 (by rfl) ⟨1141575, by rfl⟩ : syracuseStep 3044201 = 2283151) B2283151
theorem B2029467 : Blo 2029435 2029467 := bstep (se 1 (by rfl) ⟨1522100, by rfl⟩ : syracuseStep 2029467 = 3044201) B3044201
theorem B4334429 : Blo 2029435 4334429 := bbase (se 3 (by rfl) ⟨812705, by rfl⟩ : syracuseStep 4334429 = 1625411) (by norm_num)
theorem B11558477 : Blo 2029435 11558477 := bstep (se 3 (by rfl) ⟨2167214, by rfl⟩ : syracuseStep 11558477 = 4334429) B4334429
theorem B7705651 : Blo 2029435 7705651 := bstep (se 1 (by rfl) ⟨5779238, by rfl⟩ : syracuseStep 7705651 = 11558477) B11558477
theorem B10274201 : Blo 2029435 10274201 := bstep (se 2 (by rfl) ⟨3852825, by rfl⟩ : syracuseStep 10274201 = 7705651) B7705651
theorem B6849467 : Blo 2029435 6849467 := bstep (se 1 (by rfl) ⟨5137100, by rfl⟩ : syracuseStep 6849467 = 10274201) B10274201
theorem B4566311 : Blo 2029435 4566311 := bstep (se 1 (by rfl) ⟨3424733, by rfl⟩ : syracuseStep 4566311 = 6849467) B6849467
theorem B3044207 : Blo 2029435 3044207 := bstep (se 1 (by rfl) ⟨2283155, by rfl⟩ : syracuseStep 3044207 = 4566311) B4566311
theorem B2029471 : Blo 2029435 2029471 := bstep (se 1 (by rfl) ⟨1522103, by rfl⟩ : syracuseStep 2029471 = 3044207) B3044207
theorem B3044213 : Blo 2029435 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B2029475 : Blo 2029435 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B6171509 : Blo 2029435 6171509 := bbase (se 5 (by rfl) ⟨289289, by rfl⟩ : syracuseStep 6171509 = 578579) (by norm_num)
theorem B16457357 : Blo 2029435 16457357 := bstep (se 3 (by rfl) ⟨3085754, by rfl⟩ : syracuseStep 16457357 = 6171509) B6171509
theorem B10971571 : Blo 2029435 10971571 := bstep (se 1 (by rfl) ⟨8228678, by rfl⟩ : syracuseStep 10971571 = 16457357) B16457357
theorem B14628761 : Blo 2029435 14628761 := bstep (se 2 (by rfl) ⟨5485785, by rfl⟩ : syracuseStep 14628761 = 10971571) B10971571
theorem B9752507 : Blo 2029435 9752507 := bstep (se 1 (by rfl) ⟨7314380, by rfl⟩ : syracuseStep 9752507 = 14628761) B14628761
theorem B6501671 : Blo 2029435 6501671 := bstep (se 1 (by rfl) ⟨4876253, by rfl⟩ : syracuseStep 6501671 = 9752507) B9752507
theorem B4334447 : Blo 2029435 4334447 := bstep (se 1 (by rfl) ⟨3250835, by rfl⟩ : syracuseStep 4334447 = 6501671) B6501671
theorem B2889631 : Blo 2029435 2889631 := bstep (se 1 (by rfl) ⟨2167223, by rfl⟩ : syracuseStep 2889631 = 4334447) B4334447
theorem B3852841 : Blo 2029435 3852841 := bstep (se 2 (by rfl) ⟨1444815, by rfl⟩ : syracuseStep 3852841 = 2889631) B2889631
theorem B5137121 : Blo 2029435 5137121 := bstep (se 2 (by rfl) ⟨1926420, by rfl⟩ : syracuseStep 5137121 = 3852841) B3852841
theorem B3424747 : Blo 2029435 3424747 := bstep (se 1 (by rfl) ⟨2568560, by rfl⟩ : syracuseStep 3424747 = 5137121) B5137121
theorem B4566329 : Blo 2029435 4566329 := bstep (se 2 (by rfl) ⟨1712373, by rfl⟩ : syracuseStep 4566329 = 3424747) B3424747
theorem B3044219 : Blo 2029435 3044219 := bstep (se 1 (by rfl) ⟨2283164, by rfl⟩ : syracuseStep 3044219 = 4566329) B4566329
theorem B2029479 : Blo 2029435 2029479 := bstep (se 1 (by rfl) ⟨1522109, by rfl⟩ : syracuseStep 2029479 = 3044219) B3044219
theorem B2283169 : Blo 2029435 2283169 := bbase (se 2 (by rfl) ⟨856188, by rfl⟩ : syracuseStep 2283169 = 1712377) (by norm_num)
theorem B3044225 : Blo 2029435 3044225 := bstep (se 2 (by rfl) ⟨1141584, by rfl⟩ : syracuseStep 3044225 = 2283169) B2283169
theorem B2029483 : Blo 2029435 2029483 := bstep (se 1 (by rfl) ⟨1522112, by rfl⟩ : syracuseStep 2029483 = 3044225) B3044225
theorem B5137141 : Blo 2029435 5137141 := bbase (se 5 (by rfl) ⟨240803, by rfl⟩ : syracuseStep 5137141 = 481607) (by norm_num)
theorem B6849521 : Blo 2029435 6849521 := bstep (se 2 (by rfl) ⟨2568570, by rfl⟩ : syracuseStep 6849521 = 5137141) B5137141
theorem B4566347 : Blo 2029435 4566347 := bstep (se 1 (by rfl) ⟨3424760, by rfl⟩ : syracuseStep 4566347 = 6849521) B6849521
theorem B3044231 : Blo 2029435 3044231 := bstep (se 1 (by rfl) ⟨2283173, by rfl⟩ : syracuseStep 3044231 = 4566347) B4566347
theorem B2029487 : Blo 2029435 2029487 := bstep (se 1 (by rfl) ⟨1522115, by rfl⟩ : syracuseStep 2029487 = 3044231) B3044231
theorem B3044237 : Blo 2029435 3044237 := bbase (se 3 (by rfl) ⟨570794, by rfl⟩ : syracuseStep 3044237 = 1141589) (by norm_num)
theorem B2029491 : Blo 2029435 2029491 := bstep (se 1 (by rfl) ⟨1522118, by rfl⟩ : syracuseStep 2029491 = 3044237) B3044237
theorem B4566365 : Blo 2029435 4566365 := bbase (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) (by norm_num)
theorem B3044243 : Blo 2029435 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B2029495 : Blo 2029435 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B3424781 : Blo 2029435 3424781 := bbase (se 3 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 3424781 = 1284293) (by norm_num)
theorem B2283187 : Blo 2029435 2283187 := bstep (se 1 (by rfl) ⟨1712390, by rfl⟩ : syracuseStep 2283187 = 3424781) B3424781
theorem B3044249 : Blo 2029435 3044249 := bstep (se 2 (by rfl) ⟨1141593, by rfl⟩ : syracuseStep 3044249 = 2283187) B2283187
theorem B2029499 : Blo 2029435 2029499 := bstep (se 1 (by rfl) ⟨1522124, by rfl⟩ : syracuseStep 2029499 = 3044249) B3044249
theorem B2742925 : Blo 2029435 2742925 := bbase (se 3 (by rfl) ⟨514298, by rfl⟩ : syracuseStep 2742925 = 1028597) (by norm_num)
theorem B3657233 : Blo 2029435 3657233 := bstep (se 2 (by rfl) ⟨1371462, by rfl⟩ : syracuseStep 3657233 = 2742925) B2742925
theorem B2438155 : Blo 2029435 2438155 := bstep (se 1 (by rfl) ⟨1828616, by rfl⟩ : syracuseStep 2438155 = 3657233) B3657233
theorem B3250873 : Blo 2029435 3250873 := bstep (se 2 (by rfl) ⟨1219077, by rfl⟩ : syracuseStep 3250873 = 2438155) B2438155
theorem B17337989 : Blo 2029435 17337989 := bstep (se 4 (by rfl) ⟨1625436, by rfl⟩ : syracuseStep 17337989 = 3250873) B3250873
theorem B11558659 : Blo 2029435 11558659 := bstep (se 1 (by rfl) ⟨8668994, by rfl⟩ : syracuseStep 11558659 = 17337989) B17337989
theorem B15411545 : Blo 2029435 15411545 := bstep (se 2 (by rfl) ⟨5779329, by rfl⟩ : syracuseStep 15411545 = 11558659) B11558659
theorem B10274363 : Blo 2029435 10274363 := bstep (se 1 (by rfl) ⟨7705772, by rfl⟩ : syracuseStep 10274363 = 15411545) B15411545
theorem B6849575 : Blo 2029435 6849575 := bstep (se 1 (by rfl) ⟨5137181, by rfl⟩ : syracuseStep 6849575 = 10274363) B10274363
theorem B4566383 : Blo 2029435 4566383 := bstep (se 1 (by rfl) ⟨3424787, by rfl⟩ : syracuseStep 4566383 = 6849575) B6849575
theorem B3044255 : Blo 2029435 3044255 := bstep (se 1 (by rfl) ⟨2283191, by rfl⟩ : syracuseStep 3044255 = 4566383) B4566383
theorem B2029503 : Blo 2029435 2029503 := bstep (se 1 (by rfl) ⟨1522127, by rfl⟩ : syracuseStep 2029503 = 3044255) B3044255
theorem B3044261 : Blo 2029435 3044261 := bbase (se 4 (by rfl) ⟨285399, by rfl⟩ : syracuseStep 3044261 = 570799) (by norm_num)
theorem B2029507 : Blo 2029435 2029507 := bstep (se 1 (by rfl) ⟨1522130, by rfl⟩ : syracuseStep 2029507 = 3044261) B3044261
theorem B2568601 : Blo 2029435 2568601 := bbase (se 2 (by rfl) ⟨963225, by rfl⟩ : syracuseStep 2568601 = 1926451) (by norm_num)
theorem B3424801 : Blo 2029435 3424801 := bstep (se 2 (by rfl) ⟨1284300, by rfl⟩ : syracuseStep 3424801 = 2568601) B2568601
theorem B4566401 : Blo 2029435 4566401 := bstep (se 2 (by rfl) ⟨1712400, by rfl⟩ : syracuseStep 4566401 = 3424801) B3424801
theorem B3044267 : Blo 2029435 3044267 := bstep (se 1 (by rfl) ⟨2283200, by rfl⟩ : syracuseStep 3044267 = 4566401) B4566401
theorem B2029511 : Blo 2029435 2029511 := bstep (se 1 (by rfl) ⟨1522133, by rfl⟩ : syracuseStep 2029511 = 3044267) B3044267
theorem B2283205 : Blo 2029435 2283205 := bbase (se 4 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 2283205 = 428101) (by norm_num)
theorem B3044273 : Blo 2029435 3044273 := bstep (se 2 (by rfl) ⟨1141602, by rfl⟩ : syracuseStep 3044273 = 2283205) B2283205
theorem B2029515 : Blo 2029435 2029515 := bstep (se 1 (by rfl) ⟨1522136, by rfl⟩ : syracuseStep 2029515 = 3044273) B3044273
theorem B3852917 : Blo 2029435 3852917 := bbase (se 5 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 3852917 = 361211) (by norm_num)
theorem B2568611 : Blo 2029435 2568611 := bstep (se 1 (by rfl) ⟨1926458, by rfl⟩ : syracuseStep 2568611 = 3852917) B3852917
theorem B6849629 : Blo 2029435 6849629 := bstep (se 3 (by rfl) ⟨1284305, by rfl⟩ : syracuseStep 6849629 = 2568611) B2568611
theorem B4566419 : Blo 2029435 4566419 := bstep (se 1 (by rfl) ⟨3424814, by rfl⟩ : syracuseStep 4566419 = 6849629) B6849629
theorem B3044279 : Blo 2029435 3044279 := bstep (se 1 (by rfl) ⟨2283209, by rfl⟩ : syracuseStep 3044279 = 4566419) B4566419
theorem B2029519 : Blo 2029435 2029519 := bstep (se 1 (by rfl) ⟨1522139, by rfl⟩ : syracuseStep 2029519 = 3044279) B3044279
theorem B3044285 : Blo 2029435 3044285 := bbase (se 3 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 3044285 = 1141607) (by norm_num)
theorem B2029523 : Blo 2029435 2029523 := bstep (se 1 (by rfl) ⟨1522142, by rfl⟩ : syracuseStep 2029523 = 3044285) B3044285
theorem B4566437 : Blo 2029435 4566437 := bbase (se 4 (by rfl) ⟨428103, by rfl⟩ : syracuseStep 4566437 = 856207) (by norm_num)
theorem B3044291 : Blo 2029435 3044291 := bstep (se 1 (by rfl) ⟨2283218, by rfl⟩ : syracuseStep 3044291 = 4566437) B4566437
theorem B2029527 : Blo 2029435 2029527 := bstep (se 1 (by rfl) ⟨1522145, by rfl⟩ : syracuseStep 2029527 = 3044291) B3044291
theorem B5137253 : Blo 2029435 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B3424835 : Blo 2029435 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B2283223 : Blo 2029435 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B3044297 : Blo 2029435 3044297 := bstep (se 2 (by rfl) ⟨1141611, by rfl⟩ : syracuseStep 3044297 = 2283223) B2283223
theorem B2029531 : Blo 2029435 2029531 := bstep (se 1 (by rfl) ⟨1522148, by rfl⟩ : syracuseStep 2029531 = 3044297) B3044297
theorem B3250925 : Blo 2029435 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B2167283 : Blo 2029435 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B5779421 : Blo 2029435 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B3852947 : Blo 2029435 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B10274525 : Blo 2029435 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B6849683 : Blo 2029435 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B4566455 : Blo 2029435 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B3044303 : Blo 2029435 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B2029535 : Blo 2029435 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B3044309 : Blo 2029435 3044309 := bbase (se 7 (by rfl) ⟨35675, by rfl⟩ : syracuseStep 3044309 = 71351) (by norm_num)
theorem B2029539 : Blo 2029435 2029539 := bstep (se 1 (by rfl) ⟨1522154, by rfl⟩ : syracuseStep 2029539 = 3044309) B3044309
theorem B7705925 : Blo 2029435 7705925 := bbase (se 4 (by rfl) ⟨722430, by rfl⟩ : syracuseStep 7705925 = 1444861) (by norm_num)
theorem B5137283 : Blo 2029435 5137283 := bstep (se 1 (by rfl) ⟨3852962, by rfl⟩ : syracuseStep 5137283 = 7705925) B7705925
theorem B3424855 : Blo 2029435 3424855 := bstep (se 1 (by rfl) ⟨2568641, by rfl⟩ : syracuseStep 3424855 = 5137283) B5137283
theorem B4566473 : Blo 2029435 4566473 := bstep (se 2 (by rfl) ⟨1712427, by rfl⟩ : syracuseStep 4566473 = 3424855) B3424855
theorem B3044315 : Blo 2029435 3044315 := bstep (se 1 (by rfl) ⟨2283236, by rfl⟩ : syracuseStep 3044315 = 4566473) B4566473
theorem B2029543 : Blo 2029435 2029543 := bstep (se 1 (by rfl) ⟨1522157, by rfl⟩ : syracuseStep 2029543 = 3044315) B3044315
theorem B2283241 : Blo 2029435 2283241 := bbase (se 2 (by rfl) ⟨856215, by rfl⟩ : syracuseStep 2283241 = 1712431) (by norm_num)
theorem B3044321 : Blo 2029435 3044321 := bstep (se 2 (by rfl) ⟨1141620, by rfl⟩ : syracuseStep 3044321 = 2283241) B2283241
theorem B2029547 : Blo 2029435 2029547 := bstep (se 1 (by rfl) ⟨1522160, by rfl⟩ : syracuseStep 2029547 = 3044321) B3044321
theorem B11558933 : Blo 2029435 11558933 := bbase (se 6 (by rfl) ⟨270912, by rfl⟩ : syracuseStep 11558933 = 541825) (by norm_num)
theorem B7705955 : Blo 2029435 7705955 := bstep (se 1 (by rfl) ⟨5779466, by rfl⟩ : syracuseStep 7705955 = 11558933) B11558933
theorem B5137303 : Blo 2029435 5137303 := bstep (se 1 (by rfl) ⟨3852977, by rfl⟩ : syracuseStep 5137303 = 7705955) B7705955
theorem B6849737 : Blo 2029435 6849737 := bstep (se 2 (by rfl) ⟨2568651, by rfl⟩ : syracuseStep 6849737 = 5137303) B5137303
theorem B4566491 : Blo 2029435 4566491 := bstep (se 1 (by rfl) ⟨3424868, by rfl⟩ : syracuseStep 4566491 = 6849737) B6849737
theorem B3044327 : Blo 2029435 3044327 := bstep (se 1 (by rfl) ⟨2283245, by rfl⟩ : syracuseStep 3044327 = 4566491) B4566491
theorem B2029551 : Blo 2029435 2029551 := bstep (se 1 (by rfl) ⟨1522163, by rfl⟩ : syracuseStep 2029551 = 3044327) B3044327
theorem B3044333 : Blo 2029435 3044333 := bbase (se 3 (by rfl) ⟨570812, by rfl⟩ : syracuseStep 3044333 = 1141625) (by norm_num)
theorem B2029555 : Blo 2029435 2029555 := bstep (se 1 (by rfl) ⟨1522166, by rfl⟩ : syracuseStep 2029555 = 3044333) B3044333
theorem B4566509 : Blo 2029435 4566509 := bbase (se 3 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 4566509 = 1712441) (by norm_num)
theorem B3044339 : Blo 2029435 3044339 := bstep (se 1 (by rfl) ⟨2283254, by rfl⟩ : syracuseStep 3044339 = 4566509) B4566509
theorem B2029559 : Blo 2029435 2029559 := bstep (se 1 (by rfl) ⟨1522169, by rfl⟩ : syracuseStep 2029559 = 3044339) B3044339
theorem B6501941 : Blo 2029435 6501941 := bbase (se 5 (by rfl) ⟨304778, by rfl⟩ : syracuseStep 6501941 = 609557) (by norm_num)
theorem B4334627 : Blo 2029435 4334627 := bstep (se 1 (by rfl) ⟨3250970, by rfl⟩ : syracuseStep 4334627 = 6501941) B6501941
theorem B2889751 : Blo 2029435 2889751 := bstep (se 1 (by rfl) ⟨2167313, by rfl⟩ : syracuseStep 2889751 = 4334627) B4334627
theorem B3853001 : Blo 2029435 3853001 := bstep (se 2 (by rfl) ⟨1444875, by rfl⟩ : syracuseStep 3853001 = 2889751) B2889751
theorem B2568667 : Blo 2029435 2568667 := bstep (se 1 (by rfl) ⟨1926500, by rfl⟩ : syracuseStep 2568667 = 3853001) B3853001
theorem B3424889 : Blo 2029435 3424889 := bstep (se 2 (by rfl) ⟨1284333, by rfl⟩ : syracuseStep 3424889 = 2568667) B2568667
theorem B2283259 : Blo 2029435 2283259 := bstep (se 1 (by rfl) ⟨1712444, by rfl⟩ : syracuseStep 2283259 = 3424889) B3424889
theorem B3044345 : Blo 2029435 3044345 := bstep (se 2 (by rfl) ⟨1141629, by rfl⟩ : syracuseStep 3044345 = 2283259) B2283259
theorem B2029563 : Blo 2029435 2029563 := bstep (se 1 (by rfl) ⟨1522172, by rfl⟩ : syracuseStep 2029563 = 3044345) B3044345
theorem B15835445 : Blo 2029435 15835445 := bbase (se 5 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 15835445 = 1484573) (by norm_num)
theorem B10556963 : Blo 2029435 10556963 := bstep (se 1 (by rfl) ⟨7917722, by rfl⟩ : syracuseStep 10556963 = 15835445) B15835445
theorem B7037975 : Blo 2029435 7037975 := bstep (se 1 (by rfl) ⟨5278481, by rfl⟩ : syracuseStep 7037975 = 10556963) B10556963
theorem B18767933 : Blo 2029435 18767933 := bstep (se 3 (by rfl) ⟨3518987, by rfl⟩ : syracuseStep 18767933 = 7037975) B7037975
theorem B12511955 : Blo 2029435 12511955 := bstep (se 1 (by rfl) ⟨9383966, by rfl⟩ : syracuseStep 12511955 = 18767933) B18767933
theorem B33365213 : Blo 2029435 33365213 := bstep (se 3 (by rfl) ⟨6255977, by rfl⟩ : syracuseStep 33365213 = 12511955) B12511955
theorem B22243475 : Blo 2029435 22243475 := bstep (se 1 (by rfl) ⟨16682606, by rfl⟩ : syracuseStep 22243475 = 33365213) B33365213
theorem B14828983 : Blo 2029435 14828983 := bstep (se 1 (by rfl) ⟨11121737, by rfl⟩ : syracuseStep 14828983 = 22243475) B22243475
theorem B79087909 : Blo 2029435 79087909 := bstep (se 4 (by rfl) ⟨7414491, by rfl⟩ : syracuseStep 79087909 = 14828983) B14828983
theorem B105450545 : Blo 2029435 105450545 := bstep (se 2 (by rfl) ⟨39543954, by rfl⟩ : syracuseStep 105450545 = 79087909) B79087909
theorem B281201453 : Blo 2029435 281201453 := bstep (se 3 (by rfl) ⟨52725272, by rfl⟩ : syracuseStep 281201453 = 105450545) B105450545
theorem B187467635 : Blo 2029435 187467635 := bstep (se 1 (by rfl) ⟨140600726, by rfl⟩ : syracuseStep 187467635 = 281201453) B281201453
theorem B124978423 : Blo 2029435 124978423 := bstep (se 1 (by rfl) ⟨93733817, by rfl⟩ : syracuseStep 124978423 = 187467635) B187467635
theorem B166637897 : Blo 2029435 166637897 := bstep (se 2 (by rfl) ⟨62489211, by rfl⟩ : syracuseStep 166637897 = 124978423) B124978423
theorem B111091931 : Blo 2029435 111091931 := bstep (se 1 (by rfl) ⟨83318948, by rfl⟩ : syracuseStep 111091931 = 166637897) B166637897
theorem B74061287 : Blo 2029435 74061287 := bstep (se 1 (by rfl) ⟨55545965, by rfl⟩ : syracuseStep 74061287 = 111091931) B111091931
theorem B49374191 : Blo 2029435 49374191 := bstep (se 1 (by rfl) ⟨37030643, by rfl⟩ : syracuseStep 49374191 = 74061287) B74061287
theorem B32916127 : Blo 2029435 32916127 := bstep (se 1 (by rfl) ⟨24687095, by rfl⟩ : syracuseStep 32916127 = 49374191) B49374191
theorem B43888169 : Blo 2029435 43888169 := bstep (se 2 (by rfl) ⟨16458063, by rfl⟩ : syracuseStep 43888169 = 32916127) B32916127
theorem B117035117 : Blo 2029435 117035117 := bstep (se 3 (by rfl) ⟨21944084, by rfl⟩ : syracuseStep 117035117 = 43888169) B43888169
theorem B78023411 : Blo 2029435 78023411 := bstep (se 1 (by rfl) ⟨58517558, by rfl⟩ : syracuseStep 78023411 = 117035117) B117035117
theorem B52015607 : Blo 2029435 52015607 := bstep (se 1 (by rfl) ⟨39011705, by rfl⟩ : syracuseStep 52015607 = 78023411) B78023411
theorem B34677071 : Blo 2029435 34677071 := bstep (se 1 (by rfl) ⟨26007803, by rfl⟩ : syracuseStep 34677071 = 52015607) B52015607
theorem B23118047 : Blo 2029435 23118047 := bstep (se 1 (by rfl) ⟨17338535, by rfl⟩ : syracuseStep 23118047 = 34677071) B34677071
theorem B15412031 : Blo 2029435 15412031 := bstep (se 1 (by rfl) ⟨11559023, by rfl⟩ : syracuseStep 15412031 = 23118047) B23118047
theorem B10274687 : Blo 2029435 10274687 := bstep (se 1 (by rfl) ⟨7706015, by rfl⟩ : syracuseStep 10274687 = 15412031) B15412031
theorem B6849791 : Blo 2029435 6849791 := bstep (se 1 (by rfl) ⟨5137343, by rfl⟩ : syracuseStep 6849791 = 10274687) B10274687
theorem B4566527 : Blo 2029435 4566527 := bstep (se 1 (by rfl) ⟨3424895, by rfl⟩ : syracuseStep 4566527 = 6849791) B6849791
theorem B3044351 : Blo 2029435 3044351 := bstep (se 1 (by rfl) ⟨2283263, by rfl⟩ : syracuseStep 3044351 = 4566527) B4566527
theorem B2029567 : Blo 2029435 2029567 := bstep (se 1 (by rfl) ⟨1522175, by rfl⟩ : syracuseStep 2029567 = 3044351) B3044351
theorem B3044357 : Blo 2029435 3044357 := bbase (se 4 (by rfl) ⟨285408, by rfl⟩ : syracuseStep 3044357 = 570817) (by norm_num)
theorem B2029571 : Blo 2029435 2029571 := bstep (se 1 (by rfl) ⟨1522178, by rfl⟩ : syracuseStep 2029571 = 3044357) B3044357
theorem B3424909 : Blo 2029435 3424909 := bbase (se 3 (by rfl) ⟨642170, by rfl⟩ : syracuseStep 3424909 = 1284341) (by norm_num)
theorem B4566545 : Blo 2029435 4566545 := bstep (se 2 (by rfl) ⟨1712454, by rfl⟩ : syracuseStep 4566545 = 3424909) B3424909
theorem B3044363 : Blo 2029435 3044363 := bstep (se 1 (by rfl) ⟨2283272, by rfl⟩ : syracuseStep 3044363 = 4566545) B4566545
theorem B2029575 : Blo 2029435 2029575 := bstep (se 1 (by rfl) ⟨1522181, by rfl⟩ : syracuseStep 2029575 = 3044363) B3044363
theorem B2283277 : Blo 2029435 2283277 := bbase (se 3 (by rfl) ⟨428114, by rfl⟩ : syracuseStep 2283277 = 856229) (by norm_num)
theorem B3044369 : Blo 2029435 3044369 := bstep (se 2 (by rfl) ⟨1141638, by rfl⟩ : syracuseStep 3044369 = 2283277) B2283277
theorem B2029579 : Blo 2029435 2029579 := bstep (se 1 (by rfl) ⟨1522184, by rfl⟩ : syracuseStep 2029579 = 3044369) B3044369
theorem B6849845 : Blo 2029435 6849845 := bbase (se 5 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 6849845 = 642173) (by norm_num)
theorem B4566563 : Blo 2029435 4566563 := bstep (se 1 (by rfl) ⟨3424922, by rfl⟩ : syracuseStep 4566563 = 6849845) B6849845
theorem B3044375 : Blo 2029435 3044375 := bstep (se 1 (by rfl) ⟨2283281, by rfl⟩ : syracuseStep 3044375 = 4566563) B4566563
theorem B2029583 : Blo 2029435 2029583 := bstep (se 1 (by rfl) ⟨1522187, by rfl⟩ : syracuseStep 2029583 = 3044375) B3044375
theorem B3044381 : Blo 2029435 3044381 := bbase (se 3 (by rfl) ⟨570821, by rfl⟩ : syracuseStep 3044381 = 1141643) (by norm_num)
theorem B2029587 : Blo 2029435 2029587 := bstep (se 1 (by rfl) ⟨1522190, by rfl⟩ : syracuseStep 2029587 = 3044381) B3044381
theorem B4566581 : Blo 2029435 4566581 := bbase (se 5 (by rfl) ⟨214058, by rfl⟩ : syracuseStep 4566581 = 428117) (by norm_num)
theorem B3044387 : Blo 2029435 3044387 := bstep (se 1 (by rfl) ⟨2283290, by rfl⟩ : syracuseStep 3044387 = 4566581) B4566581
theorem B2029591 : Blo 2029435 2029591 := bstep (se 1 (by rfl) ⟨1522193, by rfl⟩ : syracuseStep 2029591 = 3044387) B3044387
theorem B3251021 : Blo 2029435 3251021 := bbase (se 3 (by rfl) ⟨609566, by rfl⟩ : syracuseStep 3251021 = 1219133) (by norm_num)
theorem B8669389 : Blo 2029435 8669389 := bstep (se 3 (by rfl) ⟨1625510, by rfl⟩ : syracuseStep 8669389 = 3251021) B3251021
theorem B11559185 : Blo 2029435 11559185 := bstep (se 2 (by rfl) ⟨4334694, by rfl⟩ : syracuseStep 11559185 = 8669389) B8669389
theorem B7706123 : Blo 2029435 7706123 := bstep (se 1 (by rfl) ⟨5779592, by rfl⟩ : syracuseStep 7706123 = 11559185) B11559185
theorem B5137415 : Blo 2029435 5137415 := bstep (se 1 (by rfl) ⟨3853061, by rfl⟩ : syracuseStep 5137415 = 7706123) B7706123
theorem B3424943 : Blo 2029435 3424943 := bstep (se 1 (by rfl) ⟨2568707, by rfl⟩ : syracuseStep 3424943 = 5137415) B5137415
theorem B2283295 : Blo 2029435 2283295 := bstep (se 1 (by rfl) ⟨1712471, by rfl⟩ : syracuseStep 2283295 = 3424943) B3424943
theorem B3044393 : Blo 2029435 3044393 := bstep (se 2 (by rfl) ⟨1141647, by rfl⟩ : syracuseStep 3044393 = 2283295) B2283295
theorem B2029595 : Blo 2029435 2029595 := bstep (se 1 (by rfl) ⟨1522196, by rfl⟩ : syracuseStep 2029595 = 3044393) B3044393
theorem B4876541 : Blo 2029435 4876541 := bbase (se 3 (by rfl) ⟨914351, by rfl⟩ : syracuseStep 4876541 = 1828703) (by norm_num)
theorem B3251027 : Blo 2029435 3251027 := bstep (se 1 (by rfl) ⟨2438270, by rfl⟩ : syracuseStep 3251027 = 4876541) B4876541
theorem B8669405 : Blo 2029435 8669405 := bstep (se 3 (by rfl) ⟨1625513, by rfl⟩ : syracuseStep 8669405 = 3251027) B3251027
theorem B5779603 : Blo 2029435 5779603 := bstep (se 1 (by rfl) ⟨4334702, by rfl⟩ : syracuseStep 5779603 = 8669405) B8669405
theorem B7706137 : Blo 2029435 7706137 := bstep (se 2 (by rfl) ⟨2889801, by rfl⟩ : syracuseStep 7706137 = 5779603) B5779603
theorem B10274849 : Blo 2029435 10274849 := bstep (se 2 (by rfl) ⟨3853068, by rfl⟩ : syracuseStep 10274849 = 7706137) B7706137
theorem B6849899 : Blo 2029435 6849899 := bstep (se 1 (by rfl) ⟨5137424, by rfl⟩ : syracuseStep 6849899 = 10274849) B10274849
theorem B4566599 : Blo 2029435 4566599 := bstep (se 1 (by rfl) ⟨3424949, by rfl⟩ : syracuseStep 4566599 = 6849899) B6849899
theorem B3044399 : Blo 2029435 3044399 := bstep (se 1 (by rfl) ⟨2283299, by rfl⟩ : syracuseStep 3044399 = 4566599) B4566599
theorem B2029599 : Blo 2029435 2029599 := bstep (se 1 (by rfl) ⟨1522199, by rfl⟩ : syracuseStep 2029599 = 3044399) B3044399
theorem B3044405 : Blo 2029435 3044405 := bbase (se 5 (by rfl) ⟨142706, by rfl⟩ : syracuseStep 3044405 = 285413) (by norm_num)
theorem B2029603 : Blo 2029435 2029603 := bstep (se 1 (by rfl) ⟨1522202, by rfl⟩ : syracuseStep 2029603 = 3044405) B3044405
theorem B5137445 : Blo 2029435 5137445 := bbase (se 4 (by rfl) ⟨481635, by rfl⟩ : syracuseStep 5137445 = 963271) (by norm_num)
theorem B3424963 : Blo 2029435 3424963 := bstep (se 1 (by rfl) ⟨2568722, by rfl⟩ : syracuseStep 3424963 = 5137445) B5137445
theorem B4566617 : Blo 2029435 4566617 := bstep (se 2 (by rfl) ⟨1712481, by rfl⟩ : syracuseStep 4566617 = 3424963) B3424963
theorem B3044411 : Blo 2029435 3044411 := bstep (se 1 (by rfl) ⟨2283308, by rfl⟩ : syracuseStep 3044411 = 4566617) B4566617
theorem B2029607 : Blo 2029435 2029607 := bstep (se 1 (by rfl) ⟨1522205, by rfl⟩ : syracuseStep 2029607 = 3044411) B3044411
theorem B2283313 : Blo 2029435 2283313 := bbase (se 2 (by rfl) ⟨856242, by rfl⟩ : syracuseStep 2283313 = 1712485) (by norm_num)
theorem B3044417 : Blo 2029435 3044417 := bstep (se 2 (by rfl) ⟨1141656, by rfl⟩ : syracuseStep 3044417 = 2283313) B2283313
theorem B2029611 : Blo 2029435 2029611 := bstep (se 1 (by rfl) ⟨1522208, by rfl⟩ : syracuseStep 2029611 = 3044417) B3044417
theorem B3251053 : Blo 2029435 3251053 := bbase (se 3 (by rfl) ⟨609572, by rfl⟩ : syracuseStep 3251053 = 1219145) (by norm_num)
theorem B4334737 : Blo 2029435 4334737 := bstep (se 2 (by rfl) ⟨1625526, by rfl⟩ : syracuseStep 4334737 = 3251053) B3251053
theorem B5779649 : Blo 2029435 5779649 := bstep (se 2 (by rfl) ⟨2167368, by rfl⟩ : syracuseStep 5779649 = 4334737) B4334737
theorem B3853099 : Blo 2029435 3853099 := bstep (se 1 (by rfl) ⟨2889824, by rfl⟩ : syracuseStep 3853099 = 5779649) B5779649
theorem B5137465 : Blo 2029435 5137465 := bstep (se 2 (by rfl) ⟨1926549, by rfl⟩ : syracuseStep 5137465 = 3853099) B3853099
theorem B6849953 : Blo 2029435 6849953 := bstep (se 2 (by rfl) ⟨2568732, by rfl⟩ : syracuseStep 6849953 = 5137465) B5137465
theorem B4566635 : Blo 2029435 4566635 := bstep (se 1 (by rfl) ⟨3424976, by rfl⟩ : syracuseStep 4566635 = 6849953) B6849953
theorem B3044423 : Blo 2029435 3044423 := bstep (se 1 (by rfl) ⟨2283317, by rfl⟩ : syracuseStep 3044423 = 4566635) B4566635
theorem B2029615 : Blo 2029435 2029615 := bstep (se 1 (by rfl) ⟨1522211, by rfl⟩ : syracuseStep 2029615 = 3044423) B3044423
theorem B3044429 : Blo 2029435 3044429 := bbase (se 3 (by rfl) ⟨570830, by rfl⟩ : syracuseStep 3044429 = 1141661) (by norm_num)
theorem B2029619 : Blo 2029435 2029619 := bstep (se 1 (by rfl) ⟨1522214, by rfl⟩ : syracuseStep 2029619 = 3044429) B3044429
theorem B4566653 : Blo 2029435 4566653 := bbase (se 3 (by rfl) ⟨856247, by rfl⟩ : syracuseStep 4566653 = 1712495) (by norm_num)
theorem B3044435 : Blo 2029435 3044435 := bstep (se 1 (by rfl) ⟨2283326, by rfl⟩ : syracuseStep 3044435 = 4566653) B4566653
theorem B2029623 : Blo 2029435 2029623 := bstep (se 1 (by rfl) ⟨1522217, by rfl⟩ : syracuseStep 2029623 = 3044435) B3044435
theorem B3424997 : Blo 2029435 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B2283331 : Blo 2029435 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B3044441 : Blo 2029435 3044441 := bstep (se 2 (by rfl) ⟨1141665, by rfl⟩ : syracuseStep 3044441 = 2283331) B2283331
theorem B2029627 : Blo 2029435 2029627 := bstep (se 1 (by rfl) ⟨1522220, by rfl⟩ : syracuseStep 2029627 = 3044441) B3044441
theorem B2438309 : Blo 2029435 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B6502157 : Blo 2029435 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B4334771 : Blo 2029435 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B2889847 : Blo 2029435 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B15412517 : Blo 2029435 15412517 := bstep (se 4 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 15412517 = 2889847) B2889847
theorem B10275011 : Blo 2029435 10275011 := bstep (se 1 (by rfl) ⟨7706258, by rfl⟩ : syracuseStep 10275011 = 15412517) B15412517
theorem B6850007 : Blo 2029435 6850007 := bstep (se 1 (by rfl) ⟨5137505, by rfl⟩ : syracuseStep 6850007 = 10275011) B10275011
theorem B4566671 : Blo 2029435 4566671 := bstep (se 1 (by rfl) ⟨3425003, by rfl⟩ : syracuseStep 4566671 = 6850007) B6850007
theorem B3044447 : Blo 2029435 3044447 := bstep (se 1 (by rfl) ⟨2283335, by rfl⟩ : syracuseStep 3044447 = 4566671) B4566671
theorem B2029631 : Blo 2029435 2029631 := bstep (se 1 (by rfl) ⟨1522223, by rfl⟩ : syracuseStep 2029631 = 3044447) B3044447
theorem B3044453 : Blo 2029435 3044453 := bbase (se 4 (by rfl) ⟨285417, by rfl⟩ : syracuseStep 3044453 = 570835) (by norm_num)
theorem B2029635 : Blo 2029435 2029635 := bstep (se 1 (by rfl) ⟨1522226, by rfl⟩ : syracuseStep 2029635 = 3044453) B3044453
theorem B4334789 : Blo 2029435 4334789 := bbase (se 4 (by rfl) ⟨406386, by rfl⟩ : syracuseStep 4334789 = 812773) (by norm_num)
theorem B2889859 : Blo 2029435 2889859 := bstep (se 1 (by rfl) ⟨2167394, by rfl⟩ : syracuseStep 2889859 = 4334789) B4334789
theorem B3853145 : Blo 2029435 3853145 := bstep (se 2 (by rfl) ⟨1444929, by rfl⟩ : syracuseStep 3853145 = 2889859) B2889859
theorem B2568763 : Blo 2029435 2568763 := bstep (se 1 (by rfl) ⟨1926572, by rfl⟩ : syracuseStep 2568763 = 3853145) B3853145
theorem B3425017 : Blo 2029435 3425017 := bstep (se 2 (by rfl) ⟨1284381, by rfl⟩ : syracuseStep 3425017 = 2568763) B2568763
theorem B4566689 : Blo 2029435 4566689 := bstep (se 2 (by rfl) ⟨1712508, by rfl⟩ : syracuseStep 4566689 = 3425017) B3425017
theorem B3044459 : Blo 2029435 3044459 := bstep (se 1 (by rfl) ⟨2283344, by rfl⟩ : syracuseStep 3044459 = 4566689) B4566689
theorem B2029639 : Blo 2029435 2029639 := bstep (se 1 (by rfl) ⟨1522229, by rfl⟩ : syracuseStep 2029639 = 3044459) B3044459
theorem B2283349 : Blo 2029435 2283349 := bbase (se 9 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 2283349 = 13379) (by norm_num)
theorem B3044465 : Blo 2029435 3044465 := bstep (se 2 (by rfl) ⟨1141674, by rfl⟩ : syracuseStep 3044465 = 2283349) B2283349
theorem B2029643 : Blo 2029435 2029643 := bstep (se 1 (by rfl) ⟨1522232, by rfl⟩ : syracuseStep 2029643 = 3044465) B3044465
theorem B2568773 : Blo 2029435 2568773 := bbase (se 4 (by rfl) ⟨240822, by rfl⟩ : syracuseStep 2568773 = 481645) (by norm_num)
theorem B6850061 : Blo 2029435 6850061 := bstep (se 3 (by rfl) ⟨1284386, by rfl⟩ : syracuseStep 6850061 = 2568773) B2568773
theorem B4566707 : Blo 2029435 4566707 := bstep (se 1 (by rfl) ⟨3425030, by rfl⟩ : syracuseStep 4566707 = 6850061) B6850061
theorem B3044471 : Blo 2029435 3044471 := bstep (se 1 (by rfl) ⟨2283353, by rfl⟩ : syracuseStep 3044471 = 4566707) B4566707
theorem B2029647 : Blo 2029435 2029647 := bstep (se 1 (by rfl) ⟨1522235, by rfl⟩ : syracuseStep 2029647 = 3044471) B3044471
theorem B3044477 : Blo 2029435 3044477 := bbase (se 3 (by rfl) ⟨570839, by rfl⟩ : syracuseStep 3044477 = 1141679) (by norm_num)
theorem B2029651 : Blo 2029435 2029651 := bstep (se 1 (by rfl) ⟨1522238, by rfl⟩ : syracuseStep 2029651 = 3044477) B3044477
theorem B4566725 : Blo 2029435 4566725 := bbase (se 4 (by rfl) ⟨428130, by rfl⟩ : syracuseStep 4566725 = 856261) (by norm_num)
theorem B3044483 : Blo 2029435 3044483 := bstep (se 1 (by rfl) ⟨2283362, by rfl⟩ : syracuseStep 3044483 = 4566725) B4566725
theorem B2029655 : Blo 2029435 2029655 := bstep (se 1 (by rfl) ⟨1522241, by rfl⟩ : syracuseStep 2029655 = 3044483) B3044483
theorem B7918085 : Blo 2029435 7918085 := bbase (se 4 (by rfl) ⟨742320, by rfl⟩ : syracuseStep 7918085 = 1484641) (by norm_num)
theorem B21114893 : Blo 2029435 21114893 := bstep (se 3 (by rfl) ⟨3959042, by rfl⟩ : syracuseStep 21114893 = 7918085) B7918085
theorem B14076595 : Blo 2029435 14076595 := bstep (se 1 (by rfl) ⟨10557446, by rfl⟩ : syracuseStep 14076595 = 21114893) B21114893
theorem B18768793 : Blo 2029435 18768793 := bstep (se 2 (by rfl) ⟨7038297, by rfl⟩ : syracuseStep 18768793 = 14076595) B14076595
theorem B25025057 : Blo 2029435 25025057 := bstep (se 2 (by rfl) ⟨9384396, by rfl⟩ : syracuseStep 25025057 = 18768793) B18768793
theorem B16683371 : Blo 2029435 16683371 := bstep (se 1 (by rfl) ⟨12512528, by rfl⟩ : syracuseStep 16683371 = 25025057) B25025057
theorem B11122247 : Blo 2029435 11122247 := bstep (se 1 (by rfl) ⟨8341685, by rfl⟩ : syracuseStep 11122247 = 16683371) B16683371
theorem B7414831 : Blo 2029435 7414831 := bstep (se 1 (by rfl) ⟨5561123, by rfl⟩ : syracuseStep 7414831 = 11122247) B11122247
theorem B9886441 : Blo 2029435 9886441 := bstep (se 2 (by rfl) ⟨3707415, by rfl⟩ : syracuseStep 9886441 = 7414831) B7414831
theorem B13181921 : Blo 2029435 13181921 := bstep (se 2 (by rfl) ⟨4943220, by rfl⟩ : syracuseStep 13181921 = 9886441) B9886441
theorem B8787947 : Blo 2029435 8787947 := bstep (se 1 (by rfl) ⟨6590960, by rfl⟩ : syracuseStep 8787947 = 13181921) B13181921
theorem B23434525 : Blo 2029435 23434525 := bstep (se 3 (by rfl) ⟨4393973, by rfl⟩ : syracuseStep 23434525 = 8787947) B8787947
theorem B124984133 : Blo 2029435 124984133 := bstep (se 4 (by rfl) ⟨11717262, by rfl⟩ : syracuseStep 124984133 = 23434525) B23434525
theorem B83322755 : Blo 2029435 83322755 := bstep (se 1 (by rfl) ⟨62492066, by rfl⟩ : syracuseStep 83322755 = 124984133) B124984133
theorem B55548503 : Blo 2029435 55548503 := bstep (se 1 (by rfl) ⟨41661377, by rfl⟩ : syracuseStep 55548503 = 83322755) B83322755
theorem B37032335 : Blo 2029435 37032335 := bstep (se 1 (by rfl) ⟨27774251, by rfl⟩ : syracuseStep 37032335 = 55548503) B55548503
theorem B24688223 : Blo 2029435 24688223 := bstep (se 1 (by rfl) ⟨18516167, by rfl⟩ : syracuseStep 24688223 = 37032335) B37032335
theorem B16458815 : Blo 2029435 16458815 := bstep (se 1 (by rfl) ⟨12344111, by rfl⟩ : syracuseStep 16458815 = 24688223) B24688223
theorem B43890173 : Blo 2029435 43890173 := bstep (se 3 (by rfl) ⟨8229407, by rfl⟩ : syracuseStep 43890173 = 16458815) B16458815
theorem B29260115 : Blo 2029435 29260115 := bstep (se 1 (by rfl) ⟨21945086, by rfl⟩ : syracuseStep 29260115 = 43890173) B43890173
theorem B19506743 : Blo 2029435 19506743 := bstep (se 1 (by rfl) ⟨14630057, by rfl⟩ : syracuseStep 19506743 = 29260115) B29260115
theorem B13004495 : Blo 2029435 13004495 := bstep (se 1 (by rfl) ⟨9753371, by rfl⟩ : syracuseStep 13004495 = 19506743) B19506743
theorem B8669663 : Blo 2029435 8669663 := bstep (se 1 (by rfl) ⟨6502247, by rfl⟩ : syracuseStep 8669663 = 13004495) B13004495
theorem B5779775 : Blo 2029435 5779775 := bstep (se 1 (by rfl) ⟨4334831, by rfl⟩ : syracuseStep 5779775 = 8669663) B8669663
theorem B3853183 : Blo 2029435 3853183 := bstep (se 1 (by rfl) ⟨2889887, by rfl⟩ : syracuseStep 3853183 = 5779775) B5779775
theorem B5137577 : Blo 2029435 5137577 := bstep (se 2 (by rfl) ⟨1926591, by rfl⟩ : syracuseStep 5137577 = 3853183) B3853183
theorem B3425051 : Blo 2029435 3425051 := bstep (se 1 (by rfl) ⟨2568788, by rfl⟩ : syracuseStep 3425051 = 5137577) B5137577
theorem B2283367 : Blo 2029435 2283367 := bstep (se 1 (by rfl) ⟨1712525, by rfl⟩ : syracuseStep 2283367 = 3425051) B3425051
theorem B3044489 : Blo 2029435 3044489 := bstep (se 2 (by rfl) ⟨1141683, by rfl⟩ : syracuseStep 3044489 = 2283367) B2283367
theorem B2029659 : Blo 2029435 2029659 := bstep (se 1 (by rfl) ⟨1522244, by rfl⟩ : syracuseStep 2029659 = 3044489) B3044489
theorem B10275173 : Blo 2029435 10275173 := bbase (se 4 (by rfl) ⟨963297, by rfl⟩ : syracuseStep 10275173 = 1926595) (by norm_num)
theorem B6850115 : Blo 2029435 6850115 := bstep (se 1 (by rfl) ⟨5137586, by rfl⟩ : syracuseStep 6850115 = 10275173) B10275173
theorem B4566743 : Blo 2029435 4566743 := bstep (se 1 (by rfl) ⟨3425057, by rfl⟩ : syracuseStep 4566743 = 6850115) B6850115
theorem B3044495 : Blo 2029435 3044495 := bstep (se 1 (by rfl) ⟨2283371, by rfl⟩ : syracuseStep 3044495 = 4566743) B4566743
theorem B2029663 : Blo 2029435 2029663 := bstep (se 1 (by rfl) ⟨1522247, by rfl⟩ : syracuseStep 2029663 = 3044495) B3044495
theorem B3044501 : Blo 2029435 3044501 := bbase (se 6 (by rfl) ⟨71355, by rfl⟩ : syracuseStep 3044501 = 142711) (by norm_num)
theorem B2029667 : Blo 2029435 2029667 := bstep (se 1 (by rfl) ⟨1522250, by rfl⟩ : syracuseStep 2029667 = 3044501) B3044501
theorem B2438357 : Blo 2029435 2438357 := bbase (se 7 (by rfl) ⟨28574, by rfl⟩ : syracuseStep 2438357 = 57149) (by norm_num)
theorem B6502285 : Blo 2029435 6502285 := bstep (se 3 (by rfl) ⟨1219178, by rfl⟩ : syracuseStep 6502285 = 2438357) B2438357
theorem B8669713 : Blo 2029435 8669713 := bstep (se 2 (by rfl) ⟨3251142, by rfl⟩ : syracuseStep 8669713 = 6502285) B6502285
theorem B11559617 : Blo 2029435 11559617 := bstep (se 2 (by rfl) ⟨4334856, by rfl⟩ : syracuseStep 11559617 = 8669713) B8669713
theorem B7706411 : Blo 2029435 7706411 := bstep (se 1 (by rfl) ⟨5779808, by rfl⟩ : syracuseStep 7706411 = 11559617) B11559617
theorem B5137607 : Blo 2029435 5137607 := bstep (se 1 (by rfl) ⟨3853205, by rfl⟩ : syracuseStep 5137607 = 7706411) B7706411
theorem B3425071 : Blo 2029435 3425071 := bstep (se 1 (by rfl) ⟨2568803, by rfl⟩ : syracuseStep 3425071 = 5137607) B5137607
theorem B4566761 : Blo 2029435 4566761 := bstep (se 2 (by rfl) ⟨1712535, by rfl⟩ : syracuseStep 4566761 = 3425071) B3425071
theorem B3044507 : Blo 2029435 3044507 := bstep (se 1 (by rfl) ⟨2283380, by rfl⟩ : syracuseStep 3044507 = 4566761) B4566761
theorem B2029671 : Blo 2029435 2029671 := bstep (se 1 (by rfl) ⟨1522253, by rfl⟩ : syracuseStep 2029671 = 3044507) B3044507
theorem B2283385 : Blo 2029435 2283385 := bbase (se 2 (by rfl) ⟨856269, by rfl⟩ : syracuseStep 2283385 = 1712539) (by norm_num)
theorem B3044513 : Blo 2029435 3044513 := bstep (se 2 (by rfl) ⟨1141692, by rfl⟩ : syracuseStep 3044513 = 2283385) B2283385
theorem B2029675 : Blo 2029435 2029675 := bstep (se 1 (by rfl) ⟨1522256, by rfl⟩ : syracuseStep 2029675 = 3044513) B3044513
theorem B4876733 : Blo 2029435 4876733 := bbase (se 3 (by rfl) ⟨914387, by rfl⟩ : syracuseStep 4876733 = 1828775) (by norm_num)
theorem B13004621 : Blo 2029435 13004621 := bstep (se 3 (by rfl) ⟨2438366, by rfl⟩ : syracuseStep 13004621 = 4876733) B4876733
theorem B8669747 : Blo 2029435 8669747 := bstep (se 1 (by rfl) ⟨6502310, by rfl⟩ : syracuseStep 8669747 = 13004621) B13004621
theorem B5779831 : Blo 2029435 5779831 := bstep (se 1 (by rfl) ⟨4334873, by rfl⟩ : syracuseStep 5779831 = 8669747) B8669747
theorem B7706441 : Blo 2029435 7706441 := bstep (se 2 (by rfl) ⟨2889915, by rfl⟩ : syracuseStep 7706441 = 5779831) B5779831
theorem B5137627 : Blo 2029435 5137627 := bstep (se 1 (by rfl) ⟨3853220, by rfl⟩ : syracuseStep 5137627 = 7706441) B7706441
theorem B6850169 : Blo 2029435 6850169 := bstep (se 2 (by rfl) ⟨2568813, by rfl⟩ : syracuseStep 6850169 = 5137627) B5137627
theorem B4566779 : Blo 2029435 4566779 := bstep (se 1 (by rfl) ⟨3425084, by rfl⟩ : syracuseStep 4566779 = 6850169) B6850169
theorem B3044519 : Blo 2029435 3044519 := bstep (se 1 (by rfl) ⟨2283389, by rfl⟩ : syracuseStep 3044519 = 4566779) B4566779
theorem B2029679 : Blo 2029435 2029679 := bstep (se 1 (by rfl) ⟨1522259, by rfl⟩ : syracuseStep 2029679 = 3044519) B3044519
theorem B3044525 : Blo 2029435 3044525 := bbase (se 3 (by rfl) ⟨570848, by rfl⟩ : syracuseStep 3044525 = 1141697) (by norm_num)
theorem B2029683 : Blo 2029435 2029683 := bstep (se 1 (by rfl) ⟨1522262, by rfl⟩ : syracuseStep 2029683 = 3044525) B3044525
theorem B4566797 : Blo 2029435 4566797 := bbase (se 3 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 4566797 = 1712549) (by norm_num)
theorem B3044531 : Blo 2029435 3044531 := bstep (se 1 (by rfl) ⟨2283398, by rfl⟩ : syracuseStep 3044531 = 4566797) B4566797
theorem B2029687 : Blo 2029435 2029687 := bstep (se 1 (by rfl) ⟨1522265, by rfl⟩ : syracuseStep 2029687 = 3044531) B3044531
theorem B2568829 : Blo 2029435 2568829 := bbase (se 3 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 2568829 = 963311) (by norm_num)
theorem B3425105 : Blo 2029435 3425105 := bstep (se 2 (by rfl) ⟨1284414, by rfl⟩ : syracuseStep 3425105 = 2568829) B2568829
theorem B2283403 : Blo 2029435 2283403 := bstep (se 1 (by rfl) ⟨1712552, by rfl⟩ : syracuseStep 2283403 = 3425105) B3425105
theorem B3044537 : Blo 2029435 3044537 := bstep (se 2 (by rfl) ⟨1141701, by rfl⟩ : syracuseStep 3044537 = 2283403) B2283403
theorem B2029691 : Blo 2029435 2029691 := bstep (se 1 (by rfl) ⟨1522268, by rfl⟩ : syracuseStep 2029691 = 3044537) B3044537
theorem B7315157 : Blo 2029435 7315157 := bbase (se 7 (by rfl) ⟨85724, by rfl⟩ : syracuseStep 7315157 = 171449) (by norm_num)
theorem B4876771 : Blo 2029435 4876771 := bstep (se 1 (by rfl) ⟨3657578, by rfl⟩ : syracuseStep 4876771 = 7315157) B7315157
theorem B6502361 : Blo 2029435 6502361 := bstep (se 2 (by rfl) ⟨2438385, by rfl⟩ : syracuseStep 6502361 = 4876771) B4876771
theorem B17339629 : Blo 2029435 17339629 := bstep (se 3 (by rfl) ⟨3251180, by rfl⟩ : syracuseStep 17339629 = 6502361) B6502361
theorem B23119505 : Blo 2029435 23119505 := bstep (se 2 (by rfl) ⟨8669814, by rfl⟩ : syracuseStep 23119505 = 17339629) B17339629
theorem B15413003 : Blo 2029435 15413003 := bstep (se 1 (by rfl) ⟨11559752, by rfl⟩ : syracuseStep 15413003 = 23119505) B23119505
theorem B10275335 : Blo 2029435 10275335 := bstep (se 1 (by rfl) ⟨7706501, by rfl⟩ : syracuseStep 10275335 = 15413003) B15413003
theorem B6850223 : Blo 2029435 6850223 := bstep (se 1 (by rfl) ⟨5137667, by rfl⟩ : syracuseStep 6850223 = 10275335) B10275335
theorem B4566815 : Blo 2029435 4566815 := bstep (se 1 (by rfl) ⟨3425111, by rfl⟩ : syracuseStep 4566815 = 6850223) B6850223
theorem B3044543 : Blo 2029435 3044543 := bstep (se 1 (by rfl) ⟨2283407, by rfl⟩ : syracuseStep 3044543 = 4566815) B4566815
theorem B2029695 : Blo 2029435 2029695 := bstep (se 1 (by rfl) ⟨1522271, by rfl⟩ : syracuseStep 2029695 = 3044543) B3044543
theorem B3044549 : Blo 2029435 3044549 := bbase (se 4 (by rfl) ⟨285426, by rfl⟩ : syracuseStep 3044549 = 570853) (by norm_num)
theorem B2029699 : Blo 2029435 2029699 := bstep (se 1 (by rfl) ⟨1522274, by rfl⟩ : syracuseStep 2029699 = 3044549) B3044549
theorem B3425125 : Blo 2029435 3425125 := bbase (se 4 (by rfl) ⟨321105, by rfl⟩ : syracuseStep 3425125 = 642211) (by norm_num)
theorem B4566833 : Blo 2029435 4566833 := bstep (se 2 (by rfl) ⟨1712562, by rfl⟩ : syracuseStep 4566833 = 3425125) B3425125
theorem B3044555 : Blo 2029435 3044555 := bstep (se 1 (by rfl) ⟨2283416, by rfl⟩ : syracuseStep 3044555 = 4566833) B4566833
theorem B2029703 : Blo 2029435 2029703 := bstep (se 1 (by rfl) ⟨1522277, by rfl⟩ : syracuseStep 2029703 = 3044555) B3044555
theorem B2283421 : Blo 2029435 2283421 := bbase (se 3 (by rfl) ⟨428141, by rfl⟩ : syracuseStep 2283421 = 856283) (by norm_num)
theorem B3044561 : Blo 2029435 3044561 := bstep (se 2 (by rfl) ⟨1141710, by rfl⟩ : syracuseStep 3044561 = 2283421) B2283421
theorem B2029707 : Blo 2029435 2029707 := bstep (se 1 (by rfl) ⟨1522280, by rfl⟩ : syracuseStep 2029707 = 3044561) B3044561
theorem B6850277 : Blo 2029435 6850277 := bbase (se 4 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 6850277 = 1284427) (by norm_num)
theorem B4566851 : Blo 2029435 4566851 := bstep (se 1 (by rfl) ⟨3425138, by rfl⟩ : syracuseStep 4566851 = 6850277) B6850277
theorem B3044567 : Blo 2029435 3044567 := bstep (se 1 (by rfl) ⟨2283425, by rfl⟩ : syracuseStep 3044567 = 4566851) B4566851
theorem B2029711 : Blo 2029435 2029711 := bstep (se 1 (by rfl) ⟨1522283, by rfl⟩ : syracuseStep 2029711 = 3044567) B3044567
theorem B3044573 : Blo 2029435 3044573 := bbase (se 3 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 3044573 = 1141715) (by norm_num)
theorem B2029715 : Blo 2029435 2029715 := bstep (se 1 (by rfl) ⟨1522286, by rfl⟩ : syracuseStep 2029715 = 3044573) B3044573
theorem B4566869 : Blo 2029435 4566869 := bbase (se 9 (by rfl) ⟨13379, by rfl⟩ : syracuseStep 4566869 = 26759) (by norm_num)
theorem B3044579 : Blo 2029435 3044579 := bstep (se 1 (by rfl) ⟨2283434, by rfl⟩ : syracuseStep 3044579 = 4566869) B4566869
theorem B2029719 : Blo 2029435 2029719 := bstep (se 1 (by rfl) ⟨1522289, by rfl⟩ : syracuseStep 2029719 = 3044579) B3044579
theorem B5779957 : Blo 2029435 5779957 := bbase (se 5 (by rfl) ⟨270935, by rfl⟩ : syracuseStep 5779957 = 541871) (by norm_num)
theorem B7706609 : Blo 2029435 7706609 := bstep (se 2 (by rfl) ⟨2889978, by rfl⟩ : syracuseStep 7706609 = 5779957) B5779957
theorem B5137739 : Blo 2029435 5137739 := bstep (se 1 (by rfl) ⟨3853304, by rfl⟩ : syracuseStep 5137739 = 7706609) B7706609
theorem B3425159 : Blo 2029435 3425159 := bstep (se 1 (by rfl) ⟨2568869, by rfl⟩ : syracuseStep 3425159 = 5137739) B5137739
theorem B2283439 : Blo 2029435 2283439 := bstep (se 1 (by rfl) ⟨1712579, by rfl⟩ : syracuseStep 2283439 = 3425159) B3425159
theorem B3044585 : Blo 2029435 3044585 := bstep (se 2 (by rfl) ⟨1141719, by rfl⟩ : syracuseStep 3044585 = 2283439) B2283439
theorem B2029723 : Blo 2029435 2029723 := bstep (se 1 (by rfl) ⟨1522292, by rfl⟩ : syracuseStep 2029723 = 3044585) B3044585
theorem B5207845 : Blo 2029435 5207845 := bbase (se 4 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 5207845 = 976471) (by norm_num)
theorem B444402773 : Blo 2029435 444402773 := bstep (se 8 (by rfl) ⟨2603922, by rfl⟩ : syracuseStep 444402773 = 5207845) B5207845
theorem B296268515 : Blo 2029435 296268515 := bstep (se 1 (by rfl) ⟨222201386, by rfl⟩ : syracuseStep 296268515 = 444402773) B444402773
theorem B197512343 : Blo 2029435 197512343 := bstep (se 1 (by rfl) ⟨148134257, by rfl⟩ : syracuseStep 197512343 = 296268515) B296268515
theorem B131674895 : Blo 2029435 131674895 := bstep (se 1 (by rfl) ⟨98756171, by rfl⟩ : syracuseStep 131674895 = 197512343) B197512343
theorem B87783263 : Blo 2029435 87783263 := bstep (se 1 (by rfl) ⟨65837447, by rfl⟩ : syracuseStep 87783263 = 131674895) B131674895
theorem B58522175 : Blo 2029435 58522175 := bstep (se 1 (by rfl) ⟨43891631, by rfl⟩ : syracuseStep 58522175 = 87783263) B87783263
theorem B39014783 : Blo 2029435 39014783 := bstep (se 1 (by rfl) ⟨29261087, by rfl⟩ : syracuseStep 39014783 = 58522175) B58522175
theorem B26009855 : Blo 2029435 26009855 := bstep (se 1 (by rfl) ⟨19507391, by rfl⟩ : syracuseStep 26009855 = 39014783) B39014783
theorem B17339903 : Blo 2029435 17339903 := bstep (se 1 (by rfl) ⟨13004927, by rfl⟩ : syracuseStep 17339903 = 26009855) B26009855
theorem B11559935 : Blo 2029435 11559935 := bstep (se 1 (by rfl) ⟨8669951, by rfl⟩ : syracuseStep 11559935 = 17339903) B17339903
theorem B7706623 : Blo 2029435 7706623 := bstep (se 1 (by rfl) ⟨5779967, by rfl⟩ : syracuseStep 7706623 = 11559935) B11559935
theorem B10275497 : Blo 2029435 10275497 := bstep (se 2 (by rfl) ⟨3853311, by rfl⟩ : syracuseStep 10275497 = 7706623) B7706623
theorem B6850331 : Blo 2029435 6850331 := bstep (se 1 (by rfl) ⟨5137748, by rfl⟩ : syracuseStep 6850331 = 10275497) B10275497
theorem B4566887 : Blo 2029435 4566887 := bstep (se 1 (by rfl) ⟨3425165, by rfl⟩ : syracuseStep 4566887 = 6850331) B6850331
theorem B3044591 : Blo 2029435 3044591 := bstep (se 1 (by rfl) ⟨2283443, by rfl⟩ : syracuseStep 3044591 = 4566887) B4566887
theorem B2029727 : Blo 2029435 2029727 := bstep (se 1 (by rfl) ⟨1522295, by rfl⟩ : syracuseStep 2029727 = 3044591) B3044591
theorem B3044597 : Blo 2029435 3044597 := bbase (se 5 (by rfl) ⟨142715, by rfl⟩ : syracuseStep 3044597 = 285431) (by norm_num)
theorem B2029731 : Blo 2029435 2029731 := bstep (se 1 (by rfl) ⟨1522298, by rfl⟩ : syracuseStep 2029731 = 3044597) B3044597
theorem B13004981 : Blo 2029435 13004981 := bbase (se 5 (by rfl) ⟨609608, by rfl⟩ : syracuseStep 13004981 = 1219217) (by norm_num)
theorem B8669987 : Blo 2029435 8669987 := bstep (se 1 (by rfl) ⟨6502490, by rfl⟩ : syracuseStep 8669987 = 13004981) B13004981
theorem B5779991 : Blo 2029435 5779991 := bstep (se 1 (by rfl) ⟨4334993, by rfl⟩ : syracuseStep 5779991 = 8669987) B8669987
theorem B3853327 : Blo 2029435 3853327 := bstep (se 1 (by rfl) ⟨2889995, by rfl⟩ : syracuseStep 3853327 = 5779991) B5779991
theorem B5137769 : Blo 2029435 5137769 := bstep (se 2 (by rfl) ⟨1926663, by rfl⟩ : syracuseStep 5137769 = 3853327) B3853327
theorem B3425179 : Blo 2029435 3425179 := bstep (se 1 (by rfl) ⟨2568884, by rfl⟩ : syracuseStep 3425179 = 5137769) B5137769
theorem B4566905 : Blo 2029435 4566905 := bstep (se 2 (by rfl) ⟨1712589, by rfl⟩ : syracuseStep 4566905 = 3425179) B3425179
theorem B3044603 : Blo 2029435 3044603 := bstep (se 1 (by rfl) ⟨2283452, by rfl⟩ : syracuseStep 3044603 = 4566905) B4566905
theorem B2029735 : Blo 2029435 2029735 := bstep (se 1 (by rfl) ⟨1522301, by rfl⟩ : syracuseStep 2029735 = 3044603) B3044603
theorem B2283457 : Blo 2029435 2283457 := bbase (se 2 (by rfl) ⟨856296, by rfl⟩ : syracuseStep 2283457 = 1712593) (by norm_num)
theorem B3044609 : Blo 2029435 3044609 := bstep (se 2 (by rfl) ⟨1141728, by rfl⟩ : syracuseStep 3044609 = 2283457) B2283457
theorem B2029739 : Blo 2029435 2029739 := bstep (se 1 (by rfl) ⟨1522304, by rfl⟩ : syracuseStep 2029739 = 3044609) B3044609
theorem B5137789 : Blo 2029435 5137789 := bbase (se 3 (by rfl) ⟨963335, by rfl⟩ : syracuseStep 5137789 = 1926671) (by norm_num)
theorem B6850385 : Blo 2029435 6850385 := bstep (se 2 (by rfl) ⟨2568894, by rfl⟩ : syracuseStep 6850385 = 5137789) B5137789
theorem B4566923 : Blo 2029435 4566923 := bstep (se 1 (by rfl) ⟨3425192, by rfl⟩ : syracuseStep 4566923 = 6850385) B6850385
theorem B3044615 : Blo 2029435 3044615 := bstep (se 1 (by rfl) ⟨2283461, by rfl⟩ : syracuseStep 3044615 = 4566923) B4566923
theorem B2029743 : Blo 2029435 2029743 := bstep (se 1 (by rfl) ⟨1522307, by rfl⟩ : syracuseStep 2029743 = 3044615) B3044615
theorem B3044621 : Blo 2029435 3044621 := bbase (se 3 (by rfl) ⟨570866, by rfl⟩ : syracuseStep 3044621 = 1141733) (by norm_num)
theorem B2029747 : Blo 2029435 2029747 := bstep (se 1 (by rfl) ⟨1522310, by rfl⟩ : syracuseStep 2029747 = 3044621) B3044621
theorem B4566941 : Blo 2029435 4566941 := bbase (se 3 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 4566941 = 1712603) (by norm_num)
theorem B3044627 : Blo 2029435 3044627 := bstep (se 1 (by rfl) ⟨2283470, by rfl⟩ : syracuseStep 3044627 = 4566941) B4566941
theorem B2029751 : Blo 2029435 2029751 := bstep (se 1 (by rfl) ⟨1522313, by rfl⟩ : syracuseStep 2029751 = 3044627) B3044627
theorem B3425213 : Blo 2029435 3425213 := bbase (se 3 (by rfl) ⟨642227, by rfl⟩ : syracuseStep 3425213 = 1284455) (by norm_num)
theorem B2283475 : Blo 2029435 2283475 := bstep (se 1 (by rfl) ⟨1712606, by rfl⟩ : syracuseStep 2283475 = 3425213) B3425213
theorem B3044633 : Blo 2029435 3044633 := bstep (se 2 (by rfl) ⟨1141737, by rfl⟩ : syracuseStep 3044633 = 2283475) B2283475
theorem B2029755 : Blo 2029435 2029755 := bstep (se 1 (by rfl) ⟨1522316, by rfl⟩ : syracuseStep 2029755 = 3044633) B3044633
theorem B11560117 : Blo 2029435 11560117 := bbase (se 5 (by rfl) ⟨541880, by rfl⟩ : syracuseStep 11560117 = 1083761) (by norm_num)
theorem B15413489 : Blo 2029435 15413489 := bstep (se 2 (by rfl) ⟨5780058, by rfl⟩ : syracuseStep 15413489 = 11560117) B11560117
theorem B10275659 : Blo 2029435 10275659 := bstep (se 1 (by rfl) ⟨7706744, by rfl⟩ : syracuseStep 10275659 = 15413489) B15413489
theorem B6850439 : Blo 2029435 6850439 := bstep (se 1 (by rfl) ⟨5137829, by rfl⟩ : syracuseStep 6850439 = 10275659) B10275659
theorem B4566959 : Blo 2029435 4566959 := bstep (se 1 (by rfl) ⟨3425219, by rfl⟩ : syracuseStep 4566959 = 6850439) B6850439
theorem B3044639 : Blo 2029435 3044639 := bstep (se 1 (by rfl) ⟨2283479, by rfl⟩ : syracuseStep 3044639 = 4566959) B4566959
theorem B2029759 : Blo 2029435 2029759 := bstep (se 1 (by rfl) ⟨1522319, by rfl⟩ : syracuseStep 2029759 = 3044639) B3044639
theorem B3044645 : Blo 2029435 3044645 := bbase (se 4 (by rfl) ⟨285435, by rfl⟩ : syracuseStep 3044645 = 570871) (by norm_num)
theorem B2029763 : Blo 2029435 2029763 := bstep (se 1 (by rfl) ⟨1522322, by rfl⟩ : syracuseStep 2029763 = 3044645) B3044645
theorem B2568925 : Blo 2029435 2568925 := bbase (se 3 (by rfl) ⟨481673, by rfl⟩ : syracuseStep 2568925 = 963347) (by norm_num)
theorem B3425233 : Blo 2029435 3425233 := bstep (se 2 (by rfl) ⟨1284462, by rfl⟩ : syracuseStep 3425233 = 2568925) B2568925
theorem B4566977 : Blo 2029435 4566977 := bstep (se 2 (by rfl) ⟨1712616, by rfl⟩ : syracuseStep 4566977 = 3425233) B3425233
theorem B3044651 : Blo 2029435 3044651 := bstep (se 1 (by rfl) ⟨2283488, by rfl⟩ : syracuseStep 3044651 = 4566977) B4566977
theorem B2029767 : Blo 2029435 2029767 := bstep (se 1 (by rfl) ⟨1522325, by rfl⟩ : syracuseStep 2029767 = 3044651) B3044651
theorem B2283493 : Blo 2029435 2283493 := bbase (se 4 (by rfl) ⟨214077, by rfl⟩ : syracuseStep 2283493 = 428155) (by norm_num)
theorem B3044657 : Blo 2029435 3044657 := bstep (se 2 (by rfl) ⟨1141746, by rfl⟩ : syracuseStep 3044657 = 2283493) B2283493
theorem B2029771 : Blo 2029435 2029771 := bstep (se 1 (by rfl) ⟨1522328, by rfl⟩ : syracuseStep 2029771 = 3044657) B3044657
theorem B7811957 : Blo 2029435 7811957 := bbase (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) (by norm_num)
theorem B5207971 : Blo 2029435 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B6943961 : Blo 2029435 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B4629307 : Blo 2029435 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B6172409 : Blo 2029435 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B16459757 : Blo 2029435 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B10973171 : Blo 2029435 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B7315447 : Blo 2029435 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B9753929 : Blo 2029435 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B6502619 : Blo 2029435 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B4335079 : Blo 2029435 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B5780105 : Blo 2029435 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B3853403 : Blo 2029435 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B2568935 : Blo 2029435 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B6850493 : Blo 2029435 6850493 := bstep (se 3 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 6850493 = 2568935) B2568935
theorem B4566995 : Blo 2029435 4566995 := bstep (se 1 (by rfl) ⟨3425246, by rfl⟩ : syracuseStep 4566995 = 6850493) B6850493
theorem B3044663 : Blo 2029435 3044663 := bstep (se 1 (by rfl) ⟨2283497, by rfl⟩ : syracuseStep 3044663 = 4566995) B4566995
theorem B2029775 : Blo 2029435 2029775 := bstep (se 1 (by rfl) ⟨1522331, by rfl⟩ : syracuseStep 2029775 = 3044663) B3044663
theorem B3044669 : Blo 2029435 3044669 := bbase (se 3 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 3044669 = 1141751) (by norm_num)
theorem B2029779 : Blo 2029435 2029779 := bstep (se 1 (by rfl) ⟨1522334, by rfl⟩ : syracuseStep 2029779 = 3044669) B3044669
theorem B4567013 : Blo 2029435 4567013 := bbase (se 4 (by rfl) ⟨428157, by rfl⟩ : syracuseStep 4567013 = 856315) (by norm_num)
theorem B3044675 : Blo 2029435 3044675 := bstep (se 1 (by rfl) ⟨2283506, by rfl⟩ : syracuseStep 3044675 = 4567013) B4567013
theorem B2029783 : Blo 2029435 2029783 := bstep (se 1 (by rfl) ⟨1522337, by rfl⟩ : syracuseStep 2029783 = 3044675) B3044675
theorem B5137901 : Blo 2029435 5137901 := bbase (se 3 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 5137901 = 1926713) (by norm_num)
theorem B3425267 : Blo 2029435 3425267 := bstep (se 1 (by rfl) ⟨2568950, by rfl⟩ : syracuseStep 3425267 = 5137901) B5137901
theorem B2283511 : Blo 2029435 2283511 := bstep (se 1 (by rfl) ⟨1712633, by rfl⟩ : syracuseStep 2283511 = 3425267) B3425267
theorem B3044681 : Blo 2029435 3044681 := bstep (se 2 (by rfl) ⟨1141755, by rfl⟩ : syracuseStep 3044681 = 2283511) B2283511
theorem B2029787 : Blo 2029435 2029787 := bstep (se 1 (by rfl) ⟨1522340, by rfl⟩ : syracuseStep 2029787 = 3044681) B3044681
theorem B5486629 : Blo 2029435 5486629 := bbase (se 4 (by rfl) ⟨514371, by rfl⟩ : syracuseStep 5486629 = 1028743) (by norm_num)
theorem B7315505 : Blo 2029435 7315505 := bstep (se 2 (by rfl) ⟨2743314, by rfl⟩ : syracuseStep 7315505 = 5486629) B5486629
theorem B4877003 : Blo 2029435 4877003 := bstep (se 1 (by rfl) ⟨3657752, by rfl⟩ : syracuseStep 4877003 = 7315505) B7315505
theorem B3251335 : Blo 2029435 3251335 := bstep (se 1 (by rfl) ⟨2438501, by rfl⟩ : syracuseStep 3251335 = 4877003) B4877003
theorem B4335113 : Blo 2029435 4335113 := bstep (se 2 (by rfl) ⟨1625667, by rfl⟩ : syracuseStep 4335113 = 3251335) B3251335
theorem B2890075 : Blo 2029435 2890075 := bstep (se 1 (by rfl) ⟨2167556, by rfl⟩ : syracuseStep 2890075 = 4335113) B4335113
theorem B3853433 : Blo 2029435 3853433 := bstep (se 2 (by rfl) ⟨1445037, by rfl⟩ : syracuseStep 3853433 = 2890075) B2890075
theorem B10275821 : Blo 2029435 10275821 := bstep (se 3 (by rfl) ⟨1926716, by rfl⟩ : syracuseStep 10275821 = 3853433) B3853433
theorem B6850547 : Blo 2029435 6850547 := bstep (se 1 (by rfl) ⟨5137910, by rfl⟩ : syracuseStep 6850547 = 10275821) B10275821
theorem B4567031 : Blo 2029435 4567031 := bstep (se 1 (by rfl) ⟨3425273, by rfl⟩ : syracuseStep 4567031 = 6850547) B6850547
theorem B3044687 : Blo 2029435 3044687 := bstep (se 1 (by rfl) ⟨2283515, by rfl⟩ : syracuseStep 3044687 = 4567031) B4567031
theorem B2029791 : Blo 2029435 2029791 := bstep (se 1 (by rfl) ⟨1522343, by rfl⟩ : syracuseStep 2029791 = 3044687) B3044687
theorem B3044693 : Blo 2029435 3044693 := bbase (se 13 (by rfl) ⟨557, by rfl⟩ : syracuseStep 3044693 = 1115) (by norm_num)
theorem B2029795 : Blo 2029435 2029795 := bstep (se 1 (by rfl) ⟨1522346, by rfl⟩ : syracuseStep 2029795 = 3044693) B3044693
theorem B2167565 : Blo 2029435 2167565 := bbase (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) (by norm_num)
theorem B5780173 : Blo 2029435 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B7706897 : Blo 2029435 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B5137931 : Blo 2029435 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B3425287 : Blo 2029435 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B4567049 : Blo 2029435 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B3044699 : Blo 2029435 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B2029799 : Blo 2029435 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B2283529 : Blo 2029435 2283529 := bbase (se 2 (by rfl) ⟨856323, by rfl⟩ : syracuseStep 2283529 = 1712647) (by norm_num)
theorem B3044705 : Blo 2029435 3044705 := bstep (se 2 (by rfl) ⟨1141764, by rfl⟩ : syracuseStep 3044705 = 2283529) B2283529
theorem B2029803 : Blo 2029435 2029803 := bstep (se 1 (by rfl) ⟨1522352, by rfl⟩ : syracuseStep 2029803 = 3044705) B3044705
theorem B6944069 : Blo 2029435 6944069 := bbase (se 4 (by rfl) ⟨651006, by rfl⟩ : syracuseStep 6944069 = 1302013) (by norm_num)
theorem B4629379 : Blo 2029435 4629379 := bstep (se 1 (by rfl) ⟨3472034, by rfl⟩ : syracuseStep 4629379 = 6944069) B6944069
theorem B6172505 : Blo 2029435 6172505 := bstep (se 2 (by rfl) ⟨2314689, by rfl⟩ : syracuseStep 6172505 = 4629379) B4629379
theorem B4115003 : Blo 2029435 4115003 := bstep (se 1 (by rfl) ⟨3086252, by rfl⟩ : syracuseStep 4115003 = 6172505) B6172505
theorem B10973341 : Blo 2029435 10973341 := bstep (se 3 (by rfl) ⟨2057501, by rfl⟩ : syracuseStep 10973341 = 4115003) B4115003
theorem B14631121 : Blo 2029435 14631121 := bstep (se 2 (by rfl) ⟨5486670, by rfl⟩ : syracuseStep 14631121 = 10973341) B10973341
theorem B19508161 : Blo 2029435 19508161 := bstep (se 2 (by rfl) ⟨7315560, by rfl⟩ : syracuseStep 19508161 = 14631121) B14631121
theorem B26010881 : Blo 2029435 26010881 := bstep (se 2 (by rfl) ⟨9754080, by rfl⟩ : syracuseStep 26010881 = 19508161) B19508161
theorem B17340587 : Blo 2029435 17340587 := bstep (se 1 (by rfl) ⟨13005440, by rfl⟩ : syracuseStep 17340587 = 26010881) B26010881
theorem B11560391 : Blo 2029435 11560391 := bstep (se 1 (by rfl) ⟨8670293, by rfl⟩ : syracuseStep 11560391 = 17340587) B17340587
theorem B7706927 : Blo 2029435 7706927 := bstep (se 1 (by rfl) ⟨5780195, by rfl⟩ : syracuseStep 7706927 = 11560391) B11560391
theorem B5137951 : Blo 2029435 5137951 := bstep (se 1 (by rfl) ⟨3853463, by rfl⟩ : syracuseStep 5137951 = 7706927) B7706927
theorem B6850601 : Blo 2029435 6850601 := bstep (se 2 (by rfl) ⟨2568975, by rfl⟩ : syracuseStep 6850601 = 5137951) B5137951
theorem B4567067 : Blo 2029435 4567067 := bstep (se 1 (by rfl) ⟨3425300, by rfl⟩ : syracuseStep 4567067 = 6850601) B6850601
theorem B3044711 : Blo 2029435 3044711 := bstep (se 1 (by rfl) ⟨2283533, by rfl⟩ : syracuseStep 3044711 = 4567067) B4567067
theorem B2029807 : Blo 2029435 2029807 := bstep (se 1 (by rfl) ⟨1522355, by rfl⟩ : syracuseStep 2029807 = 3044711) B3044711
theorem B3044717 : Blo 2029435 3044717 := bbase (se 3 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 3044717 = 1141769) (by norm_num)
theorem B2029811 : Blo 2029435 2029811 := bstep (se 1 (by rfl) ⟨1522358, by rfl⟩ : syracuseStep 2029811 = 3044717) B3044717
theorem B4567085 : Blo 2029435 4567085 := bbase (se 3 (by rfl) ⟨856328, by rfl⟩ : syracuseStep 4567085 = 1712657) (by norm_num)
theorem B3044723 : Blo 2029435 3044723 := bstep (se 1 (by rfl) ⟨2283542, by rfl⟩ : syracuseStep 3044723 = 4567085) B4567085
theorem B2029815 : Blo 2029435 2029815 := bstep (se 1 (by rfl) ⟨1522361, by rfl⟩ : syracuseStep 2029815 = 3044723) B3044723
theorem B4115029 : Blo 2029435 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B5486705 : Blo 2029435 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B3657803 : Blo 2029435 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B9754141 : Blo 2029435 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B13005521 : Blo 2029435 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B8670347 : Blo 2029435 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B5780231 : Blo 2029435 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B3853487 : Blo 2029435 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B2568991 : Blo 2029435 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B3425321 : Blo 2029435 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B2283547 : Blo 2029435 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B3044729 : Blo 2029435 3044729 := bstep (se 2 (by rfl) ⟨1141773, by rfl⟩ : syracuseStep 3044729 = 2283547) B2283547
theorem B2029819 : Blo 2029435 2029819 := bstep (se 1 (by rfl) ⟨1522364, by rfl⟩ : syracuseStep 2029819 = 3044729) B3044729
theorem B2743357 : Blo 2029435 2743357 := bbase (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) (by norm_num)
theorem B3657809 : Blo 2029435 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B9754157 : Blo 2029435 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B6502771 : Blo 2029435 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B34681445 : Blo 2029435 34681445 := bstep (se 4 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 34681445 = 6502771) B6502771
theorem B23120963 : Blo 2029435 23120963 := bstep (se 1 (by rfl) ⟨17340722, by rfl⟩ : syracuseStep 23120963 = 34681445) B34681445
theorem B15413975 : Blo 2029435 15413975 := bstep (se 1 (by rfl) ⟨11560481, by rfl⟩ : syracuseStep 15413975 = 23120963) B23120963
theorem B10275983 : Blo 2029435 10275983 := bstep (se 1 (by rfl) ⟨7706987, by rfl⟩ : syracuseStep 10275983 = 15413975) B15413975
theorem B6850655 : Blo 2029435 6850655 := bstep (se 1 (by rfl) ⟨5137991, by rfl⟩ : syracuseStep 6850655 = 10275983) B10275983
theorem B4567103 : Blo 2029435 4567103 := bstep (se 1 (by rfl) ⟨3425327, by rfl⟩ : syracuseStep 4567103 = 6850655) B6850655
theorem B3044735 : Blo 2029435 3044735 := bstep (se 1 (by rfl) ⟨2283551, by rfl⟩ : syracuseStep 3044735 = 4567103) B4567103
theorem B2029823 : Blo 2029435 2029823 := bstep (se 1 (by rfl) ⟨1522367, by rfl⟩ : syracuseStep 2029823 = 3044735) B3044735
theorem B3044741 : Blo 2029435 3044741 := bbase (se 4 (by rfl) ⟨285444, by rfl⟩ : syracuseStep 3044741 = 570889) (by norm_num)
theorem B2029827 : Blo 2029435 2029827 := bstep (se 1 (by rfl) ⟨1522370, by rfl⟩ : syracuseStep 2029827 = 3044741) B3044741
theorem B3425341 : Blo 2029435 3425341 := bbase (se 3 (by rfl) ⟨642251, by rfl⟩ : syracuseStep 3425341 = 1284503) (by norm_num)
theorem B4567121 : Blo 2029435 4567121 := bstep (se 2 (by rfl) ⟨1712670, by rfl⟩ : syracuseStep 4567121 = 3425341) B3425341
theorem B3044747 : Blo 2029435 3044747 := bstep (se 1 (by rfl) ⟨2283560, by rfl⟩ : syracuseStep 3044747 = 4567121) B4567121
theorem B2029831 : Blo 2029435 2029831 := bstep (se 1 (by rfl) ⟨1522373, by rfl⟩ : syracuseStep 2029831 = 3044747) B3044747
theorem B2283565 : Blo 2029435 2283565 := bbase (se 3 (by rfl) ⟨428168, by rfl⟩ : syracuseStep 2283565 = 856337) (by norm_num)
theorem B3044753 : Blo 2029435 3044753 := bstep (se 2 (by rfl) ⟨1141782, by rfl⟩ : syracuseStep 3044753 = 2283565) B2283565
theorem B2029835 : Blo 2029435 2029835 := bstep (se 1 (by rfl) ⟨1522376, by rfl⟩ : syracuseStep 2029835 = 3044753) B3044753
theorem B6850709 : Blo 2029435 6850709 := bbase (se 6 (by rfl) ⟨160563, by rfl⟩ : syracuseStep 6850709 = 321127) (by norm_num)
theorem B4567139 : Blo 2029435 4567139 := bstep (se 1 (by rfl) ⟨3425354, by rfl⟩ : syracuseStep 4567139 = 6850709) B6850709
theorem B3044759 : Blo 2029435 3044759 := bstep (se 1 (by rfl) ⟨2283569, by rfl⟩ : syracuseStep 3044759 = 4567139) B4567139
theorem B2029839 : Blo 2029435 2029839 := bstep (se 1 (by rfl) ⟨1522379, by rfl⟩ : syracuseStep 2029839 = 3044759) B3044759
theorem B3044765 : Blo 2029435 3044765 := bbase (se 3 (by rfl) ⟨570893, by rfl⟩ : syracuseStep 3044765 = 1141787) (by norm_num)
theorem B2029843 : Blo 2029435 2029843 := bstep (se 1 (by rfl) ⟨1522382, by rfl⟩ : syracuseStep 2029843 = 3044765) B3044765
theorem B4567157 : Blo 2029435 4567157 := bbase (se 5 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 4567157 = 428171) (by norm_num)
theorem B3044771 : Blo 2029435 3044771 := bstep (se 1 (by rfl) ⟨2283578, by rfl⟩ : syracuseStep 3044771 = 4567157) B4567157
theorem B2029847 : Blo 2029435 2029847 := bstep (se 1 (by rfl) ⟨1522385, by rfl⟩ : syracuseStep 2029847 = 3044771) B3044771
theorem B3906125 : Blo 2029435 3906125 := bbase (se 3 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 3906125 = 1464797) (by norm_num)
theorem B2604083 : Blo 2029435 2604083 := bstep (se 1 (by rfl) ⟨1953062, by rfl⟩ : syracuseStep 2604083 = 3906125) B3906125
theorem B6944221 : Blo 2029435 6944221 := bstep (se 3 (by rfl) ⟨1302041, by rfl⟩ : syracuseStep 6944221 = 2604083) B2604083
theorem B9258961 : Blo 2029435 9258961 := bstep (se 2 (by rfl) ⟨3472110, by rfl⟩ : syracuseStep 9258961 = 6944221) B6944221
theorem B12345281 : Blo 2029435 12345281 := bstep (se 2 (by rfl) ⟨4629480, by rfl⟩ : syracuseStep 12345281 = 9258961) B9258961
theorem B8230187 : Blo 2029435 8230187 := bstep (se 1 (by rfl) ⟨6172640, by rfl⟩ : syracuseStep 8230187 = 12345281) B12345281
theorem B5486791 : Blo 2029435 5486791 := bstep (se 1 (by rfl) ⟨4115093, by rfl⟩ : syracuseStep 5486791 = 8230187) B8230187
theorem B7315721 : Blo 2029435 7315721 := bstep (se 2 (by rfl) ⟨2743395, by rfl⟩ : syracuseStep 7315721 = 5486791) B5486791
theorem B4877147 : Blo 2029435 4877147 := bstep (se 1 (by rfl) ⟨3657860, by rfl⟩ : syracuseStep 4877147 = 7315721) B7315721
theorem B3251431 : Blo 2029435 3251431 := bstep (se 1 (by rfl) ⟨2438573, by rfl⟩ : syracuseStep 3251431 = 4877147) B4877147
theorem B17340965 : Blo 2029435 17340965 := bstep (se 4 (by rfl) ⟨1625715, by rfl⟩ : syracuseStep 17340965 = 3251431) B3251431
theorem B11560643 : Blo 2029435 11560643 := bstep (se 1 (by rfl) ⟨8670482, by rfl⟩ : syracuseStep 11560643 = 17340965) B17340965
theorem B7707095 : Blo 2029435 7707095 := bstep (se 1 (by rfl) ⟨5780321, by rfl⟩ : syracuseStep 7707095 = 11560643) B11560643
theorem B5138063 : Blo 2029435 5138063 := bstep (se 1 (by rfl) ⟨3853547, by rfl⟩ : syracuseStep 5138063 = 7707095) B7707095
theorem B3425375 : Blo 2029435 3425375 := bstep (se 1 (by rfl) ⟨2569031, by rfl⟩ : syracuseStep 3425375 = 5138063) B5138063
theorem B2283583 : Blo 2029435 2283583 := bstep (se 1 (by rfl) ⟨1712687, by rfl⟩ : syracuseStep 2283583 = 3425375) B3425375
theorem B3044777 : Blo 2029435 3044777 := bstep (se 2 (by rfl) ⟨1141791, by rfl⟩ : syracuseStep 3044777 = 2283583) B2283583
theorem B2029851 : Blo 2029435 2029851 := bstep (se 1 (by rfl) ⟨1522388, by rfl⟩ : syracuseStep 2029851 = 3044777) B3044777
theorem B7707109 : Blo 2029435 7707109 := bbase (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) (by norm_num)
theorem B10276145 : Blo 2029435 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B6850763 : Blo 2029435 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B4567175 : Blo 2029435 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B3044783 : Blo 2029435 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B2029855 : Blo 2029435 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B3044789 : Blo 2029435 3044789 := bbase (se 5 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 3044789 = 285449) (by norm_num)
theorem B2029859 : Blo 2029435 2029859 := bstep (se 1 (by rfl) ⟨1522394, by rfl⟩ : syracuseStep 2029859 = 3044789) B3044789
theorem B5138093 : Blo 2029435 5138093 := bbase (se 3 (by rfl) ⟨963392, by rfl⟩ : syracuseStep 5138093 = 1926785) (by norm_num)
theorem B3425395 : Blo 2029435 3425395 := bstep (se 1 (by rfl) ⟨2569046, by rfl⟩ : syracuseStep 3425395 = 5138093) B5138093
theorem B4567193 : Blo 2029435 4567193 := bstep (se 2 (by rfl) ⟨1712697, by rfl⟩ : syracuseStep 4567193 = 3425395) B3425395
theorem B3044795 : Blo 2029435 3044795 := bstep (se 1 (by rfl) ⟨2283596, by rfl⟩ : syracuseStep 3044795 = 4567193) B4567193
theorem B2029863 : Blo 2029435 2029863 := bstep (se 1 (by rfl) ⟨1522397, by rfl⟩ : syracuseStep 2029863 = 3044795) B3044795
theorem B2283601 : Blo 2029435 2283601 := bbase (se 2 (by rfl) ⟨856350, by rfl⟩ : syracuseStep 2283601 = 1712701) (by norm_num)
theorem B3044801 : Blo 2029435 3044801 := bstep (se 2 (by rfl) ⟨1141800, by rfl⟩ : syracuseStep 3044801 = 2283601) B2283601
theorem B2029867 : Blo 2029435 2029867 := bstep (se 1 (by rfl) ⟨1522400, by rfl⟩ : syracuseStep 2029867 = 3044801) B3044801
theorem B2890189 : Blo 2029435 2890189 := bbase (se 3 (by rfl) ⟨541910, by rfl⟩ : syracuseStep 2890189 = 1083821) (by norm_num)
theorem B3853585 : Blo 2029435 3853585 := bstep (se 2 (by rfl) ⟨1445094, by rfl⟩ : syracuseStep 3853585 = 2890189) B2890189
theorem B5138113 : Blo 2029435 5138113 := bstep (se 2 (by rfl) ⟨1926792, by rfl⟩ : syracuseStep 5138113 = 3853585) B3853585
theorem B6850817 : Blo 2029435 6850817 := bstep (se 2 (by rfl) ⟨2569056, by rfl⟩ : syracuseStep 6850817 = 5138113) B5138113
theorem B4567211 : Blo 2029435 4567211 := bstep (se 1 (by rfl) ⟨3425408, by rfl⟩ : syracuseStep 4567211 = 6850817) B6850817
theorem B3044807 : Blo 2029435 3044807 := bstep (se 1 (by rfl) ⟨2283605, by rfl⟩ : syracuseStep 3044807 = 4567211) B4567211
theorem B2029871 : Blo 2029435 2029871 := bstep (se 1 (by rfl) ⟨1522403, by rfl⟩ : syracuseStep 2029871 = 3044807) B3044807
theorem B3044813 : Blo 2029435 3044813 := bbase (se 3 (by rfl) ⟨570902, by rfl⟩ : syracuseStep 3044813 = 1141805) (by norm_num)
theorem B2029875 : Blo 2029435 2029875 := bstep (se 1 (by rfl) ⟨1522406, by rfl⟩ : syracuseStep 2029875 = 3044813) B3044813
theorem B4567229 : Blo 2029435 4567229 := bbase (se 3 (by rfl) ⟨856355, by rfl⟩ : syracuseStep 4567229 = 1712711) (by norm_num)
theorem B3044819 : Blo 2029435 3044819 := bstep (se 1 (by rfl) ⟨2283614, by rfl⟩ : syracuseStep 3044819 = 4567229) B4567229
theorem B2029879 : Blo 2029435 2029879 := bstep (se 1 (by rfl) ⟨1522409, by rfl⟩ : syracuseStep 2029879 = 3044819) B3044819
theorem B3425429 : Blo 2029435 3425429 := bbase (se 6 (by rfl) ⟨80283, by rfl⟩ : syracuseStep 3425429 = 160567) (by norm_num)
theorem B2283619 : Blo 2029435 2283619 := bstep (se 1 (by rfl) ⟨1712714, by rfl⟩ : syracuseStep 2283619 = 3425429) B3425429
theorem B3044825 : Blo 2029435 3044825 := bstep (se 2 (by rfl) ⟨1141809, by rfl⟩ : syracuseStep 3044825 = 2283619) B2283619
theorem B2029883 : Blo 2029435 2029883 := bstep (se 1 (by rfl) ⟨1522412, by rfl⟩ : syracuseStep 2029883 = 3044825) B3044825
theorem B2929645 : Blo 2029435 2929645 := bbase (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) (by norm_num)
theorem B3906193 : Blo 2029435 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B5208257 : Blo 2029435 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B13888685 : Blo 2029435 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B9259123 : Blo 2029435 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B12345497 : Blo 2029435 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B8230331 : Blo 2029435 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B5486887 : Blo 2029435 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B7315849 : Blo 2029435 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B9754465 : Blo 2029435 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B13005953 : Blo 2029435 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B8670635 : Blo 2029435 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B5780423 : Blo 2029435 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B15414461 : Blo 2029435 15414461 := bstep (se 3 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 15414461 = 5780423) B5780423
theorem B10276307 : Blo 2029435 10276307 := bstep (se 1 (by rfl) ⟨7707230, by rfl⟩ : syracuseStep 10276307 = 15414461) B15414461
theorem B6850871 : Blo 2029435 6850871 := bstep (se 1 (by rfl) ⟨5138153, by rfl⟩ : syracuseStep 6850871 = 10276307) B10276307
theorem B4567247 : Blo 2029435 4567247 := bstep (se 1 (by rfl) ⟨3425435, by rfl⟩ : syracuseStep 4567247 = 6850871) B6850871
theorem B3044831 : Blo 2029435 3044831 := bstep (se 1 (by rfl) ⟨2283623, by rfl⟩ : syracuseStep 3044831 = 4567247) B4567247
theorem B2029887 : Blo 2029435 2029887 := bstep (se 1 (by rfl) ⟨1522415, by rfl⟩ : syracuseStep 2029887 = 3044831) B3044831
theorem B3044837 : Blo 2029435 3044837 := bbase (se 4 (by rfl) ⟨285453, by rfl⟩ : syracuseStep 3044837 = 570907) (by norm_num)
theorem B2029891 : Blo 2029435 2029891 := bstep (se 1 (by rfl) ⟨1522418, by rfl⟩ : syracuseStep 2029891 = 3044837) B3044837
theorem B6256997 : Blo 2029435 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B4171331 : Blo 2029435 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B2780887 : Blo 2029435 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B3707849 : Blo 2029435 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B2471899 : Blo 2029435 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B3295865 : Blo 2029435 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B2197243 : Blo 2029435 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B2929657 : Blo 2029435 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B3906209 : Blo 2029435 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B2604139 : Blo 2029435 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B13888741 : Blo 2029435 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B18518321 : Blo 2029435 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B12345547 : Blo 2029435 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B16460729 : Blo 2029435 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B10973819 : Blo 2029435 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B29263517 : Blo 2029435 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B19509011 : Blo 2029435 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B13006007 : Blo 2029435 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B8670671 : Blo 2029435 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B5780447 : Blo 2029435 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B3853631 : Blo 2029435 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B2569087 : Blo 2029435 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B3425449 : Blo 2029435 3425449 := bstep (se 2 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 3425449 = 2569087) B2569087
theorem B4567265 : Blo 2029435 4567265 := bstep (se 2 (by rfl) ⟨1712724, by rfl⟩ : syracuseStep 4567265 = 3425449) B3425449
theorem B3044843 : Blo 2029435 3044843 := bstep (se 1 (by rfl) ⟨2283632, by rfl⟩ : syracuseStep 3044843 = 4567265) B4567265
theorem B2029895 : Blo 2029435 2029895 := bstep (se 1 (by rfl) ⟨1522421, by rfl⟩ : syracuseStep 2029895 = 3044843) B3044843
theorem B2283637 : Blo 2029435 2283637 := bbase (se 5 (by rfl) ⟨107045, by rfl⟩ : syracuseStep 2283637 = 214091) (by norm_num)
theorem B3044849 : Blo 2029435 3044849 := bstep (se 2 (by rfl) ⟨1141818, by rfl⟩ : syracuseStep 3044849 = 2283637) B2283637
theorem B2029899 : Blo 2029435 2029899 := bstep (se 1 (by rfl) ⟨1522424, by rfl⟩ : syracuseStep 2029899 = 3044849) B3044849
theorem B2569097 : Blo 2029435 2569097 := bbase (se 2 (by rfl) ⟨963411, by rfl⟩ : syracuseStep 2569097 = 1926823) (by norm_num)
theorem B6850925 : Blo 2029435 6850925 := bstep (se 3 (by rfl) ⟨1284548, by rfl⟩ : syracuseStep 6850925 = 2569097) B2569097
theorem B4567283 : Blo 2029435 4567283 := bstep (se 1 (by rfl) ⟨3425462, by rfl⟩ : syracuseStep 4567283 = 6850925) B6850925
theorem B3044855 : Blo 2029435 3044855 := bstep (se 1 (by rfl) ⟨2283641, by rfl⟩ : syracuseStep 3044855 = 4567283) B4567283
theorem B2029903 : Blo 2029435 2029903 := bstep (se 1 (by rfl) ⟨1522427, by rfl⟩ : syracuseStep 2029903 = 3044855) B3044855
theorem B3044861 : Blo 2029435 3044861 := bbase (se 3 (by rfl) ⟨570911, by rfl⟩ : syracuseStep 3044861 = 1141823) (by norm_num)
theorem B2029907 : Blo 2029435 2029907 := bstep (se 1 (by rfl) ⟨1522430, by rfl⟩ : syracuseStep 2029907 = 3044861) B3044861
theorem B4567301 : Blo 2029435 4567301 := bbase (se 4 (by rfl) ⟨428184, by rfl⟩ : syracuseStep 4567301 = 856369) (by norm_num)
theorem B3044867 : Blo 2029435 3044867 := bstep (se 1 (by rfl) ⟨2283650, by rfl⟩ : syracuseStep 3044867 = 4567301) B4567301
theorem B2029911 : Blo 2029435 2029911 := bstep (se 1 (by rfl) ⟨1522433, by rfl⟩ : syracuseStep 2029911 = 3044867) B3044867
theorem B3853669 : Blo 2029435 3853669 := bbase (se 4 (by rfl) ⟨361281, by rfl⟩ : syracuseStep 3853669 = 722563) (by norm_num)
theorem B5138225 : Blo 2029435 5138225 := bstep (se 2 (by rfl) ⟨1926834, by rfl⟩ : syracuseStep 5138225 = 3853669) B3853669
theorem B3425483 : Blo 2029435 3425483 := bstep (se 1 (by rfl) ⟨2569112, by rfl⟩ : syracuseStep 3425483 = 5138225) B5138225
theorem B2283655 : Blo 2029435 2283655 := bstep (se 1 (by rfl) ⟨1712741, by rfl⟩ : syracuseStep 2283655 = 3425483) B3425483
theorem B3044873 : Blo 2029435 3044873 := bstep (se 2 (by rfl) ⟨1141827, by rfl⟩ : syracuseStep 3044873 = 2283655) B2283655
theorem B2029915 : Blo 2029435 2029915 := bstep (se 1 (by rfl) ⟨1522436, by rfl⟩ : syracuseStep 2029915 = 3044873) B3044873
theorem B10276469 : Blo 2029435 10276469 := bbase (se 5 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 10276469 = 963419) (by norm_num)
theorem B6850979 : Blo 2029435 6850979 := bstep (se 1 (by rfl) ⟨5138234, by rfl⟩ : syracuseStep 6850979 = 10276469) B10276469
theorem B4567319 : Blo 2029435 4567319 := bstep (se 1 (by rfl) ⟨3425489, by rfl⟩ : syracuseStep 4567319 = 6850979) B6850979
theorem B3044879 : Blo 2029435 3044879 := bstep (se 1 (by rfl) ⟨2283659, by rfl⟩ : syracuseStep 3044879 = 4567319) B4567319
theorem B2029919 : Blo 2029435 2029919 := bstep (se 1 (by rfl) ⟨1522439, by rfl⟩ : syracuseStep 2029919 = 3044879) B3044879
theorem B3044885 : Blo 2029435 3044885 := bbase (se 6 (by rfl) ⟨71364, by rfl⟩ : syracuseStep 3044885 = 142729) (by norm_num)
theorem B2029923 : Blo 2029435 2029923 := bstep (se 1 (by rfl) ⟨1522442, by rfl⟩ : syracuseStep 2029923 = 3044885) B3044885
theorem B3657997 : Blo 2029435 3657997 := bbase (se 3 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 3657997 = 1371749) (by norm_num)
theorem B4877329 : Blo 2029435 4877329 := bstep (se 2 (by rfl) ⟨1828998, by rfl⟩ : syracuseStep 4877329 = 3657997) B3657997
theorem B6503105 : Blo 2029435 6503105 := bstep (se 2 (by rfl) ⟨2438664, by rfl⟩ : syracuseStep 6503105 = 4877329) B4877329
theorem B17341613 : Blo 2029435 17341613 := bstep (se 3 (by rfl) ⟨3251552, by rfl⟩ : syracuseStep 17341613 = 6503105) B6503105
theorem B11561075 : Blo 2029435 11561075 := bstep (se 1 (by rfl) ⟨8670806, by rfl⟩ : syracuseStep 11561075 = 17341613) B17341613
theorem B7707383 : Blo 2029435 7707383 := bstep (se 1 (by rfl) ⟨5780537, by rfl⟩ : syracuseStep 7707383 = 11561075) B11561075
theorem B5138255 : Blo 2029435 5138255 := bstep (se 1 (by rfl) ⟨3853691, by rfl⟩ : syracuseStep 5138255 = 7707383) B7707383
theorem B3425503 : Blo 2029435 3425503 := bstep (se 1 (by rfl) ⟨2569127, by rfl⟩ : syracuseStep 3425503 = 5138255) B5138255
theorem B4567337 : Blo 2029435 4567337 := bstep (se 2 (by rfl) ⟨1712751, by rfl⟩ : syracuseStep 4567337 = 3425503) B3425503
theorem B3044891 : Blo 2029435 3044891 := bstep (se 1 (by rfl) ⟨2283668, by rfl⟩ : syracuseStep 3044891 = 4567337) B4567337
theorem B2029927 : Blo 2029435 2029927 := bstep (se 1 (by rfl) ⟨1522445, by rfl⟩ : syracuseStep 2029927 = 3044891) B3044891
theorem B2283673 : Blo 2029435 2283673 := bbase (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) (by norm_num)
theorem B3044897 : Blo 2029435 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B2029931 : Blo 2029435 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B7707413 : Blo 2029435 7707413 := bbase (se 6 (by rfl) ⟨180642, by rfl⟩ : syracuseStep 7707413 = 361285) (by norm_num)
theorem B5138275 : Blo 2029435 5138275 := bstep (se 1 (by rfl) ⟨3853706, by rfl⟩ : syracuseStep 5138275 = 7707413) B7707413
theorem B6851033 : Blo 2029435 6851033 := bstep (se 2 (by rfl) ⟨2569137, by rfl⟩ : syracuseStep 6851033 = 5138275) B5138275
theorem B4567355 : Blo 2029435 4567355 := bstep (se 1 (by rfl) ⟨3425516, by rfl⟩ : syracuseStep 4567355 = 6851033) B6851033
theorem B3044903 : Blo 2029435 3044903 := bstep (se 1 (by rfl) ⟨2283677, by rfl⟩ : syracuseStep 3044903 = 4567355) B4567355
theorem B2029935 : Blo 2029435 2029935 := bstep (se 1 (by rfl) ⟨1522451, by rfl⟩ : syracuseStep 2029935 = 3044903) B3044903
theorem B3044909 : Blo 2029435 3044909 := bbase (se 3 (by rfl) ⟨570920, by rfl⟩ : syracuseStep 3044909 = 1141841) (by norm_num)
theorem B2029939 : Blo 2029435 2029939 := bstep (se 1 (by rfl) ⟨1522454, by rfl⟩ : syracuseStep 2029939 = 3044909) B3044909
theorem B4567373 : Blo 2029435 4567373 := bbase (se 3 (by rfl) ⟨856382, by rfl⟩ : syracuseStep 4567373 = 1712765) (by norm_num)
theorem B3044915 : Blo 2029435 3044915 := bstep (se 1 (by rfl) ⟨2283686, by rfl⟩ : syracuseStep 3044915 = 4567373) B4567373
theorem B2029943 : Blo 2029435 2029943 := bstep (se 1 (by rfl) ⟨1522457, by rfl⟩ : syracuseStep 2029943 = 3044915) B3044915
theorem B2569153 : Blo 2029435 2569153 := bbase (se 2 (by rfl) ⟨963432, by rfl⟩ : syracuseStep 2569153 = 1926865) (by norm_num)
theorem B3425537 : Blo 2029435 3425537 := bstep (se 2 (by rfl) ⟨1284576, by rfl⟩ : syracuseStep 3425537 = 2569153) B2569153
theorem B2283691 : Blo 2029435 2283691 := bstep (se 1 (by rfl) ⟨1712768, by rfl⟩ : syracuseStep 2283691 = 3425537) B3425537
theorem B3044921 : Blo 2029435 3044921 := bstep (se 2 (by rfl) ⟨1141845, by rfl⟩ : syracuseStep 3044921 = 2283691) B2283691
theorem B2029947 : Blo 2029435 2029947 := bstep (se 1 (by rfl) ⟨1522460, by rfl⟩ : syracuseStep 2029947 = 3044921) B3044921
theorem B5487061 : Blo 2029435 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B7316081 : Blo 2029435 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B4877387 : Blo 2029435 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B3251591 : Blo 2029435 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B2167727 : Blo 2029435 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B23122421 : Blo 2029435 23122421 := bstep (se 5 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 23122421 = 2167727) B2167727
theorem B15414947 : Blo 2029435 15414947 := bstep (se 1 (by rfl) ⟨11561210, by rfl⟩ : syracuseStep 15414947 = 23122421) B23122421
theorem B10276631 : Blo 2029435 10276631 := bstep (se 1 (by rfl) ⟨7707473, by rfl⟩ : syracuseStep 10276631 = 15414947) B15414947
theorem B6851087 : Blo 2029435 6851087 := bstep (se 1 (by rfl) ⟨5138315, by rfl⟩ : syracuseStep 6851087 = 10276631) B10276631
theorem B4567391 : Blo 2029435 4567391 := bstep (se 1 (by rfl) ⟨3425543, by rfl⟩ : syracuseStep 4567391 = 6851087) B6851087
theorem B3044927 : Blo 2029435 3044927 := bstep (se 1 (by rfl) ⟨2283695, by rfl⟩ : syracuseStep 3044927 = 4567391) B4567391
theorem B2029951 : Blo 2029435 2029951 := bstep (se 1 (by rfl) ⟨1522463, by rfl⟩ : syracuseStep 2029951 = 3044927) B3044927
theorem B3044933 : Blo 2029435 3044933 := bbase (se 4 (by rfl) ⟨285462, by rfl⟩ : syracuseStep 3044933 = 570925) (by norm_num)
theorem B2029955 : Blo 2029435 2029955 := bstep (se 1 (by rfl) ⟨1522466, by rfl⟩ : syracuseStep 2029955 = 3044933) B3044933
theorem B3425557 : Blo 2029435 3425557 := bbase (se 6 (by rfl) ⟨80286, by rfl⟩ : syracuseStep 3425557 = 160573) (by norm_num)
theorem B4567409 : Blo 2029435 4567409 := bstep (se 2 (by rfl) ⟨1712778, by rfl⟩ : syracuseStep 4567409 = 3425557) B3425557
theorem B3044939 : Blo 2029435 3044939 := bstep (se 1 (by rfl) ⟨2283704, by rfl⟩ : syracuseStep 3044939 = 4567409) B4567409
theorem B2029959 : Blo 2029435 2029959 := bstep (se 1 (by rfl) ⟨1522469, by rfl⟩ : syracuseStep 2029959 = 3044939) B3044939
theorem B2283709 : Blo 2029435 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B3044945 : Blo 2029435 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B2029963 : Blo 2029435 2029963 := bstep (se 1 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 2029963 = 3044945) B3044945
theorem B6851141 : Blo 2029435 6851141 := bbase (se 4 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 6851141 = 1284589) (by norm_num)
theorem B4567427 : Blo 2029435 4567427 := bstep (se 1 (by rfl) ⟨3425570, by rfl⟩ : syracuseStep 4567427 = 6851141) B6851141
theorem B3044951 : Blo 2029435 3044951 := bstep (se 1 (by rfl) ⟨2283713, by rfl⟩ : syracuseStep 3044951 = 4567427) B4567427
theorem B2029967 : Blo 2029435 2029967 := bstep (se 1 (by rfl) ⟨1522475, by rfl⟩ : syracuseStep 2029967 = 3044951) B3044951
theorem B3044957 : Blo 2029435 3044957 := bbase (se 3 (by rfl) ⟨570929, by rfl⟩ : syracuseStep 3044957 = 1141859) (by norm_num)
theorem B2029971 : Blo 2029435 2029971 := bstep (se 1 (by rfl) ⟨1522478, by rfl⟩ : syracuseStep 2029971 = 3044957) B3044957
theorem B4567445 : Blo 2029435 4567445 := bbase (se 6 (by rfl) ⟨107049, by rfl⟩ : syracuseStep 4567445 = 214099) (by norm_num)
theorem B3044963 : Blo 2029435 3044963 := bstep (se 1 (by rfl) ⟨2283722, by rfl⟩ : syracuseStep 3044963 = 4567445) B4567445
theorem B2029975 : Blo 2029435 2029975 := bstep (se 1 (by rfl) ⟨1522481, by rfl⟩ : syracuseStep 2029975 = 3044963) B3044963
theorem B4629773 : Blo 2029435 4629773 := bbase (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) (by norm_num)
theorem B3086515 : Blo 2029435 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B16461413 : Blo 2029435 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B10974275 : Blo 2029435 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B7316183 : Blo 2029435 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B4877455 : Blo 2029435 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B6503273 : Blo 2029435 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B4335515 : Blo 2029435 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B2890343 : Blo 2029435 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B7707581 : Blo 2029435 7707581 := bstep (se 3 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 7707581 = 2890343) B2890343
theorem B5138387 : Blo 2029435 5138387 := bstep (se 1 (by rfl) ⟨3853790, by rfl⟩ : syracuseStep 5138387 = 7707581) B7707581
theorem B3425591 : Blo 2029435 3425591 := bstep (se 1 (by rfl) ⟨2569193, by rfl⟩ : syracuseStep 3425591 = 5138387) B5138387
theorem B2283727 : Blo 2029435 2283727 := bstep (se 1 (by rfl) ⟨1712795, by rfl⟩ : syracuseStep 2283727 = 3425591) B3425591
theorem B3044969 : Blo 2029435 3044969 := bstep (se 2 (by rfl) ⟨1141863, by rfl⟩ : syracuseStep 3044969 = 2283727) B2283727
theorem B2029979 : Blo 2029435 2029979 := bstep (se 1 (by rfl) ⟨1522484, by rfl⟩ : syracuseStep 2029979 = 3044969) B3044969
theorem B8671045 : Blo 2029435 8671045 := bbase (se 4 (by rfl) ⟨812910, by rfl⟩ : syracuseStep 8671045 = 1625821) (by norm_num)
theorem B11561393 : Blo 2029435 11561393 := bstep (se 2 (by rfl) ⟨4335522, by rfl⟩ : syracuseStep 11561393 = 8671045) B8671045
theorem B7707595 : Blo 2029435 7707595 := bstep (se 1 (by rfl) ⟨5780696, by rfl⟩ : syracuseStep 7707595 = 11561393) B11561393
theorem B10276793 : Blo 2029435 10276793 := bstep (se 2 (by rfl) ⟨3853797, by rfl⟩ : syracuseStep 10276793 = 7707595) B7707595
theorem B6851195 : Blo 2029435 6851195 := bstep (se 1 (by rfl) ⟨5138396, by rfl⟩ : syracuseStep 6851195 = 10276793) B10276793
theorem B4567463 : Blo 2029435 4567463 := bstep (se 1 (by rfl) ⟨3425597, by rfl⟩ : syracuseStep 4567463 = 6851195) B6851195
theorem B3044975 : Blo 2029435 3044975 := bstep (se 1 (by rfl) ⟨2283731, by rfl⟩ : syracuseStep 3044975 = 4567463) B4567463
theorem B2029983 : Blo 2029435 2029983 := bstep (se 1 (by rfl) ⟨1522487, by rfl⟩ : syracuseStep 2029983 = 3044975) B3044975
theorem B3044981 : Blo 2029435 3044981 := bbase (se 5 (by rfl) ⟨142733, by rfl⟩ : syracuseStep 3044981 = 285467) (by norm_num)
theorem B2029987 : Blo 2029435 2029987 := bstep (se 1 (by rfl) ⟨1522490, by rfl⟩ : syracuseStep 2029987 = 3044981) B3044981
theorem B3853813 : Blo 2029435 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B5138417 : Blo 2029435 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B3425611 : Blo 2029435 3425611 := bstep (se 1 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 3425611 = 5138417) B5138417
theorem B4567481 : Blo 2029435 4567481 := bstep (se 2 (by rfl) ⟨1712805, by rfl⟩ : syracuseStep 4567481 = 3425611) B3425611
theorem B3044987 : Blo 2029435 3044987 := bstep (se 1 (by rfl) ⟨2283740, by rfl⟩ : syracuseStep 3044987 = 4567481) B4567481
theorem B2029991 : Blo 2029435 2029991 := bstep (se 1 (by rfl) ⟨1522493, by rfl⟩ : syracuseStep 2029991 = 3044987) B3044987
theorem B2283745 : Blo 2029435 2283745 := bbase (se 2 (by rfl) ⟨856404, by rfl⟩ : syracuseStep 2283745 = 1712809) (by norm_num)
theorem B3044993 : Blo 2029435 3044993 := bstep (se 2 (by rfl) ⟨1141872, by rfl⟩ : syracuseStep 3044993 = 2283745) B2283745
theorem B2029995 : Blo 2029435 2029995 := bstep (se 1 (by rfl) ⟨1522496, by rfl⟩ : syracuseStep 2029995 = 3044993) B3044993
theorem B5138437 : Blo 2029435 5138437 := bbase (se 4 (by rfl) ⟨481728, by rfl⟩ : syracuseStep 5138437 = 963457) (by norm_num)
theorem B6851249 : Blo 2029435 6851249 := bstep (se 2 (by rfl) ⟨2569218, by rfl⟩ : syracuseStep 6851249 = 5138437) B5138437
theorem B4567499 : Blo 2029435 4567499 := bstep (se 1 (by rfl) ⟨3425624, by rfl⟩ : syracuseStep 4567499 = 6851249) B6851249
theorem B3044999 : Blo 2029435 3044999 := bstep (se 1 (by rfl) ⟨2283749, by rfl⟩ : syracuseStep 3044999 = 4567499) B4567499
theorem B2029999 : Blo 2029435 2029999 := bstep (se 1 (by rfl) ⟨1522499, by rfl⟩ : syracuseStep 2029999 = 3044999) B3044999
theorem B3045005 : Blo 2029435 3045005 := bbase (se 3 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 3045005 = 1141877) (by norm_num)
theorem B2030003 : Blo 2029435 2030003 := bstep (se 1 (by rfl) ⟨1522502, by rfl⟩ : syracuseStep 2030003 = 3045005) B3045005
theorem B4567517 : Blo 2029435 4567517 := bbase (se 3 (by rfl) ⟨856409, by rfl⟩ : syracuseStep 4567517 = 1712819) (by norm_num)
theorem B3045011 : Blo 2029435 3045011 := bstep (se 1 (by rfl) ⟨2283758, by rfl⟩ : syracuseStep 3045011 = 4567517) B4567517
theorem B2030007 : Blo 2029435 2030007 := bstep (se 1 (by rfl) ⟨1522505, by rfl⟩ : syracuseStep 2030007 = 3045011) B3045011
theorem B3425645 : Blo 2029435 3425645 := bbase (se 3 (by rfl) ⟨642308, by rfl⟩ : syracuseStep 3425645 = 1284617) (by norm_num)
theorem B2283763 : Blo 2029435 2283763 := bstep (se 1 (by rfl) ⟨1712822, by rfl⟩ : syracuseStep 2283763 = 3425645) B3425645
theorem B3045017 : Blo 2029435 3045017 := bstep (se 2 (by rfl) ⟨1141881, by rfl⟩ : syracuseStep 3045017 = 2283763) B2283763
theorem B2030011 : Blo 2029435 2030011 := bstep (se 1 (by rfl) ⟨1522508, by rfl⟩ : syracuseStep 2030011 = 3045017) B3045017
theorem B2929829 : Blo 2029435 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B7812877 : Blo 2029435 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B10417169 : Blo 2029435 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B6944779 : Blo 2029435 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B9259705 : Blo 2029435 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B12346273 : Blo 2029435 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B65846789 : Blo 2029435 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B43897859 : Blo 2029435 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B29265239 : Blo 2029435 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B19510159 : Blo 2029435 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B26013545 : Blo 2029435 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B17342363 : Blo 2029435 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B11561575 : Blo 2029435 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B15415433 : Blo 2029435 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B10276955 : Blo 2029435 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B6851303 : Blo 2029435 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B4567535 : Blo 2029435 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B3045023 : Blo 2029435 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B2030015 : Blo 2029435 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B3045029 : Blo 2029435 3045029 := bbase (se 4 (by rfl) ⟨285471, by rfl⟩ : syracuseStep 3045029 = 570943) (by norm_num)
theorem B2030019 : Blo 2029435 2030019 := bstep (se 1 (by rfl) ⟨1522514, by rfl⟩ : syracuseStep 2030019 = 3045029) B3045029
theorem B2569249 : Blo 2029435 2569249 := bbase (se 2 (by rfl) ⟨963468, by rfl⟩ : syracuseStep 2569249 = 1926937) (by norm_num)
theorem B3425665 : Blo 2029435 3425665 := bstep (se 2 (by rfl) ⟨1284624, by rfl⟩ : syracuseStep 3425665 = 2569249) B2569249
theorem B4567553 : Blo 2029435 4567553 := bstep (se 2 (by rfl) ⟨1712832, by rfl⟩ : syracuseStep 4567553 = 3425665) B3425665
theorem B3045035 : Blo 2029435 3045035 := bstep (se 1 (by rfl) ⟨2283776, by rfl⟩ : syracuseStep 3045035 = 4567553) B4567553
theorem B2030023 : Blo 2029435 2030023 := bstep (se 1 (by rfl) ⟨1522517, by rfl⟩ : syracuseStep 2030023 = 3045035) B3045035
theorem B2283781 : Blo 2029435 2283781 := bbase (se 4 (by rfl) ⟨214104, by rfl⟩ : syracuseStep 2283781 = 428209) (by norm_num)
theorem B3045041 : Blo 2029435 3045041 := bstep (se 2 (by rfl) ⟨1141890, by rfl⟩ : syracuseStep 3045041 = 2283781) B2283781
theorem B2030027 : Blo 2029435 2030027 := bstep (se 1 (by rfl) ⟨1522520, by rfl⟩ : syracuseStep 2030027 = 3045041) B3045041
theorem B2167813 : Blo 2029435 2167813 := bbase (se 4 (by rfl) ⟨203232, by rfl⟩ : syracuseStep 2167813 = 406465) (by norm_num)
theorem B2890417 : Blo 2029435 2890417 := bstep (se 2 (by rfl) ⟨1083906, by rfl⟩ : syracuseStep 2890417 = 2167813) B2167813
theorem B3853889 : Blo 2029435 3853889 := bstep (se 2 (by rfl) ⟨1445208, by rfl⟩ : syracuseStep 3853889 = 2890417) B2890417
theorem B2569259 : Blo 2029435 2569259 := bstep (se 1 (by rfl) ⟨1926944, by rfl⟩ : syracuseStep 2569259 = 3853889) B3853889
theorem B6851357 : Blo 2029435 6851357 := bstep (se 3 (by rfl) ⟨1284629, by rfl⟩ : syracuseStep 6851357 = 2569259) B2569259
theorem B4567571 : Blo 2029435 4567571 := bstep (se 1 (by rfl) ⟨3425678, by rfl⟩ : syracuseStep 4567571 = 6851357) B6851357
theorem B3045047 : Blo 2029435 3045047 := bstep (se 1 (by rfl) ⟨2283785, by rfl⟩ : syracuseStep 3045047 = 4567571) B4567571
theorem B2030031 : Blo 2029435 2030031 := bstep (se 1 (by rfl) ⟨1522523, by rfl⟩ : syracuseStep 2030031 = 3045047) B3045047
theorem B3045053 : Blo 2029435 3045053 := bbase (se 3 (by rfl) ⟨570947, by rfl⟩ : syracuseStep 3045053 = 1141895) (by norm_num)
theorem B2030035 : Blo 2029435 2030035 := bstep (se 1 (by rfl) ⟨1522526, by rfl⟩ : syracuseStep 2030035 = 3045053) B3045053
theorem B4567589 : Blo 2029435 4567589 := bbase (se 4 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 4567589 = 856423) (by norm_num)
theorem B3045059 : Blo 2029435 3045059 := bstep (se 1 (by rfl) ⟨2283794, by rfl⟩ : syracuseStep 3045059 = 4567589) B4567589
theorem B2030039 : Blo 2029435 2030039 := bstep (se 1 (by rfl) ⟨1522529, by rfl⟩ : syracuseStep 2030039 = 3045059) B3045059
theorem B5138549 : Blo 2029435 5138549 := bbase (se 5 (by rfl) ⟨240869, by rfl⟩ : syracuseStep 5138549 = 481739) (by norm_num)
theorem B3425699 : Blo 2029435 3425699 := bstep (se 1 (by rfl) ⟨2569274, by rfl⟩ : syracuseStep 3425699 = 5138549) B5138549
theorem B2283799 : Blo 2029435 2283799 := bstep (se 1 (by rfl) ⟨1712849, by rfl⟩ : syracuseStep 2283799 = 3425699) B3425699
theorem B3045065 : Blo 2029435 3045065 := bstep (se 2 (by rfl) ⟨1141899, by rfl⟩ : syracuseStep 3045065 = 2283799) B2283799
theorem B2030043 : Blo 2029435 2030043 := bstep (se 1 (by rfl) ⟨1522532, by rfl⟩ : syracuseStep 2030043 = 3045065) B3045065
theorem B3658213 : Blo 2029435 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B19510469 : Blo 2029435 19510469 := bstep (se 4 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 19510469 = 3658213) B3658213
theorem B13006979 : Blo 2029435 13006979 := bstep (se 1 (by rfl) ⟨9755234, by rfl⟩ : syracuseStep 13006979 = 19510469) B19510469
theorem B8671319 : Blo 2029435 8671319 := bstep (se 1 (by rfl) ⟨6503489, by rfl⟩ : syracuseStep 8671319 = 13006979) B13006979
theorem B5780879 : Blo 2029435 5780879 := bstep (se 1 (by rfl) ⟨4335659, by rfl⟩ : syracuseStep 5780879 = 8671319) B8671319
theorem B3853919 : Blo 2029435 3853919 := bstep (se 1 (by rfl) ⟨2890439, by rfl⟩ : syracuseStep 3853919 = 5780879) B5780879
theorem B10277117 : Blo 2029435 10277117 := bstep (se 3 (by rfl) ⟨1926959, by rfl⟩ : syracuseStep 10277117 = 3853919) B3853919
theorem B6851411 : Blo 2029435 6851411 := bstep (se 1 (by rfl) ⟨5138558, by rfl⟩ : syracuseStep 6851411 = 10277117) B10277117
theorem B4567607 : Blo 2029435 4567607 := bstep (se 1 (by rfl) ⟨3425705, by rfl⟩ : syracuseStep 4567607 = 6851411) B6851411
theorem B3045071 : Blo 2029435 3045071 := bstep (se 1 (by rfl) ⟨2283803, by rfl⟩ : syracuseStep 3045071 = 4567607) B4567607
theorem B2030047 : Blo 2029435 2030047 := bstep (se 1 (by rfl) ⟨1522535, by rfl⟩ : syracuseStep 2030047 = 3045071) B3045071
theorem B3045077 : Blo 2029435 3045077 := bbase (se 7 (by rfl) ⟨35684, by rfl⟩ : syracuseStep 3045077 = 71369) (by norm_num)
theorem B2030051 : Blo 2029435 2030051 := bstep (se 1 (by rfl) ⟨1522538, by rfl⟩ : syracuseStep 2030051 = 3045077) B3045077
theorem B4335677 : Blo 2029435 4335677 := bbase (se 3 (by rfl) ⟨812939, by rfl⟩ : syracuseStep 4335677 = 1625879) (by norm_num)
theorem B2890451 : Blo 2029435 2890451 := bstep (se 1 (by rfl) ⟨2167838, by rfl⟩ : syracuseStep 2890451 = 4335677) B4335677
theorem B7707869 : Blo 2029435 7707869 := bstep (se 3 (by rfl) ⟨1445225, by rfl⟩ : syracuseStep 7707869 = 2890451) B2890451
theorem B5138579 : Blo 2029435 5138579 := bstep (se 1 (by rfl) ⟨3853934, by rfl⟩ : syracuseStep 5138579 = 7707869) B7707869
theorem B3425719 : Blo 2029435 3425719 := bstep (se 1 (by rfl) ⟨2569289, by rfl⟩ : syracuseStep 3425719 = 5138579) B5138579
theorem B4567625 : Blo 2029435 4567625 := bstep (se 2 (by rfl) ⟨1712859, by rfl⟩ : syracuseStep 4567625 = 3425719) B3425719
theorem B3045083 : Blo 2029435 3045083 := bstep (se 1 (by rfl) ⟨2283812, by rfl⟩ : syracuseStep 3045083 = 4567625) B4567625
theorem B2030055 : Blo 2029435 2030055 := bstep (se 1 (by rfl) ⟨1522541, by rfl⟩ : syracuseStep 2030055 = 3045083) B3045083
theorem B2283817 : Blo 2029435 2283817 := bbase (se 2 (by rfl) ⟨856431, by rfl⟩ : syracuseStep 2283817 = 1712863) (by norm_num)
theorem B3045089 : Blo 2029435 3045089 := bstep (se 2 (by rfl) ⟨1141908, by rfl⟩ : syracuseStep 3045089 = 2283817) B2283817
theorem B2030059 : Blo 2029435 2030059 := bstep (se 1 (by rfl) ⟨1522544, by rfl⟩ : syracuseStep 2030059 = 3045089) B3045089
theorem B9259925 : Blo 2029435 9259925 := bbase (se 6 (by rfl) ⟨217029, by rfl⟩ : syracuseStep 9259925 = 434059) (by norm_num)
theorem B24693133 : Blo 2029435 24693133 := bstep (se 3 (by rfl) ⟨4629962, by rfl⟩ : syracuseStep 24693133 = 9259925) B9259925
theorem B32924177 : Blo 2029435 32924177 := bstep (se 2 (by rfl) ⟨12346566, by rfl⟩ : syracuseStep 32924177 = 24693133) B24693133
theorem B21949451 : Blo 2029435 21949451 := bstep (se 1 (by rfl) ⟨16462088, by rfl⟩ : syracuseStep 21949451 = 32924177) B32924177
theorem B14632967 : Blo 2029435 14632967 := bstep (se 1 (by rfl) ⟨10974725, by rfl⟩ : syracuseStep 14632967 = 21949451) B21949451
theorem B9755311 : Blo 2029435 9755311 := bstep (se 1 (by rfl) ⟨7316483, by rfl⟩ : syracuseStep 9755311 = 14632967) B14632967
theorem B13007081 : Blo 2029435 13007081 := bstep (se 2 (by rfl) ⟨4877655, by rfl⟩ : syracuseStep 13007081 = 9755311) B9755311
theorem B8671387 : Blo 2029435 8671387 := bstep (se 1 (by rfl) ⟨6503540, by rfl⟩ : syracuseStep 8671387 = 13007081) B13007081
theorem B11561849 : Blo 2029435 11561849 := bstep (se 2 (by rfl) ⟨4335693, by rfl⟩ : syracuseStep 11561849 = 8671387) B8671387
theorem B7707899 : Blo 2029435 7707899 := bstep (se 1 (by rfl) ⟨5780924, by rfl⟩ : syracuseStep 7707899 = 11561849) B11561849
theorem B5138599 : Blo 2029435 5138599 := bstep (se 1 (by rfl) ⟨3853949, by rfl⟩ : syracuseStep 5138599 = 7707899) B7707899
theorem B6851465 : Blo 2029435 6851465 := bstep (se 2 (by rfl) ⟨2569299, by rfl⟩ : syracuseStep 6851465 = 5138599) B5138599
theorem B4567643 : Blo 2029435 4567643 := bstep (se 1 (by rfl) ⟨3425732, by rfl⟩ : syracuseStep 4567643 = 6851465) B6851465
theorem B3045095 : Blo 2029435 3045095 := bstep (se 1 (by rfl) ⟨2283821, by rfl⟩ : syracuseStep 3045095 = 4567643) B4567643
theorem B2030063 : Blo 2029435 2030063 := bstep (se 1 (by rfl) ⟨1522547, by rfl⟩ : syracuseStep 2030063 = 3045095) B3045095
theorem B3045101 : Blo 2029435 3045101 := bbase (se 3 (by rfl) ⟨570956, by rfl⟩ : syracuseStep 3045101 = 1141913) (by norm_num)
theorem B2030067 : Blo 2029435 2030067 := bstep (se 1 (by rfl) ⟨1522550, by rfl⟩ : syracuseStep 2030067 = 3045101) B3045101
theorem B4567661 : Blo 2029435 4567661 := bbase (se 3 (by rfl) ⟨856436, by rfl⟩ : syracuseStep 4567661 = 1712873) (by norm_num)
theorem B3045107 : Blo 2029435 3045107 := bstep (se 1 (by rfl) ⟨2283830, by rfl⟩ : syracuseStep 3045107 = 4567661) B4567661
theorem B2030071 : Blo 2029435 2030071 := bstep (se 1 (by rfl) ⟨1522553, by rfl⟩ : syracuseStep 2030071 = 3045107) B3045107
theorem B3853973 : Blo 2029435 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B2569315 : Blo 2029435 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B3425753 : Blo 2029435 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B2283835 : Blo 2029435 2283835 := bstep (se 1 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 2283835 = 3425753) B3425753
theorem B3045113 : Blo 2029435 3045113 := bstep (se 2 (by rfl) ⟨1141917, by rfl⟩ : syracuseStep 3045113 = 2283835) B2283835
theorem B2030075 : Blo 2029435 2030075 := bstep (se 1 (by rfl) ⟨1522556, by rfl⟩ : syracuseStep 2030075 = 3045113) B3045113
theorem B111119957 : Blo 2029435 111119957 := bbase (se 8 (by rfl) ⟨651093, by rfl⟩ : syracuseStep 111119957 = 1302187) (by norm_num)
theorem B74079971 : Blo 2029435 74079971 := bstep (se 1 (by rfl) ⟨55559978, by rfl⟩ : syracuseStep 74079971 = 111119957) B111119957
theorem B49386647 : Blo 2029435 49386647 := bstep (se 1 (by rfl) ⟨37039985, by rfl⟩ : syracuseStep 49386647 = 74079971) B74079971
theorem B32924431 : Blo 2029435 32924431 := bstep (se 1 (by rfl) ⟨24693323, by rfl⟩ : syracuseStep 32924431 = 49386647) B49386647
theorem B43899241 : Blo 2029435 43899241 := bstep (se 2 (by rfl) ⟨16462215, by rfl⟩ : syracuseStep 43899241 = 32924431) B32924431
theorem B58532321 : Blo 2029435 58532321 := bstep (se 2 (by rfl) ⟨21949620, by rfl⟩ : syracuseStep 58532321 = 43899241) B43899241
theorem B39021547 : Blo 2029435 39021547 := bstep (se 1 (by rfl) ⟨29266160, by rfl⟩ : syracuseStep 39021547 = 58532321) B58532321
theorem B52028729 : Blo 2029435 52028729 := bstep (se 2 (by rfl) ⟨19510773, by rfl⟩ : syracuseStep 52028729 = 39021547) B39021547
theorem B34685819 : Blo 2029435 34685819 := bstep (se 1 (by rfl) ⟨26014364, by rfl⟩ : syracuseStep 34685819 = 52028729) B52028729
theorem B23123879 : Blo 2029435 23123879 := bstep (se 1 (by rfl) ⟨17342909, by rfl⟩ : syracuseStep 23123879 = 34685819) B34685819
theorem B15415919 : Blo 2029435 15415919 := bstep (se 1 (by rfl) ⟨11561939, by rfl⟩ : syracuseStep 15415919 = 23123879) B23123879
theorem B10277279 : Blo 2029435 10277279 := bstep (se 1 (by rfl) ⟨7707959, by rfl⟩ : syracuseStep 10277279 = 15415919) B15415919
theorem B6851519 : Blo 2029435 6851519 := bstep (se 1 (by rfl) ⟨5138639, by rfl⟩ : syracuseStep 6851519 = 10277279) B10277279
theorem B4567679 : Blo 2029435 4567679 := bstep (se 1 (by rfl) ⟨3425759, by rfl⟩ : syracuseStep 4567679 = 6851519) B6851519
theorem B3045119 : Blo 2029435 3045119 := bstep (se 1 (by rfl) ⟨2283839, by rfl⟩ : syracuseStep 3045119 = 4567679) B4567679
theorem B2030079 : Blo 2029435 2030079 := bstep (se 1 (by rfl) ⟨1522559, by rfl⟩ : syracuseStep 2030079 = 3045119) B3045119
theorem B3045125 : Blo 2029435 3045125 := bbase (se 4 (by rfl) ⟨285480, by rfl⟩ : syracuseStep 3045125 = 570961) (by norm_num)
theorem B2030083 : Blo 2029435 2030083 := bstep (se 1 (by rfl) ⟨1522562, by rfl⟩ : syracuseStep 2030083 = 3045125) B3045125
theorem B3425773 : Blo 2029435 3425773 := bbase (se 3 (by rfl) ⟨642332, by rfl⟩ : syracuseStep 3425773 = 1284665) (by norm_num)
theorem B4567697 : Blo 2029435 4567697 := bstep (se 2 (by rfl) ⟨1712886, by rfl⟩ : syracuseStep 4567697 = 3425773) B3425773
theorem B3045131 : Blo 2029435 3045131 := bstep (se 1 (by rfl) ⟨2283848, by rfl⟩ : syracuseStep 3045131 = 4567697) B4567697
theorem B2030087 : Blo 2029435 2030087 := bstep (se 1 (by rfl) ⟨1522565, by rfl⟩ : syracuseStep 2030087 = 3045131) B3045131
theorem B2283853 : Blo 2029435 2283853 := bbase (se 3 (by rfl) ⟨428222, by rfl⟩ : syracuseStep 2283853 = 856445) (by norm_num)
theorem B3045137 : Blo 2029435 3045137 := bstep (se 2 (by rfl) ⟨1141926, by rfl⟩ : syracuseStep 3045137 = 2283853) B2283853
theorem B2030091 : Blo 2029435 2030091 := bstep (se 1 (by rfl) ⟨1522568, by rfl⟩ : syracuseStep 2030091 = 3045137) B3045137
theorem B6851573 : Blo 2029435 6851573 := bbase (se 5 (by rfl) ⟨321167, by rfl⟩ : syracuseStep 6851573 = 642335) (by norm_num)
theorem B4567715 : Blo 2029435 4567715 := bstep (se 1 (by rfl) ⟨3425786, by rfl⟩ : syracuseStep 4567715 = 6851573) B6851573
theorem B3045143 : Blo 2029435 3045143 := bstep (se 1 (by rfl) ⟨2283857, by rfl⟩ : syracuseStep 3045143 = 4567715) B4567715
theorem B2030095 : Blo 2029435 2030095 := bstep (se 1 (by rfl) ⟨1522571, by rfl⟩ : syracuseStep 2030095 = 3045143) B3045143
theorem B3045149 : Blo 2029435 3045149 := bbase (se 3 (by rfl) ⟨570965, by rfl⟩ : syracuseStep 3045149 = 1141931) (by norm_num)
theorem B2030099 : Blo 2029435 2030099 := bstep (se 1 (by rfl) ⟨1522574, by rfl⟩ : syracuseStep 2030099 = 3045149) B3045149
theorem B4567733 : Blo 2029435 4567733 := bbase (se 5 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 4567733 = 428225) (by norm_num)
theorem B3045155 : Blo 2029435 3045155 := bstep (se 1 (by rfl) ⟨2283866, by rfl⟩ : syracuseStep 3045155 = 4567733) B4567733
theorem B2030103 : Blo 2029435 2030103 := bstep (se 1 (by rfl) ⟨1522577, by rfl⟩ : syracuseStep 2030103 = 3045155) B3045155
theorem B11562101 : Blo 2029435 11562101 := bbase (se 5 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 11562101 = 1083947) (by norm_num)
theorem B7708067 : Blo 2029435 7708067 := bstep (se 1 (by rfl) ⟨5781050, by rfl⟩ : syracuseStep 7708067 = 11562101) B11562101
theorem B5138711 : Blo 2029435 5138711 := bstep (se 1 (by rfl) ⟨3854033, by rfl⟩ : syracuseStep 5138711 = 7708067) B7708067
theorem B3425807 : Blo 2029435 3425807 := bstep (se 1 (by rfl) ⟨2569355, by rfl⟩ : syracuseStep 3425807 = 5138711) B5138711
theorem B2283871 : Blo 2029435 2283871 := bstep (se 1 (by rfl) ⟨1712903, by rfl⟩ : syracuseStep 2283871 = 3425807) B3425807
theorem B3045161 : Blo 2029435 3045161 := bstep (se 2 (by rfl) ⟨1141935, by rfl⟩ : syracuseStep 3045161 = 2283871) B2283871
theorem B2030107 : Blo 2029435 2030107 := bstep (se 1 (by rfl) ⟨1522580, by rfl⟩ : syracuseStep 2030107 = 3045161) B3045161
theorem B5781061 : Blo 2029435 5781061 := bbase (se 4 (by rfl) ⟨541974, by rfl⟩ : syracuseStep 5781061 = 1083949) (by norm_num)
theorem B7708081 : Blo 2029435 7708081 := bstep (se 2 (by rfl) ⟨2890530, by rfl⟩ : syracuseStep 7708081 = 5781061) B5781061
theorem B10277441 : Blo 2029435 10277441 := bstep (se 2 (by rfl) ⟨3854040, by rfl⟩ : syracuseStep 10277441 = 7708081) B7708081
theorem B6851627 : Blo 2029435 6851627 := bstep (se 1 (by rfl) ⟨5138720, by rfl⟩ : syracuseStep 6851627 = 10277441) B10277441
theorem B4567751 : Blo 2029435 4567751 := bstep (se 1 (by rfl) ⟨3425813, by rfl⟩ : syracuseStep 4567751 = 6851627) B6851627
theorem B3045167 : Blo 2029435 3045167 := bstep (se 1 (by rfl) ⟨2283875, by rfl⟩ : syracuseStep 3045167 = 4567751) B4567751
theorem B2030111 : Blo 2029435 2030111 := bstep (se 1 (by rfl) ⟨1522583, by rfl⟩ : syracuseStep 2030111 = 3045167) B3045167
theorem B3045173 : Blo 2029435 3045173 := bbase (se 5 (by rfl) ⟨142742, by rfl⟩ : syracuseStep 3045173 = 285485) (by norm_num)
theorem B2030115 : Blo 2029435 2030115 := bstep (se 1 (by rfl) ⟨1522586, by rfl⟩ : syracuseStep 2030115 = 3045173) B3045173
theorem B5138741 : Blo 2029435 5138741 := bbase (se 5 (by rfl) ⟨240878, by rfl⟩ : syracuseStep 5138741 = 481757) (by norm_num)
theorem B3425827 : Blo 2029435 3425827 := bstep (se 1 (by rfl) ⟨2569370, by rfl⟩ : syracuseStep 3425827 = 5138741) B5138741
theorem B4567769 : Blo 2029435 4567769 := bstep (se 2 (by rfl) ⟨1712913, by rfl⟩ : syracuseStep 4567769 = 3425827) B3425827
theorem B3045179 : Blo 2029435 3045179 := bstep (se 1 (by rfl) ⟨2283884, by rfl⟩ : syracuseStep 3045179 = 4567769) B4567769
theorem B2030119 : Blo 2029435 2030119 := bstep (se 1 (by rfl) ⟨1522589, by rfl⟩ : syracuseStep 2030119 = 3045179) B3045179
theorem B2283889 : Blo 2029435 2283889 := bbase (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) (by norm_num)
theorem B3045185 : Blo 2029435 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B2030123 : Blo 2029435 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B2438905 : Blo 2029435 2438905 := bbase (se 2 (by rfl) ⟨914589, by rfl⟩ : syracuseStep 2438905 = 1829179) (by norm_num)
theorem B3251873 : Blo 2029435 3251873 := bstep (se 2 (by rfl) ⟨1219452, by rfl⟩ : syracuseStep 3251873 = 2438905) B2438905
theorem B8671661 : Blo 2029435 8671661 := bstep (se 3 (by rfl) ⟨1625936, by rfl⟩ : syracuseStep 8671661 = 3251873) B3251873
theorem B5781107 : Blo 2029435 5781107 := bstep (se 1 (by rfl) ⟨4335830, by rfl⟩ : syracuseStep 5781107 = 8671661) B8671661
theorem B3854071 : Blo 2029435 3854071 := bstep (se 1 (by rfl) ⟨2890553, by rfl⟩ : syracuseStep 3854071 = 5781107) B5781107
theorem B5138761 : Blo 2029435 5138761 := bstep (se 2 (by rfl) ⟨1927035, by rfl⟩ : syracuseStep 5138761 = 3854071) B3854071
theorem B6851681 : Blo 2029435 6851681 := bstep (se 2 (by rfl) ⟨2569380, by rfl⟩ : syracuseStep 6851681 = 5138761) B5138761
theorem B4567787 : Blo 2029435 4567787 := bstep (se 1 (by rfl) ⟨3425840, by rfl⟩ : syracuseStep 4567787 = 6851681) B6851681
theorem B3045191 : Blo 2029435 3045191 := bstep (se 1 (by rfl) ⟨2283893, by rfl⟩ : syracuseStep 3045191 = 4567787) B4567787
theorem B2030127 : Blo 2029435 2030127 := bstep (se 1 (by rfl) ⟨1522595, by rfl⟩ : syracuseStep 2030127 = 3045191) B3045191
theorem B3045197 : Blo 2029435 3045197 := bbase (se 3 (by rfl) ⟨570974, by rfl⟩ : syracuseStep 3045197 = 1141949) (by norm_num)
theorem B2030131 : Blo 2029435 2030131 := bstep (se 1 (by rfl) ⟨1522598, by rfl⟩ : syracuseStep 2030131 = 3045197) B3045197
theorem B4567805 : Blo 2029435 4567805 := bbase (se 3 (by rfl) ⟨856463, by rfl⟩ : syracuseStep 4567805 = 1712927) (by norm_num)
theorem B3045203 : Blo 2029435 3045203 := bstep (se 1 (by rfl) ⟨2283902, by rfl⟩ : syracuseStep 3045203 = 4567805) B4567805
theorem B2030135 : Blo 2029435 2030135 := bstep (se 1 (by rfl) ⟨1522601, by rfl⟩ : syracuseStep 2030135 = 3045203) B3045203
theorem B3425861 : Blo 2029435 3425861 := bbase (se 4 (by rfl) ⟨321174, by rfl⟩ : syracuseStep 3425861 = 642349) (by norm_num)
theorem B2283907 : Blo 2029435 2283907 := bstep (se 1 (by rfl) ⟨1712930, by rfl⟩ : syracuseStep 2283907 = 3425861) B3425861
theorem B3045209 : Blo 2029435 3045209 := bstep (se 2 (by rfl) ⟨1141953, by rfl⟩ : syracuseStep 3045209 = 2283907) B2283907
theorem B2030139 : Blo 2029435 2030139 := bstep (se 1 (by rfl) ⟨1522604, by rfl⟩ : syracuseStep 2030139 = 3045209) B3045209
theorem B15416405 : Blo 2029435 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B10277603 : Blo 2029435 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B6851735 : Blo 2029435 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B4567823 : Blo 2029435 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B3045215 : Blo 2029435 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B2030143 : Blo 2029435 2030143 := bstep (se 1 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 2030143 = 3045215) B3045215
theorem B3045221 : Blo 2029435 3045221 := bbase (se 4 (by rfl) ⟨285489, by rfl⟩ : syracuseStep 3045221 = 570979) (by norm_num)
theorem B2030147 : Blo 2029435 2030147 := bstep (se 1 (by rfl) ⟨1522610, by rfl⟩ : syracuseStep 2030147 = 3045221) B3045221
theorem B3854117 : Blo 2029435 3854117 := bbase (se 4 (by rfl) ⟨361323, by rfl⟩ : syracuseStep 3854117 = 722647) (by norm_num)
theorem B2569411 : Blo 2029435 2569411 := bstep (se 1 (by rfl) ⟨1927058, by rfl⟩ : syracuseStep 2569411 = 3854117) B3854117
theorem B3425881 : Blo 2029435 3425881 := bstep (se 2 (by rfl) ⟨1284705, by rfl⟩ : syracuseStep 3425881 = 2569411) B2569411
theorem B4567841 : Blo 2029435 4567841 := bstep (se 2 (by rfl) ⟨1712940, by rfl⟩ : syracuseStep 4567841 = 3425881) B3425881
theorem B3045227 : Blo 2029435 3045227 := bstep (se 1 (by rfl) ⟨2283920, by rfl⟩ : syracuseStep 3045227 = 4567841) B4567841
theorem B2030151 : Blo 2029435 2030151 := bstep (se 1 (by rfl) ⟨1522613, by rfl⟩ : syracuseStep 2030151 = 3045227) B3045227
theorem B2283925 : Blo 2029435 2283925 := bbase (se 6 (by rfl) ⟨53529, by rfl⟩ : syracuseStep 2283925 = 107059) (by norm_num)
theorem B3045233 : Blo 2029435 3045233 := bstep (se 2 (by rfl) ⟨1141962, by rfl⟩ : syracuseStep 3045233 = 2283925) B2283925
theorem B2030155 : Blo 2029435 2030155 := bstep (se 1 (by rfl) ⟨1522616, by rfl⟩ : syracuseStep 2030155 = 3045233) B3045233
theorem B2569421 : Blo 2029435 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B6851789 : Blo 2029435 6851789 := bstep (se 3 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 6851789 = 2569421) B2569421
theorem B4567859 : Blo 2029435 4567859 := bstep (se 1 (by rfl) ⟨3425894, by rfl⟩ : syracuseStep 4567859 = 6851789) B6851789
theorem B3045239 : Blo 2029435 3045239 := bstep (se 1 (by rfl) ⟨2283929, by rfl⟩ : syracuseStep 3045239 = 4567859) B4567859
theorem B2030159 : Blo 2029435 2030159 := bstep (se 1 (by rfl) ⟨1522619, by rfl⟩ : syracuseStep 2030159 = 3045239) B3045239
theorem B3045245 : Blo 2029435 3045245 := bbase (se 3 (by rfl) ⟨570983, by rfl⟩ : syracuseStep 3045245 = 1141967) (by norm_num)
theorem B2030163 : Blo 2029435 2030163 := bstep (se 1 (by rfl) ⟨1522622, by rfl⟩ : syracuseStep 2030163 = 3045245) B3045245
theorem B4567877 : Blo 2029435 4567877 := bbase (se 4 (by rfl) ⟨428238, by rfl⟩ : syracuseStep 4567877 = 856477) (by norm_num)
theorem B3045251 : Blo 2029435 3045251 := bstep (se 1 (by rfl) ⟨2283938, by rfl⟩ : syracuseStep 3045251 = 4567877) B4567877
theorem B2030167 : Blo 2029435 2030167 := bstep (se 1 (by rfl) ⟨1522625, by rfl⟩ : syracuseStep 2030167 = 3045251) B3045251
theorem B4335925 : Blo 2029435 4335925 := bbase (se 5 (by rfl) ⟨203246, by rfl⟩ : syracuseStep 4335925 = 406493) (by norm_num)
theorem B5781233 : Blo 2029435 5781233 := bstep (se 2 (by rfl) ⟨2167962, by rfl⟩ : syracuseStep 5781233 = 4335925) B4335925
theorem B3854155 : Blo 2029435 3854155 := bstep (se 1 (by rfl) ⟨2890616, by rfl⟩ : syracuseStep 3854155 = 5781233) B5781233
theorem B5138873 : Blo 2029435 5138873 := bstep (se 2 (by rfl) ⟨1927077, by rfl⟩ : syracuseStep 5138873 = 3854155) B3854155
theorem B3425915 : Blo 2029435 3425915 := bstep (se 1 (by rfl) ⟨2569436, by rfl⟩ : syracuseStep 3425915 = 5138873) B5138873
theorem B2283943 : Blo 2029435 2283943 := bstep (se 1 (by rfl) ⟨1712957, by rfl⟩ : syracuseStep 2283943 = 3425915) B3425915
theorem B3045257 : Blo 2029435 3045257 := bstep (se 2 (by rfl) ⟨1141971, by rfl⟩ : syracuseStep 3045257 = 2283943) B2283943
theorem B2030171 : Blo 2029435 2030171 := bstep (se 1 (by rfl) ⟨1522628, by rfl⟩ : syracuseStep 2030171 = 3045257) B3045257
theorem B10277765 : Blo 2029435 10277765 := bbase (se 4 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 10277765 = 1927081) (by norm_num)
theorem B6851843 : Blo 2029435 6851843 := bstep (se 1 (by rfl) ⟨5138882, by rfl⟩ : syracuseStep 6851843 = 10277765) B10277765
theorem B4567895 : Blo 2029435 4567895 := bstep (se 1 (by rfl) ⟨3425921, by rfl⟩ : syracuseStep 4567895 = 6851843) B6851843
theorem B3045263 : Blo 2029435 3045263 := bstep (se 1 (by rfl) ⟨2283947, by rfl⟩ : syracuseStep 3045263 = 4567895) B4567895
theorem B2030175 : Blo 2029435 2030175 := bstep (se 1 (by rfl) ⟨1522631, by rfl⟩ : syracuseStep 2030175 = 3045263) B3045263
theorem B3045269 : Blo 2029435 3045269 := bbase (se 6 (by rfl) ⟨71373, by rfl⟩ : syracuseStep 3045269 = 142747) (by norm_num)
theorem B2030179 : Blo 2029435 2030179 := bstep (se 1 (by rfl) ⟨1522634, by rfl⟩ : syracuseStep 2030179 = 3045269) B3045269
theorem B3296333 : Blo 2029435 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B8790221 : Blo 2029435 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B5860147 : Blo 2029435 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B7813529 : Blo 2029435 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B5209019 : Blo 2029435 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B3472679 : Blo 2029435 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B9260477 : Blo 2029435 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B6173651 : Blo 2029435 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B4115767 : Blo 2029435 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B5487689 : Blo 2029435 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B3658459 : Blo 2029435 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B4877945 : Blo 2029435 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B3251963 : Blo 2029435 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B2167975 : Blo 2029435 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B11562533 : Blo 2029435 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B7708355 : Blo 2029435 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B5138903 : Blo 2029435 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B3425935 : Blo 2029435 3425935 := bstep (se 1 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 3425935 = 5138903) B5138903
theorem B4567913 : Blo 2029435 4567913 := bstep (se 2 (by rfl) ⟨1712967, by rfl⟩ : syracuseStep 4567913 = 3425935) B3425935
theorem B3045275 : Blo 2029435 3045275 := bstep (se 1 (by rfl) ⟨2283956, by rfl⟩ : syracuseStep 3045275 = 4567913) B4567913
theorem B2030183 : Blo 2029435 2030183 := bstep (se 1 (by rfl) ⟨1522637, by rfl⟩ : syracuseStep 2030183 = 3045275) B3045275
theorem B2283961 : Blo 2029435 2283961 := bbase (se 2 (by rfl) ⟨856485, by rfl⟩ : syracuseStep 2283961 = 1712971) (by norm_num)
theorem B3045281 : Blo 2029435 3045281 := bstep (se 2 (by rfl) ⟨1141980, by rfl⟩ : syracuseStep 3045281 = 2283961) B2283961
theorem B2030187 : Blo 2029435 2030187 := bstep (se 1 (by rfl) ⟨1522640, by rfl⟩ : syracuseStep 2030187 = 3045281) B3045281
theorem B3086837 : Blo 2029435 3086837 := bbase (se 5 (by rfl) ⟨144695, by rfl⟩ : syracuseStep 3086837 = 289391) (by norm_num)
theorem B2057891 : Blo 2029435 2057891 := bstep (se 1 (by rfl) ⟨1543418, by rfl⟩ : syracuseStep 2057891 = 3086837) B3086837
theorem B21950837 : Blo 2029435 21950837 := bstep (se 5 (by rfl) ⟨1028945, by rfl⟩ : syracuseStep 21950837 = 2057891) B2057891
theorem B14633891 : Blo 2029435 14633891 := bstep (se 1 (by rfl) ⟨10975418, by rfl⟩ : syracuseStep 14633891 = 21950837) B21950837
theorem B9755927 : Blo 2029435 9755927 := bstep (se 1 (by rfl) ⟨7316945, by rfl⟩ : syracuseStep 9755927 = 14633891) B14633891
theorem B6503951 : Blo 2029435 6503951 := bstep (se 1 (by rfl) ⟨4877963, by rfl⟩ : syracuseStep 6503951 = 9755927) B9755927
theorem B4335967 : Blo 2029435 4335967 := bstep (se 1 (by rfl) ⟨3251975, by rfl⟩ : syracuseStep 4335967 = 6503951) B6503951
theorem B5781289 : Blo 2029435 5781289 := bstep (se 2 (by rfl) ⟨2167983, by rfl⟩ : syracuseStep 5781289 = 4335967) B4335967
theorem B7708385 : Blo 2029435 7708385 := bstep (se 2 (by rfl) ⟨2890644, by rfl⟩ : syracuseStep 7708385 = 5781289) B5781289
theorem B5138923 : Blo 2029435 5138923 := bstep (se 1 (by rfl) ⟨3854192, by rfl⟩ : syracuseStep 5138923 = 7708385) B7708385
theorem B6851897 : Blo 2029435 6851897 := bstep (se 2 (by rfl) ⟨2569461, by rfl⟩ : syracuseStep 6851897 = 5138923) B5138923
theorem B4567931 : Blo 2029435 4567931 := bstep (se 1 (by rfl) ⟨3425948, by rfl⟩ : syracuseStep 4567931 = 6851897) B6851897
theorem B3045287 : Blo 2029435 3045287 := bstep (se 1 (by rfl) ⟨2283965, by rfl⟩ : syracuseStep 3045287 = 4567931) B4567931
theorem B2030191 : Blo 2029435 2030191 := bstep (se 1 (by rfl) ⟨1522643, by rfl⟩ : syracuseStep 2030191 = 3045287) B3045287
theorem B3045293 : Blo 2029435 3045293 := bbase (se 3 (by rfl) ⟨570992, by rfl⟩ : syracuseStep 3045293 = 1141985) (by norm_num)
theorem B2030195 : Blo 2029435 2030195 := bstep (se 1 (by rfl) ⟨1522646, by rfl⟩ : syracuseStep 2030195 = 3045293) B3045293
theorem B4567949 : Blo 2029435 4567949 := bbase (se 3 (by rfl) ⟨856490, by rfl⟩ : syracuseStep 4567949 = 1712981) (by norm_num)
theorem B3045299 : Blo 2029435 3045299 := bstep (se 1 (by rfl) ⟨2283974, by rfl⟩ : syracuseStep 3045299 = 4567949) B4567949
theorem B2030199 : Blo 2029435 2030199 := bstep (se 1 (by rfl) ⟨1522649, by rfl⟩ : syracuseStep 2030199 = 3045299) B3045299
theorem B2569477 : Blo 2029435 2569477 := bbase (se 4 (by rfl) ⟨240888, by rfl⟩ : syracuseStep 2569477 = 481777) (by norm_num)
theorem B3425969 : Blo 2029435 3425969 := bstep (se 2 (by rfl) ⟨1284738, by rfl⟩ : syracuseStep 3425969 = 2569477) B2569477
theorem B2283979 : Blo 2029435 2283979 := bstep (se 1 (by rfl) ⟨1712984, by rfl⟩ : syracuseStep 2283979 = 3425969) B3425969
theorem B3045305 : Blo 2029435 3045305 := bstep (se 2 (by rfl) ⟨1141989, by rfl⟩ : syracuseStep 3045305 = 2283979) B2283979
theorem B2030203 : Blo 2029435 2030203 := bstep (se 1 (by rfl) ⟨1522652, by rfl⟩ : syracuseStep 2030203 = 3045305) B3045305
theorem B3658501 : Blo 2029435 3658501 := bbase (se 4 (by rfl) ⟨342984, by rfl⟩ : syracuseStep 3658501 = 685969) (by norm_num)
theorem B4878001 : Blo 2029435 4878001 := bstep (se 2 (by rfl) ⟨1829250, by rfl⟩ : syracuseStep 4878001 = 3658501) B3658501
theorem B26016005 : Blo 2029435 26016005 := bstep (se 4 (by rfl) ⟨2439000, by rfl⟩ : syracuseStep 26016005 = 4878001) B4878001
theorem B17344003 : Blo 2029435 17344003 := bstep (se 1 (by rfl) ⟨13008002, by rfl⟩ : syracuseStep 17344003 = 26016005) B26016005
theorem B23125337 : Blo 2029435 23125337 := bstep (se 2 (by rfl) ⟨8672001, by rfl⟩ : syracuseStep 23125337 = 17344003) B17344003
theorem B15416891 : Blo 2029435 15416891 := bstep (se 1 (by rfl) ⟨11562668, by rfl⟩ : syracuseStep 15416891 = 23125337) B23125337
theorem B10277927 : Blo 2029435 10277927 := bstep (se 1 (by rfl) ⟨7708445, by rfl⟩ : syracuseStep 10277927 = 15416891) B15416891
theorem B6851951 : Blo 2029435 6851951 := bstep (se 1 (by rfl) ⟨5138963, by rfl⟩ : syracuseStep 6851951 = 10277927) B10277927
theorem B4567967 : Blo 2029435 4567967 := bstep (se 1 (by rfl) ⟨3425975, by rfl⟩ : syracuseStep 4567967 = 6851951) B6851951
theorem B3045311 : Blo 2029435 3045311 := bstep (se 1 (by rfl) ⟨2283983, by rfl⟩ : syracuseStep 3045311 = 4567967) B4567967
theorem B2030207 : Blo 2029435 2030207 := bstep (se 1 (by rfl) ⟨1522655, by rfl⟩ : syracuseStep 2030207 = 3045311) B3045311
theorem B3045317 : Blo 2029435 3045317 := bbase (se 4 (by rfl) ⟨285498, by rfl⟩ : syracuseStep 3045317 = 570997) (by norm_num)
theorem B2030211 : Blo 2029435 2030211 := bstep (se 1 (by rfl) ⟨1522658, by rfl⟩ : syracuseStep 2030211 = 3045317) B3045317
theorem B3425989 : Blo 2029435 3425989 := bbase (se 4 (by rfl) ⟨321186, by rfl⟩ : syracuseStep 3425989 = 642373) (by norm_num)
theorem B4567985 : Blo 2029435 4567985 := bstep (se 2 (by rfl) ⟨1712994, by rfl⟩ : syracuseStep 4567985 = 3425989) B3425989
theorem B3045323 : Blo 2029435 3045323 := bstep (se 1 (by rfl) ⟨2283992, by rfl⟩ : syracuseStep 3045323 = 4567985) B4567985
theorem B2030215 : Blo 2029435 2030215 := bstep (se 1 (by rfl) ⟨1522661, by rfl⟩ : syracuseStep 2030215 = 3045323) B3045323
theorem B2283997 : Blo 2029435 2283997 := bbase (se 3 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 2283997 = 856499) (by norm_num)
theorem B3045329 : Blo 2029435 3045329 := bstep (se 2 (by rfl) ⟨1141998, by rfl⟩ : syracuseStep 3045329 = 2283997) B2283997
theorem B2030219 : Blo 2029435 2030219 := bstep (se 1 (by rfl) ⟨1522664, by rfl⟩ : syracuseStep 2030219 = 3045329) B3045329
theorem B6852005 : Blo 2029435 6852005 := bbase (se 4 (by rfl) ⟨642375, by rfl⟩ : syracuseStep 6852005 = 1284751) (by norm_num)
theorem B4568003 : Blo 2029435 4568003 := bstep (se 1 (by rfl) ⟨3426002, by rfl⟩ : syracuseStep 4568003 = 6852005) B6852005
theorem B3045335 : Blo 2029435 3045335 := bstep (se 1 (by rfl) ⟨2284001, by rfl⟩ : syracuseStep 3045335 = 4568003) B4568003
theorem B2030223 : Blo 2029435 2030223 := bstep (se 1 (by rfl) ⟨1522667, by rfl⟩ : syracuseStep 2030223 = 3045335) B3045335
theorem B3045341 : Blo 2029435 3045341 := bbase (se 3 (by rfl) ⟨571001, by rfl⟩ : syracuseStep 3045341 = 1142003) (by norm_num)
theorem B2030227 : Blo 2029435 2030227 := bstep (se 1 (by rfl) ⟨1522670, by rfl⟩ : syracuseStep 2030227 = 3045341) B3045341
theorem B4568021 : Blo 2029435 4568021 := bbase (se 7 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 4568021 = 107063) (by norm_num)
theorem B3045347 : Blo 2029435 3045347 := bstep (se 1 (by rfl) ⟨2284010, by rfl⟩ : syracuseStep 3045347 = 4568021) B4568021
theorem B2030231 : Blo 2029435 2030231 := bstep (se 1 (by rfl) ⟨1522673, by rfl⟩ : syracuseStep 2030231 = 3045347) B3045347
theorem B76121045 : Blo 2029435 76121045 := bbase (se 7 (by rfl) ⟨892043, by rfl⟩ : syracuseStep 76121045 = 1784087) (by norm_num)
theorem B50747363 : Blo 2029435 50747363 := bstep (se 1 (by rfl) ⟨38060522, by rfl⟩ : syracuseStep 50747363 = 76121045) B76121045
theorem B33831575 : Blo 2029435 33831575 := bstep (se 1 (by rfl) ⟨25373681, by rfl⟩ : syracuseStep 33831575 = 50747363) B50747363
theorem B22554383 : Blo 2029435 22554383 := bstep (se 1 (by rfl) ⟨16915787, by rfl⟩ : syracuseStep 22554383 = 33831575) B33831575
theorem B60145021 : Blo 2029435 60145021 := bstep (se 3 (by rfl) ⟨11277191, by rfl⟩ : syracuseStep 60145021 = 22554383) B22554383
theorem B80193361 : Blo 2029435 80193361 := bstep (se 2 (by rfl) ⟨30072510, by rfl⟩ : syracuseStep 80193361 = 60145021) B60145021
theorem B106924481 : Blo 2029435 106924481 := bstep (se 2 (by rfl) ⟨40096680, by rfl⟩ : syracuseStep 106924481 = 80193361) B80193361
theorem B71282987 : Blo 2029435 71282987 := bstep (se 1 (by rfl) ⟨53462240, by rfl⟩ : syracuseStep 71282987 = 106924481) B106924481
theorem B47521991 : Blo 2029435 47521991 := bstep (se 1 (by rfl) ⟨35641493, by rfl⟩ : syracuseStep 47521991 = 71282987) B71282987
theorem B31681327 : Blo 2029435 31681327 := bstep (se 1 (by rfl) ⟨23760995, by rfl⟩ : syracuseStep 31681327 = 47521991) B47521991
theorem B42241769 : Blo 2029435 42241769 := bstep (se 2 (by rfl) ⟨15840663, by rfl⟩ : syracuseStep 42241769 = 31681327) B31681327
theorem B28161179 : Blo 2029435 28161179 := bstep (se 1 (by rfl) ⟨21120884, by rfl⟩ : syracuseStep 28161179 = 42241769) B42241769
theorem B18774119 : Blo 2029435 18774119 := bstep (se 1 (by rfl) ⟨14080589, by rfl⟩ : syracuseStep 18774119 = 28161179) B28161179
theorem B50064317 : Blo 2029435 50064317 := bstep (se 3 (by rfl) ⟨9387059, by rfl⟩ : syracuseStep 50064317 = 18774119) B18774119
theorem B33376211 : Blo 2029435 33376211 := bstep (se 1 (by rfl) ⟨25032158, by rfl⟩ : syracuseStep 33376211 = 50064317) B50064317
theorem B22250807 : Blo 2029435 22250807 := bstep (se 1 (by rfl) ⟨16688105, by rfl⟩ : syracuseStep 22250807 = 33376211) B33376211
theorem B14833871 : Blo 2029435 14833871 := bstep (se 1 (by rfl) ⟨11125403, by rfl⟩ : syracuseStep 14833871 = 22250807) B22250807
theorem B9889247 : Blo 2029435 9889247 := bstep (se 1 (by rfl) ⟨7416935, by rfl⟩ : syracuseStep 9889247 = 14833871) B14833871
theorem B26371325 : Blo 2029435 26371325 := bstep (se 3 (by rfl) ⟨4944623, by rfl⟩ : syracuseStep 26371325 = 9889247) B9889247
theorem B17580883 : Blo 2029435 17580883 := bstep (se 1 (by rfl) ⟨13185662, by rfl⟩ : syracuseStep 17580883 = 26371325) B26371325
theorem B23441177 : Blo 2029435 23441177 := bstep (se 2 (by rfl) ⟨8790441, by rfl⟩ : syracuseStep 23441177 = 17580883) B17580883
theorem B62509805 : Blo 2029435 62509805 := bstep (se 3 (by rfl) ⟨11720588, by rfl⟩ : syracuseStep 62509805 = 23441177) B23441177
theorem B41673203 : Blo 2029435 41673203 := bstep (se 1 (by rfl) ⟨31254902, by rfl⟩ : syracuseStep 41673203 = 62509805) B62509805
theorem B27782135 : Blo 2029435 27782135 := bstep (se 1 (by rfl) ⟨20836601, by rfl⟩ : syracuseStep 27782135 = 41673203) B41673203
theorem B18521423 : Blo 2029435 18521423 := bstep (se 1 (by rfl) ⟨13891067, by rfl⟩ : syracuseStep 18521423 = 27782135) B27782135
theorem B12347615 : Blo 2029435 12347615 := bstep (se 1 (by rfl) ⟨9260711, by rfl⟩ : syracuseStep 12347615 = 18521423) B18521423
theorem B8231743 : Blo 2029435 8231743 := bstep (se 1 (by rfl) ⟨6173807, by rfl⟩ : syracuseStep 8231743 = 12347615) B12347615
theorem B10975657 : Blo 2029435 10975657 := bstep (se 2 (by rfl) ⟨4115871, by rfl⟩ : syracuseStep 10975657 = 8231743) B8231743
theorem B14634209 : Blo 2029435 14634209 := bstep (se 2 (by rfl) ⟨5487828, by rfl⟩ : syracuseStep 14634209 = 10975657) B10975657
theorem B9756139 : Blo 2029435 9756139 := bstep (se 1 (by rfl) ⟨7317104, by rfl⟩ : syracuseStep 9756139 = 14634209) B14634209
theorem B13008185 : Blo 2029435 13008185 := bstep (se 2 (by rfl) ⟨4878069, by rfl⟩ : syracuseStep 13008185 = 9756139) B9756139
theorem B8672123 : Blo 2029435 8672123 := bstep (se 1 (by rfl) ⟨6504092, by rfl⟩ : syracuseStep 8672123 = 13008185) B13008185
theorem B5781415 : Blo 2029435 5781415 := bstep (se 1 (by rfl) ⟨4336061, by rfl⟩ : syracuseStep 5781415 = 8672123) B8672123
theorem B7708553 : Blo 2029435 7708553 := bstep (se 2 (by rfl) ⟨2890707, by rfl⟩ : syracuseStep 7708553 = 5781415) B5781415
theorem B5139035 : Blo 2029435 5139035 := bstep (se 1 (by rfl) ⟨3854276, by rfl⟩ : syracuseStep 5139035 = 7708553) B7708553
theorem B3426023 : Blo 2029435 3426023 := bstep (se 1 (by rfl) ⟨2569517, by rfl⟩ : syracuseStep 3426023 = 5139035) B5139035
theorem B2284015 : Blo 2029435 2284015 := bstep (se 1 (by rfl) ⟨1713011, by rfl⟩ : syracuseStep 2284015 = 3426023) B3426023
theorem B3045353 : Blo 2029435 3045353 := bstep (se 2 (by rfl) ⟨1142007, by rfl⟩ : syracuseStep 3045353 = 2284015) B2284015
theorem B2030235 : Blo 2029435 2030235 := bstep (se 1 (by rfl) ⟨1522676, by rfl⟩ : syracuseStep 2030235 = 3045353) B3045353
theorem B17344277 : Blo 2029435 17344277 := bbase (se 6 (by rfl) ⟨406506, by rfl⟩ : syracuseStep 17344277 = 813013) (by norm_num)
theorem B11562851 : Blo 2029435 11562851 := bstep (se 1 (by rfl) ⟨8672138, by rfl⟩ : syracuseStep 11562851 = 17344277) B17344277
theorem B7708567 : Blo 2029435 7708567 := bstep (se 1 (by rfl) ⟨5781425, by rfl⟩ : syracuseStep 7708567 = 11562851) B11562851
theorem B10278089 : Blo 2029435 10278089 := bstep (se 2 (by rfl) ⟨3854283, by rfl⟩ : syracuseStep 10278089 = 7708567) B7708567
theorem B6852059 : Blo 2029435 6852059 := bstep (se 1 (by rfl) ⟨5139044, by rfl⟩ : syracuseStep 6852059 = 10278089) B10278089
theorem B4568039 : Blo 2029435 4568039 := bstep (se 1 (by rfl) ⟨3426029, by rfl⟩ : syracuseStep 4568039 = 6852059) B6852059
theorem B3045359 : Blo 2029435 3045359 := bstep (se 1 (by rfl) ⟨2284019, by rfl⟩ : syracuseStep 3045359 = 4568039) B4568039
theorem B2030239 : Blo 2029435 2030239 := bstep (se 1 (by rfl) ⟨1522679, by rfl⟩ : syracuseStep 2030239 = 3045359) B3045359
theorem B3045365 : Blo 2029435 3045365 := bbase (se 5 (by rfl) ⟨142751, by rfl⟩ : syracuseStep 3045365 = 285503) (by norm_num)
theorem B2030243 : Blo 2029435 2030243 := bstep (se 1 (by rfl) ⟨1522682, by rfl⟩ : syracuseStep 2030243 = 3045365) B3045365
theorem B9756197 : Blo 2029435 9756197 := bbase (se 4 (by rfl) ⟨914643, by rfl⟩ : syracuseStep 9756197 = 1829287) (by norm_num)
theorem B6504131 : Blo 2029435 6504131 := bstep (se 1 (by rfl) ⟨4878098, by rfl⟩ : syracuseStep 6504131 = 9756197) B9756197
theorem B4336087 : Blo 2029435 4336087 := bstep (se 1 (by rfl) ⟨3252065, by rfl⟩ : syracuseStep 4336087 = 6504131) B6504131
theorem B5781449 : Blo 2029435 5781449 := bstep (se 2 (by rfl) ⟨2168043, by rfl⟩ : syracuseStep 5781449 = 4336087) B4336087
theorem B3854299 : Blo 2029435 3854299 := bstep (se 1 (by rfl) ⟨2890724, by rfl⟩ : syracuseStep 3854299 = 5781449) B5781449
theorem B5139065 : Blo 2029435 5139065 := bstep (se 2 (by rfl) ⟨1927149, by rfl⟩ : syracuseStep 5139065 = 3854299) B3854299
theorem B3426043 : Blo 2029435 3426043 := bstep (se 1 (by rfl) ⟨2569532, by rfl⟩ : syracuseStep 3426043 = 5139065) B5139065
theorem B4568057 : Blo 2029435 4568057 := bstep (se 2 (by rfl) ⟨1713021, by rfl⟩ : syracuseStep 4568057 = 3426043) B3426043
theorem B3045371 : Blo 2029435 3045371 := bstep (se 1 (by rfl) ⟨2284028, by rfl⟩ : syracuseStep 3045371 = 4568057) B4568057
theorem B2030247 : Blo 2029435 2030247 := bstep (se 1 (by rfl) ⟨1522685, by rfl⟩ : syracuseStep 2030247 = 3045371) B3045371
theorem B2284033 : Blo 2029435 2284033 := bbase (se 2 (by rfl) ⟨856512, by rfl⟩ : syracuseStep 2284033 = 1713025) (by norm_num)
theorem B3045377 : Blo 2029435 3045377 := bstep (se 2 (by rfl) ⟨1142016, by rfl⟩ : syracuseStep 3045377 = 2284033) B2284033
theorem B2030251 : Blo 2029435 2030251 := bstep (se 1 (by rfl) ⟨1522688, by rfl⟩ : syracuseStep 2030251 = 3045377) B3045377
theorem B5139085 : Blo 2029435 5139085 := bbase (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) (by norm_num)
theorem B6852113 : Blo 2029435 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B4568075 : Blo 2029435 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B3045383 : Blo 2029435 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B2030255 : Blo 2029435 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B3045389 : Blo 2029435 3045389 := bbase (se 3 (by rfl) ⟨571010, by rfl⟩ : syracuseStep 3045389 = 1142021) (by norm_num)
theorem B2030259 : Blo 2029435 2030259 := bstep (se 1 (by rfl) ⟨1522694, by rfl⟩ : syracuseStep 2030259 = 3045389) B3045389
theorem B4568093 : Blo 2029435 4568093 := bbase (se 3 (by rfl) ⟨856517, by rfl⟩ : syracuseStep 4568093 = 1713035) (by norm_num)
theorem B3045395 : Blo 2029435 3045395 := bstep (se 1 (by rfl) ⟨2284046, by rfl⟩ : syracuseStep 3045395 = 4568093) B4568093
theorem B2030263 : Blo 2029435 2030263 := bstep (se 1 (by rfl) ⟨1522697, by rfl⟩ : syracuseStep 2030263 = 3045395) B3045395
theorem B3426077 : Blo 2029435 3426077 := bbase (se 3 (by rfl) ⟨642389, by rfl⟩ : syracuseStep 3426077 = 1284779) (by norm_num)
theorem B2284051 : Blo 2029435 2284051 := bstep (se 1 (by rfl) ⟨1713038, by rfl⟩ : syracuseStep 2284051 = 3426077) B3426077
theorem B3045401 : Blo 2029435 3045401 := bstep (se 2 (by rfl) ⟨1142025, by rfl⟩ : syracuseStep 3045401 = 2284051) B2284051
theorem B2030267 : Blo 2029435 2030267 := bstep (se 1 (by rfl) ⟨1522700, by rfl⟩ : syracuseStep 2030267 = 3045401) B3045401
theorem B5487925 : Blo 2029435 5487925 := bbase (se 5 (by rfl) ⟨257246, by rfl⟩ : syracuseStep 5487925 = 514493) (by norm_num)
theorem B7317233 : Blo 2029435 7317233 := bstep (se 2 (by rfl) ⟨2743962, by rfl⟩ : syracuseStep 7317233 = 5487925) B5487925
theorem B4878155 : Blo 2029435 4878155 := bstep (se 1 (by rfl) ⟨3658616, by rfl⟩ : syracuseStep 4878155 = 7317233) B7317233
theorem B13008413 : Blo 2029435 13008413 := bstep (se 3 (by rfl) ⟨2439077, by rfl⟩ : syracuseStep 13008413 = 4878155) B4878155
theorem B8672275 : Blo 2029435 8672275 := bstep (se 1 (by rfl) ⟨6504206, by rfl⟩ : syracuseStep 8672275 = 13008413) B13008413
theorem B11563033 : Blo 2029435 11563033 := bstep (se 2 (by rfl) ⟨4336137, by rfl⟩ : syracuseStep 11563033 = 8672275) B8672275
theorem B15417377 : Blo 2029435 15417377 := bstep (se 2 (by rfl) ⟨5781516, by rfl⟩ : syracuseStep 15417377 = 11563033) B11563033
theorem B10278251 : Blo 2029435 10278251 := bstep (se 1 (by rfl) ⟨7708688, by rfl⟩ : syracuseStep 10278251 = 15417377) B15417377
theorem B6852167 : Blo 2029435 6852167 := bstep (se 1 (by rfl) ⟨5139125, by rfl⟩ : syracuseStep 6852167 = 10278251) B10278251
theorem B4568111 : Blo 2029435 4568111 := bstep (se 1 (by rfl) ⟨3426083, by rfl⟩ : syracuseStep 4568111 = 6852167) B6852167
theorem B3045407 : Blo 2029435 3045407 := bstep (se 1 (by rfl) ⟨2284055, by rfl⟩ : syracuseStep 3045407 = 4568111) B4568111
theorem B2030271 : Blo 2029435 2030271 := bstep (se 1 (by rfl) ⟨1522703, by rfl⟩ : syracuseStep 2030271 = 3045407) B3045407
theorem B3045413 : Blo 2029435 3045413 := bbase (se 4 (by rfl) ⟨285507, by rfl⟩ : syracuseStep 3045413 = 571015) (by norm_num)
theorem B2030275 : Blo 2029435 2030275 := bstep (se 1 (by rfl) ⟨1522706, by rfl⟩ : syracuseStep 2030275 = 3045413) B3045413
theorem B2569573 : Blo 2029435 2569573 := bbase (se 4 (by rfl) ⟨240897, by rfl⟩ : syracuseStep 2569573 = 481795) (by norm_num)
theorem B3426097 : Blo 2029435 3426097 := bstep (se 2 (by rfl) ⟨1284786, by rfl⟩ : syracuseStep 3426097 = 2569573) B2569573
theorem B4568129 : Blo 2029435 4568129 := bstep (se 2 (by rfl) ⟨1713048, by rfl⟩ : syracuseStep 4568129 = 3426097) B3426097
theorem B3045419 : Blo 2029435 3045419 := bstep (se 1 (by rfl) ⟨2284064, by rfl⟩ : syracuseStep 3045419 = 4568129) B4568129
theorem B2030279 : Blo 2029435 2030279 := bstep (se 1 (by rfl) ⟨1522709, by rfl⟩ : syracuseStep 2030279 = 3045419) B3045419
theorem B2284069 : Blo 2029435 2284069 := bbase (se 4 (by rfl) ⟨214131, by rfl⟩ : syracuseStep 2284069 = 428263) (by norm_num)
theorem B3045425 : Blo 2029435 3045425 := bstep (se 2 (by rfl) ⟨1142034, by rfl⟩ : syracuseStep 3045425 = 2284069) B2284069
theorem B2030283 : Blo 2029435 2030283 := bstep (se 1 (by rfl) ⟨1522712, by rfl⟩ : syracuseStep 2030283 = 3045425) B3045425
theorem B9756389 : Blo 2029435 9756389 := bbase (se 4 (by rfl) ⟨914661, by rfl⟩ : syracuseStep 9756389 = 1829323) (by norm_num)
theorem B6504259 : Blo 2029435 6504259 := bstep (se 1 (by rfl) ⟨4878194, by rfl⟩ : syracuseStep 6504259 = 9756389) B9756389
theorem B8672345 : Blo 2029435 8672345 := bstep (se 2 (by rfl) ⟨3252129, by rfl⟩ : syracuseStep 8672345 = 6504259) B6504259
theorem B5781563 : Blo 2029435 5781563 := bstep (se 1 (by rfl) ⟨4336172, by rfl⟩ : syracuseStep 5781563 = 8672345) B8672345
theorem B3854375 : Blo 2029435 3854375 := bstep (se 1 (by rfl) ⟨2890781, by rfl⟩ : syracuseStep 3854375 = 5781563) B5781563
theorem B2569583 : Blo 2029435 2569583 := bstep (se 1 (by rfl) ⟨1927187, by rfl⟩ : syracuseStep 2569583 = 3854375) B3854375
theorem B6852221 : Blo 2029435 6852221 := bstep (se 3 (by rfl) ⟨1284791, by rfl⟩ : syracuseStep 6852221 = 2569583) B2569583
theorem B4568147 : Blo 2029435 4568147 := bstep (se 1 (by rfl) ⟨3426110, by rfl⟩ : syracuseStep 4568147 = 6852221) B6852221
theorem B3045431 : Blo 2029435 3045431 := bstep (se 1 (by rfl) ⟨2284073, by rfl⟩ : syracuseStep 3045431 = 4568147) B4568147
theorem B2030287 : Blo 2029435 2030287 := bstep (se 1 (by rfl) ⟨1522715, by rfl⟩ : syracuseStep 2030287 = 3045431) B3045431
theorem B3045437 : Blo 2029435 3045437 := bbase (se 3 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 3045437 = 1142039) (by norm_num)
theorem B2030291 : Blo 2029435 2030291 := bstep (se 1 (by rfl) ⟨1522718, by rfl⟩ : syracuseStep 2030291 = 3045437) B3045437
theorem B4568165 : Blo 2029435 4568165 := bbase (se 4 (by rfl) ⟨428265, by rfl⟩ : syracuseStep 4568165 = 856531) (by norm_num)
theorem B3045443 : Blo 2029435 3045443 := bstep (se 1 (by rfl) ⟨2284082, by rfl⟩ : syracuseStep 3045443 = 4568165) B4568165
theorem B2030295 : Blo 2029435 2030295 := bstep (se 1 (by rfl) ⟨1522721, by rfl⟩ : syracuseStep 2030295 = 3045443) B3045443
theorem B5139197 : Blo 2029435 5139197 := bbase (se 3 (by rfl) ⟨963599, by rfl⟩ : syracuseStep 5139197 = 1927199) (by norm_num)
theorem B3426131 : Blo 2029435 3426131 := bstep (se 1 (by rfl) ⟨2569598, by rfl⟩ : syracuseStep 3426131 = 5139197) B5139197
theorem B2284087 : Blo 2029435 2284087 := bstep (se 1 (by rfl) ⟨1713065, by rfl⟩ : syracuseStep 2284087 = 3426131) B3426131
theorem B3045449 : Blo 2029435 3045449 := bstep (se 2 (by rfl) ⟨1142043, by rfl⟩ : syracuseStep 3045449 = 2284087) B2284087
theorem B2030299 : Blo 2029435 2030299 := bstep (se 1 (by rfl) ⟨1522724, by rfl⟩ : syracuseStep 2030299 = 3045449) B3045449
theorem B3854405 : Blo 2029435 3854405 := bbase (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) (by norm_num)
theorem B10278413 : Blo 2029435 10278413 := bstep (se 3 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 10278413 = 3854405) B3854405
theorem B6852275 : Blo 2029435 6852275 := bstep (se 1 (by rfl) ⟨5139206, by rfl⟩ : syracuseStep 6852275 = 10278413) B10278413
theorem B4568183 : Blo 2029435 4568183 := bstep (se 1 (by rfl) ⟨3426137, by rfl⟩ : syracuseStep 4568183 = 6852275) B6852275
theorem B3045455 : Blo 2029435 3045455 := bstep (se 1 (by rfl) ⟨2284091, by rfl⟩ : syracuseStep 3045455 = 4568183) B4568183
theorem B2030303 : Blo 2029435 2030303 := bstep (se 1 (by rfl) ⟨1522727, by rfl⟩ : syracuseStep 2030303 = 3045455) B3045455
theorem B3045461 : Blo 2029435 3045461 := bbase (se 8 (by rfl) ⟨17844, by rfl⟩ : syracuseStep 3045461 = 35689) (by norm_num)
theorem B2030307 : Blo 2029435 2030307 := bstep (se 1 (by rfl) ⟨1522730, by rfl⟩ : syracuseStep 2030307 = 3045461) B3045461
theorem B2819405 : Blo 2029435 2819405 := bbase (se 3 (by rfl) ⟨528638, by rfl⟩ : syracuseStep 2819405 = 1057277) (by norm_num)
theorem B7518413 : Blo 2029435 7518413 := bstep (se 3 (by rfl) ⟨1409702, by rfl⟩ : syracuseStep 7518413 = 2819405) B2819405
theorem B5012275 : Blo 2029435 5012275 := bstep (se 1 (by rfl) ⟨3759206, by rfl⟩ : syracuseStep 5012275 = 7518413) B7518413
theorem B6683033 : Blo 2029435 6683033 := bstep (se 2 (by rfl) ⟨2506137, by rfl⟩ : syracuseStep 6683033 = 5012275) B5012275
theorem B4455355 : Blo 2029435 4455355 := bstep (se 1 (by rfl) ⟨3341516, by rfl⟩ : syracuseStep 4455355 = 6683033) B6683033
theorem B5940473 : Blo 2029435 5940473 := bstep (se 2 (by rfl) ⟨2227677, by rfl⟩ : syracuseStep 5940473 = 4455355) B4455355
theorem B15841261 : Blo 2029435 15841261 := bstep (se 3 (by rfl) ⟨2970236, by rfl⟩ : syracuseStep 15841261 = 5940473) B5940473
theorem B21121681 : Blo 2029435 21121681 := bstep (se 2 (by rfl) ⟨7920630, by rfl⟩ : syracuseStep 21121681 = 15841261) B15841261
theorem B28162241 : Blo 2029435 28162241 := bstep (se 2 (by rfl) ⟨10560840, by rfl⟩ : syracuseStep 28162241 = 21121681) B21121681
theorem B18774827 : Blo 2029435 18774827 := bstep (se 1 (by rfl) ⟨14081120, by rfl⟩ : syracuseStep 18774827 = 28162241) B28162241
theorem B12516551 : Blo 2029435 12516551 := bstep (se 1 (by rfl) ⟨9387413, by rfl⟩ : syracuseStep 12516551 = 18774827) B18774827
theorem B8344367 : Blo 2029435 8344367 := bstep (se 1 (by rfl) ⟨6258275, by rfl⟩ : syracuseStep 8344367 = 12516551) B12516551
theorem B5562911 : Blo 2029435 5562911 := bstep (se 1 (by rfl) ⟨4172183, by rfl⟩ : syracuseStep 5562911 = 8344367) B8344367
theorem B3708607 : Blo 2029435 3708607 := bstep (se 1 (by rfl) ⟨2781455, by rfl⟩ : syracuseStep 3708607 = 5562911) B5562911
theorem B4944809 : Blo 2029435 4944809 := bstep (se 2 (by rfl) ⟨1854303, by rfl⟩ : syracuseStep 4944809 = 3708607) B3708607
theorem B3296539 : Blo 2029435 3296539 := bstep (se 1 (by rfl) ⟨2472404, by rfl⟩ : syracuseStep 3296539 = 4944809) B4944809
theorem B4395385 : Blo 2029435 4395385 := bstep (se 2 (by rfl) ⟨1648269, by rfl⟩ : syracuseStep 4395385 = 3296539) B3296539
theorem B5860513 : Blo 2029435 5860513 := bstep (se 2 (by rfl) ⟨2197692, by rfl⟩ : syracuseStep 5860513 = 4395385) B4395385
theorem B7814017 : Blo 2029435 7814017 := bstep (se 2 (by rfl) ⟨2930256, by rfl⟩ : syracuseStep 7814017 = 5860513) B5860513
theorem B10418689 : Blo 2029435 10418689 := bstep (se 2 (by rfl) ⟨3907008, by rfl⟩ : syracuseStep 10418689 = 7814017) B7814017
theorem B13891585 : Blo 2029435 13891585 := bstep (se 2 (by rfl) ⟨5209344, by rfl⟩ : syracuseStep 13891585 = 10418689) B10418689
theorem B18522113 : Blo 2029435 18522113 := bstep (se 2 (by rfl) ⟨6945792, by rfl⟩ : syracuseStep 18522113 = 13891585) B13891585
theorem B49392301 : Blo 2029435 49392301 := bstep (se 3 (by rfl) ⟨9261056, by rfl⟩ : syracuseStep 49392301 = 18522113) B18522113
theorem B65856401 : Blo 2029435 65856401 := bstep (se 2 (by rfl) ⟨24696150, by rfl⟩ : syracuseStep 65856401 = 49392301) B49392301
theorem B43904267 : Blo 2029435 43904267 := bstep (se 1 (by rfl) ⟨32928200, by rfl⟩ : syracuseStep 43904267 = 65856401) B65856401
theorem B29269511 : Blo 2029435 29269511 := bstep (se 1 (by rfl) ⟨21952133, by rfl⟩ : syracuseStep 29269511 = 43904267) B43904267
theorem B19513007 : Blo 2029435 19513007 := bstep (se 1 (by rfl) ⟨14634755, by rfl⟩ : syracuseStep 19513007 = 29269511) B29269511
theorem B13008671 : Blo 2029435 13008671 := bstep (se 1 (by rfl) ⟨9756503, by rfl⟩ : syracuseStep 13008671 = 19513007) B19513007
theorem B8672447 : Blo 2029435 8672447 := bstep (se 1 (by rfl) ⟨6504335, by rfl⟩ : syracuseStep 8672447 = 13008671) B13008671
theorem B5781631 : Blo 2029435 5781631 := bstep (se 1 (by rfl) ⟨4336223, by rfl⟩ : syracuseStep 5781631 = 8672447) B8672447
theorem B7708841 : Blo 2029435 7708841 := bstep (se 2 (by rfl) ⟨2890815, by rfl⟩ : syracuseStep 7708841 = 5781631) B5781631
theorem B5139227 : Blo 2029435 5139227 := bstep (se 1 (by rfl) ⟨3854420, by rfl⟩ : syracuseStep 5139227 = 7708841) B7708841
theorem B3426151 : Blo 2029435 3426151 := bstep (se 1 (by rfl) ⟨2569613, by rfl⟩ : syracuseStep 3426151 = 5139227) B5139227
theorem B4568201 : Blo 2029435 4568201 := bstep (se 2 (by rfl) ⟨1713075, by rfl⟩ : syracuseStep 4568201 = 3426151) B3426151
theorem B3045467 : Blo 2029435 3045467 := bstep (se 1 (by rfl) ⟨2284100, by rfl⟩ : syracuseStep 3045467 = 4568201) B4568201
theorem B2030311 : Blo 2029435 2030311 := bstep (se 1 (by rfl) ⟨1522733, by rfl⟩ : syracuseStep 2030311 = 3045467) B3045467
theorem B2284105 : Blo 2029435 2284105 := bbase (se 2 (by rfl) ⟨856539, by rfl⟩ : syracuseStep 2284105 = 1713079) (by norm_num)
theorem B3045473 : Blo 2029435 3045473 := bstep (se 2 (by rfl) ⟨1142052, by rfl⟩ : syracuseStep 3045473 = 2284105) B2284105
theorem B2030315 : Blo 2029435 2030315 := bstep (se 1 (by rfl) ⟨1522736, by rfl⟩ : syracuseStep 2030315 = 3045473) B3045473
theorem B2930269 : Blo 2029435 2930269 := bbase (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) (by norm_num)
theorem B3907025 : Blo 2029435 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B2604683 : Blo 2029435 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B6945821 : Blo 2029435 6945821 := bstep (se 3 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 6945821 = 2604683) B2604683
theorem B4630547 : Blo 2029435 4630547 := bstep (se 1 (by rfl) ⟨3472910, by rfl⟩ : syracuseStep 4630547 = 6945821) B6945821
theorem B12348125 : Blo 2029435 12348125 := bstep (se 3 (by rfl) ⟨2315273, by rfl⟩ : syracuseStep 12348125 = 4630547) B4630547
theorem B8232083 : Blo 2029435 8232083 := bstep (se 1 (by rfl) ⟨6174062, by rfl⟩ : syracuseStep 8232083 = 12348125) B12348125
theorem B5488055 : Blo 2029435 5488055 := bstep (se 1 (by rfl) ⟨4116041, by rfl⟩ : syracuseStep 5488055 = 8232083) B8232083
theorem B3658703 : Blo 2029435 3658703 := bstep (se 1 (by rfl) ⟨2744027, by rfl⟩ : syracuseStep 3658703 = 5488055) B5488055
theorem B9756541 : Blo 2029435 9756541 := bstep (se 3 (by rfl) ⟨1829351, by rfl⟩ : syracuseStep 9756541 = 3658703) B3658703
theorem B13008721 : Blo 2029435 13008721 := bstep (se 2 (by rfl) ⟨4878270, by rfl⟩ : syracuseStep 13008721 = 9756541) B9756541
theorem B17344961 : Blo 2029435 17344961 := bstep (se 2 (by rfl) ⟨6504360, by rfl⟩ : syracuseStep 17344961 = 13008721) B13008721
theorem B11563307 : Blo 2029435 11563307 := bstep (se 1 (by rfl) ⟨8672480, by rfl⟩ : syracuseStep 11563307 = 17344961) B17344961
theorem B7708871 : Blo 2029435 7708871 := bstep (se 1 (by rfl) ⟨5781653, by rfl⟩ : syracuseStep 7708871 = 11563307) B11563307
theorem B5139247 : Blo 2029435 5139247 := bstep (se 1 (by rfl) ⟨3854435, by rfl⟩ : syracuseStep 5139247 = 7708871) B7708871
theorem B6852329 : Blo 2029435 6852329 := bstep (se 2 (by rfl) ⟨2569623, by rfl⟩ : syracuseStep 6852329 = 5139247) B5139247
theorem B4568219 : Blo 2029435 4568219 := bstep (se 1 (by rfl) ⟨3426164, by rfl⟩ : syracuseStep 4568219 = 6852329) B6852329
theorem B3045479 : Blo 2029435 3045479 := bstep (se 1 (by rfl) ⟨2284109, by rfl⟩ : syracuseStep 3045479 = 4568219) B4568219
theorem B2030319 : Blo 2029435 2030319 := bstep (se 1 (by rfl) ⟨1522739, by rfl⟩ : syracuseStep 2030319 = 3045479) B3045479
theorem B3045485 : Blo 2029435 3045485 := bbase (se 3 (by rfl) ⟨571028, by rfl⟩ : syracuseStep 3045485 = 1142057) (by norm_num)
theorem B2030323 : Blo 2029435 2030323 := bstep (se 1 (by rfl) ⟨1522742, by rfl⟩ : syracuseStep 2030323 = 3045485) B3045485
theorem B4568237 : Blo 2029435 4568237 := bbase (se 3 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 4568237 = 1713089) (by norm_num)
theorem B3045491 : Blo 2029435 3045491 := bstep (se 1 (by rfl) ⟨2284118, by rfl⟩ : syracuseStep 3045491 = 4568237) B4568237
theorem B2030327 : Blo 2029435 2030327 := bstep (se 1 (by rfl) ⟨1522745, by rfl⟩ : syracuseStep 2030327 = 3045491) B3045491
theorem B4878301 : Blo 2029435 4878301 := bbase (se 3 (by rfl) ⟨914681, by rfl⟩ : syracuseStep 4878301 = 1829363) (by norm_num)
theorem B6504401 : Blo 2029435 6504401 := bstep (se 2 (by rfl) ⟨2439150, by rfl⟩ : syracuseStep 6504401 = 4878301) B4878301
theorem B4336267 : Blo 2029435 4336267 := bstep (se 1 (by rfl) ⟨3252200, by rfl⟩ : syracuseStep 4336267 = 6504401) B6504401
theorem B5781689 : Blo 2029435 5781689 := bstep (se 2 (by rfl) ⟨2168133, by rfl⟩ : syracuseStep 5781689 = 4336267) B4336267
theorem B3854459 : Blo 2029435 3854459 := bstep (se 1 (by rfl) ⟨2890844, by rfl⟩ : syracuseStep 3854459 = 5781689) B5781689
theorem B2569639 : Blo 2029435 2569639 := bstep (se 1 (by rfl) ⟨1927229, by rfl⟩ : syracuseStep 2569639 = 3854459) B3854459
theorem B3426185 : Blo 2029435 3426185 := bstep (se 2 (by rfl) ⟨1284819, by rfl⟩ : syracuseStep 3426185 = 2569639) B2569639
theorem B2284123 : Blo 2029435 2284123 := bstep (se 1 (by rfl) ⟨1713092, by rfl⟩ : syracuseStep 2284123 = 3426185) B3426185
theorem B3045497 : Blo 2029435 3045497 := bstep (se 2 (by rfl) ⟨1142061, by rfl⟩ : syracuseStep 3045497 = 2284123) B2284123
theorem B2030331 : Blo 2029435 2030331 := bstep (se 1 (by rfl) ⟨1522748, by rfl⟩ : syracuseStep 2030331 = 3045497) B3045497
theorem B2640241 : Blo 2029435 2640241 := bbase (se 2 (by rfl) ⟨990090, by rfl⟩ : syracuseStep 2640241 = 1980181) (by norm_num)
theorem B14081285 : Blo 2029435 14081285 := bstep (se 4 (by rfl) ⟨1320120, by rfl⟩ : syracuseStep 14081285 = 2640241) B2640241
theorem B9387523 : Blo 2029435 9387523 := bstep (se 1 (by rfl) ⟨7040642, by rfl⟩ : syracuseStep 9387523 = 14081285) B14081285
theorem B12516697 : Blo 2029435 12516697 := bstep (se 2 (by rfl) ⟨4693761, by rfl⟩ : syracuseStep 12516697 = 9387523) B9387523
theorem B16688929 : Blo 2029435 16688929 := bstep (se 2 (by rfl) ⟨6258348, by rfl⟩ : syracuseStep 16688929 = 12516697) B12516697
theorem B22251905 : Blo 2029435 22251905 := bstep (se 2 (by rfl) ⟨8344464, by rfl⟩ : syracuseStep 22251905 = 16688929) B16688929
theorem B14834603 : Blo 2029435 14834603 := bstep (se 1 (by rfl) ⟨11125952, by rfl⟩ : syracuseStep 14834603 = 22251905) B22251905
theorem B9889735 : Blo 2029435 9889735 := bstep (se 1 (by rfl) ⟨7417301, by rfl⟩ : syracuseStep 9889735 = 14834603) B14834603
theorem B13186313 : Blo 2029435 13186313 := bstep (se 2 (by rfl) ⟨4944867, by rfl⟩ : syracuseStep 13186313 = 9889735) B9889735
theorem B8790875 : Blo 2029435 8790875 := bstep (se 1 (by rfl) ⟨6593156, by rfl⟩ : syracuseStep 8790875 = 13186313) B13186313
theorem B5860583 : Blo 2029435 5860583 := bstep (se 1 (by rfl) ⟨4395437, by rfl⟩ : syracuseStep 5860583 = 8790875) B8790875
theorem B3907055 : Blo 2029435 3907055 := bstep (se 1 (by rfl) ⟨2930291, by rfl⟩ : syracuseStep 3907055 = 5860583) B5860583
theorem B10418813 : Blo 2029435 10418813 := bstep (se 3 (by rfl) ⟨1953527, by rfl⟩ : syracuseStep 10418813 = 3907055) B3907055
theorem B6945875 : Blo 2029435 6945875 := bstep (se 1 (by rfl) ⟨5209406, by rfl⟩ : syracuseStep 6945875 = 10418813) B10418813
theorem B4630583 : Blo 2029435 4630583 := bstep (se 1 (by rfl) ⟨3472937, by rfl⟩ : syracuseStep 4630583 = 6945875) B6945875
theorem B3087055 : Blo 2029435 3087055 := bstep (se 1 (by rfl) ⟨2315291, by rfl⟩ : syracuseStep 3087055 = 4630583) B4630583
theorem B16464293 : Blo 2029435 16464293 := bstep (se 4 (by rfl) ⟨1543527, by rfl⟩ : syracuseStep 16464293 = 3087055) B3087055
theorem B10976195 : Blo 2029435 10976195 := bstep (se 1 (by rfl) ⟨8232146, by rfl⟩ : syracuseStep 10976195 = 16464293) B16464293
theorem B7317463 : Blo 2029435 7317463 := bstep (se 1 (by rfl) ⟨5488097, by rfl⟩ : syracuseStep 7317463 = 10976195) B10976195
theorem B9756617 : Blo 2029435 9756617 := bstep (se 2 (by rfl) ⟨3658731, by rfl⟩ : syracuseStep 9756617 = 7317463) B7317463
theorem B26017645 : Blo 2029435 26017645 := bstep (se 3 (by rfl) ⟨4878308, by rfl⟩ : syracuseStep 26017645 = 9756617) B9756617
theorem B34690193 : Blo 2029435 34690193 := bstep (se 2 (by rfl) ⟨13008822, by rfl⟩ : syracuseStep 34690193 = 26017645) B26017645
theorem B23126795 : Blo 2029435 23126795 := bstep (se 1 (by rfl) ⟨17345096, by rfl⟩ : syracuseStep 23126795 = 34690193) B34690193
theorem B15417863 : Blo 2029435 15417863 := bstep (se 1 (by rfl) ⟨11563397, by rfl⟩ : syracuseStep 15417863 = 23126795) B23126795
theorem B10278575 : Blo 2029435 10278575 := bstep (se 1 (by rfl) ⟨7708931, by rfl⟩ : syracuseStep 10278575 = 15417863) B15417863
theorem B6852383 : Blo 2029435 6852383 := bstep (se 1 (by rfl) ⟨5139287, by rfl⟩ : syracuseStep 6852383 = 10278575) B10278575
theorem B4568255 : Blo 2029435 4568255 := bstep (se 1 (by rfl) ⟨3426191, by rfl⟩ : syracuseStep 4568255 = 6852383) B6852383
theorem B3045503 : Blo 2029435 3045503 := bstep (se 1 (by rfl) ⟨2284127, by rfl⟩ : syracuseStep 3045503 = 4568255) B4568255
theorem B2030335 : Blo 2029435 2030335 := bstep (se 1 (by rfl) ⟨1522751, by rfl⟩ : syracuseStep 2030335 = 3045503) B3045503
theorem B3045509 : Blo 2029435 3045509 := bbase (se 4 (by rfl) ⟨285516, by rfl⟩ : syracuseStep 3045509 = 571033) (by norm_num)
theorem B2030339 : Blo 2029435 2030339 := bstep (se 1 (by rfl) ⟨1522754, by rfl⟩ : syracuseStep 2030339 = 3045509) B3045509
theorem B3426205 : Blo 2029435 3426205 := bbase (se 3 (by rfl) ⟨642413, by rfl⟩ : syracuseStep 3426205 = 1284827) (by norm_num)
theorem B4568273 : Blo 2029435 4568273 := bstep (se 2 (by rfl) ⟨1713102, by rfl⟩ : syracuseStep 4568273 = 3426205) B3426205
theorem B3045515 : Blo 2029435 3045515 := bstep (se 1 (by rfl) ⟨2284136, by rfl⟩ : syracuseStep 3045515 = 4568273) B4568273
theorem B2030343 : Blo 2029435 2030343 := bstep (se 1 (by rfl) ⟨1522757, by rfl⟩ : syracuseStep 2030343 = 3045515) B3045515
theorem B2284141 : Blo 2029435 2284141 := bbase (se 3 (by rfl) ⟨428276, by rfl⟩ : syracuseStep 2284141 = 856553) (by norm_num)
theorem B3045521 : Blo 2029435 3045521 := bstep (se 2 (by rfl) ⟨1142070, by rfl⟩ : syracuseStep 3045521 = 2284141) B2284141
theorem B2030347 : Blo 2029435 2030347 := bstep (se 1 (by rfl) ⟨1522760, by rfl⟩ : syracuseStep 2030347 = 3045521) B3045521
theorem B6852437 : Blo 2029435 6852437 := bbase (se 9 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 6852437 = 40151) (by norm_num)
theorem B4568291 : Blo 2029435 4568291 := bstep (se 1 (by rfl) ⟨3426218, by rfl⟩ : syracuseStep 4568291 = 6852437) B6852437
theorem B3045527 : Blo 2029435 3045527 := bstep (se 1 (by rfl) ⟨2284145, by rfl⟩ : syracuseStep 3045527 = 4568291) B4568291
theorem B2030351 : Blo 2029435 2030351 := bstep (se 1 (by rfl) ⟨1522763, by rfl⟩ : syracuseStep 2030351 = 3045527) B3045527
theorem B3045533 : Blo 2029435 3045533 := bbase (se 3 (by rfl) ⟨571037, by rfl⟩ : syracuseStep 3045533 = 1142075) (by norm_num)
theorem B2030355 : Blo 2029435 2030355 := bstep (se 1 (by rfl) ⟨1522766, by rfl⟩ : syracuseStep 2030355 = 3045533) B3045533
theorem B4568309 : Blo 2029435 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B3045539 : Blo 2029435 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B2030359 : Blo 2029435 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B6174197 : Blo 2029435 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B4116131 : Blo 2029435 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B2744087 : Blo 2029435 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B29270261 : Blo 2029435 29270261 := bstep (se 5 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 29270261 = 2744087) B2744087
theorem B19513507 : Blo 2029435 19513507 := bstep (se 1 (by rfl) ⟨14635130, by rfl⟩ : syracuseStep 19513507 = 29270261) B29270261
theorem B26018009 : Blo 2029435 26018009 := bstep (se 2 (by rfl) ⟨9756753, by rfl⟩ : syracuseStep 26018009 = 19513507) B19513507
theorem B17345339 : Blo 2029435 17345339 := bstep (se 1 (by rfl) ⟨13009004, by rfl⟩ : syracuseStep 17345339 = 26018009) B26018009
theorem B11563559 : Blo 2029435 11563559 := bstep (se 1 (by rfl) ⟨8672669, by rfl⟩ : syracuseStep 11563559 = 17345339) B17345339
theorem B7709039 : Blo 2029435 7709039 := bstep (se 1 (by rfl) ⟨5781779, by rfl⟩ : syracuseStep 7709039 = 11563559) B11563559
theorem B5139359 : Blo 2029435 5139359 := bstep (se 1 (by rfl) ⟨3854519, by rfl⟩ : syracuseStep 5139359 = 7709039) B7709039
theorem B3426239 : Blo 2029435 3426239 := bstep (se 1 (by rfl) ⟨2569679, by rfl⟩ : syracuseStep 3426239 = 5139359) B5139359
theorem B2284159 : Blo 2029435 2284159 := bstep (se 1 (by rfl) ⟨1713119, by rfl⟩ : syracuseStep 2284159 = 3426239) B3426239
theorem B3045545 : Blo 2029435 3045545 := bstep (se 2 (by rfl) ⟨1142079, by rfl⟩ : syracuseStep 3045545 = 2284159) B2284159
theorem B2030363 : Blo 2029435 2030363 := bstep (se 1 (by rfl) ⟨1522772, by rfl⟩ : syracuseStep 2030363 = 3045545) B3045545
theorem B9756773 : Blo 2029435 9756773 := bbase (se 4 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 9756773 = 1829395) (by norm_num)
theorem B6504515 : Blo 2029435 6504515 := bstep (se 1 (by rfl) ⟨4878386, by rfl⟩ : syracuseStep 6504515 = 9756773) B9756773
theorem B4336343 : Blo 2029435 4336343 := bstep (se 1 (by rfl) ⟨3252257, by rfl⟩ : syracuseStep 4336343 = 6504515) B6504515
theorem B2890895 : Blo 2029435 2890895 := bstep (se 1 (by rfl) ⟨2168171, by rfl⟩ : syracuseStep 2890895 = 4336343) B4336343
theorem B7709053 : Blo 2029435 7709053 := bstep (se 3 (by rfl) ⟨1445447, by rfl⟩ : syracuseStep 7709053 = 2890895) B2890895
theorem B10278737 : Blo 2029435 10278737 := bstep (se 2 (by rfl) ⟨3854526, by rfl⟩ : syracuseStep 10278737 = 7709053) B7709053
theorem B6852491 : Blo 2029435 6852491 := bstep (se 1 (by rfl) ⟨5139368, by rfl⟩ : syracuseStep 6852491 = 10278737) B10278737
theorem B4568327 : Blo 2029435 4568327 := bstep (se 1 (by rfl) ⟨3426245, by rfl⟩ : syracuseStep 4568327 = 6852491) B6852491
theorem B3045551 : Blo 2029435 3045551 := bstep (se 1 (by rfl) ⟨2284163, by rfl⟩ : syracuseStep 3045551 = 4568327) B4568327
theorem B2030367 : Blo 2029435 2030367 := bstep (se 1 (by rfl) ⟨1522775, by rfl⟩ : syracuseStep 2030367 = 3045551) B3045551
theorem B3045557 : Blo 2029435 3045557 := bbase (se 5 (by rfl) ⟨142760, by rfl⟩ : syracuseStep 3045557 = 285521) (by norm_num)
theorem B2030371 : Blo 2029435 2030371 := bstep (se 1 (by rfl) ⟨1522778, by rfl⟩ : syracuseStep 2030371 = 3045557) B3045557
theorem B5139389 : Blo 2029435 5139389 := bbase (se 3 (by rfl) ⟨963635, by rfl⟩ : syracuseStep 5139389 = 1927271) (by norm_num)
theorem B3426259 : Blo 2029435 3426259 := bstep (se 1 (by rfl) ⟨2569694, by rfl⟩ : syracuseStep 3426259 = 5139389) B5139389
theorem B4568345 : Blo 2029435 4568345 := bstep (se 2 (by rfl) ⟨1713129, by rfl⟩ : syracuseStep 4568345 = 3426259) B3426259
theorem B3045563 : Blo 2029435 3045563 := bstep (se 1 (by rfl) ⟨2284172, by rfl⟩ : syracuseStep 3045563 = 4568345) B4568345
theorem B2030375 : Blo 2029435 2030375 := bstep (se 1 (by rfl) ⟨1522781, by rfl⟩ : syracuseStep 2030375 = 3045563) B3045563
theorem B2284177 : Blo 2029435 2284177 := bbase (se 2 (by rfl) ⟨856566, by rfl⟩ : syracuseStep 2284177 = 1713133) (by norm_num)
theorem B3045569 : Blo 2029435 3045569 := bstep (se 2 (by rfl) ⟨1142088, by rfl⟩ : syracuseStep 3045569 = 2284177) B2284177
theorem B2030379 : Blo 2029435 2030379 := bstep (se 1 (by rfl) ⟨1522784, by rfl⟩ : syracuseStep 2030379 = 3045569) B3045569
theorem B3854557 : Blo 2029435 3854557 := bbase (se 3 (by rfl) ⟨722729, by rfl⟩ : syracuseStep 3854557 = 1445459) (by norm_num)
theorem B5139409 : Blo 2029435 5139409 := bstep (se 2 (by rfl) ⟨1927278, by rfl⟩ : syracuseStep 5139409 = 3854557) B3854557
theorem B6852545 : Blo 2029435 6852545 := bstep (se 2 (by rfl) ⟨2569704, by rfl⟩ : syracuseStep 6852545 = 5139409) B5139409
theorem B4568363 : Blo 2029435 4568363 := bstep (se 1 (by rfl) ⟨3426272, by rfl⟩ : syracuseStep 4568363 = 6852545) B6852545
theorem B3045575 : Blo 2029435 3045575 := bstep (se 1 (by rfl) ⟨2284181, by rfl⟩ : syracuseStep 3045575 = 4568363) B4568363
theorem B2030383 : Blo 2029435 2030383 := bstep (se 1 (by rfl) ⟨1522787, by rfl⟩ : syracuseStep 2030383 = 3045575) B3045575
theorem B3045581 : Blo 2029435 3045581 := bbase (se 3 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 3045581 = 1142093) (by norm_num)
theorem B2030387 : Blo 2029435 2030387 := bstep (se 1 (by rfl) ⟨1522790, by rfl⟩ : syracuseStep 2030387 = 3045581) B3045581
theorem B4568381 : Blo 2029435 4568381 := bbase (se 3 (by rfl) ⟨856571, by rfl⟩ : syracuseStep 4568381 = 1713143) (by norm_num)
theorem B3045587 : Blo 2029435 3045587 := bstep (se 1 (by rfl) ⟨2284190, by rfl⟩ : syracuseStep 3045587 = 4568381) B4568381
theorem B2030391 : Blo 2029435 2030391 := bstep (se 1 (by rfl) ⟨1522793, by rfl⟩ : syracuseStep 2030391 = 3045587) B3045587
theorem B3426293 : Blo 2029435 3426293 := bbase (se 5 (by rfl) ⟨160607, by rfl⟩ : syracuseStep 3426293 = 321215) (by norm_num)
theorem B2284195 : Blo 2029435 2284195 := bstep (se 1 (by rfl) ⟨1713146, by rfl⟩ : syracuseStep 2284195 = 3426293) B3426293
theorem B3045593 : Blo 2029435 3045593 := bstep (se 2 (by rfl) ⟨1142097, by rfl⟩ : syracuseStep 3045593 = 2284195) B2284195
theorem B2030395 : Blo 2029435 2030395 := bstep (se 1 (by rfl) ⟨1522796, by rfl⟩ : syracuseStep 2030395 = 3045593) B3045593
theorem B41676565 : Blo 2029435 41676565 := bbase (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) (by norm_num)
theorem B55568753 : Blo 2029435 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B37045835 : Blo 2029435 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B24697223 : Blo 2029435 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B16464815 : Blo 2029435 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B10976543 : Blo 2029435 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B7317695 : Blo 2029435 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B4878463 : Blo 2029435 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B6504617 : Blo 2029435 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B4336411 : Blo 2029435 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B5781881 : Blo 2029435 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B15418349 : Blo 2029435 15418349 := bstep (se 3 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 15418349 = 5781881) B5781881
theorem B10278899 : Blo 2029435 10278899 := bstep (se 1 (by rfl) ⟨7709174, by rfl⟩ : syracuseStep 10278899 = 15418349) B15418349
theorem B6852599 : Blo 2029435 6852599 := bstep (se 1 (by rfl) ⟨5139449, by rfl⟩ : syracuseStep 6852599 = 10278899) B10278899
theorem B4568399 : Blo 2029435 4568399 := bstep (se 1 (by rfl) ⟨3426299, by rfl⟩ : syracuseStep 4568399 = 6852599) B6852599
theorem B3045599 : Blo 2029435 3045599 := bstep (se 1 (by rfl) ⟨2284199, by rfl⟩ : syracuseStep 3045599 = 4568399) B4568399
theorem B2030399 : Blo 2029435 2030399 := bstep (se 1 (by rfl) ⟨1522799, by rfl⟩ : syracuseStep 2030399 = 3045599) B3045599
theorem B3045605 : Blo 2029435 3045605 := bbase (se 4 (by rfl) ⟨285525, by rfl⟩ : syracuseStep 3045605 = 571051) (by norm_num)
theorem B2030403 : Blo 2029435 2030403 := bstep (se 1 (by rfl) ⟨1522802, by rfl⟩ : syracuseStep 2030403 = 3045605) B3045605
theorem B4336429 : Blo 2029435 4336429 := bbase (se 3 (by rfl) ⟨813080, by rfl⟩ : syracuseStep 4336429 = 1626161) (by norm_num)
theorem B5781905 : Blo 2029435 5781905 := bstep (se 2 (by rfl) ⟨2168214, by rfl⟩ : syracuseStep 5781905 = 4336429) B4336429
theorem B3854603 : Blo 2029435 3854603 := bstep (se 1 (by rfl) ⟨2890952, by rfl⟩ : syracuseStep 3854603 = 5781905) B5781905
theorem B2569735 : Blo 2029435 2569735 := bstep (se 1 (by rfl) ⟨1927301, by rfl⟩ : syracuseStep 2569735 = 3854603) B3854603
theorem B3426313 : Blo 2029435 3426313 := bstep (se 2 (by rfl) ⟨1284867, by rfl⟩ : syracuseStep 3426313 = 2569735) B2569735
theorem B4568417 : Blo 2029435 4568417 := bstep (se 2 (by rfl) ⟨1713156, by rfl⟩ : syracuseStep 4568417 = 3426313) B3426313
theorem B3045611 : Blo 2029435 3045611 := bstep (se 1 (by rfl) ⟨2284208, by rfl⟩ : syracuseStep 3045611 = 4568417) B4568417
theorem B2030407 : Blo 2029435 2030407 := bstep (se 1 (by rfl) ⟨1522805, by rfl⟩ : syracuseStep 2030407 = 3045611) B3045611
theorem B2284213 : Blo 2029435 2284213 := bbase (se 5 (by rfl) ⟨107072, by rfl⟩ : syracuseStep 2284213 = 214145) (by norm_num)
theorem B3045617 : Blo 2029435 3045617 := bstep (se 2 (by rfl) ⟨1142106, by rfl⟩ : syracuseStep 3045617 = 2284213) B2284213
theorem B2030411 : Blo 2029435 2030411 := bstep (se 1 (by rfl) ⟨1522808, by rfl⟩ : syracuseStep 2030411 = 3045617) B3045617
theorem B2569745 : Blo 2029435 2569745 := bbase (se 2 (by rfl) ⟨963654, by rfl⟩ : syracuseStep 2569745 = 1927309) (by norm_num)
theorem B6852653 : Blo 2029435 6852653 := bstep (se 3 (by rfl) ⟨1284872, by rfl⟩ : syracuseStep 6852653 = 2569745) B2569745
theorem B4568435 : Blo 2029435 4568435 := bstep (se 1 (by rfl) ⟨3426326, by rfl⟩ : syracuseStep 4568435 = 6852653) B6852653
theorem B3045623 : Blo 2029435 3045623 := bstep (se 1 (by rfl) ⟨2284217, by rfl⟩ : syracuseStep 3045623 = 4568435) B4568435
theorem B2030415 : Blo 2029435 2030415 := bstep (se 1 (by rfl) ⟨1522811, by rfl⟩ : syracuseStep 2030415 = 3045623) B3045623
theorem B3045629 : Blo 2029435 3045629 := bbase (se 3 (by rfl) ⟨571055, by rfl⟩ : syracuseStep 3045629 = 1142111) (by norm_num)
theorem B2030419 : Blo 2029435 2030419 := bstep (se 1 (by rfl) ⟨1522814, by rfl⟩ : syracuseStep 2030419 = 3045629) B3045629
theorem B4568453 : Blo 2029435 4568453 := bbase (se 4 (by rfl) ⟨428292, by rfl⟩ : syracuseStep 4568453 = 856585) (by norm_num)
theorem B3045635 : Blo 2029435 3045635 := bstep (se 1 (by rfl) ⟨2284226, by rfl⟩ : syracuseStep 3045635 = 4568453) B4568453
theorem B2030423 : Blo 2029435 2030423 := bstep (se 1 (by rfl) ⟨1522817, by rfl⟩ : syracuseStep 2030423 = 3045635) B3045635
theorem B2890981 : Blo 2029435 2890981 := bbase (se 4 (by rfl) ⟨271029, by rfl⟩ : syracuseStep 2890981 = 542059) (by norm_num)
theorem B3854641 : Blo 2029435 3854641 := bstep (se 2 (by rfl) ⟨1445490, by rfl⟩ : syracuseStep 3854641 = 2890981) B2890981
theorem B5139521 : Blo 2029435 5139521 := bstep (se 2 (by rfl) ⟨1927320, by rfl⟩ : syracuseStep 5139521 = 3854641) B3854641
theorem B3426347 : Blo 2029435 3426347 := bstep (se 1 (by rfl) ⟨2569760, by rfl⟩ : syracuseStep 3426347 = 5139521) B5139521
theorem B2284231 : Blo 2029435 2284231 := bstep (se 1 (by rfl) ⟨1713173, by rfl⟩ : syracuseStep 2284231 = 3426347) B3426347
theorem B3045641 : Blo 2029435 3045641 := bstep (se 2 (by rfl) ⟨1142115, by rfl⟩ : syracuseStep 3045641 = 2284231) B2284231
theorem B2030427 : Blo 2029435 2030427 := bstep (se 1 (by rfl) ⟨1522820, by rfl⟩ : syracuseStep 2030427 = 3045641) B3045641
theorem B10279061 : Blo 2029435 10279061 := bbase (se 6 (by rfl) ⟨240915, by rfl⟩ : syracuseStep 10279061 = 481831) (by norm_num)
theorem B6852707 : Blo 2029435 6852707 := bstep (se 1 (by rfl) ⟨5139530, by rfl⟩ : syracuseStep 6852707 = 10279061) B10279061
theorem B4568471 : Blo 2029435 4568471 := bstep (se 1 (by rfl) ⟨3426353, by rfl⟩ : syracuseStep 4568471 = 6852707) B6852707
theorem B3045647 : Blo 2029435 3045647 := bstep (se 1 (by rfl) ⟨2284235, by rfl⟩ : syracuseStep 3045647 = 4568471) B4568471
theorem B2030431 : Blo 2029435 2030431 := bstep (se 1 (by rfl) ⟨1522823, by rfl⟩ : syracuseStep 2030431 = 3045647) B3045647
theorem B3045653 : Blo 2029435 3045653 := bbase (se 6 (by rfl) ⟨71382, by rfl⟩ : syracuseStep 3045653 = 142765) (by norm_num)
theorem B2030435 : Blo 2029435 2030435 := bstep (se 1 (by rfl) ⟨1522826, by rfl⟩ : syracuseStep 2030435 = 3045653) B3045653
theorem B38583701 : Blo 2029435 38583701 := bbase (se 6 (by rfl) ⟨904305, by rfl⟩ : syracuseStep 38583701 = 1808611) (by norm_num)
theorem B25722467 : Blo 2029435 25722467 := bstep (se 1 (by rfl) ⟨19291850, by rfl⟩ : syracuseStep 25722467 = 38583701) B38583701
theorem B17148311 : Blo 2029435 17148311 := bstep (se 1 (by rfl) ⟨12861233, by rfl⟩ : syracuseStep 17148311 = 25722467) B25722467
theorem B11432207 : Blo 2029435 11432207 := bstep (se 1 (by rfl) ⟨8574155, by rfl⟩ : syracuseStep 11432207 = 17148311) B17148311
theorem B7621471 : Blo 2029435 7621471 := bstep (se 1 (by rfl) ⟨5716103, by rfl⟩ : syracuseStep 7621471 = 11432207) B11432207
theorem B40647845 : Blo 2029435 40647845 := bstep (se 4 (by rfl) ⟨3810735, by rfl⟩ : syracuseStep 40647845 = 7621471) B7621471
theorem B27098563 : Blo 2029435 27098563 := bstep (se 1 (by rfl) ⟨20323922, by rfl⟩ : syracuseStep 27098563 = 40647845) B40647845
theorem B36131417 : Blo 2029435 36131417 := bstep (se 2 (by rfl) ⟨13549281, by rfl⟩ : syracuseStep 36131417 = 27098563) B27098563
theorem B24087611 : Blo 2029435 24087611 := bstep (se 1 (by rfl) ⟨18065708, by rfl⟩ : syracuseStep 24087611 = 36131417) B36131417
theorem B16058407 : Blo 2029435 16058407 := bstep (se 1 (by rfl) ⟨12043805, by rfl⟩ : syracuseStep 16058407 = 24087611) B24087611
theorem B21411209 : Blo 2029435 21411209 := bstep (se 2 (by rfl) ⟨8029203, by rfl⟩ : syracuseStep 21411209 = 16058407) B16058407
theorem B14274139 : Blo 2029435 14274139 := bstep (se 1 (by rfl) ⟨10705604, by rfl⟩ : syracuseStep 14274139 = 21411209) B21411209
theorem B19032185 : Blo 2029435 19032185 := bstep (se 2 (by rfl) ⟨7137069, by rfl⟩ : syracuseStep 19032185 = 14274139) B14274139
theorem B50752493 : Blo 2029435 50752493 := bstep (se 3 (by rfl) ⟨9516092, by rfl⟩ : syracuseStep 50752493 = 19032185) B19032185
theorem B33834995 : Blo 2029435 33834995 := bstep (se 1 (by rfl) ⟨25376246, by rfl⟩ : syracuseStep 33834995 = 50752493) B50752493
theorem B22556663 : Blo 2029435 22556663 := bstep (se 1 (by rfl) ⟨16917497, by rfl⟩ : syracuseStep 22556663 = 33834995) B33834995
theorem B15037775 : Blo 2029435 15037775 := bstep (se 1 (by rfl) ⟨11278331, by rfl⟩ : syracuseStep 15037775 = 22556663) B22556663
theorem B10025183 : Blo 2029435 10025183 := bstep (se 1 (by rfl) ⟨7518887, by rfl⟩ : syracuseStep 10025183 = 15037775) B15037775
theorem B6683455 : Blo 2029435 6683455 := bstep (se 1 (by rfl) ⟨5012591, by rfl⟩ : syracuseStep 6683455 = 10025183) B10025183
theorem B35645093 : Blo 2029435 35645093 := bstep (se 4 (by rfl) ⟨3341727, by rfl⟩ : syracuseStep 35645093 = 6683455) B6683455
theorem B23763395 : Blo 2029435 23763395 := bstep (se 1 (by rfl) ⟨17822546, by rfl⟩ : syracuseStep 23763395 = 35645093) B35645093
theorem B15842263 : Blo 2029435 15842263 := bstep (se 1 (by rfl) ⟨11881697, by rfl⟩ : syracuseStep 15842263 = 23763395) B23763395
theorem B21123017 : Blo 2029435 21123017 := bstep (se 2 (by rfl) ⟨7921131, by rfl⟩ : syracuseStep 21123017 = 15842263) B15842263
theorem B14082011 : Blo 2029435 14082011 := bstep (se 1 (by rfl) ⟨10561508, by rfl⟩ : syracuseStep 14082011 = 21123017) B21123017
theorem B9388007 : Blo 2029435 9388007 := bstep (se 1 (by rfl) ⟨7041005, by rfl⟩ : syracuseStep 9388007 = 14082011) B14082011
theorem B6258671 : Blo 2029435 6258671 := bstep (se 1 (by rfl) ⟨4694003, by rfl⟩ : syracuseStep 6258671 = 9388007) B9388007
theorem B4172447 : Blo 2029435 4172447 := bstep (se 1 (by rfl) ⟨3129335, by rfl⟩ : syracuseStep 4172447 = 6258671) B6258671
theorem B2781631 : Blo 2029435 2781631 := bstep (se 1 (by rfl) ⟨2086223, by rfl⟩ : syracuseStep 2781631 = 4172447) B4172447
theorem B3708841 : Blo 2029435 3708841 := bstep (se 2 (by rfl) ⟨1390815, by rfl⟩ : syracuseStep 3708841 = 2781631) B2781631
theorem B4945121 : Blo 2029435 4945121 := bstep (se 2 (by rfl) ⟨1854420, by rfl⟩ : syracuseStep 4945121 = 3708841) B3708841
theorem B3296747 : Blo 2029435 3296747 := bstep (se 1 (by rfl) ⟨2472560, by rfl⟩ : syracuseStep 3296747 = 4945121) B4945121
theorem B8791325 : Blo 2029435 8791325 := bstep (se 3 (by rfl) ⟨1648373, by rfl⟩ : syracuseStep 8791325 = 3296747) B3296747
theorem B5860883 : Blo 2029435 5860883 := bstep (se 1 (by rfl) ⟨4395662, by rfl⟩ : syracuseStep 5860883 = 8791325) B8791325
theorem B15629021 : Blo 2029435 15629021 := bstep (se 3 (by rfl) ⟨2930441, by rfl⟩ : syracuseStep 15629021 = 5860883) B5860883
theorem B10419347 : Blo 2029435 10419347 := bstep (se 1 (by rfl) ⟨7814510, by rfl⟩ : syracuseStep 10419347 = 15629021) B15629021
theorem B6946231 : Blo 2029435 6946231 := bstep (se 1 (by rfl) ⟨5209673, by rfl⟩ : syracuseStep 6946231 = 10419347) B10419347
theorem B9261641 : Blo 2029435 9261641 := bstep (se 2 (by rfl) ⟨3473115, by rfl⟩ : syracuseStep 9261641 = 6946231) B6946231
theorem B24697709 : Blo 2029435 24697709 := bstep (se 3 (by rfl) ⟨4630820, by rfl⟩ : syracuseStep 24697709 = 9261641) B9261641
theorem B16465139 : Blo 2029435 16465139 := bstep (se 1 (by rfl) ⟨12348854, by rfl⟩ : syracuseStep 16465139 = 24697709) B24697709
theorem B10976759 : Blo 2029435 10976759 := bstep (se 1 (by rfl) ⟨8232569, by rfl⟩ : syracuseStep 10976759 = 16465139) B16465139
theorem B7317839 : Blo 2029435 7317839 := bstep (se 1 (by rfl) ⟨5488379, by rfl⟩ : syracuseStep 7317839 = 10976759) B10976759
theorem B4878559 : Blo 2029435 4878559 := bstep (se 1 (by rfl) ⟨3658919, by rfl⟩ : syracuseStep 4878559 = 7317839) B7317839
theorem B26018981 : Blo 2029435 26018981 := bstep (se 4 (by rfl) ⟨2439279, by rfl⟩ : syracuseStep 26018981 = 4878559) B4878559
theorem B17345987 : Blo 2029435 17345987 := bstep (se 1 (by rfl) ⟨13009490, by rfl⟩ : syracuseStep 17345987 = 26018981) B26018981
theorem B11563991 : Blo 2029435 11563991 := bstep (se 1 (by rfl) ⟨8672993, by rfl⟩ : syracuseStep 11563991 = 17345987) B17345987
theorem B7709327 : Blo 2029435 7709327 := bstep (se 1 (by rfl) ⟨5781995, by rfl⟩ : syracuseStep 7709327 = 11563991) B11563991
theorem B5139551 : Blo 2029435 5139551 := bstep (se 1 (by rfl) ⟨3854663, by rfl⟩ : syracuseStep 5139551 = 7709327) B7709327
theorem B3426367 : Blo 2029435 3426367 := bstep (se 1 (by rfl) ⟨2569775, by rfl⟩ : syracuseStep 3426367 = 5139551) B5139551
theorem B4568489 : Blo 2029435 4568489 := bstep (se 2 (by rfl) ⟨1713183, by rfl⟩ : syracuseStep 4568489 = 3426367) B3426367
theorem B3045659 : Blo 2029435 3045659 := bstep (se 1 (by rfl) ⟨2284244, by rfl⟩ : syracuseStep 3045659 = 4568489) B4568489
theorem B2030439 : Blo 2029435 2030439 := bstep (se 1 (by rfl) ⟨1522829, by rfl⟩ : syracuseStep 2030439 = 3045659) B3045659
theorem B2284249 : Blo 2029435 2284249 := bbase (se 2 (by rfl) ⟨856593, by rfl⟩ : syracuseStep 2284249 = 1713187) (by norm_num)
theorem B3045665 : Blo 2029435 3045665 := bstep (se 2 (by rfl) ⟨1142124, by rfl⟩ : syracuseStep 3045665 = 2284249) B2284249
theorem B2030443 : Blo 2029435 2030443 := bstep (se 1 (by rfl) ⟨1522832, by rfl⟩ : syracuseStep 2030443 = 3045665) B3045665
theorem B2168257 : Blo 2029435 2168257 := bbase (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) (by norm_num)
theorem B2891009 : Blo 2029435 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B7709357 : Blo 2029435 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B5139571 : Blo 2029435 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B6852761 : Blo 2029435 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B4568507 : Blo 2029435 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B3045671 : Blo 2029435 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B2030447 : Blo 2029435 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B3045677 : Blo 2029435 3045677 := bbase (se 3 (by rfl) ⟨571064, by rfl⟩ : syracuseStep 3045677 = 1142129) (by norm_num)
theorem B2030451 : Blo 2029435 2030451 := bstep (se 1 (by rfl) ⟨1522838, by rfl⟩ : syracuseStep 2030451 = 3045677) B3045677
theorem B4568525 : Blo 2029435 4568525 := bbase (se 3 (by rfl) ⟨856598, by rfl⟩ : syracuseStep 4568525 = 1713197) (by norm_num)
theorem B3045683 : Blo 2029435 3045683 := bstep (se 1 (by rfl) ⟨2284262, by rfl⟩ : syracuseStep 3045683 = 4568525) B4568525
theorem B2030455 : Blo 2029435 2030455 := bstep (se 1 (by rfl) ⟨1522841, by rfl⟩ : syracuseStep 2030455 = 3045683) B3045683
theorem B2569801 : Blo 2029435 2569801 := bbase (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) (by norm_num)
theorem B3426401 : Blo 2029435 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B2284267 : Blo 2029435 2284267 := bstep (se 1 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 2284267 = 3426401) B3426401
theorem B3045689 : Blo 2029435 3045689 := bstep (se 2 (by rfl) ⟨1142133, by rfl⟩ : syracuseStep 3045689 = 2284267) B2284267
theorem B2030459 : Blo 2029435 2030459 := bstep (se 1 (by rfl) ⟨1522844, by rfl⟩ : syracuseStep 2030459 = 3045689) B3045689
theorem B9261749 : Blo 2029435 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B24697997 : Blo 2029435 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B16465331 : Blo 2029435 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B10976887 : Blo 2029435 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B14635849 : Blo 2029435 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B19514465 : Blo 2029435 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B13009643 : Blo 2029435 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B8673095 : Blo 2029435 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B23128253 : Blo 2029435 23128253 := bstep (se 3 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 23128253 = 8673095) B8673095
theorem B15418835 : Blo 2029435 15418835 := bstep (se 1 (by rfl) ⟨11564126, by rfl⟩ : syracuseStep 15418835 = 23128253) B23128253
theorem B10279223 : Blo 2029435 10279223 := bstep (se 1 (by rfl) ⟨7709417, by rfl⟩ : syracuseStep 10279223 = 15418835) B15418835
theorem B6852815 : Blo 2029435 6852815 := bstep (se 1 (by rfl) ⟨5139611, by rfl⟩ : syracuseStep 6852815 = 10279223) B10279223
theorem B4568543 : Blo 2029435 4568543 := bstep (se 1 (by rfl) ⟨3426407, by rfl⟩ : syracuseStep 4568543 = 6852815) B6852815
theorem B3045695 : Blo 2029435 3045695 := bstep (se 1 (by rfl) ⟨2284271, by rfl⟩ : syracuseStep 3045695 = 4568543) B4568543
theorem B2030463 : Blo 2029435 2030463 := bstep (se 1 (by rfl) ⟨1522847, by rfl⟩ : syracuseStep 2030463 = 3045695) B3045695
theorem B3045701 : Blo 2029435 3045701 := bbase (se 4 (by rfl) ⟨285534, by rfl⟩ : syracuseStep 3045701 = 571069) (by norm_num)
theorem B2030467 : Blo 2029435 2030467 := bstep (se 1 (by rfl) ⟨1522850, by rfl⟩ : syracuseStep 2030467 = 3045701) B3045701
theorem B3426421 : Blo 2029435 3426421 := bbase (se 5 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 3426421 = 321227) (by norm_num)
theorem B4568561 : Blo 2029435 4568561 := bstep (se 2 (by rfl) ⟨1713210, by rfl⟩ : syracuseStep 4568561 = 3426421) B3426421
theorem B3045707 : Blo 2029435 3045707 := bstep (se 1 (by rfl) ⟨2284280, by rfl⟩ : syracuseStep 3045707 = 4568561) B4568561
theorem B2030471 : Blo 2029435 2030471 := bstep (se 1 (by rfl) ⟨1522853, by rfl⟩ : syracuseStep 2030471 = 3045707) B3045707
theorem B2284285 : Blo 2029435 2284285 := bbase (se 3 (by rfl) ⟨428303, by rfl⟩ : syracuseStep 2284285 = 856607) (by norm_num)
theorem B3045713 : Blo 2029435 3045713 := bstep (se 2 (by rfl) ⟨1142142, by rfl⟩ : syracuseStep 3045713 = 2284285) B2284285
theorem B2030475 : Blo 2029435 2030475 := bstep (se 1 (by rfl) ⟨1522856, by rfl⟩ : syracuseStep 2030475 = 3045713) B3045713
theorem B6852869 : Blo 2029435 6852869 := bbase (se 4 (by rfl) ⟨642456, by rfl⟩ : syracuseStep 6852869 = 1284913) (by norm_num)
theorem B4568579 : Blo 2029435 4568579 := bstep (se 1 (by rfl) ⟨3426434, by rfl⟩ : syracuseStep 4568579 = 6852869) B6852869
theorem B3045719 : Blo 2029435 3045719 := bstep (se 1 (by rfl) ⟨2284289, by rfl⟩ : syracuseStep 3045719 = 4568579) B4568579
theorem B2030479 : Blo 2029435 2030479 := bstep (se 1 (by rfl) ⟨1522859, by rfl⟩ : syracuseStep 2030479 = 3045719) B3045719
theorem B3045725 : Blo 2029435 3045725 := bbase (se 3 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 3045725 = 1142147) (by norm_num)
theorem B2030483 : Blo 2029435 2030483 := bstep (se 1 (by rfl) ⟨1522862, by rfl⟩ : syracuseStep 2030483 = 3045725) B3045725
theorem B4568597 : Blo 2029435 4568597 := bbase (se 6 (by rfl) ⟨107076, by rfl⟩ : syracuseStep 4568597 = 214153) (by norm_num)
theorem B3045731 : Blo 2029435 3045731 := bstep (se 1 (by rfl) ⟨2284298, by rfl⟩ : syracuseStep 3045731 = 4568597) B4568597
theorem B2030487 : Blo 2029435 2030487 := bstep (se 1 (by rfl) ⟨1522865, by rfl⟩ : syracuseStep 2030487 = 3045731) B3045731
theorem B7709525 : Blo 2029435 7709525 := bbase (se 9 (by rfl) ⟨22586, by rfl⟩ : syracuseStep 7709525 = 45173) (by norm_num)
theorem B5139683 : Blo 2029435 5139683 := bstep (se 1 (by rfl) ⟨3854762, by rfl⟩ : syracuseStep 5139683 = 7709525) B7709525
theorem B3426455 : Blo 2029435 3426455 := bstep (se 1 (by rfl) ⟨2569841, by rfl⟩ : syracuseStep 3426455 = 5139683) B5139683
theorem B2284303 : Blo 2029435 2284303 := bstep (se 1 (by rfl) ⟨1713227, by rfl⟩ : syracuseStep 2284303 = 3426455) B3426455
theorem B3045737 : Blo 2029435 3045737 := bstep (se 2 (by rfl) ⟨1142151, by rfl⟩ : syracuseStep 3045737 = 2284303) B2284303
theorem B2030491 : Blo 2029435 2030491 := bstep (se 1 (by rfl) ⟨1522868, by rfl⟩ : syracuseStep 2030491 = 3045737) B3045737
theorem B11564309 : Blo 2029435 11564309 := bbase (se 6 (by rfl) ⟨271038, by rfl⟩ : syracuseStep 11564309 = 542077) (by norm_num)
theorem B7709539 : Blo 2029435 7709539 := bstep (se 1 (by rfl) ⟨5782154, by rfl⟩ : syracuseStep 7709539 = 11564309) B11564309
theorem B10279385 : Blo 2029435 10279385 := bstep (se 2 (by rfl) ⟨3854769, by rfl⟩ : syracuseStep 10279385 = 7709539) B7709539
theorem B6852923 : Blo 2029435 6852923 := bstep (se 1 (by rfl) ⟨5139692, by rfl⟩ : syracuseStep 6852923 = 10279385) B10279385
theorem B4568615 : Blo 2029435 4568615 := bstep (se 1 (by rfl) ⟨3426461, by rfl⟩ : syracuseStep 4568615 = 6852923) B6852923
theorem B3045743 : Blo 2029435 3045743 := bstep (se 1 (by rfl) ⟨2284307, by rfl⟩ : syracuseStep 3045743 = 4568615) B4568615
theorem B2030495 : Blo 2029435 2030495 := bstep (se 1 (by rfl) ⟨1522871, by rfl⟩ : syracuseStep 2030495 = 3045743) B3045743
theorem B3045749 : Blo 2029435 3045749 := bbase (se 5 (by rfl) ⟨142769, by rfl⟩ : syracuseStep 3045749 = 285539) (by norm_num)
theorem B2030499 : Blo 2029435 2030499 := bstep (se 1 (by rfl) ⟨1522874, by rfl⟩ : syracuseStep 2030499 = 3045749) B3045749
theorem B2168317 : Blo 2029435 2168317 := bbase (se 3 (by rfl) ⟨406559, by rfl⟩ : syracuseStep 2168317 = 813119) (by norm_num)
theorem B2891089 : Blo 2029435 2891089 := bstep (se 2 (by rfl) ⟨1084158, by rfl⟩ : syracuseStep 2891089 = 2168317) B2168317
theorem B3854785 : Blo 2029435 3854785 := bstep (se 2 (by rfl) ⟨1445544, by rfl⟩ : syracuseStep 3854785 = 2891089) B2891089
theorem B5139713 : Blo 2029435 5139713 := bstep (se 2 (by rfl) ⟨1927392, by rfl⟩ : syracuseStep 5139713 = 3854785) B3854785
theorem B3426475 : Blo 2029435 3426475 := bstep (se 1 (by rfl) ⟨2569856, by rfl⟩ : syracuseStep 3426475 = 5139713) B5139713
theorem B4568633 : Blo 2029435 4568633 := bstep (se 2 (by rfl) ⟨1713237, by rfl⟩ : syracuseStep 4568633 = 3426475) B3426475
theorem B3045755 : Blo 2029435 3045755 := bstep (se 1 (by rfl) ⟨2284316, by rfl⟩ : syracuseStep 3045755 = 4568633) B4568633
theorem B2030503 : Blo 2029435 2030503 := bstep (se 1 (by rfl) ⟨1522877, by rfl⟩ : syracuseStep 2030503 = 3045755) B3045755
theorem B2284321 : Blo 2029435 2284321 := bbase (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) (by norm_num)
theorem B3045761 : Blo 2029435 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B2030507 : Blo 2029435 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B5139733 : Blo 2029435 5139733 := bbase (se 6 (by rfl) ⟨120462, by rfl⟩ : syracuseStep 5139733 = 240925) (by norm_num)
theorem B6852977 : Blo 2029435 6852977 := bstep (se 2 (by rfl) ⟨2569866, by rfl⟩ : syracuseStep 6852977 = 5139733) B5139733
theorem B4568651 : Blo 2029435 4568651 := bstep (se 1 (by rfl) ⟨3426488, by rfl⟩ : syracuseStep 4568651 = 6852977) B6852977
theorem B3045767 : Blo 2029435 3045767 := bstep (se 1 (by rfl) ⟨2284325, by rfl⟩ : syracuseStep 3045767 = 4568651) B4568651
theorem B2030511 : Blo 2029435 2030511 := bstep (se 1 (by rfl) ⟨1522883, by rfl⟩ : syracuseStep 2030511 = 3045767) B3045767
theorem B3045773 : Blo 2029435 3045773 := bbase (se 3 (by rfl) ⟨571082, by rfl⟩ : syracuseStep 3045773 = 1142165) (by norm_num)
theorem B2030515 : Blo 2029435 2030515 := bstep (se 1 (by rfl) ⟨1522886, by rfl⟩ : syracuseStep 2030515 = 3045773) B3045773
theorem B4568669 : Blo 2029435 4568669 := bbase (se 3 (by rfl) ⟨856625, by rfl⟩ : syracuseStep 4568669 = 1713251) (by norm_num)
theorem B3045779 : Blo 2029435 3045779 := bstep (se 1 (by rfl) ⟨2284334, by rfl⟩ : syracuseStep 3045779 = 4568669) B4568669
theorem B2030519 : Blo 2029435 2030519 := bstep (se 1 (by rfl) ⟨1522889, by rfl⟩ : syracuseStep 2030519 = 3045779) B3045779
theorem B3426509 : Blo 2029435 3426509 := bbase (se 3 (by rfl) ⟨642470, by rfl⟩ : syracuseStep 3426509 = 1284941) (by norm_num)
theorem B2284339 : Blo 2029435 2284339 := bstep (se 1 (by rfl) ⟨1713254, by rfl⟩ : syracuseStep 2284339 = 3426509) B3426509
theorem B3045785 : Blo 2029435 3045785 := bstep (se 2 (by rfl) ⟨1142169, by rfl⟩ : syracuseStep 3045785 = 2284339) B2284339
theorem B2030523 : Blo 2029435 2030523 := bstep (se 1 (by rfl) ⟨1522892, by rfl⟩ : syracuseStep 2030523 = 3045785) B3045785
theorem B2439385 : Blo 2029435 2439385 := bbase (se 2 (by rfl) ⟨914769, by rfl⟩ : syracuseStep 2439385 = 1829539) (by norm_num)
theorem B13010053 : Blo 2029435 13010053 := bstep (se 4 (by rfl) ⟨1219692, by rfl⟩ : syracuseStep 13010053 = 2439385) B2439385
theorem B17346737 : Blo 2029435 17346737 := bstep (se 2 (by rfl) ⟨6505026, by rfl⟩ : syracuseStep 17346737 = 13010053) B13010053
theorem B11564491 : Blo 2029435 11564491 := bstep (se 1 (by rfl) ⟨8673368, by rfl⟩ : syracuseStep 11564491 = 17346737) B17346737
theorem B15419321 : Blo 2029435 15419321 := bstep (se 2 (by rfl) ⟨5782245, by rfl⟩ : syracuseStep 15419321 = 11564491) B11564491
theorem B10279547 : Blo 2029435 10279547 := bstep (se 1 (by rfl) ⟨7709660, by rfl⟩ : syracuseStep 10279547 = 15419321) B15419321
theorem B6853031 : Blo 2029435 6853031 := bstep (se 1 (by rfl) ⟨5139773, by rfl⟩ : syracuseStep 6853031 = 10279547) B10279547
theorem B4568687 : Blo 2029435 4568687 := bstep (se 1 (by rfl) ⟨3426515, by rfl⟩ : syracuseStep 4568687 = 6853031) B6853031
theorem B3045791 : Blo 2029435 3045791 := bstep (se 1 (by rfl) ⟨2284343, by rfl⟩ : syracuseStep 3045791 = 4568687) B4568687
theorem B2030527 : Blo 2029435 2030527 := bstep (se 1 (by rfl) ⟨1522895, by rfl⟩ : syracuseStep 2030527 = 3045791) B3045791
theorem B3045797 : Blo 2029435 3045797 := bbase (se 4 (by rfl) ⟨285543, by rfl⟩ : syracuseStep 3045797 = 571087) (by norm_num)
theorem B2030531 : Blo 2029435 2030531 := bstep (se 1 (by rfl) ⟨1522898, by rfl⟩ : syracuseStep 2030531 = 3045797) B3045797
theorem B2569897 : Blo 2029435 2569897 := bbase (se 2 (by rfl) ⟨963711, by rfl⟩ : syracuseStep 2569897 = 1927423) (by norm_num)
theorem B3426529 : Blo 2029435 3426529 := bstep (se 2 (by rfl) ⟨1284948, by rfl⟩ : syracuseStep 3426529 = 2569897) B2569897
theorem B4568705 : Blo 2029435 4568705 := bstep (se 2 (by rfl) ⟨1713264, by rfl⟩ : syracuseStep 4568705 = 3426529) B3426529
theorem B3045803 : Blo 2029435 3045803 := bstep (se 1 (by rfl) ⟨2284352, by rfl⟩ : syracuseStep 3045803 = 4568705) B4568705
theorem B2030535 : Blo 2029435 2030535 := bstep (se 1 (by rfl) ⟨1522901, by rfl⟩ : syracuseStep 2030535 = 3045803) B3045803
theorem B2284357 : Blo 2029435 2284357 := bbase (se 4 (by rfl) ⟨214158, by rfl⟩ : syracuseStep 2284357 = 428317) (by norm_num)
theorem B3045809 : Blo 2029435 3045809 := bstep (se 2 (by rfl) ⟨1142178, by rfl⟩ : syracuseStep 3045809 = 2284357) B2284357
theorem B2030539 : Blo 2029435 2030539 := bstep (se 1 (by rfl) ⟨1522904, by rfl⟩ : syracuseStep 2030539 = 3045809) B3045809
theorem B3854861 : Blo 2029435 3854861 := bbase (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) (by norm_num)
theorem B2569907 : Blo 2029435 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B6853085 : Blo 2029435 6853085 := bstep (se 3 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 6853085 = 2569907) B2569907
theorem B4568723 : Blo 2029435 4568723 := bstep (se 1 (by rfl) ⟨3426542, by rfl⟩ : syracuseStep 4568723 = 6853085) B6853085
theorem B3045815 : Blo 2029435 3045815 := bstep (se 1 (by rfl) ⟨2284361, by rfl⟩ : syracuseStep 3045815 = 4568723) B4568723
theorem B2030543 : Blo 2029435 2030543 := bstep (se 1 (by rfl) ⟨1522907, by rfl⟩ : syracuseStep 2030543 = 3045815) B3045815
theorem B3045821 : Blo 2029435 3045821 := bbase (se 3 (by rfl) ⟨571091, by rfl⟩ : syracuseStep 3045821 = 1142183) (by norm_num)
theorem B2030547 : Blo 2029435 2030547 := bstep (se 1 (by rfl) ⟨1522910, by rfl⟩ : syracuseStep 2030547 = 3045821) B3045821
theorem B4568741 : Blo 2029435 4568741 := bbase (se 4 (by rfl) ⟨428319, by rfl⟩ : syracuseStep 4568741 = 856639) (by norm_num)
theorem B3045827 : Blo 2029435 3045827 := bstep (se 1 (by rfl) ⟨2284370, by rfl⟩ : syracuseStep 3045827 = 4568741) B4568741
theorem B2030551 : Blo 2029435 2030551 := bstep (se 1 (by rfl) ⟨1522913, by rfl⟩ : syracuseStep 2030551 = 3045827) B3045827
theorem B5139845 : Blo 2029435 5139845 := bbase (se 4 (by rfl) ⟨481860, by rfl⟩ : syracuseStep 5139845 = 963721) (by norm_num)
theorem B3426563 : Blo 2029435 3426563 := bstep (se 1 (by rfl) ⟨2569922, by rfl⟩ : syracuseStep 3426563 = 5139845) B5139845
theorem B2284375 : Blo 2029435 2284375 := bstep (se 1 (by rfl) ⟨1713281, by rfl⟩ : syracuseStep 2284375 = 3426563) B3426563
theorem B3045833 : Blo 2029435 3045833 := bstep (se 2 (by rfl) ⟨1142187, by rfl⟩ : syracuseStep 3045833 = 2284375) B2284375
theorem B2030555 : Blo 2029435 2030555 := bstep (se 1 (by rfl) ⟨1522916, by rfl⟩ : syracuseStep 2030555 = 3045833) B3045833
theorem B3252565 : Blo 2029435 3252565 := bbase (se 10 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 3252565 = 9529) (by norm_num)
theorem B4336753 : Blo 2029435 4336753 := bstep (se 2 (by rfl) ⟨1626282, by rfl⟩ : syracuseStep 4336753 = 3252565) B3252565
theorem B5782337 : Blo 2029435 5782337 := bstep (se 2 (by rfl) ⟨2168376, by rfl⟩ : syracuseStep 5782337 = 4336753) B4336753
theorem B3854891 : Blo 2029435 3854891 := bstep (se 1 (by rfl) ⟨2891168, by rfl⟩ : syracuseStep 3854891 = 5782337) B5782337
theorem B10279709 : Blo 2029435 10279709 := bstep (se 3 (by rfl) ⟨1927445, by rfl⟩ : syracuseStep 10279709 = 3854891) B3854891
theorem B6853139 : Blo 2029435 6853139 := bstep (se 1 (by rfl) ⟨5139854, by rfl⟩ : syracuseStep 6853139 = 10279709) B10279709
theorem B4568759 : Blo 2029435 4568759 := bstep (se 1 (by rfl) ⟨3426569, by rfl⟩ : syracuseStep 4568759 = 6853139) B6853139
theorem B3045839 : Blo 2029435 3045839 := bstep (se 1 (by rfl) ⟨2284379, by rfl⟩ : syracuseStep 3045839 = 4568759) B4568759
theorem B2030559 : Blo 2029435 2030559 := bstep (se 1 (by rfl) ⟨1522919, by rfl⟩ : syracuseStep 2030559 = 3045839) B3045839
theorem B3045845 : Blo 2029435 3045845 := bbase (se 7 (by rfl) ⟨35693, by rfl⟩ : syracuseStep 3045845 = 71387) (by norm_num)
theorem B2030563 : Blo 2029435 2030563 := bstep (se 1 (by rfl) ⟨1522922, by rfl⟩ : syracuseStep 2030563 = 3045845) B3045845
theorem B7709813 : Blo 2029435 7709813 := bbase (se 5 (by rfl) ⟨361397, by rfl⟩ : syracuseStep 7709813 = 722795) (by norm_num)
theorem B5139875 : Blo 2029435 5139875 := bstep (se 1 (by rfl) ⟨3854906, by rfl⟩ : syracuseStep 5139875 = 7709813) B7709813
theorem B3426583 : Blo 2029435 3426583 := bstep (se 1 (by rfl) ⟨2569937, by rfl⟩ : syracuseStep 3426583 = 5139875) B5139875
theorem B4568777 : Blo 2029435 4568777 := bstep (se 2 (by rfl) ⟨1713291, by rfl⟩ : syracuseStep 4568777 = 3426583) B3426583
theorem B3045851 : Blo 2029435 3045851 := bstep (se 1 (by rfl) ⟨2284388, by rfl⟩ : syracuseStep 3045851 = 4568777) B4568777
theorem B2030567 : Blo 2029435 2030567 := bstep (se 1 (by rfl) ⟨1522925, by rfl⟩ : syracuseStep 2030567 = 3045851) B3045851
theorem B2284393 : Blo 2029435 2284393 := bbase (se 2 (by rfl) ⟨856647, by rfl⟩ : syracuseStep 2284393 = 1713295) (by norm_num)
theorem B3045857 : Blo 2029435 3045857 := bstep (se 2 (by rfl) ⟨1142196, by rfl⟩ : syracuseStep 3045857 = 2284393) B2284393
theorem B2030571 : Blo 2029435 2030571 := bstep (se 1 (by rfl) ⟨1522928, by rfl⟩ : syracuseStep 2030571 = 3045857) B3045857
theorem B3659165 : Blo 2029435 3659165 := bbase (se 3 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 3659165 = 1372187) (by norm_num)
theorem B2439443 : Blo 2029435 2439443 := bstep (se 1 (by rfl) ⟨1829582, by rfl⟩ : syracuseStep 2439443 = 3659165) B3659165
theorem B6505181 : Blo 2029435 6505181 := bstep (se 3 (by rfl) ⟨1219721, by rfl⟩ : syracuseStep 6505181 = 2439443) B2439443
theorem B4336787 : Blo 2029435 4336787 := bstep (se 1 (by rfl) ⟨3252590, by rfl⟩ : syracuseStep 4336787 = 6505181) B6505181
theorem B11564765 : Blo 2029435 11564765 := bstep (se 3 (by rfl) ⟨2168393, by rfl⟩ : syracuseStep 11564765 = 4336787) B4336787
theorem B7709843 : Blo 2029435 7709843 := bstep (se 1 (by rfl) ⟨5782382, by rfl⟩ : syracuseStep 7709843 = 11564765) B11564765
theorem B5139895 : Blo 2029435 5139895 := bstep (se 1 (by rfl) ⟨3854921, by rfl⟩ : syracuseStep 5139895 = 7709843) B7709843
theorem B6853193 : Blo 2029435 6853193 := bstep (se 2 (by rfl) ⟨2569947, by rfl⟩ : syracuseStep 6853193 = 5139895) B5139895
theorem B4568795 : Blo 2029435 4568795 := bstep (se 1 (by rfl) ⟨3426596, by rfl⟩ : syracuseStep 4568795 = 6853193) B6853193
theorem B3045863 : Blo 2029435 3045863 := bstep (se 1 (by rfl) ⟨2284397, by rfl⟩ : syracuseStep 3045863 = 4568795) B4568795
theorem B2030575 : Blo 2029435 2030575 := bstep (se 1 (by rfl) ⟨1522931, by rfl⟩ : syracuseStep 2030575 = 3045863) B3045863
theorem B3045869 : Blo 2029435 3045869 := bbase (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) (by norm_num)
theorem B2030579 : Blo 2029435 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B4568813 : Blo 2029435 4568813 := bbase (se 3 (by rfl) ⟨856652, by rfl⟩ : syracuseStep 4568813 = 1713305) (by norm_num)
theorem B3045875 : Blo 2029435 3045875 := bstep (se 1 (by rfl) ⟨2284406, by rfl⟩ : syracuseStep 3045875 = 4568813) B4568813
theorem B2030583 : Blo 2029435 2030583 := bstep (se 1 (by rfl) ⟨1522937, by rfl⟩ : syracuseStep 2030583 = 3045875) B3045875
theorem B4878917 : Blo 2029435 4878917 := bbase (se 4 (by rfl) ⟨457398, by rfl⟩ : syracuseStep 4878917 = 914797) (by norm_num)
theorem B3252611 : Blo 2029435 3252611 := bstep (se 1 (by rfl) ⟨2439458, by rfl⟩ : syracuseStep 3252611 = 4878917) B4878917
theorem B2168407 : Blo 2029435 2168407 := bstep (se 1 (by rfl) ⟨1626305, by rfl⟩ : syracuseStep 2168407 = 3252611) B3252611
theorem B2891209 : Blo 2029435 2891209 := bstep (se 2 (by rfl) ⟨1084203, by rfl⟩ : syracuseStep 2891209 = 2168407) B2168407
theorem B3854945 : Blo 2029435 3854945 := bstep (se 2 (by rfl) ⟨1445604, by rfl⟩ : syracuseStep 3854945 = 2891209) B2891209
theorem B2569963 : Blo 2029435 2569963 := bstep (se 1 (by rfl) ⟨1927472, by rfl⟩ : syracuseStep 2569963 = 3854945) B3854945
theorem B3426617 : Blo 2029435 3426617 := bstep (se 2 (by rfl) ⟨1284981, by rfl⟩ : syracuseStep 3426617 = 2569963) B2569963
theorem B2284411 : Blo 2029435 2284411 := bstep (se 1 (by rfl) ⟨1713308, by rfl⟩ : syracuseStep 2284411 = 3426617) B3426617
theorem B3045881 : Blo 2029435 3045881 := bstep (se 2 (by rfl) ⟨1142205, by rfl⟩ : syracuseStep 3045881 = 2284411) B2284411
theorem B2030587 : Blo 2029435 2030587 := bstep (se 1 (by rfl) ⟨1522940, by rfl⟩ : syracuseStep 2030587 = 3045881) B3045881
theorem B11127349 : Blo 2029435 11127349 := bbase (se 5 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 11127349 = 1043189) (by norm_num)
theorem B14836465 : Blo 2029435 14836465 := bstep (se 2 (by rfl) ⟨5563674, by rfl⟩ : syracuseStep 14836465 = 11127349) B11127349
theorem B79127813 : Blo 2029435 79127813 := bstep (se 4 (by rfl) ⟨7418232, by rfl⟩ : syracuseStep 79127813 = 14836465) B14836465
theorem B211007501 : Blo 2029435 211007501 := bstep (se 3 (by rfl) ⟨39563906, by rfl⟩ : syracuseStep 211007501 = 79127813) B79127813
theorem B140671667 : Blo 2029435 140671667 := bstep (se 1 (by rfl) ⟨105503750, by rfl⟩ : syracuseStep 140671667 = 211007501) B211007501
theorem B93781111 : Blo 2029435 93781111 := bstep (se 1 (by rfl) ⟨70335833, by rfl⟩ : syracuseStep 93781111 = 140671667) B140671667
theorem B125041481 : Blo 2029435 125041481 := bstep (se 2 (by rfl) ⟨46890555, by rfl⟩ : syracuseStep 125041481 = 93781111) B93781111
theorem B83360987 : Blo 2029435 83360987 := bstep (se 1 (by rfl) ⟨62520740, by rfl⟩ : syracuseStep 83360987 = 125041481) B125041481
theorem B55573991 : Blo 2029435 55573991 := bstep (se 1 (by rfl) ⟨41680493, by rfl⟩ : syracuseStep 55573991 = 83360987) B83360987
theorem B37049327 : Blo 2029435 37049327 := bstep (se 1 (by rfl) ⟨27786995, by rfl⟩ : syracuseStep 37049327 = 55573991) B55573991
theorem B24699551 : Blo 2029435 24699551 := bstep (se 1 (by rfl) ⟨18524663, by rfl⟩ : syracuseStep 24699551 = 37049327) B37049327
theorem B65865469 : Blo 2029435 65865469 := bstep (se 3 (by rfl) ⟨12349775, by rfl⟩ : syracuseStep 65865469 = 24699551) B24699551
theorem B87820625 : Blo 2029435 87820625 := bstep (se 2 (by rfl) ⟨32932734, by rfl⟩ : syracuseStep 87820625 = 65865469) B65865469
theorem B58547083 : Blo 2029435 58547083 := bstep (se 1 (by rfl) ⟨43910312, by rfl⟩ : syracuseStep 58547083 = 87820625) B87820625
theorem B78062777 : Blo 2029435 78062777 := bstep (se 2 (by rfl) ⟨29273541, by rfl⟩ : syracuseStep 78062777 = 58547083) B58547083
theorem B52041851 : Blo 2029435 52041851 := bstep (se 1 (by rfl) ⟨39031388, by rfl⟩ : syracuseStep 52041851 = 78062777) B78062777
theorem B34694567 : Blo 2029435 34694567 := bstep (se 1 (by rfl) ⟨26020925, by rfl⟩ : syracuseStep 34694567 = 52041851) B52041851
theorem B23129711 : Blo 2029435 23129711 := bstep (se 1 (by rfl) ⟨17347283, by rfl⟩ : syracuseStep 23129711 = 34694567) B34694567
theorem B15419807 : Blo 2029435 15419807 := bstep (se 1 (by rfl) ⟨11564855, by rfl⟩ : syracuseStep 15419807 = 23129711) B23129711
theorem B10279871 : Blo 2029435 10279871 := bstep (se 1 (by rfl) ⟨7709903, by rfl⟩ : syracuseStep 10279871 = 15419807) B15419807
theorem B6853247 : Blo 2029435 6853247 := bstep (se 1 (by rfl) ⟨5139935, by rfl⟩ : syracuseStep 6853247 = 10279871) B10279871
theorem B4568831 : Blo 2029435 4568831 := bstep (se 1 (by rfl) ⟨3426623, by rfl⟩ : syracuseStep 4568831 = 6853247) B6853247
theorem B3045887 : Blo 2029435 3045887 := bstep (se 1 (by rfl) ⟨2284415, by rfl⟩ : syracuseStep 3045887 = 4568831) B4568831
theorem B2030591 : Blo 2029435 2030591 := bstep (se 1 (by rfl) ⟨1522943, by rfl⟩ : syracuseStep 2030591 = 3045887) B3045887
theorem B3045893 : Blo 2029435 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B2030595 : Blo 2029435 2030595 := bstep (se 1 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 2030595 = 3045893) B3045893
theorem B3426637 : Blo 2029435 3426637 := bbase (se 3 (by rfl) ⟨642494, by rfl⟩ : syracuseStep 3426637 = 1284989) (by norm_num)
theorem B4568849 : Blo 2029435 4568849 := bstep (se 2 (by rfl) ⟨1713318, by rfl⟩ : syracuseStep 4568849 = 3426637) B3426637
theorem B3045899 : Blo 2029435 3045899 := bstep (se 1 (by rfl) ⟨2284424, by rfl⟩ : syracuseStep 3045899 = 4568849) B4568849
theorem B2030599 : Blo 2029435 2030599 := bstep (se 1 (by rfl) ⟨1522949, by rfl⟩ : syracuseStep 2030599 = 3045899) B3045899
theorem B2284429 : Blo 2029435 2284429 := bbase (se 3 (by rfl) ⟨428330, by rfl⟩ : syracuseStep 2284429 = 856661) (by norm_num)
theorem B3045905 : Blo 2029435 3045905 := bstep (se 2 (by rfl) ⟨1142214, by rfl⟩ : syracuseStep 3045905 = 2284429) B2284429
theorem B2030603 : Blo 2029435 2030603 := bstep (se 1 (by rfl) ⟨1522952, by rfl⟩ : syracuseStep 2030603 = 3045905) B3045905
theorem B6853301 : Blo 2029435 6853301 := bbase (se 5 (by rfl) ⟨321248, by rfl⟩ : syracuseStep 6853301 = 642497) (by norm_num)
theorem B4568867 : Blo 2029435 4568867 := bstep (se 1 (by rfl) ⟨3426650, by rfl⟩ : syracuseStep 4568867 = 6853301) B6853301
theorem B3045911 : Blo 2029435 3045911 := bstep (se 1 (by rfl) ⟨2284433, by rfl⟩ : syracuseStep 3045911 = 4568867) B4568867
theorem B2030607 : Blo 2029435 2030607 := bstep (se 1 (by rfl) ⟨1522955, by rfl⟩ : syracuseStep 2030607 = 3045911) B3045911
theorem B3045917 : Blo 2029435 3045917 := bbase (se 3 (by rfl) ⟨571109, by rfl⟩ : syracuseStep 3045917 = 1142219) (by norm_num)
theorem B2030611 : Blo 2029435 2030611 := bstep (se 1 (by rfl) ⟨1522958, by rfl⟩ : syracuseStep 2030611 = 3045917) B3045917
theorem B4568885 : Blo 2029435 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B3045923 : Blo 2029435 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B2030615 : Blo 2029435 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B13010645 : Blo 2029435 13010645 := bbase (se 7 (by rfl) ⟨152468, by rfl⟩ : syracuseStep 13010645 = 304937) (by norm_num)
theorem B8673763 : Blo 2029435 8673763 := bstep (se 1 (by rfl) ⟨6505322, by rfl⟩ : syracuseStep 8673763 = 13010645) B13010645
theorem B11565017 : Blo 2029435 11565017 := bstep (se 2 (by rfl) ⟨4336881, by rfl⟩ : syracuseStep 11565017 = 8673763) B8673763
theorem B7710011 : Blo 2029435 7710011 := bstep (se 1 (by rfl) ⟨5782508, by rfl⟩ : syracuseStep 7710011 = 11565017) B11565017
theorem B5140007 : Blo 2029435 5140007 := bstep (se 1 (by rfl) ⟨3855005, by rfl⟩ : syracuseStep 5140007 = 7710011) B7710011
theorem B3426671 : Blo 2029435 3426671 := bstep (se 1 (by rfl) ⟨2570003, by rfl⟩ : syracuseStep 3426671 = 5140007) B5140007
theorem B2284447 : Blo 2029435 2284447 := bstep (se 1 (by rfl) ⟨1713335, by rfl⟩ : syracuseStep 2284447 = 3426671) B3426671
theorem B3045929 : Blo 2029435 3045929 := bstep (se 2 (by rfl) ⟨1142223, by rfl⟩ : syracuseStep 3045929 = 2284447) B2284447
theorem B2030619 : Blo 2029435 2030619 := bstep (se 1 (by rfl) ⟨1522964, by rfl⟩ : syracuseStep 2030619 = 3045929) B3045929
theorem B2058329 : Blo 2029435 2058329 := bbase (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) (by norm_num)
theorem B5488877 : Blo 2029435 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B3659251 : Blo 2029435 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B4879001 : Blo 2029435 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B13010669 : Blo 2029435 13010669 := bstep (se 3 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 13010669 = 4879001) B4879001
theorem B8673779 : Blo 2029435 8673779 := bstep (se 1 (by rfl) ⟨6505334, by rfl⟩ : syracuseStep 8673779 = 13010669) B13010669
theorem B5782519 : Blo 2029435 5782519 := bstep (se 1 (by rfl) ⟨4336889, by rfl⟩ : syracuseStep 5782519 = 8673779) B8673779
theorem B7710025 : Blo 2029435 7710025 := bstep (se 2 (by rfl) ⟨2891259, by rfl⟩ : syracuseStep 7710025 = 5782519) B5782519
theorem B10280033 : Blo 2029435 10280033 := bstep (se 2 (by rfl) ⟨3855012, by rfl⟩ : syracuseStep 10280033 = 7710025) B7710025
theorem B6853355 : Blo 2029435 6853355 := bstep (se 1 (by rfl) ⟨5140016, by rfl⟩ : syracuseStep 6853355 = 10280033) B10280033
theorem B4568903 : Blo 2029435 4568903 := bstep (se 1 (by rfl) ⟨3426677, by rfl⟩ : syracuseStep 4568903 = 6853355) B6853355
theorem B3045935 : Blo 2029435 3045935 := bstep (se 1 (by rfl) ⟨2284451, by rfl⟩ : syracuseStep 3045935 = 4568903) B4568903
theorem B2030623 : Blo 2029435 2030623 := bstep (se 1 (by rfl) ⟨1522967, by rfl⟩ : syracuseStep 2030623 = 3045935) B3045935
theorem B3045941 : Blo 2029435 3045941 := bbase (se 5 (by rfl) ⟨142778, by rfl⟩ : syracuseStep 3045941 = 285557) (by norm_num)
theorem B2030627 : Blo 2029435 2030627 := bstep (se 1 (by rfl) ⟨1522970, by rfl⟩ : syracuseStep 2030627 = 3045941) B3045941
theorem B5140037 : Blo 2029435 5140037 := bbase (se 4 (by rfl) ⟨481878, by rfl⟩ : syracuseStep 5140037 = 963757) (by norm_num)
theorem B3426691 : Blo 2029435 3426691 := bstep (se 1 (by rfl) ⟨2570018, by rfl⟩ : syracuseStep 3426691 = 5140037) B5140037
theorem B4568921 : Blo 2029435 4568921 := bstep (se 2 (by rfl) ⟨1713345, by rfl⟩ : syracuseStep 4568921 = 3426691) B3426691
theorem B3045947 : Blo 2029435 3045947 := bstep (se 1 (by rfl) ⟨2284460, by rfl⟩ : syracuseStep 3045947 = 4568921) B4568921
theorem B2030631 : Blo 2029435 2030631 := bstep (se 1 (by rfl) ⟨1522973, by rfl⟩ : syracuseStep 2030631 = 3045947) B3045947
theorem B2284465 : Blo 2029435 2284465 := bbase (se 2 (by rfl) ⟨856674, by rfl⟩ : syracuseStep 2284465 = 1713349) (by norm_num)
theorem B3045953 : Blo 2029435 3045953 := bstep (se 2 (by rfl) ⟨1142232, by rfl⟩ : syracuseStep 3045953 = 2284465) B2284465
theorem B2030635 : Blo 2029435 2030635 := bstep (se 1 (by rfl) ⟨1522976, by rfl⟩ : syracuseStep 2030635 = 3045953) B3045953
theorem B5782565 : Blo 2029435 5782565 := bbase (se 4 (by rfl) ⟨542115, by rfl⟩ : syracuseStep 5782565 = 1084231) (by norm_num)
theorem B3855043 : Blo 2029435 3855043 := bstep (se 1 (by rfl) ⟨2891282, by rfl⟩ : syracuseStep 3855043 = 5782565) B5782565
theorem B5140057 : Blo 2029435 5140057 := bstep (se 2 (by rfl) ⟨1927521, by rfl⟩ : syracuseStep 5140057 = 3855043) B3855043
theorem B6853409 : Blo 2029435 6853409 := bstep (se 2 (by rfl) ⟨2570028, by rfl⟩ : syracuseStep 6853409 = 5140057) B5140057
theorem B4568939 : Blo 2029435 4568939 := bstep (se 1 (by rfl) ⟨3426704, by rfl⟩ : syracuseStep 4568939 = 6853409) B6853409
theorem B3045959 : Blo 2029435 3045959 := bstep (se 1 (by rfl) ⟨2284469, by rfl⟩ : syracuseStep 3045959 = 4568939) B4568939
theorem B2030639 : Blo 2029435 2030639 := bstep (se 1 (by rfl) ⟨1522979, by rfl⟩ : syracuseStep 2030639 = 3045959) B3045959
theorem B3045965 : Blo 2029435 3045965 := bbase (se 3 (by rfl) ⟨571118, by rfl⟩ : syracuseStep 3045965 = 1142237) (by norm_num)
theorem B2030643 : Blo 2029435 2030643 := bstep (se 1 (by rfl) ⟨1522982, by rfl⟩ : syracuseStep 2030643 = 3045965) B3045965
theorem B4568957 : Blo 2029435 4568957 := bbase (se 3 (by rfl) ⟨856679, by rfl⟩ : syracuseStep 4568957 = 1713359) (by norm_num)
theorem B3045971 : Blo 2029435 3045971 := bstep (se 1 (by rfl) ⟨2284478, by rfl⟩ : syracuseStep 3045971 = 4568957) B4568957
theorem B2030647 : Blo 2029435 2030647 := bstep (se 1 (by rfl) ⟨1522985, by rfl⟩ : syracuseStep 2030647 = 3045971) B3045971
theorem B3426725 : Blo 2029435 3426725 := bbase (se 4 (by rfl) ⟨321255, by rfl⟩ : syracuseStep 3426725 = 642511) (by norm_num)
theorem B2284483 : Blo 2029435 2284483 := bstep (se 1 (by rfl) ⟨1713362, by rfl⟩ : syracuseStep 2284483 = 3426725) B3426725
theorem B3045977 : Blo 2029435 3045977 := bstep (se 2 (by rfl) ⟨1142241, by rfl⟩ : syracuseStep 3045977 = 2284483) B2284483
theorem B2030651 : Blo 2029435 2030651 := bstep (se 1 (by rfl) ⟨1522988, by rfl⟩ : syracuseStep 2030651 = 3045977) B3045977
theorem B42250517 : Blo 2029435 42250517 := bbase (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) (by norm_num)
theorem B28167011 : Blo 2029435 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B18778007 : Blo 2029435 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B12518671 : Blo 2029435 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B16691561 : Blo 2029435 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B11127707 : Blo 2029435 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B7418471 : Blo 2029435 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B19782589 : Blo 2029435 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B26376785 : Blo 2029435 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B17584523 : Blo 2029435 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B11723015 : Blo 2029435 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B31261373 : Blo 2029435 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B20840915 : Blo 2029435 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B13893943 : Blo 2029435 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B18525257 : Blo 2029435 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B12350171 : Blo 2029435 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B8233447 : Blo 2029435 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B10977929 : Blo 2029435 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B7318619 : Blo 2029435 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B4879079 : Blo 2029435 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B3252719 : Blo 2029435 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B2168479 : Blo 2029435 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B2891305 : Blo 2029435 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B15420293 : Blo 2029435 15420293 := bstep (se 4 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 15420293 = 2891305) B2891305
theorem B10280195 : Blo 2029435 10280195 := bstep (se 1 (by rfl) ⟨7710146, by rfl⟩ : syracuseStep 10280195 = 15420293) B15420293
theorem B6853463 : Blo 2029435 6853463 := bstep (se 1 (by rfl) ⟨5140097, by rfl⟩ : syracuseStep 6853463 = 10280195) B10280195
theorem B4568975 : Blo 2029435 4568975 := bstep (se 1 (by rfl) ⟨3426731, by rfl⟩ : syracuseStep 4568975 = 6853463) B6853463
theorem B3045983 : Blo 2029435 3045983 := bstep (se 1 (by rfl) ⟨2284487, by rfl⟩ : syracuseStep 3045983 = 4568975) B4568975
theorem B2030655 : Blo 2029435 2030655 := bstep (se 1 (by rfl) ⟨1522991, by rfl⟩ : syracuseStep 2030655 = 3045983) B3045983
theorem B3045989 : Blo 2029435 3045989 := bbase (se 4 (by rfl) ⟨285561, by rfl⟩ : syracuseStep 3045989 = 571123) (by norm_num)
theorem B2030659 : Blo 2029435 2030659 := bstep (se 1 (by rfl) ⟨1522994, by rfl⟩ : syracuseStep 2030659 = 3045989) B3045989
theorem B2891317 : Blo 2029435 2891317 := bbase (se 5 (by rfl) ⟨135530, by rfl⟩ : syracuseStep 2891317 = 271061) (by norm_num)
theorem B3855089 : Blo 2029435 3855089 := bstep (se 2 (by rfl) ⟨1445658, by rfl⟩ : syracuseStep 3855089 = 2891317) B2891317
theorem B2570059 : Blo 2029435 2570059 := bstep (se 1 (by rfl) ⟨1927544, by rfl⟩ : syracuseStep 2570059 = 3855089) B3855089
theorem B3426745 : Blo 2029435 3426745 := bstep (se 2 (by rfl) ⟨1285029, by rfl⟩ : syracuseStep 3426745 = 2570059) B2570059
theorem B4568993 : Blo 2029435 4568993 := bstep (se 2 (by rfl) ⟨1713372, by rfl⟩ : syracuseStep 4568993 = 3426745) B3426745
theorem B3045995 : Blo 2029435 3045995 := bstep (se 1 (by rfl) ⟨2284496, by rfl⟩ : syracuseStep 3045995 = 4568993) B4568993
theorem B2030663 : Blo 2029435 2030663 := bstep (se 1 (by rfl) ⟨1522997, by rfl⟩ : syracuseStep 2030663 = 3045995) B3045995
theorem B2284501 : Blo 2029435 2284501 := bbase (se 7 (by rfl) ⟨26771, by rfl⟩ : syracuseStep 2284501 = 53543) (by norm_num)
theorem B3046001 : Blo 2029435 3046001 := bstep (se 2 (by rfl) ⟨1142250, by rfl⟩ : syracuseStep 3046001 = 2284501) B2284501
theorem B2030667 : Blo 2029435 2030667 := bstep (se 1 (by rfl) ⟨1523000, by rfl⟩ : syracuseStep 2030667 = 3046001) B3046001
theorem B2570069 : Blo 2029435 2570069 := bbase (se 9 (by rfl) ⟨7529, by rfl⟩ : syracuseStep 2570069 = 15059) (by norm_num)
theorem B6853517 : Blo 2029435 6853517 := bstep (se 3 (by rfl) ⟨1285034, by rfl⟩ : syracuseStep 6853517 = 2570069) B2570069
theorem B4569011 : Blo 2029435 4569011 := bstep (se 1 (by rfl) ⟨3426758, by rfl⟩ : syracuseStep 4569011 = 6853517) B6853517
theorem B3046007 : Blo 2029435 3046007 := bstep (se 1 (by rfl) ⟨2284505, by rfl⟩ : syracuseStep 3046007 = 4569011) B4569011
theorem B2030671 : Blo 2029435 2030671 := bstep (se 1 (by rfl) ⟨1523003, by rfl⟩ : syracuseStep 2030671 = 3046007) B3046007
theorem B3046013 : Blo 2029435 3046013 := bbase (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) (by norm_num)
theorem B2030675 : Blo 2029435 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B4569029 : Blo 2029435 4569029 := bbase (se 4 (by rfl) ⟨428346, by rfl⟩ : syracuseStep 4569029 = 856693) (by norm_num)
theorem B3046019 : Blo 2029435 3046019 := bstep (se 1 (by rfl) ⟨2284514, by rfl⟩ : syracuseStep 3046019 = 4569029) B4569029
theorem B2030679 : Blo 2029435 2030679 := bstep (se 1 (by rfl) ⟨1523009, by rfl⟩ : syracuseStep 2030679 = 3046019) B3046019
theorem B8674037 : Blo 2029435 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B5782691 : Blo 2029435 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B3855127 : Blo 2029435 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B5140169 : Blo 2029435 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B3426779 : Blo 2029435 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B2284519 : Blo 2029435 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B3046025 : Blo 2029435 3046025 := bstep (se 2 (by rfl) ⟨1142259, by rfl⟩ : syracuseStep 3046025 = 2284519) B2284519
theorem B2030683 : Blo 2029435 2030683 := bstep (se 1 (by rfl) ⟨1523012, by rfl⟩ : syracuseStep 2030683 = 3046025) B3046025
theorem B10280357 : Blo 2029435 10280357 := bbase (se 4 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 10280357 = 1927567) (by norm_num)
theorem B6853571 : Blo 2029435 6853571 := bstep (se 1 (by rfl) ⟨5140178, by rfl⟩ : syracuseStep 6853571 = 10280357) B10280357
theorem B4569047 : Blo 2029435 4569047 := bstep (se 1 (by rfl) ⟨3426785, by rfl⟩ : syracuseStep 4569047 = 6853571) B6853571
theorem B3046031 : Blo 2029435 3046031 := bstep (se 1 (by rfl) ⟨2284523, by rfl⟩ : syracuseStep 3046031 = 4569047) B4569047
theorem B2030687 : Blo 2029435 2030687 := bstep (se 1 (by rfl) ⟨1523015, by rfl⟩ : syracuseStep 2030687 = 3046031) B3046031
theorem B3046037 : Blo 2029435 3046037 := bbase (se 6 (by rfl) ⟨71391, by rfl⟩ : syracuseStep 3046037 = 142783) (by norm_num)
theorem B2030691 : Blo 2029435 2030691 := bstep (se 1 (by rfl) ⟨1523018, by rfl⟩ : syracuseStep 2030691 = 3046037) B3046037
theorem B2605165 : Blo 2029435 2605165 := bbase (se 3 (by rfl) ⟨488468, by rfl⟩ : syracuseStep 2605165 = 976937) (by norm_num)
theorem B13894213 : Blo 2029435 13894213 := bstep (se 4 (by rfl) ⟨1302582, by rfl⟩ : syracuseStep 13894213 = 2605165) B2605165
theorem B18525617 : Blo 2029435 18525617 := bstep (se 2 (by rfl) ⟨6947106, by rfl⟩ : syracuseStep 18525617 = 13894213) B13894213
theorem B12350411 : Blo 2029435 12350411 := bstep (se 1 (by rfl) ⟨9262808, by rfl⟩ : syracuseStep 12350411 = 18525617) B18525617
theorem B8233607 : Blo 2029435 8233607 := bstep (se 1 (by rfl) ⟨6175205, by rfl⟩ : syracuseStep 8233607 = 12350411) B12350411
theorem B21956285 : Blo 2029435 21956285 := bstep (se 3 (by rfl) ⟨4116803, by rfl⟩ : syracuseStep 21956285 = 8233607) B8233607
theorem B14637523 : Blo 2029435 14637523 := bstep (se 1 (by rfl) ⟨10978142, by rfl⟩ : syracuseStep 14637523 = 21956285) B21956285
theorem B19516697 : Blo 2029435 19516697 := bstep (se 2 (by rfl) ⟨7318761, by rfl⟩ : syracuseStep 19516697 = 14637523) B14637523
theorem B13011131 : Blo 2029435 13011131 := bstep (se 1 (by rfl) ⟨9758348, by rfl⟩ : syracuseStep 13011131 = 19516697) B19516697
theorem B8674087 : Blo 2029435 8674087 := bstep (se 1 (by rfl) ⟨6505565, by rfl⟩ : syracuseStep 8674087 = 13011131) B13011131
theorem B11565449 : Blo 2029435 11565449 := bstep (se 2 (by rfl) ⟨4337043, by rfl⟩ : syracuseStep 11565449 = 8674087) B8674087
theorem B7710299 : Blo 2029435 7710299 := bstep (se 1 (by rfl) ⟨5782724, by rfl⟩ : syracuseStep 7710299 = 11565449) B11565449
theorem B5140199 : Blo 2029435 5140199 := bstep (se 1 (by rfl) ⟨3855149, by rfl⟩ : syracuseStep 5140199 = 7710299) B7710299
theorem B3426799 : Blo 2029435 3426799 := bstep (se 1 (by rfl) ⟨2570099, by rfl⟩ : syracuseStep 3426799 = 5140199) B5140199
theorem B4569065 : Blo 2029435 4569065 := bstep (se 2 (by rfl) ⟨1713399, by rfl⟩ : syracuseStep 4569065 = 3426799) B3426799
theorem B3046043 : Blo 2029435 3046043 := bstep (se 1 (by rfl) ⟨2284532, by rfl⟩ : syracuseStep 3046043 = 4569065) B4569065
theorem B2030695 : Blo 2029435 2030695 := bstep (se 1 (by rfl) ⟨1523021, by rfl⟩ : syracuseStep 2030695 = 3046043) B3046043
theorem B2284537 : Blo 2029435 2284537 := bbase (se 2 (by rfl) ⟨856701, by rfl⟩ : syracuseStep 2284537 = 1713403) (by norm_num)
theorem B3046049 : Blo 2029435 3046049 := bstep (se 2 (by rfl) ⟨1142268, by rfl⟩ : syracuseStep 3046049 = 2284537) B2284537
theorem B2030699 : Blo 2029435 2030699 := bstep (se 1 (by rfl) ⟨1523024, by rfl⟩ : syracuseStep 2030699 = 3046049) B3046049
theorem B5489093 : Blo 2029435 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B14637581 : Blo 2029435 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B9758387 : Blo 2029435 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B6505591 : Blo 2029435 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B8674121 : Blo 2029435 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B5782747 : Blo 2029435 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B7710329 : Blo 2029435 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B5140219 : Blo 2029435 5140219 := bstep (se 1 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 5140219 = 7710329) B7710329
theorem B6853625 : Blo 2029435 6853625 := bstep (se 2 (by rfl) ⟨2570109, by rfl⟩ : syracuseStep 6853625 = 5140219) B5140219
theorem B4569083 : Blo 2029435 4569083 := bstep (se 1 (by rfl) ⟨3426812, by rfl⟩ : syracuseStep 4569083 = 6853625) B6853625
theorem B3046055 : Blo 2029435 3046055 := bstep (se 1 (by rfl) ⟨2284541, by rfl⟩ : syracuseStep 3046055 = 4569083) B4569083
theorem B2030703 : Blo 2029435 2030703 := bstep (se 1 (by rfl) ⟨1523027, by rfl⟩ : syracuseStep 2030703 = 3046055) B3046055
theorem B3046061 : Blo 2029435 3046061 := bbase (se 3 (by rfl) ⟨571136, by rfl⟩ : syracuseStep 3046061 = 1142273) (by norm_num)
theorem B2030707 : Blo 2029435 2030707 := bstep (se 1 (by rfl) ⟨1523030, by rfl⟩ : syracuseStep 2030707 = 3046061) B3046061
theorem B4569101 : Blo 2029435 4569101 := bbase (se 3 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 4569101 = 1713413) (by norm_num)
theorem B3046067 : Blo 2029435 3046067 := bstep (se 1 (by rfl) ⟨2284550, by rfl⟩ : syracuseStep 3046067 = 4569101) B4569101
theorem B2030711 : Blo 2029435 2030711 := bstep (se 1 (by rfl) ⟨1523033, by rfl⟩ : syracuseStep 2030711 = 3046067) B3046067
theorem B2570125 : Blo 2029435 2570125 := bbase (se 3 (by rfl) ⟨481898, by rfl⟩ : syracuseStep 2570125 = 963797) (by norm_num)
theorem B3426833 : Blo 2029435 3426833 := bstep (se 2 (by rfl) ⟨1285062, by rfl⟩ : syracuseStep 3426833 = 2570125) B2570125
theorem B2284555 : Blo 2029435 2284555 := bstep (se 1 (by rfl) ⟨1713416, by rfl⟩ : syracuseStep 2284555 = 3426833) B3426833
theorem B3046073 : Blo 2029435 3046073 := bstep (se 2 (by rfl) ⟨1142277, by rfl⟩ : syracuseStep 3046073 = 2284555) B2284555
theorem B2030715 : Blo 2029435 2030715 := bstep (se 1 (by rfl) ⟨1523036, by rfl⟩ : syracuseStep 2030715 = 3046073) B3046073
theorem B3961109 : Blo 2029435 3961109 := bbase (se 6 (by rfl) ⟨92838, by rfl⟩ : syracuseStep 3961109 = 185677) (by norm_num)
theorem B2640739 : Blo 2029435 2640739 := bstep (se 1 (by rfl) ⟨1980554, by rfl⟩ : syracuseStep 2640739 = 3961109) B3961109
theorem B56335765 : Blo 2029435 56335765 := bstep (se 6 (by rfl) ⟨1320369, by rfl⟩ : syracuseStep 56335765 = 2640739) B2640739
theorem B75114353 : Blo 2029435 75114353 := bstep (se 2 (by rfl) ⟨28167882, by rfl⟩ : syracuseStep 75114353 = 56335765) B56335765
theorem B50076235 : Blo 2029435 50076235 := bstep (se 1 (by rfl) ⟨37557176, by rfl⟩ : syracuseStep 50076235 = 75114353) B75114353
theorem B66768313 : Blo 2029435 66768313 := bstep (se 2 (by rfl) ⟨25038117, by rfl⟩ : syracuseStep 66768313 = 50076235) B50076235
theorem B89024417 : Blo 2029435 89024417 := bstep (se 2 (by rfl) ⟨33384156, by rfl⟩ : syracuseStep 89024417 = 66768313) B66768313
theorem B59349611 : Blo 2029435 59349611 := bstep (se 1 (by rfl) ⟨44512208, by rfl⟩ : syracuseStep 59349611 = 89024417) B89024417
theorem B39566407 : Blo 2029435 39566407 := bstep (se 1 (by rfl) ⟨29674805, by rfl⟩ : syracuseStep 39566407 = 59349611) B59349611
theorem B52755209 : Blo 2029435 52755209 := bstep (se 2 (by rfl) ⟨19783203, by rfl⟩ : syracuseStep 52755209 = 39566407) B39566407
theorem B35170139 : Blo 2029435 35170139 := bstep (se 1 (by rfl) ⟨26377604, by rfl⟩ : syracuseStep 35170139 = 52755209) B52755209
theorem B23446759 : Blo 2029435 23446759 := bstep (se 1 (by rfl) ⟨17585069, by rfl⟩ : syracuseStep 23446759 = 35170139) B35170139
theorem B31262345 : Blo 2029435 31262345 := bstep (se 2 (by rfl) ⟨11723379, by rfl⟩ : syracuseStep 31262345 = 23446759) B23446759
theorem B20841563 : Blo 2029435 20841563 := bstep (se 1 (by rfl) ⟨15631172, by rfl⟩ : syracuseStep 20841563 = 31262345) B31262345
theorem B55577501 : Blo 2029435 55577501 := bstep (se 3 (by rfl) ⟨10420781, by rfl⟩ : syracuseStep 55577501 = 20841563) B20841563
theorem B37051667 : Blo 2029435 37051667 := bstep (se 1 (by rfl) ⟨27788750, by rfl⟩ : syracuseStep 37051667 = 55577501) B55577501
theorem B24701111 : Blo 2029435 24701111 := bstep (se 1 (by rfl) ⟨18525833, by rfl⟩ : syracuseStep 24701111 = 37051667) B37051667
theorem B16467407 : Blo 2029435 16467407 := bstep (se 1 (by rfl) ⟨12350555, by rfl⟩ : syracuseStep 16467407 = 24701111) B24701111
theorem B10978271 : Blo 2029435 10978271 := bstep (se 1 (by rfl) ⟨8233703, by rfl⟩ : syracuseStep 10978271 = 16467407) B16467407
theorem B7318847 : Blo 2029435 7318847 := bstep (se 1 (by rfl) ⟨5489135, by rfl⟩ : syracuseStep 7318847 = 10978271) B10978271
theorem B19516925 : Blo 2029435 19516925 := bstep (se 3 (by rfl) ⟨3659423, by rfl⟩ : syracuseStep 19516925 = 7318847) B7318847
theorem B13011283 : Blo 2029435 13011283 := bstep (se 1 (by rfl) ⟨9758462, by rfl⟩ : syracuseStep 13011283 = 19516925) B19516925
theorem B17348377 : Blo 2029435 17348377 := bstep (se 2 (by rfl) ⟨6505641, by rfl⟩ : syracuseStep 17348377 = 13011283) B13011283
theorem B23131169 : Blo 2029435 23131169 := bstep (se 2 (by rfl) ⟨8674188, by rfl⟩ : syracuseStep 23131169 = 17348377) B17348377
theorem B15420779 : Blo 2029435 15420779 := bstep (se 1 (by rfl) ⟨11565584, by rfl⟩ : syracuseStep 15420779 = 23131169) B23131169
theorem B10280519 : Blo 2029435 10280519 := bstep (se 1 (by rfl) ⟨7710389, by rfl⟩ : syracuseStep 10280519 = 15420779) B15420779
theorem B6853679 : Blo 2029435 6853679 := bstep (se 1 (by rfl) ⟨5140259, by rfl⟩ : syracuseStep 6853679 = 10280519) B10280519
theorem B4569119 : Blo 2029435 4569119 := bstep (se 1 (by rfl) ⟨3426839, by rfl⟩ : syracuseStep 4569119 = 6853679) B6853679
theorem B3046079 : Blo 2029435 3046079 := bstep (se 1 (by rfl) ⟨2284559, by rfl⟩ : syracuseStep 3046079 = 4569119) B4569119
theorem B2030719 : Blo 2029435 2030719 := bstep (se 1 (by rfl) ⟨1523039, by rfl⟩ : syracuseStep 2030719 = 3046079) B3046079
theorem B3046085 : Blo 2029435 3046085 := bbase (se 4 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 3046085 = 571141) (by norm_num)
theorem B2030723 : Blo 2029435 2030723 := bstep (se 1 (by rfl) ⟨1523042, by rfl⟩ : syracuseStep 2030723 = 3046085) B3046085
theorem B3426853 : Blo 2029435 3426853 := bbase (se 4 (by rfl) ⟨321267, by rfl⟩ : syracuseStep 3426853 = 642535) (by norm_num)
theorem B4569137 : Blo 2029435 4569137 := bstep (se 2 (by rfl) ⟨1713426, by rfl⟩ : syracuseStep 4569137 = 3426853) B3426853
theorem B3046091 : Blo 2029435 3046091 := bstep (se 1 (by rfl) ⟨2284568, by rfl⟩ : syracuseStep 3046091 = 4569137) B4569137
theorem B2030727 : Blo 2029435 2030727 := bstep (se 1 (by rfl) ⟨1523045, by rfl⟩ : syracuseStep 2030727 = 3046091) B3046091
theorem B2284573 : Blo 2029435 2284573 := bbase (se 3 (by rfl) ⟨428357, by rfl⟩ : syracuseStep 2284573 = 856715) (by norm_num)
theorem B3046097 : Blo 2029435 3046097 := bstep (se 2 (by rfl) ⟨1142286, by rfl⟩ : syracuseStep 3046097 = 2284573) B2284573
theorem B2030731 : Blo 2029435 2030731 := bstep (se 1 (by rfl) ⟨1523048, by rfl⟩ : syracuseStep 2030731 = 3046097) B3046097
theorem B6853733 : Blo 2029435 6853733 := bbase (se 4 (by rfl) ⟨642537, by rfl⟩ : syracuseStep 6853733 = 1285075) (by norm_num)
theorem B4569155 : Blo 2029435 4569155 := bstep (se 1 (by rfl) ⟨3426866, by rfl⟩ : syracuseStep 4569155 = 6853733) B6853733
theorem B3046103 : Blo 2029435 3046103 := bstep (se 1 (by rfl) ⟨2284577, by rfl⟩ : syracuseStep 3046103 = 4569155) B4569155
theorem B2030735 : Blo 2029435 2030735 := bstep (se 1 (by rfl) ⟨1523051, by rfl⟩ : syracuseStep 2030735 = 3046103) B3046103
theorem B3046109 : Blo 2029435 3046109 := bbase (se 3 (by rfl) ⟨571145, by rfl⟩ : syracuseStep 3046109 = 1142291) (by norm_num)
theorem B2030739 : Blo 2029435 2030739 := bstep (se 1 (by rfl) ⟨1523054, by rfl⟩ : syracuseStep 2030739 = 3046109) B3046109
theorem B4569173 : Blo 2029435 4569173 := bbase (se 8 (by rfl) ⟨26772, by rfl⟩ : syracuseStep 4569173 = 53545) (by norm_num)
theorem B3046115 : Blo 2029435 3046115 := bstep (se 1 (by rfl) ⟨2284586, by rfl⟩ : syracuseStep 3046115 = 4569173) B4569173
theorem B2030743 : Blo 2029435 2030743 := bstep (se 1 (by rfl) ⟨1523057, by rfl⟩ : syracuseStep 2030743 = 3046115) B3046115
theorem B6505733 : Blo 2029435 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B4337155 : Blo 2029435 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B5782873 : Blo 2029435 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B7710497 : Blo 2029435 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B5140331 : Blo 2029435 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3426887 : Blo 2029435 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B2284591 : Blo 2029435 2284591 := bstep (se 1 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 2284591 = 3426887) B3426887
theorem B3046121 : Blo 2029435 3046121 := bstep (se 2 (by rfl) ⟨1142295, by rfl⟩ : syracuseStep 3046121 = 2284591) B2284591
theorem B2030747 : Blo 2029435 2030747 := bstep (se 1 (by rfl) ⟨1523060, by rfl⟩ : syracuseStep 2030747 = 3046121) B3046121
theorem B4116917 : Blo 2029435 4116917 := bbase (se 5 (by rfl) ⟨192980, by rfl⟩ : syracuseStep 4116917 = 385961) (by norm_num)
theorem B2744611 : Blo 2029435 2744611 := bstep (se 1 (by rfl) ⟨2058458, by rfl⟩ : syracuseStep 2744611 = 4116917) B4116917
theorem B14637925 : Blo 2029435 14637925 := bstep (se 4 (by rfl) ⟨1372305, by rfl⟩ : syracuseStep 14637925 = 2744611) B2744611
theorem B19517233 : Blo 2029435 19517233 := bstep (se 2 (by rfl) ⟨7318962, by rfl⟩ : syracuseStep 19517233 = 14637925) B14637925
theorem B26022977 : Blo 2029435 26022977 := bstep (se 2 (by rfl) ⟨9758616, by rfl⟩ : syracuseStep 26022977 = 19517233) B19517233
theorem B17348651 : Blo 2029435 17348651 := bstep (se 1 (by rfl) ⟨13011488, by rfl⟩ : syracuseStep 17348651 = 26022977) B26022977
theorem B11565767 : Blo 2029435 11565767 := bstep (se 1 (by rfl) ⟨8674325, by rfl⟩ : syracuseStep 11565767 = 17348651) B17348651
theorem B7710511 : Blo 2029435 7710511 := bstep (se 1 (by rfl) ⟨5782883, by rfl⟩ : syracuseStep 7710511 = 11565767) B11565767
theorem B10280681 : Blo 2029435 10280681 := bstep (se 2 (by rfl) ⟨3855255, by rfl⟩ : syracuseStep 10280681 = 7710511) B7710511
theorem B6853787 : Blo 2029435 6853787 := bstep (se 1 (by rfl) ⟨5140340, by rfl⟩ : syracuseStep 6853787 = 10280681) B10280681
theorem B4569191 : Blo 2029435 4569191 := bstep (se 1 (by rfl) ⟨3426893, by rfl⟩ : syracuseStep 4569191 = 6853787) B6853787
theorem B3046127 : Blo 2029435 3046127 := bstep (se 1 (by rfl) ⟨2284595, by rfl⟩ : syracuseStep 3046127 = 4569191) B4569191
theorem B2030751 : Blo 2029435 2030751 := bstep (se 1 (by rfl) ⟨1523063, by rfl⟩ : syracuseStep 2030751 = 3046127) B3046127
theorem B3046133 : Blo 2029435 3046133 := bbase (se 5 (by rfl) ⟨142787, by rfl⟩ : syracuseStep 3046133 = 285575) (by norm_num)
theorem B2030755 : Blo 2029435 2030755 := bstep (se 1 (by rfl) ⟨1523066, by rfl⟩ : syracuseStep 2030755 = 3046133) B3046133
theorem B3087701 : Blo 2029435 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B2058467 : Blo 2029435 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B5489245 : Blo 2029435 5489245 := bstep (se 3 (by rfl) ⟨1029233, by rfl⟩ : syracuseStep 5489245 = 2058467) B2058467
theorem B7318993 : Blo 2029435 7318993 := bstep (se 2 (by rfl) ⟨2744622, by rfl⟩ : syracuseStep 7318993 = 5489245) B5489245
theorem B9758657 : Blo 2029435 9758657 := bstep (se 2 (by rfl) ⟨3659496, by rfl⟩ : syracuseStep 9758657 = 7318993) B7318993
theorem B6505771 : Blo 2029435 6505771 := bstep (se 1 (by rfl) ⟨4879328, by rfl⟩ : syracuseStep 6505771 = 9758657) B9758657
theorem B8674361 : Blo 2029435 8674361 := bstep (se 2 (by rfl) ⟨3252885, by rfl⟩ : syracuseStep 8674361 = 6505771) B6505771
theorem B5782907 : Blo 2029435 5782907 := bstep (se 1 (by rfl) ⟨4337180, by rfl⟩ : syracuseStep 5782907 = 8674361) B8674361
theorem B3855271 : Blo 2029435 3855271 := bstep (se 1 (by rfl) ⟨2891453, by rfl⟩ : syracuseStep 3855271 = 5782907) B5782907
theorem B5140361 : Blo 2029435 5140361 := bstep (se 2 (by rfl) ⟨1927635, by rfl⟩ : syracuseStep 5140361 = 3855271) B3855271
theorem B3426907 : Blo 2029435 3426907 := bstep (se 1 (by rfl) ⟨2570180, by rfl⟩ : syracuseStep 3426907 = 5140361) B5140361
theorem B4569209 : Blo 2029435 4569209 := bstep (se 2 (by rfl) ⟨1713453, by rfl⟩ : syracuseStep 4569209 = 3426907) B3426907
theorem B3046139 : Blo 2029435 3046139 := bstep (se 1 (by rfl) ⟨2284604, by rfl⟩ : syracuseStep 3046139 = 4569209) B4569209
theorem B2030759 : Blo 2029435 2030759 := bstep (se 1 (by rfl) ⟨1523069, by rfl⟩ : syracuseStep 2030759 = 3046139) B3046139
theorem B2284609 : Blo 2029435 2284609 := bbase (se 2 (by rfl) ⟨856728, by rfl⟩ : syracuseStep 2284609 = 1713457) (by norm_num)
theorem B3046145 : Blo 2029435 3046145 := bstep (se 2 (by rfl) ⟨1142304, by rfl⟩ : syracuseStep 3046145 = 2284609) B2284609
theorem B2030763 : Blo 2029435 2030763 := bstep (se 1 (by rfl) ⟨1523072, by rfl⟩ : syracuseStep 2030763 = 3046145) B3046145
theorem B5140381 : Blo 2029435 5140381 := bbase (se 3 (by rfl) ⟨963821, by rfl⟩ : syracuseStep 5140381 = 1927643) (by norm_num)
theorem B6853841 : Blo 2029435 6853841 := bstep (se 2 (by rfl) ⟨2570190, by rfl⟩ : syracuseStep 6853841 = 5140381) B5140381
theorem B4569227 : Blo 2029435 4569227 := bstep (se 1 (by rfl) ⟨3426920, by rfl⟩ : syracuseStep 4569227 = 6853841) B6853841
theorem B3046151 : Blo 2029435 3046151 := bstep (se 1 (by rfl) ⟨2284613, by rfl⟩ : syracuseStep 3046151 = 4569227) B4569227
theorem B2030767 : Blo 2029435 2030767 := bstep (se 1 (by rfl) ⟨1523075, by rfl⟩ : syracuseStep 2030767 = 3046151) B3046151
theorem B3046157 : Blo 2029435 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B2030771 : Blo 2029435 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B4569245 : Blo 2029435 4569245 := bbase (se 3 (by rfl) ⟨856733, by rfl⟩ : syracuseStep 4569245 = 1713467) (by norm_num)
theorem B3046163 : Blo 2029435 3046163 := bstep (se 1 (by rfl) ⟨2284622, by rfl⟩ : syracuseStep 3046163 = 4569245) B4569245
theorem B2030775 : Blo 2029435 2030775 := bstep (se 1 (by rfl) ⟨1523081, by rfl⟩ : syracuseStep 2030775 = 3046163) B3046163
theorem B3426941 : Blo 2029435 3426941 := bbase (se 3 (by rfl) ⟨642551, by rfl⟩ : syracuseStep 3426941 = 1285103) (by norm_num)
theorem B2284627 : Blo 2029435 2284627 := bstep (se 1 (by rfl) ⟨1713470, by rfl⟩ : syracuseStep 2284627 = 3426941) B3426941
theorem B3046169 : Blo 2029435 3046169 := bstep (se 2 (by rfl) ⟨1142313, by rfl⟩ : syracuseStep 3046169 = 2284627) B2284627
theorem B2030779 : Blo 2029435 2030779 := bstep (se 1 (by rfl) ⟨1523084, by rfl⟩ : syracuseStep 2030779 = 3046169) B3046169
theorem B10563301 : Blo 2029435 10563301 := bbase (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) (by norm_num)
theorem B14084401 : Blo 2029435 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B18779201 : Blo 2029435 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B12519467 : Blo 2029435 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B8346311 : Blo 2029435 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B5564207 : Blo 2029435 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B3709471 : Blo 2029435 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B4945961 : Blo 2029435 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B13189229 : Blo 2029435 13189229 := bstep (se 3 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 13189229 = 4945961) B4945961
theorem B8792819 : Blo 2029435 8792819 := bstep (se 1 (by rfl) ⟨6594614, by rfl⟩ : syracuseStep 8792819 = 13189229) B13189229
theorem B5861879 : Blo 2029435 5861879 := bstep (se 1 (by rfl) ⟨4396409, by rfl⟩ : syracuseStep 5861879 = 8792819) B8792819
theorem B3907919 : Blo 2029435 3907919 := bstep (se 1 (by rfl) ⟨2930939, by rfl⟩ : syracuseStep 3907919 = 5861879) B5861879
theorem B2605279 : Blo 2029435 2605279 := bstep (se 1 (by rfl) ⟨1953959, by rfl⟩ : syracuseStep 2605279 = 3907919) B3907919
theorem B3473705 : Blo 2029435 3473705 := bstep (se 2 (by rfl) ⟨1302639, by rfl⟩ : syracuseStep 3473705 = 2605279) B2605279
theorem B2315803 : Blo 2029435 2315803 := bstep (se 1 (by rfl) ⟨1736852, by rfl⟩ : syracuseStep 2315803 = 3473705) B3473705
theorem B3087737 : Blo 2029435 3087737 := bstep (se 2 (by rfl) ⟨1157901, by rfl⟩ : syracuseStep 3087737 = 2315803) B2315803
theorem B2058491 : Blo 2029435 2058491 := bstep (se 1 (by rfl) ⟨1543868, by rfl⟩ : syracuseStep 2058491 = 3087737) B3087737
theorem B5489309 : Blo 2029435 5489309 := bstep (se 3 (by rfl) ⟨1029245, by rfl⟩ : syracuseStep 5489309 = 2058491) B2058491
theorem B14638157 : Blo 2029435 14638157 := bstep (se 3 (by rfl) ⟨2744654, by rfl⟩ : syracuseStep 14638157 = 5489309) B5489309
theorem B9758771 : Blo 2029435 9758771 := bstep (se 1 (by rfl) ⟨7319078, by rfl⟩ : syracuseStep 9758771 = 14638157) B14638157
theorem B6505847 : Blo 2029435 6505847 := bstep (se 1 (by rfl) ⟨4879385, by rfl⟩ : syracuseStep 6505847 = 9758771) B9758771
theorem B4337231 : Blo 2029435 4337231 := bstep (se 1 (by rfl) ⟨3252923, by rfl⟩ : syracuseStep 4337231 = 6505847) B6505847
theorem B11565949 : Blo 2029435 11565949 := bstep (se 3 (by rfl) ⟨2168615, by rfl⟩ : syracuseStep 11565949 = 4337231) B4337231
theorem B15421265 : Blo 2029435 15421265 := bstep (se 2 (by rfl) ⟨5782974, by rfl⟩ : syracuseStep 15421265 = 11565949) B11565949
theorem B10280843 : Blo 2029435 10280843 := bstep (se 1 (by rfl) ⟨7710632, by rfl⟩ : syracuseStep 10280843 = 15421265) B15421265
theorem B6853895 : Blo 2029435 6853895 := bstep (se 1 (by rfl) ⟨5140421, by rfl⟩ : syracuseStep 6853895 = 10280843) B10280843
theorem B4569263 : Blo 2029435 4569263 := bstep (se 1 (by rfl) ⟨3426947, by rfl⟩ : syracuseStep 4569263 = 6853895) B6853895
theorem B3046175 : Blo 2029435 3046175 := bstep (se 1 (by rfl) ⟨2284631, by rfl⟩ : syracuseStep 3046175 = 4569263) B4569263
theorem B2030783 : Blo 2029435 2030783 := bstep (se 1 (by rfl) ⟨1523087, by rfl⟩ : syracuseStep 2030783 = 3046175) B3046175
theorem B3046181 : Blo 2029435 3046181 := bbase (se 4 (by rfl) ⟨285579, by rfl⟩ : syracuseStep 3046181 = 571159) (by norm_num)
theorem B2030787 : Blo 2029435 2030787 := bstep (se 1 (by rfl) ⟨1523090, by rfl⟩ : syracuseStep 2030787 = 3046181) B3046181
theorem B2570221 : Blo 2029435 2570221 := bbase (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) (by norm_num)
theorem B3426961 : Blo 2029435 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B4569281 : Blo 2029435 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B3046187 : Blo 2029435 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B2030791 : Blo 2029435 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B2284645 : Blo 2029435 2284645 := bbase (se 4 (by rfl) ⟨214185, by rfl⟩ : syracuseStep 2284645 = 428371) (by norm_num)
theorem B3046193 : Blo 2029435 3046193 := bstep (se 2 (by rfl) ⟨1142322, by rfl⟩ : syracuseStep 3046193 = 2284645) B2284645
theorem B2030795 : Blo 2029435 2030795 := bstep (se 1 (by rfl) ⟨1523096, by rfl⟩ : syracuseStep 2030795 = 3046193) B3046193
theorem B2168633 : Blo 2029435 2168633 := bbase (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) (by norm_num)
theorem B5783021 : Blo 2029435 5783021 := bstep (se 3 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 5783021 = 2168633) B2168633
theorem B3855347 : Blo 2029435 3855347 := bstep (se 1 (by rfl) ⟨2891510, by rfl⟩ : syracuseStep 3855347 = 5783021) B5783021
theorem B2570231 : Blo 2029435 2570231 := bstep (se 1 (by rfl) ⟨1927673, by rfl⟩ : syracuseStep 2570231 = 3855347) B3855347
theorem B6853949 : Blo 2029435 6853949 := bstep (se 3 (by rfl) ⟨1285115, by rfl⟩ : syracuseStep 6853949 = 2570231) B2570231
theorem B4569299 : Blo 2029435 4569299 := bstep (se 1 (by rfl) ⟨3426974, by rfl⟩ : syracuseStep 4569299 = 6853949) B6853949
theorem B3046199 : Blo 2029435 3046199 := bstep (se 1 (by rfl) ⟨2284649, by rfl⟩ : syracuseStep 3046199 = 4569299) B4569299
theorem B2030799 : Blo 2029435 2030799 := bstep (se 1 (by rfl) ⟨1523099, by rfl⟩ : syracuseStep 2030799 = 3046199) B3046199
theorem B3046205 : Blo 2029435 3046205 := bbase (se 3 (by rfl) ⟨571163, by rfl⟩ : syracuseStep 3046205 = 1142327) (by norm_num)
theorem B2030803 : Blo 2029435 2030803 := bstep (se 1 (by rfl) ⟨1523102, by rfl⟩ : syracuseStep 2030803 = 3046205) B3046205
theorem B4569317 : Blo 2029435 4569317 := bbase (se 4 (by rfl) ⟨428373, by rfl⟩ : syracuseStep 4569317 = 856747) (by norm_num)
theorem B3046211 : Blo 2029435 3046211 := bstep (se 1 (by rfl) ⟨2284658, by rfl⟩ : syracuseStep 3046211 = 4569317) B4569317
theorem B2030807 : Blo 2029435 2030807 := bstep (se 1 (by rfl) ⟨1523105, by rfl⟩ : syracuseStep 2030807 = 3046211) B3046211
theorem B5140493 : Blo 2029435 5140493 := bbase (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) (by norm_num)
theorem B3426995 : Blo 2029435 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B2284663 : Blo 2029435 2284663 := bstep (se 1 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 2284663 = 3426995) B3426995
theorem B3046217 : Blo 2029435 3046217 := bstep (se 2 (by rfl) ⟨1142331, by rfl⟩ : syracuseStep 3046217 = 2284663) B2284663
theorem B2030811 : Blo 2029435 2030811 := bstep (se 1 (by rfl) ⟨1523108, by rfl⟩ : syracuseStep 2030811 = 3046217) B3046217
theorem B2891533 : Blo 2029435 2891533 := bbase (se 3 (by rfl) ⟨542162, by rfl⟩ : syracuseStep 2891533 = 1084325) (by norm_num)
theorem B3855377 : Blo 2029435 3855377 := bstep (se 2 (by rfl) ⟨1445766, by rfl⟩ : syracuseStep 3855377 = 2891533) B2891533
theorem B10281005 : Blo 2029435 10281005 := bstep (se 3 (by rfl) ⟨1927688, by rfl⟩ : syracuseStep 10281005 = 3855377) B3855377
theorem B6854003 : Blo 2029435 6854003 := bstep (se 1 (by rfl) ⟨5140502, by rfl⟩ : syracuseStep 6854003 = 10281005) B10281005
theorem B4569335 : Blo 2029435 4569335 := bstep (se 1 (by rfl) ⟨3427001, by rfl⟩ : syracuseStep 4569335 = 6854003) B6854003
theorem B3046223 : Blo 2029435 3046223 := bstep (se 1 (by rfl) ⟨2284667, by rfl⟩ : syracuseStep 3046223 = 4569335) B4569335
theorem B2030815 : Blo 2029435 2030815 := bstep (se 1 (by rfl) ⟨1523111, by rfl⟩ : syracuseStep 2030815 = 3046223) B3046223
theorem B3046229 : Blo 2029435 3046229 := bbase (se 9 (by rfl) ⟨8924, by rfl⟩ : syracuseStep 3046229 = 17849) (by norm_num)
theorem B2030819 : Blo 2029435 2030819 := bstep (se 1 (by rfl) ⟨1523114, by rfl⟩ : syracuseStep 2030819 = 3046229) B3046229
theorem B4337317 : Blo 2029435 4337317 := bbase (se 4 (by rfl) ⟨406623, by rfl⟩ : syracuseStep 4337317 = 813247) (by norm_num)
theorem B5783089 : Blo 2029435 5783089 := bstep (se 2 (by rfl) ⟨2168658, by rfl⟩ : syracuseStep 5783089 = 4337317) B4337317
theorem B7710785 : Blo 2029435 7710785 := bstep (se 2 (by rfl) ⟨2891544, by rfl⟩ : syracuseStep 7710785 = 5783089) B5783089
theorem B5140523 : Blo 2029435 5140523 := bstep (se 1 (by rfl) ⟨3855392, by rfl⟩ : syracuseStep 5140523 = 7710785) B7710785
theorem B3427015 : Blo 2029435 3427015 := bstep (se 1 (by rfl) ⟨2570261, by rfl⟩ : syracuseStep 3427015 = 5140523) B5140523
theorem B4569353 : Blo 2029435 4569353 := bstep (se 2 (by rfl) ⟨1713507, by rfl⟩ : syracuseStep 4569353 = 3427015) B3427015
theorem B3046235 : Blo 2029435 3046235 := bstep (se 1 (by rfl) ⟨2284676, by rfl⟩ : syracuseStep 3046235 = 4569353) B4569353
theorem B2030823 : Blo 2029435 2030823 := bstep (se 1 (by rfl) ⟨1523117, by rfl⟩ : syracuseStep 2030823 = 3046235) B3046235
theorem B2284681 : Blo 2029435 2284681 := bbase (se 2 (by rfl) ⟨856755, by rfl⟩ : syracuseStep 2284681 = 1713511) (by norm_num)
theorem B3046241 : Blo 2029435 3046241 := bstep (se 2 (by rfl) ⟨1142340, by rfl⟩ : syracuseStep 3046241 = 2284681) B2284681
theorem B2030827 : Blo 2029435 2030827 := bstep (se 1 (by rfl) ⟨1523120, by rfl⟩ : syracuseStep 2030827 = 3046241) B3046241
theorem B9263429 : Blo 2029435 9263429 := bbase (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) (by norm_num)
theorem B6175619 : Blo 2029435 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B4117079 : Blo 2029435 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B10978877 : Blo 2029435 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B7319251 : Blo 2029435 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B39036005 : Blo 2029435 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B26024003 : Blo 2029435 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B17349335 : Blo 2029435 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B11566223 : Blo 2029435 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B7710815 : Blo 2029435 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B5140543 : Blo 2029435 5140543 := bstep (se 1 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 5140543 = 7710815) B7710815
theorem B6854057 : Blo 2029435 6854057 := bstep (se 2 (by rfl) ⟨2570271, by rfl⟩ : syracuseStep 6854057 = 5140543) B5140543
theorem B4569371 : Blo 2029435 4569371 := bstep (se 1 (by rfl) ⟨3427028, by rfl⟩ : syracuseStep 4569371 = 6854057) B6854057
theorem B3046247 : Blo 2029435 3046247 := bstep (se 1 (by rfl) ⟨2284685, by rfl⟩ : syracuseStep 3046247 = 4569371) B4569371
theorem B2030831 : Blo 2029435 2030831 := bstep (se 1 (by rfl) ⟨1523123, by rfl⟩ : syracuseStep 2030831 = 3046247) B3046247
theorem B3046253 : Blo 2029435 3046253 := bbase (se 3 (by rfl) ⟨571172, by rfl⟩ : syracuseStep 3046253 = 1142345) (by norm_num)
theorem B2030835 : Blo 2029435 2030835 := bstep (se 1 (by rfl) ⟨1523126, by rfl⟩ : syracuseStep 2030835 = 3046253) B3046253
theorem B4569389 : Blo 2029435 4569389 := bbase (se 3 (by rfl) ⟨856760, by rfl⟩ : syracuseStep 4569389 = 1713521) (by norm_num)
theorem B3046259 : Blo 2029435 3046259 := bstep (se 1 (by rfl) ⟨2284694, by rfl⟩ : syracuseStep 3046259 = 4569389) B4569389
theorem B2030839 : Blo 2029435 2030839 := bstep (se 1 (by rfl) ⟨1523129, by rfl⟩ : syracuseStep 2030839 = 3046259) B3046259
theorem B3087829 : Blo 2029435 3087829 := bbase (se 7 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 3087829 = 72371) (by norm_num)
theorem B4117105 : Blo 2029435 4117105 := bstep (se 2 (by rfl) ⟨1543914, by rfl⟩ : syracuseStep 4117105 = 3087829) B3087829
theorem B5489473 : Blo 2029435 5489473 := bstep (se 2 (by rfl) ⟨2058552, by rfl⟩ : syracuseStep 5489473 = 4117105) B4117105
theorem B7319297 : Blo 2029435 7319297 := bstep (se 2 (by rfl) ⟨2744736, by rfl⟩ : syracuseStep 7319297 = 5489473) B5489473
theorem B4879531 : Blo 2029435 4879531 := bstep (se 1 (by rfl) ⟨3659648, by rfl⟩ : syracuseStep 4879531 = 7319297) B7319297
theorem B6506041 : Blo 2029435 6506041 := bstep (se 2 (by rfl) ⟨2439765, by rfl⟩ : syracuseStep 6506041 = 4879531) B4879531
theorem B8674721 : Blo 2029435 8674721 := bstep (se 2 (by rfl) ⟨3253020, by rfl⟩ : syracuseStep 8674721 = 6506041) B6506041
theorem B5783147 : Blo 2029435 5783147 := bstep (se 1 (by rfl) ⟨4337360, by rfl⟩ : syracuseStep 5783147 = 8674721) B8674721
theorem B3855431 : Blo 2029435 3855431 := bstep (se 1 (by rfl) ⟨2891573, by rfl⟩ : syracuseStep 3855431 = 5783147) B5783147
theorem B2570287 : Blo 2029435 2570287 := bstep (se 1 (by rfl) ⟨1927715, by rfl⟩ : syracuseStep 2570287 = 3855431) B3855431
theorem B3427049 : Blo 2029435 3427049 := bstep (se 2 (by rfl) ⟨1285143, by rfl⟩ : syracuseStep 3427049 = 2570287) B2570287
theorem B2284699 : Blo 2029435 2284699 := bstep (se 1 (by rfl) ⟨1713524, by rfl⟩ : syracuseStep 2284699 = 3427049) B3427049
theorem B3046265 : Blo 2029435 3046265 := bstep (se 2 (by rfl) ⟨1142349, by rfl⟩ : syracuseStep 3046265 = 2284699) B2284699
theorem B2030843 : Blo 2029435 2030843 := bstep (se 1 (by rfl) ⟨1523132, by rfl⟩ : syracuseStep 2030843 = 3046265) B3046265
theorem B3473813 : Blo 2029435 3473813 := bbase (se 6 (by rfl) ⟨81417, by rfl⟩ : syracuseStep 3473813 = 162835) (by norm_num)
theorem B9263501 : Blo 2029435 9263501 := bstep (se 3 (by rfl) ⟨1736906, by rfl⟩ : syracuseStep 9263501 = 3473813) B3473813
theorem B6175667 : Blo 2029435 6175667 := bstep (se 1 (by rfl) ⟨4631750, by rfl⟩ : syracuseStep 6175667 = 9263501) B9263501
theorem B4117111 : Blo 2029435 4117111 := bstep (se 1 (by rfl) ⟨3087833, by rfl⟩ : syracuseStep 4117111 = 6175667) B6175667
theorem B21957925 : Blo 2029435 21957925 := bstep (se 4 (by rfl) ⟨2058555, by rfl⟩ : syracuseStep 21957925 = 4117111) B4117111
theorem B29277233 : Blo 2029435 29277233 := bstep (se 2 (by rfl) ⟨10978962, by rfl⟩ : syracuseStep 29277233 = 21957925) B21957925
theorem B19518155 : Blo 2029435 19518155 := bstep (se 1 (by rfl) ⟨14638616, by rfl⟩ : syracuseStep 19518155 = 29277233) B29277233
theorem B13012103 : Blo 2029435 13012103 := bstep (se 1 (by rfl) ⟨9759077, by rfl⟩ : syracuseStep 13012103 = 19518155) B19518155
theorem B34698941 : Blo 2029435 34698941 := bstep (se 3 (by rfl) ⟨6506051, by rfl⟩ : syracuseStep 34698941 = 13012103) B13012103
theorem B23132627 : Blo 2029435 23132627 := bstep (se 1 (by rfl) ⟨17349470, by rfl⟩ : syracuseStep 23132627 = 34698941) B34698941
theorem B15421751 : Blo 2029435 15421751 := bstep (se 1 (by rfl) ⟨11566313, by rfl⟩ : syracuseStep 15421751 = 23132627) B23132627
theorem B10281167 : Blo 2029435 10281167 := bstep (se 1 (by rfl) ⟨7710875, by rfl⟩ : syracuseStep 10281167 = 15421751) B15421751
theorem B6854111 : Blo 2029435 6854111 := bstep (se 1 (by rfl) ⟨5140583, by rfl⟩ : syracuseStep 6854111 = 10281167) B10281167
theorem B4569407 : Blo 2029435 4569407 := bstep (se 1 (by rfl) ⟨3427055, by rfl⟩ : syracuseStep 4569407 = 6854111) B6854111
theorem B3046271 : Blo 2029435 3046271 := bstep (se 1 (by rfl) ⟨2284703, by rfl⟩ : syracuseStep 3046271 = 4569407) B4569407
theorem B2030847 : Blo 2029435 2030847 := bstep (se 1 (by rfl) ⟨1523135, by rfl⟩ : syracuseStep 2030847 = 3046271) B3046271
theorem B3046277 : Blo 2029435 3046277 := bbase (se 4 (by rfl) ⟨285588, by rfl⟩ : syracuseStep 3046277 = 571177) (by norm_num)
theorem B2030851 : Blo 2029435 2030851 := bstep (se 1 (by rfl) ⟨1523138, by rfl⟩ : syracuseStep 2030851 = 3046277) B3046277
theorem B3427069 : Blo 2029435 3427069 := bbase (se 3 (by rfl) ⟨642575, by rfl⟩ : syracuseStep 3427069 = 1285151) (by norm_num)
theorem B4569425 : Blo 2029435 4569425 := bstep (se 2 (by rfl) ⟨1713534, by rfl⟩ : syracuseStep 4569425 = 3427069) B3427069
theorem B3046283 : Blo 2029435 3046283 := bstep (se 1 (by rfl) ⟨2284712, by rfl⟩ : syracuseStep 3046283 = 4569425) B4569425
theorem B2030855 : Blo 2029435 2030855 := bstep (se 1 (by rfl) ⟨1523141, by rfl⟩ : syracuseStep 2030855 = 3046283) B3046283
theorem B2284717 : Blo 2029435 2284717 := bbase (se 3 (by rfl) ⟨428384, by rfl⟩ : syracuseStep 2284717 = 856769) (by norm_num)
theorem B3046289 : Blo 2029435 3046289 := bstep (se 2 (by rfl) ⟨1142358, by rfl⟩ : syracuseStep 3046289 = 2284717) B2284717
theorem B2030859 : Blo 2029435 2030859 := bstep (se 1 (by rfl) ⟨1523144, by rfl⟩ : syracuseStep 2030859 = 3046289) B3046289
theorem B6854165 : Blo 2029435 6854165 := bbase (se 6 (by rfl) ⟨160644, by rfl⟩ : syracuseStep 6854165 = 321289) (by norm_num)
theorem B4569443 : Blo 2029435 4569443 := bstep (se 1 (by rfl) ⟨3427082, by rfl⟩ : syracuseStep 4569443 = 6854165) B6854165
theorem B3046295 : Blo 2029435 3046295 := bstep (se 1 (by rfl) ⟨2284721, by rfl⟩ : syracuseStep 3046295 = 4569443) B4569443
theorem B2030863 : Blo 2029435 2030863 := bstep (se 1 (by rfl) ⟨1523147, by rfl⟩ : syracuseStep 2030863 = 3046295) B3046295
theorem B3046301 : Blo 2029435 3046301 := bbase (se 3 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 3046301 = 1142363) (by norm_num)
theorem B2030867 : Blo 2029435 2030867 := bstep (se 1 (by rfl) ⟨1523150, by rfl⟩ : syracuseStep 2030867 = 3046301) B3046301
theorem B4569461 : Blo 2029435 4569461 := bbase (se 5 (by rfl) ⟨214193, by rfl⟩ : syracuseStep 4569461 = 428387) (by norm_num)
theorem B3046307 : Blo 2029435 3046307 := bstep (se 1 (by rfl) ⟨2284730, by rfl⟩ : syracuseStep 3046307 = 4569461) B4569461
theorem B2030871 : Blo 2029435 2030871 := bstep (se 1 (by rfl) ⟨1523153, by rfl⟩ : syracuseStep 2030871 = 3046307) B3046307
theorem B3087877 : Blo 2029435 3087877 := bbase (se 4 (by rfl) ⟨289488, by rfl⟩ : syracuseStep 3087877 = 578977) (by norm_num)
theorem B4117169 : Blo 2029435 4117169 := bstep (se 2 (by rfl) ⟨1543938, by rfl⟩ : syracuseStep 4117169 = 3087877) B3087877
theorem B10979117 : Blo 2029435 10979117 := bstep (se 3 (by rfl) ⟨2058584, by rfl⟩ : syracuseStep 10979117 = 4117169) B4117169
theorem B7319411 : Blo 2029435 7319411 := bstep (se 1 (by rfl) ⟨5489558, by rfl⟩ : syracuseStep 7319411 = 10979117) B10979117
theorem B4879607 : Blo 2029435 4879607 := bstep (se 1 (by rfl) ⟨3659705, by rfl⟩ : syracuseStep 4879607 = 7319411) B7319411
theorem B13012285 : Blo 2029435 13012285 := bstep (se 3 (by rfl) ⟨2439803, by rfl⟩ : syracuseStep 13012285 = 4879607) B4879607
theorem B17349713 : Blo 2029435 17349713 := bstep (se 2 (by rfl) ⟨6506142, by rfl⟩ : syracuseStep 17349713 = 13012285) B13012285
theorem B11566475 : Blo 2029435 11566475 := bstep (se 1 (by rfl) ⟨8674856, by rfl⟩ : syracuseStep 11566475 = 17349713) B17349713
theorem B7710983 : Blo 2029435 7710983 := bstep (se 1 (by rfl) ⟨5783237, by rfl⟩ : syracuseStep 7710983 = 11566475) B11566475
theorem B5140655 : Blo 2029435 5140655 := bstep (se 1 (by rfl) ⟨3855491, by rfl⟩ : syracuseStep 5140655 = 7710983) B7710983
theorem B3427103 : Blo 2029435 3427103 := bstep (se 1 (by rfl) ⟨2570327, by rfl⟩ : syracuseStep 3427103 = 5140655) B5140655
theorem B2284735 : Blo 2029435 2284735 := bstep (se 1 (by rfl) ⟨1713551, by rfl⟩ : syracuseStep 2284735 = 3427103) B3427103
theorem B3046313 : Blo 2029435 3046313 := bstep (se 2 (by rfl) ⟨1142367, by rfl⟩ : syracuseStep 3046313 = 2284735) B2284735
theorem B2030875 : Blo 2029435 2030875 := bstep (se 1 (by rfl) ⟨1523156, by rfl⟩ : syracuseStep 2030875 = 3046313) B3046313
theorem B7710997 : Blo 2029435 7710997 := bbase (se 6 (by rfl) ⟨180726, by rfl⟩ : syracuseStep 7710997 = 361453) (by norm_num)
theorem B10281329 : Blo 2029435 10281329 := bstep (se 2 (by rfl) ⟨3855498, by rfl⟩ : syracuseStep 10281329 = 7710997) B7710997
theorem B6854219 : Blo 2029435 6854219 := bstep (se 1 (by rfl) ⟨5140664, by rfl⟩ : syracuseStep 6854219 = 10281329) B10281329
theorem B4569479 : Blo 2029435 4569479 := bstep (se 1 (by rfl) ⟨3427109, by rfl⟩ : syracuseStep 4569479 = 6854219) B6854219
theorem B3046319 : Blo 2029435 3046319 := bstep (se 1 (by rfl) ⟨2284739, by rfl⟩ : syracuseStep 3046319 = 4569479) B4569479
theorem B2030879 : Blo 2029435 2030879 := bstep (se 1 (by rfl) ⟨1523159, by rfl⟩ : syracuseStep 2030879 = 3046319) B3046319
theorem B3046325 : Blo 2029435 3046325 := bbase (se 5 (by rfl) ⟨142796, by rfl⟩ : syracuseStep 3046325 = 285593) (by norm_num)
theorem B2030883 : Blo 2029435 2030883 := bstep (se 1 (by rfl) ⟨1523162, by rfl⟩ : syracuseStep 2030883 = 3046325) B3046325
theorem B5140685 : Blo 2029435 5140685 := bbase (se 3 (by rfl) ⟨963878, by rfl⟩ : syracuseStep 5140685 = 1927757) (by norm_num)
theorem B3427123 : Blo 2029435 3427123 := bstep (se 1 (by rfl) ⟨2570342, by rfl⟩ : syracuseStep 3427123 = 5140685) B5140685
theorem B4569497 : Blo 2029435 4569497 := bstep (se 2 (by rfl) ⟨1713561, by rfl⟩ : syracuseStep 4569497 = 3427123) B3427123
theorem B3046331 : Blo 2029435 3046331 := bstep (se 1 (by rfl) ⟨2284748, by rfl⟩ : syracuseStep 3046331 = 4569497) B4569497
theorem B2030887 : Blo 2029435 2030887 := bstep (se 1 (by rfl) ⟨1523165, by rfl⟩ : syracuseStep 2030887 = 3046331) B3046331
theorem B2284753 : Blo 2029435 2284753 := bbase (se 2 (by rfl) ⟨856782, by rfl⟩ : syracuseStep 2284753 = 1713565) (by norm_num)
theorem B3046337 : Blo 2029435 3046337 := bstep (se 2 (by rfl) ⟨1142376, by rfl⟩ : syracuseStep 3046337 = 2284753) B2284753
theorem B2030891 : Blo 2029435 2030891 := bstep (se 1 (by rfl) ⟨1523168, by rfl⟩ : syracuseStep 2030891 = 3046337) B3046337
theorem B4631861 : Blo 2029435 4631861 := bbase (se 5 (by rfl) ⟨217118, by rfl⟩ : syracuseStep 4631861 = 434237) (by norm_num)
theorem B12351629 : Blo 2029435 12351629 := bstep (se 3 (by rfl) ⟨2315930, by rfl⟩ : syracuseStep 12351629 = 4631861) B4631861
theorem B32937677 : Blo 2029435 32937677 := bstep (se 3 (by rfl) ⟨6175814, by rfl⟩ : syracuseStep 32937677 = 12351629) B12351629
theorem B21958451 : Blo 2029435 21958451 := bstep (se 1 (by rfl) ⟨16468838, by rfl⟩ : syracuseStep 21958451 = 32937677) B32937677
theorem B14638967 : Blo 2029435 14638967 := bstep (se 1 (by rfl) ⟨10979225, by rfl⟩ : syracuseStep 14638967 = 21958451) B21958451
theorem B9759311 : Blo 2029435 9759311 := bstep (se 1 (by rfl) ⟨7319483, by rfl⟩ : syracuseStep 9759311 = 14638967) B14638967
theorem B6506207 : Blo 2029435 6506207 := bstep (se 1 (by rfl) ⟨4879655, by rfl⟩ : syracuseStep 6506207 = 9759311) B9759311
theorem B4337471 : Blo 2029435 4337471 := bstep (se 1 (by rfl) ⟨3253103, by rfl⟩ : syracuseStep 4337471 = 6506207) B6506207
theorem B2891647 : Blo 2029435 2891647 := bstep (se 1 (by rfl) ⟨2168735, by rfl⟩ : syracuseStep 2891647 = 4337471) B4337471
theorem B3855529 : Blo 2029435 3855529 := bstep (se 2 (by rfl) ⟨1445823, by rfl⟩ : syracuseStep 3855529 = 2891647) B2891647
theorem B5140705 : Blo 2029435 5140705 := bstep (se 2 (by rfl) ⟨1927764, by rfl⟩ : syracuseStep 5140705 = 3855529) B3855529
theorem B6854273 : Blo 2029435 6854273 := bstep (se 2 (by rfl) ⟨2570352, by rfl⟩ : syracuseStep 6854273 = 5140705) B5140705
theorem B4569515 : Blo 2029435 4569515 := bstep (se 1 (by rfl) ⟨3427136, by rfl⟩ : syracuseStep 4569515 = 6854273) B6854273
theorem B3046343 : Blo 2029435 3046343 := bstep (se 1 (by rfl) ⟨2284757, by rfl⟩ : syracuseStep 3046343 = 4569515) B4569515
theorem B2030895 : Blo 2029435 2030895 := bstep (se 1 (by rfl) ⟨1523171, by rfl⟩ : syracuseStep 2030895 = 3046343) B3046343
theorem B3046349 : Blo 2029435 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B2030899 : Blo 2029435 2030899 := bstep (se 1 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 2030899 = 3046349) B3046349
theorem B4569533 : Blo 2029435 4569533 := bbase (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) (by norm_num)
theorem B3046355 : Blo 2029435 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B2030903 : Blo 2029435 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B3427157 : Blo 2029435 3427157 := bbase (se 9 (by rfl) ⟨10040, by rfl⟩ : syracuseStep 3427157 = 20081) (by norm_num)
theorem B2284771 : Blo 2029435 2284771 := bstep (se 1 (by rfl) ⟨1713578, by rfl⟩ : syracuseStep 2284771 = 3427157) B3427157
theorem B3046361 : Blo 2029435 3046361 := bstep (se 2 (by rfl) ⟨1142385, by rfl⟩ : syracuseStep 3046361 = 2284771) B2284771
theorem B2030907 : Blo 2029435 2030907 := bstep (se 1 (by rfl) ⟨1523180, by rfl⟩ : syracuseStep 2030907 = 3046361) B3046361
theorem B4879693 : Blo 2029435 4879693 := bbase (se 3 (by rfl) ⟨914942, by rfl⟩ : syracuseStep 4879693 = 1829885) (by norm_num)
theorem B6506257 : Blo 2029435 6506257 := bstep (se 2 (by rfl) ⟨2439846, by rfl⟩ : syracuseStep 6506257 = 4879693) B4879693
theorem B8675009 : Blo 2029435 8675009 := bstep (se 2 (by rfl) ⟨3253128, by rfl⟩ : syracuseStep 8675009 = 6506257) B6506257
theorem B5783339 : Blo 2029435 5783339 := bstep (se 1 (by rfl) ⟨4337504, by rfl⟩ : syracuseStep 5783339 = 8675009) B8675009
theorem B15422237 : Blo 2029435 15422237 := bstep (se 3 (by rfl) ⟨2891669, by rfl⟩ : syracuseStep 15422237 = 5783339) B5783339
theorem B10281491 : Blo 2029435 10281491 := bstep (se 1 (by rfl) ⟨7711118, by rfl⟩ : syracuseStep 10281491 = 15422237) B15422237
theorem B6854327 : Blo 2029435 6854327 := bstep (se 1 (by rfl) ⟨5140745, by rfl⟩ : syracuseStep 6854327 = 10281491) B10281491
theorem B4569551 : Blo 2029435 4569551 := bstep (se 1 (by rfl) ⟨3427163, by rfl⟩ : syracuseStep 4569551 = 6854327) B6854327
theorem B3046367 : Blo 2029435 3046367 := bstep (se 1 (by rfl) ⟨2284775, by rfl⟩ : syracuseStep 3046367 = 4569551) B4569551
theorem B2030911 : Blo 2029435 2030911 := bstep (se 1 (by rfl) ⟨1523183, by rfl⟩ : syracuseStep 2030911 = 3046367) B3046367
theorem B3046373 : Blo 2029435 3046373 := bbase (se 4 (by rfl) ⟨285597, by rfl⟩ : syracuseStep 3046373 = 571195) (by norm_num)
theorem B2030915 : Blo 2029435 2030915 := bstep (se 1 (by rfl) ⟨1523186, by rfl⟩ : syracuseStep 2030915 = 3046373) B3046373
theorem B8675045 : Blo 2029435 8675045 := bbase (se 4 (by rfl) ⟨813285, by rfl⟩ : syracuseStep 8675045 = 1626571) (by norm_num)
theorem B5783363 : Blo 2029435 5783363 := bstep (se 1 (by rfl) ⟨4337522, by rfl⟩ : syracuseStep 5783363 = 8675045) B8675045
theorem B3855575 : Blo 2029435 3855575 := bstep (se 1 (by rfl) ⟨2891681, by rfl⟩ : syracuseStep 3855575 = 5783363) B5783363
theorem B2570383 : Blo 2029435 2570383 := bstep (se 1 (by rfl) ⟨1927787, by rfl⟩ : syracuseStep 2570383 = 3855575) B3855575
theorem B3427177 : Blo 2029435 3427177 := bstep (se 2 (by rfl) ⟨1285191, by rfl⟩ : syracuseStep 3427177 = 2570383) B2570383
theorem B4569569 : Blo 2029435 4569569 := bstep (se 2 (by rfl) ⟨1713588, by rfl⟩ : syracuseStep 4569569 = 3427177) B3427177
theorem B3046379 : Blo 2029435 3046379 := bstep (se 1 (by rfl) ⟨2284784, by rfl⟩ : syracuseStep 3046379 = 4569569) B4569569
theorem B2030919 : Blo 2029435 2030919 := bstep (se 1 (by rfl) ⟨1523189, by rfl⟩ : syracuseStep 2030919 = 3046379) B3046379
theorem B2284789 : Blo 2029435 2284789 := bbase (se 5 (by rfl) ⟨107099, by rfl⟩ : syracuseStep 2284789 = 214199) (by norm_num)
theorem B3046385 : Blo 2029435 3046385 := bstep (se 2 (by rfl) ⟨1142394, by rfl⟩ : syracuseStep 3046385 = 2284789) B2284789
theorem B2030923 : Blo 2029435 2030923 := bstep (se 1 (by rfl) ⟨1523192, by rfl⟩ : syracuseStep 2030923 = 3046385) B3046385
theorem B2570393 : Blo 2029435 2570393 := bbase (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) (by norm_num)
theorem B6854381 : Blo 2029435 6854381 := bstep (se 3 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 6854381 = 2570393) B2570393
theorem B4569587 : Blo 2029435 4569587 := bstep (se 1 (by rfl) ⟨3427190, by rfl⟩ : syracuseStep 4569587 = 6854381) B6854381
theorem B3046391 : Blo 2029435 3046391 := bstep (se 1 (by rfl) ⟨2284793, by rfl⟩ : syracuseStep 3046391 = 4569587) B4569587
theorem B2030927 : Blo 2029435 2030927 := bstep (se 1 (by rfl) ⟨1523195, by rfl⟩ : syracuseStep 2030927 = 3046391) B3046391
theorem B3046397 : Blo 2029435 3046397 := bbase (se 3 (by rfl) ⟨571199, by rfl⟩ : syracuseStep 3046397 = 1142399) (by norm_num)
theorem B2030931 : Blo 2029435 2030931 := bstep (se 1 (by rfl) ⟨1523198, by rfl⟩ : syracuseStep 2030931 = 3046397) B3046397
theorem B4569605 : Blo 2029435 4569605 := bbase (se 4 (by rfl) ⟨428400, by rfl⟩ : syracuseStep 4569605 = 856801) (by norm_num)
theorem B3046403 : Blo 2029435 3046403 := bstep (se 1 (by rfl) ⟨2284802, by rfl⟩ : syracuseStep 3046403 = 4569605) B4569605
theorem B2030935 : Blo 2029435 2030935 := bstep (se 1 (by rfl) ⟨1523201, by rfl⟩ : syracuseStep 2030935 = 3046403) B3046403
theorem B3855613 : Blo 2029435 3855613 := bbase (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) (by norm_num)
theorem B5140817 : Blo 2029435 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B3427211 : Blo 2029435 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B2284807 : Blo 2029435 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B3046409 : Blo 2029435 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B2030939 : Blo 2029435 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B10281653 : Blo 2029435 10281653 := bbase (se 5 (by rfl) ⟨481952, by rfl⟩ : syracuseStep 10281653 = 963905) (by norm_num)
theorem B6854435 : Blo 2029435 6854435 := bstep (se 1 (by rfl) ⟨5140826, by rfl⟩ : syracuseStep 6854435 = 10281653) B10281653
theorem B4569623 : Blo 2029435 4569623 := bstep (se 1 (by rfl) ⟨3427217, by rfl⟩ : syracuseStep 4569623 = 6854435) B6854435
theorem B3046415 : Blo 2029435 3046415 := bstep (se 1 (by rfl) ⟨2284811, by rfl⟩ : syracuseStep 3046415 = 4569623) B4569623
theorem B2030943 : Blo 2029435 2030943 := bstep (se 1 (by rfl) ⟨1523207, by rfl⟩ : syracuseStep 2030943 = 3046415) B3046415
theorem B3046421 : Blo 2029435 3046421 := bbase (se 6 (by rfl) ⟨71400, by rfl⟩ : syracuseStep 3046421 = 142801) (by norm_num)
theorem B2030947 : Blo 2029435 2030947 := bstep (se 1 (by rfl) ⟨1523210, by rfl⟩ : syracuseStep 2030947 = 3046421) B3046421
theorem B19519157 : Blo 2029435 19519157 := bbase (se 5 (by rfl) ⟨914960, by rfl⟩ : syracuseStep 19519157 = 1829921) (by norm_num)
theorem B13012771 : Blo 2029435 13012771 := bstep (se 1 (by rfl) ⟨9759578, by rfl⟩ : syracuseStep 13012771 = 19519157) B19519157
theorem B17350361 : Blo 2029435 17350361 := bstep (se 2 (by rfl) ⟨6506385, by rfl⟩ : syracuseStep 17350361 = 13012771) B13012771
theorem B11566907 : Blo 2029435 11566907 := bstep (se 1 (by rfl) ⟨8675180, by rfl⟩ : syracuseStep 11566907 = 17350361) B17350361
theorem B7711271 : Blo 2029435 7711271 := bstep (se 1 (by rfl) ⟨5783453, by rfl⟩ : syracuseStep 7711271 = 11566907) B11566907
theorem B5140847 : Blo 2029435 5140847 := bstep (se 1 (by rfl) ⟨3855635, by rfl⟩ : syracuseStep 5140847 = 7711271) B7711271
theorem B3427231 : Blo 2029435 3427231 := bstep (se 1 (by rfl) ⟨2570423, by rfl⟩ : syracuseStep 3427231 = 5140847) B5140847
theorem B4569641 : Blo 2029435 4569641 := bstep (se 2 (by rfl) ⟨1713615, by rfl⟩ : syracuseStep 4569641 = 3427231) B3427231
theorem B3046427 : Blo 2029435 3046427 := bstep (se 1 (by rfl) ⟨2284820, by rfl⟩ : syracuseStep 3046427 = 4569641) B4569641
theorem B2030951 : Blo 2029435 2030951 := bstep (se 1 (by rfl) ⟨1523213, by rfl⟩ : syracuseStep 2030951 = 3046427) B3046427
theorem B2284825 : Blo 2029435 2284825 := bbase (se 2 (by rfl) ⟨856809, by rfl⟩ : syracuseStep 2284825 = 1713619) (by norm_num)
theorem B3046433 : Blo 2029435 3046433 := bstep (se 2 (by rfl) ⟨1142412, by rfl⟩ : syracuseStep 3046433 = 2284825) B2284825
theorem B2030955 : Blo 2029435 2030955 := bstep (se 1 (by rfl) ⟨1523216, by rfl⟩ : syracuseStep 2030955 = 3046433) B3046433
theorem B7711301 : Blo 2029435 7711301 := bbase (se 4 (by rfl) ⟨722934, by rfl⟩ : syracuseStep 7711301 = 1445869) (by norm_num)
theorem B5140867 : Blo 2029435 5140867 := bstep (se 1 (by rfl) ⟨3855650, by rfl⟩ : syracuseStep 5140867 = 7711301) B7711301
theorem B6854489 : Blo 2029435 6854489 := bstep (se 2 (by rfl) ⟨2570433, by rfl⟩ : syracuseStep 6854489 = 5140867) B5140867
theorem B4569659 : Blo 2029435 4569659 := bstep (se 1 (by rfl) ⟨3427244, by rfl⟩ : syracuseStep 4569659 = 6854489) B6854489
theorem B3046439 : Blo 2029435 3046439 := bstep (se 1 (by rfl) ⟨2284829, by rfl⟩ : syracuseStep 3046439 = 4569659) B4569659
theorem B2030959 : Blo 2029435 2030959 := bstep (se 1 (by rfl) ⟨1523219, by rfl⟩ : syracuseStep 2030959 = 3046439) B3046439
theorem B3046445 : Blo 2029435 3046445 := bbase (se 3 (by rfl) ⟨571208, by rfl⟩ : syracuseStep 3046445 = 1142417) (by norm_num)
theorem B2030963 : Blo 2029435 2030963 := bstep (se 1 (by rfl) ⟨1523222, by rfl⟩ : syracuseStep 2030963 = 3046445) B3046445
theorem B4569677 : Blo 2029435 4569677 := bbase (se 3 (by rfl) ⟨856814, by rfl⟩ : syracuseStep 4569677 = 1713629) (by norm_num)
theorem B3046451 : Blo 2029435 3046451 := bstep (se 1 (by rfl) ⟨2284838, by rfl⟩ : syracuseStep 3046451 = 4569677) B4569677
theorem B2030967 : Blo 2029435 2030967 := bstep (se 1 (by rfl) ⟨1523225, by rfl⟩ : syracuseStep 2030967 = 3046451) B3046451
theorem B2570449 : Blo 2029435 2570449 := bbase (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) (by norm_num)
theorem B3427265 : Blo 2029435 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B2284843 : Blo 2029435 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B3046457 : Blo 2029435 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B2030971 : Blo 2029435 2030971 := bstep (se 1 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 2030971 = 3046457) B3046457
theorem B42257173 : Blo 2029435 42257173 := bbase (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) (by norm_num)
theorem B56342897 : Blo 2029435 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B37561931 : Blo 2029435 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B25041287 : Blo 2029435 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B16694191 : Blo 2029435 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B22258921 : Blo 2029435 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B29678561 : Blo 2029435 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B19785707 : Blo 2029435 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B13190471 : Blo 2029435 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B8793647 : Blo 2029435 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B5862431 : Blo 2029435 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B3908287 : Blo 2029435 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B5211049 : Blo 2029435 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B6948065 : Blo 2029435 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B18528173 : Blo 2029435 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B12352115 : Blo 2029435 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B8234743 : Blo 2029435 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B10979657 : Blo 2029435 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B7319771 : Blo 2029435 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B4879847 : Blo 2029435 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B3253231 : Blo 2029435 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B4337641 : Blo 2029435 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B23134085 : Blo 2029435 23134085 := bstep (se 4 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 23134085 = 4337641) B4337641
theorem B15422723 : Blo 2029435 15422723 := bstep (se 1 (by rfl) ⟨11567042, by rfl⟩ : syracuseStep 15422723 = 23134085) B23134085
theorem B10281815 : Blo 2029435 10281815 := bstep (se 1 (by rfl) ⟨7711361, by rfl⟩ : syracuseStep 10281815 = 15422723) B15422723
theorem B6854543 : Blo 2029435 6854543 := bstep (se 1 (by rfl) ⟨5140907, by rfl⟩ : syracuseStep 6854543 = 10281815) B10281815
theorem B4569695 : Blo 2029435 4569695 := bstep (se 1 (by rfl) ⟨3427271, by rfl⟩ : syracuseStep 4569695 = 6854543) B6854543
theorem B3046463 : Blo 2029435 3046463 := bstep (se 1 (by rfl) ⟨2284847, by rfl⟩ : syracuseStep 3046463 = 4569695) B4569695
theorem B2030975 : Blo 2029435 2030975 := bstep (se 1 (by rfl) ⟨1523231, by rfl⟩ : syracuseStep 2030975 = 3046463) B3046463
theorem B3046469 : Blo 2029435 3046469 := bbase (se 4 (by rfl) ⟨285606, by rfl⟩ : syracuseStep 3046469 = 571213) (by norm_num)
theorem B2030979 : Blo 2029435 2030979 := bstep (se 1 (by rfl) ⟨1523234, by rfl⟩ : syracuseStep 2030979 = 3046469) B3046469
theorem B3427285 : Blo 2029435 3427285 := bbase (se 7 (by rfl) ⟨40163, by rfl⟩ : syracuseStep 3427285 = 80327) (by norm_num)
theorem B4569713 : Blo 2029435 4569713 := bstep (se 2 (by rfl) ⟨1713642, by rfl⟩ : syracuseStep 4569713 = 3427285) B3427285
theorem B3046475 : Blo 2029435 3046475 := bstep (se 1 (by rfl) ⟨2284856, by rfl⟩ : syracuseStep 3046475 = 4569713) B4569713
theorem B2030983 : Blo 2029435 2030983 := bstep (se 1 (by rfl) ⟨1523237, by rfl⟩ : syracuseStep 2030983 = 3046475) B3046475
theorem B2284861 : Blo 2029435 2284861 := bbase (se 3 (by rfl) ⟨428411, by rfl⟩ : syracuseStep 2284861 = 856823) (by norm_num)
theorem B3046481 : Blo 2029435 3046481 := bstep (se 2 (by rfl) ⟨1142430, by rfl⟩ : syracuseStep 3046481 = 2284861) B2284861
theorem B2030987 : Blo 2029435 2030987 := bstep (se 1 (by rfl) ⟨1523240, by rfl⟩ : syracuseStep 2030987 = 3046481) B3046481
theorem B6854597 : Blo 2029435 6854597 := bbase (se 4 (by rfl) ⟨642618, by rfl⟩ : syracuseStep 6854597 = 1285237) (by norm_num)
theorem B4569731 : Blo 2029435 4569731 := bstep (se 1 (by rfl) ⟨3427298, by rfl⟩ : syracuseStep 4569731 = 6854597) B6854597
theorem B3046487 : Blo 2029435 3046487 := bstep (se 1 (by rfl) ⟨2284865, by rfl⟩ : syracuseStep 3046487 = 4569731) B4569731
theorem B2030991 : Blo 2029435 2030991 := bstep (se 1 (by rfl) ⟨1523243, by rfl⟩ : syracuseStep 2030991 = 3046487) B3046487
theorem B3046493 : Blo 2029435 3046493 := bbase (se 3 (by rfl) ⟨571217, by rfl⟩ : syracuseStep 3046493 = 1142435) (by norm_num)
theorem B2030995 : Blo 2029435 2030995 := bstep (se 1 (by rfl) ⟨1523246, by rfl⟩ : syracuseStep 2030995 = 3046493) B3046493
theorem B4569749 : Blo 2029435 4569749 := bbase (se 6 (by rfl) ⟨107103, by rfl⟩ : syracuseStep 4569749 = 214207) (by norm_num)
theorem B3046499 : Blo 2029435 3046499 := bstep (se 1 (by rfl) ⟨2284874, by rfl⟩ : syracuseStep 3046499 = 4569749) B4569749
theorem B2030999 : Blo 2029435 2030999 := bstep (se 1 (by rfl) ⟨1523249, by rfl⟩ : syracuseStep 2030999 = 3046499) B3046499
theorem B3253277 : Blo 2029435 3253277 := bbase (se 3 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 3253277 = 1219979) (by norm_num)
theorem B2168851 : Blo 2029435 2168851 := bstep (se 1 (by rfl) ⟨1626638, by rfl⟩ : syracuseStep 2168851 = 3253277) B3253277
theorem B2891801 : Blo 2029435 2891801 := bstep (se 2 (by rfl) ⟨1084425, by rfl⟩ : syracuseStep 2891801 = 2168851) B2168851
theorem B7711469 : Blo 2029435 7711469 := bstep (se 3 (by rfl) ⟨1445900, by rfl⟩ : syracuseStep 7711469 = 2891801) B2891801
theorem B5140979 : Blo 2029435 5140979 := bstep (se 1 (by rfl) ⟨3855734, by rfl⟩ : syracuseStep 5140979 = 7711469) B7711469
theorem B3427319 : Blo 2029435 3427319 := bstep (se 1 (by rfl) ⟨2570489, by rfl⟩ : syracuseStep 3427319 = 5140979) B5140979
theorem B2284879 : Blo 2029435 2284879 := bstep (se 1 (by rfl) ⟨1713659, by rfl⟩ : syracuseStep 2284879 = 3427319) B3427319
theorem B3046505 : Blo 2029435 3046505 := bstep (se 2 (by rfl) ⟨1142439, by rfl⟩ : syracuseStep 3046505 = 2284879) B2284879
theorem B2031003 : Blo 2029435 2031003 := bstep (se 1 (by rfl) ⟨1523252, by rfl⟩ : syracuseStep 2031003 = 3046505) B3046505
theorem B3521485 : Blo 2029435 3521485 := bbase (se 3 (by rfl) ⟨660278, by rfl⟩ : syracuseStep 3521485 = 1320557) (by norm_num)
theorem B18781253 : Blo 2029435 18781253 := bstep (se 4 (by rfl) ⟨1760742, by rfl⟩ : syracuseStep 18781253 = 3521485) B3521485
theorem B12520835 : Blo 2029435 12520835 := bstep (se 1 (by rfl) ⟨9390626, by rfl⟩ : syracuseStep 12520835 = 18781253) B18781253
theorem B8347223 : Blo 2029435 8347223 := bstep (se 1 (by rfl) ⟨6260417, by rfl⟩ : syracuseStep 8347223 = 12520835) B12520835
theorem B22259261 : Blo 2029435 22259261 := bstep (se 3 (by rfl) ⟨4173611, by rfl⟩ : syracuseStep 22259261 = 8347223) B8347223
theorem B14839507 : Blo 2029435 14839507 := bstep (se 1 (by rfl) ⟨11129630, by rfl⟩ : syracuseStep 14839507 = 22259261) B22259261
theorem B79144037 : Blo 2029435 79144037 := bstep (se 4 (by rfl) ⟨7419753, by rfl⟩ : syracuseStep 79144037 = 14839507) B14839507
theorem B52762691 : Blo 2029435 52762691 := bstep (se 1 (by rfl) ⟨39572018, by rfl⟩ : syracuseStep 52762691 = 79144037) B79144037
theorem B140700509 : Blo 2029435 140700509 := bstep (se 3 (by rfl) ⟨26381345, by rfl⟩ : syracuseStep 140700509 = 52762691) B52762691
theorem B93800339 : Blo 2029435 93800339 := bstep (se 1 (by rfl) ⟨70350254, by rfl⟩ : syracuseStep 93800339 = 140700509) B140700509
theorem B62533559 : Blo 2029435 62533559 := bstep (se 1 (by rfl) ⟨46900169, by rfl⟩ : syracuseStep 62533559 = 93800339) B93800339
theorem B41689039 : Blo 2029435 41689039 := bstep (se 1 (by rfl) ⟨31266779, by rfl⟩ : syracuseStep 41689039 = 62533559) B62533559
theorem B55585385 : Blo 2029435 55585385 := bstep (se 2 (by rfl) ⟨20844519, by rfl⟩ : syracuseStep 55585385 = 41689039) B41689039
theorem B37056923 : Blo 2029435 37056923 := bstep (se 1 (by rfl) ⟨27792692, by rfl⟩ : syracuseStep 37056923 = 55585385) B55585385
theorem B24704615 : Blo 2029435 24704615 := bstep (se 1 (by rfl) ⟨18528461, by rfl⟩ : syracuseStep 24704615 = 37056923) B37056923
theorem B16469743 : Blo 2029435 16469743 := bstep (se 1 (by rfl) ⟨12352307, by rfl⟩ : syracuseStep 16469743 = 24704615) B24704615
theorem B21959657 : Blo 2029435 21959657 := bstep (se 2 (by rfl) ⟨8234871, by rfl⟩ : syracuseStep 21959657 = 16469743) B16469743
theorem B14639771 : Blo 2029435 14639771 := bstep (se 1 (by rfl) ⟨10979828, by rfl⟩ : syracuseStep 14639771 = 21959657) B21959657
theorem B9759847 : Blo 2029435 9759847 := bstep (se 1 (by rfl) ⟨7319885, by rfl⟩ : syracuseStep 9759847 = 14639771) B14639771
theorem B13013129 : Blo 2029435 13013129 := bstep (se 2 (by rfl) ⟨4879923, by rfl⟩ : syracuseStep 13013129 = 9759847) B9759847
theorem B8675419 : Blo 2029435 8675419 := bstep (se 1 (by rfl) ⟨6506564, by rfl⟩ : syracuseStep 8675419 = 13013129) B13013129
theorem B11567225 : Blo 2029435 11567225 := bstep (se 2 (by rfl) ⟨4337709, by rfl⟩ : syracuseStep 11567225 = 8675419) B8675419
theorem B7711483 : Blo 2029435 7711483 := bstep (se 1 (by rfl) ⟨5783612, by rfl⟩ : syracuseStep 7711483 = 11567225) B11567225
theorem B10281977 : Blo 2029435 10281977 := bstep (se 2 (by rfl) ⟨3855741, by rfl⟩ : syracuseStep 10281977 = 7711483) B7711483
theorem B6854651 : Blo 2029435 6854651 := bstep (se 1 (by rfl) ⟨5140988, by rfl⟩ : syracuseStep 6854651 = 10281977) B10281977
theorem B4569767 : Blo 2029435 4569767 := bstep (se 1 (by rfl) ⟨3427325, by rfl⟩ : syracuseStep 4569767 = 6854651) B6854651
theorem B3046511 : Blo 2029435 3046511 := bstep (se 1 (by rfl) ⟨2284883, by rfl⟩ : syracuseStep 3046511 = 4569767) B4569767
theorem B2031007 : Blo 2029435 2031007 := bstep (se 1 (by rfl) ⟨1523255, by rfl⟩ : syracuseStep 2031007 = 3046511) B3046511
theorem B3046517 : Blo 2029435 3046517 := bbase (se 5 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 3046517 = 285611) (by norm_num)
theorem B2031011 : Blo 2029435 2031011 := bstep (se 1 (by rfl) ⟨1523258, by rfl⟩ : syracuseStep 2031011 = 3046517) B3046517
theorem B3855757 : Blo 2029435 3855757 := bbase (se 3 (by rfl) ⟨722954, by rfl⟩ : syracuseStep 3855757 = 1445909) (by norm_num)
theorem B5141009 : Blo 2029435 5141009 := bstep (se 2 (by rfl) ⟨1927878, by rfl⟩ : syracuseStep 5141009 = 3855757) B3855757
theorem B3427339 : Blo 2029435 3427339 := bstep (se 1 (by rfl) ⟨2570504, by rfl⟩ : syracuseStep 3427339 = 5141009) B5141009
theorem B4569785 : Blo 2029435 4569785 := bstep (se 2 (by rfl) ⟨1713669, by rfl⟩ : syracuseStep 4569785 = 3427339) B3427339
theorem B3046523 : Blo 2029435 3046523 := bstep (se 1 (by rfl) ⟨2284892, by rfl⟩ : syracuseStep 3046523 = 4569785) B4569785
theorem B2031015 : Blo 2029435 2031015 := bstep (se 1 (by rfl) ⟨1523261, by rfl⟩ : syracuseStep 2031015 = 3046523) B3046523
theorem B2284897 : Blo 2029435 2284897 := bbase (se 2 (by rfl) ⟨856836, by rfl⟩ : syracuseStep 2284897 = 1713673) (by norm_num)
theorem B3046529 : Blo 2029435 3046529 := bstep (se 2 (by rfl) ⟨1142448, by rfl⟩ : syracuseStep 3046529 = 2284897) B2284897
theorem B2031019 : Blo 2029435 2031019 := bstep (se 1 (by rfl) ⟨1523264, by rfl⟩ : syracuseStep 2031019 = 3046529) B3046529
theorem B5141029 : Blo 2029435 5141029 := bbase (se 4 (by rfl) ⟨481971, by rfl⟩ : syracuseStep 5141029 = 963943) (by norm_num)
theorem B6854705 : Blo 2029435 6854705 := bstep (se 2 (by rfl) ⟨2570514, by rfl⟩ : syracuseStep 6854705 = 5141029) B5141029
theorem B4569803 : Blo 2029435 4569803 := bstep (se 1 (by rfl) ⟨3427352, by rfl⟩ : syracuseStep 4569803 = 6854705) B6854705
theorem B3046535 : Blo 2029435 3046535 := bstep (se 1 (by rfl) ⟨2284901, by rfl⟩ : syracuseStep 3046535 = 4569803) B4569803
theorem B2031023 : Blo 2029435 2031023 := bstep (se 1 (by rfl) ⟨1523267, by rfl⟩ : syracuseStep 2031023 = 3046535) B3046535
theorem B3046541 : Blo 2029435 3046541 := bbase (se 3 (by rfl) ⟨571226, by rfl⟩ : syracuseStep 3046541 = 1142453) (by norm_num)
theorem B2031027 : Blo 2029435 2031027 := bstep (se 1 (by rfl) ⟨1523270, by rfl⟩ : syracuseStep 2031027 = 3046541) B3046541
theorem B4569821 : Blo 2029435 4569821 := bbase (se 3 (by rfl) ⟨856841, by rfl⟩ : syracuseStep 4569821 = 1713683) (by norm_num)
theorem B3046547 : Blo 2029435 3046547 := bstep (se 1 (by rfl) ⟨2284910, by rfl⟩ : syracuseStep 3046547 = 4569821) B4569821
theorem B2031031 : Blo 2029435 2031031 := bstep (se 1 (by rfl) ⟨1523273, by rfl⟩ : syracuseStep 2031031 = 3046547) B3046547
theorem B3427373 : Blo 2029435 3427373 := bbase (se 3 (by rfl) ⟨642632, by rfl⟩ : syracuseStep 3427373 = 1285265) (by norm_num)
theorem B2284915 : Blo 2029435 2284915 := bstep (se 1 (by rfl) ⟨1713686, by rfl⟩ : syracuseStep 2284915 = 3427373) B3427373
theorem B3046553 : Blo 2029435 3046553 := bstep (se 2 (by rfl) ⟨1142457, by rfl⟩ : syracuseStep 3046553 = 2284915) B2284915
theorem B2031035 : Blo 2029435 2031035 := bstep (se 1 (by rfl) ⟨1523276, by rfl⟩ : syracuseStep 2031035 = 3046553) B3046553
theorem B12352501 : Blo 2029435 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B16470001 : Blo 2029435 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B21960001 : Blo 2029435 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B29280001 : Blo 2029435 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B39040001 : Blo 2029435 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B26026667 : Blo 2029435 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B17351111 : Blo 2029435 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B11567407 : Blo 2029435 11567407 := bstep (se 1 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 11567407 = 17351111) B17351111
theorem B15423209 : Blo 2029435 15423209 := bstep (se 2 (by rfl) ⟨5783703, by rfl⟩ : syracuseStep 15423209 = 11567407) B11567407
theorem B10282139 : Blo 2029435 10282139 := bstep (se 1 (by rfl) ⟨7711604, by rfl⟩ : syracuseStep 10282139 = 15423209) B15423209
theorem B6854759 : Blo 2029435 6854759 := bstep (se 1 (by rfl) ⟨5141069, by rfl⟩ : syracuseStep 6854759 = 10282139) B10282139
theorem B4569839 : Blo 2029435 4569839 := bstep (se 1 (by rfl) ⟨3427379, by rfl⟩ : syracuseStep 4569839 = 6854759) B6854759
theorem B3046559 : Blo 2029435 3046559 := bstep (se 1 (by rfl) ⟨2284919, by rfl⟩ : syracuseStep 3046559 = 4569839) B4569839
theorem B2031039 : Blo 2029435 2031039 := bstep (se 1 (by rfl) ⟨1523279, by rfl⟩ : syracuseStep 2031039 = 3046559) B3046559
theorem B3046565 : Blo 2029435 3046565 := bbase (se 4 (by rfl) ⟨285615, by rfl⟩ : syracuseStep 3046565 = 571231) (by norm_num)
theorem B2031043 : Blo 2029435 2031043 := bstep (se 1 (by rfl) ⟨1523282, by rfl⟩ : syracuseStep 2031043 = 3046565) B3046565
theorem B2570545 : Blo 2029435 2570545 := bbase (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) (by norm_num)
theorem B3427393 : Blo 2029435 3427393 := bstep (se 2 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 3427393 = 2570545) B2570545
theorem B4569857 : Blo 2029435 4569857 := bstep (se 2 (by rfl) ⟨1713696, by rfl⟩ : syracuseStep 4569857 = 3427393) B3427393
theorem B3046571 : Blo 2029435 3046571 := bstep (se 1 (by rfl) ⟨2284928, by rfl⟩ : syracuseStep 3046571 = 4569857) B4569857
theorem B2031047 : Blo 2029435 2031047 := bstep (se 1 (by rfl) ⟨1523285, by rfl⟩ : syracuseStep 2031047 = 3046571) B3046571
theorem B2284933 : Blo 2029435 2284933 := bbase (se 4 (by rfl) ⟨214212, by rfl⟩ : syracuseStep 2284933 = 428425) (by norm_num)
theorem B3046577 : Blo 2029435 3046577 := bstep (se 2 (by rfl) ⟨1142466, by rfl⟩ : syracuseStep 3046577 = 2284933) B2284933
theorem B2031051 : Blo 2029435 2031051 := bstep (se 1 (by rfl) ⟨1523288, by rfl⟩ : syracuseStep 2031051 = 3046577) B3046577
theorem B4337813 : Blo 2029435 4337813 := bbase (se 6 (by rfl) ⟨101667, by rfl⟩ : syracuseStep 4337813 = 203335) (by norm_num)
theorem B2891875 : Blo 2029435 2891875 := bstep (se 1 (by rfl) ⟨2168906, by rfl⟩ : syracuseStep 2891875 = 4337813) B4337813
theorem B3855833 : Blo 2029435 3855833 := bstep (se 2 (by rfl) ⟨1445937, by rfl⟩ : syracuseStep 3855833 = 2891875) B2891875
theorem B2570555 : Blo 2029435 2570555 := bstep (se 1 (by rfl) ⟨1927916, by rfl⟩ : syracuseStep 2570555 = 3855833) B3855833
theorem B6854813 : Blo 2029435 6854813 := bstep (se 3 (by rfl) ⟨1285277, by rfl⟩ : syracuseStep 6854813 = 2570555) B2570555
theorem B4569875 : Blo 2029435 4569875 := bstep (se 1 (by rfl) ⟨3427406, by rfl⟩ : syracuseStep 4569875 = 6854813) B6854813
theorem B3046583 : Blo 2029435 3046583 := bstep (se 1 (by rfl) ⟨2284937, by rfl⟩ : syracuseStep 3046583 = 4569875) B4569875
theorem B2031055 : Blo 2029435 2031055 := bstep (se 1 (by rfl) ⟨1523291, by rfl⟩ : syracuseStep 2031055 = 3046583) B3046583
theorem B3046589 : Blo 2029435 3046589 := bbase (se 3 (by rfl) ⟨571235, by rfl⟩ : syracuseStep 3046589 = 1142471) (by norm_num)
theorem B2031059 : Blo 2029435 2031059 := bstep (se 1 (by rfl) ⟨1523294, by rfl⟩ : syracuseStep 2031059 = 3046589) B3046589
theorem B4569893 : Blo 2029435 4569893 := bbase (se 4 (by rfl) ⟨428427, by rfl⟩ : syracuseStep 4569893 = 856855) (by norm_num)
theorem B3046595 : Blo 2029435 3046595 := bstep (se 1 (by rfl) ⟨2284946, by rfl⟩ : syracuseStep 3046595 = 4569893) B4569893
theorem B2031063 : Blo 2029435 2031063 := bstep (se 1 (by rfl) ⟨1523297, by rfl⟩ : syracuseStep 2031063 = 3046595) B3046595
theorem B5141141 : Blo 2029435 5141141 := bbase (se 6 (by rfl) ⟨120495, by rfl⟩ : syracuseStep 5141141 = 240991) (by norm_num)
theorem B3427427 : Blo 2029435 3427427 := bstep (se 1 (by rfl) ⟨2570570, by rfl⟩ : syracuseStep 3427427 = 5141141) B5141141
theorem B2284951 : Blo 2029435 2284951 := bstep (se 1 (by rfl) ⟨1713713, by rfl⟩ : syracuseStep 2284951 = 3427427) B3427427
theorem B3046601 : Blo 2029435 3046601 := bstep (se 2 (by rfl) ⟨1142475, by rfl⟩ : syracuseStep 3046601 = 2284951) B2284951
theorem B2031067 : Blo 2029435 2031067 := bstep (se 1 (by rfl) ⟨1523300, by rfl⟩ : syracuseStep 2031067 = 3046601) B3046601
theorem B5862709 : Blo 2029435 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B31267781 : Blo 2029435 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B20845187 : Blo 2029435 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B13896791 : Blo 2029435 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B9264527 : Blo 2029435 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B6176351 : Blo 2029435 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B4117567 : Blo 2029435 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B5490089 : Blo 2029435 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B3660059 : Blo 2029435 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2440039 : Blo 2029435 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B3253385 : Blo 2029435 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B8675693 : Blo 2029435 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B5783795 : Blo 2029435 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B3855863 : Blo 2029435 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B10282301 : Blo 2029435 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B6854867 : Blo 2029435 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B4569911 : Blo 2029435 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B3046607 : Blo 2029435 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B2031071 : Blo 2029435 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B3046613 : Blo 2029435 3046613 := bbase (se 7 (by rfl) ⟨35702, by rfl⟩ : syracuseStep 3046613 = 71405) (by norm_num)
theorem B2031075 : Blo 2029435 2031075 := bstep (se 1 (by rfl) ⟨1523306, by rfl⟩ : syracuseStep 2031075 = 3046613) B3046613
theorem B2891909 : Blo 2029435 2891909 := bbase (se 4 (by rfl) ⟨271116, by rfl⟩ : syracuseStep 2891909 = 542233) (by norm_num)
theorem B7711757 : Blo 2029435 7711757 := bstep (se 3 (by rfl) ⟨1445954, by rfl⟩ : syracuseStep 7711757 = 2891909) B2891909
theorem B5141171 : Blo 2029435 5141171 := bstep (se 1 (by rfl) ⟨3855878, by rfl⟩ : syracuseStep 5141171 = 7711757) B7711757
theorem B3427447 : Blo 2029435 3427447 := bstep (se 1 (by rfl) ⟨2570585, by rfl⟩ : syracuseStep 3427447 = 5141171) B5141171
theorem B4569929 : Blo 2029435 4569929 := bstep (se 2 (by rfl) ⟨1713723, by rfl⟩ : syracuseStep 4569929 = 3427447) B3427447
theorem B3046619 : Blo 2029435 3046619 := bstep (se 1 (by rfl) ⟨2284964, by rfl⟩ : syracuseStep 3046619 = 4569929) B4569929
theorem B2031079 : Blo 2029435 2031079 := bstep (se 1 (by rfl) ⟨1523309, by rfl⟩ : syracuseStep 2031079 = 3046619) B3046619
theorem B2284969 : Blo 2029435 2284969 := bbase (se 2 (by rfl) ⟨856863, by rfl⟩ : syracuseStep 2284969 = 1713727) (by norm_num)
theorem B3046625 : Blo 2029435 3046625 := bstep (se 2 (by rfl) ⟨1142484, by rfl⟩ : syracuseStep 3046625 = 2284969) B2284969
theorem B2031083 : Blo 2029435 2031083 := bstep (se 1 (by rfl) ⟨1523312, by rfl⟩ : syracuseStep 2031083 = 3046625) B3046625
theorem B6506821 : Blo 2029435 6506821 := bbase (se 4 (by rfl) ⟨610014, by rfl⟩ : syracuseStep 6506821 = 1220029) (by norm_num)
theorem B8675761 : Blo 2029435 8675761 := bstep (se 2 (by rfl) ⟨3253410, by rfl⟩ : syracuseStep 8675761 = 6506821) B6506821
theorem B11567681 : Blo 2029435 11567681 := bstep (se 2 (by rfl) ⟨4337880, by rfl⟩ : syracuseStep 11567681 = 8675761) B8675761
theorem B7711787 : Blo 2029435 7711787 := bstep (se 1 (by rfl) ⟨5783840, by rfl⟩ : syracuseStep 7711787 = 11567681) B11567681
theorem B5141191 : Blo 2029435 5141191 := bstep (se 1 (by rfl) ⟨3855893, by rfl⟩ : syracuseStep 5141191 = 7711787) B7711787
theorem B6854921 : Blo 2029435 6854921 := bstep (se 2 (by rfl) ⟨2570595, by rfl⟩ : syracuseStep 6854921 = 5141191) B5141191
theorem B4569947 : Blo 2029435 4569947 := bstep (se 1 (by rfl) ⟨3427460, by rfl⟩ : syracuseStep 4569947 = 6854921) B6854921
theorem B3046631 : Blo 2029435 3046631 := bstep (se 1 (by rfl) ⟨2284973, by rfl⟩ : syracuseStep 3046631 = 4569947) B4569947
theorem B2031087 : Blo 2029435 2031087 := bstep (se 1 (by rfl) ⟨1523315, by rfl⟩ : syracuseStep 2031087 = 3046631) B3046631
theorem B3046637 : Blo 2029435 3046637 := bbase (se 3 (by rfl) ⟨571244, by rfl⟩ : syracuseStep 3046637 = 1142489) (by norm_num)
theorem B2031091 : Blo 2029435 2031091 := bstep (se 1 (by rfl) ⟨1523318, by rfl⟩ : syracuseStep 2031091 = 3046637) B3046637
theorem B4569965 : Blo 2029435 4569965 := bbase (se 3 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 4569965 = 1713737) (by norm_num)
theorem B3046643 : Blo 2029435 3046643 := bstep (se 1 (by rfl) ⟨2284982, by rfl⟩ : syracuseStep 3046643 = 4569965) B4569965
theorem B2031095 : Blo 2029435 2031095 := bstep (se 1 (by rfl) ⟨1523321, by rfl⟩ : syracuseStep 2031095 = 3046643) B3046643
theorem B3855917 : Blo 2029435 3855917 := bbase (se 3 (by rfl) ⟨722984, by rfl⟩ : syracuseStep 3855917 = 1445969) (by norm_num)
theorem B2570611 : Blo 2029435 2570611 := bstep (se 1 (by rfl) ⟨1927958, by rfl⟩ : syracuseStep 2570611 = 3855917) B3855917
theorem B3427481 : Blo 2029435 3427481 := bstep (se 2 (by rfl) ⟨1285305, by rfl⟩ : syracuseStep 3427481 = 2570611) B2570611
theorem B2284987 : Blo 2029435 2284987 := bstep (se 1 (by rfl) ⟨1713740, by rfl⟩ : syracuseStep 2284987 = 3427481) B3427481
theorem B3046649 : Blo 2029435 3046649 := bstep (se 2 (by rfl) ⟨1142493, by rfl⟩ : syracuseStep 3046649 = 2284987) B2284987
theorem B2031099 : Blo 2029435 2031099 := bstep (se 1 (by rfl) ⟨1523324, by rfl⟩ : syracuseStep 2031099 = 3046649) B3046649
theorem B28173205 : Blo 2029435 28173205 := bbase (se 6 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 28173205 = 1320619) (by norm_num)
theorem B37564273 : Blo 2029435 37564273 := bstep (se 2 (by rfl) ⟨14086602, by rfl⟩ : syracuseStep 37564273 = 28173205) B28173205
theorem B50085697 : Blo 2029435 50085697 := bstep (se 2 (by rfl) ⟨18782136, by rfl⟩ : syracuseStep 50085697 = 37564273) B37564273
theorem B66780929 : Blo 2029435 66780929 := bstep (se 2 (by rfl) ⟨25042848, by rfl⟩ : syracuseStep 66780929 = 50085697) B50085697
theorem B44520619 : Blo 2029435 44520619 := bstep (se 1 (by rfl) ⟨33390464, by rfl⟩ : syracuseStep 44520619 = 66780929) B66780929
theorem B59360825 : Blo 2029435 59360825 := bstep (se 2 (by rfl) ⟨22260309, by rfl⟩ : syracuseStep 59360825 = 44520619) B44520619
theorem B39573883 : Blo 2029435 39573883 := bstep (se 1 (by rfl) ⟨29680412, by rfl⟩ : syracuseStep 39573883 = 59360825) B59360825
theorem B52765177 : Blo 2029435 52765177 := bstep (se 2 (by rfl) ⟨19786941, by rfl⟩ : syracuseStep 52765177 = 39573883) B39573883
theorem B70353569 : Blo 2029435 70353569 := bstep (se 2 (by rfl) ⟨26382588, by rfl⟩ : syracuseStep 70353569 = 52765177) B52765177
theorem B187609517 : Blo 2029435 187609517 := bstep (se 3 (by rfl) ⟨35176784, by rfl⟩ : syracuseStep 187609517 = 70353569) B70353569
theorem B125073011 : Blo 2029435 125073011 := bstep (se 1 (by rfl) ⟨93804758, by rfl⟩ : syracuseStep 125073011 = 187609517) B187609517
theorem B83382007 : Blo 2029435 83382007 := bstep (se 1 (by rfl) ⟨62536505, by rfl⟩ : syracuseStep 83382007 = 125073011) B125073011
theorem B111176009 : Blo 2029435 111176009 := bstep (se 2 (by rfl) ⟨41691003, by rfl⟩ : syracuseStep 111176009 = 83382007) B83382007
theorem B74117339 : Blo 2029435 74117339 := bstep (se 1 (by rfl) ⟨55588004, by rfl⟩ : syracuseStep 74117339 = 111176009) B111176009
theorem B49411559 : Blo 2029435 49411559 := bstep (se 1 (by rfl) ⟨37058669, by rfl⟩ : syracuseStep 49411559 = 74117339) B74117339
theorem B32941039 : Blo 2029435 32941039 := bstep (se 1 (by rfl) ⟨24705779, by rfl⟩ : syracuseStep 32941039 = 49411559) B49411559
theorem B43921385 : Blo 2029435 43921385 := bstep (se 2 (by rfl) ⟨16470519, by rfl⟩ : syracuseStep 43921385 = 32941039) B32941039
theorem B29280923 : Blo 2029435 29280923 := bstep (se 1 (by rfl) ⟨21960692, by rfl⟩ : syracuseStep 29280923 = 43921385) B43921385
theorem B19520615 : Blo 2029435 19520615 := bstep (se 1 (by rfl) ⟨14640461, by rfl⟩ : syracuseStep 19520615 = 29280923) B29280923
theorem B52054973 : Blo 2029435 52054973 := bstep (se 3 (by rfl) ⟨9760307, by rfl⟩ : syracuseStep 52054973 = 19520615) B19520615
theorem B34703315 : Blo 2029435 34703315 := bstep (se 1 (by rfl) ⟨26027486, by rfl⟩ : syracuseStep 34703315 = 52054973) B52054973
theorem B23135543 : Blo 2029435 23135543 := bstep (se 1 (by rfl) ⟨17351657, by rfl⟩ : syracuseStep 23135543 = 34703315) B34703315
theorem B15423695 : Blo 2029435 15423695 := bstep (se 1 (by rfl) ⟨11567771, by rfl⟩ : syracuseStep 15423695 = 23135543) B23135543
theorem B10282463 : Blo 2029435 10282463 := bstep (se 1 (by rfl) ⟨7711847, by rfl⟩ : syracuseStep 10282463 = 15423695) B15423695
theorem B6854975 : Blo 2029435 6854975 := bstep (se 1 (by rfl) ⟨5141231, by rfl⟩ : syracuseStep 6854975 = 10282463) B10282463
theorem B4569983 : Blo 2029435 4569983 := bstep (se 1 (by rfl) ⟨3427487, by rfl⟩ : syracuseStep 4569983 = 6854975) B6854975
theorem B3046655 : Blo 2029435 3046655 := bstep (se 1 (by rfl) ⟨2284991, by rfl⟩ : syracuseStep 3046655 = 4569983) B4569983
theorem B2031103 : Blo 2029435 2031103 := bstep (se 1 (by rfl) ⟨1523327, by rfl⟩ : syracuseStep 2031103 = 3046655) B3046655
theorem B3046661 : Blo 2029435 3046661 := bbase (se 4 (by rfl) ⟨285624, by rfl⟩ : syracuseStep 3046661 = 571249) (by norm_num)
theorem B2031107 : Blo 2029435 2031107 := bstep (se 1 (by rfl) ⟨1523330, by rfl⟩ : syracuseStep 2031107 = 3046661) B3046661
theorem B3427501 : Blo 2029435 3427501 := bbase (se 3 (by rfl) ⟨642656, by rfl⟩ : syracuseStep 3427501 = 1285313) (by norm_num)
theorem B4570001 : Blo 2029435 4570001 := bstep (se 2 (by rfl) ⟨1713750, by rfl⟩ : syracuseStep 4570001 = 3427501) B3427501
theorem B3046667 : Blo 2029435 3046667 := bstep (se 1 (by rfl) ⟨2285000, by rfl⟩ : syracuseStep 3046667 = 4570001) B4570001
theorem B2031111 : Blo 2029435 2031111 := bstep (se 1 (by rfl) ⟨1523333, by rfl⟩ : syracuseStep 2031111 = 3046667) B3046667
theorem B2285005 : Blo 2029435 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B3046673 : Blo 2029435 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B2031115 : Blo 2029435 2031115 := bstep (se 1 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 2031115 = 3046673) B3046673
theorem B6855029 : Blo 2029435 6855029 := bbase (se 5 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 6855029 = 642659) (by norm_num)
theorem B4570019 : Blo 2029435 4570019 := bstep (se 1 (by rfl) ⟨3427514, by rfl⟩ : syracuseStep 4570019 = 6855029) B6855029
theorem B3046679 : Blo 2029435 3046679 := bstep (se 1 (by rfl) ⟨2285009, by rfl⟩ : syracuseStep 3046679 = 4570019) B4570019
theorem B2031119 : Blo 2029435 2031119 := bstep (se 1 (by rfl) ⟨1523339, by rfl⟩ : syracuseStep 2031119 = 3046679) B3046679
theorem B3046685 : Blo 2029435 3046685 := bbase (se 3 (by rfl) ⟨571253, by rfl⟩ : syracuseStep 3046685 = 1142507) (by norm_num)
theorem B2031123 : Blo 2029435 2031123 := bstep (se 1 (by rfl) ⟨1523342, by rfl⟩ : syracuseStep 2031123 = 3046685) B3046685
theorem B4570037 : Blo 2029435 4570037 := bbase (se 5 (by rfl) ⟨214220, by rfl⟩ : syracuseStep 4570037 = 428441) (by norm_num)
theorem B3046691 : Blo 2029435 3046691 := bstep (se 1 (by rfl) ⟨2285018, by rfl⟩ : syracuseStep 3046691 = 4570037) B4570037
theorem B2031127 : Blo 2029435 2031127 := bstep (se 1 (by rfl) ⟨1523345, by rfl⟩ : syracuseStep 2031127 = 3046691) B3046691
theorem B6176533 : Blo 2029435 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B8235377 : Blo 2029435 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B5490251 : Blo 2029435 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B3660167 : Blo 2029435 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B9760445 : Blo 2029435 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B6506963 : Blo 2029435 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B4337975 : Blo 2029435 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B11567933 : Blo 2029435 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B7711955 : Blo 2029435 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B5141303 : Blo 2029435 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B3427535 : Blo 2029435 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B2285023 : Blo 2029435 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B3046697 : Blo 2029435 3046697 := bstep (se 2 (by rfl) ⟨1142511, by rfl⟩ : syracuseStep 3046697 = 2285023) B2285023
theorem B2031131 : Blo 2029435 2031131 := bstep (se 1 (by rfl) ⟨1523348, by rfl⟩ : syracuseStep 2031131 = 3046697) B3046697
theorem B7521461 : Blo 2029435 7521461 := bbase (se 5 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 7521461 = 705137) (by norm_num)
theorem B5014307 : Blo 2029435 5014307 := bstep (se 1 (by rfl) ⟨3760730, by rfl⟩ : syracuseStep 5014307 = 7521461) B7521461
theorem B13371485 : Blo 2029435 13371485 := bstep (se 3 (by rfl) ⟨2507153, by rfl⟩ : syracuseStep 13371485 = 5014307) B5014307
theorem B35657293 : Blo 2029435 35657293 := bstep (se 3 (by rfl) ⟨6685742, by rfl⟩ : syracuseStep 35657293 = 13371485) B13371485
theorem B47543057 : Blo 2029435 47543057 := bstep (se 2 (by rfl) ⟨17828646, by rfl⟩ : syracuseStep 47543057 = 35657293) B35657293
theorem B31695371 : Blo 2029435 31695371 := bstep (se 1 (by rfl) ⟨23771528, by rfl⟩ : syracuseStep 31695371 = 47543057) B47543057
theorem B21130247 : Blo 2029435 21130247 := bstep (se 1 (by rfl) ⟨15847685, by rfl⟩ : syracuseStep 21130247 = 31695371) B31695371
theorem B56347325 : Blo 2029435 56347325 := bstep (se 3 (by rfl) ⟨10565123, by rfl⟩ : syracuseStep 56347325 = 21130247) B21130247
theorem B37564883 : Blo 2029435 37564883 := bstep (se 1 (by rfl) ⟨28173662, by rfl⟩ : syracuseStep 37564883 = 56347325) B56347325
theorem B25043255 : Blo 2029435 25043255 := bstep (se 1 (by rfl) ⟨18782441, by rfl⟩ : syracuseStep 25043255 = 37564883) B37564883
theorem B16695503 : Blo 2029435 16695503 := bstep (se 1 (by rfl) ⟨12521627, by rfl⟩ : syracuseStep 16695503 = 25043255) B25043255
theorem B11130335 : Blo 2029435 11130335 := bstep (se 1 (by rfl) ⟨8347751, by rfl⟩ : syracuseStep 11130335 = 16695503) B16695503
theorem B7420223 : Blo 2029435 7420223 := bstep (se 1 (by rfl) ⟨5565167, by rfl⟩ : syracuseStep 7420223 = 11130335) B11130335
theorem B4946815 : Blo 2029435 4946815 := bstep (se 1 (by rfl) ⟨3710111, by rfl⟩ : syracuseStep 4946815 = 7420223) B7420223
theorem B6595753 : Blo 2029435 6595753 := bstep (se 2 (by rfl) ⟨2473407, by rfl⟩ : syracuseStep 6595753 = 4946815) B4946815
theorem B8794337 : Blo 2029435 8794337 := bstep (se 2 (by rfl) ⟨3297876, by rfl⟩ : syracuseStep 8794337 = 6595753) B6595753
theorem B93806261 : Blo 2029435 93806261 := bstep (se 5 (by rfl) ⟨4397168, by rfl⟩ : syracuseStep 93806261 = 8794337) B8794337
theorem B62537507 : Blo 2029435 62537507 := bstep (se 1 (by rfl) ⟨46903130, by rfl⟩ : syracuseStep 62537507 = 93806261) B93806261
theorem B41691671 : Blo 2029435 41691671 := bstep (se 1 (by rfl) ⟨31268753, by rfl⟩ : syracuseStep 41691671 = 62537507) B62537507
theorem B27794447 : Blo 2029435 27794447 := bstep (se 1 (by rfl) ⟨20845835, by rfl⟩ : syracuseStep 27794447 = 41691671) B41691671
theorem B18529631 : Blo 2029435 18529631 := bstep (se 1 (by rfl) ⟨13897223, by rfl⟩ : syracuseStep 18529631 = 27794447) B27794447
theorem B12353087 : Blo 2029435 12353087 := bstep (se 1 (by rfl) ⟨9264815, by rfl⟩ : syracuseStep 12353087 = 18529631) B18529631
theorem B32941565 : Blo 2029435 32941565 := bstep (se 3 (by rfl) ⟨6176543, by rfl⟩ : syracuseStep 32941565 = 12353087) B12353087
theorem B21961043 : Blo 2029435 21961043 := bstep (se 1 (by rfl) ⟨16470782, by rfl⟩ : syracuseStep 21961043 = 32941565) B32941565
theorem B14640695 : Blo 2029435 14640695 := bstep (se 1 (by rfl) ⟨10980521, by rfl⟩ : syracuseStep 14640695 = 21961043) B21961043
theorem B9760463 : Blo 2029435 9760463 := bstep (se 1 (by rfl) ⟨7320347, by rfl⟩ : syracuseStep 9760463 = 14640695) B14640695
theorem B6506975 : Blo 2029435 6506975 := bstep (se 1 (by rfl) ⟨4880231, by rfl⟩ : syracuseStep 6506975 = 9760463) B9760463
theorem B4337983 : Blo 2029435 4337983 := bstep (se 1 (by rfl) ⟨3253487, by rfl⟩ : syracuseStep 4337983 = 6506975) B6506975
theorem B5783977 : Blo 2029435 5783977 := bstep (se 2 (by rfl) ⟨2168991, by rfl⟩ : syracuseStep 5783977 = 4337983) B4337983
theorem B7711969 : Blo 2029435 7711969 := bstep (se 2 (by rfl) ⟨2891988, by rfl⟩ : syracuseStep 7711969 = 5783977) B5783977
theorem B10282625 : Blo 2029435 10282625 := bstep (se 2 (by rfl) ⟨3855984, by rfl⟩ : syracuseStep 10282625 = 7711969) B7711969
theorem B6855083 : Blo 2029435 6855083 := bstep (se 1 (by rfl) ⟨5141312, by rfl⟩ : syracuseStep 6855083 = 10282625) B10282625
theorem B4570055 : Blo 2029435 4570055 := bstep (se 1 (by rfl) ⟨3427541, by rfl⟩ : syracuseStep 4570055 = 6855083) B6855083
theorem B3046703 : Blo 2029435 3046703 := bstep (se 1 (by rfl) ⟨2285027, by rfl⟩ : syracuseStep 3046703 = 4570055) B4570055
theorem B2031135 : Blo 2029435 2031135 := bstep (se 1 (by rfl) ⟨1523351, by rfl⟩ : syracuseStep 2031135 = 3046703) B3046703
theorem B3046709 : Blo 2029435 3046709 := bbase (se 5 (by rfl) ⟨142814, by rfl⟩ : syracuseStep 3046709 = 285629) (by norm_num)
theorem B2031139 : Blo 2029435 2031139 := bstep (se 1 (by rfl) ⟨1523354, by rfl⟩ : syracuseStep 2031139 = 3046709) B3046709
theorem B5141333 : Blo 2029435 5141333 := bbase (se 9 (by rfl) ⟨15062, by rfl⟩ : syracuseStep 5141333 = 30125) (by norm_num)
theorem B3427555 : Blo 2029435 3427555 := bstep (se 1 (by rfl) ⟨2570666, by rfl⟩ : syracuseStep 3427555 = 5141333) B5141333
theorem B4570073 : Blo 2029435 4570073 := bstep (se 2 (by rfl) ⟨1713777, by rfl⟩ : syracuseStep 4570073 = 3427555) B3427555
theorem B3046715 : Blo 2029435 3046715 := bstep (se 1 (by rfl) ⟨2285036, by rfl⟩ : syracuseStep 3046715 = 4570073) B4570073
theorem B2031143 : Blo 2029435 2031143 := bstep (se 1 (by rfl) ⟨1523357, by rfl⟩ : syracuseStep 2031143 = 3046715) B3046715
theorem B2285041 : Blo 2029435 2285041 := bbase (se 2 (by rfl) ⟨856890, by rfl⟩ : syracuseStep 2285041 = 1713781) (by norm_num)
theorem B3046721 : Blo 2029435 3046721 := bstep (se 2 (by rfl) ⟨1142520, by rfl⟩ : syracuseStep 3046721 = 2285041) B2285041
theorem B2031147 : Blo 2029435 2031147 := bstep (se 1 (by rfl) ⟨1523360, by rfl⟩ : syracuseStep 2031147 = 3046721) B3046721
theorem B4759717 : Blo 2029435 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B6346289 : Blo 2029435 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B4230859 : Blo 2029435 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B5641145 : Blo 2029435 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B3760763 : Blo 2029435 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B10028701 : Blo 2029435 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B13371601 : Blo 2029435 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B17828801 : Blo 2029435 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B11885867 : Blo 2029435 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B7923911 : Blo 2029435 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B21130429 : Blo 2029435 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B28173905 : Blo 2029435 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B18782603 : Blo 2029435 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B12521735 : Blo 2029435 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B8347823 : Blo 2029435 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B5565215 : Blo 2029435 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B3710143 : Blo 2029435 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B19787429 : Blo 2029435 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B13191619 : Blo 2029435 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B17588825 : Blo 2029435 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B11725883 : Blo 2029435 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B7817255 : Blo 2029435 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B5211503 : Blo 2029435 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B3474335 : Blo 2029435 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B2316223 : Blo 2029435 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B3088297 : Blo 2029435 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B4117729 : Blo 2029435 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B5490305 : Blo 2029435 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B3660203 : Blo 2029435 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B2440135 : Blo 2029435 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B13014053 : Blo 2029435 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B8676035 : Blo 2029435 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B5784023 : Blo 2029435 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B3856015 : Blo 2029435 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B5141353 : Blo 2029435 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B6855137 : Blo 2029435 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B4570091 : Blo 2029435 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B3046727 : Blo 2029435 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B2031151 : Blo 2029435 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B3046733 : Blo 2029435 3046733 := bbase (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) (by norm_num)
theorem B2031155 : Blo 2029435 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B4570109 : Blo 2029435 4570109 := bbase (se 3 (by rfl) ⟨856895, by rfl⟩ : syracuseStep 4570109 = 1713791) (by norm_num)
theorem B3046739 : Blo 2029435 3046739 := bstep (se 1 (by rfl) ⟨2285054, by rfl⟩ : syracuseStep 3046739 = 4570109) B4570109
theorem B2031159 : Blo 2029435 2031159 := bstep (se 1 (by rfl) ⟨1523369, by rfl⟩ : syracuseStep 2031159 = 3046739) B3046739
theorem B3427589 : Blo 2029435 3427589 := bbase (se 4 (by rfl) ⟨321336, by rfl⟩ : syracuseStep 3427589 = 642673) (by norm_num)
theorem B2285059 : Blo 2029435 2285059 := bstep (se 1 (by rfl) ⟨1713794, by rfl⟩ : syracuseStep 2285059 = 3427589) B3427589
theorem B3046745 : Blo 2029435 3046745 := bstep (se 2 (by rfl) ⟨1142529, by rfl⟩ : syracuseStep 3046745 = 2285059) B2285059
theorem B2031163 : Blo 2029435 2031163 := bstep (se 1 (by rfl) ⟨1523372, by rfl⟩ : syracuseStep 2031163 = 3046745) B3046745
theorem B15424181 : Blo 2029435 15424181 := bbase (se 5 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 15424181 = 1446017) (by norm_num)
theorem B10282787 : Blo 2029435 10282787 := bstep (se 1 (by rfl) ⟨7712090, by rfl⟩ : syracuseStep 10282787 = 15424181) B15424181
theorem B6855191 : Blo 2029435 6855191 := bstep (se 1 (by rfl) ⟨5141393, by rfl⟩ : syracuseStep 6855191 = 10282787) B10282787
theorem B4570127 : Blo 2029435 4570127 := bstep (se 1 (by rfl) ⟨3427595, by rfl⟩ : syracuseStep 4570127 = 6855191) B6855191
theorem B3046751 : Blo 2029435 3046751 := bstep (se 1 (by rfl) ⟨2285063, by rfl⟩ : syracuseStep 3046751 = 4570127) B4570127
theorem B2031167 : Blo 2029435 2031167 := bstep (se 1 (by rfl) ⟨1523375, by rfl⟩ : syracuseStep 2031167 = 3046751) B3046751
theorem B3046757 : Blo 2029435 3046757 := bbase (se 4 (by rfl) ⟨285633, by rfl⟩ : syracuseStep 3046757 = 571267) (by norm_num)
theorem B2031171 : Blo 2029435 2031171 := bstep (se 1 (by rfl) ⟨1523378, by rfl⟩ : syracuseStep 2031171 = 3046757) B3046757
theorem B3856061 : Blo 2029435 3856061 := bbase (se 3 (by rfl) ⟨723011, by rfl⟩ : syracuseStep 3856061 = 1446023) (by norm_num)
theorem B2570707 : Blo 2029435 2570707 := bstep (se 1 (by rfl) ⟨1928030, by rfl⟩ : syracuseStep 2570707 = 3856061) B3856061
theorem B3427609 : Blo 2029435 3427609 := bstep (se 2 (by rfl) ⟨1285353, by rfl⟩ : syracuseStep 3427609 = 2570707) B2570707
theorem B4570145 : Blo 2029435 4570145 := bstep (se 2 (by rfl) ⟨1713804, by rfl⟩ : syracuseStep 4570145 = 3427609) B3427609
theorem B3046763 : Blo 2029435 3046763 := bstep (se 1 (by rfl) ⟨2285072, by rfl⟩ : syracuseStep 3046763 = 4570145) B4570145
theorem B2031175 : Blo 2029435 2031175 := bstep (se 1 (by rfl) ⟨1523381, by rfl⟩ : syracuseStep 2031175 = 3046763) B3046763
theorem B2285077 : Blo 2029435 2285077 := bbase (se 6 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 2285077 = 107113) (by norm_num)
theorem B3046769 : Blo 2029435 3046769 := bstep (se 2 (by rfl) ⟨1142538, by rfl⟩ : syracuseStep 3046769 = 2285077) B2285077
theorem B2031179 : Blo 2029435 2031179 := bstep (se 1 (by rfl) ⟨1523384, by rfl⟩ : syracuseStep 2031179 = 3046769) B3046769
theorem B2570717 : Blo 2029435 2570717 := bbase (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) (by norm_num)
theorem B6855245 : Blo 2029435 6855245 := bstep (se 3 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 6855245 = 2570717) B2570717
theorem B4570163 : Blo 2029435 4570163 := bstep (se 1 (by rfl) ⟨3427622, by rfl⟩ : syracuseStep 4570163 = 6855245) B6855245
theorem B3046775 : Blo 2029435 3046775 := bstep (se 1 (by rfl) ⟨2285081, by rfl⟩ : syracuseStep 3046775 = 4570163) B4570163
theorem B2031183 : Blo 2029435 2031183 := bstep (se 1 (by rfl) ⟨1523387, by rfl⟩ : syracuseStep 2031183 = 3046775) B3046775
theorem B3046781 : Blo 2029435 3046781 := bbase (se 3 (by rfl) ⟨571271, by rfl⟩ : syracuseStep 3046781 = 1142543) (by norm_num)
theorem B2031187 : Blo 2029435 2031187 := bstep (se 1 (by rfl) ⟨1523390, by rfl⟩ : syracuseStep 2031187 = 3046781) B3046781
theorem B4570181 : Blo 2029435 4570181 := bbase (se 4 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 4570181 = 856909) (by norm_num)
theorem B3046787 : Blo 2029435 3046787 := bstep (se 1 (by rfl) ⟨2285090, by rfl⟩ : syracuseStep 3046787 = 4570181) B4570181
theorem B2031191 : Blo 2029435 2031191 := bstep (se 1 (by rfl) ⟨1523393, by rfl⟩ : syracuseStep 2031191 = 3046787) B3046787
theorem B5784149 : Blo 2029435 5784149 := bbase (se 8 (by rfl) ⟨33891, by rfl⟩ : syracuseStep 5784149 = 67783) (by norm_num)
theorem B3856099 : Blo 2029435 3856099 := bstep (se 1 (by rfl) ⟨2892074, by rfl⟩ : syracuseStep 3856099 = 5784149) B5784149
theorem B5141465 : Blo 2029435 5141465 := bstep (se 2 (by rfl) ⟨1928049, by rfl⟩ : syracuseStep 5141465 = 3856099) B3856099
theorem B3427643 : Blo 2029435 3427643 := bstep (se 1 (by rfl) ⟨2570732, by rfl⟩ : syracuseStep 3427643 = 5141465) B5141465
theorem B2285095 : Blo 2029435 2285095 := bstep (se 1 (by rfl) ⟨1713821, by rfl⟩ : syracuseStep 2285095 = 3427643) B3427643
theorem B3046793 : Blo 2029435 3046793 := bstep (se 2 (by rfl) ⟨1142547, by rfl⟩ : syracuseStep 3046793 = 2285095) B2285095
theorem B2031195 : Blo 2029435 2031195 := bstep (se 1 (by rfl) ⟨1523396, by rfl⟩ : syracuseStep 2031195 = 3046793) B3046793
theorem B10282949 : Blo 2029435 10282949 := bbase (se 4 (by rfl) ⟨964026, by rfl⟩ : syracuseStep 10282949 = 1928053) (by norm_num)
theorem B6855299 : Blo 2029435 6855299 := bstep (se 1 (by rfl) ⟨5141474, by rfl⟩ : syracuseStep 6855299 = 10282949) B10282949
theorem B4570199 : Blo 2029435 4570199 := bstep (se 1 (by rfl) ⟨3427649, by rfl⟩ : syracuseStep 4570199 = 6855299) B6855299
theorem B3046799 : Blo 2029435 3046799 := bstep (se 1 (by rfl) ⟨2285099, by rfl⟩ : syracuseStep 3046799 = 4570199) B4570199
theorem B2031199 : Blo 2029435 2031199 := bstep (se 1 (by rfl) ⟨1523399, by rfl⟩ : syracuseStep 2031199 = 3046799) B3046799
theorem B3046805 : Blo 2029435 3046805 := bbase (se 6 (by rfl) ⟨71409, by rfl⟩ : syracuseStep 3046805 = 142819) (by norm_num)
theorem B2031203 : Blo 2029435 2031203 := bstep (se 1 (by rfl) ⟨1523402, by rfl⟩ : syracuseStep 2031203 = 3046805) B3046805
theorem B4880405 : Blo 2029435 4880405 := bbase (se 6 (by rfl) ⟨114384, by rfl⟩ : syracuseStep 4880405 = 228769) (by norm_num)
theorem B3253603 : Blo 2029435 3253603 := bstep (se 1 (by rfl) ⟨2440202, by rfl⟩ : syracuseStep 3253603 = 4880405) B4880405
theorem B4338137 : Blo 2029435 4338137 := bstep (se 2 (by rfl) ⟨1626801, by rfl⟩ : syracuseStep 4338137 = 3253603) B3253603
theorem B11568365 : Blo 2029435 11568365 := bstep (se 3 (by rfl) ⟨2169068, by rfl⟩ : syracuseStep 11568365 = 4338137) B4338137
theorem B7712243 : Blo 2029435 7712243 := bstep (se 1 (by rfl) ⟨5784182, by rfl⟩ : syracuseStep 7712243 = 11568365) B11568365
theorem B5141495 : Blo 2029435 5141495 := bstep (se 1 (by rfl) ⟨3856121, by rfl⟩ : syracuseStep 5141495 = 7712243) B7712243
theorem B3427663 : Blo 2029435 3427663 := bstep (se 1 (by rfl) ⟨2570747, by rfl⟩ : syracuseStep 3427663 = 5141495) B5141495
theorem B4570217 : Blo 2029435 4570217 := bstep (se 2 (by rfl) ⟨1713831, by rfl⟩ : syracuseStep 4570217 = 3427663) B3427663
theorem B3046811 : Blo 2029435 3046811 := bstep (se 1 (by rfl) ⟨2285108, by rfl⟩ : syracuseStep 3046811 = 4570217) B4570217
theorem B2031207 : Blo 2029435 2031207 := bstep (se 1 (by rfl) ⟨1523405, by rfl⟩ : syracuseStep 2031207 = 3046811) B3046811
theorem B2285113 : Blo 2029435 2285113 := bbase (se 2 (by rfl) ⟨856917, by rfl⟩ : syracuseStep 2285113 = 1713835) (by norm_num)
theorem B3046817 : Blo 2029435 3046817 := bstep (se 2 (by rfl) ⟨1142556, by rfl⟩ : syracuseStep 3046817 = 2285113) B2285113
theorem B2031211 : Blo 2029435 2031211 := bstep (se 1 (by rfl) ⟨1523408, by rfl⟩ : syracuseStep 2031211 = 3046817) B3046817
theorem B2169077 : Blo 2029435 2169077 := bbase (se 5 (by rfl) ⟨101675, by rfl⟩ : syracuseStep 2169077 = 203351) (by norm_num)
theorem B5784205 : Blo 2029435 5784205 := bstep (se 3 (by rfl) ⟨1084538, by rfl⟩ : syracuseStep 5784205 = 2169077) B2169077
theorem B7712273 : Blo 2029435 7712273 := bstep (se 2 (by rfl) ⟨2892102, by rfl⟩ : syracuseStep 7712273 = 5784205) B5784205
theorem B5141515 : Blo 2029435 5141515 := bstep (se 1 (by rfl) ⟨3856136, by rfl⟩ : syracuseStep 5141515 = 7712273) B7712273
theorem B6855353 : Blo 2029435 6855353 := bstep (se 2 (by rfl) ⟨2570757, by rfl⟩ : syracuseStep 6855353 = 5141515) B5141515
theorem B4570235 : Blo 2029435 4570235 := bstep (se 1 (by rfl) ⟨3427676, by rfl⟩ : syracuseStep 4570235 = 6855353) B6855353
theorem B3046823 : Blo 2029435 3046823 := bstep (se 1 (by rfl) ⟨2285117, by rfl⟩ : syracuseStep 3046823 = 4570235) B4570235
theorem B2031215 : Blo 2029435 2031215 := bstep (se 1 (by rfl) ⟨1523411, by rfl⟩ : syracuseStep 2031215 = 3046823) B3046823
theorem B3046829 : Blo 2029435 3046829 := bbase (se 3 (by rfl) ⟨571280, by rfl⟩ : syracuseStep 3046829 = 1142561) (by norm_num)
theorem B2031219 : Blo 2029435 2031219 := bstep (se 1 (by rfl) ⟨1523414, by rfl⟩ : syracuseStep 2031219 = 3046829) B3046829
theorem B4570253 : Blo 2029435 4570253 := bbase (se 3 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 4570253 = 1713845) (by norm_num)
theorem B3046835 : Blo 2029435 3046835 := bstep (se 1 (by rfl) ⟨2285126, by rfl⟩ : syracuseStep 3046835 = 4570253) B4570253
theorem B2031223 : Blo 2029435 2031223 := bstep (se 1 (by rfl) ⟨1523417, by rfl⟩ : syracuseStep 2031223 = 3046835) B3046835
theorem B2570773 : Blo 2029435 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B3427697 : Blo 2029435 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B2285131 : Blo 2029435 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B3046841 : Blo 2029435 3046841 := bstep (se 2 (by rfl) ⟨1142565, by rfl⟩ : syracuseStep 3046841 = 2285131) B2285131
theorem B2031227 : Blo 2029435 2031227 := bstep (se 1 (by rfl) ⟨1523420, by rfl⟩ : syracuseStep 2031227 = 3046841) B3046841
theorem B13897877 : Blo 2029435 13897877 := bbase (se 6 (by rfl) ⟨325731, by rfl⟩ : syracuseStep 13897877 = 651463) (by norm_num)
theorem B37061005 : Blo 2029435 37061005 := bstep (se 3 (by rfl) ⟨6948938, by rfl⟩ : syracuseStep 37061005 = 13897877) B13897877
theorem B49414673 : Blo 2029435 49414673 := bstep (se 2 (by rfl) ⟨18530502, by rfl⟩ : syracuseStep 49414673 = 37061005) B37061005
theorem B32943115 : Blo 2029435 32943115 := bstep (se 1 (by rfl) ⟨24707336, by rfl⟩ : syracuseStep 32943115 = 49414673) B49414673
theorem B43924153 : Blo 2029435 43924153 := bstep (se 2 (by rfl) ⟨16471557, by rfl⟩ : syracuseStep 43924153 = 32943115) B32943115
theorem B58565537 : Blo 2029435 58565537 := bstep (se 2 (by rfl) ⟨21962076, by rfl⟩ : syracuseStep 58565537 = 43924153) B43924153
theorem B39043691 : Blo 2029435 39043691 := bstep (se 1 (by rfl) ⟨29282768, by rfl⟩ : syracuseStep 39043691 = 58565537) B58565537
theorem B26029127 : Blo 2029435 26029127 := bstep (se 1 (by rfl) ⟨19521845, by rfl⟩ : syracuseStep 26029127 = 39043691) B39043691
theorem B17352751 : Blo 2029435 17352751 := bstep (se 1 (by rfl) ⟨13014563, by rfl⟩ : syracuseStep 17352751 = 26029127) B26029127
theorem B23137001 : Blo 2029435 23137001 := bstep (se 2 (by rfl) ⟨8676375, by rfl⟩ : syracuseStep 23137001 = 17352751) B17352751
theorem B15424667 : Blo 2029435 15424667 := bstep (se 1 (by rfl) ⟨11568500, by rfl⟩ : syracuseStep 15424667 = 23137001) B23137001
theorem B10283111 : Blo 2029435 10283111 := bstep (se 1 (by rfl) ⟨7712333, by rfl⟩ : syracuseStep 10283111 = 15424667) B15424667
theorem B6855407 : Blo 2029435 6855407 := bstep (se 1 (by rfl) ⟨5141555, by rfl⟩ : syracuseStep 6855407 = 10283111) B10283111
theorem B4570271 : Blo 2029435 4570271 := bstep (se 1 (by rfl) ⟨3427703, by rfl⟩ : syracuseStep 4570271 = 6855407) B6855407
theorem B3046847 : Blo 2029435 3046847 := bstep (se 1 (by rfl) ⟨2285135, by rfl⟩ : syracuseStep 3046847 = 4570271) B4570271
theorem B2031231 : Blo 2029435 2031231 := bstep (se 1 (by rfl) ⟨1523423, by rfl⟩ : syracuseStep 2031231 = 3046847) B3046847
theorem B3046853 : Blo 2029435 3046853 := bbase (se 4 (by rfl) ⟨285642, by rfl⟩ : syracuseStep 3046853 = 571285) (by norm_num)
theorem B2031235 : Blo 2029435 2031235 := bstep (se 1 (by rfl) ⟨1523426, by rfl⟩ : syracuseStep 2031235 = 3046853) B3046853
theorem B3427717 : Blo 2029435 3427717 := bbase (se 4 (by rfl) ⟨321348, by rfl⟩ : syracuseStep 3427717 = 642697) (by norm_num)
theorem B4570289 : Blo 2029435 4570289 := bstep (se 2 (by rfl) ⟨1713858, by rfl⟩ : syracuseStep 4570289 = 3427717) B3427717
theorem B3046859 : Blo 2029435 3046859 := bstep (se 1 (by rfl) ⟨2285144, by rfl⟩ : syracuseStep 3046859 = 4570289) B4570289
theorem B2031239 : Blo 2029435 2031239 := bstep (se 1 (by rfl) ⟨1523429, by rfl⟩ : syracuseStep 2031239 = 3046859) B3046859
theorem B2285149 : Blo 2029435 2285149 := bbase (se 3 (by rfl) ⟨428465, by rfl⟩ : syracuseStep 2285149 = 856931) (by norm_num)
theorem B3046865 : Blo 2029435 3046865 := bstep (se 2 (by rfl) ⟨1142574, by rfl⟩ : syracuseStep 3046865 = 2285149) B2285149
theorem B2031243 : Blo 2029435 2031243 := bstep (se 1 (by rfl) ⟨1523432, by rfl⟩ : syracuseStep 2031243 = 3046865) B3046865
theorem B6855461 : Blo 2029435 6855461 := bbase (se 4 (by rfl) ⟨642699, by rfl⟩ : syracuseStep 6855461 = 1285399) (by norm_num)
theorem B4570307 : Blo 2029435 4570307 := bstep (se 1 (by rfl) ⟨3427730, by rfl⟩ : syracuseStep 4570307 = 6855461) B6855461
theorem B3046871 : Blo 2029435 3046871 := bstep (se 1 (by rfl) ⟨2285153, by rfl⟩ : syracuseStep 3046871 = 4570307) B4570307
theorem B2031247 : Blo 2029435 2031247 := bstep (se 1 (by rfl) ⟨1523435, by rfl⟩ : syracuseStep 2031247 = 3046871) B3046871
theorem B3046877 : Blo 2029435 3046877 := bbase (se 3 (by rfl) ⟨571289, by rfl⟩ : syracuseStep 3046877 = 1142579) (by norm_num)
theorem B2031251 : Blo 2029435 2031251 := bstep (se 1 (by rfl) ⟨1523438, by rfl⟩ : syracuseStep 2031251 = 3046877) B3046877
theorem B4570325 : Blo 2029435 4570325 := bbase (se 7 (by rfl) ⟨53558, by rfl⟩ : syracuseStep 4570325 = 107117) (by norm_num)
theorem B3046883 : Blo 2029435 3046883 := bstep (se 1 (by rfl) ⟨2285162, by rfl⟩ : syracuseStep 3046883 = 4570325) B4570325
theorem B2031255 : Blo 2029435 2031255 := bstep (se 1 (by rfl) ⟨1523441, by rfl⟩ : syracuseStep 2031255 = 3046883) B3046883
theorem B2440265 : Blo 2029435 2440265 := bbase (se 2 (by rfl) ⟨915099, by rfl⟩ : syracuseStep 2440265 = 1830199) (by norm_num)
theorem B6507373 : Blo 2029435 6507373 := bstep (se 3 (by rfl) ⟨1220132, by rfl⟩ : syracuseStep 6507373 = 2440265) B2440265
theorem B8676497 : Blo 2029435 8676497 := bstep (se 2 (by rfl) ⟨3253686, by rfl⟩ : syracuseStep 8676497 = 6507373) B6507373
theorem B5784331 : Blo 2029435 5784331 := bstep (se 1 (by rfl) ⟨4338248, by rfl⟩ : syracuseStep 5784331 = 8676497) B8676497
theorem B7712441 : Blo 2029435 7712441 := bstep (se 2 (by rfl) ⟨2892165, by rfl⟩ : syracuseStep 7712441 = 5784331) B5784331
theorem B5141627 : Blo 2029435 5141627 := bstep (se 1 (by rfl) ⟨3856220, by rfl⟩ : syracuseStep 5141627 = 7712441) B7712441
theorem B3427751 : Blo 2029435 3427751 := bstep (se 1 (by rfl) ⟨2570813, by rfl⟩ : syracuseStep 3427751 = 5141627) B5141627
theorem B2285167 : Blo 2029435 2285167 := bstep (se 1 (by rfl) ⟨1713875, by rfl⟩ : syracuseStep 2285167 = 3427751) B3427751
theorem B3046889 : Blo 2029435 3046889 := bstep (se 2 (by rfl) ⟨1142583, by rfl⟩ : syracuseStep 3046889 = 2285167) B2285167
theorem B2031259 : Blo 2029435 2031259 := bstep (se 1 (by rfl) ⟨1523444, by rfl⟩ : syracuseStep 2031259 = 3046889) B3046889
theorem B9761077 : Blo 2029435 9761077 := bbase (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) (by norm_num)
theorem B13014769 : Blo 2029435 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B17353025 : Blo 2029435 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B11568683 : Blo 2029435 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B7712455 : Blo 2029435 7712455 := bstep (se 1 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 7712455 = 11568683) B11568683
theorem B10283273 : Blo 2029435 10283273 := bstep (se 2 (by rfl) ⟨3856227, by rfl⟩ : syracuseStep 10283273 = 7712455) B7712455
theorem B6855515 : Blo 2029435 6855515 := bstep (se 1 (by rfl) ⟨5141636, by rfl⟩ : syracuseStep 6855515 = 10283273) B10283273
theorem B4570343 : Blo 2029435 4570343 := bstep (se 1 (by rfl) ⟨3427757, by rfl⟩ : syracuseStep 4570343 = 6855515) B6855515
theorem B3046895 : Blo 2029435 3046895 := bstep (se 1 (by rfl) ⟨2285171, by rfl⟩ : syracuseStep 3046895 = 4570343) B4570343
theorem B2031263 : Blo 2029435 2031263 := bstep (se 1 (by rfl) ⟨1523447, by rfl⟩ : syracuseStep 2031263 = 3046895) B3046895
theorem B3046901 : Blo 2029435 3046901 := bbase (se 5 (by rfl) ⟨142823, by rfl⟩ : syracuseStep 3046901 = 285647) (by norm_num)
theorem B2031267 : Blo 2029435 2031267 := bstep (se 1 (by rfl) ⟨1523450, by rfl⟩ : syracuseStep 2031267 = 3046901) B3046901
theorem B2169137 : Blo 2029435 2169137 := bbase (se 2 (by rfl) ⟨813426, by rfl⟩ : syracuseStep 2169137 = 1626853) (by norm_num)
theorem B5784365 : Blo 2029435 5784365 := bstep (se 3 (by rfl) ⟨1084568, by rfl⟩ : syracuseStep 5784365 = 2169137) B2169137
theorem B3856243 : Blo 2029435 3856243 := bstep (se 1 (by rfl) ⟨2892182, by rfl⟩ : syracuseStep 3856243 = 5784365) B5784365
theorem B5141657 : Blo 2029435 5141657 := bstep (se 2 (by rfl) ⟨1928121, by rfl⟩ : syracuseStep 5141657 = 3856243) B3856243
theorem B3427771 : Blo 2029435 3427771 := bstep (se 1 (by rfl) ⟨2570828, by rfl⟩ : syracuseStep 3427771 = 5141657) B5141657
theorem B4570361 : Blo 2029435 4570361 := bstep (se 2 (by rfl) ⟨1713885, by rfl⟩ : syracuseStep 4570361 = 3427771) B3427771
theorem B3046907 : Blo 2029435 3046907 := bstep (se 1 (by rfl) ⟨2285180, by rfl⟩ : syracuseStep 3046907 = 4570361) B4570361
theorem B2031271 : Blo 2029435 2031271 := bstep (se 1 (by rfl) ⟨1523453, by rfl⟩ : syracuseStep 2031271 = 3046907) B3046907
theorem B2285185 : Blo 2029435 2285185 := bbase (se 2 (by rfl) ⟨856944, by rfl⟩ : syracuseStep 2285185 = 1713889) (by norm_num)
theorem B3046913 : Blo 2029435 3046913 := bstep (se 2 (by rfl) ⟨1142592, by rfl⟩ : syracuseStep 3046913 = 2285185) B2285185
theorem B2031275 : Blo 2029435 2031275 := bstep (se 1 (by rfl) ⟨1523456, by rfl⟩ : syracuseStep 2031275 = 3046913) B3046913
theorem B5141677 : Blo 2029435 5141677 := bbase (se 3 (by rfl) ⟨964064, by rfl⟩ : syracuseStep 5141677 = 1928129) (by norm_num)
theorem B6855569 : Blo 2029435 6855569 := bstep (se 2 (by rfl) ⟨2570838, by rfl⟩ : syracuseStep 6855569 = 5141677) B5141677
theorem B4570379 : Blo 2029435 4570379 := bstep (se 1 (by rfl) ⟨3427784, by rfl⟩ : syracuseStep 4570379 = 6855569) B6855569
theorem B3046919 : Blo 2029435 3046919 := bstep (se 1 (by rfl) ⟨2285189, by rfl⟩ : syracuseStep 3046919 = 4570379) B4570379
theorem B2031279 : Blo 2029435 2031279 := bstep (se 1 (by rfl) ⟨1523459, by rfl⟩ : syracuseStep 2031279 = 3046919) B3046919
theorem B3046925 : Blo 2029435 3046925 := bbase (se 3 (by rfl) ⟨571298, by rfl⟩ : syracuseStep 3046925 = 1142597) (by norm_num)
theorem B2031283 : Blo 2029435 2031283 := bstep (se 1 (by rfl) ⟨1523462, by rfl⟩ : syracuseStep 2031283 = 3046925) B3046925
theorem B4570397 : Blo 2029435 4570397 := bbase (se 3 (by rfl) ⟨856949, by rfl⟩ : syracuseStep 4570397 = 1713899) (by norm_num)
theorem B3046931 : Blo 2029435 3046931 := bstep (se 1 (by rfl) ⟨2285198, by rfl⟩ : syracuseStep 3046931 = 4570397) B4570397
theorem B2031287 : Blo 2029435 2031287 := bstep (se 1 (by rfl) ⟨1523465, by rfl⟩ : syracuseStep 2031287 = 3046931) B3046931
theorem B3427805 : Blo 2029435 3427805 := bbase (se 3 (by rfl) ⟨642713, by rfl⟩ : syracuseStep 3427805 = 1285427) (by norm_num)
theorem B2285203 : Blo 2029435 2285203 := bstep (se 1 (by rfl) ⟨1713902, by rfl⟩ : syracuseStep 2285203 = 3427805) B3427805
theorem B3046937 : Blo 2029435 3046937 := bstep (se 2 (by rfl) ⟨1142601, by rfl⟩ : syracuseStep 3046937 = 2285203) B2285203
theorem B2031291 : Blo 2029435 2031291 := bstep (se 1 (by rfl) ⟨1523468, by rfl⟩ : syracuseStep 2031291 = 3046937) B3046937
theorem B5211869 : Blo 2029435 5211869 := bbase (se 3 (by rfl) ⟨977225, by rfl⟩ : syracuseStep 5211869 = 1954451) (by norm_num)
theorem B13898317 : Blo 2029435 13898317 := bstep (se 3 (by rfl) ⟨2605934, by rfl⟩ : syracuseStep 13898317 = 5211869) B5211869
theorem B18531089 : Blo 2029435 18531089 := bstep (se 2 (by rfl) ⟨6949158, by rfl⟩ : syracuseStep 18531089 = 13898317) B13898317
theorem B12354059 : Blo 2029435 12354059 := bstep (se 1 (by rfl) ⟨9265544, by rfl⟩ : syracuseStep 12354059 = 18531089) B18531089
theorem B32944157 : Blo 2029435 32944157 := bstep (se 3 (by rfl) ⟨6177029, by rfl⟩ : syracuseStep 32944157 = 12354059) B12354059
theorem B21962771 : Blo 2029435 21962771 := bstep (se 1 (by rfl) ⟨16472078, by rfl⟩ : syracuseStep 21962771 = 32944157) B32944157
theorem B14641847 : Blo 2029435 14641847 := bstep (se 1 (by rfl) ⟨10981385, by rfl⟩ : syracuseStep 14641847 = 21962771) B21962771
theorem B9761231 : Blo 2029435 9761231 := bstep (se 1 (by rfl) ⟨7320923, by rfl⟩ : syracuseStep 9761231 = 14641847) B14641847
theorem B6507487 : Blo 2029435 6507487 := bstep (se 1 (by rfl) ⟨4880615, by rfl⟩ : syracuseStep 6507487 = 9761231) B9761231
theorem B8676649 : Blo 2029435 8676649 := bstep (se 2 (by rfl) ⟨3253743, by rfl⟩ : syracuseStep 8676649 = 6507487) B6507487
theorem B11568865 : Blo 2029435 11568865 := bstep (se 2 (by rfl) ⟨4338324, by rfl⟩ : syracuseStep 11568865 = 8676649) B8676649
theorem B15425153 : Blo 2029435 15425153 := bstep (se 2 (by rfl) ⟨5784432, by rfl⟩ : syracuseStep 15425153 = 11568865) B11568865
theorem B10283435 : Blo 2029435 10283435 := bstep (se 1 (by rfl) ⟨7712576, by rfl⟩ : syracuseStep 10283435 = 15425153) B15425153
theorem B6855623 : Blo 2029435 6855623 := bstep (se 1 (by rfl) ⟨5141717, by rfl⟩ : syracuseStep 6855623 = 10283435) B10283435
theorem B4570415 : Blo 2029435 4570415 := bstep (se 1 (by rfl) ⟨3427811, by rfl⟩ : syracuseStep 4570415 = 6855623) B6855623
theorem B3046943 : Blo 2029435 3046943 := bstep (se 1 (by rfl) ⟨2285207, by rfl⟩ : syracuseStep 3046943 = 4570415) B4570415
theorem B2031295 : Blo 2029435 2031295 := bstep (se 1 (by rfl) ⟨1523471, by rfl⟩ : syracuseStep 2031295 = 3046943) B3046943
theorem B3046949 : Blo 2029435 3046949 := bbase (se 4 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 3046949 = 571303) (by norm_num)
theorem B2031299 : Blo 2029435 2031299 := bstep (se 1 (by rfl) ⟨1523474, by rfl⟩ : syracuseStep 2031299 = 3046949) B3046949
theorem B2570869 : Blo 2029435 2570869 := bbase (se 5 (by rfl) ⟨120509, by rfl⟩ : syracuseStep 2570869 = 241019) (by norm_num)
theorem B3427825 : Blo 2029435 3427825 := bstep (se 2 (by rfl) ⟨1285434, by rfl⟩ : syracuseStep 3427825 = 2570869) B2570869
theorem B4570433 : Blo 2029435 4570433 := bstep (se 2 (by rfl) ⟨1713912, by rfl⟩ : syracuseStep 4570433 = 3427825) B3427825
theorem B3046955 : Blo 2029435 3046955 := bstep (se 1 (by rfl) ⟨2285216, by rfl⟩ : syracuseStep 3046955 = 4570433) B4570433
theorem B2031303 : Blo 2029435 2031303 := bstep (se 1 (by rfl) ⟨1523477, by rfl⟩ : syracuseStep 2031303 = 3046955) B3046955
theorem B2285221 : Blo 2029435 2285221 := bbase (se 4 (by rfl) ⟨214239, by rfl⟩ : syracuseStep 2285221 = 428479) (by norm_num)
theorem B3046961 : Blo 2029435 3046961 := bstep (se 2 (by rfl) ⟨1142610, by rfl⟩ : syracuseStep 3046961 = 2285221) B2285221
theorem B2031307 : Blo 2029435 2031307 := bstep (se 1 (by rfl) ⟨1523480, by rfl⟩ : syracuseStep 2031307 = 3046961) B3046961
theorem B4947245 : Blo 2029435 4947245 := bbase (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) (by norm_num)
theorem B3298163 : Blo 2029435 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B8795101 : Blo 2029435 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B11726801 : Blo 2029435 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B7817867 : Blo 2029435 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B5211911 : Blo 2029435 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B13898429 : Blo 2029435 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B9265619 : Blo 2029435 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B6177079 : Blo 2029435 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B32944421 : Blo 2029435 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B21962947 : Blo 2029435 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B29283929 : Blo 2029435 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B19522619 : Blo 2029435 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B13015079 : Blo 2029435 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B8676719 : Blo 2029435 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B5784479 : Blo 2029435 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B3856319 : Blo 2029435 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B2570879 : Blo 2029435 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B6855677 : Blo 2029435 6855677 := bstep (se 3 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 6855677 = 2570879) B2570879
theorem B4570451 : Blo 2029435 4570451 := bstep (se 1 (by rfl) ⟨3427838, by rfl⟩ : syracuseStep 4570451 = 6855677) B6855677
theorem B3046967 : Blo 2029435 3046967 := bstep (se 1 (by rfl) ⟨2285225, by rfl⟩ : syracuseStep 3046967 = 4570451) B4570451
theorem B2031311 : Blo 2029435 2031311 := bstep (se 1 (by rfl) ⟨1523483, by rfl⟩ : syracuseStep 2031311 = 3046967) B3046967
theorem B3046973 : Blo 2029435 3046973 := bbase (se 3 (by rfl) ⟨571307, by rfl⟩ : syracuseStep 3046973 = 1142615) (by norm_num)
theorem B2031315 : Blo 2029435 2031315 := bstep (se 1 (by rfl) ⟨1523486, by rfl⟩ : syracuseStep 2031315 = 3046973) B3046973
theorem B4570469 : Blo 2029435 4570469 := bbase (se 4 (by rfl) ⟨428481, by rfl⟩ : syracuseStep 4570469 = 856963) (by norm_num)
theorem B3046979 : Blo 2029435 3046979 := bstep (se 1 (by rfl) ⟨2285234, by rfl⟩ : syracuseStep 3046979 = 4570469) B4570469
theorem B2031319 : Blo 2029435 2031319 := bstep (se 1 (by rfl) ⟨1523489, by rfl⟩ : syracuseStep 2031319 = 3046979) B3046979
theorem B5141789 : Blo 2029435 5141789 := bbase (se 3 (by rfl) ⟨964085, by rfl⟩ : syracuseStep 5141789 = 1928171) (by norm_num)
theorem B3427859 : Blo 2029435 3427859 := bstep (se 1 (by rfl) ⟨2570894, by rfl⟩ : syracuseStep 3427859 = 5141789) B5141789
theorem B2285239 : Blo 2029435 2285239 := bstep (se 1 (by rfl) ⟨1713929, by rfl⟩ : syracuseStep 2285239 = 3427859) B3427859
theorem B3046985 : Blo 2029435 3046985 := bstep (se 2 (by rfl) ⟨1142619, by rfl⟩ : syracuseStep 3046985 = 2285239) B2285239
theorem B2031323 : Blo 2029435 2031323 := bstep (se 1 (by rfl) ⟨1523492, by rfl⟩ : syracuseStep 2031323 = 3046985) B3046985
theorem B3856349 : Blo 2029435 3856349 := bbase (se 3 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 3856349 = 1446131) (by norm_num)
theorem B10283597 : Blo 2029435 10283597 := bstep (se 3 (by rfl) ⟨1928174, by rfl⟩ : syracuseStep 10283597 = 3856349) B3856349
theorem B6855731 : Blo 2029435 6855731 := bstep (se 1 (by rfl) ⟨5141798, by rfl⟩ : syracuseStep 6855731 = 10283597) B10283597
theorem B4570487 : Blo 2029435 4570487 := bstep (se 1 (by rfl) ⟨3427865, by rfl⟩ : syracuseStep 4570487 = 6855731) B6855731
theorem B3046991 : Blo 2029435 3046991 := bstep (se 1 (by rfl) ⟨2285243, by rfl⟩ : syracuseStep 3046991 = 4570487) B4570487
theorem B2031327 : Blo 2029435 2031327 := bstep (se 1 (by rfl) ⟨1523495, by rfl⟩ : syracuseStep 2031327 = 3046991) B3046991
theorem B3046997 : Blo 2029435 3046997 := bbase (se 8 (by rfl) ⟨17853, by rfl⟩ : syracuseStep 3046997 = 35707) (by norm_num)
theorem B2031331 : Blo 2029435 2031331 := bstep (se 1 (by rfl) ⟨1523498, by rfl⟩ : syracuseStep 2031331 = 3046997) B3046997
theorem B8676821 : Blo 2029435 8676821 := bbase (se 7 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 8676821 = 203363) (by norm_num)
theorem B5784547 : Blo 2029435 5784547 := bstep (se 1 (by rfl) ⟨4338410, by rfl⟩ : syracuseStep 5784547 = 8676821) B8676821
theorem B7712729 : Blo 2029435 7712729 := bstep (se 2 (by rfl) ⟨2892273, by rfl⟩ : syracuseStep 7712729 = 5784547) B5784547
theorem B5141819 : Blo 2029435 5141819 := bstep (se 1 (by rfl) ⟨3856364, by rfl⟩ : syracuseStep 5141819 = 7712729) B7712729
theorem B3427879 : Blo 2029435 3427879 := bstep (se 1 (by rfl) ⟨2570909, by rfl⟩ : syracuseStep 3427879 = 5141819) B5141819
theorem B4570505 : Blo 2029435 4570505 := bstep (se 2 (by rfl) ⟨1713939, by rfl⟩ : syracuseStep 4570505 = 3427879) B3427879
theorem B3047003 : Blo 2029435 3047003 := bstep (se 1 (by rfl) ⟨2285252, by rfl⟩ : syracuseStep 3047003 = 4570505) B4570505
theorem B2031335 : Blo 2029435 2031335 := bstep (se 1 (by rfl) ⟨1523501, by rfl⟩ : syracuseStep 2031335 = 3047003) B3047003
theorem B2285257 : Blo 2029435 2285257 := bbase (se 2 (by rfl) ⟨856971, by rfl⟩ : syracuseStep 2285257 = 1713943) (by norm_num)
theorem B3047009 : Blo 2029435 3047009 := bstep (se 2 (by rfl) ⟨1142628, by rfl⟩ : syracuseStep 3047009 = 2285257) B2285257
theorem B2031339 : Blo 2029435 2031339 := bstep (se 1 (by rfl) ⟨1523504, by rfl⟩ : syracuseStep 2031339 = 3047009) B3047009
theorem B9265765 : Blo 2029435 9265765 := bbase (se 4 (by rfl) ⟨868665, by rfl⟩ : syracuseStep 9265765 = 1737331) (by norm_num)
theorem B12354353 : Blo 2029435 12354353 := bstep (se 2 (by rfl) ⟨4632882, by rfl⟩ : syracuseStep 12354353 = 9265765) B9265765
theorem B8236235 : Blo 2029435 8236235 := bstep (se 1 (by rfl) ⟨6177176, by rfl⟩ : syracuseStep 8236235 = 12354353) B12354353
theorem B5490823 : Blo 2029435 5490823 := bstep (se 1 (by rfl) ⟨4118117, by rfl⟩ : syracuseStep 5490823 = 8236235) B8236235
theorem B7321097 : Blo 2029435 7321097 := bstep (se 2 (by rfl) ⟨2745411, by rfl⟩ : syracuseStep 7321097 = 5490823) B5490823
theorem B4880731 : Blo 2029435 4880731 := bstep (se 1 (by rfl) ⟨3660548, by rfl⟩ : syracuseStep 4880731 = 7321097) B7321097
theorem B6507641 : Blo 2029435 6507641 := bstep (se 2 (by rfl) ⟨2440365, by rfl⟩ : syracuseStep 6507641 = 4880731) B4880731
theorem B17353709 : Blo 2029435 17353709 := bstep (se 3 (by rfl) ⟨3253820, by rfl⟩ : syracuseStep 17353709 = 6507641) B6507641
theorem B11569139 : Blo 2029435 11569139 := bstep (se 1 (by rfl) ⟨8676854, by rfl⟩ : syracuseStep 11569139 = 17353709) B17353709
theorem B7712759 : Blo 2029435 7712759 := bstep (se 1 (by rfl) ⟨5784569, by rfl⟩ : syracuseStep 7712759 = 11569139) B11569139
theorem B5141839 : Blo 2029435 5141839 := bstep (se 1 (by rfl) ⟨3856379, by rfl⟩ : syracuseStep 5141839 = 7712759) B7712759
theorem B6855785 : Blo 2029435 6855785 := bstep (se 2 (by rfl) ⟨2570919, by rfl⟩ : syracuseStep 6855785 = 5141839) B5141839
theorem B4570523 : Blo 2029435 4570523 := bstep (se 1 (by rfl) ⟨3427892, by rfl⟩ : syracuseStep 4570523 = 6855785) B6855785
theorem B3047015 : Blo 2029435 3047015 := bstep (se 1 (by rfl) ⟨2285261, by rfl⟩ : syracuseStep 3047015 = 4570523) B4570523
theorem B2031343 : Blo 2029435 2031343 := bstep (se 1 (by rfl) ⟨1523507, by rfl⟩ : syracuseStep 2031343 = 3047015) B3047015
theorem B3047021 : Blo 2029435 3047021 := bbase (se 3 (by rfl) ⟨571316, by rfl⟩ : syracuseStep 3047021 = 1142633) (by norm_num)
theorem B2031347 : Blo 2029435 2031347 := bstep (se 1 (by rfl) ⟨1523510, by rfl⟩ : syracuseStep 2031347 = 3047021) B3047021
theorem B4570541 : Blo 2029435 4570541 := bbase (se 3 (by rfl) ⟨856976, by rfl⟩ : syracuseStep 4570541 = 1713953) (by norm_num)
theorem B3047027 : Blo 2029435 3047027 := bstep (se 1 (by rfl) ⟨2285270, by rfl⟩ : syracuseStep 3047027 = 4570541) B4570541
theorem B2031351 : Blo 2029435 2031351 := bstep (se 1 (by rfl) ⟨1523513, by rfl⟩ : syracuseStep 2031351 = 3047027) B3047027
theorem B2440381 : Blo 2029435 2440381 := bbase (se 3 (by rfl) ⟨457571, by rfl⟩ : syracuseStep 2440381 = 915143) (by norm_num)
theorem B3253841 : Blo 2029435 3253841 := bstep (se 2 (by rfl) ⟨1220190, by rfl⟩ : syracuseStep 3253841 = 2440381) B2440381
theorem B2169227 : Blo 2029435 2169227 := bstep (se 1 (by rfl) ⟨1626920, by rfl⟩ : syracuseStep 2169227 = 3253841) B3253841
theorem B5784605 : Blo 2029435 5784605 := bstep (se 3 (by rfl) ⟨1084613, by rfl⟩ : syracuseStep 5784605 = 2169227) B2169227
theorem B3856403 : Blo 2029435 3856403 := bstep (se 1 (by rfl) ⟨2892302, by rfl⟩ : syracuseStep 3856403 = 5784605) B5784605
theorem B2570935 : Blo 2029435 2570935 := bstep (se 1 (by rfl) ⟨1928201, by rfl⟩ : syracuseStep 2570935 = 3856403) B3856403
theorem B3427913 : Blo 2029435 3427913 := bstep (se 2 (by rfl) ⟨1285467, by rfl⟩ : syracuseStep 3427913 = 2570935) B2570935
theorem B2285275 : Blo 2029435 2285275 := bstep (se 1 (by rfl) ⟨1713956, by rfl⟩ : syracuseStep 2285275 = 3427913) B3427913
theorem B3047033 : Blo 2029435 3047033 := bstep (se 2 (by rfl) ⟨1142637, by rfl⟩ : syracuseStep 3047033 = 2285275) B2285275
theorem B2031355 : Blo 2029435 2031355 := bstep (se 1 (by rfl) ⟨1523516, by rfl⟩ : syracuseStep 2031355 = 3047033) B3047033
theorem B4397653 : Blo 2029435 4397653 := bbase (se 8 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 4397653 = 51535) (by norm_num)
theorem B5863537 : Blo 2029435 5863537 := bstep (se 2 (by rfl) ⟨2198826, by rfl⟩ : syracuseStep 5863537 = 4397653) B4397653
theorem B7818049 : Blo 2029435 7818049 := bstep (se 2 (by rfl) ⟨2931768, by rfl⟩ : syracuseStep 7818049 = 5863537) B5863537
theorem B10424065 : Blo 2029435 10424065 := bstep (se 2 (by rfl) ⟨3909024, by rfl⟩ : syracuseStep 10424065 = 7818049) B7818049
theorem B13898753 : Blo 2029435 13898753 := bstep (se 2 (by rfl) ⟨5212032, by rfl⟩ : syracuseStep 13898753 = 10424065) B10424065
theorem B9265835 : Blo 2029435 9265835 := bstep (se 1 (by rfl) ⟨6949376, by rfl⟩ : syracuseStep 9265835 = 13898753) B13898753
theorem B24708893 : Blo 2029435 24708893 := bstep (se 3 (by rfl) ⟨4632917, by rfl⟩ : syracuseStep 24708893 = 9265835) B9265835
theorem B65890381 : Blo 2029435 65890381 := bstep (se 3 (by rfl) ⟨12354446, by rfl⟩ : syracuseStep 65890381 = 24708893) B24708893
theorem B87853841 : Blo 2029435 87853841 := bstep (se 2 (by rfl) ⟨32945190, by rfl⟩ : syracuseStep 87853841 = 65890381) B65890381
theorem B58569227 : Blo 2029435 58569227 := bstep (se 1 (by rfl) ⟨43926920, by rfl⟩ : syracuseStep 58569227 = 87853841) B87853841
theorem B39046151 : Blo 2029435 39046151 := bstep (se 1 (by rfl) ⟨29284613, by rfl⟩ : syracuseStep 39046151 = 58569227) B58569227
theorem B26030767 : Blo 2029435 26030767 := bstep (se 1 (by rfl) ⟨19523075, by rfl⟩ : syracuseStep 26030767 = 39046151) B39046151
theorem B34707689 : Blo 2029435 34707689 := bstep (se 2 (by rfl) ⟨13015383, by rfl⟩ : syracuseStep 34707689 = 26030767) B26030767
theorem B23138459 : Blo 2029435 23138459 := bstep (se 1 (by rfl) ⟨17353844, by rfl⟩ : syracuseStep 23138459 = 34707689) B34707689
theorem B15425639 : Blo 2029435 15425639 := bstep (se 1 (by rfl) ⟨11569229, by rfl⟩ : syracuseStep 15425639 = 23138459) B23138459
theorem B10283759 : Blo 2029435 10283759 := bstep (se 1 (by rfl) ⟨7712819, by rfl⟩ : syracuseStep 10283759 = 15425639) B15425639
theorem B6855839 : Blo 2029435 6855839 := bstep (se 1 (by rfl) ⟨5141879, by rfl⟩ : syracuseStep 6855839 = 10283759) B10283759
theorem B4570559 : Blo 2029435 4570559 := bstep (se 1 (by rfl) ⟨3427919, by rfl⟩ : syracuseStep 4570559 = 6855839) B6855839
theorem B3047039 : Blo 2029435 3047039 := bstep (se 1 (by rfl) ⟨2285279, by rfl⟩ : syracuseStep 3047039 = 4570559) B4570559
theorem B2031359 : Blo 2029435 2031359 := bstep (se 1 (by rfl) ⟨1523519, by rfl⟩ : syracuseStep 2031359 = 3047039) B3047039
theorem B3047045 : Blo 2029435 3047045 := bbase (se 4 (by rfl) ⟨285660, by rfl⟩ : syracuseStep 3047045 = 571321) (by norm_num)
theorem B2031363 : Blo 2029435 2031363 := bstep (se 1 (by rfl) ⟨1523522, by rfl⟩ : syracuseStep 2031363 = 3047045) B3047045
theorem B3427933 : Blo 2029435 3427933 := bbase (se 3 (by rfl) ⟨642737, by rfl⟩ : syracuseStep 3427933 = 1285475) (by norm_num)
theorem B4570577 : Blo 2029435 4570577 := bstep (se 2 (by rfl) ⟨1713966, by rfl⟩ : syracuseStep 4570577 = 3427933) B3427933
theorem B3047051 : Blo 2029435 3047051 := bstep (se 1 (by rfl) ⟨2285288, by rfl⟩ : syracuseStep 3047051 = 4570577) B4570577
theorem B2031367 : Blo 2029435 2031367 := bstep (se 1 (by rfl) ⟨1523525, by rfl⟩ : syracuseStep 2031367 = 3047051) B3047051
theorem B2285293 : Blo 2029435 2285293 := bbase (se 3 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 2285293 = 856985) (by norm_num)
theorem B3047057 : Blo 2029435 3047057 := bstep (se 2 (by rfl) ⟨1142646, by rfl⟩ : syracuseStep 3047057 = 2285293) B2285293
theorem B2031371 : Blo 2029435 2031371 := bstep (se 1 (by rfl) ⟨1523528, by rfl⟩ : syracuseStep 2031371 = 3047057) B3047057
theorem B6855893 : Blo 2029435 6855893 := bbase (se 7 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 6855893 = 160685) (by norm_num)
theorem B4570595 : Blo 2029435 4570595 := bstep (se 1 (by rfl) ⟨3427946, by rfl⟩ : syracuseStep 4570595 = 6855893) B6855893
theorem B3047063 : Blo 2029435 3047063 := bstep (se 1 (by rfl) ⟨2285297, by rfl⟩ : syracuseStep 3047063 = 4570595) B4570595
theorem B2031375 : Blo 2029435 2031375 := bstep (se 1 (by rfl) ⟨1523531, by rfl⟩ : syracuseStep 2031375 = 3047063) B3047063
theorem B3047069 : Blo 2029435 3047069 := bbase (se 3 (by rfl) ⟨571325, by rfl⟩ : syracuseStep 3047069 = 1142651) (by norm_num)
theorem B2031379 : Blo 2029435 2031379 := bstep (se 1 (by rfl) ⟨1523534, by rfl⟩ : syracuseStep 2031379 = 3047069) B3047069
theorem B4570613 : Blo 2029435 4570613 := bbase (se 5 (by rfl) ⟨214247, by rfl⟩ : syracuseStep 4570613 = 428495) (by norm_num)
theorem B3047075 : Blo 2029435 3047075 := bstep (se 1 (by rfl) ⟨2285306, by rfl⟩ : syracuseStep 3047075 = 4570613) B4570613
theorem B2031383 : Blo 2029435 2031383 := bstep (se 1 (by rfl) ⟨1523537, by rfl⟩ : syracuseStep 2031383 = 3047075) B3047075
theorem B6261589 : Blo 2029435 6261589 := bbase (se 9 (by rfl) ⟨18344, by rfl⟩ : syracuseStep 6261589 = 36689) (by norm_num)
theorem B33395141 : Blo 2029435 33395141 := bstep (se 4 (by rfl) ⟨3130794, by rfl⟩ : syracuseStep 33395141 = 6261589) B6261589
theorem B22263427 : Blo 2029435 22263427 := bstep (se 1 (by rfl) ⟨16697570, by rfl⟩ : syracuseStep 22263427 = 33395141) B33395141
theorem B29684569 : Blo 2029435 29684569 := bstep (se 2 (by rfl) ⟨11131713, by rfl⟩ : syracuseStep 29684569 = 22263427) B22263427
theorem B39579425 : Blo 2029435 39579425 := bstep (se 2 (by rfl) ⟨14842284, by rfl⟩ : syracuseStep 39579425 = 29684569) B29684569
theorem B26386283 : Blo 2029435 26386283 := bstep (se 1 (by rfl) ⟨19789712, by rfl⟩ : syracuseStep 26386283 = 39579425) B39579425
theorem B17590855 : Blo 2029435 17590855 := bstep (se 1 (by rfl) ⟨13193141, by rfl⟩ : syracuseStep 17590855 = 26386283) B26386283
theorem B23454473 : Blo 2029435 23454473 := bstep (se 2 (by rfl) ⟨8795427, by rfl⟩ : syracuseStep 23454473 = 17590855) B17590855
theorem B250181045 : Blo 2029435 250181045 := bstep (se 5 (by rfl) ⟨11727236, by rfl⟩ : syracuseStep 250181045 = 23454473) B23454473
theorem B166787363 : Blo 2029435 166787363 := bstep (se 1 (by rfl) ⟨125090522, by rfl⟩ : syracuseStep 166787363 = 250181045) B250181045
theorem B111191575 : Blo 2029435 111191575 := bstep (se 1 (by rfl) ⟨83393681, by rfl⟩ : syracuseStep 111191575 = 166787363) B166787363
theorem B148255433 : Blo 2029435 148255433 := bstep (se 2 (by rfl) ⟨55595787, by rfl⟩ : syracuseStep 148255433 = 111191575) B111191575
theorem B98836955 : Blo 2029435 98836955 := bstep (se 1 (by rfl) ⟨74127716, by rfl⟩ : syracuseStep 98836955 = 148255433) B148255433
theorem B65891303 : Blo 2029435 65891303 := bstep (se 1 (by rfl) ⟨49418477, by rfl⟩ : syracuseStep 65891303 = 98836955) B98836955
theorem B43927535 : Blo 2029435 43927535 := bstep (se 1 (by rfl) ⟨32945651, by rfl⟩ : syracuseStep 43927535 = 65891303) B65891303
theorem B29285023 : Blo 2029435 29285023 := bstep (se 1 (by rfl) ⟨21963767, by rfl⟩ : syracuseStep 29285023 = 43927535) B43927535
theorem B39046697 : Blo 2029435 39046697 := bstep (se 2 (by rfl) ⟨14642511, by rfl⟩ : syracuseStep 39046697 = 29285023) B29285023
theorem B26031131 : Blo 2029435 26031131 := bstep (se 1 (by rfl) ⟨19523348, by rfl⟩ : syracuseStep 26031131 = 39046697) B39046697
theorem B17354087 : Blo 2029435 17354087 := bstep (se 1 (by rfl) ⟨13015565, by rfl⟩ : syracuseStep 17354087 = 26031131) B26031131
theorem B11569391 : Blo 2029435 11569391 := bstep (se 1 (by rfl) ⟨8677043, by rfl⟩ : syracuseStep 11569391 = 17354087) B17354087
theorem B7712927 : Blo 2029435 7712927 := bstep (se 1 (by rfl) ⟨5784695, by rfl⟩ : syracuseStep 7712927 = 11569391) B11569391
theorem B5141951 : Blo 2029435 5141951 := bstep (se 1 (by rfl) ⟨3856463, by rfl⟩ : syracuseStep 5141951 = 7712927) B7712927
theorem B3427967 : Blo 2029435 3427967 := bstep (se 1 (by rfl) ⟨2570975, by rfl⟩ : syracuseStep 3427967 = 5141951) B5141951
theorem B2285311 : Blo 2029435 2285311 := bstep (se 1 (by rfl) ⟨1713983, by rfl⟩ : syracuseStep 2285311 = 3427967) B3427967
theorem B3047081 : Blo 2029435 3047081 := bstep (se 2 (by rfl) ⟨1142655, by rfl⟩ : syracuseStep 3047081 = 2285311) B2285311
theorem B2031387 : Blo 2029435 2031387 := bstep (se 1 (by rfl) ⟨1523540, by rfl⟩ : syracuseStep 2031387 = 3047081) B3047081
theorem B2169265 : Blo 2029435 2169265 := bbase (se 2 (by rfl) ⟨813474, by rfl⟩ : syracuseStep 2169265 = 1626949) (by norm_num)
theorem B2892353 : Blo 2029435 2892353 := bstep (se 2 (by rfl) ⟨1084632, by rfl⟩ : syracuseStep 2892353 = 2169265) B2169265
theorem B7712941 : Blo 2029435 7712941 := bstep (se 3 (by rfl) ⟨1446176, by rfl⟩ : syracuseStep 7712941 = 2892353) B2892353
theorem B10283921 : Blo 2029435 10283921 := bstep (se 2 (by rfl) ⟨3856470, by rfl⟩ : syracuseStep 10283921 = 7712941) B7712941
theorem B6855947 : Blo 2029435 6855947 := bstep (se 1 (by rfl) ⟨5141960, by rfl⟩ : syracuseStep 6855947 = 10283921) B10283921
theorem B4570631 : Blo 2029435 4570631 := bstep (se 1 (by rfl) ⟨3427973, by rfl⟩ : syracuseStep 4570631 = 6855947) B6855947
theorem B3047087 : Blo 2029435 3047087 := bstep (se 1 (by rfl) ⟨2285315, by rfl⟩ : syracuseStep 3047087 = 4570631) B4570631
theorem B2031391 : Blo 2029435 2031391 := bstep (se 1 (by rfl) ⟨1523543, by rfl⟩ : syracuseStep 2031391 = 3047087) B3047087
theorem B3047093 : Blo 2029435 3047093 := bbase (se 5 (by rfl) ⟨142832, by rfl⟩ : syracuseStep 3047093 = 285665) (by norm_num)
theorem B2031395 : Blo 2029435 2031395 := bstep (se 1 (by rfl) ⟨1523546, by rfl⟩ : syracuseStep 2031395 = 3047093) B3047093
theorem B5141981 : Blo 2029435 5141981 := bbase (se 3 (by rfl) ⟨964121, by rfl⟩ : syracuseStep 5141981 = 1928243) (by norm_num)
theorem B3427987 : Blo 2029435 3427987 := bstep (se 1 (by rfl) ⟨2570990, by rfl⟩ : syracuseStep 3427987 = 5141981) B5141981
theorem B4570649 : Blo 2029435 4570649 := bstep (se 2 (by rfl) ⟨1713993, by rfl⟩ : syracuseStep 4570649 = 3427987) B3427987
theorem B3047099 : Blo 2029435 3047099 := bstep (se 1 (by rfl) ⟨2285324, by rfl⟩ : syracuseStep 3047099 = 4570649) B4570649
theorem B2031399 : Blo 2029435 2031399 := bstep (se 1 (by rfl) ⟨1523549, by rfl⟩ : syracuseStep 2031399 = 3047099) B3047099
theorem B2285329 : Blo 2029435 2285329 := bbase (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) (by norm_num)
theorem B3047105 : Blo 2029435 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2031403 : Blo 2029435 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B3856501 : Blo 2029435 3856501 := bbase (se 5 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 3856501 = 361547) (by norm_num)
theorem B5142001 : Blo 2029435 5142001 := bstep (se 2 (by rfl) ⟨1928250, by rfl⟩ : syracuseStep 5142001 = 3856501) B3856501
theorem B6856001 : Blo 2029435 6856001 := bstep (se 2 (by rfl) ⟨2571000, by rfl⟩ : syracuseStep 6856001 = 5142001) B5142001
theorem B4570667 : Blo 2029435 4570667 := bstep (se 1 (by rfl) ⟨3428000, by rfl⟩ : syracuseStep 4570667 = 6856001) B6856001
theorem B3047111 : Blo 2029435 3047111 := bstep (se 1 (by rfl) ⟨2285333, by rfl⟩ : syracuseStep 3047111 = 4570667) B4570667
theorem B2031407 : Blo 2029435 2031407 := bstep (se 1 (by rfl) ⟨1523555, by rfl⟩ : syracuseStep 2031407 = 3047111) B3047111
theorem B3047117 : Blo 2029435 3047117 := bbase (se 3 (by rfl) ⟨571334, by rfl⟩ : syracuseStep 3047117 = 1142669) (by norm_num)
theorem B2031411 : Blo 2029435 2031411 := bstep (se 1 (by rfl) ⟨1523558, by rfl⟩ : syracuseStep 2031411 = 3047117) B3047117
theorem B4570685 : Blo 2029435 4570685 := bbase (se 3 (by rfl) ⟨857003, by rfl⟩ : syracuseStep 4570685 = 1714007) (by norm_num)
theorem B3047123 : Blo 2029435 3047123 := bstep (se 1 (by rfl) ⟨2285342, by rfl⟩ : syracuseStep 3047123 = 4570685) B4570685
theorem B2031415 : Blo 2029435 2031415 := bstep (se 1 (by rfl) ⟨1523561, by rfl⟩ : syracuseStep 2031415 = 3047123) B3047123
theorem B3428021 : Blo 2029435 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B2285347 : Blo 2029435 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B3047129 : Blo 2029435 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B2031419 : Blo 2029435 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B3253949 : Blo 2029435 3253949 := bbase (se 3 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 3253949 = 1220231) (by norm_num)
theorem B2169299 : Blo 2029435 2169299 := bstep (se 1 (by rfl) ⟨1626974, by rfl⟩ : syracuseStep 2169299 = 3253949) B3253949
theorem B5784797 : Blo 2029435 5784797 := bstep (se 3 (by rfl) ⟨1084649, by rfl⟩ : syracuseStep 5784797 = 2169299) B2169299
theorem B15426125 : Blo 2029435 15426125 := bstep (se 3 (by rfl) ⟨2892398, by rfl⟩ : syracuseStep 15426125 = 5784797) B5784797
theorem B10284083 : Blo 2029435 10284083 := bstep (se 1 (by rfl) ⟨7713062, by rfl⟩ : syracuseStep 10284083 = 15426125) B15426125
theorem B6856055 : Blo 2029435 6856055 := bstep (se 1 (by rfl) ⟨5142041, by rfl⟩ : syracuseStep 6856055 = 10284083) B10284083
theorem B4570703 : Blo 2029435 4570703 := bstep (se 1 (by rfl) ⟨3428027, by rfl⟩ : syracuseStep 4570703 = 6856055) B6856055
theorem B3047135 : Blo 2029435 3047135 := bstep (se 1 (by rfl) ⟨2285351, by rfl⟩ : syracuseStep 3047135 = 4570703) B4570703
theorem B2031423 : Blo 2029435 2031423 := bstep (se 1 (by rfl) ⟨1523567, by rfl⟩ : syracuseStep 2031423 = 3047135) B3047135
theorem B3047141 : Blo 2029435 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B2031427 : Blo 2029435 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B5784821 : Blo 2029435 5784821 := bbase (se 5 (by rfl) ⟨271163, by rfl⟩ : syracuseStep 5784821 = 542327) (by norm_num)
theorem B3856547 : Blo 2029435 3856547 := bstep (se 1 (by rfl) ⟨2892410, by rfl⟩ : syracuseStep 3856547 = 5784821) B5784821
theorem B2571031 : Blo 2029435 2571031 := bstep (se 1 (by rfl) ⟨1928273, by rfl⟩ : syracuseStep 2571031 = 3856547) B3856547
theorem B3428041 : Blo 2029435 3428041 := bstep (se 2 (by rfl) ⟨1285515, by rfl⟩ : syracuseStep 3428041 = 2571031) B2571031
theorem B4570721 : Blo 2029435 4570721 := bstep (se 2 (by rfl) ⟨1714020, by rfl⟩ : syracuseStep 4570721 = 3428041) B3428041
theorem B3047147 : Blo 2029435 3047147 := bstep (se 1 (by rfl) ⟨2285360, by rfl⟩ : syracuseStep 3047147 = 4570721) B4570721
theorem B2031431 : Blo 2029435 2031431 := bstep (se 1 (by rfl) ⟨1523573, by rfl⟩ : syracuseStep 2031431 = 3047147) B3047147
theorem B2285365 : Blo 2029435 2285365 := bbase (se 5 (by rfl) ⟨107126, by rfl⟩ : syracuseStep 2285365 = 214253) (by norm_num)
theorem B3047153 : Blo 2029435 3047153 := bstep (se 2 (by rfl) ⟨1142682, by rfl⟩ : syracuseStep 3047153 = 2285365) B2285365
theorem B2031435 : Blo 2029435 2031435 := bstep (se 1 (by rfl) ⟨1523576, by rfl⟩ : syracuseStep 2031435 = 3047153) B3047153
theorem C0 (j : ℕ) (h1 : 507358 ≤ j) (h2 : j ≤ 507858) : Blo 2029435 (4 * j + 3) := by
  interval_cases j
  · exact B2029435
  · exact B2029439
  · exact B2029443
  · exact B2029447
  · exact B2029451
  · exact B2029455
  · exact B2029459
  · exact B2029463
  · exact B2029467
  · exact B2029471
  · exact B2029475
  · exact B2029479
  · exact B2029483
  · exact B2029487
  · exact B2029491
  · exact B2029495
  · exact B2029499
  · exact B2029503
  · exact B2029507
  · exact B2029511
  · exact B2029515
  · exact B2029519
  · exact B2029523
  · exact B2029527
  · exact B2029531
  · exact B2029535
  · exact B2029539
  · exact B2029543
  · exact B2029547
  · exact B2029551
  · exact B2029555
  · exact B2029559
  · exact B2029563
  · exact B2029567
  · exact B2029571
  · exact B2029575
  · exact B2029579
  · exact B2029583
  · exact B2029587
  · exact B2029591
  · exact B2029595
  · exact B2029599
  · exact B2029603
  · exact B2029607
  · exact B2029611
  · exact B2029615
  · exact B2029619
  · exact B2029623
  · exact B2029627
  · exact B2029631
  · exact B2029635
  · exact B2029639
  · exact B2029643
  · exact B2029647
  · exact B2029651
  · exact B2029655
  · exact B2029659
  · exact B2029663
  · exact B2029667
  · exact B2029671
  · exact B2029675
  · exact B2029679
  · exact B2029683
  · exact B2029687
  · exact B2029691
  · exact B2029695
  · exact B2029699
  · exact B2029703
  · exact B2029707
  · exact B2029711
  · exact B2029715
  · exact B2029719
  · exact B2029723
  · exact B2029727
  · exact B2029731
  · exact B2029735
  · exact B2029739
  · exact B2029743
  · exact B2029747
  · exact B2029751
  · exact B2029755
  · exact B2029759
  · exact B2029763
  · exact B2029767
  · exact B2029771
  · exact B2029775
  · exact B2029779
  · exact B2029783
  · exact B2029787
  · exact B2029791
  · exact B2029795
  · exact B2029799
  · exact B2029803
  · exact B2029807
  · exact B2029811
  · exact B2029815
  · exact B2029819
  · exact B2029823
  · exact B2029827
  · exact B2029831
  · exact B2029835
  · exact B2029839
  · exact B2029843
  · exact B2029847
  · exact B2029851
  · exact B2029855
  · exact B2029859
  · exact B2029863
  · exact B2029867
  · exact B2029871
  · exact B2029875
  · exact B2029879
  · exact B2029883
  · exact B2029887
  · exact B2029891
  · exact B2029895
  · exact B2029899
  · exact B2029903
  · exact B2029907
  · exact B2029911
  · exact B2029915
  · exact B2029919
  · exact B2029923
  · exact B2029927
  · exact B2029931
  · exact B2029935
  · exact B2029939
  · exact B2029943
  · exact B2029947
  · exact B2029951
  · exact B2029955
  · exact B2029959
  · exact B2029963
  · exact B2029967
  · exact B2029971
  · exact B2029975
  · exact B2029979
  · exact B2029983
  · exact B2029987
  · exact B2029991
  · exact B2029995
  · exact B2029999
  · exact B2030003
  · exact B2030007
  · exact B2030011
  · exact B2030015
  · exact B2030019
  · exact B2030023
  · exact B2030027
  · exact B2030031
  · exact B2030035
  · exact B2030039
  · exact B2030043
  · exact B2030047
  · exact B2030051
  · exact B2030055
  · exact B2030059
  · exact B2030063
  · exact B2030067
  · exact B2030071
  · exact B2030075
  · exact B2030079
  · exact B2030083
  · exact B2030087
  · exact B2030091
  · exact B2030095
  · exact B2030099
  · exact B2030103
  · exact B2030107
  · exact B2030111
  · exact B2030115
  · exact B2030119
  · exact B2030123
  · exact B2030127
  · exact B2030131
  · exact B2030135
  · exact B2030139
  · exact B2030143
  · exact B2030147
  · exact B2030151
  · exact B2030155
  · exact B2030159
  · exact B2030163
  · exact B2030167
  · exact B2030171
  · exact B2030175
  · exact B2030179
  · exact B2030183
  · exact B2030187
  · exact B2030191
  · exact B2030195
  · exact B2030199
  · exact B2030203
  · exact B2030207
  · exact B2030211
  · exact B2030215
  · exact B2030219
  · exact B2030223
  · exact B2030227
  · exact B2030231
  · exact B2030235
  · exact B2030239
  · exact B2030243
  · exact B2030247
  · exact B2030251
  · exact B2030255
  · exact B2030259
  · exact B2030263
  · exact B2030267
  · exact B2030271
  · exact B2030275
  · exact B2030279
  · exact B2030283
  · exact B2030287
  · exact B2030291
  · exact B2030295
  · exact B2030299
  · exact B2030303
  · exact B2030307
  · exact B2030311
  · exact B2030315
  · exact B2030319
  · exact B2030323
  · exact B2030327
  · exact B2030331
  · exact B2030335
  · exact B2030339
  · exact B2030343
  · exact B2030347
  · exact B2030351
  · exact B2030355
  · exact B2030359
  · exact B2030363
  · exact B2030367
  · exact B2030371
  · exact B2030375
  · exact B2030379
  · exact B2030383
  · exact B2030387
  · exact B2030391
  · exact B2030395
  · exact B2030399
  · exact B2030403
  · exact B2030407
  · exact B2030411
  · exact B2030415
  · exact B2030419
  · exact B2030423
  · exact B2030427
  · exact B2030431
  · exact B2030435
  · exact B2030439
  · exact B2030443
  · exact B2030447
  · exact B2030451
  · exact B2030455
  · exact B2030459
  · exact B2030463
  · exact B2030467
  · exact B2030471
  · exact B2030475
  · exact B2030479
  · exact B2030483
  · exact B2030487
  · exact B2030491
  · exact B2030495
  · exact B2030499
  · exact B2030503
  · exact B2030507
  · exact B2030511
  · exact B2030515
  · exact B2030519
  · exact B2030523
  · exact B2030527
  · exact B2030531
  · exact B2030535
  · exact B2030539
  · exact B2030543
  · exact B2030547
  · exact B2030551
  · exact B2030555
  · exact B2030559
  · exact B2030563
  · exact B2030567
  · exact B2030571
  · exact B2030575
  · exact B2030579
  · exact B2030583
  · exact B2030587
  · exact B2030591
  · exact B2030595
  · exact B2030599
  · exact B2030603
  · exact B2030607
  · exact B2030611
  · exact B2030615
  · exact B2030619
  · exact B2030623
  · exact B2030627
  · exact B2030631
  · exact B2030635
  · exact B2030639
  · exact B2030643
  · exact B2030647
  · exact B2030651
  · exact B2030655
  · exact B2030659
  · exact B2030663
  · exact B2030667
  · exact B2030671
  · exact B2030675
  · exact B2030679
  · exact B2030683
  · exact B2030687
  · exact B2030691
  · exact B2030695
  · exact B2030699
  · exact B2030703
  · exact B2030707
  · exact B2030711
  · exact B2030715
  · exact B2030719
  · exact B2030723
  · exact B2030727
  · exact B2030731
  · exact B2030735
  · exact B2030739
  · exact B2030743
  · exact B2030747
  · exact B2030751
  · exact B2030755
  · exact B2030759
  · exact B2030763
  · exact B2030767
  · exact B2030771
  · exact B2030775
  · exact B2030779
  · exact B2030783
  · exact B2030787
  · exact B2030791
  · exact B2030795
  · exact B2030799
  · exact B2030803
  · exact B2030807
  · exact B2030811
  · exact B2030815
  · exact B2030819
  · exact B2030823
  · exact B2030827
  · exact B2030831
  · exact B2030835
  · exact B2030839
  · exact B2030843
  · exact B2030847
  · exact B2030851
  · exact B2030855
  · exact B2030859
  · exact B2030863
  · exact B2030867
  · exact B2030871
  · exact B2030875
  · exact B2030879
  · exact B2030883
  · exact B2030887
  · exact B2030891
  · exact B2030895
  · exact B2030899
  · exact B2030903
  · exact B2030907
  · exact B2030911
  · exact B2030915
  · exact B2030919
  · exact B2030923
  · exact B2030927
  · exact B2030931
  · exact B2030935
  · exact B2030939
  · exact B2030943
  · exact B2030947
  · exact B2030951
  · exact B2030955
  · exact B2030959
  · exact B2030963
  · exact B2030967
  · exact B2030971
  · exact B2030975
  · exact B2030979
  · exact B2030983
  · exact B2030987
  · exact B2030991
  · exact B2030995
  · exact B2030999
  · exact B2031003
  · exact B2031007
  · exact B2031011
  · exact B2031015
  · exact B2031019
  · exact B2031023
  · exact B2031027
  · exact B2031031
  · exact B2031035
  · exact B2031039
  · exact B2031043
  · exact B2031047
  · exact B2031051
  · exact B2031055
  · exact B2031059
  · exact B2031063
  · exact B2031067
  · exact B2031071
  · exact B2031075
  · exact B2031079
  · exact B2031083
  · exact B2031087
  · exact B2031091
  · exact B2031095
  · exact B2031099
  · exact B2031103
  · exact B2031107
  · exact B2031111
  · exact B2031115
  · exact B2031119
  · exact B2031123
  · exact B2031127
  · exact B2031131
  · exact B2031135
  · exact B2031139
  · exact B2031143
  · exact B2031147
  · exact B2031151
  · exact B2031155
  · exact B2031159
  · exact B2031163
  · exact B2031167
  · exact B2031171
  · exact B2031175
  · exact B2031179
  · exact B2031183
  · exact B2031187
  · exact B2031191
  · exact B2031195
  · exact B2031199
  · exact B2031203
  · exact B2031207
  · exact B2031211
  · exact B2031215
  · exact B2031219
  · exact B2031223
  · exact B2031227
  · exact B2031231
  · exact B2031235
  · exact B2031239
  · exact B2031243
  · exact B2031247
  · exact B2031251
  · exact B2031255
  · exact B2031259
  · exact B2031263
  · exact B2031267
  · exact B2031271
  · exact B2031275
  · exact B2031279
  · exact B2031283
  · exact B2031287
  · exact B2031291
  · exact B2031295
  · exact B2031299
  · exact B2031303
  · exact B2031307
  · exact B2031311
  · exact B2031315
  · exact B2031319
  · exact B2031323
  · exact B2031327
  · exact B2031331
  · exact B2031335
  · exact B2031339
  · exact B2031343
  · exact B2031347
  · exact B2031351
  · exact B2031355
  · exact B2031359
  · exact B2031363
  · exact B2031367
  · exact B2031371
  · exact B2031375
  · exact B2031379
  · exact B2031383
  · exact B2031387
  · exact B2031391
  · exact B2031395
  · exact B2031399
  · exact B2031403
  · exact B2031407
  · exact B2031411
  · exact B2031415
  · exact B2031419
  · exact B2031423
  · exact B2031427
  · exact B2031431
  · exact B2031435
theorem solution (m : ℕ) (hlo : 2029435 ≤ m) (hhi : m ≤ 2031435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 507358 ≤ j := by omega
    have hj2 : j ≤ 507858 := by omega
    have hb : Blo 2029435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
