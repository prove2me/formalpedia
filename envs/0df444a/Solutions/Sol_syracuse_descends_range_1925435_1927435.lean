-- Prove2me | solution 1 for syracuse_descends_range_1925435_1927435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:16.058114+00:00
-- url     : https://prove2.me/submissions/5e902a2b-03db-4da5-8c90-125b2cb005cf

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

theorem B3249173 : Blo 1925435 3249173 := bbase (se 6 (by rfl) ⟨76152, by rfl⟩ : syracuseStep 3249173 = 152305) (by norm_num)
theorem B2166115 : Blo 1925435 2166115 := bstep (se 1 (by rfl) ⟨1624586, by rfl⟩ : syracuseStep 2166115 = 3249173) B3249173
theorem B2888153 : Blo 1925435 2888153 := bstep (se 2 (by rfl) ⟨1083057, by rfl⟩ : syracuseStep 2888153 = 2166115) B2166115
theorem B1925435 : Blo 1925435 1925435 := bstep (se 1 (by rfl) ⟨1444076, by rfl⟩ : syracuseStep 1925435 = 2888153) B2888153
theorem B35130773 : Blo 1925435 35130773 := bbase (se 6 (by rfl) ⟨823377, by rfl⟩ : syracuseStep 35130773 = 1646755) (by norm_num)
theorem B23420515 : Blo 1925435 23420515 := bstep (se 1 (by rfl) ⟨17565386, by rfl⟩ : syracuseStep 23420515 = 35130773) B35130773
theorem B31227353 : Blo 1925435 31227353 := bstep (se 2 (by rfl) ⟨11710257, by rfl⟩ : syracuseStep 31227353 = 23420515) B23420515
theorem B20818235 : Blo 1925435 20818235 := bstep (se 1 (by rfl) ⟨15613676, by rfl⟩ : syracuseStep 20818235 = 31227353) B31227353
theorem B13878823 : Blo 1925435 13878823 := bstep (se 1 (by rfl) ⟨10409117, by rfl⟩ : syracuseStep 13878823 = 20818235) B20818235
theorem B18505097 : Blo 1925435 18505097 := bstep (se 2 (by rfl) ⟨6939411, by rfl⟩ : syracuseStep 18505097 = 13878823) B13878823
theorem B12336731 : Blo 1925435 12336731 := bstep (se 1 (by rfl) ⟨9252548, by rfl⟩ : syracuseStep 12336731 = 18505097) B18505097
theorem B8224487 : Blo 1925435 8224487 := bstep (se 1 (by rfl) ⟨6168365, by rfl⟩ : syracuseStep 8224487 = 12336731) B12336731
theorem B5482991 : Blo 1925435 5482991 := bstep (se 1 (by rfl) ⟨4112243, by rfl⟩ : syracuseStep 5482991 = 8224487) B8224487
theorem B14621309 : Blo 1925435 14621309 := bstep (se 3 (by rfl) ⟨2741495, by rfl⟩ : syracuseStep 14621309 = 5482991) B5482991
theorem B9747539 : Blo 1925435 9747539 := bstep (se 1 (by rfl) ⟨7310654, by rfl⟩ : syracuseStep 9747539 = 14621309) B14621309
theorem B6498359 : Blo 1925435 6498359 := bstep (se 1 (by rfl) ⟨4873769, by rfl⟩ : syracuseStep 6498359 = 9747539) B9747539
theorem B4332239 : Blo 1925435 4332239 := bstep (se 1 (by rfl) ⟨3249179, by rfl⟩ : syracuseStep 4332239 = 6498359) B6498359
theorem B2888159 : Blo 1925435 2888159 := bstep (se 1 (by rfl) ⟨2166119, by rfl⟩ : syracuseStep 2888159 = 4332239) B4332239
theorem B1925439 : Blo 1925435 1925439 := bstep (se 1 (by rfl) ⟨1444079, by rfl⟩ : syracuseStep 1925439 = 2888159) B2888159
theorem B2888165 : Blo 1925435 2888165 := bbase (se 4 (by rfl) ⟨270765, by rfl⟩ : syracuseStep 2888165 = 541531) (by norm_num)
theorem B1925443 : Blo 1925435 1925443 := bstep (se 1 (by rfl) ⟨1444082, by rfl⟩ : syracuseStep 1925443 = 2888165) B2888165
theorem B3903437 : Blo 1925435 3903437 := bbase (se 3 (by rfl) ⟨731894, by rfl⟩ : syracuseStep 3903437 = 1463789) (by norm_num)
theorem B2602291 : Blo 1925435 2602291 := bstep (se 1 (by rfl) ⟨1951718, by rfl⟩ : syracuseStep 2602291 = 3903437) B3903437
theorem B3469721 : Blo 1925435 3469721 := bstep (se 2 (by rfl) ⟨1301145, by rfl⟩ : syracuseStep 3469721 = 2602291) B2602291
theorem B9252589 : Blo 1925435 9252589 := bstep (se 3 (by rfl) ⟨1734860, by rfl⟩ : syracuseStep 9252589 = 3469721) B3469721
theorem B12336785 : Blo 1925435 12336785 := bstep (se 2 (by rfl) ⟨4626294, by rfl⟩ : syracuseStep 12336785 = 9252589) B9252589
theorem B8224523 : Blo 1925435 8224523 := bstep (se 1 (by rfl) ⟨6168392, by rfl⟩ : syracuseStep 8224523 = 12336785) B12336785
theorem B5483015 : Blo 1925435 5483015 := bstep (se 1 (by rfl) ⟨4112261, by rfl⟩ : syracuseStep 5483015 = 8224523) B8224523
theorem B3655343 : Blo 1925435 3655343 := bstep (se 1 (by rfl) ⟨2741507, by rfl⟩ : syracuseStep 3655343 = 5483015) B5483015
theorem B2436895 : Blo 1925435 2436895 := bstep (se 1 (by rfl) ⟨1827671, by rfl⟩ : syracuseStep 2436895 = 3655343) B3655343
theorem B3249193 : Blo 1925435 3249193 := bstep (se 2 (by rfl) ⟨1218447, by rfl⟩ : syracuseStep 3249193 = 2436895) B2436895
theorem B4332257 : Blo 1925435 4332257 := bstep (se 2 (by rfl) ⟨1624596, by rfl⟩ : syracuseStep 4332257 = 3249193) B3249193
theorem B2888171 : Blo 1925435 2888171 := bstep (se 1 (by rfl) ⟨2166128, by rfl⟩ : syracuseStep 2888171 = 4332257) B4332257
theorem B1925447 : Blo 1925435 1925447 := bstep (se 1 (by rfl) ⟨1444085, by rfl⟩ : syracuseStep 1925447 = 2888171) B2888171
theorem B2166133 : Blo 1925435 2166133 := bbase (se 5 (by rfl) ⟨101537, by rfl⟩ : syracuseStep 2166133 = 203075) (by norm_num)
theorem B2888177 : Blo 1925435 2888177 := bstep (se 2 (by rfl) ⟨1083066, by rfl⟩ : syracuseStep 2888177 = 2166133) B2166133
theorem B1925451 : Blo 1925435 1925451 := bstep (se 1 (by rfl) ⟨1444088, by rfl⟩ : syracuseStep 1925451 = 2888177) B2888177
theorem B2436905 : Blo 1925435 2436905 := bbase (se 2 (by rfl) ⟨913839, by rfl⟩ : syracuseStep 2436905 = 1827679) (by norm_num)
theorem B6498413 : Blo 1925435 6498413 := bstep (se 3 (by rfl) ⟨1218452, by rfl⟩ : syracuseStep 6498413 = 2436905) B2436905
theorem B4332275 : Blo 1925435 4332275 := bstep (se 1 (by rfl) ⟨3249206, by rfl⟩ : syracuseStep 4332275 = 6498413) B6498413
theorem B2888183 : Blo 1925435 2888183 := bstep (se 1 (by rfl) ⟨2166137, by rfl⟩ : syracuseStep 2888183 = 4332275) B4332275
theorem B1925455 : Blo 1925435 1925455 := bstep (se 1 (by rfl) ⟨1444091, by rfl⟩ : syracuseStep 1925455 = 2888183) B2888183
theorem B2888189 : Blo 1925435 2888189 := bbase (se 3 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 2888189 = 1083071) (by norm_num)
theorem B1925459 : Blo 1925435 1925459 := bstep (se 1 (by rfl) ⟨1444094, by rfl⟩ : syracuseStep 1925459 = 2888189) B2888189
theorem B4332293 : Blo 1925435 4332293 := bbase (se 4 (by rfl) ⟨406152, by rfl⟩ : syracuseStep 4332293 = 812305) (by norm_num)
theorem B2888195 : Blo 1925435 2888195 := bstep (se 1 (by rfl) ⟨2166146, by rfl⟩ : syracuseStep 2888195 = 4332293) B4332293
theorem B1925463 : Blo 1925435 1925463 := bstep (se 1 (by rfl) ⟨1444097, by rfl⟩ : syracuseStep 1925463 = 2888195) B2888195
theorem B3655381 : Blo 1925435 3655381 := bbase (se 7 (by rfl) ⟨42836, by rfl⟩ : syracuseStep 3655381 = 85673) (by norm_num)
theorem B4873841 : Blo 1925435 4873841 := bstep (se 2 (by rfl) ⟨1827690, by rfl⟩ : syracuseStep 4873841 = 3655381) B3655381
theorem B3249227 : Blo 1925435 3249227 := bstep (se 1 (by rfl) ⟨2436920, by rfl⟩ : syracuseStep 3249227 = 4873841) B4873841
theorem B2166151 : Blo 1925435 2166151 := bstep (se 1 (by rfl) ⟨1624613, by rfl⟩ : syracuseStep 2166151 = 3249227) B3249227
theorem B2888201 : Blo 1925435 2888201 := bstep (se 2 (by rfl) ⟨1083075, by rfl⟩ : syracuseStep 2888201 = 2166151) B2166151
theorem B1925467 : Blo 1925435 1925467 := bstep (se 1 (by rfl) ⟨1444100, by rfl⟩ : syracuseStep 1925467 = 2888201) B2888201
theorem B9747701 : Blo 1925435 9747701 := bbase (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) (by norm_num)
theorem B6498467 : Blo 1925435 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B4332311 : Blo 1925435 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B2888207 : Blo 1925435 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B1925471 : Blo 1925435 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B2888213 : Blo 1925435 2888213 := bbase (se 6 (by rfl) ⟨67692, by rfl⟩ : syracuseStep 2888213 = 135385) (by norm_num)
theorem B1925475 : Blo 1925435 1925475 := bstep (se 1 (by rfl) ⟨1444106, by rfl⟩ : syracuseStep 1925475 = 2888213) B2888213
theorem B6939557 : Blo 1925435 6939557 := bbase (se 4 (by rfl) ⟨650583, by rfl⟩ : syracuseStep 6939557 = 1301167) (by norm_num)
theorem B4626371 : Blo 1925435 4626371 := bstep (se 1 (by rfl) ⟨3469778, by rfl⟩ : syracuseStep 4626371 = 6939557) B6939557
theorem B3084247 : Blo 1925435 3084247 := bstep (se 1 (by rfl) ⟨2313185, by rfl⟩ : syracuseStep 3084247 = 4626371) B4626371
theorem B16449317 : Blo 1925435 16449317 := bstep (se 4 (by rfl) ⟨1542123, by rfl⟩ : syracuseStep 16449317 = 3084247) B3084247
theorem B10966211 : Blo 1925435 10966211 := bstep (se 1 (by rfl) ⟨8224658, by rfl⟩ : syracuseStep 10966211 = 16449317) B16449317
theorem B7310807 : Blo 1925435 7310807 := bstep (se 1 (by rfl) ⟨5483105, by rfl⟩ : syracuseStep 7310807 = 10966211) B10966211
theorem B4873871 : Blo 1925435 4873871 := bstep (se 1 (by rfl) ⟨3655403, by rfl⟩ : syracuseStep 4873871 = 7310807) B7310807
theorem B3249247 : Blo 1925435 3249247 := bstep (se 1 (by rfl) ⟨2436935, by rfl⟩ : syracuseStep 3249247 = 4873871) B4873871
theorem B4332329 : Blo 1925435 4332329 := bstep (se 2 (by rfl) ⟨1624623, by rfl⟩ : syracuseStep 4332329 = 3249247) B3249247
theorem B2888219 : Blo 1925435 2888219 := bstep (se 1 (by rfl) ⟨2166164, by rfl⟩ : syracuseStep 2888219 = 4332329) B4332329
theorem B1925479 : Blo 1925435 1925479 := bstep (se 1 (by rfl) ⟨1444109, by rfl⟩ : syracuseStep 1925479 = 2888219) B2888219
theorem B2166169 : Blo 1925435 2166169 := bbase (se 2 (by rfl) ⟨812313, by rfl⟩ : syracuseStep 2166169 = 1624627) (by norm_num)
theorem B2888225 : Blo 1925435 2888225 := bstep (se 2 (by rfl) ⟨1083084, by rfl⟩ : syracuseStep 2888225 = 2166169) B2166169
theorem B1925483 : Blo 1925435 1925483 := bstep (se 1 (by rfl) ⟨1444112, by rfl⟩ : syracuseStep 1925483 = 2888225) B2888225
theorem B7310837 : Blo 1925435 7310837 := bbase (se 5 (by rfl) ⟨342695, by rfl⟩ : syracuseStep 7310837 = 685391) (by norm_num)
theorem B4873891 : Blo 1925435 4873891 := bstep (se 1 (by rfl) ⟨3655418, by rfl⟩ : syracuseStep 4873891 = 7310837) B7310837
theorem B6498521 : Blo 1925435 6498521 := bstep (se 2 (by rfl) ⟨2436945, by rfl⟩ : syracuseStep 6498521 = 4873891) B4873891
theorem B4332347 : Blo 1925435 4332347 := bstep (se 1 (by rfl) ⟨3249260, by rfl⟩ : syracuseStep 4332347 = 6498521) B6498521
theorem B2888231 : Blo 1925435 2888231 := bstep (se 1 (by rfl) ⟨2166173, by rfl⟩ : syracuseStep 2888231 = 4332347) B4332347
theorem B1925487 : Blo 1925435 1925487 := bstep (se 1 (by rfl) ⟨1444115, by rfl⟩ : syracuseStep 1925487 = 2888231) B2888231
theorem B2888237 : Blo 1925435 2888237 := bbase (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) (by norm_num)
theorem B1925491 : Blo 1925435 1925491 := bstep (se 1 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 1925491 = 2888237) B2888237
theorem B4332365 : Blo 1925435 4332365 := bbase (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) (by norm_num)
theorem B2888243 : Blo 1925435 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B1925495 : Blo 1925435 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B2436961 : Blo 1925435 2436961 := bbase (se 2 (by rfl) ⟨913860, by rfl⟩ : syracuseStep 2436961 = 1827721) (by norm_num)
theorem B3249281 : Blo 1925435 3249281 := bstep (se 2 (by rfl) ⟨1218480, by rfl⟩ : syracuseStep 3249281 = 2436961) B2436961
theorem B2166187 : Blo 1925435 2166187 := bstep (se 1 (by rfl) ⟨1624640, by rfl⟩ : syracuseStep 2166187 = 3249281) B3249281
theorem B2888249 : Blo 1925435 2888249 := bstep (se 2 (by rfl) ⟨1083093, by rfl⟩ : syracuseStep 2888249 = 2166187) B2166187
theorem B1925499 : Blo 1925435 1925499 := bstep (se 1 (by rfl) ⟨1444124, by rfl⟩ : syracuseStep 1925499 = 2888249) B2888249
theorem B21932693 : Blo 1925435 21932693 := bbase (se 6 (by rfl) ⟨514047, by rfl⟩ : syracuseStep 21932693 = 1028095) (by norm_num)
theorem B14621795 : Blo 1925435 14621795 := bstep (se 1 (by rfl) ⟨10966346, by rfl⟩ : syracuseStep 14621795 = 21932693) B21932693
theorem B9747863 : Blo 1925435 9747863 := bstep (se 1 (by rfl) ⟨7310897, by rfl⟩ : syracuseStep 9747863 = 14621795) B14621795
theorem B6498575 : Blo 1925435 6498575 := bstep (se 1 (by rfl) ⟨4873931, by rfl⟩ : syracuseStep 6498575 = 9747863) B9747863
theorem B4332383 : Blo 1925435 4332383 := bstep (se 1 (by rfl) ⟨3249287, by rfl⟩ : syracuseStep 4332383 = 6498575) B6498575
theorem B2888255 : Blo 1925435 2888255 := bstep (se 1 (by rfl) ⟨2166191, by rfl⟩ : syracuseStep 2888255 = 4332383) B4332383
theorem B1925503 : Blo 1925435 1925503 := bstep (se 1 (by rfl) ⟨1444127, by rfl⟩ : syracuseStep 1925503 = 2888255) B2888255
theorem B2888261 : Blo 1925435 2888261 := bbase (se 4 (by rfl) ⟨270774, by rfl⟩ : syracuseStep 2888261 = 541549) (by norm_num)
theorem B1925507 : Blo 1925435 1925507 := bstep (se 1 (by rfl) ⟨1444130, by rfl⟩ : syracuseStep 1925507 = 2888261) B2888261
theorem B3249301 : Blo 1925435 3249301 := bbase (se 6 (by rfl) ⟨76155, by rfl⟩ : syracuseStep 3249301 = 152311) (by norm_num)
theorem B4332401 : Blo 1925435 4332401 := bstep (se 2 (by rfl) ⟨1624650, by rfl⟩ : syracuseStep 4332401 = 3249301) B3249301
theorem B2888267 : Blo 1925435 2888267 := bstep (se 1 (by rfl) ⟨2166200, by rfl⟩ : syracuseStep 2888267 = 4332401) B4332401
theorem B1925511 : Blo 1925435 1925511 := bstep (se 1 (by rfl) ⟨1444133, by rfl⟩ : syracuseStep 1925511 = 2888267) B2888267
theorem B2166205 : Blo 1925435 2166205 := bbase (se 3 (by rfl) ⟨406163, by rfl⟩ : syracuseStep 2166205 = 812327) (by norm_num)
theorem B2888273 : Blo 1925435 2888273 := bstep (se 2 (by rfl) ⟨1083102, by rfl⟩ : syracuseStep 2888273 = 2166205) B2166205
theorem B1925515 : Blo 1925435 1925515 := bstep (se 1 (by rfl) ⟨1444136, by rfl⟩ : syracuseStep 1925515 = 2888273) B2888273
theorem B6498629 : Blo 1925435 6498629 := bbase (se 4 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 6498629 = 1218493) (by norm_num)
theorem B4332419 : Blo 1925435 4332419 := bstep (se 1 (by rfl) ⟨3249314, by rfl⟩ : syracuseStep 4332419 = 6498629) B6498629
theorem B2888279 : Blo 1925435 2888279 := bstep (se 1 (by rfl) ⟨2166209, by rfl⟩ : syracuseStep 2888279 = 4332419) B4332419
theorem B1925519 : Blo 1925435 1925519 := bstep (se 1 (by rfl) ⟨1444139, by rfl⟩ : syracuseStep 1925519 = 2888279) B2888279
theorem B2888285 : Blo 1925435 2888285 := bbase (se 3 (by rfl) ⟨541553, by rfl⟩ : syracuseStep 2888285 = 1083107) (by norm_num)
theorem B1925523 : Blo 1925435 1925523 := bstep (se 1 (by rfl) ⟨1444142, by rfl⟩ : syracuseStep 1925523 = 2888285) B2888285
theorem B4332437 : Blo 1925435 4332437 := bbase (se 6 (by rfl) ⟨101541, by rfl⟩ : syracuseStep 4332437 = 203083) (by norm_num)
theorem B2888291 : Blo 1925435 2888291 := bstep (se 1 (by rfl) ⟨2166218, by rfl⟩ : syracuseStep 2888291 = 4332437) B4332437
theorem B1925527 : Blo 1925435 1925527 := bstep (se 1 (by rfl) ⟨1444145, by rfl⟩ : syracuseStep 1925527 = 2888291) B2888291
theorem B2602405 : Blo 1925435 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B3469873 : Blo 1925435 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B4626497 : Blo 1925435 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B3084331 : Blo 1925435 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B4112441 : Blo 1925435 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B2741627 : Blo 1925435 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B7311005 : Blo 1925435 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B4874003 : Blo 1925435 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B3249335 : Blo 1925435 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2166223 : Blo 1925435 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B2888297 : Blo 1925435 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B1925531 : Blo 1925435 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B4451485 : Blo 1925435 4451485 := bbase (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) (by norm_num)
theorem B5935313 : Blo 1925435 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B15827501 : Blo 1925435 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B10551667 : Blo 1925435 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B14068889 : Blo 1925435 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B9379259 : Blo 1925435 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B6252839 : Blo 1925435 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B4168559 : Blo 1925435 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B2779039 : Blo 1925435 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B14821541 : Blo 1925435 14821541 := bstep (se 4 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 14821541 = 2779039) B2779039
theorem B9881027 : Blo 1925435 9881027 := bstep (se 1 (by rfl) ⟨7410770, by rfl⟩ : syracuseStep 9881027 = 14821541) B14821541
theorem B6587351 : Blo 1925435 6587351 := bstep (se 1 (by rfl) ⟨4940513, by rfl⟩ : syracuseStep 6587351 = 9881027) B9881027
theorem B4391567 : Blo 1925435 4391567 := bstep (se 1 (by rfl) ⟨3293675, by rfl⟩ : syracuseStep 4391567 = 6587351) B6587351
theorem B2927711 : Blo 1925435 2927711 := bstep (se 1 (by rfl) ⟨2195783, by rfl⟩ : syracuseStep 2927711 = 4391567) B4391567
theorem B7807229 : Blo 1925435 7807229 := bstep (se 3 (by rfl) ⟨1463855, by rfl⟩ : syracuseStep 7807229 = 2927711) B2927711
theorem B5204819 : Blo 1925435 5204819 := bstep (se 1 (by rfl) ⟨3903614, by rfl⟩ : syracuseStep 5204819 = 7807229) B7807229
theorem B3469879 : Blo 1925435 3469879 := bstep (se 1 (by rfl) ⟨2602409, by rfl⟩ : syracuseStep 3469879 = 5204819) B5204819
theorem B4626505 : Blo 1925435 4626505 := bstep (se 2 (by rfl) ⟨1734939, by rfl⟩ : syracuseStep 4626505 = 3469879) B3469879
theorem B6168673 : Blo 1925435 6168673 := bstep (se 2 (by rfl) ⟨2313252, by rfl⟩ : syracuseStep 6168673 = 4626505) B4626505
theorem B8224897 : Blo 1925435 8224897 := bstep (se 2 (by rfl) ⟨3084336, by rfl⟩ : syracuseStep 8224897 = 6168673) B6168673
theorem B10966529 : Blo 1925435 10966529 := bstep (se 2 (by rfl) ⟨4112448, by rfl⟩ : syracuseStep 10966529 = 8224897) B8224897
theorem B7311019 : Blo 1925435 7311019 := bstep (se 1 (by rfl) ⟨5483264, by rfl⟩ : syracuseStep 7311019 = 10966529) B10966529
theorem B9748025 : Blo 1925435 9748025 := bstep (se 2 (by rfl) ⟨3655509, by rfl⟩ : syracuseStep 9748025 = 7311019) B7311019
theorem B6498683 : Blo 1925435 6498683 := bstep (se 1 (by rfl) ⟨4874012, by rfl⟩ : syracuseStep 6498683 = 9748025) B9748025
theorem B4332455 : Blo 1925435 4332455 := bstep (se 1 (by rfl) ⟨3249341, by rfl⟩ : syracuseStep 4332455 = 6498683) B6498683
theorem B2888303 : Blo 1925435 2888303 := bstep (se 1 (by rfl) ⟨2166227, by rfl⟩ : syracuseStep 2888303 = 4332455) B4332455
theorem B1925535 : Blo 1925435 1925535 := bstep (se 1 (by rfl) ⟨1444151, by rfl⟩ : syracuseStep 1925535 = 2888303) B2888303
theorem B2888309 : Blo 1925435 2888309 := bbase (se 5 (by rfl) ⟨135389, by rfl⟩ : syracuseStep 2888309 = 270779) (by norm_num)
theorem B1925539 : Blo 1925435 1925539 := bstep (se 1 (by rfl) ⟨1444154, by rfl⟩ : syracuseStep 1925539 = 2888309) B2888309
theorem B3655525 : Blo 1925435 3655525 := bbase (se 4 (by rfl) ⟨342705, by rfl⟩ : syracuseStep 3655525 = 685411) (by norm_num)
theorem B4874033 : Blo 1925435 4874033 := bstep (se 2 (by rfl) ⟨1827762, by rfl⟩ : syracuseStep 4874033 = 3655525) B3655525
theorem B3249355 : Blo 1925435 3249355 := bstep (se 1 (by rfl) ⟨2437016, by rfl⟩ : syracuseStep 3249355 = 4874033) B4874033
theorem B4332473 : Blo 1925435 4332473 := bstep (se 2 (by rfl) ⟨1624677, by rfl⟩ : syracuseStep 4332473 = 3249355) B3249355
theorem B2888315 : Blo 1925435 2888315 := bstep (se 1 (by rfl) ⟨2166236, by rfl⟩ : syracuseStep 2888315 = 4332473) B4332473
theorem B1925543 : Blo 1925435 1925543 := bstep (se 1 (by rfl) ⟨1444157, by rfl⟩ : syracuseStep 1925543 = 2888315) B2888315
theorem B2166241 : Blo 1925435 2166241 := bbase (se 2 (by rfl) ⟨812340, by rfl⟩ : syracuseStep 2166241 = 1624681) (by norm_num)
theorem B2888321 : Blo 1925435 2888321 := bstep (se 2 (by rfl) ⟨1083120, by rfl⟩ : syracuseStep 2888321 = 2166241) B2166241
theorem B1925547 : Blo 1925435 1925547 := bstep (se 1 (by rfl) ⟨1444160, by rfl⟩ : syracuseStep 1925547 = 2888321) B2888321
theorem B4874053 : Blo 1925435 4874053 := bbase (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) (by norm_num)
theorem B6498737 : Blo 1925435 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B4332491 : Blo 1925435 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B2888327 : Blo 1925435 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B1925551 : Blo 1925435 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B2888333 : Blo 1925435 2888333 := bbase (se 3 (by rfl) ⟨541562, by rfl⟩ : syracuseStep 2888333 = 1083125) (by norm_num)
theorem B1925555 : Blo 1925435 1925555 := bstep (se 1 (by rfl) ⟨1444166, by rfl⟩ : syracuseStep 1925555 = 2888333) B2888333
theorem B4332509 : Blo 1925435 4332509 := bbase (se 3 (by rfl) ⟨812345, by rfl⟩ : syracuseStep 4332509 = 1624691) (by norm_num)
theorem B2888339 : Blo 1925435 2888339 := bstep (se 1 (by rfl) ⟨2166254, by rfl⟩ : syracuseStep 2888339 = 4332509) B4332509
theorem B1925559 : Blo 1925435 1925559 := bstep (se 1 (by rfl) ⟨1444169, by rfl⟩ : syracuseStep 1925559 = 2888339) B2888339
theorem B3249389 : Blo 1925435 3249389 := bbase (se 3 (by rfl) ⟨609260, by rfl⟩ : syracuseStep 3249389 = 1218521) (by norm_num)
theorem B2166259 : Blo 1925435 2166259 := bstep (se 1 (by rfl) ⟨1624694, by rfl⟩ : syracuseStep 2166259 = 3249389) B3249389
theorem B2888345 : Blo 1925435 2888345 := bstep (se 2 (by rfl) ⟨1083129, by rfl⟩ : syracuseStep 2888345 = 2166259) B2166259
theorem B1925563 : Blo 1925435 1925563 := bstep (se 1 (by rfl) ⟨1444172, by rfl⟩ : syracuseStep 1925563 = 2888345) B2888345
theorem B9881189 : Blo 1925435 9881189 := bbase (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) (by norm_num)
theorem B6587459 : Blo 1925435 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B4391639 : Blo 1925435 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B2927759 : Blo 1925435 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B7807357 : Blo 1925435 7807357 := bstep (se 3 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 7807357 = 2927759) B2927759
theorem B10409809 : Blo 1925435 10409809 := bstep (se 2 (by rfl) ⟨3903678, by rfl⟩ : syracuseStep 10409809 = 7807357) B7807357
theorem B13879745 : Blo 1925435 13879745 := bstep (se 2 (by rfl) ⟨5204904, by rfl⟩ : syracuseStep 13879745 = 10409809) B10409809
theorem B9253163 : Blo 1925435 9253163 := bstep (se 1 (by rfl) ⟨6939872, by rfl⟩ : syracuseStep 9253163 = 13879745) B13879745
theorem B24675101 : Blo 1925435 24675101 := bstep (se 3 (by rfl) ⟨4626581, by rfl⟩ : syracuseStep 24675101 = 9253163) B9253163
theorem B16450067 : Blo 1925435 16450067 := bstep (se 1 (by rfl) ⟨12337550, by rfl⟩ : syracuseStep 16450067 = 24675101) B24675101
theorem B10966711 : Blo 1925435 10966711 := bstep (se 1 (by rfl) ⟨8225033, by rfl⟩ : syracuseStep 10966711 = 16450067) B16450067
theorem B14622281 : Blo 1925435 14622281 := bstep (se 2 (by rfl) ⟨5483355, by rfl⟩ : syracuseStep 14622281 = 10966711) B10966711
theorem B9748187 : Blo 1925435 9748187 := bstep (se 1 (by rfl) ⟨7311140, by rfl⟩ : syracuseStep 9748187 = 14622281) B14622281
theorem B6498791 : Blo 1925435 6498791 := bstep (se 1 (by rfl) ⟨4874093, by rfl⟩ : syracuseStep 6498791 = 9748187) B9748187
theorem B4332527 : Blo 1925435 4332527 := bstep (se 1 (by rfl) ⟨3249395, by rfl⟩ : syracuseStep 4332527 = 6498791) B6498791
theorem B2888351 : Blo 1925435 2888351 := bstep (se 1 (by rfl) ⟨2166263, by rfl⟩ : syracuseStep 2888351 = 4332527) B4332527
theorem B1925567 : Blo 1925435 1925567 := bstep (se 1 (by rfl) ⟨1444175, by rfl⟩ : syracuseStep 1925567 = 2888351) B2888351
theorem B2888357 : Blo 1925435 2888357 := bbase (se 4 (by rfl) ⟨270783, by rfl⟩ : syracuseStep 2888357 = 541567) (by norm_num)
theorem B1925571 : Blo 1925435 1925571 := bstep (se 1 (by rfl) ⟨1444178, by rfl⟩ : syracuseStep 1925571 = 2888357) B2888357
theorem B2437057 : Blo 1925435 2437057 := bbase (se 2 (by rfl) ⟨913896, by rfl⟩ : syracuseStep 2437057 = 1827793) (by norm_num)
theorem B3249409 : Blo 1925435 3249409 := bstep (se 2 (by rfl) ⟨1218528, by rfl⟩ : syracuseStep 3249409 = 2437057) B2437057
theorem B4332545 : Blo 1925435 4332545 := bstep (se 2 (by rfl) ⟨1624704, by rfl⟩ : syracuseStep 4332545 = 3249409) B3249409
theorem B2888363 : Blo 1925435 2888363 := bstep (se 1 (by rfl) ⟨2166272, by rfl⟩ : syracuseStep 2888363 = 4332545) B4332545
theorem B1925575 : Blo 1925435 1925575 := bstep (se 1 (by rfl) ⟨1444181, by rfl⟩ : syracuseStep 1925575 = 2888363) B2888363
theorem B2166277 : Blo 1925435 2166277 := bbase (se 4 (by rfl) ⟨203088, by rfl⟩ : syracuseStep 2166277 = 406177) (by norm_num)
theorem B2888369 : Blo 1925435 2888369 := bstep (se 2 (by rfl) ⟨1083138, by rfl⟩ : syracuseStep 2888369 = 2166277) B2166277
theorem B1925579 : Blo 1925435 1925579 := bstep (se 1 (by rfl) ⟨1444184, by rfl⟩ : syracuseStep 1925579 = 2888369) B2888369
theorem B2741701 : Blo 1925435 2741701 := bbase (se 4 (by rfl) ⟨257034, by rfl⟩ : syracuseStep 2741701 = 514069) (by norm_num)
theorem B3655601 : Blo 1925435 3655601 := bstep (se 2 (by rfl) ⟨1370850, by rfl⟩ : syracuseStep 3655601 = 2741701) B2741701
theorem B2437067 : Blo 1925435 2437067 := bstep (se 1 (by rfl) ⟨1827800, by rfl⟩ : syracuseStep 2437067 = 3655601) B3655601
theorem B6498845 : Blo 1925435 6498845 := bstep (se 3 (by rfl) ⟨1218533, by rfl⟩ : syracuseStep 6498845 = 2437067) B2437067
theorem B4332563 : Blo 1925435 4332563 := bstep (se 1 (by rfl) ⟨3249422, by rfl⟩ : syracuseStep 4332563 = 6498845) B6498845
theorem B2888375 : Blo 1925435 2888375 := bstep (se 1 (by rfl) ⟨2166281, by rfl⟩ : syracuseStep 2888375 = 4332563) B4332563
theorem B1925583 : Blo 1925435 1925583 := bstep (se 1 (by rfl) ⟨1444187, by rfl⟩ : syracuseStep 1925583 = 2888375) B2888375
theorem B2888381 : Blo 1925435 2888381 := bbase (se 3 (by rfl) ⟨541571, by rfl⟩ : syracuseStep 2888381 = 1083143) (by norm_num)
theorem B1925587 : Blo 1925435 1925587 := bstep (se 1 (by rfl) ⟨1444190, by rfl⟩ : syracuseStep 1925587 = 2888381) B2888381
theorem B4332581 : Blo 1925435 4332581 := bbase (se 4 (by rfl) ⟨406179, by rfl⟩ : syracuseStep 4332581 = 812359) (by norm_num)
theorem B2888387 : Blo 1925435 2888387 := bstep (se 1 (by rfl) ⟨2166290, by rfl⟩ : syracuseStep 2888387 = 4332581) B4332581
theorem B1925591 : Blo 1925435 1925591 := bstep (se 1 (by rfl) ⟨1444193, by rfl⟩ : syracuseStep 1925591 = 2888387) B2888387
theorem B4874165 : Blo 1925435 4874165 := bbase (se 5 (by rfl) ⟨228476, by rfl⟩ : syracuseStep 4874165 = 456953) (by norm_num)
theorem B3249443 : Blo 1925435 3249443 := bstep (se 1 (by rfl) ⟨2437082, by rfl⟩ : syracuseStep 3249443 = 4874165) B4874165
theorem B2166295 : Blo 1925435 2166295 := bstep (se 1 (by rfl) ⟨1624721, by rfl⟩ : syracuseStep 2166295 = 3249443) B3249443
theorem B2888393 : Blo 1925435 2888393 := bstep (se 2 (by rfl) ⟨1083147, by rfl⟩ : syracuseStep 2888393 = 2166295) B2166295
theorem B1925595 : Blo 1925435 1925595 := bstep (se 1 (by rfl) ⟨1444196, by rfl⟩ : syracuseStep 1925595 = 2888393) B2888393
theorem B6939989 : Blo 1925435 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B4626659 : Blo 1925435 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B12337757 : Blo 1925435 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B8225171 : Blo 1925435 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B5483447 : Blo 1925435 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B3655631 : Blo 1925435 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B9748349 : Blo 1925435 9748349 := bstep (se 3 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 9748349 = 3655631) B3655631
theorem B6498899 : Blo 1925435 6498899 := bstep (se 1 (by rfl) ⟨4874174, by rfl⟩ : syracuseStep 6498899 = 9748349) B9748349
theorem B4332599 : Blo 1925435 4332599 := bstep (se 1 (by rfl) ⟨3249449, by rfl⟩ : syracuseStep 4332599 = 6498899) B6498899
theorem B2888399 : Blo 1925435 2888399 := bstep (se 1 (by rfl) ⟨2166299, by rfl⟩ : syracuseStep 2888399 = 4332599) B4332599
theorem B1925599 : Blo 1925435 1925599 := bstep (se 1 (by rfl) ⟨1444199, by rfl⟩ : syracuseStep 1925599 = 2888399) B2888399
theorem B2888405 : Blo 1925435 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B1925603 : Blo 1925435 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B2927821 : Blo 1925435 2927821 := bbase (se 3 (by rfl) ⟨548966, by rfl⟩ : syracuseStep 2927821 = 1097933) (by norm_num)
theorem B3903761 : Blo 1925435 3903761 := bstep (se 2 (by rfl) ⟨1463910, by rfl⟩ : syracuseStep 3903761 = 2927821) B2927821
theorem B10410029 : Blo 1925435 10410029 := bstep (se 3 (by rfl) ⟨1951880, by rfl⟩ : syracuseStep 10410029 = 3903761) B3903761
theorem B6940019 : Blo 1925435 6940019 := bstep (se 1 (by rfl) ⟨5205014, by rfl⟩ : syracuseStep 6940019 = 10410029) B10410029
theorem B4626679 : Blo 1925435 4626679 := bstep (se 1 (by rfl) ⟨3470009, by rfl⟩ : syracuseStep 4626679 = 6940019) B6940019
theorem B6168905 : Blo 1925435 6168905 := bstep (se 2 (by rfl) ⟨2313339, by rfl⟩ : syracuseStep 6168905 = 4626679) B4626679
theorem B4112603 : Blo 1925435 4112603 := bstep (se 1 (by rfl) ⟨3084452, by rfl⟩ : syracuseStep 4112603 = 6168905) B6168905
theorem B2741735 : Blo 1925435 2741735 := bstep (se 1 (by rfl) ⟨2056301, by rfl⟩ : syracuseStep 2741735 = 4112603) B4112603
theorem B7311293 : Blo 1925435 7311293 := bstep (se 3 (by rfl) ⟨1370867, by rfl⟩ : syracuseStep 7311293 = 2741735) B2741735
theorem B4874195 : Blo 1925435 4874195 := bstep (se 1 (by rfl) ⟨3655646, by rfl⟩ : syracuseStep 4874195 = 7311293) B7311293
theorem B3249463 : Blo 1925435 3249463 := bstep (se 1 (by rfl) ⟨2437097, by rfl⟩ : syracuseStep 3249463 = 4874195) B4874195
theorem B4332617 : Blo 1925435 4332617 := bstep (se 2 (by rfl) ⟨1624731, by rfl⟩ : syracuseStep 4332617 = 3249463) B3249463
theorem B2888411 : Blo 1925435 2888411 := bstep (se 1 (by rfl) ⟨2166308, by rfl⟩ : syracuseStep 2888411 = 4332617) B4332617
theorem B1925607 : Blo 1925435 1925607 := bstep (se 1 (by rfl) ⟨1444205, by rfl⟩ : syracuseStep 1925607 = 2888411) B2888411
theorem B2166313 : Blo 1925435 2166313 := bbase (se 2 (by rfl) ⟨812367, by rfl⟩ : syracuseStep 2166313 = 1624735) (by norm_num)
theorem B2888417 : Blo 1925435 2888417 := bstep (se 2 (by rfl) ⟨1083156, by rfl⟩ : syracuseStep 2888417 = 2166313) B2166313
theorem B1925611 : Blo 1925435 1925611 := bstep (se 1 (by rfl) ⟨1444208, by rfl⟩ : syracuseStep 1925611 = 2888417) B2888417
theorem B4391749 : Blo 1925435 4391749 := bbase (se 4 (by rfl) ⟨411726, by rfl⟩ : syracuseStep 4391749 = 823453) (by norm_num)
theorem B5855665 : Blo 1925435 5855665 := bstep (se 2 (by rfl) ⟨2195874, by rfl⟩ : syracuseStep 5855665 = 4391749) B4391749
theorem B7807553 : Blo 1925435 7807553 := bstep (se 2 (by rfl) ⟨2927832, by rfl⟩ : syracuseStep 7807553 = 5855665) B5855665
theorem B5205035 : Blo 1925435 5205035 := bstep (se 1 (by rfl) ⟨3903776, by rfl⟩ : syracuseStep 5205035 = 7807553) B7807553
theorem B3470023 : Blo 1925435 3470023 := bstep (se 1 (by rfl) ⟨2602517, by rfl⟩ : syracuseStep 3470023 = 5205035) B5205035
theorem B18506789 : Blo 1925435 18506789 := bstep (se 4 (by rfl) ⟨1735011, by rfl⟩ : syracuseStep 18506789 = 3470023) B3470023
theorem B12337859 : Blo 1925435 12337859 := bstep (se 1 (by rfl) ⟨9253394, by rfl⟩ : syracuseStep 12337859 = 18506789) B18506789
theorem B8225239 : Blo 1925435 8225239 := bstep (se 1 (by rfl) ⟨6168929, by rfl⟩ : syracuseStep 8225239 = 12337859) B12337859
theorem B10966985 : Blo 1925435 10966985 := bstep (se 2 (by rfl) ⟨4112619, by rfl⟩ : syracuseStep 10966985 = 8225239) B8225239
theorem B7311323 : Blo 1925435 7311323 := bstep (se 1 (by rfl) ⟨5483492, by rfl⟩ : syracuseStep 7311323 = 10966985) B10966985
theorem B4874215 : Blo 1925435 4874215 := bstep (se 1 (by rfl) ⟨3655661, by rfl⟩ : syracuseStep 4874215 = 7311323) B7311323
theorem B6498953 : Blo 1925435 6498953 := bstep (se 2 (by rfl) ⟨2437107, by rfl⟩ : syracuseStep 6498953 = 4874215) B4874215
theorem B4332635 : Blo 1925435 4332635 := bstep (se 1 (by rfl) ⟨3249476, by rfl⟩ : syracuseStep 4332635 = 6498953) B6498953
theorem B2888423 : Blo 1925435 2888423 := bstep (se 1 (by rfl) ⟨2166317, by rfl⟩ : syracuseStep 2888423 = 4332635) B4332635
theorem B1925615 : Blo 1925435 1925615 := bstep (se 1 (by rfl) ⟨1444211, by rfl⟩ : syracuseStep 1925615 = 2888423) B2888423
theorem B2888429 : Blo 1925435 2888429 := bbase (se 3 (by rfl) ⟨541580, by rfl⟩ : syracuseStep 2888429 = 1083161) (by norm_num)
theorem B1925619 : Blo 1925435 1925619 := bstep (se 1 (by rfl) ⟨1444214, by rfl⟩ : syracuseStep 1925619 = 2888429) B2888429
theorem B4332653 : Blo 1925435 4332653 := bbase (se 3 (by rfl) ⟨812372, by rfl⟩ : syracuseStep 4332653 = 1624745) (by norm_num)
theorem B2888435 : Blo 1925435 2888435 := bstep (se 1 (by rfl) ⟨2166326, by rfl⟩ : syracuseStep 2888435 = 4332653) B4332653
theorem B1925623 : Blo 1925435 1925623 := bstep (se 1 (by rfl) ⟨1444217, by rfl⟩ : syracuseStep 1925623 = 2888435) B2888435
theorem B3655685 : Blo 1925435 3655685 := bbase (se 4 (by rfl) ⟨342720, by rfl⟩ : syracuseStep 3655685 = 685441) (by norm_num)
theorem B2437123 : Blo 1925435 2437123 := bstep (se 1 (by rfl) ⟨1827842, by rfl⟩ : syracuseStep 2437123 = 3655685) B3655685
theorem B3249497 : Blo 1925435 3249497 := bstep (se 2 (by rfl) ⟨1218561, by rfl⟩ : syracuseStep 3249497 = 2437123) B2437123
theorem B2166331 : Blo 1925435 2166331 := bstep (se 1 (by rfl) ⟨1624748, by rfl⟩ : syracuseStep 2166331 = 3249497) B3249497
theorem B2888441 : Blo 1925435 2888441 := bstep (se 2 (by rfl) ⟨1083165, by rfl⟩ : syracuseStep 2888441 = 2166331) B2166331
theorem B1925627 : Blo 1925435 1925627 := bstep (se 1 (by rfl) ⟨1444220, by rfl⟩ : syracuseStep 1925627 = 2888441) B2888441
theorem B20032661 : Blo 1925435 20032661 := bbase (se 6 (by rfl) ⟨469515, by rfl⟩ : syracuseStep 20032661 = 939031) (by norm_num)
theorem B13355107 : Blo 1925435 13355107 := bstep (se 1 (by rfl) ⟨10016330, by rfl⟩ : syracuseStep 13355107 = 20032661) B20032661
theorem B71227237 : Blo 1925435 71227237 := bstep (se 4 (by rfl) ⟨6677553, by rfl⟩ : syracuseStep 71227237 = 13355107) B13355107
theorem B94969649 : Blo 1925435 94969649 := bstep (se 2 (by rfl) ⟨35613618, by rfl⟩ : syracuseStep 94969649 = 71227237) B71227237
theorem B63313099 : Blo 1925435 63313099 := bstep (se 1 (by rfl) ⟨47484824, by rfl⟩ : syracuseStep 63313099 = 94969649) B94969649
theorem B1350679445 : Blo 1925435 1350679445 := bstep (se 6 (by rfl) ⟨31656549, by rfl⟩ : syracuseStep 1350679445 = 63313099) B63313099
theorem B900452963 : Blo 1925435 900452963 := bstep (se 1 (by rfl) ⟨675339722, by rfl⟩ : syracuseStep 900452963 = 1350679445) B1350679445
theorem B600301975 : Blo 1925435 600301975 := bstep (se 1 (by rfl) ⟨450226481, by rfl⟩ : syracuseStep 600301975 = 900452963) B900452963
theorem B800402633 : Blo 1925435 800402633 := bstep (se 2 (by rfl) ⟨300150987, by rfl⟩ : syracuseStep 800402633 = 600301975) B600301975
theorem B533601755 : Blo 1925435 533601755 := bstep (se 1 (by rfl) ⟨400201316, by rfl⟩ : syracuseStep 533601755 = 800402633) B800402633
theorem B355734503 : Blo 1925435 355734503 := bstep (se 1 (by rfl) ⟨266800877, by rfl⟩ : syracuseStep 355734503 = 533601755) B533601755
theorem B237156335 : Blo 1925435 237156335 := bstep (se 1 (by rfl) ⟨177867251, by rfl⟩ : syracuseStep 237156335 = 355734503) B355734503
theorem B158104223 : Blo 1925435 158104223 := bstep (se 1 (by rfl) ⟨118578167, by rfl⟩ : syracuseStep 158104223 = 237156335) B237156335
theorem B105402815 : Blo 1925435 105402815 := bstep (se 1 (by rfl) ⟨79052111, by rfl⟩ : syracuseStep 105402815 = 158104223) B158104223
theorem B70268543 : Blo 1925435 70268543 := bstep (se 1 (by rfl) ⟨52701407, by rfl⟩ : syracuseStep 70268543 = 105402815) B105402815
theorem B46845695 : Blo 1925435 46845695 := bstep (se 1 (by rfl) ⟨35134271, by rfl⟩ : syracuseStep 46845695 = 70268543) B70268543
theorem B31230463 : Blo 1925435 31230463 := bstep (se 1 (by rfl) ⟨23422847, by rfl⟩ : syracuseStep 31230463 = 46845695) B46845695
theorem B41640617 : Blo 1925435 41640617 := bstep (se 2 (by rfl) ⟨15615231, by rfl⟩ : syracuseStep 41640617 = 31230463) B31230463
theorem B27760411 : Blo 1925435 27760411 := bstep (se 1 (by rfl) ⟨20820308, by rfl⟩ : syracuseStep 27760411 = 41640617) B41640617
theorem B37013881 : Blo 1925435 37013881 := bstep (se 2 (by rfl) ⟨13880205, by rfl⟩ : syracuseStep 37013881 = 27760411) B27760411
theorem B49351841 : Blo 1925435 49351841 := bstep (se 2 (by rfl) ⟨18506940, by rfl⟩ : syracuseStep 49351841 = 37013881) B37013881
theorem B32901227 : Blo 1925435 32901227 := bstep (se 1 (by rfl) ⟨24675920, by rfl⟩ : syracuseStep 32901227 = 49351841) B49351841
theorem B21934151 : Blo 1925435 21934151 := bstep (se 1 (by rfl) ⟨16450613, by rfl⟩ : syracuseStep 21934151 = 32901227) B32901227
theorem B14622767 : Blo 1925435 14622767 := bstep (se 1 (by rfl) ⟨10967075, by rfl⟩ : syracuseStep 14622767 = 21934151) B21934151
theorem B9748511 : Blo 1925435 9748511 := bstep (se 1 (by rfl) ⟨7311383, by rfl⟩ : syracuseStep 9748511 = 14622767) B14622767
theorem B6499007 : Blo 1925435 6499007 := bstep (se 1 (by rfl) ⟨4874255, by rfl⟩ : syracuseStep 6499007 = 9748511) B9748511
theorem B4332671 : Blo 1925435 4332671 := bstep (se 1 (by rfl) ⟨3249503, by rfl⟩ : syracuseStep 4332671 = 6499007) B6499007
theorem B2888447 : Blo 1925435 2888447 := bstep (se 1 (by rfl) ⟨2166335, by rfl⟩ : syracuseStep 2888447 = 4332671) B4332671
theorem B1925631 : Blo 1925435 1925631 := bstep (se 1 (by rfl) ⟨1444223, by rfl⟩ : syracuseStep 1925631 = 2888447) B2888447
theorem B2888453 : Blo 1925435 2888453 := bbase (se 4 (by rfl) ⟨270792, by rfl⟩ : syracuseStep 2888453 = 541585) (by norm_num)
theorem B1925635 : Blo 1925435 1925635 := bstep (se 1 (by rfl) ⟨1444226, by rfl⟩ : syracuseStep 1925635 = 2888453) B2888453
theorem B3249517 : Blo 1925435 3249517 := bbase (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) (by norm_num)
theorem B4332689 : Blo 1925435 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B2888459 : Blo 1925435 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B1925639 : Blo 1925435 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B2166349 : Blo 1925435 2166349 := bbase (se 3 (by rfl) ⟨406190, by rfl⟩ : syracuseStep 2166349 = 812381) (by norm_num)
theorem B2888465 : Blo 1925435 2888465 := bstep (se 2 (by rfl) ⟨1083174, by rfl⟩ : syracuseStep 2888465 = 2166349) B2166349
theorem B1925643 : Blo 1925435 1925643 := bstep (se 1 (by rfl) ⟨1444232, by rfl⟩ : syracuseStep 1925643 = 2888465) B2888465
theorem B6499061 : Blo 1925435 6499061 := bbase (se 5 (by rfl) ⟨304643, by rfl⟩ : syracuseStep 6499061 = 609287) (by norm_num)
theorem B4332707 : Blo 1925435 4332707 := bstep (se 1 (by rfl) ⟨3249530, by rfl⟩ : syracuseStep 4332707 = 6499061) B6499061
theorem B2888471 : Blo 1925435 2888471 := bstep (se 1 (by rfl) ⟨2166353, by rfl⟩ : syracuseStep 2888471 = 4332707) B4332707
theorem B1925647 : Blo 1925435 1925647 := bstep (se 1 (by rfl) ⟨1444235, by rfl⟩ : syracuseStep 1925647 = 2888471) B2888471
theorem B2888477 : Blo 1925435 2888477 := bbase (se 3 (by rfl) ⟨541589, by rfl⟩ : syracuseStep 2888477 = 1083179) (by norm_num)
theorem B1925651 : Blo 1925435 1925651 := bstep (se 1 (by rfl) ⟨1444238, by rfl⟩ : syracuseStep 1925651 = 2888477) B2888477
theorem B4332725 : Blo 1925435 4332725 := bbase (se 5 (by rfl) ⟨203096, by rfl⟩ : syracuseStep 4332725 = 406193) (by norm_num)
theorem B2888483 : Blo 1925435 2888483 := bstep (se 1 (by rfl) ⟨2166362, by rfl⟩ : syracuseStep 2888483 = 4332725) B4332725
theorem B1925655 : Blo 1925435 1925655 := bstep (se 1 (by rfl) ⟨1444241, by rfl⟩ : syracuseStep 1925655 = 2888483) B2888483
theorem B2056357 : Blo 1925435 2056357 := bbase (se 4 (by rfl) ⟨192783, by rfl⟩ : syracuseStep 2056357 = 385567) (by norm_num)
theorem B10967237 : Blo 1925435 10967237 := bstep (se 4 (by rfl) ⟨1028178, by rfl⟩ : syracuseStep 10967237 = 2056357) B2056357
theorem B7311491 : Blo 1925435 7311491 := bstep (se 1 (by rfl) ⟨5483618, by rfl⟩ : syracuseStep 7311491 = 10967237) B10967237
theorem B4874327 : Blo 1925435 4874327 := bstep (se 1 (by rfl) ⟨3655745, by rfl⟩ : syracuseStep 4874327 = 7311491) B7311491
theorem B3249551 : Blo 1925435 3249551 := bstep (se 1 (by rfl) ⟨2437163, by rfl⟩ : syracuseStep 3249551 = 4874327) B4874327
theorem B2166367 : Blo 1925435 2166367 := bstep (se 1 (by rfl) ⟨1624775, by rfl⟩ : syracuseStep 2166367 = 3249551) B3249551
theorem B2888489 : Blo 1925435 2888489 := bstep (se 2 (by rfl) ⟨1083183, by rfl⟩ : syracuseStep 2888489 = 2166367) B2166367
theorem B1925659 : Blo 1925435 1925659 := bstep (se 1 (by rfl) ⟨1444244, by rfl⟩ : syracuseStep 1925659 = 2888489) B2888489
theorem B2056361 : Blo 1925435 2056361 := bbase (se 2 (by rfl) ⟨771135, by rfl⟩ : syracuseStep 2056361 = 1542271) (by norm_num)
theorem B5483629 : Blo 1925435 5483629 := bstep (se 3 (by rfl) ⟨1028180, by rfl⟩ : syracuseStep 5483629 = 2056361) B2056361
theorem B7311505 : Blo 1925435 7311505 := bstep (se 2 (by rfl) ⟨2741814, by rfl⟩ : syracuseStep 7311505 = 5483629) B5483629
theorem B9748673 : Blo 1925435 9748673 := bstep (se 2 (by rfl) ⟨3655752, by rfl⟩ : syracuseStep 9748673 = 7311505) B7311505
theorem B6499115 : Blo 1925435 6499115 := bstep (se 1 (by rfl) ⟨4874336, by rfl⟩ : syracuseStep 6499115 = 9748673) B9748673
theorem B4332743 : Blo 1925435 4332743 := bstep (se 1 (by rfl) ⟨3249557, by rfl⟩ : syracuseStep 4332743 = 6499115) B6499115
theorem B2888495 : Blo 1925435 2888495 := bstep (se 1 (by rfl) ⟨2166371, by rfl⟩ : syracuseStep 2888495 = 4332743) B4332743
theorem B1925663 : Blo 1925435 1925663 := bstep (se 1 (by rfl) ⟨1444247, by rfl⟩ : syracuseStep 1925663 = 2888495) B2888495
theorem B2888501 : Blo 1925435 2888501 := bbase (se 5 (by rfl) ⟨135398, by rfl⟩ : syracuseStep 2888501 = 270797) (by norm_num)
theorem B1925667 : Blo 1925435 1925667 := bstep (se 1 (by rfl) ⟨1444250, by rfl⟩ : syracuseStep 1925667 = 2888501) B2888501
theorem B4874357 : Blo 1925435 4874357 := bbase (se 5 (by rfl) ⟨228485, by rfl⟩ : syracuseStep 4874357 = 456971) (by norm_num)
theorem B3249571 : Blo 1925435 3249571 := bstep (se 1 (by rfl) ⟨2437178, by rfl⟩ : syracuseStep 3249571 = 4874357) B4874357
theorem B4332761 : Blo 1925435 4332761 := bstep (se 2 (by rfl) ⟨1624785, by rfl⟩ : syracuseStep 4332761 = 3249571) B3249571
theorem B2888507 : Blo 1925435 2888507 := bstep (se 1 (by rfl) ⟨2166380, by rfl⟩ : syracuseStep 2888507 = 4332761) B4332761
theorem B1925671 : Blo 1925435 1925671 := bstep (se 1 (by rfl) ⟨1444253, by rfl⟩ : syracuseStep 1925671 = 2888507) B2888507
theorem B2166385 : Blo 1925435 2166385 := bbase (se 2 (by rfl) ⟨812394, by rfl⟩ : syracuseStep 2166385 = 1624789) (by norm_num)
theorem B2888513 : Blo 1925435 2888513 := bstep (se 2 (by rfl) ⟨1083192, by rfl⟩ : syracuseStep 2888513 = 2166385) B2166385
theorem B1925675 : Blo 1925435 1925675 := bstep (se 1 (by rfl) ⟨1444256, by rfl⟩ : syracuseStep 1925675 = 2888513) B2888513
theorem B53421781 : Blo 1925435 53421781 := bbase (se 7 (by rfl) ⟨626036, by rfl⟩ : syracuseStep 53421781 = 1252073) (by norm_num)
theorem B71229041 : Blo 1925435 71229041 := bstep (se 2 (by rfl) ⟨26710890, by rfl⟩ : syracuseStep 71229041 = 53421781) B53421781
theorem B47486027 : Blo 1925435 47486027 := bstep (se 1 (by rfl) ⟨35614520, by rfl⟩ : syracuseStep 47486027 = 71229041) B71229041
theorem B126629405 : Blo 1925435 126629405 := bstep (se 3 (by rfl) ⟨23743013, by rfl⟩ : syracuseStep 126629405 = 47486027) B47486027
theorem B84419603 : Blo 1925435 84419603 := bstep (se 1 (by rfl) ⟨63314702, by rfl⟩ : syracuseStep 84419603 = 126629405) B126629405
theorem B56279735 : Blo 1925435 56279735 := bstep (se 1 (by rfl) ⟨42209801, by rfl⟩ : syracuseStep 56279735 = 84419603) B84419603
theorem B37519823 : Blo 1925435 37519823 := bstep (se 1 (by rfl) ⟨28139867, by rfl⟩ : syracuseStep 37519823 = 56279735) B56279735
theorem B25013215 : Blo 1925435 25013215 := bstep (se 1 (by rfl) ⟨18759911, by rfl⟩ : syracuseStep 25013215 = 37519823) B37519823
theorem B33350953 : Blo 1925435 33350953 := bstep (se 2 (by rfl) ⟨12506607, by rfl⟩ : syracuseStep 33350953 = 25013215) B25013215
theorem B44467937 : Blo 1925435 44467937 := bstep (se 2 (by rfl) ⟨16675476, by rfl⟩ : syracuseStep 44467937 = 33350953) B33350953
theorem B29645291 : Blo 1925435 29645291 := bstep (se 1 (by rfl) ⟨22233968, by rfl⟩ : syracuseStep 29645291 = 44467937) B44467937
theorem B19763527 : Blo 1925435 19763527 := bstep (se 1 (by rfl) ⟨14822645, by rfl⟩ : syracuseStep 19763527 = 29645291) B29645291
theorem B26351369 : Blo 1925435 26351369 := bstep (se 2 (by rfl) ⟨9881763, by rfl⟩ : syracuseStep 26351369 = 19763527) B19763527
theorem B17567579 : Blo 1925435 17567579 := bstep (se 1 (by rfl) ⟨13175684, by rfl⟩ : syracuseStep 17567579 = 26351369) B26351369
theorem B11711719 : Blo 1925435 11711719 := bstep (se 1 (by rfl) ⟨8783789, by rfl⟩ : syracuseStep 11711719 = 17567579) B17567579
theorem B15615625 : Blo 1925435 15615625 := bstep (se 2 (by rfl) ⟨5855859, by rfl⟩ : syracuseStep 15615625 = 11711719) B11711719
theorem B20820833 : Blo 1925435 20820833 := bstep (se 2 (by rfl) ⟨7807812, by rfl⟩ : syracuseStep 20820833 = 15615625) B15615625
theorem B13880555 : Blo 1925435 13880555 := bstep (se 1 (by rfl) ⟨10410416, by rfl⟩ : syracuseStep 13880555 = 20820833) B20820833
theorem B9253703 : Blo 1925435 9253703 := bstep (se 1 (by rfl) ⟨6940277, by rfl⟩ : syracuseStep 9253703 = 13880555) B13880555
theorem B6169135 : Blo 1925435 6169135 := bstep (se 1 (by rfl) ⟨4626851, by rfl⟩ : syracuseStep 6169135 = 9253703) B9253703
theorem B8225513 : Blo 1925435 8225513 := bstep (se 2 (by rfl) ⟨3084567, by rfl⟩ : syracuseStep 8225513 = 6169135) B6169135
theorem B5483675 : Blo 1925435 5483675 := bstep (se 1 (by rfl) ⟨4112756, by rfl⟩ : syracuseStep 5483675 = 8225513) B8225513
theorem B3655783 : Blo 1925435 3655783 := bstep (se 1 (by rfl) ⟨2741837, by rfl⟩ : syracuseStep 3655783 = 5483675) B5483675
theorem B4874377 : Blo 1925435 4874377 := bstep (se 2 (by rfl) ⟨1827891, by rfl⟩ : syracuseStep 4874377 = 3655783) B3655783
theorem B6499169 : Blo 1925435 6499169 := bstep (se 2 (by rfl) ⟨2437188, by rfl⟩ : syracuseStep 6499169 = 4874377) B4874377
theorem B4332779 : Blo 1925435 4332779 := bstep (se 1 (by rfl) ⟨3249584, by rfl⟩ : syracuseStep 4332779 = 6499169) B6499169
theorem B2888519 : Blo 1925435 2888519 := bstep (se 1 (by rfl) ⟨2166389, by rfl⟩ : syracuseStep 2888519 = 4332779) B4332779
theorem B1925679 : Blo 1925435 1925679 := bstep (se 1 (by rfl) ⟨1444259, by rfl⟩ : syracuseStep 1925679 = 2888519) B2888519
theorem B2888525 : Blo 1925435 2888525 := bbase (se 3 (by rfl) ⟨541598, by rfl⟩ : syracuseStep 2888525 = 1083197) (by norm_num)
theorem B1925683 : Blo 1925435 1925683 := bstep (se 1 (by rfl) ⟨1444262, by rfl⟩ : syracuseStep 1925683 = 2888525) B2888525
theorem B4332797 : Blo 1925435 4332797 := bbase (se 3 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 4332797 = 1624799) (by norm_num)
theorem B2888531 : Blo 1925435 2888531 := bstep (se 1 (by rfl) ⟨2166398, by rfl⟩ : syracuseStep 2888531 = 4332797) B4332797
theorem B1925687 : Blo 1925435 1925687 := bstep (se 1 (by rfl) ⟨1444265, by rfl⟩ : syracuseStep 1925687 = 2888531) B2888531
theorem B3249605 : Blo 1925435 3249605 := bbase (se 4 (by rfl) ⟨304650, by rfl⟩ : syracuseStep 3249605 = 609301) (by norm_num)
theorem B2166403 : Blo 1925435 2166403 := bstep (se 1 (by rfl) ⟨1624802, by rfl⟩ : syracuseStep 2166403 = 3249605) B3249605
theorem B2888537 : Blo 1925435 2888537 := bstep (se 2 (by rfl) ⟨1083201, by rfl⟩ : syracuseStep 2888537 = 2166403) B2166403
theorem B1925691 : Blo 1925435 1925691 := bstep (se 1 (by rfl) ⟨1444268, by rfl⟩ : syracuseStep 1925691 = 2888537) B2888537
theorem B14623253 : Blo 1925435 14623253 := bbase (se 6 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 14623253 = 685465) (by norm_num)
theorem B9748835 : Blo 1925435 9748835 := bstep (se 1 (by rfl) ⟨7311626, by rfl⟩ : syracuseStep 9748835 = 14623253) B14623253
theorem B6499223 : Blo 1925435 6499223 := bstep (se 1 (by rfl) ⟨4874417, by rfl⟩ : syracuseStep 6499223 = 9748835) B9748835
theorem B4332815 : Blo 1925435 4332815 := bstep (se 1 (by rfl) ⟨3249611, by rfl⟩ : syracuseStep 4332815 = 6499223) B6499223
theorem B2888543 : Blo 1925435 2888543 := bstep (se 1 (by rfl) ⟨2166407, by rfl⟩ : syracuseStep 2888543 = 4332815) B4332815
theorem B1925695 : Blo 1925435 1925695 := bstep (se 1 (by rfl) ⟨1444271, by rfl⟩ : syracuseStep 1925695 = 2888543) B2888543
theorem B2888549 : Blo 1925435 2888549 := bbase (se 4 (by rfl) ⟨270801, by rfl⟩ : syracuseStep 2888549 = 541603) (by norm_num)
theorem B1925699 : Blo 1925435 1925699 := bstep (se 1 (by rfl) ⟨1444274, by rfl⟩ : syracuseStep 1925699 = 2888549) B2888549
theorem B3655829 : Blo 1925435 3655829 := bbase (se 6 (by rfl) ⟨85683, by rfl⟩ : syracuseStep 3655829 = 171367) (by norm_num)
theorem B2437219 : Blo 1925435 2437219 := bstep (se 1 (by rfl) ⟨1827914, by rfl⟩ : syracuseStep 2437219 = 3655829) B3655829
theorem B3249625 : Blo 1925435 3249625 := bstep (se 2 (by rfl) ⟨1218609, by rfl⟩ : syracuseStep 3249625 = 2437219) B2437219
theorem B4332833 : Blo 1925435 4332833 := bstep (se 2 (by rfl) ⟨1624812, by rfl⟩ : syracuseStep 4332833 = 3249625) B3249625
theorem B2888555 : Blo 1925435 2888555 := bstep (se 1 (by rfl) ⟨2166416, by rfl⟩ : syracuseStep 2888555 = 4332833) B4332833
theorem B1925703 : Blo 1925435 1925703 := bstep (se 1 (by rfl) ⟨1444277, by rfl⟩ : syracuseStep 1925703 = 2888555) B2888555
theorem B2166421 : Blo 1925435 2166421 := bbase (se 6 (by rfl) ⟨50775, by rfl⟩ : syracuseStep 2166421 = 101551) (by norm_num)
theorem B2888561 : Blo 1925435 2888561 := bstep (se 2 (by rfl) ⟨1083210, by rfl⟩ : syracuseStep 2888561 = 2166421) B2166421
theorem B1925707 : Blo 1925435 1925707 := bstep (se 1 (by rfl) ⟨1444280, by rfl⟩ : syracuseStep 1925707 = 2888561) B2888561
theorem B2437229 : Blo 1925435 2437229 := bbase (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) (by norm_num)
theorem B6499277 : Blo 1925435 6499277 := bstep (se 3 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 6499277 = 2437229) B2437229
theorem B4332851 : Blo 1925435 4332851 := bstep (se 1 (by rfl) ⟨3249638, by rfl⟩ : syracuseStep 4332851 = 6499277) B6499277
theorem B2888567 : Blo 1925435 2888567 := bstep (se 1 (by rfl) ⟨2166425, by rfl⟩ : syracuseStep 2888567 = 4332851) B4332851
theorem B1925711 : Blo 1925435 1925711 := bstep (se 1 (by rfl) ⟨1444283, by rfl⟩ : syracuseStep 1925711 = 2888567) B2888567
theorem B2888573 : Blo 1925435 2888573 := bbase (se 3 (by rfl) ⟨541607, by rfl⟩ : syracuseStep 2888573 = 1083215) (by norm_num)
theorem B1925715 : Blo 1925435 1925715 := bstep (se 1 (by rfl) ⟨1444286, by rfl⟩ : syracuseStep 1925715 = 2888573) B2888573
theorem B4332869 : Blo 1925435 4332869 := bbase (se 4 (by rfl) ⟨406206, by rfl⟩ : syracuseStep 4332869 = 812413) (by norm_num)
theorem B2888579 : Blo 1925435 2888579 := bstep (se 1 (by rfl) ⟨2166434, by rfl⟩ : syracuseStep 2888579 = 4332869) B4332869
theorem B1925719 : Blo 1925435 1925719 := bstep (se 1 (by rfl) ⟨1444289, by rfl⟩ : syracuseStep 1925719 = 2888579) B2888579
theorem B3903997 : Blo 1925435 3903997 := bbase (se 3 (by rfl) ⟨731999, by rfl⟩ : syracuseStep 3903997 = 1463999) (by norm_num)
theorem B5205329 : Blo 1925435 5205329 := bstep (se 2 (by rfl) ⟨1951998, by rfl⟩ : syracuseStep 5205329 = 3903997) B3903997
theorem B3470219 : Blo 1925435 3470219 := bstep (se 1 (by rfl) ⟨2602664, by rfl⟩ : syracuseStep 3470219 = 5205329) B5205329
theorem B2313479 : Blo 1925435 2313479 := bstep (se 1 (by rfl) ⟨1735109, by rfl⟩ : syracuseStep 2313479 = 3470219) B3470219
theorem B6169277 : Blo 1925435 6169277 := bstep (se 3 (by rfl) ⟨1156739, by rfl⟩ : syracuseStep 6169277 = 2313479) B2313479
theorem B4112851 : Blo 1925435 4112851 := bstep (se 1 (by rfl) ⟨3084638, by rfl⟩ : syracuseStep 4112851 = 6169277) B6169277
theorem B5483801 : Blo 1925435 5483801 := bstep (se 2 (by rfl) ⟨2056425, by rfl⟩ : syracuseStep 5483801 = 4112851) B4112851
theorem B3655867 : Blo 1925435 3655867 := bstep (se 1 (by rfl) ⟨2741900, by rfl⟩ : syracuseStep 3655867 = 5483801) B5483801
theorem B4874489 : Blo 1925435 4874489 := bstep (se 2 (by rfl) ⟨1827933, by rfl⟩ : syracuseStep 4874489 = 3655867) B3655867
theorem B3249659 : Blo 1925435 3249659 := bstep (se 1 (by rfl) ⟨2437244, by rfl⟩ : syracuseStep 3249659 = 4874489) B4874489
theorem B2166439 : Blo 1925435 2166439 := bstep (se 1 (by rfl) ⟨1624829, by rfl⟩ : syracuseStep 2166439 = 3249659) B3249659
theorem B2888585 : Blo 1925435 2888585 := bstep (se 2 (by rfl) ⟨1083219, by rfl⟩ : syracuseStep 2888585 = 2166439) B2166439
theorem B1925723 : Blo 1925435 1925723 := bstep (se 1 (by rfl) ⟨1444292, by rfl⟩ : syracuseStep 1925723 = 2888585) B2888585
theorem B9748997 : Blo 1925435 9748997 := bbase (se 4 (by rfl) ⟨913968, by rfl⟩ : syracuseStep 9748997 = 1827937) (by norm_num)
theorem B6499331 : Blo 1925435 6499331 := bstep (se 1 (by rfl) ⟨4874498, by rfl⟩ : syracuseStep 6499331 = 9748997) B9748997
theorem B4332887 : Blo 1925435 4332887 := bstep (se 1 (by rfl) ⟨3249665, by rfl⟩ : syracuseStep 4332887 = 6499331) B6499331
theorem B2888591 : Blo 1925435 2888591 := bstep (se 1 (by rfl) ⟨2166443, by rfl⟩ : syracuseStep 2888591 = 4332887) B4332887
theorem B1925727 : Blo 1925435 1925727 := bstep (se 1 (by rfl) ⟨1444295, by rfl⟩ : syracuseStep 1925727 = 2888591) B2888591
theorem B2888597 : Blo 1925435 2888597 := bbase (se 6 (by rfl) ⟨67701, by rfl⟩ : syracuseStep 2888597 = 135403) (by norm_num)
theorem B1925731 : Blo 1925435 1925731 := bstep (se 1 (by rfl) ⟨1444298, by rfl⟩ : syracuseStep 1925731 = 2888597) B2888597
theorem B10967669 : Blo 1925435 10967669 := bbase (se 5 (by rfl) ⟨514109, by rfl⟩ : syracuseStep 10967669 = 1028219) (by norm_num)
theorem B7311779 : Blo 1925435 7311779 := bstep (se 1 (by rfl) ⟨5483834, by rfl⟩ : syracuseStep 7311779 = 10967669) B10967669
theorem B4874519 : Blo 1925435 4874519 := bstep (se 1 (by rfl) ⟨3655889, by rfl⟩ : syracuseStep 4874519 = 7311779) B7311779
theorem B3249679 : Blo 1925435 3249679 := bstep (se 1 (by rfl) ⟨2437259, by rfl⟩ : syracuseStep 3249679 = 4874519) B4874519
theorem B4332905 : Blo 1925435 4332905 := bstep (se 2 (by rfl) ⟨1624839, by rfl⟩ : syracuseStep 4332905 = 3249679) B3249679
theorem B2888603 : Blo 1925435 2888603 := bstep (se 1 (by rfl) ⟨2166452, by rfl⟩ : syracuseStep 2888603 = 4332905) B4332905
theorem B1925735 : Blo 1925435 1925735 := bstep (se 1 (by rfl) ⟨1444301, by rfl⟩ : syracuseStep 1925735 = 2888603) B2888603
theorem B2166457 : Blo 1925435 2166457 := bbase (se 2 (by rfl) ⟨812421, by rfl⟩ : syracuseStep 2166457 = 1624843) (by norm_num)
theorem B2888609 : Blo 1925435 2888609 := bstep (se 2 (by rfl) ⟨1083228, by rfl⟩ : syracuseStep 2888609 = 2166457) B2166457
theorem B1925739 : Blo 1925435 1925739 := bstep (se 1 (by rfl) ⟨1444304, by rfl⟩ : syracuseStep 1925739 = 2888609) B2888609
theorem B4112893 : Blo 1925435 4112893 := bbase (se 3 (by rfl) ⟨771167, by rfl⟩ : syracuseStep 4112893 = 1542335) (by norm_num)
theorem B5483857 : Blo 1925435 5483857 := bstep (se 2 (by rfl) ⟨2056446, by rfl⟩ : syracuseStep 5483857 = 4112893) B4112893
theorem B7311809 : Blo 1925435 7311809 := bstep (se 2 (by rfl) ⟨2741928, by rfl⟩ : syracuseStep 7311809 = 5483857) B5483857
theorem B4874539 : Blo 1925435 4874539 := bstep (se 1 (by rfl) ⟨3655904, by rfl⟩ : syracuseStep 4874539 = 7311809) B7311809
theorem B6499385 : Blo 1925435 6499385 := bstep (se 2 (by rfl) ⟨2437269, by rfl⟩ : syracuseStep 6499385 = 4874539) B4874539
theorem B4332923 : Blo 1925435 4332923 := bstep (se 1 (by rfl) ⟨3249692, by rfl⟩ : syracuseStep 4332923 = 6499385) B6499385
theorem B2888615 : Blo 1925435 2888615 := bstep (se 1 (by rfl) ⟨2166461, by rfl⟩ : syracuseStep 2888615 = 4332923) B4332923
theorem B1925743 : Blo 1925435 1925743 := bstep (se 1 (by rfl) ⟨1444307, by rfl⟩ : syracuseStep 1925743 = 2888615) B2888615
theorem B2888621 : Blo 1925435 2888621 := bbase (se 3 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 2888621 = 1083233) (by norm_num)
theorem B1925747 : Blo 1925435 1925747 := bstep (se 1 (by rfl) ⟨1444310, by rfl⟩ : syracuseStep 1925747 = 2888621) B2888621
theorem B4332941 : Blo 1925435 4332941 := bbase (se 3 (by rfl) ⟨812426, by rfl⟩ : syracuseStep 4332941 = 1624853) (by norm_num)
theorem B2888627 : Blo 1925435 2888627 := bstep (se 1 (by rfl) ⟨2166470, by rfl⟩ : syracuseStep 2888627 = 4332941) B4332941
theorem B1925751 : Blo 1925435 1925751 := bstep (se 1 (by rfl) ⟨1444313, by rfl⟩ : syracuseStep 1925751 = 2888627) B2888627
theorem B2437285 : Blo 1925435 2437285 := bbase (se 4 (by rfl) ⟨228495, by rfl⟩ : syracuseStep 2437285 = 456991) (by norm_num)
theorem B3249713 : Blo 1925435 3249713 := bstep (se 2 (by rfl) ⟨1218642, by rfl⟩ : syracuseStep 3249713 = 2437285) B2437285
theorem B2166475 : Blo 1925435 2166475 := bstep (se 1 (by rfl) ⟨1624856, by rfl⟩ : syracuseStep 2166475 = 3249713) B3249713
theorem B2888633 : Blo 1925435 2888633 := bstep (se 2 (by rfl) ⟨1083237, by rfl⟩ : syracuseStep 2888633 = 2166475) B2166475
theorem B1925755 : Blo 1925435 1925755 := bstep (se 1 (by rfl) ⟨1444316, by rfl⟩ : syracuseStep 1925755 = 2888633) B2888633
theorem B8338085 : Blo 1925435 8338085 := bbase (se 4 (by rfl) ⟨781695, by rfl⟩ : syracuseStep 8338085 = 1563391) (by norm_num)
theorem B5558723 : Blo 1925435 5558723 := bstep (se 1 (by rfl) ⟨4169042, by rfl⟩ : syracuseStep 5558723 = 8338085) B8338085
theorem B3705815 : Blo 1925435 3705815 := bstep (se 1 (by rfl) ⟨2779361, by rfl⟩ : syracuseStep 3705815 = 5558723) B5558723
theorem B2470543 : Blo 1925435 2470543 := bstep (se 1 (by rfl) ⟨1852907, by rfl⟩ : syracuseStep 2470543 = 3705815) B3705815
theorem B13176229 : Blo 1925435 13176229 := bstep (se 4 (by rfl) ⟨1235271, by rfl⟩ : syracuseStep 13176229 = 2470543) B2470543
theorem B17568305 : Blo 1925435 17568305 := bstep (se 2 (by rfl) ⟨6588114, by rfl⟩ : syracuseStep 17568305 = 13176229) B13176229
theorem B11712203 : Blo 1925435 11712203 := bstep (se 1 (by rfl) ⟨8784152, by rfl⟩ : syracuseStep 11712203 = 17568305) B17568305
theorem B7808135 : Blo 1925435 7808135 := bstep (se 1 (by rfl) ⟨5856101, by rfl⟩ : syracuseStep 7808135 = 11712203) B11712203
theorem B20821693 : Blo 1925435 20821693 := bstep (se 3 (by rfl) ⟨3904067, by rfl⟩ : syracuseStep 20821693 = 7808135) B7808135
theorem B27762257 : Blo 1925435 27762257 := bstep (se 2 (by rfl) ⟨10410846, by rfl⟩ : syracuseStep 27762257 = 20821693) B20821693
theorem B18508171 : Blo 1925435 18508171 := bstep (se 1 (by rfl) ⟨13881128, by rfl⟩ : syracuseStep 18508171 = 27762257) B27762257
theorem B24677561 : Blo 1925435 24677561 := bstep (se 2 (by rfl) ⟨9254085, by rfl⟩ : syracuseStep 24677561 = 18508171) B18508171
theorem B16451707 : Blo 1925435 16451707 := bstep (se 1 (by rfl) ⟨12338780, by rfl⟩ : syracuseStep 16451707 = 24677561) B24677561
theorem B21935609 : Blo 1925435 21935609 := bstep (se 2 (by rfl) ⟨8225853, by rfl⟩ : syracuseStep 21935609 = 16451707) B16451707
theorem B14623739 : Blo 1925435 14623739 := bstep (se 1 (by rfl) ⟨10967804, by rfl⟩ : syracuseStep 14623739 = 21935609) B21935609
theorem B9749159 : Blo 1925435 9749159 := bstep (se 1 (by rfl) ⟨7311869, by rfl⟩ : syracuseStep 9749159 = 14623739) B14623739
theorem B6499439 : Blo 1925435 6499439 := bstep (se 1 (by rfl) ⟨4874579, by rfl⟩ : syracuseStep 6499439 = 9749159) B9749159
theorem B4332959 : Blo 1925435 4332959 := bstep (se 1 (by rfl) ⟨3249719, by rfl⟩ : syracuseStep 4332959 = 6499439) B6499439
theorem B2888639 : Blo 1925435 2888639 := bstep (se 1 (by rfl) ⟨2166479, by rfl⟩ : syracuseStep 2888639 = 4332959) B4332959
theorem B1925759 : Blo 1925435 1925759 := bstep (se 1 (by rfl) ⟨1444319, by rfl⟩ : syracuseStep 1925759 = 2888639) B2888639
theorem B2888645 : Blo 1925435 2888645 := bbase (se 4 (by rfl) ⟨270810, by rfl⟩ : syracuseStep 2888645 = 541621) (by norm_num)
theorem B1925763 : Blo 1925435 1925763 := bstep (se 1 (by rfl) ⟨1444322, by rfl⟩ : syracuseStep 1925763 = 2888645) B2888645
theorem B3249733 : Blo 1925435 3249733 := bbase (se 4 (by rfl) ⟨304662, by rfl⟩ : syracuseStep 3249733 = 609325) (by norm_num)
theorem B4332977 : Blo 1925435 4332977 := bstep (se 2 (by rfl) ⟨1624866, by rfl⟩ : syracuseStep 4332977 = 3249733) B3249733
theorem B2888651 : Blo 1925435 2888651 := bstep (se 1 (by rfl) ⟨2166488, by rfl⟩ : syracuseStep 2888651 = 4332977) B4332977
theorem B1925767 : Blo 1925435 1925767 := bstep (se 1 (by rfl) ⟨1444325, by rfl⟩ : syracuseStep 1925767 = 2888651) B2888651
theorem B2166493 : Blo 1925435 2166493 := bbase (se 3 (by rfl) ⟨406217, by rfl⟩ : syracuseStep 2166493 = 812435) (by norm_num)
theorem B2888657 : Blo 1925435 2888657 := bstep (se 2 (by rfl) ⟨1083246, by rfl⟩ : syracuseStep 2888657 = 2166493) B2166493
theorem B1925771 : Blo 1925435 1925771 := bstep (se 1 (by rfl) ⟨1444328, by rfl⟩ : syracuseStep 1925771 = 2888657) B2888657
theorem B6499493 : Blo 1925435 6499493 := bbase (se 4 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 6499493 = 1218655) (by norm_num)
theorem B4332995 : Blo 1925435 4332995 := bstep (se 1 (by rfl) ⟨3249746, by rfl⟩ : syracuseStep 4332995 = 6499493) B6499493
theorem B2888663 : Blo 1925435 2888663 := bstep (se 1 (by rfl) ⟨2166497, by rfl⟩ : syracuseStep 2888663 = 4332995) B4332995
theorem B1925775 : Blo 1925435 1925775 := bstep (se 1 (by rfl) ⟨1444331, by rfl⟩ : syracuseStep 1925775 = 2888663) B2888663
theorem B2888669 : Blo 1925435 2888669 := bbase (se 3 (by rfl) ⟨541625, by rfl⟩ : syracuseStep 2888669 = 1083251) (by norm_num)
theorem B1925779 : Blo 1925435 1925779 := bstep (se 1 (by rfl) ⟨1444334, by rfl⟩ : syracuseStep 1925779 = 2888669) B2888669
theorem B4333013 : Blo 1925435 4333013 := bbase (se 7 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 4333013 = 101555) (by norm_num)
theorem B2888675 : Blo 1925435 2888675 := bstep (se 1 (by rfl) ⟨2166506, by rfl⟩ : syracuseStep 2888675 = 4333013) B4333013
theorem B1925783 : Blo 1925435 1925783 := bstep (se 1 (by rfl) ⟨1444337, by rfl⟩ : syracuseStep 1925783 = 2888675) B2888675
theorem B2377117 : Blo 1925435 2377117 := bbase (se 3 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 2377117 = 891419) (by norm_num)
theorem B3169489 : Blo 1925435 3169489 := bstep (se 2 (by rfl) ⟨1188558, by rfl⟩ : syracuseStep 3169489 = 2377117) B2377117
theorem B4225985 : Blo 1925435 4225985 := bstep (se 2 (by rfl) ⟨1584744, by rfl⟩ : syracuseStep 4225985 = 3169489) B3169489
theorem B2817323 : Blo 1925435 2817323 := bstep (se 1 (by rfl) ⟨2112992, by rfl⟩ : syracuseStep 2817323 = 4225985) B4225985
theorem B30051445 : Blo 1925435 30051445 := bstep (se 5 (by rfl) ⟨1408661, by rfl⟩ : syracuseStep 30051445 = 2817323) B2817323
theorem B40068593 : Blo 1925435 40068593 := bstep (se 2 (by rfl) ⟨15025722, by rfl⟩ : syracuseStep 40068593 = 30051445) B30051445
theorem B26712395 : Blo 1925435 26712395 := bstep (se 1 (by rfl) ⟨20034296, by rfl⟩ : syracuseStep 26712395 = 40068593) B40068593
theorem B17808263 : Blo 1925435 17808263 := bstep (se 1 (by rfl) ⟨13356197, by rfl⟩ : syracuseStep 17808263 = 26712395) B26712395
theorem B11872175 : Blo 1925435 11872175 := bstep (se 1 (by rfl) ⟨8904131, by rfl⟩ : syracuseStep 11872175 = 17808263) B17808263
theorem B31659133 : Blo 1925435 31659133 := bstep (se 3 (by rfl) ⟨5936087, by rfl⟩ : syracuseStep 31659133 = 11872175) B11872175
theorem B42212177 : Blo 1925435 42212177 := bstep (se 2 (by rfl) ⟨15829566, by rfl⟩ : syracuseStep 42212177 = 31659133) B31659133
theorem B28141451 : Blo 1925435 28141451 := bstep (se 1 (by rfl) ⟨21106088, by rfl⟩ : syracuseStep 28141451 = 42212177) B42212177
theorem B18760967 : Blo 1925435 18760967 := bstep (se 1 (by rfl) ⟨14070725, by rfl⟩ : syracuseStep 18760967 = 28141451) B28141451
theorem B12507311 : Blo 1925435 12507311 := bstep (se 1 (by rfl) ⟨9380483, by rfl⟩ : syracuseStep 12507311 = 18760967) B18760967
theorem B33352829 : Blo 1925435 33352829 := bstep (se 3 (by rfl) ⟨6253655, by rfl⟩ : syracuseStep 33352829 = 12507311) B12507311
theorem B22235219 : Blo 1925435 22235219 := bstep (se 1 (by rfl) ⟨16676414, by rfl⟩ : syracuseStep 22235219 = 33352829) B33352829
theorem B14823479 : Blo 1925435 14823479 := bstep (se 1 (by rfl) ⟨11117609, by rfl⟩ : syracuseStep 14823479 = 22235219) B22235219
theorem B9882319 : Blo 1925435 9882319 := bstep (se 1 (by rfl) ⟨7411739, by rfl⟩ : syracuseStep 9882319 = 14823479) B14823479
theorem B13176425 : Blo 1925435 13176425 := bstep (se 2 (by rfl) ⟨4941159, by rfl⟩ : syracuseStep 13176425 = 9882319) B9882319
theorem B8784283 : Blo 1925435 8784283 := bstep (se 1 (by rfl) ⟨6588212, by rfl⟩ : syracuseStep 8784283 = 13176425) B13176425
theorem B11712377 : Blo 1925435 11712377 := bstep (se 2 (by rfl) ⟨4392141, by rfl⟩ : syracuseStep 11712377 = 8784283) B8784283
theorem B7808251 : Blo 1925435 7808251 := bstep (se 1 (by rfl) ⟨5856188, by rfl⟩ : syracuseStep 7808251 = 11712377) B11712377
theorem B10411001 : Blo 1925435 10411001 := bstep (se 2 (by rfl) ⟨3904125, by rfl⟩ : syracuseStep 10411001 = 7808251) B7808251
theorem B6940667 : Blo 1925435 6940667 := bstep (se 1 (by rfl) ⟨5205500, by rfl⟩ : syracuseStep 6940667 = 10411001) B10411001
theorem B18508445 : Blo 1925435 18508445 := bstep (se 3 (by rfl) ⟨3470333, by rfl⟩ : syracuseStep 18508445 = 6940667) B6940667
theorem B12338963 : Blo 1925435 12338963 := bstep (se 1 (by rfl) ⟨9254222, by rfl⟩ : syracuseStep 12338963 = 18508445) B18508445
theorem B8225975 : Blo 1925435 8225975 := bstep (se 1 (by rfl) ⟨6169481, by rfl⟩ : syracuseStep 8225975 = 12338963) B12338963
theorem B5483983 : Blo 1925435 5483983 := bstep (se 1 (by rfl) ⟨4112987, by rfl⟩ : syracuseStep 5483983 = 8225975) B8225975
theorem B7311977 : Blo 1925435 7311977 := bstep (se 2 (by rfl) ⟨2741991, by rfl⟩ : syracuseStep 7311977 = 5483983) B5483983
theorem B4874651 : Blo 1925435 4874651 := bstep (se 1 (by rfl) ⟨3655988, by rfl⟩ : syracuseStep 4874651 = 7311977) B7311977
theorem B3249767 : Blo 1925435 3249767 := bstep (se 1 (by rfl) ⟨2437325, by rfl⟩ : syracuseStep 3249767 = 4874651) B4874651
theorem B2166511 : Blo 1925435 2166511 := bstep (se 1 (by rfl) ⟨1624883, by rfl⟩ : syracuseStep 2166511 = 3249767) B3249767
theorem B2888681 : Blo 1925435 2888681 := bstep (se 2 (by rfl) ⟨1083255, by rfl⟩ : syracuseStep 2888681 = 2166511) B2166511
theorem B1925787 : Blo 1925435 1925787 := bstep (se 1 (by rfl) ⟨1444340, by rfl⟩ : syracuseStep 1925787 = 2888681) B2888681
theorem B6169493 : Blo 1925435 6169493 := bbase (se 6 (by rfl) ⟨144597, by rfl⟩ : syracuseStep 6169493 = 289195) (by norm_num)
theorem B16451981 : Blo 1925435 16451981 := bstep (se 3 (by rfl) ⟨3084746, by rfl⟩ : syracuseStep 16451981 = 6169493) B6169493
theorem B10967987 : Blo 1925435 10967987 := bstep (se 1 (by rfl) ⟨8225990, by rfl⟩ : syracuseStep 10967987 = 16451981) B16451981
theorem B7311991 : Blo 1925435 7311991 := bstep (se 1 (by rfl) ⟨5483993, by rfl⟩ : syracuseStep 7311991 = 10967987) B10967987
theorem B9749321 : Blo 1925435 9749321 := bstep (se 2 (by rfl) ⟨3655995, by rfl⟩ : syracuseStep 9749321 = 7311991) B7311991
theorem B6499547 : Blo 1925435 6499547 := bstep (se 1 (by rfl) ⟨4874660, by rfl⟩ : syracuseStep 6499547 = 9749321) B9749321
theorem B4333031 : Blo 1925435 4333031 := bstep (se 1 (by rfl) ⟨3249773, by rfl⟩ : syracuseStep 4333031 = 6499547) B6499547
theorem B2888687 : Blo 1925435 2888687 := bstep (se 1 (by rfl) ⟨2166515, by rfl⟩ : syracuseStep 2888687 = 4333031) B4333031
theorem B1925791 : Blo 1925435 1925791 := bstep (se 1 (by rfl) ⟨1444343, by rfl⟩ : syracuseStep 1925791 = 2888687) B2888687
theorem B2888693 : Blo 1925435 2888693 := bbase (se 5 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 2888693 = 270815) (by norm_num)
theorem B1925795 : Blo 1925435 1925795 := bstep (se 1 (by rfl) ⟨1444346, by rfl⟩ : syracuseStep 1925795 = 2888693) B2888693
theorem B4113013 : Blo 1925435 4113013 := bbase (se 5 (by rfl) ⟨192797, by rfl⟩ : syracuseStep 4113013 = 385595) (by norm_num)
theorem B5484017 : Blo 1925435 5484017 := bstep (se 2 (by rfl) ⟨2056506, by rfl⟩ : syracuseStep 5484017 = 4113013) B4113013
theorem B3656011 : Blo 1925435 3656011 := bstep (se 1 (by rfl) ⟨2742008, by rfl⟩ : syracuseStep 3656011 = 5484017) B5484017
theorem B4874681 : Blo 1925435 4874681 := bstep (se 2 (by rfl) ⟨1828005, by rfl⟩ : syracuseStep 4874681 = 3656011) B3656011
theorem B3249787 : Blo 1925435 3249787 := bstep (se 1 (by rfl) ⟨2437340, by rfl⟩ : syracuseStep 3249787 = 4874681) B4874681
theorem B4333049 : Blo 1925435 4333049 := bstep (se 2 (by rfl) ⟨1624893, by rfl⟩ : syracuseStep 4333049 = 3249787) B3249787
theorem B2888699 : Blo 1925435 2888699 := bstep (se 1 (by rfl) ⟨2166524, by rfl⟩ : syracuseStep 2888699 = 4333049) B4333049
theorem B1925799 : Blo 1925435 1925799 := bstep (se 1 (by rfl) ⟨1444349, by rfl⟩ : syracuseStep 1925799 = 2888699) B2888699
theorem B2166529 : Blo 1925435 2166529 := bbase (se 2 (by rfl) ⟨812448, by rfl⟩ : syracuseStep 2166529 = 1624897) (by norm_num)
theorem B2888705 : Blo 1925435 2888705 := bstep (se 2 (by rfl) ⟨1083264, by rfl⟩ : syracuseStep 2888705 = 2166529) B2166529
theorem B1925803 : Blo 1925435 1925803 := bstep (se 1 (by rfl) ⟨1444352, by rfl⟩ : syracuseStep 1925803 = 2888705) B2888705
theorem B4874701 : Blo 1925435 4874701 := bbase (se 3 (by rfl) ⟨914006, by rfl⟩ : syracuseStep 4874701 = 1828013) (by norm_num)
theorem B6499601 : Blo 1925435 6499601 := bstep (se 2 (by rfl) ⟨2437350, by rfl⟩ : syracuseStep 6499601 = 4874701) B4874701
theorem B4333067 : Blo 1925435 4333067 := bstep (se 1 (by rfl) ⟨3249800, by rfl⟩ : syracuseStep 4333067 = 6499601) B6499601
theorem B2888711 : Blo 1925435 2888711 := bstep (se 1 (by rfl) ⟨2166533, by rfl⟩ : syracuseStep 2888711 = 4333067) B4333067
theorem B1925807 : Blo 1925435 1925807 := bstep (se 1 (by rfl) ⟨1444355, by rfl⟩ : syracuseStep 1925807 = 2888711) B2888711
theorem B2888717 : Blo 1925435 2888717 := bbase (se 3 (by rfl) ⟨541634, by rfl⟩ : syracuseStep 2888717 = 1083269) (by norm_num)
theorem B1925811 : Blo 1925435 1925811 := bstep (se 1 (by rfl) ⟨1444358, by rfl⟩ : syracuseStep 1925811 = 2888717) B2888717
theorem B4333085 : Blo 1925435 4333085 := bbase (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) (by norm_num)
theorem B2888723 : Blo 1925435 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B1925815 : Blo 1925435 1925815 := bstep (se 1 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 1925815 = 2888723) B2888723
theorem B3249821 : Blo 1925435 3249821 := bbase (se 3 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 3249821 = 1218683) (by norm_num)
theorem B2166547 : Blo 1925435 2166547 := bstep (se 1 (by rfl) ⟨1624910, by rfl⟩ : syracuseStep 2166547 = 3249821) B3249821
theorem B2888729 : Blo 1925435 2888729 := bstep (se 2 (by rfl) ⟨1083273, by rfl⟩ : syracuseStep 2888729 = 2166547) B2166547
theorem B1925819 : Blo 1925435 1925819 := bstep (se 1 (by rfl) ⟨1444364, by rfl⟩ : syracuseStep 1925819 = 2888729) B2888729
theorem B7411877 : Blo 1925435 7411877 := bbase (se 4 (by rfl) ⟨694863, by rfl⟩ : syracuseStep 7411877 = 1389727) (by norm_num)
theorem B4941251 : Blo 1925435 4941251 := bstep (se 1 (by rfl) ⟨3705938, by rfl⟩ : syracuseStep 4941251 = 7411877) B7411877
theorem B3294167 : Blo 1925435 3294167 := bstep (se 1 (by rfl) ⟨2470625, by rfl⟩ : syracuseStep 3294167 = 4941251) B4941251
theorem B8784445 : Blo 1925435 8784445 := bstep (se 3 (by rfl) ⟨1647083, by rfl⟩ : syracuseStep 8784445 = 3294167) B3294167
theorem B11712593 : Blo 1925435 11712593 := bstep (se 2 (by rfl) ⟨4392222, by rfl⟩ : syracuseStep 11712593 = 8784445) B8784445
theorem B7808395 : Blo 1925435 7808395 := bstep (se 1 (by rfl) ⟨5856296, by rfl⟩ : syracuseStep 7808395 = 11712593) B11712593
theorem B10411193 : Blo 1925435 10411193 := bstep (se 2 (by rfl) ⟨3904197, by rfl⟩ : syracuseStep 10411193 = 7808395) B7808395
theorem B27763181 : Blo 1925435 27763181 := bstep (se 3 (by rfl) ⟨5205596, by rfl⟩ : syracuseStep 27763181 = 10411193) B10411193
theorem B18508787 : Blo 1925435 18508787 := bstep (se 1 (by rfl) ⟨13881590, by rfl⟩ : syracuseStep 18508787 = 27763181) B27763181
theorem B12339191 : Blo 1925435 12339191 := bstep (se 1 (by rfl) ⟨9254393, by rfl⟩ : syracuseStep 12339191 = 18508787) B18508787
theorem B8226127 : Blo 1925435 8226127 := bstep (se 1 (by rfl) ⟨6169595, by rfl⟩ : syracuseStep 8226127 = 12339191) B12339191
theorem B10968169 : Blo 1925435 10968169 := bstep (se 2 (by rfl) ⟨4113063, by rfl⟩ : syracuseStep 10968169 = 8226127) B8226127
theorem B14624225 : Blo 1925435 14624225 := bstep (se 2 (by rfl) ⟨5484084, by rfl⟩ : syracuseStep 14624225 = 10968169) B10968169
theorem B9749483 : Blo 1925435 9749483 := bstep (se 1 (by rfl) ⟨7312112, by rfl⟩ : syracuseStep 9749483 = 14624225) B14624225
theorem B6499655 : Blo 1925435 6499655 := bstep (se 1 (by rfl) ⟨4874741, by rfl⟩ : syracuseStep 6499655 = 9749483) B9749483
theorem B4333103 : Blo 1925435 4333103 := bstep (se 1 (by rfl) ⟨3249827, by rfl⟩ : syracuseStep 4333103 = 6499655) B6499655
theorem B2888735 : Blo 1925435 2888735 := bstep (se 1 (by rfl) ⟨2166551, by rfl⟩ : syracuseStep 2888735 = 4333103) B4333103
theorem B1925823 : Blo 1925435 1925823 := bstep (se 1 (by rfl) ⟨1444367, by rfl⟩ : syracuseStep 1925823 = 2888735) B2888735
theorem B2888741 : Blo 1925435 2888741 := bbase (se 4 (by rfl) ⟨270819, by rfl⟩ : syracuseStep 2888741 = 541639) (by norm_num)
theorem B1925827 : Blo 1925435 1925827 := bstep (se 1 (by rfl) ⟨1444370, by rfl⟩ : syracuseStep 1925827 = 2888741) B2888741
theorem B2437381 : Blo 1925435 2437381 := bbase (se 4 (by rfl) ⟨228504, by rfl⟩ : syracuseStep 2437381 = 457009) (by norm_num)
theorem B3249841 : Blo 1925435 3249841 := bstep (se 2 (by rfl) ⟨1218690, by rfl⟩ : syracuseStep 3249841 = 2437381) B2437381
theorem B4333121 : Blo 1925435 4333121 := bstep (se 2 (by rfl) ⟨1624920, by rfl⟩ : syracuseStep 4333121 = 3249841) B3249841
theorem B2888747 : Blo 1925435 2888747 := bstep (se 1 (by rfl) ⟨2166560, by rfl⟩ : syracuseStep 2888747 = 4333121) B4333121
theorem B1925831 : Blo 1925435 1925831 := bstep (se 1 (by rfl) ⟨1444373, by rfl⟩ : syracuseStep 1925831 = 2888747) B2888747
theorem B2166565 : Blo 1925435 2166565 := bbase (se 4 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 2166565 = 406231) (by norm_num)
theorem B2888753 : Blo 1925435 2888753 := bstep (se 2 (by rfl) ⟨1083282, by rfl⟩ : syracuseStep 2888753 = 2166565) B2166565
theorem B1925835 : Blo 1925435 1925835 := bstep (se 1 (by rfl) ⟨1444376, by rfl⟩ : syracuseStep 1925835 = 2888753) B2888753
theorem B8226197 : Blo 1925435 8226197 := bbase (se 6 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 8226197 = 385603) (by norm_num)
theorem B5484131 : Blo 1925435 5484131 := bstep (se 1 (by rfl) ⟨4113098, by rfl⟩ : syracuseStep 5484131 = 8226197) B8226197
theorem B3656087 : Blo 1925435 3656087 := bstep (se 1 (by rfl) ⟨2742065, by rfl⟩ : syracuseStep 3656087 = 5484131) B5484131
theorem B2437391 : Blo 1925435 2437391 := bstep (se 1 (by rfl) ⟨1828043, by rfl⟩ : syracuseStep 2437391 = 3656087) B3656087
theorem B6499709 : Blo 1925435 6499709 := bstep (se 3 (by rfl) ⟨1218695, by rfl⟩ : syracuseStep 6499709 = 2437391) B2437391
theorem B4333139 : Blo 1925435 4333139 := bstep (se 1 (by rfl) ⟨3249854, by rfl⟩ : syracuseStep 4333139 = 6499709) B6499709
theorem B2888759 : Blo 1925435 2888759 := bstep (se 1 (by rfl) ⟨2166569, by rfl⟩ : syracuseStep 2888759 = 4333139) B4333139
theorem B1925839 : Blo 1925435 1925839 := bstep (se 1 (by rfl) ⟨1444379, by rfl⟩ : syracuseStep 1925839 = 2888759) B2888759
theorem B2888765 : Blo 1925435 2888765 := bbase (se 3 (by rfl) ⟨541643, by rfl⟩ : syracuseStep 2888765 = 1083287) (by norm_num)
theorem B1925843 : Blo 1925435 1925843 := bstep (se 1 (by rfl) ⟨1444382, by rfl⟩ : syracuseStep 1925843 = 2888765) B2888765
theorem B4333157 : Blo 1925435 4333157 := bbase (se 4 (by rfl) ⟨406233, by rfl⟩ : syracuseStep 4333157 = 812467) (by norm_num)
theorem B2888771 : Blo 1925435 2888771 := bstep (se 1 (by rfl) ⟨2166578, by rfl⟩ : syracuseStep 2888771 = 4333157) B4333157
theorem B1925847 : Blo 1925435 1925847 := bstep (se 1 (by rfl) ⟨1444385, by rfl⟩ : syracuseStep 1925847 = 2888771) B2888771
theorem B4874813 : Blo 1925435 4874813 := bbase (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) (by norm_num)
theorem B3249875 : Blo 1925435 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B2166583 : Blo 1925435 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B2888777 : Blo 1925435 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B1925851 : Blo 1925435 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B3656117 : Blo 1925435 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B9749645 : Blo 1925435 9749645 := bstep (se 3 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 9749645 = 3656117) B3656117
theorem B6499763 : Blo 1925435 6499763 := bstep (se 1 (by rfl) ⟨4874822, by rfl⟩ : syracuseStep 6499763 = 9749645) B9749645
theorem B4333175 : Blo 1925435 4333175 := bstep (se 1 (by rfl) ⟨3249881, by rfl⟩ : syracuseStep 4333175 = 6499763) B6499763
theorem B2888783 : Blo 1925435 2888783 := bstep (se 1 (by rfl) ⟨2166587, by rfl⟩ : syracuseStep 2888783 = 4333175) B4333175
theorem B1925855 : Blo 1925435 1925855 := bstep (se 1 (by rfl) ⟨1444391, by rfl⟩ : syracuseStep 1925855 = 2888783) B2888783
theorem B2888789 : Blo 1925435 2888789 := bbase (se 8 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 2888789 = 33853) (by norm_num)
theorem B1925859 : Blo 1925435 1925859 := bstep (se 1 (by rfl) ⟨1444394, by rfl⟩ : syracuseStep 1925859 = 2888789) B2888789
theorem B8784629 : Blo 1925435 8784629 := bbase (se 5 (by rfl) ⟨411779, by rfl⟩ : syracuseStep 8784629 = 823559) (by norm_num)
theorem B5856419 : Blo 1925435 5856419 := bstep (se 1 (by rfl) ⟨4392314, by rfl⟩ : syracuseStep 5856419 = 8784629) B8784629
theorem B15617117 : Blo 1925435 15617117 := bstep (se 3 (by rfl) ⟨2928209, by rfl⟩ : syracuseStep 15617117 = 5856419) B5856419
theorem B10411411 : Blo 1925435 10411411 := bstep (se 1 (by rfl) ⟨7808558, by rfl⟩ : syracuseStep 10411411 = 15617117) B15617117
theorem B13881881 : Blo 1925435 13881881 := bstep (se 2 (by rfl) ⟨5205705, by rfl⟩ : syracuseStep 13881881 = 10411411) B10411411
theorem B9254587 : Blo 1925435 9254587 := bstep (se 1 (by rfl) ⟨6940940, by rfl⟩ : syracuseStep 9254587 = 13881881) B13881881
theorem B12339449 : Blo 1925435 12339449 := bstep (se 2 (by rfl) ⟨4627293, by rfl⟩ : syracuseStep 12339449 = 9254587) B9254587
theorem B8226299 : Blo 1925435 8226299 := bstep (se 1 (by rfl) ⟨6169724, by rfl⟩ : syracuseStep 8226299 = 12339449) B12339449
theorem B5484199 : Blo 1925435 5484199 := bstep (se 1 (by rfl) ⟨4113149, by rfl⟩ : syracuseStep 5484199 = 8226299) B8226299
theorem B7312265 : Blo 1925435 7312265 := bstep (se 2 (by rfl) ⟨2742099, by rfl⟩ : syracuseStep 7312265 = 5484199) B5484199
theorem B4874843 : Blo 1925435 4874843 := bstep (se 1 (by rfl) ⟨3656132, by rfl⟩ : syracuseStep 4874843 = 7312265) B7312265
theorem B3249895 : Blo 1925435 3249895 := bstep (se 1 (by rfl) ⟨2437421, by rfl⟩ : syracuseStep 3249895 = 4874843) B4874843
theorem B4333193 : Blo 1925435 4333193 := bstep (se 2 (by rfl) ⟨1624947, by rfl⟩ : syracuseStep 4333193 = 3249895) B3249895
theorem B2888795 : Blo 1925435 2888795 := bstep (se 1 (by rfl) ⟨2166596, by rfl⟩ : syracuseStep 2888795 = 4333193) B4333193
theorem B1925863 : Blo 1925435 1925863 := bstep (se 1 (by rfl) ⟨1444397, by rfl⟩ : syracuseStep 1925863 = 2888795) B2888795
theorem B2166601 : Blo 1925435 2166601 := bbase (se 2 (by rfl) ⟨812475, by rfl⟩ : syracuseStep 2166601 = 1624951) (by norm_num)
theorem B2888801 : Blo 1925435 2888801 := bstep (se 2 (by rfl) ⟨1083300, by rfl⟩ : syracuseStep 2888801 = 2166601) B2166601
theorem B1925867 : Blo 1925435 1925867 := bstep (se 1 (by rfl) ⟨1444400, by rfl⟩ : syracuseStep 1925867 = 2888801) B2888801
theorem B3957565 : Blo 1925435 3957565 := bbase (se 3 (by rfl) ⟨742043, by rfl⟩ : syracuseStep 3957565 = 1484087) (by norm_num)
theorem B5276753 : Blo 1925435 5276753 := bstep (se 2 (by rfl) ⟨1978782, by rfl⟩ : syracuseStep 5276753 = 3957565) B3957565
theorem B3517835 : Blo 1925435 3517835 := bstep (se 1 (by rfl) ⟨2638376, by rfl⟩ : syracuseStep 3517835 = 5276753) B5276753
theorem B9380893 : Blo 1925435 9380893 := bstep (se 3 (by rfl) ⟨1758917, by rfl⟩ : syracuseStep 9380893 = 3517835) B3517835
theorem B12507857 : Blo 1925435 12507857 := bstep (se 2 (by rfl) ⟨4690446, by rfl⟩ : syracuseStep 12507857 = 9380893) B9380893
theorem B8338571 : Blo 1925435 8338571 := bstep (se 1 (by rfl) ⟨6253928, by rfl⟩ : syracuseStep 8338571 = 12507857) B12507857
theorem B5559047 : Blo 1925435 5559047 := bstep (se 1 (by rfl) ⟨4169285, by rfl⟩ : syracuseStep 5559047 = 8338571) B8338571
theorem B3706031 : Blo 1925435 3706031 := bstep (se 1 (by rfl) ⟨2779523, by rfl⟩ : syracuseStep 3706031 = 5559047) B5559047
theorem B9882749 : Blo 1925435 9882749 := bstep (se 3 (by rfl) ⟨1853015, by rfl⟩ : syracuseStep 9882749 = 3706031) B3706031
theorem B6588499 : Blo 1925435 6588499 := bstep (se 1 (by rfl) ⟨4941374, by rfl⟩ : syracuseStep 6588499 = 9882749) B9882749
theorem B8784665 : Blo 1925435 8784665 := bstep (se 2 (by rfl) ⟨3294249, by rfl⟩ : syracuseStep 8784665 = 6588499) B6588499
theorem B5856443 : Blo 1925435 5856443 := bstep (se 1 (by rfl) ⟨4392332, by rfl⟩ : syracuseStep 5856443 = 8784665) B8784665
theorem B3904295 : Blo 1925435 3904295 := bstep (se 1 (by rfl) ⟨2928221, by rfl⟩ : syracuseStep 3904295 = 5856443) B5856443
theorem B10411453 : Blo 1925435 10411453 := bstep (se 3 (by rfl) ⟨1952147, by rfl⟩ : syracuseStep 10411453 = 3904295) B3904295
theorem B13881937 : Blo 1925435 13881937 := bstep (se 2 (by rfl) ⟨5205726, by rfl⟩ : syracuseStep 13881937 = 10411453) B10411453
theorem B18509249 : Blo 1925435 18509249 := bstep (se 2 (by rfl) ⟨6940968, by rfl⟩ : syracuseStep 18509249 = 13881937) B13881937
theorem B12339499 : Blo 1925435 12339499 := bstep (se 1 (by rfl) ⟨9254624, by rfl⟩ : syracuseStep 12339499 = 18509249) B18509249
theorem B16452665 : Blo 1925435 16452665 := bstep (se 2 (by rfl) ⟨6169749, by rfl⟩ : syracuseStep 16452665 = 12339499) B12339499
theorem B10968443 : Blo 1925435 10968443 := bstep (se 1 (by rfl) ⟨8226332, by rfl⟩ : syracuseStep 10968443 = 16452665) B16452665
theorem B7312295 : Blo 1925435 7312295 := bstep (se 1 (by rfl) ⟨5484221, by rfl⟩ : syracuseStep 7312295 = 10968443) B10968443
theorem B4874863 : Blo 1925435 4874863 := bstep (se 1 (by rfl) ⟨3656147, by rfl⟩ : syracuseStep 4874863 = 7312295) B7312295
theorem B6499817 : Blo 1925435 6499817 := bstep (se 2 (by rfl) ⟨2437431, by rfl⟩ : syracuseStep 6499817 = 4874863) B4874863
theorem B4333211 : Blo 1925435 4333211 := bstep (se 1 (by rfl) ⟨3249908, by rfl⟩ : syracuseStep 4333211 = 6499817) B6499817
theorem B2888807 : Blo 1925435 2888807 := bstep (se 1 (by rfl) ⟨2166605, by rfl⟩ : syracuseStep 2888807 = 4333211) B4333211
theorem B1925871 : Blo 1925435 1925871 := bstep (se 1 (by rfl) ⟨1444403, by rfl⟩ : syracuseStep 1925871 = 2888807) B2888807
theorem B2888813 : Blo 1925435 2888813 := bbase (se 3 (by rfl) ⟨541652, by rfl⟩ : syracuseStep 2888813 = 1083305) (by norm_num)
theorem B1925875 : Blo 1925435 1925875 := bstep (se 1 (by rfl) ⟨1444406, by rfl⟩ : syracuseStep 1925875 = 2888813) B2888813
theorem B4333229 : Blo 1925435 4333229 := bbase (se 3 (by rfl) ⟨812480, by rfl⟩ : syracuseStep 4333229 = 1624961) (by norm_num)
theorem B2888819 : Blo 1925435 2888819 := bstep (se 1 (by rfl) ⟨2166614, by rfl⟩ : syracuseStep 2888819 = 4333229) B4333229
theorem B1925879 : Blo 1925435 1925879 := bstep (se 1 (by rfl) ⟨1444409, by rfl⟩ : syracuseStep 1925879 = 2888819) B2888819
theorem B2196181 : Blo 1925435 2196181 := bbase (se 7 (by rfl) ⟨25736, by rfl⟩ : syracuseStep 2196181 = 51473) (by norm_num)
theorem B2928241 : Blo 1925435 2928241 := bstep (se 2 (by rfl) ⟨1098090, by rfl⟩ : syracuseStep 2928241 = 2196181) B2196181
theorem B15617285 : Blo 1925435 15617285 := bstep (se 4 (by rfl) ⟨1464120, by rfl⟩ : syracuseStep 15617285 = 2928241) B2928241
theorem B10411523 : Blo 1925435 10411523 := bstep (se 1 (by rfl) ⟨7808642, by rfl⟩ : syracuseStep 10411523 = 15617285) B15617285
theorem B6941015 : Blo 1925435 6941015 := bstep (se 1 (by rfl) ⟨5205761, by rfl⟩ : syracuseStep 6941015 = 10411523) B10411523
theorem B4627343 : Blo 1925435 4627343 := bstep (se 1 (by rfl) ⟨3470507, by rfl⟩ : syracuseStep 4627343 = 6941015) B6941015
theorem B3084895 : Blo 1925435 3084895 := bstep (se 1 (by rfl) ⟨2313671, by rfl⟩ : syracuseStep 3084895 = 4627343) B4627343
theorem B4113193 : Blo 1925435 4113193 := bstep (se 2 (by rfl) ⟨1542447, by rfl⟩ : syracuseStep 4113193 = 3084895) B3084895
theorem B5484257 : Blo 1925435 5484257 := bstep (se 2 (by rfl) ⟨2056596, by rfl⟩ : syracuseStep 5484257 = 4113193) B4113193
theorem B3656171 : Blo 1925435 3656171 := bstep (se 1 (by rfl) ⟨2742128, by rfl⟩ : syracuseStep 3656171 = 5484257) B5484257
theorem B2437447 : Blo 1925435 2437447 := bstep (se 1 (by rfl) ⟨1828085, by rfl⟩ : syracuseStep 2437447 = 3656171) B3656171
theorem B3249929 : Blo 1925435 3249929 := bstep (se 2 (by rfl) ⟨1218723, by rfl⟩ : syracuseStep 3249929 = 2437447) B2437447
theorem B2166619 : Blo 1925435 2166619 := bstep (se 1 (by rfl) ⟨1624964, by rfl⟩ : syracuseStep 2166619 = 3249929) B3249929
theorem B2888825 : Blo 1925435 2888825 := bstep (se 2 (by rfl) ⟨1083309, by rfl⟩ : syracuseStep 2888825 = 2166619) B2166619
theorem B1925883 : Blo 1925435 1925883 := bstep (se 1 (by rfl) ⟨1444412, by rfl⟩ : syracuseStep 1925883 = 2888825) B2888825
theorem B2504417 : Blo 1925435 2504417 := bbase (se 2 (by rfl) ⟨939156, by rfl⟩ : syracuseStep 2504417 = 1878313) (by norm_num)
theorem B6678445 : Blo 1925435 6678445 := bstep (se 3 (by rfl) ⟨1252208, by rfl⟩ : syracuseStep 6678445 = 2504417) B2504417
theorem B8904593 : Blo 1925435 8904593 := bstep (se 2 (by rfl) ⟨3339222, by rfl⟩ : syracuseStep 8904593 = 6678445) B6678445
theorem B23745581 : Blo 1925435 23745581 := bstep (se 3 (by rfl) ⟨4452296, by rfl⟩ : syracuseStep 23745581 = 8904593) B8904593
theorem B15830387 : Blo 1925435 15830387 := bstep (se 1 (by rfl) ⟨11872790, by rfl⟩ : syracuseStep 15830387 = 23745581) B23745581
theorem B10553591 : Blo 1925435 10553591 := bstep (se 1 (by rfl) ⟨7915193, by rfl⟩ : syracuseStep 10553591 = 15830387) B15830387
theorem B28142909 : Blo 1925435 28142909 := bstep (se 3 (by rfl) ⟨5276795, by rfl⟩ : syracuseStep 28142909 = 10553591) B10553591
theorem B18761939 : Blo 1925435 18761939 := bstep (se 1 (by rfl) ⟨14071454, by rfl⟩ : syracuseStep 18761939 = 28142909) B28142909
theorem B12507959 : Blo 1925435 12507959 := bstep (se 1 (by rfl) ⟨9380969, by rfl⟩ : syracuseStep 12507959 = 18761939) B18761939
theorem B8338639 : Blo 1925435 8338639 := bstep (se 1 (by rfl) ⟨6253979, by rfl⟩ : syracuseStep 8338639 = 12507959) B12507959
theorem B11118185 : Blo 1925435 11118185 := bstep (se 2 (by rfl) ⟨4169319, by rfl⟩ : syracuseStep 11118185 = 8338639) B8338639
theorem B7412123 : Blo 1925435 7412123 := bstep (se 1 (by rfl) ⟨5559092, by rfl⟩ : syracuseStep 7412123 = 11118185) B11118185
theorem B4941415 : Blo 1925435 4941415 := bstep (se 1 (by rfl) ⟨3706061, by rfl⟩ : syracuseStep 4941415 = 7412123) B7412123
theorem B6588553 : Blo 1925435 6588553 := bstep (se 2 (by rfl) ⟨2470707, by rfl⟩ : syracuseStep 6588553 = 4941415) B4941415
theorem B8784737 : Blo 1925435 8784737 := bstep (se 2 (by rfl) ⟨3294276, by rfl⟩ : syracuseStep 8784737 = 6588553) B6588553
theorem B5856491 : Blo 1925435 5856491 := bstep (se 1 (by rfl) ⟨4392368, by rfl⟩ : syracuseStep 5856491 = 8784737) B8784737
theorem B3904327 : Blo 1925435 3904327 := bstep (se 1 (by rfl) ⟨2928245, by rfl⟩ : syracuseStep 3904327 = 5856491) B5856491
theorem B20823077 : Blo 1925435 20823077 := bstep (se 4 (by rfl) ⟨1952163, by rfl⟩ : syracuseStep 20823077 = 3904327) B3904327
theorem B13882051 : Blo 1925435 13882051 := bstep (se 1 (by rfl) ⟨10411538, by rfl⟩ : syracuseStep 13882051 = 20823077) B20823077
theorem B18509401 : Blo 1925435 18509401 := bstep (se 2 (by rfl) ⟨6941025, by rfl⟩ : syracuseStep 18509401 = 13882051) B13882051
theorem B24679201 : Blo 1925435 24679201 := bstep (se 2 (by rfl) ⟨9254700, by rfl⟩ : syracuseStep 24679201 = 18509401) B18509401
theorem B32905601 : Blo 1925435 32905601 := bstep (se 2 (by rfl) ⟨12339600, by rfl⟩ : syracuseStep 32905601 = 24679201) B24679201
theorem B21937067 : Blo 1925435 21937067 := bstep (se 1 (by rfl) ⟨16452800, by rfl⟩ : syracuseStep 21937067 = 32905601) B32905601
theorem B14624711 : Blo 1925435 14624711 := bstep (se 1 (by rfl) ⟨10968533, by rfl⟩ : syracuseStep 14624711 = 21937067) B21937067
theorem B9749807 : Blo 1925435 9749807 := bstep (se 1 (by rfl) ⟨7312355, by rfl⟩ : syracuseStep 9749807 = 14624711) B14624711
theorem B6499871 : Blo 1925435 6499871 := bstep (se 1 (by rfl) ⟨4874903, by rfl⟩ : syracuseStep 6499871 = 9749807) B9749807
theorem B4333247 : Blo 1925435 4333247 := bstep (se 1 (by rfl) ⟨3249935, by rfl⟩ : syracuseStep 4333247 = 6499871) B6499871
theorem B2888831 : Blo 1925435 2888831 := bstep (se 1 (by rfl) ⟨2166623, by rfl⟩ : syracuseStep 2888831 = 4333247) B4333247
theorem B1925887 : Blo 1925435 1925887 := bstep (se 1 (by rfl) ⟨1444415, by rfl⟩ : syracuseStep 1925887 = 2888831) B2888831
theorem B2888837 : Blo 1925435 2888837 := bbase (se 4 (by rfl) ⟨270828, by rfl⟩ : syracuseStep 2888837 = 541657) (by norm_num)
theorem B1925891 : Blo 1925435 1925891 := bstep (se 1 (by rfl) ⟨1444418, by rfl⟩ : syracuseStep 1925891 = 2888837) B2888837
theorem B3249949 : Blo 1925435 3249949 := bbase (se 3 (by rfl) ⟨609365, by rfl⟩ : syracuseStep 3249949 = 1218731) (by norm_num)
theorem B4333265 : Blo 1925435 4333265 := bstep (se 2 (by rfl) ⟨1624974, by rfl⟩ : syracuseStep 4333265 = 3249949) B3249949
theorem B2888843 : Blo 1925435 2888843 := bstep (se 1 (by rfl) ⟨2166632, by rfl⟩ : syracuseStep 2888843 = 4333265) B4333265
theorem B1925895 : Blo 1925435 1925895 := bstep (se 1 (by rfl) ⟨1444421, by rfl⟩ : syracuseStep 1925895 = 2888843) B2888843
theorem B2166637 : Blo 1925435 2166637 := bbase (se 3 (by rfl) ⟨406244, by rfl⟩ : syracuseStep 2166637 = 812489) (by norm_num)
theorem B2888849 : Blo 1925435 2888849 := bstep (se 2 (by rfl) ⟨1083318, by rfl⟩ : syracuseStep 2888849 = 2166637) B2166637
theorem B1925899 : Blo 1925435 1925899 := bstep (se 1 (by rfl) ⟨1444424, by rfl⟩ : syracuseStep 1925899 = 2888849) B2888849
theorem B6499925 : Blo 1925435 6499925 := bbase (se 8 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 6499925 = 76171) (by norm_num)
theorem B4333283 : Blo 1925435 4333283 := bstep (se 1 (by rfl) ⟨3249962, by rfl⟩ : syracuseStep 4333283 = 6499925) B6499925
theorem B2888855 : Blo 1925435 2888855 := bstep (se 1 (by rfl) ⟨2166641, by rfl⟩ : syracuseStep 2888855 = 4333283) B4333283
theorem B1925903 : Blo 1925435 1925903 := bstep (se 1 (by rfl) ⟨1444427, by rfl⟩ : syracuseStep 1925903 = 2888855) B2888855
theorem B2888861 : Blo 1925435 2888861 := bbase (se 3 (by rfl) ⟨541661, by rfl⟩ : syracuseStep 2888861 = 1083323) (by norm_num)
theorem B1925907 : Blo 1925435 1925907 := bstep (se 1 (by rfl) ⟨1444430, by rfl⟩ : syracuseStep 1925907 = 2888861) B2888861
theorem B4333301 : Blo 1925435 4333301 := bbase (se 5 (by rfl) ⟨203123, by rfl⟩ : syracuseStep 4333301 = 406247) (by norm_num)
theorem B2888867 : Blo 1925435 2888867 := bstep (se 1 (by rfl) ⟨2166650, by rfl⟩ : syracuseStep 2888867 = 4333301) B4333301
theorem B1925911 : Blo 1925435 1925911 := bstep (se 1 (by rfl) ⟨1444433, by rfl⟩ : syracuseStep 1925911 = 2888867) B2888867
theorem B9254837 : Blo 1925435 9254837 := bbase (se 5 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 9254837 = 867641) (by norm_num)
theorem B24679565 : Blo 1925435 24679565 := bstep (se 3 (by rfl) ⟨4627418, by rfl⟩ : syracuseStep 24679565 = 9254837) B9254837
theorem B16453043 : Blo 1925435 16453043 := bstep (se 1 (by rfl) ⟨12339782, by rfl⟩ : syracuseStep 16453043 = 24679565) B24679565
theorem B10968695 : Blo 1925435 10968695 := bstep (se 1 (by rfl) ⟨8226521, by rfl⟩ : syracuseStep 10968695 = 16453043) B16453043
theorem B7312463 : Blo 1925435 7312463 := bstep (se 1 (by rfl) ⟨5484347, by rfl⟩ : syracuseStep 7312463 = 10968695) B10968695
theorem B4874975 : Blo 1925435 4874975 := bstep (se 1 (by rfl) ⟨3656231, by rfl⟩ : syracuseStep 4874975 = 7312463) B7312463
theorem B3249983 : Blo 1925435 3249983 := bstep (se 1 (by rfl) ⟨2437487, by rfl⟩ : syracuseStep 3249983 = 4874975) B4874975
theorem B2166655 : Blo 1925435 2166655 := bstep (se 1 (by rfl) ⟨1624991, by rfl⟩ : syracuseStep 2166655 = 3249983) B3249983
theorem B2888873 : Blo 1925435 2888873 := bstep (se 2 (by rfl) ⟨1083327, by rfl⟩ : syracuseStep 2888873 = 2166655) B2166655
theorem B1925915 : Blo 1925435 1925915 := bstep (se 1 (by rfl) ⟨1444436, by rfl⟩ : syracuseStep 1925915 = 2888873) B2888873
theorem B4113269 : Blo 1925435 4113269 := bbase (se 5 (by rfl) ⟨192809, by rfl⟩ : syracuseStep 4113269 = 385619) (by norm_num)
theorem B2742179 : Blo 1925435 2742179 := bstep (se 1 (by rfl) ⟨2056634, by rfl⟩ : syracuseStep 2742179 = 4113269) B4113269
theorem B7312477 : Blo 1925435 7312477 := bstep (se 3 (by rfl) ⟨1371089, by rfl⟩ : syracuseStep 7312477 = 2742179) B2742179
theorem B9749969 : Blo 1925435 9749969 := bstep (se 2 (by rfl) ⟨3656238, by rfl⟩ : syracuseStep 9749969 = 7312477) B7312477
theorem B6499979 : Blo 1925435 6499979 := bstep (se 1 (by rfl) ⟨4874984, by rfl⟩ : syracuseStep 6499979 = 9749969) B9749969
theorem B4333319 : Blo 1925435 4333319 := bstep (se 1 (by rfl) ⟨3249989, by rfl⟩ : syracuseStep 4333319 = 6499979) B6499979
theorem B2888879 : Blo 1925435 2888879 := bstep (se 1 (by rfl) ⟨2166659, by rfl⟩ : syracuseStep 2888879 = 4333319) B4333319
theorem B1925919 : Blo 1925435 1925919 := bstep (se 1 (by rfl) ⟨1444439, by rfl⟩ : syracuseStep 1925919 = 2888879) B2888879
theorem B2888885 : Blo 1925435 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B1925923 : Blo 1925435 1925923 := bstep (se 1 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 1925923 = 2888885) B2888885
theorem B4875005 : Blo 1925435 4875005 := bbase (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) (by norm_num)
theorem B3250003 : Blo 1925435 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B4333337 : Blo 1925435 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B2888891 : Blo 1925435 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B1925927 : Blo 1925435 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B2166673 : Blo 1925435 2166673 := bbase (se 2 (by rfl) ⟨812502, by rfl⟩ : syracuseStep 2166673 = 1625005) (by norm_num)
theorem B2888897 : Blo 1925435 2888897 := bstep (se 2 (by rfl) ⟨1083336, by rfl⟩ : syracuseStep 2888897 = 2166673) B2166673
theorem B1925931 : Blo 1925435 1925931 := bstep (se 1 (by rfl) ⟨1444448, by rfl⟩ : syracuseStep 1925931 = 2888897) B2888897
theorem B3656269 : Blo 1925435 3656269 := bbase (se 3 (by rfl) ⟨685550, by rfl⟩ : syracuseStep 3656269 = 1371101) (by norm_num)
theorem B4875025 : Blo 1925435 4875025 := bstep (se 2 (by rfl) ⟨1828134, by rfl⟩ : syracuseStep 4875025 = 3656269) B3656269
theorem B6500033 : Blo 1925435 6500033 := bstep (se 2 (by rfl) ⟨2437512, by rfl⟩ : syracuseStep 6500033 = 4875025) B4875025
theorem B4333355 : Blo 1925435 4333355 := bstep (se 1 (by rfl) ⟨3250016, by rfl⟩ : syracuseStep 4333355 = 6500033) B6500033
theorem B2888903 : Blo 1925435 2888903 := bstep (se 1 (by rfl) ⟨2166677, by rfl⟩ : syracuseStep 2888903 = 4333355) B4333355
theorem B1925935 : Blo 1925435 1925935 := bstep (se 1 (by rfl) ⟨1444451, by rfl⟩ : syracuseStep 1925935 = 2888903) B2888903
theorem B2888909 : Blo 1925435 2888909 := bbase (se 3 (by rfl) ⟨541670, by rfl⟩ : syracuseStep 2888909 = 1083341) (by norm_num)
theorem B1925939 : Blo 1925435 1925939 := bstep (se 1 (by rfl) ⟨1444454, by rfl⟩ : syracuseStep 1925939 = 2888909) B2888909
theorem B4333373 : Blo 1925435 4333373 := bbase (se 3 (by rfl) ⟨812507, by rfl⟩ : syracuseStep 4333373 = 1625015) (by norm_num)
theorem B2888915 : Blo 1925435 2888915 := bstep (se 1 (by rfl) ⟨2166686, by rfl⟩ : syracuseStep 2888915 = 4333373) B4333373
theorem B1925943 : Blo 1925435 1925943 := bstep (se 1 (by rfl) ⟨1444457, by rfl⟩ : syracuseStep 1925943 = 2888915) B2888915
theorem B3250037 : Blo 1925435 3250037 := bbase (se 5 (by rfl) ⟨152345, by rfl⟩ : syracuseStep 3250037 = 304691) (by norm_num)
theorem B2166691 : Blo 1925435 2166691 := bstep (se 1 (by rfl) ⟨1625018, by rfl⟩ : syracuseStep 2166691 = 3250037) B3250037
theorem B2888921 : Blo 1925435 2888921 := bstep (se 2 (by rfl) ⟨1083345, by rfl⟩ : syracuseStep 2888921 = 2166691) B2166691
theorem B1925947 : Blo 1925435 1925947 := bstep (se 1 (by rfl) ⟨1444460, by rfl⟩ : syracuseStep 1925947 = 2888921) B2888921
theorem B3470629 : Blo 1925435 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B4627505 : Blo 1925435 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B3085003 : Blo 1925435 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B4113337 : Blo 1925435 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B5484449 : Blo 1925435 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B14625197 : Blo 1925435 14625197 := bstep (se 3 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 14625197 = 5484449) B5484449
theorem B9750131 : Blo 1925435 9750131 := bstep (se 1 (by rfl) ⟨7312598, by rfl⟩ : syracuseStep 9750131 = 14625197) B14625197
theorem B6500087 : Blo 1925435 6500087 := bstep (se 1 (by rfl) ⟨4875065, by rfl⟩ : syracuseStep 6500087 = 9750131) B9750131
theorem B4333391 : Blo 1925435 4333391 := bstep (se 1 (by rfl) ⟨3250043, by rfl⟩ : syracuseStep 4333391 = 6500087) B6500087
theorem B2888927 : Blo 1925435 2888927 := bstep (se 1 (by rfl) ⟨2166695, by rfl⟩ : syracuseStep 2888927 = 4333391) B4333391
theorem B1925951 : Blo 1925435 1925951 := bstep (se 1 (by rfl) ⟨1444463, by rfl⟩ : syracuseStep 1925951 = 2888927) B2888927
theorem B2888933 : Blo 1925435 2888933 := bbase (se 4 (by rfl) ⟨270837, by rfl⟩ : syracuseStep 2888933 = 541675) (by norm_num)
theorem B1925955 : Blo 1925435 1925955 := bstep (se 1 (by rfl) ⟨1444466, by rfl⟩ : syracuseStep 1925955 = 2888933) B2888933
theorem B4627525 : Blo 1925435 4627525 := bbase (se 4 (by rfl) ⟨433830, by rfl⟩ : syracuseStep 4627525 = 867661) (by norm_num)
theorem B6170033 : Blo 1925435 6170033 := bstep (se 2 (by rfl) ⟨2313762, by rfl⟩ : syracuseStep 6170033 = 4627525) B4627525
theorem B4113355 : Blo 1925435 4113355 := bstep (se 1 (by rfl) ⟨3085016, by rfl⟩ : syracuseStep 4113355 = 6170033) B6170033
theorem B5484473 : Blo 1925435 5484473 := bstep (se 2 (by rfl) ⟨2056677, by rfl⟩ : syracuseStep 5484473 = 4113355) B4113355
theorem B3656315 : Blo 1925435 3656315 := bstep (se 1 (by rfl) ⟨2742236, by rfl⟩ : syracuseStep 3656315 = 5484473) B5484473
theorem B2437543 : Blo 1925435 2437543 := bstep (se 1 (by rfl) ⟨1828157, by rfl⟩ : syracuseStep 2437543 = 3656315) B3656315
theorem B3250057 : Blo 1925435 3250057 := bstep (se 2 (by rfl) ⟨1218771, by rfl⟩ : syracuseStep 3250057 = 2437543) B2437543
theorem B4333409 : Blo 1925435 4333409 := bstep (se 2 (by rfl) ⟨1625028, by rfl⟩ : syracuseStep 4333409 = 3250057) B3250057
theorem B2888939 : Blo 1925435 2888939 := bstep (se 1 (by rfl) ⟨2166704, by rfl⟩ : syracuseStep 2888939 = 4333409) B4333409
theorem B1925959 : Blo 1925435 1925959 := bstep (se 1 (by rfl) ⟨1444469, by rfl⟩ : syracuseStep 1925959 = 2888939) B2888939
theorem B2166709 : Blo 1925435 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B2888945 : Blo 1925435 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B1925963 : Blo 1925435 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B2437553 : Blo 1925435 2437553 := bbase (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) (by norm_num)
theorem B6500141 : Blo 1925435 6500141 := bstep (se 3 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 6500141 = 2437553) B2437553
theorem B4333427 : Blo 1925435 4333427 := bstep (se 1 (by rfl) ⟨3250070, by rfl⟩ : syracuseStep 4333427 = 6500141) B6500141
theorem B2888951 : Blo 1925435 2888951 := bstep (se 1 (by rfl) ⟨2166713, by rfl⟩ : syracuseStep 2888951 = 4333427) B4333427
theorem B1925967 : Blo 1925435 1925967 := bstep (se 1 (by rfl) ⟨1444475, by rfl⟩ : syracuseStep 1925967 = 2888951) B2888951
theorem B2888957 : Blo 1925435 2888957 := bbase (se 3 (by rfl) ⟨541679, by rfl⟩ : syracuseStep 2888957 = 1083359) (by norm_num)
theorem B1925971 : Blo 1925435 1925971 := bstep (se 1 (by rfl) ⟨1444478, by rfl⟩ : syracuseStep 1925971 = 2888957) B2888957
theorem B4333445 : Blo 1925435 4333445 := bbase (se 4 (by rfl) ⟨406260, by rfl⟩ : syracuseStep 4333445 = 812521) (by norm_num)
theorem B2888963 : Blo 1925435 2888963 := bstep (se 1 (by rfl) ⟨2166722, by rfl⟩ : syracuseStep 2888963 = 4333445) B4333445
theorem B1925975 : Blo 1925435 1925975 := bstep (se 1 (by rfl) ⟨1444481, by rfl⟩ : syracuseStep 1925975 = 2888963) B2888963
theorem B3904517 : Blo 1925435 3904517 := bbase (se 4 (by rfl) ⟨366048, by rfl⟩ : syracuseStep 3904517 = 732097) (by norm_num)
theorem B2603011 : Blo 1925435 2603011 := bstep (se 1 (by rfl) ⟨1952258, by rfl⟩ : syracuseStep 2603011 = 3904517) B3904517
theorem B3470681 : Blo 1925435 3470681 := bstep (se 2 (by rfl) ⟨1301505, by rfl⟩ : syracuseStep 3470681 = 2603011) B2603011
theorem B2313787 : Blo 1925435 2313787 := bstep (se 1 (by rfl) ⟨1735340, by rfl⟩ : syracuseStep 2313787 = 3470681) B3470681
theorem B3085049 : Blo 1925435 3085049 := bstep (se 2 (by rfl) ⟨1156893, by rfl⟩ : syracuseStep 3085049 = 2313787) B2313787
theorem B2056699 : Blo 1925435 2056699 := bstep (se 1 (by rfl) ⟨1542524, by rfl⟩ : syracuseStep 2056699 = 3085049) B3085049
theorem B2742265 : Blo 1925435 2742265 := bstep (se 2 (by rfl) ⟨1028349, by rfl⟩ : syracuseStep 2742265 = 2056699) B2056699
theorem B3656353 : Blo 1925435 3656353 := bstep (se 2 (by rfl) ⟨1371132, by rfl⟩ : syracuseStep 3656353 = 2742265) B2742265
theorem B4875137 : Blo 1925435 4875137 := bstep (se 2 (by rfl) ⟨1828176, by rfl⟩ : syracuseStep 4875137 = 3656353) B3656353
theorem B3250091 : Blo 1925435 3250091 := bstep (se 1 (by rfl) ⟨2437568, by rfl⟩ : syracuseStep 3250091 = 4875137) B4875137
theorem B2166727 : Blo 1925435 2166727 := bstep (se 1 (by rfl) ⟨1625045, by rfl⟩ : syracuseStep 2166727 = 3250091) B3250091
theorem B2888969 : Blo 1925435 2888969 := bstep (se 2 (by rfl) ⟨1083363, by rfl⟩ : syracuseStep 2888969 = 2166727) B2166727
theorem B1925979 : Blo 1925435 1925979 := bstep (se 1 (by rfl) ⟨1444484, by rfl⟩ : syracuseStep 1925979 = 2888969) B2888969
theorem B9750293 : Blo 1925435 9750293 := bbase (se 6 (by rfl) ⟨228522, by rfl⟩ : syracuseStep 9750293 = 457045) (by norm_num)
theorem B6500195 : Blo 1925435 6500195 := bstep (se 1 (by rfl) ⟨4875146, by rfl⟩ : syracuseStep 6500195 = 9750293) B9750293
theorem B4333463 : Blo 1925435 4333463 := bstep (se 1 (by rfl) ⟨3250097, by rfl⟩ : syracuseStep 4333463 = 6500195) B6500195
theorem B2888975 : Blo 1925435 2888975 := bstep (se 1 (by rfl) ⟨2166731, by rfl⟩ : syracuseStep 2888975 = 4333463) B4333463
theorem B1925983 : Blo 1925435 1925983 := bstep (se 1 (by rfl) ⟨1444487, by rfl⟩ : syracuseStep 1925983 = 2888975) B2888975
theorem B2888981 : Blo 1925435 2888981 := bbase (se 6 (by rfl) ⟨67710, by rfl⟩ : syracuseStep 2888981 = 135421) (by norm_num)
theorem B1925987 : Blo 1925435 1925987 := bstep (se 1 (by rfl) ⟨1444490, by rfl⟩ : syracuseStep 1925987 = 2888981) B2888981
theorem B7809077 : Blo 1925435 7809077 := bbase (se 5 (by rfl) ⟨366050, by rfl⟩ : syracuseStep 7809077 = 732101) (by norm_num)
theorem B5206051 : Blo 1925435 5206051 := bstep (se 1 (by rfl) ⟨3904538, by rfl⟩ : syracuseStep 5206051 = 7809077) B7809077
theorem B27765605 : Blo 1925435 27765605 := bstep (se 4 (by rfl) ⟨2603025, by rfl⟩ : syracuseStep 27765605 = 5206051) B5206051
theorem B18510403 : Blo 1925435 18510403 := bstep (se 1 (by rfl) ⟨13882802, by rfl⟩ : syracuseStep 18510403 = 27765605) B27765605
theorem B24680537 : Blo 1925435 24680537 := bstep (se 2 (by rfl) ⟨9255201, by rfl⟩ : syracuseStep 24680537 = 18510403) B18510403
theorem B16453691 : Blo 1925435 16453691 := bstep (se 1 (by rfl) ⟨12340268, by rfl⟩ : syracuseStep 16453691 = 24680537) B24680537
theorem B10969127 : Blo 1925435 10969127 := bstep (se 1 (by rfl) ⟨8226845, by rfl⟩ : syracuseStep 10969127 = 16453691) B16453691
theorem B7312751 : Blo 1925435 7312751 := bstep (se 1 (by rfl) ⟨5484563, by rfl⟩ : syracuseStep 7312751 = 10969127) B10969127
theorem B4875167 : Blo 1925435 4875167 := bstep (se 1 (by rfl) ⟨3656375, by rfl⟩ : syracuseStep 4875167 = 7312751) B7312751
theorem B3250111 : Blo 1925435 3250111 := bstep (se 1 (by rfl) ⟨2437583, by rfl⟩ : syracuseStep 3250111 = 4875167) B4875167
theorem B4333481 : Blo 1925435 4333481 := bstep (se 2 (by rfl) ⟨1625055, by rfl⟩ : syracuseStep 4333481 = 3250111) B3250111
theorem B2888987 : Blo 1925435 2888987 := bstep (se 1 (by rfl) ⟨2166740, by rfl⟩ : syracuseStep 2888987 = 4333481) B4333481
theorem B1925991 : Blo 1925435 1925991 := bstep (se 1 (by rfl) ⟨1444493, by rfl⟩ : syracuseStep 1925991 = 2888987) B2888987
theorem B2166745 : Blo 1925435 2166745 := bbase (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) (by norm_num)
theorem B2888993 : Blo 1925435 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B1925995 : Blo 1925435 1925995 := bstep (se 1 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 1925995 = 2888993) B2888993
theorem B2742293 : Blo 1925435 2742293 := bbase (se 6 (by rfl) ⟨64272, by rfl⟩ : syracuseStep 2742293 = 128545) (by norm_num)
theorem B7312781 : Blo 1925435 7312781 := bstep (se 3 (by rfl) ⟨1371146, by rfl⟩ : syracuseStep 7312781 = 2742293) B2742293
theorem B4875187 : Blo 1925435 4875187 := bstep (se 1 (by rfl) ⟨3656390, by rfl⟩ : syracuseStep 4875187 = 7312781) B7312781
theorem B6500249 : Blo 1925435 6500249 := bstep (se 2 (by rfl) ⟨2437593, by rfl⟩ : syracuseStep 6500249 = 4875187) B4875187
theorem B4333499 : Blo 1925435 4333499 := bstep (se 1 (by rfl) ⟨3250124, by rfl⟩ : syracuseStep 4333499 = 6500249) B6500249
theorem B2888999 : Blo 1925435 2888999 := bstep (se 1 (by rfl) ⟨2166749, by rfl⟩ : syracuseStep 2888999 = 4333499) B4333499
theorem B1925999 : Blo 1925435 1925999 := bstep (se 1 (by rfl) ⟨1444499, by rfl⟩ : syracuseStep 1925999 = 2888999) B2888999
theorem B2889005 : Blo 1925435 2889005 := bbase (se 3 (by rfl) ⟨541688, by rfl⟩ : syracuseStep 2889005 = 1083377) (by norm_num)
theorem B1926003 : Blo 1925435 1926003 := bstep (se 1 (by rfl) ⟨1444502, by rfl⟩ : syracuseStep 1926003 = 2889005) B2889005
theorem B4333517 : Blo 1925435 4333517 := bbase (se 3 (by rfl) ⟨812534, by rfl⟩ : syracuseStep 4333517 = 1625069) (by norm_num)
theorem B2889011 : Blo 1925435 2889011 := bstep (se 1 (by rfl) ⟨2166758, by rfl⟩ : syracuseStep 2889011 = 4333517) B4333517
theorem B1926007 : Blo 1925435 1926007 := bstep (se 1 (by rfl) ⟨1444505, by rfl⟩ : syracuseStep 1926007 = 2889011) B2889011
theorem B2437609 : Blo 1925435 2437609 := bbase (se 2 (by rfl) ⟨914103, by rfl⟩ : syracuseStep 2437609 = 1828207) (by norm_num)
theorem B3250145 : Blo 1925435 3250145 := bstep (se 2 (by rfl) ⟨1218804, by rfl⟩ : syracuseStep 3250145 = 2437609) B2437609
theorem B2166763 : Blo 1925435 2166763 := bstep (se 1 (by rfl) ⟨1625072, by rfl⟩ : syracuseStep 2166763 = 3250145) B3250145
theorem B2889017 : Blo 1925435 2889017 := bstep (se 2 (by rfl) ⟨1083381, by rfl⟩ : syracuseStep 2889017 = 2166763) B2166763
theorem B1926011 : Blo 1925435 1926011 := bstep (se 1 (by rfl) ⟨1444508, by rfl⟩ : syracuseStep 1926011 = 2889017) B2889017
theorem B2313829 : Blo 1925435 2313829 := bbase (se 4 (by rfl) ⟨216921, by rfl⟩ : syracuseStep 2313829 = 433843) (by norm_num)
theorem B12340421 : Blo 1925435 12340421 := bstep (se 4 (by rfl) ⟨1156914, by rfl⟩ : syracuseStep 12340421 = 2313829) B2313829
theorem B8226947 : Blo 1925435 8226947 := bstep (se 1 (by rfl) ⟨6170210, by rfl⟩ : syracuseStep 8226947 = 12340421) B12340421
theorem B21938525 : Blo 1925435 21938525 := bstep (se 3 (by rfl) ⟨4113473, by rfl⟩ : syracuseStep 21938525 = 8226947) B8226947
theorem B14625683 : Blo 1925435 14625683 := bstep (se 1 (by rfl) ⟨10969262, by rfl⟩ : syracuseStep 14625683 = 21938525) B21938525
theorem B9750455 : Blo 1925435 9750455 := bstep (se 1 (by rfl) ⟨7312841, by rfl⟩ : syracuseStep 9750455 = 14625683) B14625683
theorem B6500303 : Blo 1925435 6500303 := bstep (se 1 (by rfl) ⟨4875227, by rfl⟩ : syracuseStep 6500303 = 9750455) B9750455
theorem B4333535 : Blo 1925435 4333535 := bstep (se 1 (by rfl) ⟨3250151, by rfl⟩ : syracuseStep 4333535 = 6500303) B6500303
theorem B2889023 : Blo 1925435 2889023 := bstep (se 1 (by rfl) ⟨2166767, by rfl⟩ : syracuseStep 2889023 = 4333535) B4333535
theorem B1926015 : Blo 1925435 1926015 := bstep (se 1 (by rfl) ⟨1444511, by rfl⟩ : syracuseStep 1926015 = 2889023) B2889023
theorem B2889029 : Blo 1925435 2889029 := bbase (se 4 (by rfl) ⟨270846, by rfl⟩ : syracuseStep 2889029 = 541693) (by norm_num)
theorem B1926019 : Blo 1925435 1926019 := bstep (se 1 (by rfl) ⟨1444514, by rfl⟩ : syracuseStep 1926019 = 2889029) B2889029
theorem B3250165 : Blo 1925435 3250165 := bbase (se 5 (by rfl) ⟨152351, by rfl⟩ : syracuseStep 3250165 = 304703) (by norm_num)
theorem B4333553 : Blo 1925435 4333553 := bstep (se 2 (by rfl) ⟨1625082, by rfl⟩ : syracuseStep 4333553 = 3250165) B3250165
theorem B2889035 : Blo 1925435 2889035 := bstep (se 1 (by rfl) ⟨2166776, by rfl⟩ : syracuseStep 2889035 = 4333553) B4333553
theorem B1926023 : Blo 1925435 1926023 := bstep (se 1 (by rfl) ⟨1444517, by rfl⟩ : syracuseStep 1926023 = 2889035) B2889035
theorem B2166781 : Blo 1925435 2166781 := bbase (se 3 (by rfl) ⟨406271, by rfl⟩ : syracuseStep 2166781 = 812543) (by norm_num)
theorem B2889041 : Blo 1925435 2889041 := bstep (se 2 (by rfl) ⟨1083390, by rfl⟩ : syracuseStep 2889041 = 2166781) B2166781
theorem B1926027 : Blo 1925435 1926027 := bstep (se 1 (by rfl) ⟨1444520, by rfl⟩ : syracuseStep 1926027 = 2889041) B2889041
theorem B6500357 : Blo 1925435 6500357 := bbase (se 4 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 6500357 = 1218817) (by norm_num)
theorem B4333571 : Blo 1925435 4333571 := bstep (se 1 (by rfl) ⟨3250178, by rfl⟩ : syracuseStep 4333571 = 6500357) B6500357
theorem B2889047 : Blo 1925435 2889047 := bstep (se 1 (by rfl) ⟨2166785, by rfl⟩ : syracuseStep 2889047 = 4333571) B4333571
theorem B1926031 : Blo 1925435 1926031 := bstep (se 1 (by rfl) ⟨1444523, by rfl⟩ : syracuseStep 1926031 = 2889047) B2889047
theorem B2889053 : Blo 1925435 2889053 := bbase (se 3 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 2889053 = 1083395) (by norm_num)
theorem B1926035 : Blo 1925435 1926035 := bstep (se 1 (by rfl) ⟨1444526, by rfl⟩ : syracuseStep 1926035 = 2889053) B2889053
theorem B4333589 : Blo 1925435 4333589 := bbase (se 6 (by rfl) ⟨101568, by rfl⟩ : syracuseStep 4333589 = 203137) (by norm_num)
theorem B2889059 : Blo 1925435 2889059 := bstep (se 1 (by rfl) ⟨2166794, by rfl⟩ : syracuseStep 2889059 = 4333589) B4333589
theorem B1926039 : Blo 1925435 1926039 := bstep (se 1 (by rfl) ⟨1444529, by rfl⟩ : syracuseStep 1926039 = 2889059) B2889059
theorem B7312949 : Blo 1925435 7312949 := bbase (se 5 (by rfl) ⟨342794, by rfl⟩ : syracuseStep 7312949 = 685589) (by norm_num)
theorem B4875299 : Blo 1925435 4875299 := bstep (se 1 (by rfl) ⟨3656474, by rfl⟩ : syracuseStep 4875299 = 7312949) B7312949
theorem B3250199 : Blo 1925435 3250199 := bstep (se 1 (by rfl) ⟨2437649, by rfl⟩ : syracuseStep 3250199 = 4875299) B4875299
theorem B2166799 : Blo 1925435 2166799 := bstep (se 1 (by rfl) ⟨1625099, by rfl⟩ : syracuseStep 2166799 = 3250199) B3250199
theorem B2889065 : Blo 1925435 2889065 := bstep (se 2 (by rfl) ⟨1083399, by rfl⟩ : syracuseStep 2889065 = 2166799) B2166799
theorem B1926043 : Blo 1925435 1926043 := bstep (se 1 (by rfl) ⟨1444532, by rfl⟩ : syracuseStep 1926043 = 2889065) B2889065
theorem B3085157 : Blo 1925435 3085157 := bbase (se 4 (by rfl) ⟨289233, by rfl⟩ : syracuseStep 3085157 = 578467) (by norm_num)
theorem B2056771 : Blo 1925435 2056771 := bstep (se 1 (by rfl) ⟨1542578, by rfl⟩ : syracuseStep 2056771 = 3085157) B3085157
theorem B10969445 : Blo 1925435 10969445 := bstep (se 4 (by rfl) ⟨1028385, by rfl⟩ : syracuseStep 10969445 = 2056771) B2056771
theorem B7312963 : Blo 1925435 7312963 := bstep (se 1 (by rfl) ⟨5484722, by rfl⟩ : syracuseStep 7312963 = 10969445) B10969445
theorem B9750617 : Blo 1925435 9750617 := bstep (se 2 (by rfl) ⟨3656481, by rfl⟩ : syracuseStep 9750617 = 7312963) B7312963
theorem B6500411 : Blo 1925435 6500411 := bstep (se 1 (by rfl) ⟨4875308, by rfl⟩ : syracuseStep 6500411 = 9750617) B9750617
theorem B4333607 : Blo 1925435 4333607 := bstep (se 1 (by rfl) ⟨3250205, by rfl⟩ : syracuseStep 4333607 = 6500411) B6500411
theorem B2889071 : Blo 1925435 2889071 := bstep (se 1 (by rfl) ⟨2166803, by rfl⟩ : syracuseStep 2889071 = 4333607) B4333607
theorem B1926047 : Blo 1925435 1926047 := bstep (se 1 (by rfl) ⟨1444535, by rfl⟩ : syracuseStep 1926047 = 2889071) B2889071
theorem B2889077 : Blo 1925435 2889077 := bbase (se 5 (by rfl) ⟨135425, by rfl⟩ : syracuseStep 2889077 = 270851) (by norm_num)
theorem B1926051 : Blo 1925435 1926051 := bstep (se 1 (by rfl) ⟨1444538, by rfl⟩ : syracuseStep 1926051 = 2889077) B2889077
theorem B2742373 : Blo 1925435 2742373 := bbase (se 4 (by rfl) ⟨257097, by rfl⟩ : syracuseStep 2742373 = 514195) (by norm_num)
theorem B3656497 : Blo 1925435 3656497 := bstep (se 2 (by rfl) ⟨1371186, by rfl⟩ : syracuseStep 3656497 = 2742373) B2742373
theorem B4875329 : Blo 1925435 4875329 := bstep (se 2 (by rfl) ⟨1828248, by rfl⟩ : syracuseStep 4875329 = 3656497) B3656497
theorem B3250219 : Blo 1925435 3250219 := bstep (se 1 (by rfl) ⟨2437664, by rfl⟩ : syracuseStep 3250219 = 4875329) B4875329
theorem B4333625 : Blo 1925435 4333625 := bstep (se 2 (by rfl) ⟨1625109, by rfl⟩ : syracuseStep 4333625 = 3250219) B3250219
theorem B2889083 : Blo 1925435 2889083 := bstep (se 1 (by rfl) ⟨2166812, by rfl⟩ : syracuseStep 2889083 = 4333625) B4333625
theorem B1926055 : Blo 1925435 1926055 := bstep (se 1 (by rfl) ⟨1444541, by rfl⟩ : syracuseStep 1926055 = 2889083) B2889083
theorem B2166817 : Blo 1925435 2166817 := bbase (se 2 (by rfl) ⟨812556, by rfl⟩ : syracuseStep 2166817 = 1625113) (by norm_num)
theorem B2889089 : Blo 1925435 2889089 := bstep (se 2 (by rfl) ⟨1083408, by rfl⟩ : syracuseStep 2889089 = 2166817) B2166817
theorem B1926059 : Blo 1925435 1926059 := bstep (se 1 (by rfl) ⟨1444544, by rfl⟩ : syracuseStep 1926059 = 2889089) B2889089
theorem B4875349 : Blo 1925435 4875349 := bbase (se 8 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 4875349 = 57133) (by norm_num)
theorem B6500465 : Blo 1925435 6500465 := bstep (se 2 (by rfl) ⟨2437674, by rfl⟩ : syracuseStep 6500465 = 4875349) B4875349
theorem B4333643 : Blo 1925435 4333643 := bstep (se 1 (by rfl) ⟨3250232, by rfl⟩ : syracuseStep 4333643 = 6500465) B6500465
theorem B2889095 : Blo 1925435 2889095 := bstep (se 1 (by rfl) ⟨2166821, by rfl⟩ : syracuseStep 2889095 = 4333643) B4333643
theorem B1926063 : Blo 1925435 1926063 := bstep (se 1 (by rfl) ⟨1444547, by rfl⟩ : syracuseStep 1926063 = 2889095) B2889095
theorem B2889101 : Blo 1925435 2889101 := bbase (se 3 (by rfl) ⟨541706, by rfl⟩ : syracuseStep 2889101 = 1083413) (by norm_num)
theorem B1926067 : Blo 1925435 1926067 := bstep (se 1 (by rfl) ⟨1444550, by rfl⟩ : syracuseStep 1926067 = 2889101) B2889101
theorem B4333661 : Blo 1925435 4333661 := bbase (se 3 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 4333661 = 1625123) (by norm_num)
theorem B2889107 : Blo 1925435 2889107 := bstep (se 1 (by rfl) ⟨2166830, by rfl⟩ : syracuseStep 2889107 = 4333661) B4333661
theorem B1926071 : Blo 1925435 1926071 := bstep (se 1 (by rfl) ⟨1444553, by rfl⟩ : syracuseStep 1926071 = 2889107) B2889107
theorem B3250253 : Blo 1925435 3250253 := bbase (se 3 (by rfl) ⟨609422, by rfl⟩ : syracuseStep 3250253 = 1218845) (by norm_num)
theorem B2166835 : Blo 1925435 2166835 := bstep (se 1 (by rfl) ⟨1625126, by rfl⟩ : syracuseStep 2166835 = 3250253) B3250253
theorem B2889113 : Blo 1925435 2889113 := bstep (se 2 (by rfl) ⟨1083417, by rfl⟩ : syracuseStep 2889113 = 2166835) B2166835
theorem B1926075 : Blo 1925435 1926075 := bstep (se 1 (by rfl) ⟨1444556, by rfl⟩ : syracuseStep 1926075 = 2889113) B2889113
theorem B3294605 : Blo 1925435 3294605 := bbase (se 3 (by rfl) ⟨617738, by rfl⟩ : syracuseStep 3294605 = 1235477) (by norm_num)
theorem B2196403 : Blo 1925435 2196403 := bstep (se 1 (by rfl) ⟨1647302, by rfl⟩ : syracuseStep 2196403 = 3294605) B3294605
theorem B11714149 : Blo 1925435 11714149 := bstep (se 4 (by rfl) ⟨1098201, by rfl⟩ : syracuseStep 11714149 = 2196403) B2196403
theorem B62475461 : Blo 1925435 62475461 := bstep (se 4 (by rfl) ⟨5857074, by rfl⟩ : syracuseStep 62475461 = 11714149) B11714149
theorem B41650307 : Blo 1925435 41650307 := bstep (se 1 (by rfl) ⟨31237730, by rfl⟩ : syracuseStep 41650307 = 62475461) B62475461
theorem B27766871 : Blo 1925435 27766871 := bstep (se 1 (by rfl) ⟨20825153, by rfl⟩ : syracuseStep 27766871 = 41650307) B41650307
theorem B18511247 : Blo 1925435 18511247 := bstep (se 1 (by rfl) ⟨13883435, by rfl⟩ : syracuseStep 18511247 = 27766871) B27766871
theorem B12340831 : Blo 1925435 12340831 := bstep (se 1 (by rfl) ⟨9255623, by rfl⟩ : syracuseStep 12340831 = 18511247) B18511247
theorem B16454441 : Blo 1925435 16454441 := bstep (se 2 (by rfl) ⟨6170415, by rfl⟩ : syracuseStep 16454441 = 12340831) B12340831
theorem B10969627 : Blo 1925435 10969627 := bstep (se 1 (by rfl) ⟨8227220, by rfl⟩ : syracuseStep 10969627 = 16454441) B16454441
theorem B14626169 : Blo 1925435 14626169 := bstep (se 2 (by rfl) ⟨5484813, by rfl⟩ : syracuseStep 14626169 = 10969627) B10969627
theorem B9750779 : Blo 1925435 9750779 := bstep (se 1 (by rfl) ⟨7313084, by rfl⟩ : syracuseStep 9750779 = 14626169) B14626169
theorem B6500519 : Blo 1925435 6500519 := bstep (se 1 (by rfl) ⟨4875389, by rfl⟩ : syracuseStep 6500519 = 9750779) B9750779
theorem B4333679 : Blo 1925435 4333679 := bstep (se 1 (by rfl) ⟨3250259, by rfl⟩ : syracuseStep 4333679 = 6500519) B6500519
theorem B2889119 : Blo 1925435 2889119 := bstep (se 1 (by rfl) ⟨2166839, by rfl⟩ : syracuseStep 2889119 = 4333679) B4333679
theorem B1926079 : Blo 1925435 1926079 := bstep (se 1 (by rfl) ⟨1444559, by rfl⟩ : syracuseStep 1926079 = 2889119) B2889119
theorem B2889125 : Blo 1925435 2889125 := bbase (se 4 (by rfl) ⟨270855, by rfl⟩ : syracuseStep 2889125 = 541711) (by norm_num)
theorem B1926083 : Blo 1925435 1926083 := bstep (se 1 (by rfl) ⟨1444562, by rfl⟩ : syracuseStep 1926083 = 2889125) B2889125
theorem B2437705 : Blo 1925435 2437705 := bbase (se 2 (by rfl) ⟨914139, by rfl⟩ : syracuseStep 2437705 = 1828279) (by norm_num)
theorem B3250273 : Blo 1925435 3250273 := bstep (se 2 (by rfl) ⟨1218852, by rfl⟩ : syracuseStep 3250273 = 2437705) B2437705
theorem B4333697 : Blo 1925435 4333697 := bstep (se 2 (by rfl) ⟨1625136, by rfl⟩ : syracuseStep 4333697 = 3250273) B3250273
theorem B2889131 : Blo 1925435 2889131 := bstep (se 1 (by rfl) ⟨2166848, by rfl⟩ : syracuseStep 2889131 = 4333697) B4333697
theorem B1926087 : Blo 1925435 1926087 := bstep (se 1 (by rfl) ⟨1444565, by rfl⟩ : syracuseStep 1926087 = 2889131) B2889131
theorem B2166853 : Blo 1925435 2166853 := bbase (se 4 (by rfl) ⟨203142, by rfl⟩ : syracuseStep 2166853 = 406285) (by norm_num)
theorem B2889137 : Blo 1925435 2889137 := bstep (se 2 (by rfl) ⟨1083426, by rfl⟩ : syracuseStep 2889137 = 2166853) B2166853
theorem B1926091 : Blo 1925435 1926091 := bstep (se 1 (by rfl) ⟨1444568, by rfl⟩ : syracuseStep 1926091 = 2889137) B2889137
theorem B3656573 : Blo 1925435 3656573 := bbase (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) (by norm_num)
theorem B2437715 : Blo 1925435 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B6500573 : Blo 1925435 6500573 := bstep (se 3 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 6500573 = 2437715) B2437715
theorem B4333715 : Blo 1925435 4333715 := bstep (se 1 (by rfl) ⟨3250286, by rfl⟩ : syracuseStep 4333715 = 6500573) B6500573
theorem B2889143 : Blo 1925435 2889143 := bstep (se 1 (by rfl) ⟨2166857, by rfl⟩ : syracuseStep 2889143 = 4333715) B4333715
theorem B1926095 : Blo 1925435 1926095 := bstep (se 1 (by rfl) ⟨1444571, by rfl⟩ : syracuseStep 1926095 = 2889143) B2889143
theorem B2889149 : Blo 1925435 2889149 := bbase (se 3 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 2889149 = 1083431) (by norm_num)
theorem B1926099 : Blo 1925435 1926099 := bstep (se 1 (by rfl) ⟨1444574, by rfl⟩ : syracuseStep 1926099 = 2889149) B2889149
theorem B4333733 : Blo 1925435 4333733 := bbase (se 4 (by rfl) ⟨406287, by rfl⟩ : syracuseStep 4333733 = 812575) (by norm_num)
theorem B2889155 : Blo 1925435 2889155 := bstep (se 1 (by rfl) ⟨2166866, by rfl⟩ : syracuseStep 2889155 = 4333733) B4333733
theorem B1926103 : Blo 1925435 1926103 := bstep (se 1 (by rfl) ⟨1444577, by rfl⟩ : syracuseStep 1926103 = 2889155) B2889155
theorem B4875461 : Blo 1925435 4875461 := bbase (se 4 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 4875461 = 914149) (by norm_num)
theorem B3250307 : Blo 1925435 3250307 := bstep (se 1 (by rfl) ⟨2437730, by rfl⟩ : syracuseStep 3250307 = 4875461) B4875461
theorem B2166871 : Blo 1925435 2166871 := bstep (se 1 (by rfl) ⟨1625153, by rfl⟩ : syracuseStep 2166871 = 3250307) B3250307
theorem B2889161 : Blo 1925435 2889161 := bstep (se 2 (by rfl) ⟨1083435, by rfl⟩ : syracuseStep 2889161 = 2166871) B2166871
theorem B1926107 : Blo 1925435 1926107 := bstep (se 1 (by rfl) ⟨1444580, by rfl⟩ : syracuseStep 1926107 = 2889161) B2889161
theorem B13883669 : Blo 1925435 13883669 := bbase (se 6 (by rfl) ⟨325398, by rfl⟩ : syracuseStep 13883669 = 650797) (by norm_num)
theorem B9255779 : Blo 1925435 9255779 := bstep (se 1 (by rfl) ⟨6941834, by rfl⟩ : syracuseStep 9255779 = 13883669) B13883669
theorem B6170519 : Blo 1925435 6170519 := bstep (se 1 (by rfl) ⟨4627889, by rfl⟩ : syracuseStep 6170519 = 9255779) B9255779
theorem B4113679 : Blo 1925435 4113679 := bstep (se 1 (by rfl) ⟨3085259, by rfl⟩ : syracuseStep 4113679 = 6170519) B6170519
theorem B5484905 : Blo 1925435 5484905 := bstep (se 2 (by rfl) ⟨2056839, by rfl⟩ : syracuseStep 5484905 = 4113679) B4113679
theorem B3656603 : Blo 1925435 3656603 := bstep (se 1 (by rfl) ⟨2742452, by rfl⟩ : syracuseStep 3656603 = 5484905) B5484905
theorem B9750941 : Blo 1925435 9750941 := bstep (se 3 (by rfl) ⟨1828301, by rfl⟩ : syracuseStep 9750941 = 3656603) B3656603
theorem B6500627 : Blo 1925435 6500627 := bstep (se 1 (by rfl) ⟨4875470, by rfl⟩ : syracuseStep 6500627 = 9750941) B9750941
theorem B4333751 : Blo 1925435 4333751 := bstep (se 1 (by rfl) ⟨3250313, by rfl⟩ : syracuseStep 4333751 = 6500627) B6500627
theorem B2889167 : Blo 1925435 2889167 := bstep (se 1 (by rfl) ⟨2166875, by rfl⟩ : syracuseStep 2889167 = 4333751) B4333751
theorem B1926111 : Blo 1925435 1926111 := bstep (se 1 (by rfl) ⟨1444583, by rfl⟩ : syracuseStep 1926111 = 2889167) B2889167
theorem B2889173 : Blo 1925435 2889173 := bbase (se 7 (by rfl) ⟨33857, by rfl⟩ : syracuseStep 2889173 = 67715) (by norm_num)
theorem B1926115 : Blo 1925435 1926115 := bstep (se 1 (by rfl) ⟨1444586, by rfl⟩ : syracuseStep 1926115 = 2889173) B2889173
theorem B7313237 : Blo 1925435 7313237 := bbase (se 9 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 7313237 = 42851) (by norm_num)
theorem B4875491 : Blo 1925435 4875491 := bstep (se 1 (by rfl) ⟨3656618, by rfl⟩ : syracuseStep 4875491 = 7313237) B7313237
theorem B3250327 : Blo 1925435 3250327 := bstep (se 1 (by rfl) ⟨2437745, by rfl⟩ : syracuseStep 3250327 = 4875491) B4875491
theorem B4333769 : Blo 1925435 4333769 := bstep (se 2 (by rfl) ⟨1625163, by rfl⟩ : syracuseStep 4333769 = 3250327) B3250327
theorem B2889179 : Blo 1925435 2889179 := bstep (se 1 (by rfl) ⟨2166884, by rfl⟩ : syracuseStep 2889179 = 4333769) B4333769
theorem B1926119 : Blo 1925435 1926119 := bstep (se 1 (by rfl) ⟨1444589, by rfl⟩ : syracuseStep 1926119 = 2889179) B2889179
theorem B2166889 : Blo 1925435 2166889 := bbase (se 2 (by rfl) ⟨812583, by rfl⟩ : syracuseStep 2166889 = 1625167) (by norm_num)
theorem B2889185 : Blo 1925435 2889185 := bstep (se 2 (by rfl) ⟨1083444, by rfl⟩ : syracuseStep 2889185 = 2166889) B2166889
theorem B1926123 : Blo 1925435 1926123 := bstep (se 1 (by rfl) ⟨1444592, by rfl⟩ : syracuseStep 1926123 = 2889185) B2889185
theorem B3085285 : Blo 1925435 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B4113713 : Blo 1925435 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B10969901 : Blo 1925435 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B7313267 : Blo 1925435 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B4875511 : Blo 1925435 4875511 := bstep (se 1 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 4875511 = 7313267) B7313267
theorem B6500681 : Blo 1925435 6500681 := bstep (se 2 (by rfl) ⟨2437755, by rfl⟩ : syracuseStep 6500681 = 4875511) B4875511
theorem B4333787 : Blo 1925435 4333787 := bstep (se 1 (by rfl) ⟨3250340, by rfl⟩ : syracuseStep 4333787 = 6500681) B6500681
theorem B2889191 : Blo 1925435 2889191 := bstep (se 1 (by rfl) ⟨2166893, by rfl⟩ : syracuseStep 2889191 = 4333787) B4333787
theorem B1926127 : Blo 1925435 1926127 := bstep (se 1 (by rfl) ⟨1444595, by rfl⟩ : syracuseStep 1926127 = 2889191) B2889191
theorem B2889197 : Blo 1925435 2889197 := bbase (se 3 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 2889197 = 1083449) (by norm_num)
theorem B1926131 : Blo 1925435 1926131 := bstep (se 1 (by rfl) ⟨1444598, by rfl⟩ : syracuseStep 1926131 = 2889197) B2889197
theorem B4333805 : Blo 1925435 4333805 := bbase (se 3 (by rfl) ⟨812588, by rfl⟩ : syracuseStep 4333805 = 1625177) (by norm_num)
theorem B2889203 : Blo 1925435 2889203 := bstep (se 1 (by rfl) ⟨2166902, by rfl⟩ : syracuseStep 2889203 = 4333805) B4333805
theorem B1926135 : Blo 1925435 1926135 := bstep (se 1 (by rfl) ⟨1444601, by rfl⟩ : syracuseStep 1926135 = 2889203) B2889203
theorem B2742493 : Blo 1925435 2742493 := bbase (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) (by norm_num)
theorem B3656657 : Blo 1925435 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B2437771 : Blo 1925435 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B3250361 : Blo 1925435 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B2166907 : Blo 1925435 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B2889209 : Blo 1925435 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B1926139 : Blo 1925435 1926139 := bstep (se 1 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 1926139 = 2889209) B2889209
theorem B74047445 : Blo 1925435 74047445 := bbase (se 7 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 74047445 = 1735487) (by norm_num)
theorem B49364963 : Blo 1925435 49364963 := bstep (se 1 (by rfl) ⟨37023722, by rfl⟩ : syracuseStep 49364963 = 74047445) B74047445
theorem B32909975 : Blo 1925435 32909975 := bstep (se 1 (by rfl) ⟨24682481, by rfl⟩ : syracuseStep 32909975 = 49364963) B49364963
theorem B21939983 : Blo 1925435 21939983 := bstep (se 1 (by rfl) ⟨16454987, by rfl⟩ : syracuseStep 21939983 = 32909975) B32909975
theorem B14626655 : Blo 1925435 14626655 := bstep (se 1 (by rfl) ⟨10969991, by rfl⟩ : syracuseStep 14626655 = 21939983) B21939983
theorem B9751103 : Blo 1925435 9751103 := bstep (se 1 (by rfl) ⟨7313327, by rfl⟩ : syracuseStep 9751103 = 14626655) B14626655
theorem B6500735 : Blo 1925435 6500735 := bstep (se 1 (by rfl) ⟨4875551, by rfl⟩ : syracuseStep 6500735 = 9751103) B9751103
theorem B4333823 : Blo 1925435 4333823 := bstep (se 1 (by rfl) ⟨3250367, by rfl⟩ : syracuseStep 4333823 = 6500735) B6500735
theorem B2889215 : Blo 1925435 2889215 := bstep (se 1 (by rfl) ⟨2166911, by rfl⟩ : syracuseStep 2889215 = 4333823) B4333823
theorem B1926143 : Blo 1925435 1926143 := bstep (se 1 (by rfl) ⟨1444607, by rfl⟩ : syracuseStep 1926143 = 2889215) B2889215
theorem B2889221 : Blo 1925435 2889221 := bbase (se 4 (by rfl) ⟨270864, by rfl⟩ : syracuseStep 2889221 = 541729) (by norm_num)
theorem B1926147 : Blo 1925435 1926147 := bstep (se 1 (by rfl) ⟨1444610, by rfl⟩ : syracuseStep 1926147 = 2889221) B2889221
theorem B3250381 : Blo 1925435 3250381 := bbase (se 3 (by rfl) ⟨609446, by rfl⟩ : syracuseStep 3250381 = 1218893) (by norm_num)
theorem B4333841 : Blo 1925435 4333841 := bstep (se 2 (by rfl) ⟨1625190, by rfl⟩ : syracuseStep 4333841 = 3250381) B3250381
theorem B2889227 : Blo 1925435 2889227 := bstep (se 1 (by rfl) ⟨2166920, by rfl⟩ : syracuseStep 2889227 = 4333841) B4333841
theorem B1926151 : Blo 1925435 1926151 := bstep (se 1 (by rfl) ⟨1444613, by rfl⟩ : syracuseStep 1926151 = 2889227) B2889227
theorem B2166925 : Blo 1925435 2166925 := bbase (se 3 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 2166925 = 812597) (by norm_num)
theorem B2889233 : Blo 1925435 2889233 := bstep (se 2 (by rfl) ⟨1083462, by rfl⟩ : syracuseStep 2889233 = 2166925) B2166925
theorem B1926155 : Blo 1925435 1926155 := bstep (se 1 (by rfl) ⟨1444616, by rfl⟩ : syracuseStep 1926155 = 2889233) B2889233
theorem B6500789 : Blo 1925435 6500789 := bbase (se 5 (by rfl) ⟨304724, by rfl⟩ : syracuseStep 6500789 = 609449) (by norm_num)
theorem B4333859 : Blo 1925435 4333859 := bstep (se 1 (by rfl) ⟨3250394, by rfl⟩ : syracuseStep 4333859 = 6500789) B6500789
theorem B2889239 : Blo 1925435 2889239 := bstep (se 1 (by rfl) ⟨2166929, by rfl⟩ : syracuseStep 2889239 = 4333859) B4333859
theorem B1926159 : Blo 1925435 1926159 := bstep (se 1 (by rfl) ⟨1444619, by rfl⟩ : syracuseStep 1926159 = 2889239) B2889239
theorem B2889245 : Blo 1925435 2889245 := bbase (se 3 (by rfl) ⟨541733, by rfl⟩ : syracuseStep 2889245 = 1083467) (by norm_num)
theorem B1926163 : Blo 1925435 1926163 := bstep (se 1 (by rfl) ⟨1444622, by rfl⟩ : syracuseStep 1926163 = 2889245) B2889245
theorem B4333877 : Blo 1925435 4333877 := bbase (se 5 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 4333877 = 406301) (by norm_num)
theorem B2889251 : Blo 1925435 2889251 := bstep (se 1 (by rfl) ⟨2166938, by rfl⟩ : syracuseStep 2889251 = 4333877) B4333877
theorem B1926167 : Blo 1925435 1926167 := bstep (se 1 (by rfl) ⟨1444625, by rfl⟩ : syracuseStep 1926167 = 2889251) B2889251
theorem B26358101 : Blo 1925435 26358101 := bbase (se 10 (by rfl) ⟨38610, by rfl⟩ : syracuseStep 26358101 = 77221) (by norm_num)
theorem B17572067 : Blo 1925435 17572067 := bstep (se 1 (by rfl) ⟨13179050, by rfl⟩ : syracuseStep 17572067 = 26358101) B26358101
theorem B11714711 : Blo 1925435 11714711 := bstep (se 1 (by rfl) ⟨8786033, by rfl⟩ : syracuseStep 11714711 = 17572067) B17572067
theorem B31239229 : Blo 1925435 31239229 := bstep (se 3 (by rfl) ⟨5857355, by rfl⟩ : syracuseStep 31239229 = 11714711) B11714711
theorem B41652305 : Blo 1925435 41652305 := bstep (se 2 (by rfl) ⟨15619614, by rfl⟩ : syracuseStep 41652305 = 31239229) B31239229
theorem B27768203 : Blo 1925435 27768203 := bstep (se 1 (by rfl) ⟨20826152, by rfl⟩ : syracuseStep 27768203 = 41652305) B41652305
theorem B18512135 : Blo 1925435 18512135 := bstep (se 1 (by rfl) ⟨13884101, by rfl⟩ : syracuseStep 18512135 = 27768203) B27768203
theorem B12341423 : Blo 1925435 12341423 := bstep (se 1 (by rfl) ⟨9256067, by rfl⟩ : syracuseStep 12341423 = 18512135) B18512135
theorem B8227615 : Blo 1925435 8227615 := bstep (se 1 (by rfl) ⟨6170711, by rfl⟩ : syracuseStep 8227615 = 12341423) B12341423
theorem B10970153 : Blo 1925435 10970153 := bstep (se 2 (by rfl) ⟨4113807, by rfl⟩ : syracuseStep 10970153 = 8227615) B8227615
theorem B7313435 : Blo 1925435 7313435 := bstep (se 1 (by rfl) ⟨5485076, by rfl⟩ : syracuseStep 7313435 = 10970153) B10970153
theorem B4875623 : Blo 1925435 4875623 := bstep (se 1 (by rfl) ⟨3656717, by rfl⟩ : syracuseStep 4875623 = 7313435) B7313435
theorem B3250415 : Blo 1925435 3250415 := bstep (se 1 (by rfl) ⟨2437811, by rfl⟩ : syracuseStep 3250415 = 4875623) B4875623
theorem B2166943 : Blo 1925435 2166943 := bstep (se 1 (by rfl) ⟨1625207, by rfl⟩ : syracuseStep 2166943 = 3250415) B3250415
theorem B2889257 : Blo 1925435 2889257 := bstep (se 2 (by rfl) ⟨1083471, by rfl⟩ : syracuseStep 2889257 = 2166943) B2166943
theorem B1926171 : Blo 1925435 1926171 := bstep (se 1 (by rfl) ⟨1444628, by rfl⟩ : syracuseStep 1926171 = 2889257) B2889257
theorem B2471077 : Blo 1925435 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B13179077 : Blo 1925435 13179077 := bstep (se 4 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 13179077 = 2471077) B2471077
theorem B8786051 : Blo 1925435 8786051 := bstep (se 1 (by rfl) ⟨6589538, by rfl⟩ : syracuseStep 8786051 = 13179077) B13179077
theorem B5857367 : Blo 1925435 5857367 := bstep (se 1 (by rfl) ⟨4393025, by rfl⟩ : syracuseStep 5857367 = 8786051) B8786051
theorem B15619645 : Blo 1925435 15619645 := bstep (se 3 (by rfl) ⟨2928683, by rfl⟩ : syracuseStep 15619645 = 5857367) B5857367
theorem B20826193 : Blo 1925435 20826193 := bstep (se 2 (by rfl) ⟨7809822, by rfl⟩ : syracuseStep 20826193 = 15619645) B15619645
theorem B27768257 : Blo 1925435 27768257 := bstep (se 2 (by rfl) ⟨10413096, by rfl⟩ : syracuseStep 27768257 = 20826193) B20826193
theorem B18512171 : Blo 1925435 18512171 := bstep (se 1 (by rfl) ⟨13884128, by rfl⟩ : syracuseStep 18512171 = 27768257) B27768257
theorem B12341447 : Blo 1925435 12341447 := bstep (se 1 (by rfl) ⟨9256085, by rfl⟩ : syracuseStep 12341447 = 18512171) B18512171
theorem B8227631 : Blo 1925435 8227631 := bstep (se 1 (by rfl) ⟨6170723, by rfl⟩ : syracuseStep 8227631 = 12341447) B12341447
theorem B5485087 : Blo 1925435 5485087 := bstep (se 1 (by rfl) ⟨4113815, by rfl⟩ : syracuseStep 5485087 = 8227631) B8227631
theorem B7313449 : Blo 1925435 7313449 := bstep (se 2 (by rfl) ⟨2742543, by rfl⟩ : syracuseStep 7313449 = 5485087) B5485087
theorem B9751265 : Blo 1925435 9751265 := bstep (se 2 (by rfl) ⟨3656724, by rfl⟩ : syracuseStep 9751265 = 7313449) B7313449
theorem B6500843 : Blo 1925435 6500843 := bstep (se 1 (by rfl) ⟨4875632, by rfl⟩ : syracuseStep 6500843 = 9751265) B9751265
theorem B4333895 : Blo 1925435 4333895 := bstep (se 1 (by rfl) ⟨3250421, by rfl⟩ : syracuseStep 4333895 = 6500843) B6500843
theorem B2889263 : Blo 1925435 2889263 := bstep (se 1 (by rfl) ⟨2166947, by rfl⟩ : syracuseStep 2889263 = 4333895) B4333895
theorem B1926175 : Blo 1925435 1926175 := bstep (se 1 (by rfl) ⟨1444631, by rfl⟩ : syracuseStep 1926175 = 2889263) B2889263
theorem B2889269 : Blo 1925435 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B1926179 : Blo 1925435 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B4875653 : Blo 1925435 4875653 := bbase (se 4 (by rfl) ⟨457092, by rfl⟩ : syracuseStep 4875653 = 914185) (by norm_num)
theorem B3250435 : Blo 1925435 3250435 := bstep (se 1 (by rfl) ⟨2437826, by rfl⟩ : syracuseStep 3250435 = 4875653) B4875653
theorem B4333913 : Blo 1925435 4333913 := bstep (se 2 (by rfl) ⟨1625217, by rfl⟩ : syracuseStep 4333913 = 3250435) B3250435
theorem B2889275 : Blo 1925435 2889275 := bstep (se 1 (by rfl) ⟨2166956, by rfl⟩ : syracuseStep 2889275 = 4333913) B4333913
theorem B1926183 : Blo 1925435 1926183 := bstep (se 1 (by rfl) ⟨1444637, by rfl⟩ : syracuseStep 1926183 = 2889275) B2889275
theorem B2166961 : Blo 1925435 2166961 := bbase (se 2 (by rfl) ⟨812610, by rfl⟩ : syracuseStep 2166961 = 1625221) (by norm_num)
theorem B2889281 : Blo 1925435 2889281 := bstep (se 2 (by rfl) ⟨1083480, by rfl⟩ : syracuseStep 2889281 = 2166961) B2166961
theorem B1926187 : Blo 1925435 1926187 := bstep (se 1 (by rfl) ⟨1444640, by rfl⟩ : syracuseStep 1926187 = 2889281) B2889281
theorem B2056925 : Blo 1925435 2056925 := bbase (se 3 (by rfl) ⟨385673, by rfl⟩ : syracuseStep 2056925 = 771347) (by norm_num)
theorem B5485133 : Blo 1925435 5485133 := bstep (se 3 (by rfl) ⟨1028462, by rfl⟩ : syracuseStep 5485133 = 2056925) B2056925
theorem B3656755 : Blo 1925435 3656755 := bstep (se 1 (by rfl) ⟨2742566, by rfl⟩ : syracuseStep 3656755 = 5485133) B5485133
theorem B4875673 : Blo 1925435 4875673 := bstep (se 2 (by rfl) ⟨1828377, by rfl⟩ : syracuseStep 4875673 = 3656755) B3656755
theorem B6500897 : Blo 1925435 6500897 := bstep (se 2 (by rfl) ⟨2437836, by rfl⟩ : syracuseStep 6500897 = 4875673) B4875673
theorem B4333931 : Blo 1925435 4333931 := bstep (se 1 (by rfl) ⟨3250448, by rfl⟩ : syracuseStep 4333931 = 6500897) B6500897
theorem B2889287 : Blo 1925435 2889287 := bstep (se 1 (by rfl) ⟨2166965, by rfl⟩ : syracuseStep 2889287 = 4333931) B4333931
theorem B1926191 : Blo 1925435 1926191 := bstep (se 1 (by rfl) ⟨1444643, by rfl⟩ : syracuseStep 1926191 = 2889287) B2889287
theorem B2889293 : Blo 1925435 2889293 := bbase (se 3 (by rfl) ⟨541742, by rfl⟩ : syracuseStep 2889293 = 1083485) (by norm_num)
theorem B1926195 : Blo 1925435 1926195 := bstep (se 1 (by rfl) ⟨1444646, by rfl⟩ : syracuseStep 1926195 = 2889293) B2889293
theorem B4333949 : Blo 1925435 4333949 := bbase (se 3 (by rfl) ⟨812615, by rfl⟩ : syracuseStep 4333949 = 1625231) (by norm_num)
theorem B2889299 : Blo 1925435 2889299 := bstep (se 1 (by rfl) ⟨2166974, by rfl⟩ : syracuseStep 2889299 = 4333949) B4333949
theorem B1926199 : Blo 1925435 1926199 := bstep (se 1 (by rfl) ⟨1444649, by rfl⟩ : syracuseStep 1926199 = 2889299) B2889299
theorem B3250469 : Blo 1925435 3250469 := bbase (se 4 (by rfl) ⟨304731, by rfl⟩ : syracuseStep 3250469 = 609463) (by norm_num)
theorem B2166979 : Blo 1925435 2166979 := bstep (se 1 (by rfl) ⟨1625234, by rfl⟩ : syracuseStep 2166979 = 3250469) B3250469
theorem B2889305 : Blo 1925435 2889305 := bstep (se 2 (by rfl) ⟨1083489, by rfl⟩ : syracuseStep 2889305 = 2166979) B2166979
theorem B1926203 : Blo 1925435 1926203 := bstep (se 1 (by rfl) ⟨1444652, by rfl⟩ : syracuseStep 1926203 = 2889305) B2889305
theorem B2742589 : Blo 1925435 2742589 := bbase (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) (by norm_num)
theorem B14627141 : Blo 1925435 14627141 := bstep (se 4 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 14627141 = 2742589) B2742589
theorem B9751427 : Blo 1925435 9751427 := bstep (se 1 (by rfl) ⟨7313570, by rfl⟩ : syracuseStep 9751427 = 14627141) B14627141
theorem B6500951 : Blo 1925435 6500951 := bstep (se 1 (by rfl) ⟨4875713, by rfl⟩ : syracuseStep 6500951 = 9751427) B9751427
theorem B4333967 : Blo 1925435 4333967 := bstep (se 1 (by rfl) ⟨3250475, by rfl⟩ : syracuseStep 4333967 = 6500951) B6500951
theorem B2889311 : Blo 1925435 2889311 := bstep (se 1 (by rfl) ⟨2166983, by rfl⟩ : syracuseStep 2889311 = 4333967) B4333967
theorem B1926207 : Blo 1925435 1926207 := bstep (se 1 (by rfl) ⟨1444655, by rfl⟩ : syracuseStep 1926207 = 2889311) B2889311
theorem B2889317 : Blo 1925435 2889317 := bbase (se 4 (by rfl) ⟨270873, by rfl⟩ : syracuseStep 2889317 = 541747) (by norm_num)
theorem B1926211 : Blo 1925435 1926211 := bstep (se 1 (by rfl) ⟨1444658, by rfl⟩ : syracuseStep 1926211 = 2889317) B2889317
theorem B4628141 : Blo 1925435 4628141 := bbase (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) (by norm_num)
theorem B3085427 : Blo 1925435 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B2056951 : Blo 1925435 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B2742601 : Blo 1925435 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B3656801 : Blo 1925435 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B2437867 : Blo 1925435 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B3250489 : Blo 1925435 3250489 := bstep (se 2 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 3250489 = 2437867) B2437867
theorem B4333985 : Blo 1925435 4333985 := bstep (se 2 (by rfl) ⟨1625244, by rfl⟩ : syracuseStep 4333985 = 3250489) B3250489
theorem B2889323 : Blo 1925435 2889323 := bstep (se 1 (by rfl) ⟨2166992, by rfl⟩ : syracuseStep 2889323 = 4333985) B4333985
theorem B1926215 : Blo 1925435 1926215 := bstep (se 1 (by rfl) ⟨1444661, by rfl⟩ : syracuseStep 1926215 = 2889323) B2889323
theorem B2166997 : Blo 1925435 2166997 := bbase (se 7 (by rfl) ⟨25394, by rfl⟩ : syracuseStep 2166997 = 50789) (by norm_num)
theorem B2889329 : Blo 1925435 2889329 := bstep (se 2 (by rfl) ⟨1083498, by rfl⟩ : syracuseStep 2889329 = 2166997) B2166997
theorem B1926219 : Blo 1925435 1926219 := bstep (se 1 (by rfl) ⟨1444664, by rfl⟩ : syracuseStep 1926219 = 2889329) B2889329
theorem B2437877 : Blo 1925435 2437877 := bbase (se 5 (by rfl) ⟨114275, by rfl⟩ : syracuseStep 2437877 = 228551) (by norm_num)
theorem B6501005 : Blo 1925435 6501005 := bstep (se 3 (by rfl) ⟨1218938, by rfl⟩ : syracuseStep 6501005 = 2437877) B2437877
theorem B4334003 : Blo 1925435 4334003 := bstep (se 1 (by rfl) ⟨3250502, by rfl⟩ : syracuseStep 4334003 = 6501005) B6501005
theorem B2889335 : Blo 1925435 2889335 := bstep (se 1 (by rfl) ⟨2167001, by rfl⟩ : syracuseStep 2889335 = 4334003) B4334003
theorem B1926223 : Blo 1925435 1926223 := bstep (se 1 (by rfl) ⟨1444667, by rfl⟩ : syracuseStep 1926223 = 2889335) B2889335
theorem B2889341 : Blo 1925435 2889341 := bbase (se 3 (by rfl) ⟨541751, by rfl⟩ : syracuseStep 2889341 = 1083503) (by norm_num)
theorem B1926227 : Blo 1925435 1926227 := bstep (se 1 (by rfl) ⟨1444670, by rfl⟩ : syracuseStep 1926227 = 2889341) B2889341
theorem B4334021 : Blo 1925435 4334021 := bbase (se 4 (by rfl) ⟨406314, by rfl⟩ : syracuseStep 4334021 = 812629) (by norm_num)
theorem B2889347 : Blo 1925435 2889347 := bstep (se 1 (by rfl) ⟨2167010, by rfl⟩ : syracuseStep 2889347 = 4334021) B4334021
theorem B1926231 : Blo 1925435 1926231 := bstep (se 1 (by rfl) ⟨1444673, by rfl⟩ : syracuseStep 1926231 = 2889347) B2889347
theorem B6170917 : Blo 1925435 6170917 := bbase (se 4 (by rfl) ⟨578523, by rfl⟩ : syracuseStep 6170917 = 1157047) (by norm_num)
theorem B8227889 : Blo 1925435 8227889 := bstep (se 2 (by rfl) ⟨3085458, by rfl⟩ : syracuseStep 8227889 = 6170917) B6170917
theorem B5485259 : Blo 1925435 5485259 := bstep (se 1 (by rfl) ⟨4113944, by rfl⟩ : syracuseStep 5485259 = 8227889) B8227889
theorem B3656839 : Blo 1925435 3656839 := bstep (se 1 (by rfl) ⟨2742629, by rfl⟩ : syracuseStep 3656839 = 5485259) B5485259
theorem B4875785 : Blo 1925435 4875785 := bstep (se 2 (by rfl) ⟨1828419, by rfl⟩ : syracuseStep 4875785 = 3656839) B3656839
theorem B3250523 : Blo 1925435 3250523 := bstep (se 1 (by rfl) ⟨2437892, by rfl⟩ : syracuseStep 3250523 = 4875785) B4875785
theorem B2167015 : Blo 1925435 2167015 := bstep (se 1 (by rfl) ⟨1625261, by rfl⟩ : syracuseStep 2167015 = 3250523) B3250523
theorem B2889353 : Blo 1925435 2889353 := bstep (se 2 (by rfl) ⟨1083507, by rfl⟩ : syracuseStep 2889353 = 2167015) B2167015
theorem B1926235 : Blo 1925435 1926235 := bstep (se 1 (by rfl) ⟨1444676, by rfl⟩ : syracuseStep 1926235 = 2889353) B2889353
theorem B9751589 : Blo 1925435 9751589 := bbase (se 4 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 9751589 = 1828423) (by norm_num)
theorem B6501059 : Blo 1925435 6501059 := bstep (se 1 (by rfl) ⟨4875794, by rfl⟩ : syracuseStep 6501059 = 9751589) B9751589
theorem B4334039 : Blo 1925435 4334039 := bstep (se 1 (by rfl) ⟨3250529, by rfl⟩ : syracuseStep 4334039 = 6501059) B6501059
theorem B2889359 : Blo 1925435 2889359 := bstep (se 1 (by rfl) ⟨2167019, by rfl⟩ : syracuseStep 2889359 = 4334039) B4334039
theorem B1926239 : Blo 1925435 1926239 := bstep (se 1 (by rfl) ⟨1444679, by rfl⟩ : syracuseStep 1926239 = 2889359) B2889359
theorem B2889365 : Blo 1925435 2889365 := bbase (se 6 (by rfl) ⟨67719, by rfl⟩ : syracuseStep 2889365 = 135439) (by norm_num)
theorem B1926243 : Blo 1925435 1926243 := bstep (se 1 (by rfl) ⟨1444682, by rfl⟩ : syracuseStep 1926243 = 2889365) B2889365
theorem B12341909 : Blo 1925435 12341909 := bbase (se 6 (by rfl) ⟨289263, by rfl⟩ : syracuseStep 12341909 = 578527) (by norm_num)
theorem B8227939 : Blo 1925435 8227939 := bstep (se 1 (by rfl) ⟨6170954, by rfl⟩ : syracuseStep 8227939 = 12341909) B12341909
theorem B10970585 : Blo 1925435 10970585 := bstep (se 2 (by rfl) ⟨4113969, by rfl⟩ : syracuseStep 10970585 = 8227939) B8227939
theorem B7313723 : Blo 1925435 7313723 := bstep (se 1 (by rfl) ⟨5485292, by rfl⟩ : syracuseStep 7313723 = 10970585) B10970585
theorem B4875815 : Blo 1925435 4875815 := bstep (se 1 (by rfl) ⟨3656861, by rfl⟩ : syracuseStep 4875815 = 7313723) B7313723
theorem B3250543 : Blo 1925435 3250543 := bstep (se 1 (by rfl) ⟨2437907, by rfl⟩ : syracuseStep 3250543 = 4875815) B4875815
theorem B4334057 : Blo 1925435 4334057 := bstep (se 2 (by rfl) ⟨1625271, by rfl⟩ : syracuseStep 4334057 = 3250543) B3250543
theorem B2889371 : Blo 1925435 2889371 := bstep (se 1 (by rfl) ⟨2167028, by rfl⟩ : syracuseStep 2889371 = 4334057) B4334057
theorem B1926247 : Blo 1925435 1926247 := bstep (se 1 (by rfl) ⟨1444685, by rfl⟩ : syracuseStep 1926247 = 2889371) B2889371
theorem B2167033 : Blo 1925435 2167033 := bbase (se 2 (by rfl) ⟨812637, by rfl⟩ : syracuseStep 2167033 = 1625275) (by norm_num)
theorem B2889377 : Blo 1925435 2889377 := bstep (se 2 (by rfl) ⟨1083516, by rfl⟩ : syracuseStep 2889377 = 2167033) B2167033
theorem B1926251 : Blo 1925435 1926251 := bstep (se 1 (by rfl) ⟨1444688, by rfl⟩ : syracuseStep 1926251 = 2889377) B2889377
theorem B8227973 : Blo 1925435 8227973 := bbase (se 4 (by rfl) ⟨771372, by rfl⟩ : syracuseStep 8227973 = 1542745) (by norm_num)
theorem B5485315 : Blo 1925435 5485315 := bstep (se 1 (by rfl) ⟨4113986, by rfl⟩ : syracuseStep 5485315 = 8227973) B8227973
theorem B7313753 : Blo 1925435 7313753 := bstep (se 2 (by rfl) ⟨2742657, by rfl⟩ : syracuseStep 7313753 = 5485315) B5485315
theorem B4875835 : Blo 1925435 4875835 := bstep (se 1 (by rfl) ⟨3656876, by rfl⟩ : syracuseStep 4875835 = 7313753) B7313753
theorem B6501113 : Blo 1925435 6501113 := bstep (se 2 (by rfl) ⟨2437917, by rfl⟩ : syracuseStep 6501113 = 4875835) B4875835
theorem B4334075 : Blo 1925435 4334075 := bstep (se 1 (by rfl) ⟨3250556, by rfl⟩ : syracuseStep 4334075 = 6501113) B6501113
theorem B2889383 : Blo 1925435 2889383 := bstep (se 1 (by rfl) ⟨2167037, by rfl⟩ : syracuseStep 2889383 = 4334075) B4334075
theorem B1926255 : Blo 1925435 1926255 := bstep (se 1 (by rfl) ⟨1444691, by rfl⟩ : syracuseStep 1926255 = 2889383) B2889383
theorem B2889389 : Blo 1925435 2889389 := bbase (se 3 (by rfl) ⟨541760, by rfl⟩ : syracuseStep 2889389 = 1083521) (by norm_num)
theorem B1926259 : Blo 1925435 1926259 := bstep (se 1 (by rfl) ⟨1444694, by rfl⟩ : syracuseStep 1926259 = 2889389) B2889389
theorem B4334093 : Blo 1925435 4334093 := bbase (se 3 (by rfl) ⟨812642, by rfl⟩ : syracuseStep 4334093 = 1625285) (by norm_num)
theorem B2889395 : Blo 1925435 2889395 := bstep (se 1 (by rfl) ⟨2167046, by rfl⟩ : syracuseStep 2889395 = 4334093) B4334093
theorem B1926263 : Blo 1925435 1926263 := bstep (se 1 (by rfl) ⟨1444697, by rfl⟩ : syracuseStep 1926263 = 2889395) B2889395
theorem B2437933 : Blo 1925435 2437933 := bbase (se 3 (by rfl) ⟨457112, by rfl⟩ : syracuseStep 2437933 = 914225) (by norm_num)
theorem B3250577 : Blo 1925435 3250577 := bstep (se 2 (by rfl) ⟨1218966, by rfl⟩ : syracuseStep 3250577 = 2437933) B2437933
theorem B2167051 : Blo 1925435 2167051 := bstep (se 1 (by rfl) ⟨1625288, by rfl⟩ : syracuseStep 2167051 = 3250577) B3250577
theorem B2889401 : Blo 1925435 2889401 := bstep (se 2 (by rfl) ⟨1083525, by rfl⟩ : syracuseStep 2889401 = 2167051) B2167051
theorem B1926267 : Blo 1925435 1926267 := bstep (se 1 (by rfl) ⟨1444700, by rfl⟩ : syracuseStep 1926267 = 2889401) B2889401
theorem B3471205 : Blo 1925435 3471205 := bbase (se 4 (by rfl) ⟨325425, by rfl⟩ : syracuseStep 3471205 = 650851) (by norm_num)
theorem B4628273 : Blo 1925435 4628273 := bstep (se 2 (by rfl) ⟨1735602, by rfl⟩ : syracuseStep 4628273 = 3471205) B3471205
theorem B12342061 : Blo 1925435 12342061 := bstep (se 3 (by rfl) ⟨2314136, by rfl⟩ : syracuseStep 12342061 = 4628273) B4628273
theorem B16456081 : Blo 1925435 16456081 := bstep (se 2 (by rfl) ⟨6171030, by rfl⟩ : syracuseStep 16456081 = 12342061) B12342061
theorem B21941441 : Blo 1925435 21941441 := bstep (se 2 (by rfl) ⟨8228040, by rfl⟩ : syracuseStep 21941441 = 16456081) B16456081
theorem B14627627 : Blo 1925435 14627627 := bstep (se 1 (by rfl) ⟨10970720, by rfl⟩ : syracuseStep 14627627 = 21941441) B21941441
theorem B9751751 : Blo 1925435 9751751 := bstep (se 1 (by rfl) ⟨7313813, by rfl⟩ : syracuseStep 9751751 = 14627627) B14627627
theorem B6501167 : Blo 1925435 6501167 := bstep (se 1 (by rfl) ⟨4875875, by rfl⟩ : syracuseStep 6501167 = 9751751) B9751751
theorem B4334111 : Blo 1925435 4334111 := bstep (se 1 (by rfl) ⟨3250583, by rfl⟩ : syracuseStep 4334111 = 6501167) B6501167
theorem B2889407 : Blo 1925435 2889407 := bstep (se 1 (by rfl) ⟨2167055, by rfl⟩ : syracuseStep 2889407 = 4334111) B4334111
theorem B1926271 : Blo 1925435 1926271 := bstep (se 1 (by rfl) ⟨1444703, by rfl⟩ : syracuseStep 1926271 = 2889407) B2889407
theorem B2889413 : Blo 1925435 2889413 := bbase (se 4 (by rfl) ⟨270882, by rfl⟩ : syracuseStep 2889413 = 541765) (by norm_num)
theorem B1926275 : Blo 1925435 1926275 := bstep (se 1 (by rfl) ⟨1444706, by rfl⟩ : syracuseStep 1926275 = 2889413) B2889413
theorem B3250597 : Blo 1925435 3250597 := bbase (se 4 (by rfl) ⟨304743, by rfl⟩ : syracuseStep 3250597 = 609487) (by norm_num)
theorem B4334129 : Blo 1925435 4334129 := bstep (se 2 (by rfl) ⟨1625298, by rfl⟩ : syracuseStep 4334129 = 3250597) B3250597
theorem B2889419 : Blo 1925435 2889419 := bstep (se 1 (by rfl) ⟨2167064, by rfl⟩ : syracuseStep 2889419 = 4334129) B4334129
theorem B1926279 : Blo 1925435 1926279 := bstep (se 1 (by rfl) ⟨1444709, by rfl⟩ : syracuseStep 1926279 = 2889419) B2889419
theorem B2167069 : Blo 1925435 2167069 := bbase (se 3 (by rfl) ⟨406325, by rfl⟩ : syracuseStep 2167069 = 812651) (by norm_num)
theorem B2889425 : Blo 1925435 2889425 := bstep (se 2 (by rfl) ⟨1083534, by rfl⟩ : syracuseStep 2889425 = 2167069) B2167069
theorem B1926283 : Blo 1925435 1926283 := bstep (se 1 (by rfl) ⟨1444712, by rfl⟩ : syracuseStep 1926283 = 2889425) B2889425
theorem B6501221 : Blo 1925435 6501221 := bbase (se 4 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 6501221 = 1218979) (by norm_num)
theorem B4334147 : Blo 1925435 4334147 := bstep (se 1 (by rfl) ⟨3250610, by rfl⟩ : syracuseStep 4334147 = 6501221) B6501221
theorem B2889431 : Blo 1925435 2889431 := bstep (se 1 (by rfl) ⟨2167073, by rfl⟩ : syracuseStep 2889431 = 4334147) B4334147
theorem B1926287 : Blo 1925435 1926287 := bstep (se 1 (by rfl) ⟨1444715, by rfl⟩ : syracuseStep 1926287 = 2889431) B2889431
theorem B2889437 : Blo 1925435 2889437 := bbase (se 3 (by rfl) ⟨541769, by rfl⟩ : syracuseStep 2889437 = 1083539) (by norm_num)
theorem B1926291 : Blo 1925435 1926291 := bstep (se 1 (by rfl) ⟨1444718, by rfl⟩ : syracuseStep 1926291 = 2889437) B2889437
theorem B4334165 : Blo 1925435 4334165 := bbase (se 8 (by rfl) ⟨25395, by rfl⟩ : syracuseStep 4334165 = 50791) (by norm_num)
theorem B2889443 : Blo 1925435 2889443 := bstep (se 1 (by rfl) ⟨2167082, by rfl⟩ : syracuseStep 2889443 = 4334165) B4334165
theorem B1926295 : Blo 1925435 1926295 := bstep (se 1 (by rfl) ⟨1444721, by rfl⟩ : syracuseStep 1926295 = 2889443) B2889443
theorem B3905165 : Blo 1925435 3905165 := bbase (se 3 (by rfl) ⟨732218, by rfl⟩ : syracuseStep 3905165 = 1464437) (by norm_num)
theorem B2603443 : Blo 1925435 2603443 := bstep (se 1 (by rfl) ⟨1952582, by rfl⟩ : syracuseStep 2603443 = 3905165) B3905165
theorem B3471257 : Blo 1925435 3471257 := bstep (se 2 (by rfl) ⟨1301721, by rfl⟩ : syracuseStep 3471257 = 2603443) B2603443
theorem B2314171 : Blo 1925435 2314171 := bstep (se 1 (by rfl) ⟨1735628, by rfl⟩ : syracuseStep 2314171 = 3471257) B3471257
theorem B3085561 : Blo 1925435 3085561 := bstep (se 2 (by rfl) ⟨1157085, by rfl⟩ : syracuseStep 3085561 = 2314171) B2314171
theorem B4114081 : Blo 1925435 4114081 := bstep (se 2 (by rfl) ⟨1542780, by rfl⟩ : syracuseStep 4114081 = 3085561) B3085561
theorem B5485441 : Blo 1925435 5485441 := bstep (se 2 (by rfl) ⟨2057040, by rfl⟩ : syracuseStep 5485441 = 4114081) B4114081
theorem B7313921 : Blo 1925435 7313921 := bstep (se 2 (by rfl) ⟨2742720, by rfl⟩ : syracuseStep 7313921 = 5485441) B5485441
theorem B4875947 : Blo 1925435 4875947 := bstep (se 1 (by rfl) ⟨3656960, by rfl⟩ : syracuseStep 4875947 = 7313921) B7313921
theorem B3250631 : Blo 1925435 3250631 := bstep (se 1 (by rfl) ⟨2437973, by rfl⟩ : syracuseStep 3250631 = 4875947) B4875947
theorem B2167087 : Blo 1925435 2167087 := bstep (se 1 (by rfl) ⟨1625315, by rfl⟩ : syracuseStep 2167087 = 3250631) B3250631
theorem B2889449 : Blo 1925435 2889449 := bstep (se 2 (by rfl) ⟨1083543, by rfl⟩ : syracuseStep 2889449 = 2167087) B2167087
theorem B1926299 : Blo 1925435 1926299 := bstep (se 1 (by rfl) ⟨1444724, by rfl⟩ : syracuseStep 1926299 = 2889449) B2889449
theorem B4170221 : Blo 1925435 4170221 := bbase (se 3 (by rfl) ⟨781916, by rfl⟩ : syracuseStep 4170221 = 1563833) (by norm_num)
theorem B2780147 : Blo 1925435 2780147 := bstep (se 1 (by rfl) ⟨2085110, by rfl⟩ : syracuseStep 2780147 = 4170221) B4170221
theorem B7413725 : Blo 1925435 7413725 := bstep (se 3 (by rfl) ⟨1390073, by rfl⟩ : syracuseStep 7413725 = 2780147) B2780147
theorem B19769933 : Blo 1925435 19769933 := bstep (se 3 (by rfl) ⟨3706862, by rfl⟩ : syracuseStep 19769933 = 7413725) B7413725
theorem B13179955 : Blo 1925435 13179955 := bstep (se 1 (by rfl) ⟨9884966, by rfl⟩ : syracuseStep 13179955 = 19769933) B19769933
theorem B17573273 : Blo 1925435 17573273 := bstep (se 2 (by rfl) ⟨6589977, by rfl⟩ : syracuseStep 17573273 = 13179955) B13179955
theorem B11715515 : Blo 1925435 11715515 := bstep (se 1 (by rfl) ⟨8786636, by rfl⟩ : syracuseStep 11715515 = 17573273) B17573273
theorem B7810343 : Blo 1925435 7810343 := bstep (se 1 (by rfl) ⟨5857757, by rfl⟩ : syracuseStep 7810343 = 11715515) B11715515
theorem B5206895 : Blo 1925435 5206895 := bstep (se 1 (by rfl) ⟨3905171, by rfl⟩ : syracuseStep 5206895 = 7810343) B7810343
theorem B3471263 : Blo 1925435 3471263 := bstep (se 1 (by rfl) ⟨2603447, by rfl⟩ : syracuseStep 3471263 = 5206895) B5206895
theorem B2314175 : Blo 1925435 2314175 := bstep (se 1 (by rfl) ⟨1735631, by rfl⟩ : syracuseStep 2314175 = 3471263) B3471263
theorem B24684533 : Blo 1925435 24684533 := bstep (se 5 (by rfl) ⟨1157087, by rfl⟩ : syracuseStep 24684533 = 2314175) B2314175
theorem B16456355 : Blo 1925435 16456355 := bstep (se 1 (by rfl) ⟨12342266, by rfl⟩ : syracuseStep 16456355 = 24684533) B24684533
theorem B10970903 : Blo 1925435 10970903 := bstep (se 1 (by rfl) ⟨8228177, by rfl⟩ : syracuseStep 10970903 = 16456355) B16456355
theorem B7313935 : Blo 1925435 7313935 := bstep (se 1 (by rfl) ⟨5485451, by rfl⟩ : syracuseStep 7313935 = 10970903) B10970903
theorem B9751913 : Blo 1925435 9751913 := bstep (se 2 (by rfl) ⟨3656967, by rfl⟩ : syracuseStep 9751913 = 7313935) B7313935
theorem B6501275 : Blo 1925435 6501275 := bstep (se 1 (by rfl) ⟨4875956, by rfl⟩ : syracuseStep 6501275 = 9751913) B9751913
theorem B4334183 : Blo 1925435 4334183 := bstep (se 1 (by rfl) ⟨3250637, by rfl⟩ : syracuseStep 4334183 = 6501275) B6501275
theorem B2889455 : Blo 1925435 2889455 := bstep (se 1 (by rfl) ⟨2167091, by rfl⟩ : syracuseStep 2889455 = 4334183) B4334183
theorem B1926303 : Blo 1925435 1926303 := bstep (se 1 (by rfl) ⟨1444727, by rfl⟩ : syracuseStep 1926303 = 2889455) B2889455
theorem B2889461 : Blo 1925435 2889461 := bbase (se 5 (by rfl) ⟨135443, by rfl⟩ : syracuseStep 2889461 = 270887) (by norm_num)
theorem B1926307 : Blo 1925435 1926307 := bstep (se 1 (by rfl) ⟨1444730, by rfl⟩ : syracuseStep 1926307 = 2889461) B2889461
theorem B8228213 : Blo 1925435 8228213 := bbase (se 5 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 8228213 = 771395) (by norm_num)
theorem B5485475 : Blo 1925435 5485475 := bstep (se 1 (by rfl) ⟨4114106, by rfl⟩ : syracuseStep 5485475 = 8228213) B8228213
theorem B3656983 : Blo 1925435 3656983 := bstep (se 1 (by rfl) ⟨2742737, by rfl⟩ : syracuseStep 3656983 = 5485475) B5485475
theorem B4875977 : Blo 1925435 4875977 := bstep (se 2 (by rfl) ⟨1828491, by rfl⟩ : syracuseStep 4875977 = 3656983) B3656983
theorem B3250651 : Blo 1925435 3250651 := bstep (se 1 (by rfl) ⟨2437988, by rfl⟩ : syracuseStep 3250651 = 4875977) B4875977
theorem B4334201 : Blo 1925435 4334201 := bstep (se 2 (by rfl) ⟨1625325, by rfl⟩ : syracuseStep 4334201 = 3250651) B3250651
theorem B2889467 : Blo 1925435 2889467 := bstep (se 1 (by rfl) ⟨2167100, by rfl⟩ : syracuseStep 2889467 = 4334201) B4334201
theorem B1926311 : Blo 1925435 1926311 := bstep (se 1 (by rfl) ⟨1444733, by rfl⟩ : syracuseStep 1926311 = 2889467) B2889467
theorem B2167105 : Blo 1925435 2167105 := bbase (se 2 (by rfl) ⟨812664, by rfl⟩ : syracuseStep 2167105 = 1625329) (by norm_num)
theorem B2889473 : Blo 1925435 2889473 := bstep (se 2 (by rfl) ⟨1083552, by rfl⟩ : syracuseStep 2889473 = 2167105) B2167105
theorem B1926315 : Blo 1925435 1926315 := bstep (se 1 (by rfl) ⟨1444736, by rfl⟩ : syracuseStep 1926315 = 2889473) B2889473
theorem B4875997 : Blo 1925435 4875997 := bbase (se 3 (by rfl) ⟨914249, by rfl⟩ : syracuseStep 4875997 = 1828499) (by norm_num)
theorem B6501329 : Blo 1925435 6501329 := bstep (se 2 (by rfl) ⟨2437998, by rfl⟩ : syracuseStep 6501329 = 4875997) B4875997
theorem B4334219 : Blo 1925435 4334219 := bstep (se 1 (by rfl) ⟨3250664, by rfl⟩ : syracuseStep 4334219 = 6501329) B6501329
theorem B2889479 : Blo 1925435 2889479 := bstep (se 1 (by rfl) ⟨2167109, by rfl⟩ : syracuseStep 2889479 = 4334219) B4334219
theorem B1926319 : Blo 1925435 1926319 := bstep (se 1 (by rfl) ⟨1444739, by rfl⟩ : syracuseStep 1926319 = 2889479) B2889479
theorem B2889485 : Blo 1925435 2889485 := bbase (se 3 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 2889485 = 1083557) (by norm_num)
theorem B1926323 : Blo 1925435 1926323 := bstep (se 1 (by rfl) ⟨1444742, by rfl⟩ : syracuseStep 1926323 = 2889485) B2889485
theorem B4334237 : Blo 1925435 4334237 := bbase (se 3 (by rfl) ⟨812669, by rfl⟩ : syracuseStep 4334237 = 1625339) (by norm_num)
theorem B2889491 : Blo 1925435 2889491 := bstep (se 1 (by rfl) ⟨2167118, by rfl⟩ : syracuseStep 2889491 = 4334237) B4334237
theorem B1926327 : Blo 1925435 1926327 := bstep (se 1 (by rfl) ⟨1444745, by rfl⟩ : syracuseStep 1926327 = 2889491) B2889491
theorem B3250685 : Blo 1925435 3250685 := bbase (se 3 (by rfl) ⟨609503, by rfl⟩ : syracuseStep 3250685 = 1219007) (by norm_num)
theorem B2167123 : Blo 1925435 2167123 := bstep (se 1 (by rfl) ⟨1625342, by rfl⟩ : syracuseStep 2167123 = 3250685) B3250685
theorem B2889497 : Blo 1925435 2889497 := bstep (se 2 (by rfl) ⟨1083561, by rfl⟩ : syracuseStep 2889497 = 2167123) B2167123
theorem B1926331 : Blo 1925435 1926331 := bstep (se 1 (by rfl) ⟨1444748, by rfl⟩ : syracuseStep 1926331 = 2889497) B2889497
theorem B4114157 : Blo 1925435 4114157 := bbase (se 3 (by rfl) ⟨771404, by rfl⟩ : syracuseStep 4114157 = 1542809) (by norm_num)
theorem B10971085 : Blo 1925435 10971085 := bstep (se 3 (by rfl) ⟨2057078, by rfl⟩ : syracuseStep 10971085 = 4114157) B4114157
theorem B14628113 : Blo 1925435 14628113 := bstep (se 2 (by rfl) ⟨5485542, by rfl⟩ : syracuseStep 14628113 = 10971085) B10971085
theorem B9752075 : Blo 1925435 9752075 := bstep (se 1 (by rfl) ⟨7314056, by rfl⟩ : syracuseStep 9752075 = 14628113) B14628113
theorem B6501383 : Blo 1925435 6501383 := bstep (se 1 (by rfl) ⟨4876037, by rfl⟩ : syracuseStep 6501383 = 9752075) B9752075
theorem B4334255 : Blo 1925435 4334255 := bstep (se 1 (by rfl) ⟨3250691, by rfl⟩ : syracuseStep 4334255 = 6501383) B6501383
theorem B2889503 : Blo 1925435 2889503 := bstep (se 1 (by rfl) ⟨2167127, by rfl⟩ : syracuseStep 2889503 = 4334255) B4334255
theorem B1926335 : Blo 1925435 1926335 := bstep (se 1 (by rfl) ⟨1444751, by rfl⟩ : syracuseStep 1926335 = 2889503) B2889503
theorem B2889509 : Blo 1925435 2889509 := bbase (se 4 (by rfl) ⟨270891, by rfl⟩ : syracuseStep 2889509 = 541783) (by norm_num)
theorem B1926339 : Blo 1925435 1926339 := bstep (se 1 (by rfl) ⟨1444754, by rfl⟩ : syracuseStep 1926339 = 2889509) B2889509
theorem B2438029 : Blo 1925435 2438029 := bbase (se 3 (by rfl) ⟨457130, by rfl⟩ : syracuseStep 2438029 = 914261) (by norm_num)
theorem B3250705 : Blo 1925435 3250705 := bstep (se 2 (by rfl) ⟨1219014, by rfl⟩ : syracuseStep 3250705 = 2438029) B2438029
theorem B4334273 : Blo 1925435 4334273 := bstep (se 2 (by rfl) ⟨1625352, by rfl⟩ : syracuseStep 4334273 = 3250705) B3250705
theorem B2889515 : Blo 1925435 2889515 := bstep (se 1 (by rfl) ⟨2167136, by rfl⟩ : syracuseStep 2889515 = 4334273) B4334273
theorem B1926343 : Blo 1925435 1926343 := bstep (se 1 (by rfl) ⟨1444757, by rfl⟩ : syracuseStep 1926343 = 2889515) B2889515
theorem B2167141 : Blo 1925435 2167141 := bbase (se 4 (by rfl) ⟨203169, by rfl⟩ : syracuseStep 2167141 = 406339) (by norm_num)
theorem B2889521 : Blo 1925435 2889521 := bstep (se 2 (by rfl) ⟨1083570, by rfl⟩ : syracuseStep 2889521 = 2167141) B2167141
theorem B1926347 : Blo 1925435 1926347 := bstep (se 1 (by rfl) ⟨1444760, by rfl⟩ : syracuseStep 1926347 = 2889521) B2889521
theorem B5485589 : Blo 1925435 5485589 := bbase (se 6 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 5485589 = 257137) (by norm_num)
theorem B3657059 : Blo 1925435 3657059 := bstep (se 1 (by rfl) ⟨2742794, by rfl⟩ : syracuseStep 3657059 = 5485589) B5485589
theorem B2438039 : Blo 1925435 2438039 := bstep (se 1 (by rfl) ⟨1828529, by rfl⟩ : syracuseStep 2438039 = 3657059) B3657059
theorem B6501437 : Blo 1925435 6501437 := bstep (se 3 (by rfl) ⟨1219019, by rfl⟩ : syracuseStep 6501437 = 2438039) B2438039
theorem B4334291 : Blo 1925435 4334291 := bstep (se 1 (by rfl) ⟨3250718, by rfl⟩ : syracuseStep 4334291 = 6501437) B6501437
theorem B2889527 : Blo 1925435 2889527 := bstep (se 1 (by rfl) ⟨2167145, by rfl⟩ : syracuseStep 2889527 = 4334291) B4334291
theorem B1926351 : Blo 1925435 1926351 := bstep (se 1 (by rfl) ⟨1444763, by rfl⟩ : syracuseStep 1926351 = 2889527) B2889527
theorem B2889533 : Blo 1925435 2889533 := bbase (se 3 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 2889533 = 1083575) (by norm_num)
theorem B1926355 : Blo 1925435 1926355 := bstep (se 1 (by rfl) ⟨1444766, by rfl⟩ : syracuseStep 1926355 = 2889533) B2889533
theorem B4334309 : Blo 1925435 4334309 := bbase (se 4 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 4334309 = 812683) (by norm_num)
theorem B2889539 : Blo 1925435 2889539 := bstep (se 1 (by rfl) ⟨2167154, by rfl⟩ : syracuseStep 2889539 = 4334309) B4334309
theorem B1926359 : Blo 1925435 1926359 := bstep (se 1 (by rfl) ⟨1444769, by rfl⟩ : syracuseStep 1926359 = 2889539) B2889539
theorem B4876109 : Blo 1925435 4876109 := bbase (se 3 (by rfl) ⟨914270, by rfl⟩ : syracuseStep 4876109 = 1828541) (by norm_num)
theorem B3250739 : Blo 1925435 3250739 := bstep (se 1 (by rfl) ⟨2438054, by rfl⟩ : syracuseStep 3250739 = 4876109) B4876109
theorem B2167159 : Blo 1925435 2167159 := bstep (se 1 (by rfl) ⟨1625369, by rfl⟩ : syracuseStep 2167159 = 3250739) B3250739
theorem B2889545 : Blo 1925435 2889545 := bstep (se 2 (by rfl) ⟨1083579, by rfl⟩ : syracuseStep 2889545 = 2167159) B2167159
theorem B1926363 : Blo 1925435 1926363 := bstep (se 1 (by rfl) ⟨1444772, by rfl⟩ : syracuseStep 1926363 = 2889545) B2889545
theorem B2057113 : Blo 1925435 2057113 := bbase (se 2 (by rfl) ⟨771417, by rfl⟩ : syracuseStep 2057113 = 1542835) (by norm_num)
theorem B2742817 : Blo 1925435 2742817 := bstep (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) B2057113
theorem B3657089 : Blo 1925435 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B9752237 : Blo 1925435 9752237 := bstep (se 3 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 9752237 = 3657089) B3657089
theorem B6501491 : Blo 1925435 6501491 := bstep (se 1 (by rfl) ⟨4876118, by rfl⟩ : syracuseStep 6501491 = 9752237) B9752237
theorem B4334327 : Blo 1925435 4334327 := bstep (se 1 (by rfl) ⟨3250745, by rfl⟩ : syracuseStep 4334327 = 6501491) B6501491
theorem B2889551 : Blo 1925435 2889551 := bstep (se 1 (by rfl) ⟨2167163, by rfl⟩ : syracuseStep 2889551 = 4334327) B4334327
theorem B1926367 : Blo 1925435 1926367 := bstep (se 1 (by rfl) ⟨1444775, by rfl⟩ : syracuseStep 1926367 = 2889551) B2889551
theorem B2889557 : Blo 1925435 2889557 := bbase (se 9 (by rfl) ⟨8465, by rfl⟩ : syracuseStep 2889557 = 16931) (by norm_num)
theorem B1926371 : Blo 1925435 1926371 := bstep (se 1 (by rfl) ⟨1444778, by rfl⟩ : syracuseStep 1926371 = 2889557) B2889557
theorem B6171365 : Blo 1925435 6171365 := bbase (se 4 (by rfl) ⟨578565, by rfl⟩ : syracuseStep 6171365 = 1157131) (by norm_num)
theorem B4114243 : Blo 1925435 4114243 := bstep (se 1 (by rfl) ⟨3085682, by rfl⟩ : syracuseStep 4114243 = 6171365) B6171365
theorem B5485657 : Blo 1925435 5485657 := bstep (se 2 (by rfl) ⟨2057121, by rfl⟩ : syracuseStep 5485657 = 4114243) B4114243
theorem B7314209 : Blo 1925435 7314209 := bstep (se 2 (by rfl) ⟨2742828, by rfl⟩ : syracuseStep 7314209 = 5485657) B5485657
theorem B4876139 : Blo 1925435 4876139 := bstep (se 1 (by rfl) ⟨3657104, by rfl⟩ : syracuseStep 4876139 = 7314209) B7314209
theorem B3250759 : Blo 1925435 3250759 := bstep (se 1 (by rfl) ⟨2438069, by rfl⟩ : syracuseStep 3250759 = 4876139) B4876139
theorem B4334345 : Blo 1925435 4334345 := bstep (se 2 (by rfl) ⟨1625379, by rfl⟩ : syracuseStep 4334345 = 3250759) B3250759
theorem B2889563 : Blo 1925435 2889563 := bstep (se 1 (by rfl) ⟨2167172, by rfl⟩ : syracuseStep 2889563 = 4334345) B4334345
theorem B1926375 : Blo 1925435 1926375 := bstep (se 1 (by rfl) ⟨1444781, by rfl⟩ : syracuseStep 1926375 = 2889563) B2889563
theorem B2167177 : Blo 1925435 2167177 := bbase (se 2 (by rfl) ⟨812691, by rfl⟩ : syracuseStep 2167177 = 1625383) (by norm_num)
theorem B2889569 : Blo 1925435 2889569 := bstep (se 2 (by rfl) ⟨1083588, by rfl⟩ : syracuseStep 2889569 = 2167177) B2167177
theorem B1926379 : Blo 1925435 1926379 := bstep (se 1 (by rfl) ⟨1444784, by rfl⟩ : syracuseStep 1926379 = 2889569) B2889569
theorem B25022357 : Blo 1925435 25022357 := bbase (se 6 (by rfl) ⟨586461, by rfl⟩ : syracuseStep 25022357 = 1172923) (by norm_num)
theorem B16681571 : Blo 1925435 16681571 := bstep (se 1 (by rfl) ⟨12511178, by rfl⟩ : syracuseStep 16681571 = 25022357) B25022357
theorem B11121047 : Blo 1925435 11121047 := bstep (se 1 (by rfl) ⟨8340785, by rfl⟩ : syracuseStep 11121047 = 16681571) B16681571
theorem B7414031 : Blo 1925435 7414031 := bstep (se 1 (by rfl) ⟨5560523, by rfl⟩ : syracuseStep 7414031 = 11121047) B11121047
theorem B19770749 : Blo 1925435 19770749 := bstep (se 3 (by rfl) ⟨3707015, by rfl⟩ : syracuseStep 19770749 = 7414031) B7414031
theorem B13180499 : Blo 1925435 13180499 := bstep (se 1 (by rfl) ⟨9885374, by rfl⟩ : syracuseStep 13180499 = 19770749) B19770749
theorem B8786999 : Blo 1925435 8786999 := bstep (se 1 (by rfl) ⟨6590249, by rfl⟩ : syracuseStep 8786999 = 13180499) B13180499
theorem B23431997 : Blo 1925435 23431997 := bstep (se 3 (by rfl) ⟨4393499, by rfl⟩ : syracuseStep 23431997 = 8786999) B8786999
theorem B15621331 : Blo 1925435 15621331 := bstep (se 1 (by rfl) ⟨11715998, by rfl⟩ : syracuseStep 15621331 = 23431997) B23431997
theorem B20828441 : Blo 1925435 20828441 := bstep (se 2 (by rfl) ⟨7810665, by rfl⟩ : syracuseStep 20828441 = 15621331) B15621331
theorem B55542509 : Blo 1925435 55542509 := bstep (se 3 (by rfl) ⟨10414220, by rfl⟩ : syracuseStep 55542509 = 20828441) B20828441
theorem B37028339 : Blo 1925435 37028339 := bstep (se 1 (by rfl) ⟨27771254, by rfl⟩ : syracuseStep 37028339 = 55542509) B55542509
theorem B24685559 : Blo 1925435 24685559 := bstep (se 1 (by rfl) ⟨18514169, by rfl⟩ : syracuseStep 24685559 = 37028339) B37028339
theorem B16457039 : Blo 1925435 16457039 := bstep (se 1 (by rfl) ⟨12342779, by rfl⟩ : syracuseStep 16457039 = 24685559) B24685559
theorem B10971359 : Blo 1925435 10971359 := bstep (se 1 (by rfl) ⟨8228519, by rfl⟩ : syracuseStep 10971359 = 16457039) B16457039
theorem B7314239 : Blo 1925435 7314239 := bstep (se 1 (by rfl) ⟨5485679, by rfl⟩ : syracuseStep 7314239 = 10971359) B10971359
theorem B4876159 : Blo 1925435 4876159 := bstep (se 1 (by rfl) ⟨3657119, by rfl⟩ : syracuseStep 4876159 = 7314239) B7314239
theorem B6501545 : Blo 1925435 6501545 := bstep (se 2 (by rfl) ⟨2438079, by rfl⟩ : syracuseStep 6501545 = 4876159) B4876159
theorem B4334363 : Blo 1925435 4334363 := bstep (se 1 (by rfl) ⟨3250772, by rfl⟩ : syracuseStep 4334363 = 6501545) B6501545
theorem B2889575 : Blo 1925435 2889575 := bstep (se 1 (by rfl) ⟨2167181, by rfl⟩ : syracuseStep 2889575 = 4334363) B4334363
theorem B1926383 : Blo 1925435 1926383 := bstep (se 1 (by rfl) ⟨1444787, by rfl⟩ : syracuseStep 1926383 = 2889575) B2889575
theorem B2889581 : Blo 1925435 2889581 := bbase (se 3 (by rfl) ⟨541796, by rfl⟩ : syracuseStep 2889581 = 1083593) (by norm_num)
theorem B1926387 : Blo 1925435 1926387 := bstep (se 1 (by rfl) ⟨1444790, by rfl⟩ : syracuseStep 1926387 = 2889581) B2889581
theorem B4334381 : Blo 1925435 4334381 := bbase (se 3 (by rfl) ⟨812696, by rfl⟩ : syracuseStep 4334381 = 1625393) (by norm_num)
theorem B2889587 : Blo 1925435 2889587 := bstep (se 1 (by rfl) ⟨2167190, by rfl⟩ : syracuseStep 2889587 = 4334381) B4334381
theorem B1926391 : Blo 1925435 1926391 := bstep (se 1 (by rfl) ⟨1444793, by rfl⟩ : syracuseStep 1926391 = 2889587) B2889587
theorem B4628573 : Blo 1925435 4628573 := bbase (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) (by norm_num)
theorem B3085715 : Blo 1925435 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B8228573 : Blo 1925435 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B5485715 : Blo 1925435 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B3657143 : Blo 1925435 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B2438095 : Blo 1925435 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B3250793 : Blo 1925435 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B2167195 : Blo 1925435 2167195 := bstep (se 1 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 2167195 = 3250793) B3250793
theorem B2889593 : Blo 1925435 2889593 := bstep (se 2 (by rfl) ⟨1083597, by rfl⟩ : syracuseStep 2889593 = 2167195) B2167195
theorem B1926395 : Blo 1925435 1926395 := bstep (se 1 (by rfl) ⟨1444796, by rfl⟩ : syracuseStep 1926395 = 2889593) B2889593
theorem B15621461 : Blo 1925435 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B10414307 : Blo 1925435 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B6942871 : Blo 1925435 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B9257161 : Blo 1925435 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B12342881 : Blo 1925435 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B32914349 : Blo 1925435 32914349 := bstep (se 3 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 32914349 = 12342881) B12342881
theorem B21942899 : Blo 1925435 21942899 := bstep (se 1 (by rfl) ⟨16457174, by rfl⟩ : syracuseStep 21942899 = 32914349) B32914349
theorem B14628599 : Blo 1925435 14628599 := bstep (se 1 (by rfl) ⟨10971449, by rfl⟩ : syracuseStep 14628599 = 21942899) B21942899
theorem B9752399 : Blo 1925435 9752399 := bstep (se 1 (by rfl) ⟨7314299, by rfl⟩ : syracuseStep 9752399 = 14628599) B14628599
theorem B6501599 : Blo 1925435 6501599 := bstep (se 1 (by rfl) ⟨4876199, by rfl⟩ : syracuseStep 6501599 = 9752399) B9752399
theorem B4334399 : Blo 1925435 4334399 := bstep (se 1 (by rfl) ⟨3250799, by rfl⟩ : syracuseStep 4334399 = 6501599) B6501599
theorem B2889599 : Blo 1925435 2889599 := bstep (se 1 (by rfl) ⟨2167199, by rfl⟩ : syracuseStep 2889599 = 4334399) B4334399
theorem B1926399 : Blo 1925435 1926399 := bstep (se 1 (by rfl) ⟨1444799, by rfl⟩ : syracuseStep 1926399 = 2889599) B2889599
theorem B2889605 : Blo 1925435 2889605 := bbase (se 4 (by rfl) ⟨270900, by rfl⟩ : syracuseStep 2889605 = 541801) (by norm_num)
theorem B1926403 : Blo 1925435 1926403 := bstep (se 1 (by rfl) ⟨1444802, by rfl⟩ : syracuseStep 1926403 = 2889605) B2889605
theorem B3250813 : Blo 1925435 3250813 := bbase (se 3 (by rfl) ⟨609527, by rfl⟩ : syracuseStep 3250813 = 1219055) (by norm_num)
theorem B4334417 : Blo 1925435 4334417 := bstep (se 2 (by rfl) ⟨1625406, by rfl⟩ : syracuseStep 4334417 = 3250813) B3250813
theorem B2889611 : Blo 1925435 2889611 := bstep (se 1 (by rfl) ⟨2167208, by rfl⟩ : syracuseStep 2889611 = 4334417) B4334417
theorem B1926407 : Blo 1925435 1926407 := bstep (se 1 (by rfl) ⟨1444805, by rfl⟩ : syracuseStep 1926407 = 2889611) B2889611
theorem B2167213 : Blo 1925435 2167213 := bbase (se 3 (by rfl) ⟨406352, by rfl⟩ : syracuseStep 2167213 = 812705) (by norm_num)
theorem B2889617 : Blo 1925435 2889617 := bstep (se 2 (by rfl) ⟨1083606, by rfl⟩ : syracuseStep 2889617 = 2167213) B2167213
theorem B1926411 : Blo 1925435 1926411 := bstep (se 1 (by rfl) ⟨1444808, by rfl⟩ : syracuseStep 1926411 = 2889617) B2889617
theorem B6501653 : Blo 1925435 6501653 := bbase (se 6 (by rfl) ⟨152382, by rfl⟩ : syracuseStep 6501653 = 304765) (by norm_num)
theorem B4334435 : Blo 1925435 4334435 := bstep (se 1 (by rfl) ⟨3250826, by rfl⟩ : syracuseStep 4334435 = 6501653) B6501653
theorem B2889623 : Blo 1925435 2889623 := bstep (se 1 (by rfl) ⟨2167217, by rfl⟩ : syracuseStep 2889623 = 4334435) B4334435
theorem B1926415 : Blo 1925435 1926415 := bstep (se 1 (by rfl) ⟨1444811, by rfl⟩ : syracuseStep 1926415 = 2889623) B2889623
theorem B2889629 : Blo 1925435 2889629 := bbase (se 3 (by rfl) ⟨541805, by rfl⟩ : syracuseStep 2889629 = 1083611) (by norm_num)
theorem B1926419 : Blo 1925435 1926419 := bstep (se 1 (by rfl) ⟨1444814, by rfl⟩ : syracuseStep 1926419 = 2889629) B2889629
theorem B4334453 : Blo 1925435 4334453 := bbase (se 5 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 4334453 = 406355) (by norm_num)
theorem B2889635 : Blo 1925435 2889635 := bstep (se 1 (by rfl) ⟨2167226, by rfl⟩ : syracuseStep 2889635 = 4334453) B4334453
theorem B1926423 : Blo 1925435 1926423 := bstep (se 1 (by rfl) ⟨1444817, by rfl⟩ : syracuseStep 1926423 = 2889635) B2889635
theorem B2471401 : Blo 1925435 2471401 := bbase (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) (by norm_num)
theorem B13180805 : Blo 1925435 13180805 := bstep (se 4 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 13180805 = 2471401) B2471401
theorem B8787203 : Blo 1925435 8787203 := bstep (se 1 (by rfl) ⟨6590402, by rfl⟩ : syracuseStep 8787203 = 13180805) B13180805
theorem B5858135 : Blo 1925435 5858135 := bstep (se 1 (by rfl) ⟨4393601, by rfl⟩ : syracuseStep 5858135 = 8787203) B8787203
theorem B3905423 : Blo 1925435 3905423 := bstep (se 1 (by rfl) ⟨2929067, by rfl⟩ : syracuseStep 3905423 = 5858135) B5858135
theorem B2603615 : Blo 1925435 2603615 := bstep (se 1 (by rfl) ⟨1952711, by rfl⟩ : syracuseStep 2603615 = 3905423) B3905423
theorem B27771893 : Blo 1925435 27771893 := bstep (se 5 (by rfl) ⟨1301807, by rfl⟩ : syracuseStep 27771893 = 2603615) B2603615
theorem B18514595 : Blo 1925435 18514595 := bstep (se 1 (by rfl) ⟨13885946, by rfl⟩ : syracuseStep 18514595 = 27771893) B27771893
theorem B12343063 : Blo 1925435 12343063 := bstep (se 1 (by rfl) ⟨9257297, by rfl⟩ : syracuseStep 12343063 = 18514595) B18514595
theorem B16457417 : Blo 1925435 16457417 := bstep (se 2 (by rfl) ⟨6171531, by rfl⟩ : syracuseStep 16457417 = 12343063) B12343063
theorem B10971611 : Blo 1925435 10971611 := bstep (se 1 (by rfl) ⟨8228708, by rfl⟩ : syracuseStep 10971611 = 16457417) B16457417
theorem B7314407 : Blo 1925435 7314407 := bstep (se 1 (by rfl) ⟨5485805, by rfl⟩ : syracuseStep 7314407 = 10971611) B10971611
theorem B4876271 : Blo 1925435 4876271 := bstep (se 1 (by rfl) ⟨3657203, by rfl⟩ : syracuseStep 4876271 = 7314407) B7314407
theorem B3250847 : Blo 1925435 3250847 := bstep (se 1 (by rfl) ⟨2438135, by rfl⟩ : syracuseStep 3250847 = 4876271) B4876271
theorem B2167231 : Blo 1925435 2167231 := bstep (se 1 (by rfl) ⟨1625423, by rfl⟩ : syracuseStep 2167231 = 3250847) B3250847
theorem B2889641 : Blo 1925435 2889641 := bstep (se 2 (by rfl) ⟨1083615, by rfl⟩ : syracuseStep 2889641 = 2167231) B2167231
theorem B1926427 : Blo 1925435 1926427 := bstep (se 1 (by rfl) ⟨1444820, by rfl⟩ : syracuseStep 1926427 = 2889641) B2889641
theorem B7314421 : Blo 1925435 7314421 := bbase (se 5 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 7314421 = 685727) (by norm_num)
theorem B9752561 : Blo 1925435 9752561 := bstep (se 2 (by rfl) ⟨3657210, by rfl⟩ : syracuseStep 9752561 = 7314421) B7314421
theorem B6501707 : Blo 1925435 6501707 := bstep (se 1 (by rfl) ⟨4876280, by rfl⟩ : syracuseStep 6501707 = 9752561) B9752561
theorem B4334471 : Blo 1925435 4334471 := bstep (se 1 (by rfl) ⟨3250853, by rfl⟩ : syracuseStep 4334471 = 6501707) B6501707
theorem B2889647 : Blo 1925435 2889647 := bstep (se 1 (by rfl) ⟨2167235, by rfl⟩ : syracuseStep 2889647 = 4334471) B4334471
theorem B1926431 : Blo 1925435 1926431 := bstep (se 1 (by rfl) ⟨1444823, by rfl⟩ : syracuseStep 1926431 = 2889647) B2889647
theorem B2889653 : Blo 1925435 2889653 := bbase (se 5 (by rfl) ⟨135452, by rfl⟩ : syracuseStep 2889653 = 270905) (by norm_num)
theorem B1926435 : Blo 1925435 1926435 := bstep (se 1 (by rfl) ⟨1444826, by rfl⟩ : syracuseStep 1926435 = 2889653) B2889653
theorem B4876301 : Blo 1925435 4876301 := bbase (se 3 (by rfl) ⟨914306, by rfl⟩ : syracuseStep 4876301 = 1828613) (by norm_num)
theorem B3250867 : Blo 1925435 3250867 := bstep (se 1 (by rfl) ⟨2438150, by rfl⟩ : syracuseStep 3250867 = 4876301) B4876301
theorem B4334489 : Blo 1925435 4334489 := bstep (se 2 (by rfl) ⟨1625433, by rfl⟩ : syracuseStep 4334489 = 3250867) B3250867
theorem B2889659 : Blo 1925435 2889659 := bstep (se 1 (by rfl) ⟨2167244, by rfl⟩ : syracuseStep 2889659 = 4334489) B4334489
theorem B1926439 : Blo 1925435 1926439 := bstep (se 1 (by rfl) ⟨1444829, by rfl⟩ : syracuseStep 1926439 = 2889659) B2889659
theorem B2167249 : Blo 1925435 2167249 := bbase (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) (by norm_num)
theorem B2889665 : Blo 1925435 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B1926443 : Blo 1925435 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B4114397 : Blo 1925435 4114397 := bbase (se 3 (by rfl) ⟨771449, by rfl⟩ : syracuseStep 4114397 = 1542899) (by norm_num)
theorem B2742931 : Blo 1925435 2742931 := bstep (se 1 (by rfl) ⟨2057198, by rfl⟩ : syracuseStep 2742931 = 4114397) B4114397
theorem B3657241 : Blo 1925435 3657241 := bstep (se 2 (by rfl) ⟨1371465, by rfl⟩ : syracuseStep 3657241 = 2742931) B2742931
theorem B4876321 : Blo 1925435 4876321 := bstep (se 2 (by rfl) ⟨1828620, by rfl⟩ : syracuseStep 4876321 = 3657241) B3657241
theorem B6501761 : Blo 1925435 6501761 := bstep (se 2 (by rfl) ⟨2438160, by rfl⟩ : syracuseStep 6501761 = 4876321) B4876321
theorem B4334507 : Blo 1925435 4334507 := bstep (se 1 (by rfl) ⟨3250880, by rfl⟩ : syracuseStep 4334507 = 6501761) B6501761
theorem B2889671 : Blo 1925435 2889671 := bstep (se 1 (by rfl) ⟨2167253, by rfl⟩ : syracuseStep 2889671 = 4334507) B4334507
theorem B1926447 : Blo 1925435 1926447 := bstep (se 1 (by rfl) ⟨1444835, by rfl⟩ : syracuseStep 1926447 = 2889671) B2889671
theorem B2889677 : Blo 1925435 2889677 := bbase (se 3 (by rfl) ⟨541814, by rfl⟩ : syracuseStep 2889677 = 1083629) (by norm_num)
theorem B1926451 : Blo 1925435 1926451 := bstep (se 1 (by rfl) ⟨1444838, by rfl⟩ : syracuseStep 1926451 = 2889677) B2889677
theorem B4334525 : Blo 1925435 4334525 := bbase (se 3 (by rfl) ⟨812723, by rfl⟩ : syracuseStep 4334525 = 1625447) (by norm_num)
theorem B2889683 : Blo 1925435 2889683 := bstep (se 1 (by rfl) ⟨2167262, by rfl⟩ : syracuseStep 2889683 = 4334525) B4334525
theorem B1926455 : Blo 1925435 1926455 := bstep (se 1 (by rfl) ⟨1444841, by rfl⟩ : syracuseStep 1926455 = 2889683) B2889683
theorem B3250901 : Blo 1925435 3250901 := bbase (se 7 (by rfl) ⟨38096, by rfl⟩ : syracuseStep 3250901 = 76193) (by norm_num)
theorem B2167267 : Blo 1925435 2167267 := bstep (se 1 (by rfl) ⟨1625450, by rfl⟩ : syracuseStep 2167267 = 3250901) B3250901
theorem B2889689 : Blo 1925435 2889689 := bstep (se 2 (by rfl) ⟨1083633, by rfl⟩ : syracuseStep 2889689 = 2167267) B2167267
theorem B1926459 : Blo 1925435 1926459 := bstep (se 1 (by rfl) ⟨1444844, by rfl⟩ : syracuseStep 1926459 = 2889689) B2889689
theorem B79086293 : Blo 1925435 79086293 := bbase (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) (by norm_num)
theorem B52724195 : Blo 1925435 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B35149463 : Blo 1925435 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B23432975 : Blo 1925435 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B15621983 : Blo 1925435 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B10414655 : Blo 1925435 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B6943103 : Blo 1925435 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B4628735 : Blo 1925435 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3085823 : Blo 1925435 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B8228861 : Blo 1925435 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B5485907 : Blo 1925435 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B14629085 : Blo 1925435 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B9752723 : Blo 1925435 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B6501815 : Blo 1925435 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B4334543 : Blo 1925435 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B2889695 : Blo 1925435 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B1926463 : Blo 1925435 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B2889701 : Blo 1925435 2889701 := bbase (se 4 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 2889701 = 541819) (by norm_num)
theorem B1926467 : Blo 1925435 1926467 := bstep (se 1 (by rfl) ⟨1444850, by rfl⟩ : syracuseStep 1926467 = 2889701) B2889701
theorem B13360949 : Blo 1925435 13360949 := bbase (se 5 (by rfl) ⟨626294, by rfl⟩ : syracuseStep 13360949 = 1252589) (by norm_num)
theorem B8907299 : Blo 1925435 8907299 := bstep (se 1 (by rfl) ⟨6680474, by rfl⟩ : syracuseStep 8907299 = 13360949) B13360949
theorem B5938199 : Blo 1925435 5938199 := bstep (se 1 (by rfl) ⟨4453649, by rfl⟩ : syracuseStep 5938199 = 8907299) B8907299
theorem B3958799 : Blo 1925435 3958799 := bstep (se 1 (by rfl) ⟨2969099, by rfl⟩ : syracuseStep 3958799 = 5938199) B5938199
theorem B42227189 : Blo 1925435 42227189 := bstep (se 5 (by rfl) ⟨1979399, by rfl⟩ : syracuseStep 42227189 = 3958799) B3958799
theorem B28151459 : Blo 1925435 28151459 := bstep (se 1 (by rfl) ⟨21113594, by rfl⟩ : syracuseStep 28151459 = 42227189) B42227189
theorem B18767639 : Blo 1925435 18767639 := bstep (se 1 (by rfl) ⟨14075729, by rfl⟩ : syracuseStep 18767639 = 28151459) B28151459
theorem B12511759 : Blo 1925435 12511759 := bstep (se 1 (by rfl) ⟨9383819, by rfl⟩ : syracuseStep 12511759 = 18767639) B18767639
theorem B16682345 : Blo 1925435 16682345 := bstep (se 2 (by rfl) ⟨6255879, by rfl⟩ : syracuseStep 16682345 = 12511759) B12511759
theorem B11121563 : Blo 1925435 11121563 := bstep (se 1 (by rfl) ⟨8341172, by rfl⟩ : syracuseStep 11121563 = 16682345) B16682345
theorem B7414375 : Blo 1925435 7414375 := bstep (se 1 (by rfl) ⟨5560781, by rfl⟩ : syracuseStep 7414375 = 11121563) B11121563
theorem B9885833 : Blo 1925435 9885833 := bstep (se 2 (by rfl) ⟨3707187, by rfl⟩ : syracuseStep 9885833 = 7414375) B7414375
theorem B6590555 : Blo 1925435 6590555 := bstep (se 1 (by rfl) ⟨4942916, by rfl⟩ : syracuseStep 6590555 = 9885833) B9885833
theorem B4393703 : Blo 1925435 4393703 := bstep (se 1 (by rfl) ⟨3295277, by rfl⟩ : syracuseStep 4393703 = 6590555) B6590555
theorem B2929135 : Blo 1925435 2929135 := bstep (se 1 (by rfl) ⟨2196851, by rfl⟩ : syracuseStep 2929135 = 4393703) B4393703
theorem B3905513 : Blo 1925435 3905513 := bstep (se 2 (by rfl) ⟨1464567, by rfl⟩ : syracuseStep 3905513 = 2929135) B2929135
theorem B2603675 : Blo 1925435 2603675 := bstep (se 1 (by rfl) ⟨1952756, by rfl⟩ : syracuseStep 2603675 = 3905513) B3905513
theorem B6943133 : Blo 1925435 6943133 := bstep (se 3 (by rfl) ⟨1301837, by rfl⟩ : syracuseStep 6943133 = 2603675) B2603675
theorem B4628755 : Blo 1925435 4628755 := bstep (se 1 (by rfl) ⟨3471566, by rfl⟩ : syracuseStep 4628755 = 6943133) B6943133
theorem B6171673 : Blo 1925435 6171673 := bstep (se 2 (by rfl) ⟨2314377, by rfl⟩ : syracuseStep 6171673 = 4628755) B4628755
theorem B8228897 : Blo 1925435 8228897 := bstep (se 2 (by rfl) ⟨3085836, by rfl⟩ : syracuseStep 8228897 = 6171673) B6171673
theorem B5485931 : Blo 1925435 5485931 := bstep (se 1 (by rfl) ⟨4114448, by rfl⟩ : syracuseStep 5485931 = 8228897) B8228897
theorem B3657287 : Blo 1925435 3657287 := bstep (se 1 (by rfl) ⟨2742965, by rfl⟩ : syracuseStep 3657287 = 5485931) B5485931
theorem B2438191 : Blo 1925435 2438191 := bstep (se 1 (by rfl) ⟨1828643, by rfl⟩ : syracuseStep 2438191 = 3657287) B3657287
theorem B3250921 : Blo 1925435 3250921 := bstep (se 2 (by rfl) ⟨1219095, by rfl⟩ : syracuseStep 3250921 = 2438191) B2438191
theorem B4334561 : Blo 1925435 4334561 := bstep (se 2 (by rfl) ⟨1625460, by rfl⟩ : syracuseStep 4334561 = 3250921) B3250921
theorem B2889707 : Blo 1925435 2889707 := bstep (se 1 (by rfl) ⟨2167280, by rfl⟩ : syracuseStep 2889707 = 4334561) B4334561
theorem B1926471 : Blo 1925435 1926471 := bstep (se 1 (by rfl) ⟨1444853, by rfl⟩ : syracuseStep 1926471 = 2889707) B2889707
theorem B2167285 : Blo 1925435 2167285 := bbase (se 5 (by rfl) ⟨101591, by rfl⟩ : syracuseStep 2167285 = 203183) (by norm_num)
theorem B2889713 : Blo 1925435 2889713 := bstep (se 2 (by rfl) ⟨1083642, by rfl⟩ : syracuseStep 2889713 = 2167285) B2167285
theorem B1926475 : Blo 1925435 1926475 := bstep (se 1 (by rfl) ⟨1444856, by rfl⟩ : syracuseStep 1926475 = 2889713) B2889713
theorem B2438201 : Blo 1925435 2438201 := bbase (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) (by norm_num)
theorem B6501869 : Blo 1925435 6501869 := bstep (se 3 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 6501869 = 2438201) B2438201
theorem B4334579 : Blo 1925435 4334579 := bstep (se 1 (by rfl) ⟨3250934, by rfl⟩ : syracuseStep 4334579 = 6501869) B6501869
theorem B2889719 : Blo 1925435 2889719 := bstep (se 1 (by rfl) ⟨2167289, by rfl⟩ : syracuseStep 2889719 = 4334579) B4334579
theorem B1926479 : Blo 1925435 1926479 := bstep (se 1 (by rfl) ⟨1444859, by rfl⟩ : syracuseStep 1926479 = 2889719) B2889719
theorem B2889725 : Blo 1925435 2889725 := bbase (se 3 (by rfl) ⟨541823, by rfl⟩ : syracuseStep 2889725 = 1083647) (by norm_num)
theorem B1926483 : Blo 1925435 1926483 := bstep (se 1 (by rfl) ⟨1444862, by rfl⟩ : syracuseStep 1926483 = 2889725) B2889725
theorem B4334597 : Blo 1925435 4334597 := bbase (se 4 (by rfl) ⟨406368, by rfl⟩ : syracuseStep 4334597 = 812737) (by norm_num)
theorem B2889731 : Blo 1925435 2889731 := bstep (se 1 (by rfl) ⟨2167298, by rfl⟩ : syracuseStep 2889731 = 4334597) B4334597
theorem B1926487 : Blo 1925435 1926487 := bstep (se 1 (by rfl) ⟨1444865, by rfl⟩ : syracuseStep 1926487 = 2889731) B2889731
theorem B3657325 : Blo 1925435 3657325 := bbase (se 3 (by rfl) ⟨685748, by rfl⟩ : syracuseStep 3657325 = 1371497) (by norm_num)
theorem B4876433 : Blo 1925435 4876433 := bstep (se 2 (by rfl) ⟨1828662, by rfl⟩ : syracuseStep 4876433 = 3657325) B3657325
theorem B3250955 : Blo 1925435 3250955 := bstep (se 1 (by rfl) ⟨2438216, by rfl⟩ : syracuseStep 3250955 = 4876433) B4876433
theorem B2167303 : Blo 1925435 2167303 := bstep (se 1 (by rfl) ⟨1625477, by rfl⟩ : syracuseStep 2167303 = 3250955) B3250955
theorem B2889737 : Blo 1925435 2889737 := bstep (se 2 (by rfl) ⟨1083651, by rfl⟩ : syracuseStep 2889737 = 2167303) B2167303
theorem B1926491 : Blo 1925435 1926491 := bstep (se 1 (by rfl) ⟨1444868, by rfl⟩ : syracuseStep 1926491 = 2889737) B2889737
theorem B9752885 : Blo 1925435 9752885 := bbase (se 5 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 9752885 = 914333) (by norm_num)
theorem B6501923 : Blo 1925435 6501923 := bstep (se 1 (by rfl) ⟨4876442, by rfl⟩ : syracuseStep 6501923 = 9752885) B9752885
theorem B4334615 : Blo 1925435 4334615 := bstep (se 1 (by rfl) ⟨3250961, by rfl⟩ : syracuseStep 4334615 = 6501923) B6501923
theorem B2889743 : Blo 1925435 2889743 := bstep (se 1 (by rfl) ⟨2167307, by rfl⟩ : syracuseStep 2889743 = 4334615) B4334615
theorem B1926495 : Blo 1925435 1926495 := bstep (se 1 (by rfl) ⟨1444871, by rfl⟩ : syracuseStep 1926495 = 2889743) B2889743
theorem B2889749 : Blo 1925435 2889749 := bbase (se 6 (by rfl) ⟨67728, by rfl⟩ : syracuseStep 2889749 = 135457) (by norm_num)
theorem B1926499 : Blo 1925435 1926499 := bstep (se 1 (by rfl) ⟨1444874, by rfl⟩ : syracuseStep 1926499 = 2889749) B2889749
theorem B4942997 : Blo 1925435 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B3295331 : Blo 1925435 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2196887 : Blo 1925435 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B23433461 : Blo 1925435 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B15622307 : Blo 1925435 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B10414871 : Blo 1925435 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B6943247 : Blo 1925435 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B4628831 : Blo 1925435 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B12343549 : Blo 1925435 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B16458065 : Blo 1925435 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B10972043 : Blo 1925435 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B7314695 : Blo 1925435 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B4876463 : Blo 1925435 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B3250975 : Blo 1925435 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B4334633 : Blo 1925435 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B2889755 : Blo 1925435 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B1926503 : Blo 1925435 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B2167321 : Blo 1925435 2167321 := bbase (se 2 (by rfl) ⟨812745, by rfl⟩ : syracuseStep 2167321 = 1625491) (by norm_num)
theorem B2889761 : Blo 1925435 2889761 := bstep (se 2 (by rfl) ⟨1083660, by rfl⟩ : syracuseStep 2889761 = 2167321) B2167321
theorem B1926507 : Blo 1925435 1926507 := bstep (se 1 (by rfl) ⟨1444880, by rfl⟩ : syracuseStep 1926507 = 2889761) B2889761
theorem B7314725 : Blo 1925435 7314725 := bbase (se 4 (by rfl) ⟨685755, by rfl⟩ : syracuseStep 7314725 = 1371511) (by norm_num)
theorem B4876483 : Blo 1925435 4876483 := bstep (se 1 (by rfl) ⟨3657362, by rfl⟩ : syracuseStep 4876483 = 7314725) B7314725
theorem B6501977 : Blo 1925435 6501977 := bstep (se 2 (by rfl) ⟨2438241, by rfl⟩ : syracuseStep 6501977 = 4876483) B4876483
theorem B4334651 : Blo 1925435 4334651 := bstep (se 1 (by rfl) ⟨3250988, by rfl⟩ : syracuseStep 4334651 = 6501977) B6501977
theorem B2889767 : Blo 1925435 2889767 := bstep (se 1 (by rfl) ⟨2167325, by rfl⟩ : syracuseStep 2889767 = 4334651) B4334651
theorem B1926511 : Blo 1925435 1926511 := bstep (se 1 (by rfl) ⟨1444883, by rfl⟩ : syracuseStep 1926511 = 2889767) B2889767
theorem B2889773 : Blo 1925435 2889773 := bbase (se 3 (by rfl) ⟨541832, by rfl⟩ : syracuseStep 2889773 = 1083665) (by norm_num)
theorem B1926515 : Blo 1925435 1926515 := bstep (se 1 (by rfl) ⟨1444886, by rfl⟩ : syracuseStep 1926515 = 2889773) B2889773
theorem B4334669 : Blo 1925435 4334669 := bbase (se 3 (by rfl) ⟨812750, by rfl⟩ : syracuseStep 4334669 = 1625501) (by norm_num)
theorem B2889779 : Blo 1925435 2889779 := bstep (se 1 (by rfl) ⟨2167334, by rfl⟩ : syracuseStep 2889779 = 4334669) B4334669
theorem B1926519 : Blo 1925435 1926519 := bstep (se 1 (by rfl) ⟨1444889, by rfl⟩ : syracuseStep 1926519 = 2889779) B2889779
theorem B2438257 : Blo 1925435 2438257 := bbase (se 2 (by rfl) ⟨914346, by rfl⟩ : syracuseStep 2438257 = 1828693) (by norm_num)
theorem B3251009 : Blo 1925435 3251009 := bstep (se 2 (by rfl) ⟨1219128, by rfl⟩ : syracuseStep 3251009 = 2438257) B2438257
theorem B2167339 : Blo 1925435 2167339 := bstep (se 1 (by rfl) ⟨1625504, by rfl⟩ : syracuseStep 2167339 = 3251009) B3251009
theorem B2889785 : Blo 1925435 2889785 := bstep (se 2 (by rfl) ⟨1083669, by rfl⟩ : syracuseStep 2889785 = 2167339) B2167339
theorem B1926523 : Blo 1925435 1926523 := bstep (se 1 (by rfl) ⟨1444892, by rfl⟩ : syracuseStep 1926523 = 2889785) B2889785
theorem B6943333 : Blo 1925435 6943333 := bbase (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) (by norm_num)
theorem B9257777 : Blo 1925435 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B6171851 : Blo 1925435 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B4114567 : Blo 1925435 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B21944357 : Blo 1925435 21944357 := bstep (se 4 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 21944357 = 4114567) B4114567
theorem B14629571 : Blo 1925435 14629571 := bstep (se 1 (by rfl) ⟨10972178, by rfl⟩ : syracuseStep 14629571 = 21944357) B21944357
theorem B9753047 : Blo 1925435 9753047 := bstep (se 1 (by rfl) ⟨7314785, by rfl⟩ : syracuseStep 9753047 = 14629571) B14629571
theorem B6502031 : Blo 1925435 6502031 := bstep (se 1 (by rfl) ⟨4876523, by rfl⟩ : syracuseStep 6502031 = 9753047) B9753047
theorem B4334687 : Blo 1925435 4334687 := bstep (se 1 (by rfl) ⟨3251015, by rfl⟩ : syracuseStep 4334687 = 6502031) B6502031
theorem B2889791 : Blo 1925435 2889791 := bstep (se 1 (by rfl) ⟨2167343, by rfl⟩ : syracuseStep 2889791 = 4334687) B4334687
theorem B1926527 : Blo 1925435 1926527 := bstep (se 1 (by rfl) ⟨1444895, by rfl⟩ : syracuseStep 1926527 = 2889791) B2889791
theorem B2889797 : Blo 1925435 2889797 := bbase (se 4 (by rfl) ⟨270918, by rfl⟩ : syracuseStep 2889797 = 541837) (by norm_num)
theorem B1926531 : Blo 1925435 1926531 := bstep (se 1 (by rfl) ⟨1444898, by rfl⟩ : syracuseStep 1926531 = 2889797) B2889797
theorem B3251029 : Blo 1925435 3251029 := bbase (se 9 (by rfl) ⟨9524, by rfl⟩ : syracuseStep 3251029 = 19049) (by norm_num)
theorem B4334705 : Blo 1925435 4334705 := bstep (se 2 (by rfl) ⟨1625514, by rfl⟩ : syracuseStep 4334705 = 3251029) B3251029
theorem B2889803 : Blo 1925435 2889803 := bstep (se 1 (by rfl) ⟨2167352, by rfl⟩ : syracuseStep 2889803 = 4334705) B4334705
theorem B1926535 : Blo 1925435 1926535 := bstep (se 1 (by rfl) ⟨1444901, by rfl⟩ : syracuseStep 1926535 = 2889803) B2889803
theorem B2167357 : Blo 1925435 2167357 := bbase (se 3 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 2167357 = 812759) (by norm_num)
theorem B2889809 : Blo 1925435 2889809 := bstep (se 2 (by rfl) ⟨1083678, by rfl⟩ : syracuseStep 2889809 = 2167357) B2167357
theorem B1926539 : Blo 1925435 1926539 := bstep (se 1 (by rfl) ⟨1444904, by rfl⟩ : syracuseStep 1926539 = 2889809) B2889809
theorem B6502085 : Blo 1925435 6502085 := bbase (se 4 (by rfl) ⟨609570, by rfl⟩ : syracuseStep 6502085 = 1219141) (by norm_num)
theorem B4334723 : Blo 1925435 4334723 := bstep (se 1 (by rfl) ⟨3251042, by rfl⟩ : syracuseStep 4334723 = 6502085) B6502085
theorem B2889815 : Blo 1925435 2889815 := bstep (se 1 (by rfl) ⟨2167361, by rfl⟩ : syracuseStep 2889815 = 4334723) B4334723
theorem B1926543 : Blo 1925435 1926543 := bstep (se 1 (by rfl) ⟨1444907, by rfl⟩ : syracuseStep 1926543 = 2889815) B2889815
theorem B2889821 : Blo 1925435 2889821 := bbase (se 3 (by rfl) ⟨541841, by rfl⟩ : syracuseStep 2889821 = 1083683) (by norm_num)
theorem B1926547 : Blo 1925435 1926547 := bstep (se 1 (by rfl) ⟨1444910, by rfl⟩ : syracuseStep 1926547 = 2889821) B2889821
theorem B4334741 : Blo 1925435 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B2889827 : Blo 1925435 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B1926551 : Blo 1925435 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B2743085 : Blo 1925435 2743085 := bbase (se 3 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 2743085 = 1028657) (by norm_num)
theorem B7314893 : Blo 1925435 7314893 := bstep (se 3 (by rfl) ⟨1371542, by rfl⟩ : syracuseStep 7314893 = 2743085) B2743085
theorem B4876595 : Blo 1925435 4876595 := bstep (se 1 (by rfl) ⟨3657446, by rfl⟩ : syracuseStep 4876595 = 7314893) B7314893
theorem B3251063 : Blo 1925435 3251063 := bstep (se 1 (by rfl) ⟨2438297, by rfl⟩ : syracuseStep 3251063 = 4876595) B4876595
theorem B2167375 : Blo 1925435 2167375 := bstep (se 1 (by rfl) ⟨1625531, by rfl⟩ : syracuseStep 2167375 = 3251063) B3251063
theorem B2889833 : Blo 1925435 2889833 := bstep (se 2 (by rfl) ⟨1083687, by rfl⟩ : syracuseStep 2889833 = 2167375) B2167375
theorem B1926555 : Blo 1925435 1926555 := bstep (se 1 (by rfl) ⟨1444916, by rfl⟩ : syracuseStep 1926555 = 2889833) B2889833
theorem B18515861 : Blo 1925435 18515861 := bbase (se 6 (by rfl) ⟨433965, by rfl⟩ : syracuseStep 18515861 = 867931) (by norm_num)
theorem B12343907 : Blo 1925435 12343907 := bstep (se 1 (by rfl) ⟨9257930, by rfl⟩ : syracuseStep 12343907 = 18515861) B18515861
theorem B8229271 : Blo 1925435 8229271 := bstep (se 1 (by rfl) ⟨6171953, by rfl⟩ : syracuseStep 8229271 = 12343907) B12343907
theorem B10972361 : Blo 1925435 10972361 := bstep (se 2 (by rfl) ⟨4114635, by rfl⟩ : syracuseStep 10972361 = 8229271) B8229271
theorem B7314907 : Blo 1925435 7314907 := bstep (se 1 (by rfl) ⟨5486180, by rfl⟩ : syracuseStep 7314907 = 10972361) B10972361
theorem B9753209 : Blo 1925435 9753209 := bstep (se 2 (by rfl) ⟨3657453, by rfl⟩ : syracuseStep 9753209 = 7314907) B7314907
theorem B6502139 : Blo 1925435 6502139 := bstep (se 1 (by rfl) ⟨4876604, by rfl⟩ : syracuseStep 6502139 = 9753209) B9753209
theorem B4334759 : Blo 1925435 4334759 := bstep (se 1 (by rfl) ⟨3251069, by rfl⟩ : syracuseStep 4334759 = 6502139) B6502139
theorem B2889839 : Blo 1925435 2889839 := bstep (se 1 (by rfl) ⟨2167379, by rfl⟩ : syracuseStep 2889839 = 4334759) B4334759
theorem B1926559 : Blo 1925435 1926559 := bstep (se 1 (by rfl) ⟨1444919, by rfl⟩ : syracuseStep 1926559 = 2889839) B2889839
theorem B2889845 : Blo 1925435 2889845 := bbase (se 5 (by rfl) ⟨135461, by rfl⟩ : syracuseStep 2889845 = 270923) (by norm_num)
theorem B1926563 : Blo 1925435 1926563 := bstep (se 1 (by rfl) ⟨1444922, by rfl⟩ : syracuseStep 1926563 = 2889845) B2889845
theorem B3657469 : Blo 1925435 3657469 := bbase (se 3 (by rfl) ⟨685775, by rfl⟩ : syracuseStep 3657469 = 1371551) (by norm_num)
theorem B4876625 : Blo 1925435 4876625 := bstep (se 2 (by rfl) ⟨1828734, by rfl⟩ : syracuseStep 4876625 = 3657469) B3657469
theorem B3251083 : Blo 1925435 3251083 := bstep (se 1 (by rfl) ⟨2438312, by rfl⟩ : syracuseStep 3251083 = 4876625) B4876625
theorem B4334777 : Blo 1925435 4334777 := bstep (se 2 (by rfl) ⟨1625541, by rfl⟩ : syracuseStep 4334777 = 3251083) B3251083
theorem B2889851 : Blo 1925435 2889851 := bstep (se 1 (by rfl) ⟨2167388, by rfl⟩ : syracuseStep 2889851 = 4334777) B4334777
theorem B1926567 : Blo 1925435 1926567 := bstep (se 1 (by rfl) ⟨1444925, by rfl⟩ : syracuseStep 1926567 = 2889851) B2889851
theorem B2167393 : Blo 1925435 2167393 := bbase (se 2 (by rfl) ⟨812772, by rfl⟩ : syracuseStep 2167393 = 1625545) (by norm_num)
theorem B2889857 : Blo 1925435 2889857 := bstep (se 2 (by rfl) ⟨1083696, by rfl⟩ : syracuseStep 2889857 = 2167393) B2167393
theorem B1926571 : Blo 1925435 1926571 := bstep (se 1 (by rfl) ⟨1444928, by rfl⟩ : syracuseStep 1926571 = 2889857) B2889857
theorem B4876645 : Blo 1925435 4876645 := bbase (se 4 (by rfl) ⟨457185, by rfl⟩ : syracuseStep 4876645 = 914371) (by norm_num)
theorem B6502193 : Blo 1925435 6502193 := bstep (se 2 (by rfl) ⟨2438322, by rfl⟩ : syracuseStep 6502193 = 4876645) B4876645
theorem B4334795 : Blo 1925435 4334795 := bstep (se 1 (by rfl) ⟨3251096, by rfl⟩ : syracuseStep 4334795 = 6502193) B6502193
theorem B2889863 : Blo 1925435 2889863 := bstep (se 1 (by rfl) ⟨2167397, by rfl⟩ : syracuseStep 2889863 = 4334795) B4334795
theorem B1926575 : Blo 1925435 1926575 := bstep (se 1 (by rfl) ⟨1444931, by rfl⟩ : syracuseStep 1926575 = 2889863) B2889863
theorem B2889869 : Blo 1925435 2889869 := bbase (se 3 (by rfl) ⟨541850, by rfl⟩ : syracuseStep 2889869 = 1083701) (by norm_num)
theorem B1926579 : Blo 1925435 1926579 := bstep (se 1 (by rfl) ⟨1444934, by rfl⟩ : syracuseStep 1926579 = 2889869) B2889869
theorem B4334813 : Blo 1925435 4334813 := bbase (se 3 (by rfl) ⟨812777, by rfl⟩ : syracuseStep 4334813 = 1625555) (by norm_num)
theorem B2889875 : Blo 1925435 2889875 := bstep (se 1 (by rfl) ⟨2167406, by rfl⟩ : syracuseStep 2889875 = 4334813) B4334813
theorem B1926583 : Blo 1925435 1926583 := bstep (se 1 (by rfl) ⟨1444937, by rfl⟩ : syracuseStep 1926583 = 2889875) B2889875
theorem B3251117 : Blo 1925435 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B2167411 : Blo 1925435 2167411 := bstep (se 1 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 2167411 = 3251117) B3251117
theorem B2889881 : Blo 1925435 2889881 := bstep (se 2 (by rfl) ⟨1083705, by rfl⟩ : syracuseStep 2889881 = 2167411) B2167411
theorem B1926587 : Blo 1925435 1926587 := bstep (se 1 (by rfl) ⟨1444940, by rfl⟩ : syracuseStep 1926587 = 2889881) B2889881
theorem B7918085 : Blo 1925435 7918085 := bbase (se 4 (by rfl) ⟨742320, by rfl⟩ : syracuseStep 7918085 = 1484641) (by norm_num)
theorem B21114893 : Blo 1925435 21114893 := bstep (se 3 (by rfl) ⟨3959042, by rfl⟩ : syracuseStep 21114893 = 7918085) B7918085
theorem B14076595 : Blo 1925435 14076595 := bstep (se 1 (by rfl) ⟨10557446, by rfl⟩ : syracuseStep 14076595 = 21114893) B21114893
theorem B18768793 : Blo 1925435 18768793 := bstep (se 2 (by rfl) ⟨7038297, by rfl⟩ : syracuseStep 18768793 = 14076595) B14076595
theorem B25025057 : Blo 1925435 25025057 := bstep (se 2 (by rfl) ⟨9384396, by rfl⟩ : syracuseStep 25025057 = 18768793) B18768793
theorem B16683371 : Blo 1925435 16683371 := bstep (se 1 (by rfl) ⟨12512528, by rfl⟩ : syracuseStep 16683371 = 25025057) B25025057
theorem B11122247 : Blo 1925435 11122247 := bstep (se 1 (by rfl) ⟨8341685, by rfl⟩ : syracuseStep 11122247 = 16683371) B16683371
theorem B7414831 : Blo 1925435 7414831 := bstep (se 1 (by rfl) ⟨5561123, by rfl⟩ : syracuseStep 7414831 = 11122247) B11122247
theorem B9886441 : Blo 1925435 9886441 := bstep (se 2 (by rfl) ⟨3707415, by rfl⟩ : syracuseStep 9886441 = 7414831) B7414831
theorem B13181921 : Blo 1925435 13181921 := bstep (se 2 (by rfl) ⟨4943220, by rfl⟩ : syracuseStep 13181921 = 9886441) B9886441
theorem B8787947 : Blo 1925435 8787947 := bstep (se 1 (by rfl) ⟨6590960, by rfl⟩ : syracuseStep 8787947 = 13181921) B13181921
theorem B23434525 : Blo 1925435 23434525 := bstep (se 3 (by rfl) ⟨4393973, by rfl⟩ : syracuseStep 23434525 = 8787947) B8787947
theorem B124984133 : Blo 1925435 124984133 := bstep (se 4 (by rfl) ⟨11717262, by rfl⟩ : syracuseStep 124984133 = 23434525) B23434525
theorem B83322755 : Blo 1925435 83322755 := bstep (se 1 (by rfl) ⟨62492066, by rfl⟩ : syracuseStep 83322755 = 124984133) B124984133
theorem B55548503 : Blo 1925435 55548503 := bstep (se 1 (by rfl) ⟨41661377, by rfl⟩ : syracuseStep 55548503 = 83322755) B83322755
theorem B37032335 : Blo 1925435 37032335 := bstep (se 1 (by rfl) ⟨27774251, by rfl⟩ : syracuseStep 37032335 = 55548503) B55548503
theorem B24688223 : Blo 1925435 24688223 := bstep (se 1 (by rfl) ⟨18516167, by rfl⟩ : syracuseStep 24688223 = 37032335) B37032335
theorem B16458815 : Blo 1925435 16458815 := bstep (se 1 (by rfl) ⟨12344111, by rfl⟩ : syracuseStep 16458815 = 24688223) B24688223
theorem B10972543 : Blo 1925435 10972543 := bstep (se 1 (by rfl) ⟨8229407, by rfl⟩ : syracuseStep 10972543 = 16458815) B16458815
theorem B14630057 : Blo 1925435 14630057 := bstep (se 2 (by rfl) ⟨5486271, by rfl⟩ : syracuseStep 14630057 = 10972543) B10972543
theorem B9753371 : Blo 1925435 9753371 := bstep (se 1 (by rfl) ⟨7315028, by rfl⟩ : syracuseStep 9753371 = 14630057) B14630057
theorem B6502247 : Blo 1925435 6502247 := bstep (se 1 (by rfl) ⟨4876685, by rfl⟩ : syracuseStep 6502247 = 9753371) B9753371
theorem B4334831 : Blo 1925435 4334831 := bstep (se 1 (by rfl) ⟨3251123, by rfl⟩ : syracuseStep 4334831 = 6502247) B6502247
theorem B2889887 : Blo 1925435 2889887 := bstep (se 1 (by rfl) ⟨2167415, by rfl⟩ : syracuseStep 2889887 = 4334831) B4334831
theorem B1926591 : Blo 1925435 1926591 := bstep (se 1 (by rfl) ⟨1444943, by rfl⟩ : syracuseStep 1926591 = 2889887) B2889887
theorem B2889893 : Blo 1925435 2889893 := bbase (se 4 (by rfl) ⟨270927, by rfl⟩ : syracuseStep 2889893 = 541855) (by norm_num)
theorem B1926595 : Blo 1925435 1926595 := bstep (se 1 (by rfl) ⟨1444946, by rfl⟩ : syracuseStep 1926595 = 2889893) B2889893
theorem B2438353 : Blo 1925435 2438353 := bbase (se 2 (by rfl) ⟨914382, by rfl⟩ : syracuseStep 2438353 = 1828765) (by norm_num)
theorem B3251137 : Blo 1925435 3251137 := bstep (se 2 (by rfl) ⟨1219176, by rfl⟩ : syracuseStep 3251137 = 2438353) B2438353
theorem B4334849 : Blo 1925435 4334849 := bstep (se 2 (by rfl) ⟨1625568, by rfl⟩ : syracuseStep 4334849 = 3251137) B3251137
theorem B2889899 : Blo 1925435 2889899 := bstep (se 1 (by rfl) ⟨2167424, by rfl⟩ : syracuseStep 2889899 = 4334849) B4334849
theorem B1926599 : Blo 1925435 1926599 := bstep (se 1 (by rfl) ⟨1444949, by rfl⟩ : syracuseStep 1926599 = 2889899) B2889899
theorem B2167429 : Blo 1925435 2167429 := bbase (se 4 (by rfl) ⟨203196, by rfl⟩ : syracuseStep 2167429 = 406393) (by norm_num)
theorem B2889905 : Blo 1925435 2889905 := bstep (se 2 (by rfl) ⟨1083714, by rfl⟩ : syracuseStep 2889905 = 2167429) B2167429
theorem B1926603 : Blo 1925435 1926603 := bstep (se 1 (by rfl) ⟨1444952, by rfl⟩ : syracuseStep 1926603 = 2889905) B2889905
theorem B2314541 : Blo 1925435 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B6172109 : Blo 1925435 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B4114739 : Blo 1925435 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B2743159 : Blo 1925435 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B3657545 : Blo 1925435 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B2438363 : Blo 1925435 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B6502301 : Blo 1925435 6502301 := bstep (se 3 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 6502301 = 2438363) B2438363
theorem B4334867 : Blo 1925435 4334867 := bstep (se 1 (by rfl) ⟨3251150, by rfl⟩ : syracuseStep 4334867 = 6502301) B6502301
theorem B2889911 : Blo 1925435 2889911 := bstep (se 1 (by rfl) ⟨2167433, by rfl⟩ : syracuseStep 2889911 = 4334867) B4334867
theorem B1926607 : Blo 1925435 1926607 := bstep (se 1 (by rfl) ⟨1444955, by rfl⟩ : syracuseStep 1926607 = 2889911) B2889911
theorem B2889917 : Blo 1925435 2889917 := bbase (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) (by norm_num)
theorem B1926611 : Blo 1925435 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B4334885 : Blo 1925435 4334885 := bbase (se 4 (by rfl) ⟨406395, by rfl⟩ : syracuseStep 4334885 = 812791) (by norm_num)
theorem B2889923 : Blo 1925435 2889923 := bstep (se 1 (by rfl) ⟨2167442, by rfl⟩ : syracuseStep 2889923 = 4334885) B4334885
theorem B1926615 : Blo 1925435 1926615 := bstep (se 1 (by rfl) ⟨1444961, by rfl⟩ : syracuseStep 1926615 = 2889923) B2889923
theorem B4876757 : Blo 1925435 4876757 := bbase (se 7 (by rfl) ⟨57149, by rfl⟩ : syracuseStep 4876757 = 114299) (by norm_num)
theorem B3251171 : Blo 1925435 3251171 := bstep (se 1 (by rfl) ⟨2438378, by rfl⟩ : syracuseStep 3251171 = 4876757) B4876757
theorem B2167447 : Blo 1925435 2167447 := bstep (se 1 (by rfl) ⟨1625585, by rfl⟩ : syracuseStep 2167447 = 3251171) B3251171
theorem B2889929 : Blo 1925435 2889929 := bstep (se 2 (by rfl) ⟨1083723, by rfl⟩ : syracuseStep 2889929 = 2167447) B2167447
theorem B1926619 : Blo 1925435 1926619 := bstep (se 1 (by rfl) ⟨1444964, by rfl⟩ : syracuseStep 1926619 = 2889929) B2889929
theorem B8455637 : Blo 1925435 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B22548365 : Blo 1925435 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B15032243 : Blo 1925435 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B10021495 : Blo 1925435 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B13361993 : Blo 1925435 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B8907995 : Blo 1925435 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B23754653 : Blo 1925435 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B15836435 : Blo 1925435 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B10557623 : Blo 1925435 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B7038415 : Blo 1925435 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B9384553 : Blo 1925435 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B12512737 : Blo 1925435 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B66734597 : Blo 1925435 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B44489731 : Blo 1925435 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B59319641 : Blo 1925435 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B158185709 : Blo 1925435 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B105457139 : Blo 1925435 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B70304759 : Blo 1925435 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B46869839 : Blo 1925435 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B31246559 : Blo 1925435 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B20831039 : Blo 1925435 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B13887359 : Blo 1925435 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B9258239 : Blo 1925435 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B6172159 : Blo 1925435 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B8229545 : Blo 1925435 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B5486363 : Blo 1925435 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B3657575 : Blo 1925435 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B9753533 : Blo 1925435 9753533 := bstep (se 3 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 9753533 = 3657575) B3657575
theorem B6502355 : Blo 1925435 6502355 := bstep (se 1 (by rfl) ⟨4876766, by rfl⟩ : syracuseStep 6502355 = 9753533) B9753533
theorem B4334903 : Blo 1925435 4334903 := bstep (se 1 (by rfl) ⟨3251177, by rfl⟩ : syracuseStep 4334903 = 6502355) B6502355
theorem B2889935 : Blo 1925435 2889935 := bstep (se 1 (by rfl) ⟨2167451, by rfl⟩ : syracuseStep 2889935 = 4334903) B4334903
theorem B1926623 : Blo 1925435 1926623 := bstep (se 1 (by rfl) ⟨1444967, by rfl⟩ : syracuseStep 1926623 = 2889935) B2889935
theorem B2889941 : Blo 1925435 2889941 := bbase (se 7 (by rfl) ⟨33866, by rfl⟩ : syracuseStep 2889941 = 67733) (by norm_num)
theorem B1926627 : Blo 1925435 1926627 := bstep (se 1 (by rfl) ⟨1444970, by rfl⟩ : syracuseStep 1926627 = 2889941) B2889941
theorem B3086093 : Blo 1925435 3086093 := bbase (se 3 (by rfl) ⟨578642, by rfl⟩ : syracuseStep 3086093 = 1157285) (by norm_num)
theorem B2057395 : Blo 1925435 2057395 := bstep (se 1 (by rfl) ⟨1543046, by rfl⟩ : syracuseStep 2057395 = 3086093) B3086093
theorem B2743193 : Blo 1925435 2743193 := bstep (se 2 (by rfl) ⟨1028697, by rfl⟩ : syracuseStep 2743193 = 2057395) B2057395
theorem B7315181 : Blo 1925435 7315181 := bstep (se 3 (by rfl) ⟨1371596, by rfl⟩ : syracuseStep 7315181 = 2743193) B2743193
theorem B4876787 : Blo 1925435 4876787 := bstep (se 1 (by rfl) ⟨3657590, by rfl⟩ : syracuseStep 4876787 = 7315181) B7315181
theorem B3251191 : Blo 1925435 3251191 := bstep (se 1 (by rfl) ⟨2438393, by rfl⟩ : syracuseStep 3251191 = 4876787) B4876787
theorem B4334921 : Blo 1925435 4334921 := bstep (se 2 (by rfl) ⟨1625595, by rfl⟩ : syracuseStep 4334921 = 3251191) B3251191
theorem B2889947 : Blo 1925435 2889947 := bstep (se 1 (by rfl) ⟨2167460, by rfl⟩ : syracuseStep 2889947 = 4334921) B4334921
theorem B1926631 : Blo 1925435 1926631 := bstep (se 1 (by rfl) ⟨1444973, by rfl⟩ : syracuseStep 1926631 = 2889947) B2889947
theorem B2167465 : Blo 1925435 2167465 := bbase (se 2 (by rfl) ⟨812799, by rfl⟩ : syracuseStep 2167465 = 1625599) (by norm_num)
theorem B2889953 : Blo 1925435 2889953 := bstep (se 2 (by rfl) ⟨1083732, by rfl⟩ : syracuseStep 2889953 = 2167465) B2167465
theorem B1926635 : Blo 1925435 1926635 := bstep (se 1 (by rfl) ⟨1444976, by rfl⟩ : syracuseStep 1926635 = 2889953) B2889953
theorem B3471869 : Blo 1925435 3471869 := bbase (se 3 (by rfl) ⟨650975, by rfl⟩ : syracuseStep 3471869 = 1301951) (by norm_num)
theorem B2314579 : Blo 1925435 2314579 := bstep (se 1 (by rfl) ⟨1735934, by rfl⟩ : syracuseStep 2314579 = 3471869) B3471869
theorem B3086105 : Blo 1925435 3086105 := bstep (se 2 (by rfl) ⟨1157289, by rfl⟩ : syracuseStep 3086105 = 2314579) B2314579
theorem B8229613 : Blo 1925435 8229613 := bstep (se 3 (by rfl) ⟨1543052, by rfl⟩ : syracuseStep 8229613 = 3086105) B3086105
theorem B10972817 : Blo 1925435 10972817 := bstep (se 2 (by rfl) ⟨4114806, by rfl⟩ : syracuseStep 10972817 = 8229613) B8229613
theorem B7315211 : Blo 1925435 7315211 := bstep (se 1 (by rfl) ⟨5486408, by rfl⟩ : syracuseStep 7315211 = 10972817) B10972817
theorem B4876807 : Blo 1925435 4876807 := bstep (se 1 (by rfl) ⟨3657605, by rfl⟩ : syracuseStep 4876807 = 7315211) B7315211
theorem B6502409 : Blo 1925435 6502409 := bstep (se 2 (by rfl) ⟨2438403, by rfl⟩ : syracuseStep 6502409 = 4876807) B4876807
theorem B4334939 : Blo 1925435 4334939 := bstep (se 1 (by rfl) ⟨3251204, by rfl⟩ : syracuseStep 4334939 = 6502409) B6502409
theorem B2889959 : Blo 1925435 2889959 := bstep (se 1 (by rfl) ⟨2167469, by rfl⟩ : syracuseStep 2889959 = 4334939) B4334939
theorem B1926639 : Blo 1925435 1926639 := bstep (se 1 (by rfl) ⟨1444979, by rfl⟩ : syracuseStep 1926639 = 2889959) B2889959
theorem B2889965 : Blo 1925435 2889965 := bbase (se 3 (by rfl) ⟨541868, by rfl⟩ : syracuseStep 2889965 = 1083737) (by norm_num)
theorem B1926643 : Blo 1925435 1926643 := bstep (se 1 (by rfl) ⟨1444982, by rfl⟩ : syracuseStep 1926643 = 2889965) B2889965
theorem B4334957 : Blo 1925435 4334957 := bbase (se 3 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 4334957 = 1625609) (by norm_num)
theorem B2889971 : Blo 1925435 2889971 := bstep (se 1 (by rfl) ⟨2167478, by rfl⟩ : syracuseStep 2889971 = 4334957) B4334957
theorem B1926647 : Blo 1925435 1926647 := bstep (se 1 (by rfl) ⟨1444985, by rfl⟩ : syracuseStep 1926647 = 2889971) B2889971
theorem B3657629 : Blo 1925435 3657629 := bbase (se 3 (by rfl) ⟨685805, by rfl⟩ : syracuseStep 3657629 = 1371611) (by norm_num)
theorem B2438419 : Blo 1925435 2438419 := bstep (se 1 (by rfl) ⟨1828814, by rfl⟩ : syracuseStep 2438419 = 3657629) B3657629
theorem B3251225 : Blo 1925435 3251225 := bstep (se 2 (by rfl) ⟨1219209, by rfl⟩ : syracuseStep 3251225 = 2438419) B2438419
theorem B2167483 : Blo 1925435 2167483 := bstep (se 1 (by rfl) ⟨1625612, by rfl⟩ : syracuseStep 2167483 = 3251225) B3251225
theorem B2889977 : Blo 1925435 2889977 := bstep (se 2 (by rfl) ⟨1083741, by rfl⟩ : syracuseStep 2889977 = 2167483) B2167483
theorem B1926651 : Blo 1925435 1926651 := bstep (se 1 (by rfl) ⟨1444988, by rfl⟩ : syracuseStep 1926651 = 2889977) B2889977
theorem B20831381 : Blo 1925435 20831381 := bbase (se 6 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 20831381 = 976471) (by norm_num)
theorem B13887587 : Blo 1925435 13887587 := bstep (se 1 (by rfl) ⟨10415690, by rfl⟩ : syracuseStep 13887587 = 20831381) B20831381
theorem B9258391 : Blo 1925435 9258391 := bstep (se 1 (by rfl) ⟨6943793, by rfl⟩ : syracuseStep 9258391 = 13887587) B13887587
theorem B49378085 : Blo 1925435 49378085 := bstep (se 4 (by rfl) ⟨4629195, by rfl⟩ : syracuseStep 49378085 = 9258391) B9258391
theorem B32918723 : Blo 1925435 32918723 := bstep (se 1 (by rfl) ⟨24689042, by rfl⟩ : syracuseStep 32918723 = 49378085) B49378085
theorem B21945815 : Blo 1925435 21945815 := bstep (se 1 (by rfl) ⟨16459361, by rfl⟩ : syracuseStep 21945815 = 32918723) B32918723
theorem B14630543 : Blo 1925435 14630543 := bstep (se 1 (by rfl) ⟨10972907, by rfl⟩ : syracuseStep 14630543 = 21945815) B21945815
theorem B9753695 : Blo 1925435 9753695 := bstep (se 1 (by rfl) ⟨7315271, by rfl⟩ : syracuseStep 9753695 = 14630543) B14630543
theorem B6502463 : Blo 1925435 6502463 := bstep (se 1 (by rfl) ⟨4876847, by rfl⟩ : syracuseStep 6502463 = 9753695) B9753695
theorem B4334975 : Blo 1925435 4334975 := bstep (se 1 (by rfl) ⟨3251231, by rfl⟩ : syracuseStep 4334975 = 6502463) B6502463
theorem B2889983 : Blo 1925435 2889983 := bstep (se 1 (by rfl) ⟨2167487, by rfl⟩ : syracuseStep 2889983 = 4334975) B4334975
theorem B1926655 : Blo 1925435 1926655 := bstep (se 1 (by rfl) ⟨1444991, by rfl⟩ : syracuseStep 1926655 = 2889983) B2889983
theorem B2889989 : Blo 1925435 2889989 := bbase (se 4 (by rfl) ⟨270936, by rfl⟩ : syracuseStep 2889989 = 541873) (by norm_num)
theorem B1926659 : Blo 1925435 1926659 := bstep (se 1 (by rfl) ⟨1444994, by rfl⟩ : syracuseStep 1926659 = 2889989) B2889989
theorem B3251245 : Blo 1925435 3251245 := bbase (se 3 (by rfl) ⟨609608, by rfl⟩ : syracuseStep 3251245 = 1219217) (by norm_num)
theorem B4334993 : Blo 1925435 4334993 := bstep (se 2 (by rfl) ⟨1625622, by rfl⟩ : syracuseStep 4334993 = 3251245) B3251245
theorem B2889995 : Blo 1925435 2889995 := bstep (se 1 (by rfl) ⟨2167496, by rfl⟩ : syracuseStep 2889995 = 4334993) B4334993
theorem B1926663 : Blo 1925435 1926663 := bstep (se 1 (by rfl) ⟨1444997, by rfl⟩ : syracuseStep 1926663 = 2889995) B2889995
theorem B2167501 : Blo 1925435 2167501 := bbase (se 3 (by rfl) ⟨406406, by rfl⟩ : syracuseStep 2167501 = 812813) (by norm_num)
theorem B2890001 : Blo 1925435 2890001 := bstep (se 2 (by rfl) ⟨1083750, by rfl⟩ : syracuseStep 2890001 = 2167501) B2167501
theorem B1926667 : Blo 1925435 1926667 := bstep (se 1 (by rfl) ⟨1445000, by rfl⟩ : syracuseStep 1926667 = 2890001) B2890001
theorem B6502517 : Blo 1925435 6502517 := bbase (se 5 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 6502517 = 609611) (by norm_num)
theorem B4335011 : Blo 1925435 4335011 := bstep (se 1 (by rfl) ⟨3251258, by rfl⟩ : syracuseStep 4335011 = 6502517) B6502517
theorem B2890007 : Blo 1925435 2890007 := bstep (se 1 (by rfl) ⟨2167505, by rfl⟩ : syracuseStep 2890007 = 4335011) B4335011
theorem B1926671 : Blo 1925435 1926671 := bstep (se 1 (by rfl) ⟨1445003, by rfl⟩ : syracuseStep 1926671 = 2890007) B2890007
theorem B2890013 : Blo 1925435 2890013 := bbase (se 3 (by rfl) ⟨541877, by rfl⟩ : syracuseStep 2890013 = 1083755) (by norm_num)
theorem B1926675 : Blo 1925435 1926675 := bstep (se 1 (by rfl) ⟨1445006, by rfl⟩ : syracuseStep 1926675 = 2890013) B2890013
theorem B4335029 : Blo 1925435 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B2890019 : Blo 1925435 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B1926679 : Blo 1925435 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B4114901 : Blo 1925435 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B10973069 : Blo 1925435 10973069 := bstep (se 3 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 10973069 = 4114901) B4114901
theorem B7315379 : Blo 1925435 7315379 := bstep (se 1 (by rfl) ⟨5486534, by rfl⟩ : syracuseStep 7315379 = 10973069) B10973069
theorem B4876919 : Blo 1925435 4876919 := bstep (se 1 (by rfl) ⟨3657689, by rfl⟩ : syracuseStep 4876919 = 7315379) B7315379
theorem B3251279 : Blo 1925435 3251279 := bstep (se 1 (by rfl) ⟨2438459, by rfl⟩ : syracuseStep 3251279 = 4876919) B4876919
theorem B2167519 : Blo 1925435 2167519 := bstep (se 1 (by rfl) ⟨1625639, by rfl⟩ : syracuseStep 2167519 = 3251279) B3251279
theorem B2890025 : Blo 1925435 2890025 := bstep (se 2 (by rfl) ⟨1083759, by rfl⟩ : syracuseStep 2890025 = 2167519) B2167519
theorem B1926683 : Blo 1925435 1926683 := bstep (se 1 (by rfl) ⟨1445012, by rfl⟩ : syracuseStep 1926683 = 2890025) B2890025
theorem B4114909 : Blo 1925435 4114909 := bbase (se 3 (by rfl) ⟨771545, by rfl⟩ : syracuseStep 4114909 = 1543091) (by norm_num)
theorem B5486545 : Blo 1925435 5486545 := bstep (se 2 (by rfl) ⟨2057454, by rfl⟩ : syracuseStep 5486545 = 4114909) B4114909
theorem B7315393 : Blo 1925435 7315393 := bstep (se 2 (by rfl) ⟨2743272, by rfl⟩ : syracuseStep 7315393 = 5486545) B5486545
theorem B9753857 : Blo 1925435 9753857 := bstep (se 2 (by rfl) ⟨3657696, by rfl⟩ : syracuseStep 9753857 = 7315393) B7315393
theorem B6502571 : Blo 1925435 6502571 := bstep (se 1 (by rfl) ⟨4876928, by rfl⟩ : syracuseStep 6502571 = 9753857) B9753857
theorem B4335047 : Blo 1925435 4335047 := bstep (se 1 (by rfl) ⟨3251285, by rfl⟩ : syracuseStep 4335047 = 6502571) B6502571
theorem B2890031 : Blo 1925435 2890031 := bstep (se 1 (by rfl) ⟨2167523, by rfl⟩ : syracuseStep 2890031 = 4335047) B4335047
theorem B1926687 : Blo 1925435 1926687 := bstep (se 1 (by rfl) ⟨1445015, by rfl⟩ : syracuseStep 1926687 = 2890031) B2890031
theorem B2890037 : Blo 1925435 2890037 := bbase (se 5 (by rfl) ⟨135470, by rfl⟩ : syracuseStep 2890037 = 270941) (by norm_num)
theorem B1926691 : Blo 1925435 1926691 := bstep (se 1 (by rfl) ⟨1445018, by rfl⟩ : syracuseStep 1926691 = 2890037) B2890037
theorem B4876949 : Blo 1925435 4876949 := bbase (se 6 (by rfl) ⟨114303, by rfl⟩ : syracuseStep 4876949 = 228607) (by norm_num)
theorem B3251299 : Blo 1925435 3251299 := bstep (se 1 (by rfl) ⟨2438474, by rfl⟩ : syracuseStep 3251299 = 4876949) B4876949
theorem B4335065 : Blo 1925435 4335065 := bstep (se 2 (by rfl) ⟨1625649, by rfl⟩ : syracuseStep 4335065 = 3251299) B3251299
theorem B2890043 : Blo 1925435 2890043 := bstep (se 1 (by rfl) ⟨2167532, by rfl⟩ : syracuseStep 2890043 = 4335065) B4335065
theorem B1926695 : Blo 1925435 1926695 := bstep (se 1 (by rfl) ⟨1445021, by rfl⟩ : syracuseStep 1926695 = 2890043) B2890043
theorem B2167537 : Blo 1925435 2167537 := bbase (se 2 (by rfl) ⟨812826, by rfl⟩ : syracuseStep 2167537 = 1625653) (by norm_num)
theorem B2890049 : Blo 1925435 2890049 := bstep (se 2 (by rfl) ⟨1083768, by rfl⟩ : syracuseStep 2890049 = 2167537) B2167537
theorem B1926699 : Blo 1925435 1926699 := bstep (se 1 (by rfl) ⟨1445024, by rfl⟩ : syracuseStep 1926699 = 2890049) B2890049
theorem B25367957 : Blo 1925435 25367957 := bbase (se 6 (by rfl) ⟨594561, by rfl⟩ : syracuseStep 25367957 = 1189123) (by norm_num)
theorem B16911971 : Blo 1925435 16911971 := bstep (se 1 (by rfl) ⟨12683978, by rfl⟩ : syracuseStep 16911971 = 25367957) B25367957
theorem B11274647 : Blo 1925435 11274647 := bstep (se 1 (by rfl) ⟨8455985, by rfl⟩ : syracuseStep 11274647 = 16911971) B16911971
theorem B30065725 : Blo 1925435 30065725 := bstep (se 3 (by rfl) ⟨5637323, by rfl⟩ : syracuseStep 30065725 = 11274647) B11274647
theorem B160350533 : Blo 1925435 160350533 := bstep (se 4 (by rfl) ⟨15032862, by rfl⟩ : syracuseStep 160350533 = 30065725) B30065725
theorem B106900355 : Blo 1925435 106900355 := bstep (se 1 (by rfl) ⟨80175266, by rfl⟩ : syracuseStep 106900355 = 160350533) B160350533
theorem B285067613 : Blo 1925435 285067613 := bstep (se 3 (by rfl) ⟨53450177, by rfl⟩ : syracuseStep 285067613 = 106900355) B106900355
theorem B760180301 : Blo 1925435 760180301 := bstep (se 3 (by rfl) ⟨142533806, by rfl⟩ : syracuseStep 760180301 = 285067613) B285067613
theorem B506786867 : Blo 1925435 506786867 := bstep (se 1 (by rfl) ⟨380090150, by rfl⟩ : syracuseStep 506786867 = 760180301) B760180301
theorem B337857911 : Blo 1925435 337857911 := bstep (se 1 (by rfl) ⟨253393433, by rfl⟩ : syracuseStep 337857911 = 506786867) B506786867
theorem B225238607 : Blo 1925435 225238607 := bstep (se 1 (by rfl) ⟨168928955, by rfl⟩ : syracuseStep 225238607 = 337857911) B337857911
theorem B150159071 : Blo 1925435 150159071 := bstep (se 1 (by rfl) ⟨112619303, by rfl⟩ : syracuseStep 150159071 = 225238607) B225238607
theorem B100106047 : Blo 1925435 100106047 := bstep (se 1 (by rfl) ⟨75079535, by rfl⟩ : syracuseStep 100106047 = 150159071) B150159071
theorem B133474729 : Blo 1925435 133474729 := bstep (se 2 (by rfl) ⟨50053023, by rfl⟩ : syracuseStep 133474729 = 100106047) B100106047
theorem B177966305 : Blo 1925435 177966305 := bstep (se 2 (by rfl) ⟨66737364, by rfl⟩ : syracuseStep 177966305 = 133474729) B133474729
theorem B118644203 : Blo 1925435 118644203 := bstep (se 1 (by rfl) ⟨88983152, by rfl⟩ : syracuseStep 118644203 = 177966305) B177966305
theorem B316384541 : Blo 1925435 316384541 := bstep (se 3 (by rfl) ⟨59322101, by rfl⟩ : syracuseStep 316384541 = 118644203) B118644203
theorem B210923027 : Blo 1925435 210923027 := bstep (se 1 (by rfl) ⟨158192270, by rfl⟩ : syracuseStep 210923027 = 316384541) B316384541
theorem B140615351 : Blo 1925435 140615351 := bstep (se 1 (by rfl) ⟨105461513, by rfl⟩ : syracuseStep 140615351 = 210923027) B210923027
theorem B93743567 : Blo 1925435 93743567 := bstep (se 1 (by rfl) ⟨70307675, by rfl⟩ : syracuseStep 93743567 = 140615351) B140615351
theorem B62495711 : Blo 1925435 62495711 := bstep (se 1 (by rfl) ⟨46871783, by rfl⟩ : syracuseStep 62495711 = 93743567) B93743567
theorem B41663807 : Blo 1925435 41663807 := bstep (se 1 (by rfl) ⟨31247855, by rfl⟩ : syracuseStep 41663807 = 62495711) B62495711
theorem B27775871 : Blo 1925435 27775871 := bstep (se 1 (by rfl) ⟨20831903, by rfl⟩ : syracuseStep 27775871 = 41663807) B41663807
theorem B18517247 : Blo 1925435 18517247 := bstep (se 1 (by rfl) ⟨13887935, by rfl⟩ : syracuseStep 18517247 = 27775871) B27775871
theorem B12344831 : Blo 1925435 12344831 := bstep (se 1 (by rfl) ⟨9258623, by rfl⟩ : syracuseStep 12344831 = 18517247) B18517247
theorem B8229887 : Blo 1925435 8229887 := bstep (se 1 (by rfl) ⟨6172415, by rfl⟩ : syracuseStep 8229887 = 12344831) B12344831
theorem B5486591 : Blo 1925435 5486591 := bstep (se 1 (by rfl) ⟨4114943, by rfl⟩ : syracuseStep 5486591 = 8229887) B8229887
theorem B3657727 : Blo 1925435 3657727 := bstep (se 1 (by rfl) ⟨2743295, by rfl⟩ : syracuseStep 3657727 = 5486591) B5486591
theorem B4876969 : Blo 1925435 4876969 := bstep (se 2 (by rfl) ⟨1828863, by rfl⟩ : syracuseStep 4876969 = 3657727) B3657727
theorem B6502625 : Blo 1925435 6502625 := bstep (se 2 (by rfl) ⟨2438484, by rfl⟩ : syracuseStep 6502625 = 4876969) B4876969
theorem B4335083 : Blo 1925435 4335083 := bstep (se 1 (by rfl) ⟨3251312, by rfl⟩ : syracuseStep 4335083 = 6502625) B6502625
theorem B2890055 : Blo 1925435 2890055 := bstep (se 1 (by rfl) ⟨2167541, by rfl⟩ : syracuseStep 2890055 = 4335083) B4335083
theorem B1926703 : Blo 1925435 1926703 := bstep (se 1 (by rfl) ⟨1445027, by rfl⟩ : syracuseStep 1926703 = 2890055) B2890055
theorem B2890061 : Blo 1925435 2890061 := bbase (se 3 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 2890061 = 1083773) (by norm_num)
theorem B1926707 : Blo 1925435 1926707 := bstep (se 1 (by rfl) ⟨1445030, by rfl⟩ : syracuseStep 1926707 = 2890061) B2890061
theorem B4335101 : Blo 1925435 4335101 := bbase (se 3 (by rfl) ⟨812831, by rfl⟩ : syracuseStep 4335101 = 1625663) (by norm_num)
theorem B2890067 : Blo 1925435 2890067 := bstep (se 1 (by rfl) ⟨2167550, by rfl⟩ : syracuseStep 2890067 = 4335101) B4335101
theorem B1926711 : Blo 1925435 1926711 := bstep (se 1 (by rfl) ⟨1445033, by rfl⟩ : syracuseStep 1926711 = 2890067) B2890067
theorem B3251333 : Blo 1925435 3251333 := bbase (se 4 (by rfl) ⟨304812, by rfl⟩ : syracuseStep 3251333 = 609625) (by norm_num)
theorem B2167555 : Blo 1925435 2167555 := bstep (se 1 (by rfl) ⟨1625666, by rfl⟩ : syracuseStep 2167555 = 3251333) B3251333
theorem B2890073 : Blo 1925435 2890073 := bstep (se 2 (by rfl) ⟨1083777, by rfl⟩ : syracuseStep 2890073 = 2167555) B2167555
theorem B1926715 : Blo 1925435 1926715 := bstep (se 1 (by rfl) ⟨1445036, by rfl⟩ : syracuseStep 1926715 = 2890073) B2890073
theorem B14631029 : Blo 1925435 14631029 := bbase (se 5 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 14631029 = 1371659) (by norm_num)
theorem B9754019 : Blo 1925435 9754019 := bstep (se 1 (by rfl) ⟨7315514, by rfl⟩ : syracuseStep 9754019 = 14631029) B14631029
theorem B6502679 : Blo 1925435 6502679 := bstep (se 1 (by rfl) ⟨4877009, by rfl⟩ : syracuseStep 6502679 = 9754019) B9754019
theorem B4335119 : Blo 1925435 4335119 := bstep (se 1 (by rfl) ⟨3251339, by rfl⟩ : syracuseStep 4335119 = 6502679) B6502679
theorem B2890079 : Blo 1925435 2890079 := bstep (se 1 (by rfl) ⟨2167559, by rfl⟩ : syracuseStep 2890079 = 4335119) B4335119
theorem B1926719 : Blo 1925435 1926719 := bstep (se 1 (by rfl) ⟨1445039, by rfl⟩ : syracuseStep 1926719 = 2890079) B2890079
theorem B2890085 : Blo 1925435 2890085 := bbase (se 4 (by rfl) ⟨270945, by rfl⟩ : syracuseStep 2890085 = 541891) (by norm_num)
theorem B1926723 : Blo 1925435 1926723 := bstep (se 1 (by rfl) ⟨1445042, by rfl⟩ : syracuseStep 1926723 = 2890085) B2890085
theorem B3657773 : Blo 1925435 3657773 := bbase (se 3 (by rfl) ⟨685832, by rfl⟩ : syracuseStep 3657773 = 1371665) (by norm_num)
theorem B2438515 : Blo 1925435 2438515 := bstep (se 1 (by rfl) ⟨1828886, by rfl⟩ : syracuseStep 2438515 = 3657773) B3657773
theorem B3251353 : Blo 1925435 3251353 := bstep (se 2 (by rfl) ⟨1219257, by rfl⟩ : syracuseStep 3251353 = 2438515) B2438515
theorem B4335137 : Blo 1925435 4335137 := bstep (se 2 (by rfl) ⟨1625676, by rfl⟩ : syracuseStep 4335137 = 3251353) B3251353
theorem B2890091 : Blo 1925435 2890091 := bstep (se 1 (by rfl) ⟨2167568, by rfl⟩ : syracuseStep 2890091 = 4335137) B4335137
theorem B1926727 : Blo 1925435 1926727 := bstep (se 1 (by rfl) ⟨1445045, by rfl⟩ : syracuseStep 1926727 = 2890091) B2890091
theorem B2167573 : Blo 1925435 2167573 := bbase (se 6 (by rfl) ⟨50802, by rfl⟩ : syracuseStep 2167573 = 101605) (by norm_num)
theorem B2890097 : Blo 1925435 2890097 := bstep (se 2 (by rfl) ⟨1083786, by rfl⟩ : syracuseStep 2890097 = 2167573) B2167573
theorem B1926731 : Blo 1925435 1926731 := bstep (se 1 (by rfl) ⟨1445048, by rfl⟩ : syracuseStep 1926731 = 2890097) B2890097
theorem B2438525 : Blo 1925435 2438525 := bbase (se 3 (by rfl) ⟨457223, by rfl⟩ : syracuseStep 2438525 = 914447) (by norm_num)
theorem B6502733 : Blo 1925435 6502733 := bstep (se 3 (by rfl) ⟨1219262, by rfl⟩ : syracuseStep 6502733 = 2438525) B2438525
theorem B4335155 : Blo 1925435 4335155 := bstep (se 1 (by rfl) ⟨3251366, by rfl⟩ : syracuseStep 4335155 = 6502733) B6502733
theorem B2890103 : Blo 1925435 2890103 := bstep (se 1 (by rfl) ⟨2167577, by rfl⟩ : syracuseStep 2890103 = 4335155) B4335155
theorem B1926735 : Blo 1925435 1926735 := bstep (se 1 (by rfl) ⟨1445051, by rfl⟩ : syracuseStep 1926735 = 2890103) B2890103
theorem B2890109 : Blo 1925435 2890109 := bbase (se 3 (by rfl) ⟨541895, by rfl⟩ : syracuseStep 2890109 = 1083791) (by norm_num)
theorem B1926739 : Blo 1925435 1926739 := bstep (se 1 (by rfl) ⟨1445054, by rfl⟩ : syracuseStep 1926739 = 2890109) B2890109
theorem B4335173 : Blo 1925435 4335173 := bbase (se 4 (by rfl) ⟨406422, by rfl⟩ : syracuseStep 4335173 = 812845) (by norm_num)
theorem B2890115 : Blo 1925435 2890115 := bstep (se 1 (by rfl) ⟨2167586, by rfl⟩ : syracuseStep 2890115 = 4335173) B4335173
theorem B1926743 : Blo 1925435 1926743 := bstep (se 1 (by rfl) ⟨1445057, by rfl⟩ : syracuseStep 1926743 = 2890115) B2890115
theorem B4394333 : Blo 1925435 4394333 := bbase (se 3 (by rfl) ⟨823937, by rfl⟩ : syracuseStep 4394333 = 1647875) (by norm_num)
theorem B2929555 : Blo 1925435 2929555 := bstep (se 1 (by rfl) ⟨2197166, by rfl⟩ : syracuseStep 2929555 = 4394333) B4394333
theorem B3906073 : Blo 1925435 3906073 := bstep (se 2 (by rfl) ⟨1464777, by rfl⟩ : syracuseStep 3906073 = 2929555) B2929555
theorem B5208097 : Blo 1925435 5208097 := bstep (se 2 (by rfl) ⟨1953036, by rfl⟩ : syracuseStep 5208097 = 3906073) B3906073
theorem B6944129 : Blo 1925435 6944129 := bstep (se 2 (by rfl) ⟨2604048, by rfl⟩ : syracuseStep 6944129 = 5208097) B5208097
theorem B4629419 : Blo 1925435 4629419 := bstep (se 1 (by rfl) ⟨3472064, by rfl⟩ : syracuseStep 4629419 = 6944129) B6944129
theorem B3086279 : Blo 1925435 3086279 := bstep (se 1 (by rfl) ⟨2314709, by rfl⟩ : syracuseStep 3086279 = 4629419) B4629419
theorem B2057519 : Blo 1925435 2057519 := bstep (se 1 (by rfl) ⟨1543139, by rfl⟩ : syracuseStep 2057519 = 3086279) B3086279
theorem B5486717 : Blo 1925435 5486717 := bstep (se 3 (by rfl) ⟨1028759, by rfl⟩ : syracuseStep 5486717 = 2057519) B2057519
theorem B3657811 : Blo 1925435 3657811 := bstep (se 1 (by rfl) ⟨2743358, by rfl⟩ : syracuseStep 3657811 = 5486717) B5486717
theorem B4877081 : Blo 1925435 4877081 := bstep (se 2 (by rfl) ⟨1828905, by rfl⟩ : syracuseStep 4877081 = 3657811) B3657811
theorem B3251387 : Blo 1925435 3251387 := bstep (se 1 (by rfl) ⟨2438540, by rfl⟩ : syracuseStep 3251387 = 4877081) B4877081
theorem B2167591 : Blo 1925435 2167591 := bstep (se 1 (by rfl) ⟨1625693, by rfl⟩ : syracuseStep 2167591 = 3251387) B3251387
theorem B2890121 : Blo 1925435 2890121 := bstep (se 2 (by rfl) ⟨1083795, by rfl⟩ : syracuseStep 2890121 = 2167591) B2167591
theorem B1926747 : Blo 1925435 1926747 := bstep (se 1 (by rfl) ⟨1445060, by rfl⟩ : syracuseStep 1926747 = 2890121) B2890121
theorem B9754181 : Blo 1925435 9754181 := bbase (se 4 (by rfl) ⟨914454, by rfl⟩ : syracuseStep 9754181 = 1828909) (by norm_num)
theorem B6502787 : Blo 1925435 6502787 := bstep (se 1 (by rfl) ⟨4877090, by rfl⟩ : syracuseStep 6502787 = 9754181) B9754181
theorem B4335191 : Blo 1925435 4335191 := bstep (se 1 (by rfl) ⟨3251393, by rfl⟩ : syracuseStep 4335191 = 6502787) B6502787
theorem B2890127 : Blo 1925435 2890127 := bstep (se 1 (by rfl) ⟨2167595, by rfl⟩ : syracuseStep 2890127 = 4335191) B4335191
theorem B1926751 : Blo 1925435 1926751 := bstep (se 1 (by rfl) ⟨1445063, by rfl⟩ : syracuseStep 1926751 = 2890127) B2890127
theorem B2890133 : Blo 1925435 2890133 := bbase (se 6 (by rfl) ⟨67737, by rfl⟩ : syracuseStep 2890133 = 135475) (by norm_num)
theorem B1926755 : Blo 1925435 1926755 := bstep (se 1 (by rfl) ⟨1445066, by rfl⟩ : syracuseStep 1926755 = 2890133) B2890133
theorem B3472085 : Blo 1925435 3472085 := bbase (se 7 (by rfl) ⟨40688, by rfl⟩ : syracuseStep 3472085 = 81377) (by norm_num)
theorem B9258893 : Blo 1925435 9258893 := bstep (se 3 (by rfl) ⟨1736042, by rfl⟩ : syracuseStep 9258893 = 3472085) B3472085
theorem B6172595 : Blo 1925435 6172595 := bstep (se 1 (by rfl) ⟨4629446, by rfl⟩ : syracuseStep 6172595 = 9258893) B9258893
theorem B4115063 : Blo 1925435 4115063 := bstep (se 1 (by rfl) ⟨3086297, by rfl⟩ : syracuseStep 4115063 = 6172595) B6172595
theorem B10973501 : Blo 1925435 10973501 := bstep (se 3 (by rfl) ⟨2057531, by rfl⟩ : syracuseStep 10973501 = 4115063) B4115063
theorem B7315667 : Blo 1925435 7315667 := bstep (se 1 (by rfl) ⟨5486750, by rfl⟩ : syracuseStep 7315667 = 10973501) B10973501
theorem B4877111 : Blo 1925435 4877111 := bstep (se 1 (by rfl) ⟨3657833, by rfl⟩ : syracuseStep 4877111 = 7315667) B7315667
theorem B3251407 : Blo 1925435 3251407 := bstep (se 1 (by rfl) ⟨2438555, by rfl⟩ : syracuseStep 3251407 = 4877111) B4877111
theorem B4335209 : Blo 1925435 4335209 := bstep (se 2 (by rfl) ⟨1625703, by rfl⟩ : syracuseStep 4335209 = 3251407) B3251407
theorem B2890139 : Blo 1925435 2890139 := bstep (se 1 (by rfl) ⟨2167604, by rfl⟩ : syracuseStep 2890139 = 4335209) B4335209
theorem B1926759 : Blo 1925435 1926759 := bstep (se 1 (by rfl) ⟨1445069, by rfl⟩ : syracuseStep 1926759 = 2890139) B2890139
theorem B2167609 : Blo 1925435 2167609 := bbase (se 2 (by rfl) ⟨812853, by rfl⟩ : syracuseStep 2167609 = 1625707) (by norm_num)
theorem B2890145 : Blo 1925435 2890145 := bstep (se 2 (by rfl) ⟨1083804, by rfl⟩ : syracuseStep 2890145 = 2167609) B2167609
theorem B1926763 : Blo 1925435 1926763 := bstep (se 1 (by rfl) ⟨1445072, by rfl⟩ : syracuseStep 1926763 = 2890145) B2890145
theorem B5486773 : Blo 1925435 5486773 := bbase (se 5 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 5486773 = 514385) (by norm_num)
theorem B7315697 : Blo 1925435 7315697 := bstep (se 2 (by rfl) ⟨2743386, by rfl⟩ : syracuseStep 7315697 = 5486773) B5486773
theorem B4877131 : Blo 1925435 4877131 := bstep (se 1 (by rfl) ⟨3657848, by rfl⟩ : syracuseStep 4877131 = 7315697) B7315697
theorem B6502841 : Blo 1925435 6502841 := bstep (se 2 (by rfl) ⟨2438565, by rfl⟩ : syracuseStep 6502841 = 4877131) B4877131
theorem B4335227 : Blo 1925435 4335227 := bstep (se 1 (by rfl) ⟨3251420, by rfl⟩ : syracuseStep 4335227 = 6502841) B6502841
theorem B2890151 : Blo 1925435 2890151 := bstep (se 1 (by rfl) ⟨2167613, by rfl⟩ : syracuseStep 2890151 = 4335227) B4335227
theorem B1926767 : Blo 1925435 1926767 := bstep (se 1 (by rfl) ⟨1445075, by rfl⟩ : syracuseStep 1926767 = 2890151) B2890151
theorem B2890157 : Blo 1925435 2890157 := bbase (se 3 (by rfl) ⟨541904, by rfl⟩ : syracuseStep 2890157 = 1083809) (by norm_num)
theorem B1926771 : Blo 1925435 1926771 := bstep (se 1 (by rfl) ⟨1445078, by rfl⟩ : syracuseStep 1926771 = 2890157) B2890157
theorem B4335245 : Blo 1925435 4335245 := bbase (se 3 (by rfl) ⟨812858, by rfl⟩ : syracuseStep 4335245 = 1625717) (by norm_num)
theorem B2890163 : Blo 1925435 2890163 := bstep (se 1 (by rfl) ⟨2167622, by rfl⟩ : syracuseStep 2890163 = 4335245) B4335245
theorem B1926775 : Blo 1925435 1926775 := bstep (se 1 (by rfl) ⟨1445081, by rfl⟩ : syracuseStep 1926775 = 2890163) B2890163
theorem B2438581 : Blo 1925435 2438581 := bbase (se 5 (by rfl) ⟨114308, by rfl⟩ : syracuseStep 2438581 = 228617) (by norm_num)
theorem B3251441 : Blo 1925435 3251441 := bstep (se 2 (by rfl) ⟨1219290, by rfl⟩ : syracuseStep 3251441 = 2438581) B2438581
theorem B2167627 : Blo 1925435 2167627 := bstep (se 1 (by rfl) ⟨1625720, by rfl⟩ : syracuseStep 2167627 = 3251441) B3251441
theorem B2890169 : Blo 1925435 2890169 := bstep (se 2 (by rfl) ⟨1083813, by rfl⟩ : syracuseStep 2890169 = 2167627) B2167627
theorem B1926779 : Blo 1925435 1926779 := bstep (se 1 (by rfl) ⟨1445084, by rfl⟩ : syracuseStep 1926779 = 2890169) B2890169
theorem B3386357 : Blo 1925435 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2257571 : Blo 1925435 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B6020189 : Blo 1925435 6020189 := bstep (se 3 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 6020189 = 2257571) B2257571
theorem B4013459 : Blo 1925435 4013459 := bstep (se 1 (by rfl) ⟨3010094, by rfl⟩ : syracuseStep 4013459 = 6020189) B6020189
theorem B2675639 : Blo 1925435 2675639 := bstep (se 1 (by rfl) ⟨2006729, by rfl⟩ : syracuseStep 2675639 = 4013459) B4013459
theorem B7135037 : Blo 1925435 7135037 := bstep (se 3 (by rfl) ⟨1337819, by rfl⟩ : syracuseStep 7135037 = 2675639) B2675639
theorem B4756691 : Blo 1925435 4756691 := bstep (se 1 (by rfl) ⟨3567518, by rfl⟩ : syracuseStep 4756691 = 7135037) B7135037
theorem B12684509 : Blo 1925435 12684509 := bstep (se 3 (by rfl) ⟨2378345, by rfl⟩ : syracuseStep 12684509 = 4756691) B4756691
theorem B8456339 : Blo 1925435 8456339 := bstep (se 1 (by rfl) ⟨6342254, by rfl⟩ : syracuseStep 8456339 = 12684509) B12684509
theorem B5637559 : Blo 1925435 5637559 := bstep (se 1 (by rfl) ⟨4228169, by rfl⟩ : syracuseStep 5637559 = 8456339) B8456339
theorem B7516745 : Blo 1925435 7516745 := bstep (se 2 (by rfl) ⟨2818779, by rfl⟩ : syracuseStep 7516745 = 5637559) B5637559
theorem B5011163 : Blo 1925435 5011163 := bstep (se 1 (by rfl) ⟨3758372, by rfl⟩ : syracuseStep 5011163 = 7516745) B7516745
theorem B3340775 : Blo 1925435 3340775 := bstep (se 1 (by rfl) ⟨2505581, by rfl⟩ : syracuseStep 3340775 = 5011163) B5011163
theorem B2227183 : Blo 1925435 2227183 := bstep (se 1 (by rfl) ⟨1670387, by rfl⟩ : syracuseStep 2227183 = 3340775) B3340775
theorem B11878309 : Blo 1925435 11878309 := bstep (se 4 (by rfl) ⟨1113591, by rfl⟩ : syracuseStep 11878309 = 2227183) B2227183
theorem B63350981 : Blo 1925435 63350981 := bstep (se 4 (by rfl) ⟨5939154, by rfl⟩ : syracuseStep 63350981 = 11878309) B11878309
theorem B42233987 : Blo 1925435 42233987 := bstep (se 1 (by rfl) ⟨31675490, by rfl⟩ : syracuseStep 42233987 = 63350981) B63350981
theorem B28155991 : Blo 1925435 28155991 := bstep (se 1 (by rfl) ⟨21116993, by rfl⟩ : syracuseStep 28155991 = 42233987) B42233987
theorem B37541321 : Blo 1925435 37541321 := bstep (se 2 (by rfl) ⟨14077995, by rfl⟩ : syracuseStep 37541321 = 28155991) B28155991
theorem B25027547 : Blo 1925435 25027547 := bstep (se 1 (by rfl) ⟨18770660, by rfl⟩ : syracuseStep 25027547 = 37541321) B37541321
theorem B66740125 : Blo 1925435 66740125 := bstep (se 3 (by rfl) ⟨12513773, by rfl⟩ : syracuseStep 66740125 = 25027547) B25027547
theorem B88986833 : Blo 1925435 88986833 := bstep (se 2 (by rfl) ⟨33370062, by rfl⟩ : syracuseStep 88986833 = 66740125) B66740125
theorem B59324555 : Blo 1925435 59324555 := bstep (se 1 (by rfl) ⟨44493416, by rfl⟩ : syracuseStep 59324555 = 88986833) B88986833
theorem B39549703 : Blo 1925435 39549703 := bstep (se 1 (by rfl) ⟨29662277, by rfl⟩ : syracuseStep 39549703 = 59324555) B59324555
theorem B52732937 : Blo 1925435 52732937 := bstep (se 2 (by rfl) ⟨19774851, by rfl⟩ : syracuseStep 52732937 = 39549703) B39549703
theorem B35155291 : Blo 1925435 35155291 := bstep (se 1 (by rfl) ⟨26366468, by rfl⟩ : syracuseStep 35155291 = 52732937) B52732937
theorem B46873721 : Blo 1925435 46873721 := bstep (se 2 (by rfl) ⟨17577645, by rfl⟩ : syracuseStep 46873721 = 35155291) B35155291
theorem B31249147 : Blo 1925435 31249147 := bstep (se 1 (by rfl) ⟨23436860, by rfl⟩ : syracuseStep 31249147 = 46873721) B46873721
theorem B41665529 : Blo 1925435 41665529 := bstep (se 2 (by rfl) ⟨15624573, by rfl⟩ : syracuseStep 41665529 = 31249147) B31249147
theorem B27777019 : Blo 1925435 27777019 := bstep (se 1 (by rfl) ⟨20832764, by rfl⟩ : syracuseStep 27777019 = 41665529) B41665529
theorem B37036025 : Blo 1925435 37036025 := bstep (se 2 (by rfl) ⟨13888509, by rfl⟩ : syracuseStep 37036025 = 27777019) B27777019
theorem B24690683 : Blo 1925435 24690683 := bstep (se 1 (by rfl) ⟨18518012, by rfl⟩ : syracuseStep 24690683 = 37036025) B37036025
theorem B16460455 : Blo 1925435 16460455 := bstep (se 1 (by rfl) ⟨12345341, by rfl⟩ : syracuseStep 16460455 = 24690683) B24690683
theorem B21947273 : Blo 1925435 21947273 := bstep (se 2 (by rfl) ⟨8230227, by rfl⟩ : syracuseStep 21947273 = 16460455) B16460455
theorem B14631515 : Blo 1925435 14631515 := bstep (se 1 (by rfl) ⟨10973636, by rfl⟩ : syracuseStep 14631515 = 21947273) B21947273
theorem B9754343 : Blo 1925435 9754343 := bstep (se 1 (by rfl) ⟨7315757, by rfl⟩ : syracuseStep 9754343 = 14631515) B14631515
theorem B6502895 : Blo 1925435 6502895 := bstep (se 1 (by rfl) ⟨4877171, by rfl⟩ : syracuseStep 6502895 = 9754343) B9754343
theorem B4335263 : Blo 1925435 4335263 := bstep (se 1 (by rfl) ⟨3251447, by rfl⟩ : syracuseStep 4335263 = 6502895) B6502895
theorem B2890175 : Blo 1925435 2890175 := bstep (se 1 (by rfl) ⟨2167631, by rfl⟩ : syracuseStep 2890175 = 4335263) B4335263
theorem B1926783 : Blo 1925435 1926783 := bstep (se 1 (by rfl) ⟨1445087, by rfl⟩ : syracuseStep 1926783 = 2890175) B2890175
theorem B2890181 : Blo 1925435 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B1926787 : Blo 1925435 1926787 := bstep (se 1 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 1926787 = 2890181) B2890181
theorem B3251461 : Blo 1925435 3251461 := bbase (se 4 (by rfl) ⟨304824, by rfl⟩ : syracuseStep 3251461 = 609649) (by norm_num)
theorem B4335281 : Blo 1925435 4335281 := bstep (se 2 (by rfl) ⟨1625730, by rfl⟩ : syracuseStep 4335281 = 3251461) B3251461
theorem B2890187 : Blo 1925435 2890187 := bstep (se 1 (by rfl) ⟨2167640, by rfl⟩ : syracuseStep 2890187 = 4335281) B4335281
theorem B1926791 : Blo 1925435 1926791 := bstep (se 1 (by rfl) ⟨1445093, by rfl⟩ : syracuseStep 1926791 = 2890187) B2890187
theorem B2167645 : Blo 1925435 2167645 := bbase (se 3 (by rfl) ⟨406433, by rfl⟩ : syracuseStep 2167645 = 812867) (by norm_num)
theorem B2890193 : Blo 1925435 2890193 := bstep (se 2 (by rfl) ⟨1083822, by rfl⟩ : syracuseStep 2890193 = 2167645) B2167645
theorem B1926795 : Blo 1925435 1926795 := bstep (se 1 (by rfl) ⟨1445096, by rfl⟩ : syracuseStep 1926795 = 2890193) B2890193
theorem B6502949 : Blo 1925435 6502949 := bbase (se 4 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 6502949 = 1219303) (by norm_num)
theorem B4335299 : Blo 1925435 4335299 := bstep (se 1 (by rfl) ⟨3251474, by rfl⟩ : syracuseStep 4335299 = 6502949) B6502949
theorem B2890199 : Blo 1925435 2890199 := bstep (se 1 (by rfl) ⟨2167649, by rfl⟩ : syracuseStep 2890199 = 4335299) B4335299
theorem B1926799 : Blo 1925435 1926799 := bstep (se 1 (by rfl) ⟨1445099, by rfl⟩ : syracuseStep 1926799 = 2890199) B2890199
theorem B2890205 : Blo 1925435 2890205 := bbase (se 3 (by rfl) ⟨541913, by rfl⟩ : syracuseStep 2890205 = 1083827) (by norm_num)
theorem B1926803 : Blo 1925435 1926803 := bstep (se 1 (by rfl) ⟨1445102, by rfl⟩ : syracuseStep 1926803 = 2890205) B2890205
theorem B4335317 : Blo 1925435 4335317 := bbase (se 7 (by rfl) ⟨50804, by rfl⟩ : syracuseStep 4335317 = 101609) (by norm_num)
theorem B2890211 : Blo 1925435 2890211 := bstep (se 1 (by rfl) ⟨2167658, by rfl⟩ : syracuseStep 2890211 = 4335317) B4335317
theorem B1926807 : Blo 1925435 1926807 := bstep (se 1 (by rfl) ⟨1445105, by rfl⟩ : syracuseStep 1926807 = 2890211) B2890211
theorem B3086381 : Blo 1925435 3086381 := bbase (se 3 (by rfl) ⟨578696, by rfl⟩ : syracuseStep 3086381 = 1157393) (by norm_num)
theorem B8230349 : Blo 1925435 8230349 := bstep (se 3 (by rfl) ⟨1543190, by rfl⟩ : syracuseStep 8230349 = 3086381) B3086381
theorem B5486899 : Blo 1925435 5486899 := bstep (se 1 (by rfl) ⟨4115174, by rfl⟩ : syracuseStep 5486899 = 8230349) B8230349
theorem B7315865 : Blo 1925435 7315865 := bstep (se 2 (by rfl) ⟨2743449, by rfl⟩ : syracuseStep 7315865 = 5486899) B5486899
theorem B4877243 : Blo 1925435 4877243 := bstep (se 1 (by rfl) ⟨3657932, by rfl⟩ : syracuseStep 4877243 = 7315865) B7315865
theorem B3251495 : Blo 1925435 3251495 := bstep (se 1 (by rfl) ⟨2438621, by rfl⟩ : syracuseStep 3251495 = 4877243) B4877243
theorem B2167663 : Blo 1925435 2167663 := bstep (se 1 (by rfl) ⟨1625747, by rfl⟩ : syracuseStep 2167663 = 3251495) B3251495
theorem B2890217 : Blo 1925435 2890217 := bstep (se 2 (by rfl) ⟨1083831, by rfl⟩ : syracuseStep 2890217 = 2167663) B2167663
theorem B1926811 : Blo 1925435 1926811 := bstep (se 1 (by rfl) ⟨1445108, by rfl⟩ : syracuseStep 1926811 = 2890217) B2890217
theorem B6256997 : Blo 1925435 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B4171331 : Blo 1925435 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B2780887 : Blo 1925435 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B3707849 : Blo 1925435 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B2471899 : Blo 1925435 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B3295865 : Blo 1925435 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B2197243 : Blo 1925435 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B2929657 : Blo 1925435 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B3906209 : Blo 1925435 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B2604139 : Blo 1925435 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B13888741 : Blo 1925435 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B18518321 : Blo 1925435 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B12345547 : Blo 1925435 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B16460729 : Blo 1925435 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B10973819 : Blo 1925435 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B7315879 : Blo 1925435 7315879 := bstep (se 1 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 7315879 = 10973819) B10973819
theorem B9754505 : Blo 1925435 9754505 := bstep (se 2 (by rfl) ⟨3657939, by rfl⟩ : syracuseStep 9754505 = 7315879) B7315879
theorem B6503003 : Blo 1925435 6503003 := bstep (se 1 (by rfl) ⟨4877252, by rfl⟩ : syracuseStep 6503003 = 9754505) B9754505
theorem B4335335 : Blo 1925435 4335335 := bstep (se 1 (by rfl) ⟨3251501, by rfl⟩ : syracuseStep 4335335 = 6503003) B6503003
theorem B2890223 : Blo 1925435 2890223 := bstep (se 1 (by rfl) ⟨2167667, by rfl⟩ : syracuseStep 2890223 = 4335335) B4335335
theorem B1926815 : Blo 1925435 1926815 := bstep (se 1 (by rfl) ⟨1445111, by rfl⟩ : syracuseStep 1926815 = 2890223) B2890223
theorem B2890229 : Blo 1925435 2890229 := bbase (se 5 (by rfl) ⟨135479, by rfl⟩ : syracuseStep 2890229 = 270959) (by norm_num)
theorem B1926819 : Blo 1925435 1926819 := bstep (se 1 (by rfl) ⟨1445114, by rfl⟩ : syracuseStep 1926819 = 2890229) B2890229
theorem B5486933 : Blo 1925435 5486933 := bbase (se 10 (by rfl) ⟨8037, by rfl⟩ : syracuseStep 5486933 = 16075) (by norm_num)
theorem B3657955 : Blo 1925435 3657955 := bstep (se 1 (by rfl) ⟨2743466, by rfl⟩ : syracuseStep 3657955 = 5486933) B5486933
theorem B4877273 : Blo 1925435 4877273 := bstep (se 2 (by rfl) ⟨1828977, by rfl⟩ : syracuseStep 4877273 = 3657955) B3657955
theorem B3251515 : Blo 1925435 3251515 := bstep (se 1 (by rfl) ⟨2438636, by rfl⟩ : syracuseStep 3251515 = 4877273) B4877273
theorem B4335353 : Blo 1925435 4335353 := bstep (se 2 (by rfl) ⟨1625757, by rfl⟩ : syracuseStep 4335353 = 3251515) B3251515
theorem B2890235 : Blo 1925435 2890235 := bstep (se 1 (by rfl) ⟨2167676, by rfl⟩ : syracuseStep 2890235 = 4335353) B4335353
theorem B1926823 : Blo 1925435 1926823 := bstep (se 1 (by rfl) ⟨1445117, by rfl⟩ : syracuseStep 1926823 = 2890235) B2890235
theorem B2167681 : Blo 1925435 2167681 := bbase (se 2 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 2167681 = 1625761) (by norm_num)
theorem B2890241 : Blo 1925435 2890241 := bstep (se 2 (by rfl) ⟨1083840, by rfl⟩ : syracuseStep 2890241 = 2167681) B2167681
theorem B1926827 : Blo 1925435 1926827 := bstep (se 1 (by rfl) ⟨1445120, by rfl⟩ : syracuseStep 1926827 = 2890241) B2890241
theorem B4877293 : Blo 1925435 4877293 := bbase (se 3 (by rfl) ⟨914492, by rfl⟩ : syracuseStep 4877293 = 1828985) (by norm_num)
theorem B6503057 : Blo 1925435 6503057 := bstep (se 2 (by rfl) ⟨2438646, by rfl⟩ : syracuseStep 6503057 = 4877293) B4877293
theorem B4335371 : Blo 1925435 4335371 := bstep (se 1 (by rfl) ⟨3251528, by rfl⟩ : syracuseStep 4335371 = 6503057) B6503057
theorem B2890247 : Blo 1925435 2890247 := bstep (se 1 (by rfl) ⟨2167685, by rfl⟩ : syracuseStep 2890247 = 4335371) B4335371
theorem B1926831 : Blo 1925435 1926831 := bstep (se 1 (by rfl) ⟨1445123, by rfl⟩ : syracuseStep 1926831 = 2890247) B2890247
theorem B2890253 : Blo 1925435 2890253 := bbase (se 3 (by rfl) ⟨541922, by rfl⟩ : syracuseStep 2890253 = 1083845) (by norm_num)
theorem B1926835 : Blo 1925435 1926835 := bstep (se 1 (by rfl) ⟨1445126, by rfl⟩ : syracuseStep 1926835 = 2890253) B2890253
theorem B4335389 : Blo 1925435 4335389 := bbase (se 3 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 4335389 = 1625771) (by norm_num)
theorem B2890259 : Blo 1925435 2890259 := bstep (se 1 (by rfl) ⟨2167694, by rfl⟩ : syracuseStep 2890259 = 4335389) B4335389
theorem B1926839 : Blo 1925435 1926839 := bstep (se 1 (by rfl) ⟨1445129, by rfl⟩ : syracuseStep 1926839 = 2890259) B2890259
theorem B3251549 : Blo 1925435 3251549 := bbase (se 3 (by rfl) ⟨609665, by rfl⟩ : syracuseStep 3251549 = 1219331) (by norm_num)
theorem B2167699 : Blo 1925435 2167699 := bstep (se 1 (by rfl) ⟨1625774, by rfl⟩ : syracuseStep 2167699 = 3251549) B3251549
theorem B2890265 : Blo 1925435 2890265 := bstep (se 2 (by rfl) ⟨1083849, by rfl⟩ : syracuseStep 2890265 = 2167699) B2167699
theorem B1926843 : Blo 1925435 1926843 := bstep (se 1 (by rfl) ⟨1445132, by rfl⟩ : syracuseStep 1926843 = 2890265) B2890265
theorem B8230501 : Blo 1925435 8230501 := bbase (se 4 (by rfl) ⟨771609, by rfl⟩ : syracuseStep 8230501 = 1543219) (by norm_num)
theorem B10974001 : Blo 1925435 10974001 := bstep (se 2 (by rfl) ⟨4115250, by rfl⟩ : syracuseStep 10974001 = 8230501) B8230501
theorem B14632001 : Blo 1925435 14632001 := bstep (se 2 (by rfl) ⟨5487000, by rfl⟩ : syracuseStep 14632001 = 10974001) B10974001
theorem B9754667 : Blo 1925435 9754667 := bstep (se 1 (by rfl) ⟨7316000, by rfl⟩ : syracuseStep 9754667 = 14632001) B14632001
theorem B6503111 : Blo 1925435 6503111 := bstep (se 1 (by rfl) ⟨4877333, by rfl⟩ : syracuseStep 6503111 = 9754667) B9754667
theorem B4335407 : Blo 1925435 4335407 := bstep (se 1 (by rfl) ⟨3251555, by rfl⟩ : syracuseStep 4335407 = 6503111) B6503111
theorem B2890271 : Blo 1925435 2890271 := bstep (se 1 (by rfl) ⟨2167703, by rfl⟩ : syracuseStep 2890271 = 4335407) B4335407
theorem B1926847 : Blo 1925435 1926847 := bstep (se 1 (by rfl) ⟨1445135, by rfl⟩ : syracuseStep 1926847 = 2890271) B2890271
theorem B2890277 : Blo 1925435 2890277 := bbase (se 4 (by rfl) ⟨270963, by rfl⟩ : syracuseStep 2890277 = 541927) (by norm_num)
theorem B1926851 : Blo 1925435 1926851 := bstep (se 1 (by rfl) ⟨1445138, by rfl⟩ : syracuseStep 1926851 = 2890277) B2890277
theorem B2438677 : Blo 1925435 2438677 := bbase (se 6 (by rfl) ⟨57156, by rfl⟩ : syracuseStep 2438677 = 114313) (by norm_num)
theorem B3251569 : Blo 1925435 3251569 := bstep (se 2 (by rfl) ⟨1219338, by rfl⟩ : syracuseStep 3251569 = 2438677) B2438677
theorem B4335425 : Blo 1925435 4335425 := bstep (se 2 (by rfl) ⟨1625784, by rfl⟩ : syracuseStep 4335425 = 3251569) B3251569
theorem B2890283 : Blo 1925435 2890283 := bstep (se 1 (by rfl) ⟨2167712, by rfl⟩ : syracuseStep 2890283 = 4335425) B4335425
theorem B1926855 : Blo 1925435 1926855 := bstep (se 1 (by rfl) ⟨1445141, by rfl⟩ : syracuseStep 1926855 = 2890283) B2890283
theorem B2167717 : Blo 1925435 2167717 := bbase (se 4 (by rfl) ⟨203223, by rfl⟩ : syracuseStep 2167717 = 406447) (by norm_num)
theorem B2890289 : Blo 1925435 2890289 := bstep (se 2 (by rfl) ⟨1083858, by rfl⟩ : syracuseStep 2890289 = 2167717) B2167717
theorem B1926859 : Blo 1925435 1926859 := bstep (se 1 (by rfl) ⟨1445144, by rfl⟩ : syracuseStep 1926859 = 2890289) B2890289
theorem B5859461 : Blo 1925435 5859461 := bbase (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) (by norm_num)
theorem B3906307 : Blo 1925435 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B5208409 : Blo 1925435 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B6944545 : Blo 1925435 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B9259393 : Blo 1925435 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B12345857 : Blo 1925435 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B8230571 : Blo 1925435 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B5487047 : Blo 1925435 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B3658031 : Blo 1925435 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B2438687 : Blo 1925435 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B6503165 : Blo 1925435 6503165 := bstep (se 3 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 6503165 = 2438687) B2438687
theorem B4335443 : Blo 1925435 4335443 := bstep (se 1 (by rfl) ⟨3251582, by rfl⟩ : syracuseStep 4335443 = 6503165) B6503165
theorem B2890295 : Blo 1925435 2890295 := bstep (se 1 (by rfl) ⟨2167721, by rfl⟩ : syracuseStep 2890295 = 4335443) B4335443
theorem B1926863 : Blo 1925435 1926863 := bstep (se 1 (by rfl) ⟨1445147, by rfl⟩ : syracuseStep 1926863 = 2890295) B2890295
theorem B2890301 : Blo 1925435 2890301 := bbase (se 3 (by rfl) ⟨541931, by rfl⟩ : syracuseStep 2890301 = 1083863) (by norm_num)
theorem B1926867 : Blo 1925435 1926867 := bstep (se 1 (by rfl) ⟨1445150, by rfl⟩ : syracuseStep 1926867 = 2890301) B2890301
theorem B4335461 : Blo 1925435 4335461 := bbase (se 4 (by rfl) ⟨406449, by rfl⟩ : syracuseStep 4335461 = 812899) (by norm_num)
theorem B2890307 : Blo 1925435 2890307 := bstep (se 1 (by rfl) ⟨2167730, by rfl⟩ : syracuseStep 2890307 = 4335461) B4335461
theorem B1926871 : Blo 1925435 1926871 := bstep (se 1 (by rfl) ⟨1445153, by rfl⟩ : syracuseStep 1926871 = 2890307) B2890307
theorem B4877405 : Blo 1925435 4877405 := bbase (se 3 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 4877405 = 1829027) (by norm_num)
theorem B3251603 : Blo 1925435 3251603 := bstep (se 1 (by rfl) ⟨2438702, by rfl⟩ : syracuseStep 3251603 = 4877405) B4877405
theorem B2167735 : Blo 1925435 2167735 := bstep (se 1 (by rfl) ⟨1625801, by rfl⟩ : syracuseStep 2167735 = 3251603) B3251603
theorem B2890313 : Blo 1925435 2890313 := bstep (se 2 (by rfl) ⟨1083867, by rfl⟩ : syracuseStep 2890313 = 2167735) B2167735
theorem B1926875 : Blo 1925435 1926875 := bstep (se 1 (by rfl) ⟨1445156, by rfl⟩ : syracuseStep 1926875 = 2890313) B2890313
theorem B3658061 : Blo 1925435 3658061 := bbase (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) (by norm_num)
theorem B9754829 : Blo 1925435 9754829 := bstep (se 3 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 9754829 = 3658061) B3658061
theorem B6503219 : Blo 1925435 6503219 := bstep (se 1 (by rfl) ⟨4877414, by rfl⟩ : syracuseStep 6503219 = 9754829) B9754829
theorem B4335479 : Blo 1925435 4335479 := bstep (se 1 (by rfl) ⟨3251609, by rfl⟩ : syracuseStep 4335479 = 6503219) B6503219
theorem B2890319 : Blo 1925435 2890319 := bstep (se 1 (by rfl) ⟨2167739, by rfl⟩ : syracuseStep 2890319 = 4335479) B4335479
theorem B1926879 : Blo 1925435 1926879 := bstep (se 1 (by rfl) ⟨1445159, by rfl⟩ : syracuseStep 1926879 = 2890319) B2890319
theorem B2890325 : Blo 1925435 2890325 := bbase (se 8 (by rfl) ⟨16935, by rfl⟩ : syracuseStep 2890325 = 33871) (by norm_num)
theorem B1926883 : Blo 1925435 1926883 := bstep (se 1 (by rfl) ⟨1445162, by rfl⟩ : syracuseStep 1926883 = 2890325) B2890325
theorem B2314877 : Blo 1925435 2314877 := bbase (se 3 (by rfl) ⟨434039, by rfl⟩ : syracuseStep 2314877 = 868079) (by norm_num)
theorem B6173005 : Blo 1925435 6173005 := bstep (se 3 (by rfl) ⟨1157438, by rfl⟩ : syracuseStep 6173005 = 2314877) B2314877
theorem B8230673 : Blo 1925435 8230673 := bstep (se 2 (by rfl) ⟨3086502, by rfl⟩ : syracuseStep 8230673 = 6173005) B6173005
theorem B5487115 : Blo 1925435 5487115 := bstep (se 1 (by rfl) ⟨4115336, by rfl⟩ : syracuseStep 5487115 = 8230673) B8230673
theorem B7316153 : Blo 1925435 7316153 := bstep (se 2 (by rfl) ⟨2743557, by rfl⟩ : syracuseStep 7316153 = 5487115) B5487115
theorem B4877435 : Blo 1925435 4877435 := bstep (se 1 (by rfl) ⟨3658076, by rfl⟩ : syracuseStep 4877435 = 7316153) B7316153
theorem B3251623 : Blo 1925435 3251623 := bstep (se 1 (by rfl) ⟨2438717, by rfl⟩ : syracuseStep 3251623 = 4877435) B4877435
theorem B4335497 : Blo 1925435 4335497 := bstep (se 2 (by rfl) ⟨1625811, by rfl⟩ : syracuseStep 4335497 = 3251623) B3251623
theorem B2890331 : Blo 1925435 2890331 := bstep (se 1 (by rfl) ⟨2167748, by rfl⟩ : syracuseStep 2890331 = 4335497) B4335497
theorem B1926887 : Blo 1925435 1926887 := bstep (se 1 (by rfl) ⟨1445165, by rfl⟩ : syracuseStep 1926887 = 2890331) B2890331
theorem B2167753 : Blo 1925435 2167753 := bbase (se 2 (by rfl) ⟨812907, by rfl⟩ : syracuseStep 2167753 = 1625815) (by norm_num)
theorem B2890337 : Blo 1925435 2890337 := bstep (se 2 (by rfl) ⟨1083876, by rfl⟩ : syracuseStep 2890337 = 2167753) B2167753
theorem B1926891 : Blo 1925435 1926891 := bstep (se 1 (by rfl) ⟨1445168, by rfl⟩ : syracuseStep 1926891 = 2890337) B2890337
theorem B4629773 : Blo 1925435 4629773 := bbase (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) (by norm_num)
theorem B3086515 : Blo 1925435 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B16461413 : Blo 1925435 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B10974275 : Blo 1925435 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B7316183 : Blo 1925435 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B4877455 : Blo 1925435 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B6503273 : Blo 1925435 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B4335515 : Blo 1925435 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B2890343 : Blo 1925435 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B1926895 : Blo 1925435 1926895 := bstep (se 1 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 1926895 = 2890343) B2890343
theorem B2890349 : Blo 1925435 2890349 := bbase (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) (by norm_num)
theorem B1926899 : Blo 1925435 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B4335533 : Blo 1925435 4335533 := bbase (se 3 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 4335533 = 1625825) (by norm_num)
theorem B2890355 : Blo 1925435 2890355 := bstep (se 1 (by rfl) ⟨2167766, by rfl⟩ : syracuseStep 2890355 = 4335533) B4335533
theorem B1926903 : Blo 1925435 1926903 := bstep (se 1 (by rfl) ⟨1445177, by rfl⟩ : syracuseStep 1926903 = 2890355) B2890355
theorem B5487173 : Blo 1925435 5487173 := bbase (se 4 (by rfl) ⟨514422, by rfl⟩ : syracuseStep 5487173 = 1028845) (by norm_num)
theorem B3658115 : Blo 1925435 3658115 := bstep (se 1 (by rfl) ⟨2743586, by rfl⟩ : syracuseStep 3658115 = 5487173) B5487173
theorem B2438743 : Blo 1925435 2438743 := bstep (se 1 (by rfl) ⟨1829057, by rfl⟩ : syracuseStep 2438743 = 3658115) B3658115
theorem B3251657 : Blo 1925435 3251657 := bstep (se 2 (by rfl) ⟨1219371, by rfl⟩ : syracuseStep 3251657 = 2438743) B2438743
theorem B2167771 : Blo 1925435 2167771 := bstep (se 1 (by rfl) ⟨1625828, by rfl⟩ : syracuseStep 2167771 = 3251657) B3251657
theorem B2890361 : Blo 1925435 2890361 := bstep (se 2 (by rfl) ⟨1083885, by rfl⟩ : syracuseStep 2890361 = 2167771) B2167771
theorem B1926907 : Blo 1925435 1926907 := bstep (se 1 (by rfl) ⟨1445180, by rfl⟩ : syracuseStep 1926907 = 2890361) B2890361
theorem B37038485 : Blo 1925435 37038485 := bbase (se 6 (by rfl) ⟨868089, by rfl⟩ : syracuseStep 37038485 = 1736179) (by norm_num)
theorem B24692323 : Blo 1925435 24692323 := bstep (se 1 (by rfl) ⟨18519242, by rfl⟩ : syracuseStep 24692323 = 37038485) B37038485
theorem B32923097 : Blo 1925435 32923097 := bstep (se 2 (by rfl) ⟨12346161, by rfl⟩ : syracuseStep 32923097 = 24692323) B24692323
theorem B21948731 : Blo 1925435 21948731 := bstep (se 1 (by rfl) ⟨16461548, by rfl⟩ : syracuseStep 21948731 = 32923097) B32923097
theorem B14632487 : Blo 1925435 14632487 := bstep (se 1 (by rfl) ⟨10974365, by rfl⟩ : syracuseStep 14632487 = 21948731) B21948731
theorem B9754991 : Blo 1925435 9754991 := bstep (se 1 (by rfl) ⟨7316243, by rfl⟩ : syracuseStep 9754991 = 14632487) B14632487
theorem B6503327 : Blo 1925435 6503327 := bstep (se 1 (by rfl) ⟨4877495, by rfl⟩ : syracuseStep 6503327 = 9754991) B9754991
theorem B4335551 : Blo 1925435 4335551 := bstep (se 1 (by rfl) ⟨3251663, by rfl⟩ : syracuseStep 4335551 = 6503327) B6503327
theorem B2890367 : Blo 1925435 2890367 := bstep (se 1 (by rfl) ⟨2167775, by rfl⟩ : syracuseStep 2890367 = 4335551) B4335551
theorem B1926911 : Blo 1925435 1926911 := bstep (se 1 (by rfl) ⟨1445183, by rfl⟩ : syracuseStep 1926911 = 2890367) B2890367
theorem B2890373 : Blo 1925435 2890373 := bbase (se 4 (by rfl) ⟨270972, by rfl⟩ : syracuseStep 2890373 = 541945) (by norm_num)
theorem B1926915 : Blo 1925435 1926915 := bstep (se 1 (by rfl) ⟨1445186, by rfl⟩ : syracuseStep 1926915 = 2890373) B2890373
theorem B3251677 : Blo 1925435 3251677 := bbase (se 3 (by rfl) ⟨609689, by rfl⟩ : syracuseStep 3251677 = 1219379) (by norm_num)
theorem B4335569 : Blo 1925435 4335569 := bstep (se 2 (by rfl) ⟨1625838, by rfl⟩ : syracuseStep 4335569 = 3251677) B3251677
theorem B2890379 : Blo 1925435 2890379 := bstep (se 1 (by rfl) ⟨2167784, by rfl⟩ : syracuseStep 2890379 = 4335569) B4335569
theorem B1926919 : Blo 1925435 1926919 := bstep (se 1 (by rfl) ⟨1445189, by rfl⟩ : syracuseStep 1926919 = 2890379) B2890379
theorem B2167789 : Blo 1925435 2167789 := bbase (se 3 (by rfl) ⟨406460, by rfl⟩ : syracuseStep 2167789 = 812921) (by norm_num)
theorem B2890385 : Blo 1925435 2890385 := bstep (se 2 (by rfl) ⟨1083894, by rfl⟩ : syracuseStep 2890385 = 2167789) B2167789
theorem B1926923 : Blo 1925435 1926923 := bstep (se 1 (by rfl) ⟨1445192, by rfl⟩ : syracuseStep 1926923 = 2890385) B2890385
theorem B6503381 : Blo 1925435 6503381 := bbase (se 7 (by rfl) ⟨76211, by rfl⟩ : syracuseStep 6503381 = 152423) (by norm_num)
theorem B4335587 : Blo 1925435 4335587 := bstep (se 1 (by rfl) ⟨3251690, by rfl⟩ : syracuseStep 4335587 = 6503381) B6503381
theorem B2890391 : Blo 1925435 2890391 := bstep (se 1 (by rfl) ⟨2167793, by rfl⟩ : syracuseStep 2890391 = 4335587) B4335587
theorem B1926927 : Blo 1925435 1926927 := bstep (se 1 (by rfl) ⟨1445195, by rfl⟩ : syracuseStep 1926927 = 2890391) B2890391
theorem B2890397 : Blo 1925435 2890397 := bbase (se 3 (by rfl) ⟨541949, by rfl⟩ : syracuseStep 2890397 = 1083899) (by norm_num)
theorem B1926931 : Blo 1925435 1926931 := bstep (se 1 (by rfl) ⟨1445198, by rfl⟩ : syracuseStep 1926931 = 2890397) B2890397
theorem B4335605 : Blo 1925435 4335605 := bbase (se 5 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 4335605 = 406463) (by norm_num)
theorem B2890403 : Blo 1925435 2890403 := bstep (se 1 (by rfl) ⟨2167802, by rfl⟩ : syracuseStep 2890403 = 4335605) B4335605
theorem B1926935 : Blo 1925435 1926935 := bstep (se 1 (by rfl) ⟨1445201, by rfl⟩ : syracuseStep 1926935 = 2890403) B2890403
theorem B46877525 : Blo 1925435 46877525 := bbase (se 9 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 46877525 = 274673) (by norm_num)
theorem B31251683 : Blo 1925435 31251683 := bstep (se 1 (by rfl) ⟨23438762, by rfl⟩ : syracuseStep 31251683 = 46877525) B46877525
theorem B83337821 : Blo 1925435 83337821 := bstep (se 3 (by rfl) ⟨15625841, by rfl⟩ : syracuseStep 83337821 = 31251683) B31251683
theorem B55558547 : Blo 1925435 55558547 := bstep (se 1 (by rfl) ⟨41668910, by rfl⟩ : syracuseStep 55558547 = 83337821) B83337821
theorem B37039031 : Blo 1925435 37039031 := bstep (se 1 (by rfl) ⟨27779273, by rfl⟩ : syracuseStep 37039031 = 55558547) B55558547
theorem B24692687 : Blo 1925435 24692687 := bstep (se 1 (by rfl) ⟨18519515, by rfl⟩ : syracuseStep 24692687 = 37039031) B37039031
theorem B16461791 : Blo 1925435 16461791 := bstep (se 1 (by rfl) ⟨12346343, by rfl⟩ : syracuseStep 16461791 = 24692687) B24692687
theorem B10974527 : Blo 1925435 10974527 := bstep (se 1 (by rfl) ⟨8230895, by rfl⟩ : syracuseStep 10974527 = 16461791) B16461791
theorem B7316351 : Blo 1925435 7316351 := bstep (se 1 (by rfl) ⟨5487263, by rfl⟩ : syracuseStep 7316351 = 10974527) B10974527
theorem B4877567 : Blo 1925435 4877567 := bstep (se 1 (by rfl) ⟨3658175, by rfl⟩ : syracuseStep 4877567 = 7316351) B7316351
theorem B3251711 : Blo 1925435 3251711 := bstep (se 1 (by rfl) ⟨2438783, by rfl⟩ : syracuseStep 3251711 = 4877567) B4877567
theorem B2167807 : Blo 1925435 2167807 := bstep (se 1 (by rfl) ⟨1625855, by rfl⟩ : syracuseStep 2167807 = 3251711) B3251711
theorem B2890409 : Blo 1925435 2890409 := bstep (se 2 (by rfl) ⟨1083903, by rfl⟩ : syracuseStep 2890409 = 2167807) B2167807
theorem B1926939 : Blo 1925435 1926939 := bstep (se 1 (by rfl) ⟨1445204, by rfl⟩ : syracuseStep 1926939 = 2890409) B2890409
theorem B2743637 : Blo 1925435 2743637 := bbase (se 11 (by rfl) ⟨2009, by rfl⟩ : syracuseStep 2743637 = 4019) (by norm_num)
theorem B7316365 : Blo 1925435 7316365 := bstep (se 3 (by rfl) ⟨1371818, by rfl⟩ : syracuseStep 7316365 = 2743637) B2743637
theorem B9755153 : Blo 1925435 9755153 := bstep (se 2 (by rfl) ⟨3658182, by rfl⟩ : syracuseStep 9755153 = 7316365) B7316365
theorem B6503435 : Blo 1925435 6503435 := bstep (se 1 (by rfl) ⟨4877576, by rfl⟩ : syracuseStep 6503435 = 9755153) B9755153
theorem B4335623 : Blo 1925435 4335623 := bstep (se 1 (by rfl) ⟨3251717, by rfl⟩ : syracuseStep 4335623 = 6503435) B6503435
theorem B2890415 : Blo 1925435 2890415 := bstep (se 1 (by rfl) ⟨2167811, by rfl⟩ : syracuseStep 2890415 = 4335623) B4335623
theorem B1926943 : Blo 1925435 1926943 := bstep (se 1 (by rfl) ⟨1445207, by rfl⟩ : syracuseStep 1926943 = 2890415) B2890415
theorem B2890421 : Blo 1925435 2890421 := bbase (se 5 (by rfl) ⟨135488, by rfl⟩ : syracuseStep 2890421 = 270977) (by norm_num)
theorem B1926947 : Blo 1925435 1926947 := bstep (se 1 (by rfl) ⟨1445210, by rfl⟩ : syracuseStep 1926947 = 2890421) B2890421
theorem B4877597 : Blo 1925435 4877597 := bbase (se 3 (by rfl) ⟨914549, by rfl⟩ : syracuseStep 4877597 = 1829099) (by norm_num)
theorem B3251731 : Blo 1925435 3251731 := bstep (se 1 (by rfl) ⟨2438798, by rfl⟩ : syracuseStep 3251731 = 4877597) B4877597
theorem B4335641 : Blo 1925435 4335641 := bstep (se 2 (by rfl) ⟨1625865, by rfl⟩ : syracuseStep 4335641 = 3251731) B3251731
theorem B2890427 : Blo 1925435 2890427 := bstep (se 1 (by rfl) ⟨2167820, by rfl⟩ : syracuseStep 2890427 = 4335641) B4335641
theorem B1926951 : Blo 1925435 1926951 := bstep (se 1 (by rfl) ⟨1445213, by rfl⟩ : syracuseStep 1926951 = 2890427) B2890427
theorem B2167825 : Blo 1925435 2167825 := bbase (se 2 (by rfl) ⟨812934, by rfl⟩ : syracuseStep 2167825 = 1625869) (by norm_num)
theorem B2890433 : Blo 1925435 2890433 := bstep (se 2 (by rfl) ⟨1083912, by rfl⟩ : syracuseStep 2890433 = 2167825) B2167825
theorem B1926955 : Blo 1925435 1926955 := bstep (se 1 (by rfl) ⟨1445216, by rfl⟩ : syracuseStep 1926955 = 2890433) B2890433
theorem B3658213 : Blo 1925435 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B4877617 : Blo 1925435 4877617 := bstep (se 2 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 4877617 = 3658213) B3658213
theorem B6503489 : Blo 1925435 6503489 := bstep (se 2 (by rfl) ⟨2438808, by rfl⟩ : syracuseStep 6503489 = 4877617) B4877617
theorem B4335659 : Blo 1925435 4335659 := bstep (se 1 (by rfl) ⟨3251744, by rfl⟩ : syracuseStep 4335659 = 6503489) B6503489
theorem B2890439 : Blo 1925435 2890439 := bstep (se 1 (by rfl) ⟨2167829, by rfl⟩ : syracuseStep 2890439 = 4335659) B4335659
theorem B1926959 : Blo 1925435 1926959 := bstep (se 1 (by rfl) ⟨1445219, by rfl⟩ : syracuseStep 1926959 = 2890439) B2890439
theorem B2890445 : Blo 1925435 2890445 := bbase (se 3 (by rfl) ⟨541958, by rfl⟩ : syracuseStep 2890445 = 1083917) (by norm_num)
theorem B1926963 : Blo 1925435 1926963 := bstep (se 1 (by rfl) ⟨1445222, by rfl⟩ : syracuseStep 1926963 = 2890445) B2890445
theorem B4335677 : Blo 1925435 4335677 := bbase (se 3 (by rfl) ⟨812939, by rfl⟩ : syracuseStep 4335677 = 1625879) (by norm_num)
theorem B2890451 : Blo 1925435 2890451 := bstep (se 1 (by rfl) ⟨2167838, by rfl⟩ : syracuseStep 2890451 = 4335677) B4335677
theorem B1926967 : Blo 1925435 1926967 := bstep (se 1 (by rfl) ⟨1445225, by rfl⟩ : syracuseStep 1926967 = 2890451) B2890451
theorem B3251765 : Blo 1925435 3251765 := bbase (se 5 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 3251765 = 304853) (by norm_num)
theorem B2167843 : Blo 1925435 2167843 := bstep (se 1 (by rfl) ⟨1625882, by rfl⟩ : syracuseStep 2167843 = 3251765) B3251765
theorem B2890457 : Blo 1925435 2890457 := bstep (se 2 (by rfl) ⟨1083921, by rfl⟩ : syracuseStep 2890457 = 2167843) B2167843
theorem B1926971 : Blo 1925435 1926971 := bstep (se 1 (by rfl) ⟨1445228, by rfl⟩ : syracuseStep 1926971 = 2890457) B2890457
theorem B5487365 : Blo 1925435 5487365 := bbase (se 4 (by rfl) ⟨514440, by rfl⟩ : syracuseStep 5487365 = 1028881) (by norm_num)
theorem B14632973 : Blo 1925435 14632973 := bstep (se 3 (by rfl) ⟨2743682, by rfl⟩ : syracuseStep 14632973 = 5487365) B5487365
theorem B9755315 : Blo 1925435 9755315 := bstep (se 1 (by rfl) ⟨7316486, by rfl⟩ : syracuseStep 9755315 = 14632973) B14632973
theorem B6503543 : Blo 1925435 6503543 := bstep (se 1 (by rfl) ⟨4877657, by rfl⟩ : syracuseStep 6503543 = 9755315) B9755315
theorem B4335695 : Blo 1925435 4335695 := bstep (se 1 (by rfl) ⟨3251771, by rfl⟩ : syracuseStep 4335695 = 6503543) B6503543
theorem B2890463 : Blo 1925435 2890463 := bstep (se 1 (by rfl) ⟨2167847, by rfl⟩ : syracuseStep 2890463 = 4335695) B4335695
theorem B1926975 : Blo 1925435 1926975 := bstep (se 1 (by rfl) ⟨1445231, by rfl⟩ : syracuseStep 1926975 = 2890463) B2890463
theorem B2890469 : Blo 1925435 2890469 := bbase (se 4 (by rfl) ⟨270981, by rfl⟩ : syracuseStep 2890469 = 541963) (by norm_num)
theorem B1926979 : Blo 1925435 1926979 := bstep (se 1 (by rfl) ⟨1445234, by rfl⟩ : syracuseStep 1926979 = 2890469) B2890469
theorem B2314993 : Blo 1925435 2314993 := bbase (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) (by norm_num)
theorem B3086657 : Blo 1925435 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B2057771 : Blo 1925435 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B5487389 : Blo 1925435 5487389 := bstep (se 3 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 5487389 = 2057771) B2057771
theorem B3658259 : Blo 1925435 3658259 := bstep (se 1 (by rfl) ⟨2743694, by rfl⟩ : syracuseStep 3658259 = 5487389) B5487389
theorem B2438839 : Blo 1925435 2438839 := bstep (se 1 (by rfl) ⟨1829129, by rfl⟩ : syracuseStep 2438839 = 3658259) B3658259
theorem B3251785 : Blo 1925435 3251785 := bstep (se 2 (by rfl) ⟨1219419, by rfl⟩ : syracuseStep 3251785 = 2438839) B2438839
theorem B4335713 : Blo 1925435 4335713 := bstep (se 2 (by rfl) ⟨1625892, by rfl⟩ : syracuseStep 4335713 = 3251785) B3251785
theorem B2890475 : Blo 1925435 2890475 := bstep (se 1 (by rfl) ⟨2167856, by rfl⟩ : syracuseStep 2890475 = 4335713) B4335713
theorem B1926983 : Blo 1925435 1926983 := bstep (se 1 (by rfl) ⟨1445237, by rfl⟩ : syracuseStep 1926983 = 2890475) B2890475
theorem B2167861 : Blo 1925435 2167861 := bbase (se 5 (by rfl) ⟨101618, by rfl⟩ : syracuseStep 2167861 = 203237) (by norm_num)
theorem B2890481 : Blo 1925435 2890481 := bstep (se 2 (by rfl) ⟨1083930, by rfl⟩ : syracuseStep 2890481 = 2167861) B2167861
theorem B1926987 : Blo 1925435 1926987 := bstep (se 1 (by rfl) ⟨1445240, by rfl⟩ : syracuseStep 1926987 = 2890481) B2890481
theorem B2438849 : Blo 1925435 2438849 := bbase (se 2 (by rfl) ⟨914568, by rfl⟩ : syracuseStep 2438849 = 1829137) (by norm_num)
theorem B6503597 : Blo 1925435 6503597 := bstep (se 3 (by rfl) ⟨1219424, by rfl⟩ : syracuseStep 6503597 = 2438849) B2438849
theorem B4335731 : Blo 1925435 4335731 := bstep (se 1 (by rfl) ⟨3251798, by rfl⟩ : syracuseStep 4335731 = 6503597) B6503597
theorem B2890487 : Blo 1925435 2890487 := bstep (se 1 (by rfl) ⟨2167865, by rfl⟩ : syracuseStep 2890487 = 4335731) B4335731
theorem B1926991 : Blo 1925435 1926991 := bstep (se 1 (by rfl) ⟨1445243, by rfl⟩ : syracuseStep 1926991 = 2890487) B2890487
theorem B2890493 : Blo 1925435 2890493 := bbase (se 3 (by rfl) ⟨541967, by rfl⟩ : syracuseStep 2890493 = 1083935) (by norm_num)
theorem B1926995 : Blo 1925435 1926995 := bstep (se 1 (by rfl) ⟨1445246, by rfl⟩ : syracuseStep 1926995 = 2890493) B2890493
theorem B4335749 : Blo 1925435 4335749 := bbase (se 4 (by rfl) ⟨406476, by rfl⟩ : syracuseStep 4335749 = 812953) (by norm_num)
theorem B2890499 : Blo 1925435 2890499 := bstep (se 1 (by rfl) ⟨2167874, by rfl⟩ : syracuseStep 2890499 = 4335749) B4335749
theorem B1926999 : Blo 1925435 1926999 := bstep (se 1 (by rfl) ⟨1445249, by rfl⟩ : syracuseStep 1926999 = 2890499) B2890499
theorem B2315017 : Blo 1925435 2315017 := bbase (se 2 (by rfl) ⟨868131, by rfl⟩ : syracuseStep 2315017 = 1736263) (by norm_num)
theorem B3086689 : Blo 1925435 3086689 := bstep (se 2 (by rfl) ⟨1157508, by rfl⟩ : syracuseStep 3086689 = 2315017) B2315017
theorem B4115585 : Blo 1925435 4115585 := bstep (se 2 (by rfl) ⟨1543344, by rfl⟩ : syracuseStep 4115585 = 3086689) B3086689
theorem B2743723 : Blo 1925435 2743723 := bstep (se 1 (by rfl) ⟨2057792, by rfl⟩ : syracuseStep 2743723 = 4115585) B4115585
theorem B3658297 : Blo 1925435 3658297 := bstep (se 2 (by rfl) ⟨1371861, by rfl⟩ : syracuseStep 3658297 = 2743723) B2743723
theorem B4877729 : Blo 1925435 4877729 := bstep (se 2 (by rfl) ⟨1829148, by rfl⟩ : syracuseStep 4877729 = 3658297) B3658297
theorem B3251819 : Blo 1925435 3251819 := bstep (se 1 (by rfl) ⟨2438864, by rfl⟩ : syracuseStep 3251819 = 4877729) B4877729
theorem B2167879 : Blo 1925435 2167879 := bstep (se 1 (by rfl) ⟨1625909, by rfl⟩ : syracuseStep 2167879 = 3251819) B3251819
theorem B2890505 : Blo 1925435 2890505 := bstep (se 2 (by rfl) ⟨1083939, by rfl⟩ : syracuseStep 2890505 = 2167879) B2167879
theorem B1927003 : Blo 1925435 1927003 := bstep (se 1 (by rfl) ⟨1445252, by rfl⟩ : syracuseStep 1927003 = 2890505) B2890505
theorem B9755477 : Blo 1925435 9755477 := bbase (se 9 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 9755477 = 57161) (by norm_num)
theorem B6503651 : Blo 1925435 6503651 := bstep (se 1 (by rfl) ⟨4877738, by rfl⟩ : syracuseStep 6503651 = 9755477) B9755477
theorem B4335767 : Blo 1925435 4335767 := bstep (se 1 (by rfl) ⟨3251825, by rfl⟩ : syracuseStep 4335767 = 6503651) B6503651
theorem B2890511 : Blo 1925435 2890511 := bstep (se 1 (by rfl) ⟨2167883, by rfl⟩ : syracuseStep 2890511 = 4335767) B4335767
theorem B1927007 : Blo 1925435 1927007 := bstep (se 1 (by rfl) ⟨1445255, by rfl⟩ : syracuseStep 1927007 = 2890511) B2890511
theorem B2890517 : Blo 1925435 2890517 := bbase (se 6 (by rfl) ⟨67746, by rfl⟩ : syracuseStep 2890517 = 135493) (by norm_num)
theorem B1927011 : Blo 1925435 1927011 := bstep (se 1 (by rfl) ⟨1445258, by rfl⟩ : syracuseStep 1927011 = 2890517) B2890517
theorem B4394941 : Blo 1925435 4394941 := bbase (se 3 (by rfl) ⟨824051, by rfl⟩ : syracuseStep 4394941 = 1648103) (by norm_num)
theorem B93758741 : Blo 1925435 93758741 := bstep (se 6 (by rfl) ⟨2197470, by rfl⟩ : syracuseStep 93758741 = 4394941) B4394941
theorem B62505827 : Blo 1925435 62505827 := bstep (se 1 (by rfl) ⟨46879370, by rfl⟩ : syracuseStep 62505827 = 93758741) B93758741
theorem B41670551 : Blo 1925435 41670551 := bstep (se 1 (by rfl) ⟨31252913, by rfl⟩ : syracuseStep 41670551 = 62505827) B62505827
theorem B27780367 : Blo 1925435 27780367 := bstep (se 1 (by rfl) ⟨20835275, by rfl⟩ : syracuseStep 27780367 = 41670551) B41670551
theorem B37040489 : Blo 1925435 37040489 := bstep (se 2 (by rfl) ⟨13890183, by rfl⟩ : syracuseStep 37040489 = 27780367) B27780367
theorem B24693659 : Blo 1925435 24693659 := bstep (se 1 (by rfl) ⟨18520244, by rfl⟩ : syracuseStep 24693659 = 37040489) B37040489
theorem B16462439 : Blo 1925435 16462439 := bstep (se 1 (by rfl) ⟨12346829, by rfl⟩ : syracuseStep 16462439 = 24693659) B24693659
theorem B10974959 : Blo 1925435 10974959 := bstep (se 1 (by rfl) ⟨8231219, by rfl⟩ : syracuseStep 10974959 = 16462439) B16462439
theorem B7316639 : Blo 1925435 7316639 := bstep (se 1 (by rfl) ⟨5487479, by rfl⟩ : syracuseStep 7316639 = 10974959) B10974959
theorem B4877759 : Blo 1925435 4877759 := bstep (se 1 (by rfl) ⟨3658319, by rfl⟩ : syracuseStep 4877759 = 7316639) B7316639
theorem B3251839 : Blo 1925435 3251839 := bstep (se 1 (by rfl) ⟨2438879, by rfl⟩ : syracuseStep 3251839 = 4877759) B4877759
theorem B4335785 : Blo 1925435 4335785 := bstep (se 2 (by rfl) ⟨1625919, by rfl⟩ : syracuseStep 4335785 = 3251839) B3251839
theorem B2890523 : Blo 1925435 2890523 := bstep (se 1 (by rfl) ⟨2167892, by rfl⟩ : syracuseStep 2890523 = 4335785) B4335785
theorem B1927015 : Blo 1925435 1927015 := bstep (se 1 (by rfl) ⟨1445261, by rfl⟩ : syracuseStep 1927015 = 2890523) B2890523
theorem B2167897 : Blo 1925435 2167897 := bbase (se 2 (by rfl) ⟨812961, by rfl⟩ : syracuseStep 2167897 = 1625923) (by norm_num)
theorem B2890529 : Blo 1925435 2890529 := bstep (se 2 (by rfl) ⟨1083948, by rfl⟩ : syracuseStep 2890529 = 2167897) B2167897
theorem B1927019 : Blo 1925435 1927019 := bstep (se 1 (by rfl) ⟨1445264, by rfl⟩ : syracuseStep 1927019 = 2890529) B2890529
theorem B2604421 : Blo 1925435 2604421 := bbase (se 4 (by rfl) ⟨244164, by rfl⟩ : syracuseStep 2604421 = 488329) (by norm_num)
theorem B3472561 : Blo 1925435 3472561 := bstep (se 2 (by rfl) ⟨1302210, by rfl⟩ : syracuseStep 3472561 = 2604421) B2604421
theorem B4630081 : Blo 1925435 4630081 := bstep (se 2 (by rfl) ⟨1736280, by rfl⟩ : syracuseStep 4630081 = 3472561) B3472561
theorem B6173441 : Blo 1925435 6173441 := bstep (se 2 (by rfl) ⟨2315040, by rfl⟩ : syracuseStep 6173441 = 4630081) B4630081
theorem B4115627 : Blo 1925435 4115627 := bstep (se 1 (by rfl) ⟨3086720, by rfl⟩ : syracuseStep 4115627 = 6173441) B6173441
theorem B2743751 : Blo 1925435 2743751 := bstep (se 1 (by rfl) ⟨2057813, by rfl⟩ : syracuseStep 2743751 = 4115627) B4115627
theorem B7316669 : Blo 1925435 7316669 := bstep (se 3 (by rfl) ⟨1371875, by rfl⟩ : syracuseStep 7316669 = 2743751) B2743751
theorem B4877779 : Blo 1925435 4877779 := bstep (se 1 (by rfl) ⟨3658334, by rfl⟩ : syracuseStep 4877779 = 7316669) B7316669
theorem B6503705 : Blo 1925435 6503705 := bstep (se 2 (by rfl) ⟨2438889, by rfl⟩ : syracuseStep 6503705 = 4877779) B4877779
theorem B4335803 : Blo 1925435 4335803 := bstep (se 1 (by rfl) ⟨3251852, by rfl⟩ : syracuseStep 4335803 = 6503705) B6503705
theorem B2890535 : Blo 1925435 2890535 := bstep (se 1 (by rfl) ⟨2167901, by rfl⟩ : syracuseStep 2890535 = 4335803) B4335803
theorem B1927023 : Blo 1925435 1927023 := bstep (se 1 (by rfl) ⟨1445267, by rfl⟩ : syracuseStep 1927023 = 2890535) B2890535
theorem B2890541 : Blo 1925435 2890541 := bbase (se 3 (by rfl) ⟨541976, by rfl⟩ : syracuseStep 2890541 = 1083953) (by norm_num)
theorem B1927027 : Blo 1925435 1927027 := bstep (se 1 (by rfl) ⟨1445270, by rfl⟩ : syracuseStep 1927027 = 2890541) B2890541
theorem B4335821 : Blo 1925435 4335821 := bbase (se 3 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 4335821 = 1625933) (by norm_num)
theorem B2890547 : Blo 1925435 2890547 := bstep (se 1 (by rfl) ⟨2167910, by rfl⟩ : syracuseStep 2890547 = 4335821) B4335821
theorem B1927031 : Blo 1925435 1927031 := bstep (se 1 (by rfl) ⟨1445273, by rfl⟩ : syracuseStep 1927031 = 2890547) B2890547
theorem B2438905 : Blo 1925435 2438905 := bbase (se 2 (by rfl) ⟨914589, by rfl⟩ : syracuseStep 2438905 = 1829179) (by norm_num)
theorem B3251873 : Blo 1925435 3251873 := bstep (se 2 (by rfl) ⟨1219452, by rfl⟩ : syracuseStep 3251873 = 2438905) B2438905
theorem B2167915 : Blo 1925435 2167915 := bstep (se 1 (by rfl) ⟨1625936, by rfl⟩ : syracuseStep 2167915 = 3251873) B3251873
theorem B2890553 : Blo 1925435 2890553 := bstep (se 2 (by rfl) ⟨1083957, by rfl⟩ : syracuseStep 2890553 = 2167915) B2167915
theorem B1927035 : Blo 1925435 1927035 := bstep (se 1 (by rfl) ⟨1445276, by rfl⟩ : syracuseStep 1927035 = 2890553) B2890553
theorem B3472589 : Blo 1925435 3472589 := bbase (se 3 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 3472589 = 1302221) (by norm_num)
theorem B9260237 : Blo 1925435 9260237 := bstep (se 3 (by rfl) ⟨1736294, by rfl⟩ : syracuseStep 9260237 = 3472589) B3472589
theorem B6173491 : Blo 1925435 6173491 := bstep (se 1 (by rfl) ⟨4630118, by rfl⟩ : syracuseStep 6173491 = 9260237) B9260237
theorem B8231321 : Blo 1925435 8231321 := bstep (se 2 (by rfl) ⟨3086745, by rfl⟩ : syracuseStep 8231321 = 6173491) B6173491
theorem B21950189 : Blo 1925435 21950189 := bstep (se 3 (by rfl) ⟨4115660, by rfl⟩ : syracuseStep 21950189 = 8231321) B8231321
theorem B14633459 : Blo 1925435 14633459 := bstep (se 1 (by rfl) ⟨10975094, by rfl⟩ : syracuseStep 14633459 = 21950189) B21950189
theorem B9755639 : Blo 1925435 9755639 := bstep (se 1 (by rfl) ⟨7316729, by rfl⟩ : syracuseStep 9755639 = 14633459) B14633459
theorem B6503759 : Blo 1925435 6503759 := bstep (se 1 (by rfl) ⟨4877819, by rfl⟩ : syracuseStep 6503759 = 9755639) B9755639
theorem B4335839 : Blo 1925435 4335839 := bstep (se 1 (by rfl) ⟨3251879, by rfl⟩ : syracuseStep 4335839 = 6503759) B6503759
theorem B2890559 : Blo 1925435 2890559 := bstep (se 1 (by rfl) ⟨2167919, by rfl⟩ : syracuseStep 2890559 = 4335839) B4335839
theorem B1927039 : Blo 1925435 1927039 := bstep (se 1 (by rfl) ⟨1445279, by rfl⟩ : syracuseStep 1927039 = 2890559) B2890559
theorem B2890565 : Blo 1925435 2890565 := bbase (se 4 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 2890565 = 541981) (by norm_num)
theorem B1927043 : Blo 1925435 1927043 := bstep (se 1 (by rfl) ⟨1445282, by rfl⟩ : syracuseStep 1927043 = 2890565) B2890565
theorem B3251893 : Blo 1925435 3251893 := bbase (se 5 (by rfl) ⟨152432, by rfl⟩ : syracuseStep 3251893 = 304865) (by norm_num)
theorem B4335857 : Blo 1925435 4335857 := bstep (se 2 (by rfl) ⟨1625946, by rfl⟩ : syracuseStep 4335857 = 3251893) B3251893
theorem B2890571 : Blo 1925435 2890571 := bstep (se 1 (by rfl) ⟨2167928, by rfl⟩ : syracuseStep 2890571 = 4335857) B4335857
theorem B1927047 : Blo 1925435 1927047 := bstep (se 1 (by rfl) ⟨1445285, by rfl⟩ : syracuseStep 1927047 = 2890571) B2890571
theorem B2167933 : Blo 1925435 2167933 := bbase (se 3 (by rfl) ⟨406487, by rfl⟩ : syracuseStep 2167933 = 812975) (by norm_num)
theorem B2890577 : Blo 1925435 2890577 := bstep (se 2 (by rfl) ⟨1083966, by rfl⟩ : syracuseStep 2890577 = 2167933) B2167933
theorem B1927051 : Blo 1925435 1927051 := bstep (se 1 (by rfl) ⟨1445288, by rfl⟩ : syracuseStep 1927051 = 2890577) B2890577
theorem B6503813 : Blo 1925435 6503813 := bbase (se 4 (by rfl) ⟨609732, by rfl⟩ : syracuseStep 6503813 = 1219465) (by norm_num)
theorem B4335875 : Blo 1925435 4335875 := bstep (se 1 (by rfl) ⟨3251906, by rfl⟩ : syracuseStep 4335875 = 6503813) B6503813
theorem B2890583 : Blo 1925435 2890583 := bstep (se 1 (by rfl) ⟨2167937, by rfl⟩ : syracuseStep 2890583 = 4335875) B4335875
theorem B1927055 : Blo 1925435 1927055 := bstep (se 1 (by rfl) ⟨1445291, by rfl⟩ : syracuseStep 1927055 = 2890583) B2890583
theorem B2890589 : Blo 1925435 2890589 := bbase (se 3 (by rfl) ⟨541985, by rfl⟩ : syracuseStep 2890589 = 1083971) (by norm_num)
theorem B1927059 : Blo 1925435 1927059 := bstep (se 1 (by rfl) ⟨1445294, by rfl⟩ : syracuseStep 1927059 = 2890589) B2890589
theorem B4335893 : Blo 1925435 4335893 := bbase (se 6 (by rfl) ⟨101622, by rfl⟩ : syracuseStep 4335893 = 203245) (by norm_num)
theorem B2890595 : Blo 1925435 2890595 := bstep (se 1 (by rfl) ⟨2167946, by rfl⟩ : syracuseStep 2890595 = 4335893) B4335893
theorem B1927063 : Blo 1925435 1927063 := bstep (se 1 (by rfl) ⟨1445297, by rfl⟩ : syracuseStep 1927063 = 2890595) B2890595
theorem B7316837 : Blo 1925435 7316837 := bbase (se 4 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 7316837 = 1371907) (by norm_num)
theorem B4877891 : Blo 1925435 4877891 := bstep (se 1 (by rfl) ⟨3658418, by rfl⟩ : syracuseStep 4877891 = 7316837) B7316837
theorem B3251927 : Blo 1925435 3251927 := bstep (se 1 (by rfl) ⟨2438945, by rfl⟩ : syracuseStep 3251927 = 4877891) B4877891
theorem B2167951 : Blo 1925435 2167951 := bstep (se 1 (by rfl) ⟨1625963, by rfl⟩ : syracuseStep 2167951 = 3251927) B3251927
theorem B2890601 : Blo 1925435 2890601 := bstep (se 2 (by rfl) ⟨1083975, by rfl⟩ : syracuseStep 2890601 = 2167951) B2167951
theorem B1927067 : Blo 1925435 1927067 := bstep (se 1 (by rfl) ⟨1445300, by rfl⟩ : syracuseStep 1927067 = 2890601) B2890601
theorem B3086797 : Blo 1925435 3086797 := bbase (se 3 (by rfl) ⟨578774, by rfl⟩ : syracuseStep 3086797 = 1157549) (by norm_num)
theorem B4115729 : Blo 1925435 4115729 := bstep (se 2 (by rfl) ⟨1543398, by rfl⟩ : syracuseStep 4115729 = 3086797) B3086797
theorem B10975277 : Blo 1925435 10975277 := bstep (se 3 (by rfl) ⟨2057864, by rfl⟩ : syracuseStep 10975277 = 4115729) B4115729
theorem B7316851 : Blo 1925435 7316851 := bstep (se 1 (by rfl) ⟨5487638, by rfl⟩ : syracuseStep 7316851 = 10975277) B10975277
theorem B9755801 : Blo 1925435 9755801 := bstep (se 2 (by rfl) ⟨3658425, by rfl⟩ : syracuseStep 9755801 = 7316851) B7316851
theorem B6503867 : Blo 1925435 6503867 := bstep (se 1 (by rfl) ⟨4877900, by rfl⟩ : syracuseStep 6503867 = 9755801) B9755801
theorem B4335911 : Blo 1925435 4335911 := bstep (se 1 (by rfl) ⟨3251933, by rfl⟩ : syracuseStep 4335911 = 6503867) B6503867
theorem B2890607 : Blo 1925435 2890607 := bstep (se 1 (by rfl) ⟨2167955, by rfl⟩ : syracuseStep 2890607 = 4335911) B4335911
theorem B1927071 : Blo 1925435 1927071 := bstep (se 1 (by rfl) ⟨1445303, by rfl⟩ : syracuseStep 1927071 = 2890607) B2890607
theorem B2890613 : Blo 1925435 2890613 := bbase (se 5 (by rfl) ⟨135497, by rfl⟩ : syracuseStep 2890613 = 270995) (by norm_num)
theorem B1927075 : Blo 1925435 1927075 := bstep (se 1 (by rfl) ⟨1445306, by rfl⟩ : syracuseStep 1927075 = 2890613) B2890613
theorem B6173621 : Blo 1925435 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B4115747 : Blo 1925435 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B2743831 : Blo 1925435 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B3658441 : Blo 1925435 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B4877921 : Blo 1925435 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B3251947 : Blo 1925435 3251947 := bstep (se 1 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 3251947 = 4877921) B4877921
theorem B4335929 : Blo 1925435 4335929 := bstep (se 2 (by rfl) ⟨1625973, by rfl⟩ : syracuseStep 4335929 = 3251947) B3251947
theorem B2890619 : Blo 1925435 2890619 := bstep (se 1 (by rfl) ⟨2167964, by rfl⟩ : syracuseStep 2890619 = 4335929) B4335929
theorem B1927079 : Blo 1925435 1927079 := bstep (se 1 (by rfl) ⟨1445309, by rfl⟩ : syracuseStep 1927079 = 2890619) B2890619
theorem B2167969 : Blo 1925435 2167969 := bbase (se 2 (by rfl) ⟨812988, by rfl⟩ : syracuseStep 2167969 = 1625977) (by norm_num)
theorem B2890625 : Blo 1925435 2890625 := bstep (se 2 (by rfl) ⟨1083984, by rfl⟩ : syracuseStep 2890625 = 2167969) B2167969
theorem B1927083 : Blo 1925435 1927083 := bstep (se 1 (by rfl) ⟨1445312, by rfl⟩ : syracuseStep 1927083 = 2890625) B2890625
theorem B4877941 : Blo 1925435 4877941 := bbase (se 5 (by rfl) ⟨228653, by rfl⟩ : syracuseStep 4877941 = 457307) (by norm_num)
theorem B6503921 : Blo 1925435 6503921 := bstep (se 2 (by rfl) ⟨2438970, by rfl⟩ : syracuseStep 6503921 = 4877941) B4877941
theorem B4335947 : Blo 1925435 4335947 := bstep (se 1 (by rfl) ⟨3251960, by rfl⟩ : syracuseStep 4335947 = 6503921) B6503921
theorem B2890631 : Blo 1925435 2890631 := bstep (se 1 (by rfl) ⟨2167973, by rfl⟩ : syracuseStep 2890631 = 4335947) B4335947
theorem B1927087 : Blo 1925435 1927087 := bstep (se 1 (by rfl) ⟨1445315, by rfl⟩ : syracuseStep 1927087 = 2890631) B2890631
theorem B2890637 : Blo 1925435 2890637 := bbase (se 3 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 2890637 = 1083989) (by norm_num)
theorem B1927091 : Blo 1925435 1927091 := bstep (se 1 (by rfl) ⟨1445318, by rfl⟩ : syracuseStep 1927091 = 2890637) B2890637
theorem B4335965 : Blo 1925435 4335965 := bbase (se 3 (by rfl) ⟨812993, by rfl⟩ : syracuseStep 4335965 = 1625987) (by norm_num)
theorem B2890643 : Blo 1925435 2890643 := bstep (se 1 (by rfl) ⟨2167982, by rfl⟩ : syracuseStep 2890643 = 4335965) B4335965
theorem B1927095 : Blo 1925435 1927095 := bstep (se 1 (by rfl) ⟨1445321, by rfl⟩ : syracuseStep 1927095 = 2890643) B2890643
theorem B3251981 : Blo 1925435 3251981 := bbase (se 3 (by rfl) ⟨609746, by rfl⟩ : syracuseStep 3251981 = 1219493) (by norm_num)
theorem B2167987 : Blo 1925435 2167987 := bstep (se 1 (by rfl) ⟨1625990, by rfl⟩ : syracuseStep 2167987 = 3251981) B3251981
theorem B2890649 : Blo 1925435 2890649 := bstep (se 2 (by rfl) ⟨1083993, by rfl⟩ : syracuseStep 2890649 = 2167987) B2167987
theorem B1927099 : Blo 1925435 1927099 := bstep (se 1 (by rfl) ⟨1445324, by rfl⟩ : syracuseStep 1927099 = 2890649) B2890649
theorem B16463189 : Blo 1925435 16463189 := bbase (se 13 (by rfl) ⟨3014, by rfl⟩ : syracuseStep 16463189 = 6029) (by norm_num)
theorem B10975459 : Blo 1925435 10975459 := bstep (se 1 (by rfl) ⟨8231594, by rfl⟩ : syracuseStep 10975459 = 16463189) B16463189
theorem B14633945 : Blo 1925435 14633945 := bstep (se 2 (by rfl) ⟨5487729, by rfl⟩ : syracuseStep 14633945 = 10975459) B10975459
theorem B9755963 : Blo 1925435 9755963 := bstep (se 1 (by rfl) ⟨7316972, by rfl⟩ : syracuseStep 9755963 = 14633945) B14633945
theorem B6503975 : Blo 1925435 6503975 := bstep (se 1 (by rfl) ⟨4877981, by rfl⟩ : syracuseStep 6503975 = 9755963) B9755963
theorem B4335983 : Blo 1925435 4335983 := bstep (se 1 (by rfl) ⟨3251987, by rfl⟩ : syracuseStep 4335983 = 6503975) B6503975
theorem B2890655 : Blo 1925435 2890655 := bstep (se 1 (by rfl) ⟨2167991, by rfl⟩ : syracuseStep 2890655 = 4335983) B4335983
theorem B1927103 : Blo 1925435 1927103 := bstep (se 1 (by rfl) ⟨1445327, by rfl⟩ : syracuseStep 1927103 = 2890655) B2890655
theorem B2890661 : Blo 1925435 2890661 := bbase (se 4 (by rfl) ⟨270999, by rfl⟩ : syracuseStep 2890661 = 541999) (by norm_num)
theorem B1927107 : Blo 1925435 1927107 := bstep (se 1 (by rfl) ⟨1445330, by rfl⟩ : syracuseStep 1927107 = 2890661) B2890661
theorem B2439001 : Blo 1925435 2439001 := bbase (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) (by norm_num)
theorem B3252001 : Blo 1925435 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B4336001 : Blo 1925435 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B2890667 : Blo 1925435 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B1927111 : Blo 1925435 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B2168005 : Blo 1925435 2168005 := bbase (se 4 (by rfl) ⟨203250, by rfl⟩ : syracuseStep 2168005 = 406501) (by norm_num)
theorem B2890673 : Blo 1925435 2890673 := bstep (se 2 (by rfl) ⟨1084002, by rfl⟩ : syracuseStep 2890673 = 2168005) B2168005
theorem B1927115 : Blo 1925435 1927115 := bstep (se 1 (by rfl) ⟨1445336, by rfl⟩ : syracuseStep 1927115 = 2890673) B2890673
theorem B3658517 : Blo 1925435 3658517 := bbase (se 6 (by rfl) ⟨85746, by rfl⟩ : syracuseStep 3658517 = 171493) (by norm_num)
theorem B2439011 : Blo 1925435 2439011 := bstep (se 1 (by rfl) ⟨1829258, by rfl⟩ : syracuseStep 2439011 = 3658517) B3658517
theorem B6504029 : Blo 1925435 6504029 := bstep (se 3 (by rfl) ⟨1219505, by rfl⟩ : syracuseStep 6504029 = 2439011) B2439011
theorem B4336019 : Blo 1925435 4336019 := bstep (se 1 (by rfl) ⟨3252014, by rfl⟩ : syracuseStep 4336019 = 6504029) B6504029
theorem B2890679 : Blo 1925435 2890679 := bstep (se 1 (by rfl) ⟨2168009, by rfl⟩ : syracuseStep 2890679 = 4336019) B4336019
theorem B1927119 : Blo 1925435 1927119 := bstep (se 1 (by rfl) ⟨1445339, by rfl⟩ : syracuseStep 1927119 = 2890679) B2890679
theorem B2890685 : Blo 1925435 2890685 := bbase (se 3 (by rfl) ⟨542003, by rfl⟩ : syracuseStep 2890685 = 1084007) (by norm_num)
theorem B1927123 : Blo 1925435 1927123 := bstep (se 1 (by rfl) ⟨1445342, by rfl⟩ : syracuseStep 1927123 = 2890685) B2890685
theorem B4336037 : Blo 1925435 4336037 := bbase (se 4 (by rfl) ⟨406503, by rfl⟩ : syracuseStep 4336037 = 813007) (by norm_num)
theorem B2890691 : Blo 1925435 2890691 := bstep (se 1 (by rfl) ⟨2168018, by rfl⟩ : syracuseStep 2890691 = 4336037) B4336037
theorem B1927127 : Blo 1925435 1927127 := bstep (se 1 (by rfl) ⟨1445345, by rfl⟩ : syracuseStep 1927127 = 2890691) B2890691
theorem B4878053 : Blo 1925435 4878053 := bbase (se 4 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 4878053 = 914635) (by norm_num)
theorem B3252035 : Blo 1925435 3252035 := bstep (se 1 (by rfl) ⟨2439026, by rfl⟩ : syracuseStep 3252035 = 4878053) B4878053
theorem B2168023 : Blo 1925435 2168023 := bstep (se 1 (by rfl) ⟨1626017, by rfl⟩ : syracuseStep 2168023 = 3252035) B3252035
theorem B2890697 : Blo 1925435 2890697 := bstep (se 2 (by rfl) ⟨1084011, by rfl⟩ : syracuseStep 2890697 = 2168023) B2168023
theorem B1927131 : Blo 1925435 1927131 := bstep (se 1 (by rfl) ⟨1445348, by rfl⟩ : syracuseStep 1927131 = 2890697) B2890697
theorem B2057933 : Blo 1925435 2057933 := bbase (se 3 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 2057933 = 771725) (by norm_num)
theorem B5487821 : Blo 1925435 5487821 := bstep (se 3 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 5487821 = 2057933) B2057933
theorem B3658547 : Blo 1925435 3658547 := bstep (se 1 (by rfl) ⟨2743910, by rfl⟩ : syracuseStep 3658547 = 5487821) B5487821
theorem B9756125 : Blo 1925435 9756125 := bstep (se 3 (by rfl) ⟨1829273, by rfl⟩ : syracuseStep 9756125 = 3658547) B3658547
theorem B6504083 : Blo 1925435 6504083 := bstep (se 1 (by rfl) ⟨4878062, by rfl⟩ : syracuseStep 6504083 = 9756125) B9756125
theorem B4336055 : Blo 1925435 4336055 := bstep (se 1 (by rfl) ⟨3252041, by rfl⟩ : syracuseStep 4336055 = 6504083) B6504083
theorem B2890703 : Blo 1925435 2890703 := bstep (se 1 (by rfl) ⟨2168027, by rfl⟩ : syracuseStep 2890703 = 4336055) B4336055
theorem B1927135 : Blo 1925435 1927135 := bstep (se 1 (by rfl) ⟨1445351, by rfl⟩ : syracuseStep 1927135 = 2890703) B2890703
theorem B2890709 : Blo 1925435 2890709 := bbase (se 7 (by rfl) ⟨33875, by rfl⟩ : syracuseStep 2890709 = 67751) (by norm_num)
theorem B1927139 : Blo 1925435 1927139 := bstep (se 1 (by rfl) ⟨1445354, by rfl⟩ : syracuseStep 1927139 = 2890709) B2890709
theorem B7317125 : Blo 1925435 7317125 := bbase (se 4 (by rfl) ⟨685980, by rfl⟩ : syracuseStep 7317125 = 1371961) (by norm_num)
theorem B4878083 : Blo 1925435 4878083 := bstep (se 1 (by rfl) ⟨3658562, by rfl⟩ : syracuseStep 4878083 = 7317125) B7317125
theorem B3252055 : Blo 1925435 3252055 := bstep (se 1 (by rfl) ⟨2439041, by rfl⟩ : syracuseStep 3252055 = 4878083) B4878083
theorem B4336073 : Blo 1925435 4336073 := bstep (se 2 (by rfl) ⟨1626027, by rfl⟩ : syracuseStep 4336073 = 3252055) B3252055
theorem B2890715 : Blo 1925435 2890715 := bstep (se 1 (by rfl) ⟨2168036, by rfl⟩ : syracuseStep 2890715 = 4336073) B4336073
theorem B1927143 : Blo 1925435 1927143 := bstep (se 1 (by rfl) ⟨1445357, by rfl⟩ : syracuseStep 1927143 = 2890715) B2890715
theorem B2168041 : Blo 1925435 2168041 := bbase (se 2 (by rfl) ⟨813015, by rfl⟩ : syracuseStep 2168041 = 1626031) (by norm_num)
theorem B2890721 : Blo 1925435 2890721 := bstep (se 2 (by rfl) ⟨1084020, by rfl⟩ : syracuseStep 2890721 = 2168041) B2168041
theorem B1927147 : Blo 1925435 1927147 := bstep (se 1 (by rfl) ⟨1445360, by rfl⟩ : syracuseStep 1927147 = 2890721) B2890721
theorem B10975733 : Blo 1925435 10975733 := bbase (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) (by norm_num)
theorem B7317155 : Blo 1925435 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B4878103 : Blo 1925435 4878103 := bstep (se 1 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 4878103 = 7317155) B7317155
theorem B6504137 : Blo 1925435 6504137 := bstep (se 2 (by rfl) ⟨2439051, by rfl⟩ : syracuseStep 6504137 = 4878103) B4878103
theorem B4336091 : Blo 1925435 4336091 := bstep (se 1 (by rfl) ⟨3252068, by rfl⟩ : syracuseStep 4336091 = 6504137) B6504137
theorem B2890727 : Blo 1925435 2890727 := bstep (se 1 (by rfl) ⟨2168045, by rfl⟩ : syracuseStep 2890727 = 4336091) B4336091
theorem B1927151 : Blo 1925435 1927151 := bstep (se 1 (by rfl) ⟨1445363, by rfl⟩ : syracuseStep 1927151 = 2890727) B2890727
theorem B2890733 : Blo 1925435 2890733 := bbase (se 3 (by rfl) ⟨542012, by rfl⟩ : syracuseStep 2890733 = 1084025) (by norm_num)
theorem B1927155 : Blo 1925435 1927155 := bstep (se 1 (by rfl) ⟨1445366, by rfl⟩ : syracuseStep 1927155 = 2890733) B2890733
theorem B4336109 : Blo 1925435 4336109 := bbase (se 3 (by rfl) ⟨813020, by rfl⟩ : syracuseStep 4336109 = 1626041) (by norm_num)
theorem B2890739 : Blo 1925435 2890739 := bstep (se 1 (by rfl) ⟨2168054, by rfl⟩ : syracuseStep 2890739 = 4336109) B4336109
theorem B1927159 : Blo 1925435 1927159 := bstep (se 1 (by rfl) ⟨1445369, by rfl⟩ : syracuseStep 1927159 = 2890739) B2890739
theorem B9260837 : Blo 1925435 9260837 := bbase (se 4 (by rfl) ⟨868203, by rfl⟩ : syracuseStep 9260837 = 1736407) (by norm_num)
theorem B6173891 : Blo 1925435 6173891 := bstep (se 1 (by rfl) ⟨4630418, by rfl⟩ : syracuseStep 6173891 = 9260837) B9260837
theorem B4115927 : Blo 1925435 4115927 := bstep (se 1 (by rfl) ⟨3086945, by rfl⟩ : syracuseStep 4115927 = 6173891) B6173891
theorem B2743951 : Blo 1925435 2743951 := bstep (se 1 (by rfl) ⟨2057963, by rfl⟩ : syracuseStep 2743951 = 4115927) B4115927
theorem B3658601 : Blo 1925435 3658601 := bstep (se 2 (by rfl) ⟨1371975, by rfl⟩ : syracuseStep 3658601 = 2743951) B2743951
theorem B2439067 : Blo 1925435 2439067 := bstep (se 1 (by rfl) ⟨1829300, by rfl⟩ : syracuseStep 2439067 = 3658601) B3658601
theorem B3252089 : Blo 1925435 3252089 := bstep (se 2 (by rfl) ⟨1219533, by rfl⟩ : syracuseStep 3252089 = 2439067) B2439067
theorem B2168059 : Blo 1925435 2168059 := bstep (se 1 (by rfl) ⟨1626044, by rfl⟩ : syracuseStep 2168059 = 3252089) B3252089
theorem B2890745 : Blo 1925435 2890745 := bstep (se 2 (by rfl) ⟨1084029, by rfl⟩ : syracuseStep 2890745 = 2168059) B2168059
theorem B1927163 : Blo 1925435 1927163 := bstep (se 1 (by rfl) ⟨1445372, by rfl⟩ : syracuseStep 1927163 = 2890745) B2890745
theorem B25032533 : Blo 1925435 25032533 := bbase (se 9 (by rfl) ⟨73337, by rfl⟩ : syracuseStep 25032533 = 146675) (by norm_num)
theorem B267013685 : Blo 1925435 267013685 := bstep (se 5 (by rfl) ⟨12516266, by rfl⟩ : syracuseStep 267013685 = 25032533) B25032533
theorem B178009123 : Blo 1925435 178009123 := bstep (se 1 (by rfl) ⟨133506842, by rfl⟩ : syracuseStep 178009123 = 267013685) B267013685
theorem B237345497 : Blo 1925435 237345497 := bstep (se 2 (by rfl) ⟨89004561, by rfl⟩ : syracuseStep 237345497 = 178009123) B178009123
theorem B158230331 : Blo 1925435 158230331 := bstep (se 1 (by rfl) ⟨118672748, by rfl⟩ : syracuseStep 158230331 = 237345497) B237345497
theorem B105486887 : Blo 1925435 105486887 := bstep (se 1 (by rfl) ⟨79115165, by rfl⟩ : syracuseStep 105486887 = 158230331) B158230331
theorem B281298365 : Blo 1925435 281298365 := bstep (se 3 (by rfl) ⟨52743443, by rfl⟩ : syracuseStep 281298365 = 105486887) B105486887
theorem B187532243 : Blo 1925435 187532243 := bstep (se 1 (by rfl) ⟨140649182, by rfl⟩ : syracuseStep 187532243 = 281298365) B281298365
theorem B125021495 : Blo 1925435 125021495 := bstep (se 1 (by rfl) ⟨93766121, by rfl⟩ : syracuseStep 125021495 = 187532243) B187532243
theorem B83347663 : Blo 1925435 83347663 := bstep (se 1 (by rfl) ⟨62510747, by rfl⟩ : syracuseStep 83347663 = 125021495) B125021495
theorem B111130217 : Blo 1925435 111130217 := bstep (se 2 (by rfl) ⟨41673831, by rfl⟩ : syracuseStep 111130217 = 83347663) B83347663
theorem B74086811 : Blo 1925435 74086811 := bstep (se 1 (by rfl) ⟨55565108, by rfl⟩ : syracuseStep 74086811 = 111130217) B111130217
theorem B49391207 : Blo 1925435 49391207 := bstep (se 1 (by rfl) ⟨37043405, by rfl⟩ : syracuseStep 49391207 = 74086811) B74086811
theorem B32927471 : Blo 1925435 32927471 := bstep (se 1 (by rfl) ⟨24695603, by rfl⟩ : syracuseStep 32927471 = 49391207) B49391207
theorem B21951647 : Blo 1925435 21951647 := bstep (se 1 (by rfl) ⟨16463735, by rfl⟩ : syracuseStep 21951647 = 32927471) B32927471
theorem B14634431 : Blo 1925435 14634431 := bstep (se 1 (by rfl) ⟨10975823, by rfl⟩ : syracuseStep 14634431 = 21951647) B21951647
theorem B9756287 : Blo 1925435 9756287 := bstep (se 1 (by rfl) ⟨7317215, by rfl⟩ : syracuseStep 9756287 = 14634431) B14634431
theorem B6504191 : Blo 1925435 6504191 := bstep (se 1 (by rfl) ⟨4878143, by rfl⟩ : syracuseStep 6504191 = 9756287) B9756287
theorem B4336127 : Blo 1925435 4336127 := bstep (se 1 (by rfl) ⟨3252095, by rfl⟩ : syracuseStep 4336127 = 6504191) B6504191
theorem B2890751 : Blo 1925435 2890751 := bstep (se 1 (by rfl) ⟨2168063, by rfl⟩ : syracuseStep 2890751 = 4336127) B4336127
theorem B1927167 : Blo 1925435 1927167 := bstep (se 1 (by rfl) ⟨1445375, by rfl⟩ : syracuseStep 1927167 = 2890751) B2890751
theorem B2890757 : Blo 1925435 2890757 := bbase (se 4 (by rfl) ⟨271008, by rfl⟩ : syracuseStep 2890757 = 542017) (by norm_num)
theorem B1927171 : Blo 1925435 1927171 := bstep (se 1 (by rfl) ⟨1445378, by rfl⟩ : syracuseStep 1927171 = 2890757) B2890757
theorem B3252109 : Blo 1925435 3252109 := bbase (se 3 (by rfl) ⟨609770, by rfl⟩ : syracuseStep 3252109 = 1219541) (by norm_num)
theorem B4336145 : Blo 1925435 4336145 := bstep (se 2 (by rfl) ⟨1626054, by rfl⟩ : syracuseStep 4336145 = 3252109) B3252109
theorem B2890763 : Blo 1925435 2890763 := bstep (se 1 (by rfl) ⟨2168072, by rfl⟩ : syracuseStep 2890763 = 4336145) B4336145
theorem B1927175 : Blo 1925435 1927175 := bstep (se 1 (by rfl) ⟨1445381, by rfl⟩ : syracuseStep 1927175 = 2890763) B2890763
theorem B2168077 : Blo 1925435 2168077 := bbase (se 3 (by rfl) ⟨406514, by rfl⟩ : syracuseStep 2168077 = 813029) (by norm_num)
theorem B2890769 : Blo 1925435 2890769 := bstep (se 2 (by rfl) ⟨1084038, by rfl⟩ : syracuseStep 2890769 = 2168077) B2168077
theorem B1927179 : Blo 1925435 1927179 := bstep (se 1 (by rfl) ⟨1445384, by rfl⟩ : syracuseStep 1927179 = 2890769) B2890769
theorem B6504245 : Blo 1925435 6504245 := bbase (se 5 (by rfl) ⟨304886, by rfl⟩ : syracuseStep 6504245 = 609773) (by norm_num)
theorem B4336163 : Blo 1925435 4336163 := bstep (se 1 (by rfl) ⟨3252122, by rfl⟩ : syracuseStep 4336163 = 6504245) B6504245
theorem B2890775 : Blo 1925435 2890775 := bstep (se 1 (by rfl) ⟨2168081, by rfl⟩ : syracuseStep 2890775 = 4336163) B4336163
theorem B1927183 : Blo 1925435 1927183 := bstep (se 1 (by rfl) ⟨1445387, by rfl⟩ : syracuseStep 1927183 = 2890775) B2890775
theorem B2890781 : Blo 1925435 2890781 := bbase (se 3 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 2890781 = 1084043) (by norm_num)
theorem B1927187 : Blo 1925435 1927187 := bstep (se 1 (by rfl) ⟨1445390, by rfl⟩ : syracuseStep 1927187 = 2890781) B2890781
theorem B4336181 : Blo 1925435 4336181 := bbase (se 5 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 4336181 = 406517) (by norm_num)
theorem B2890787 : Blo 1925435 2890787 := bstep (se 1 (by rfl) ⟨2168090, by rfl⟩ : syracuseStep 2890787 = 4336181) B4336181
theorem B1927191 : Blo 1925435 1927191 := bstep (se 1 (by rfl) ⟨1445393, by rfl⟩ : syracuseStep 1927191 = 2890787) B2890787
theorem B8231989 : Blo 1925435 8231989 := bbase (se 5 (by rfl) ⟨385874, by rfl⟩ : syracuseStep 8231989 = 771749) (by norm_num)
theorem B10975985 : Blo 1925435 10975985 := bstep (se 2 (by rfl) ⟨4115994, by rfl⟩ : syracuseStep 10975985 = 8231989) B8231989
theorem B7317323 : Blo 1925435 7317323 := bstep (se 1 (by rfl) ⟨5487992, by rfl⟩ : syracuseStep 7317323 = 10975985) B10975985
theorem B4878215 : Blo 1925435 4878215 := bstep (se 1 (by rfl) ⟨3658661, by rfl⟩ : syracuseStep 4878215 = 7317323) B7317323
theorem B3252143 : Blo 1925435 3252143 := bstep (se 1 (by rfl) ⟨2439107, by rfl⟩ : syracuseStep 3252143 = 4878215) B4878215
theorem B2168095 : Blo 1925435 2168095 := bstep (se 1 (by rfl) ⟨1626071, by rfl⟩ : syracuseStep 2168095 = 3252143) B3252143
theorem B2890793 : Blo 1925435 2890793 := bstep (se 2 (by rfl) ⟨1084047, by rfl⟩ : syracuseStep 2890793 = 2168095) B2168095
theorem B1927195 : Blo 1925435 1927195 := bstep (se 1 (by rfl) ⟨1445396, by rfl⟩ : syracuseStep 1927195 = 2890793) B2890793
theorem B8232005 : Blo 1925435 8232005 := bbase (se 4 (by rfl) ⟨771750, by rfl⟩ : syracuseStep 8232005 = 1543501) (by norm_num)
theorem B5488003 : Blo 1925435 5488003 := bstep (se 1 (by rfl) ⟨4116002, by rfl⟩ : syracuseStep 5488003 = 8232005) B8232005
theorem B7317337 : Blo 1925435 7317337 := bstep (se 2 (by rfl) ⟨2744001, by rfl⟩ : syracuseStep 7317337 = 5488003) B5488003
theorem B9756449 : Blo 1925435 9756449 := bstep (se 2 (by rfl) ⟨3658668, by rfl⟩ : syracuseStep 9756449 = 7317337) B7317337
theorem B6504299 : Blo 1925435 6504299 := bstep (se 1 (by rfl) ⟨4878224, by rfl⟩ : syracuseStep 6504299 = 9756449) B9756449
theorem B4336199 : Blo 1925435 4336199 := bstep (se 1 (by rfl) ⟨3252149, by rfl⟩ : syracuseStep 4336199 = 6504299) B6504299
theorem B2890799 : Blo 1925435 2890799 := bstep (se 1 (by rfl) ⟨2168099, by rfl⟩ : syracuseStep 2890799 = 4336199) B4336199
theorem B1927199 : Blo 1925435 1927199 := bstep (se 1 (by rfl) ⟨1445399, by rfl⟩ : syracuseStep 1927199 = 2890799) B2890799
theorem B2890805 : Blo 1925435 2890805 := bbase (se 5 (by rfl) ⟨135506, by rfl⟩ : syracuseStep 2890805 = 271013) (by norm_num)
theorem B1927203 : Blo 1925435 1927203 := bstep (se 1 (by rfl) ⟨1445402, by rfl⟩ : syracuseStep 1927203 = 2890805) B2890805
theorem B4878245 : Blo 1925435 4878245 := bbase (se 4 (by rfl) ⟨457335, by rfl⟩ : syracuseStep 4878245 = 914671) (by norm_num)
theorem B3252163 : Blo 1925435 3252163 := bstep (se 1 (by rfl) ⟨2439122, by rfl⟩ : syracuseStep 3252163 = 4878245) B4878245
theorem B4336217 : Blo 1925435 4336217 := bstep (se 2 (by rfl) ⟨1626081, by rfl⟩ : syracuseStep 4336217 = 3252163) B3252163
theorem B2890811 : Blo 1925435 2890811 := bstep (se 1 (by rfl) ⟨2168108, by rfl⟩ : syracuseStep 2890811 = 4336217) B4336217
theorem B1927207 : Blo 1925435 1927207 := bstep (se 1 (by rfl) ⟨1445405, by rfl⟩ : syracuseStep 1927207 = 2890811) B2890811
theorem B2168113 : Blo 1925435 2168113 := bbase (se 2 (by rfl) ⟨813042, by rfl⟩ : syracuseStep 2168113 = 1626085) (by norm_num)
theorem B2890817 : Blo 1925435 2890817 := bstep (se 2 (by rfl) ⟨1084056, by rfl⟩ : syracuseStep 2890817 = 2168113) B2168113
theorem B1927211 : Blo 1925435 1927211 := bstep (se 1 (by rfl) ⟨1445408, by rfl⟩ : syracuseStep 1927211 = 2890817) B2890817
theorem B4116037 : Blo 1925435 4116037 := bbase (se 4 (by rfl) ⟨385878, by rfl⟩ : syracuseStep 4116037 = 771757) (by norm_num)
theorem B5488049 : Blo 1925435 5488049 := bstep (se 2 (by rfl) ⟨2058018, by rfl⟩ : syracuseStep 5488049 = 4116037) B4116037
theorem B3658699 : Blo 1925435 3658699 := bstep (se 1 (by rfl) ⟨2744024, by rfl⟩ : syracuseStep 3658699 = 5488049) B5488049
theorem B4878265 : Blo 1925435 4878265 := bstep (se 2 (by rfl) ⟨1829349, by rfl⟩ : syracuseStep 4878265 = 3658699) B3658699
theorem B6504353 : Blo 1925435 6504353 := bstep (se 2 (by rfl) ⟨2439132, by rfl⟩ : syracuseStep 6504353 = 4878265) B4878265
theorem B4336235 : Blo 1925435 4336235 := bstep (se 1 (by rfl) ⟨3252176, by rfl⟩ : syracuseStep 4336235 = 6504353) B6504353
theorem B2890823 : Blo 1925435 2890823 := bstep (se 1 (by rfl) ⟨2168117, by rfl⟩ : syracuseStep 2890823 = 4336235) B4336235
theorem B1927215 : Blo 1925435 1927215 := bstep (se 1 (by rfl) ⟨1445411, by rfl⟩ : syracuseStep 1927215 = 2890823) B2890823
theorem B2890829 : Blo 1925435 2890829 := bbase (se 3 (by rfl) ⟨542030, by rfl⟩ : syracuseStep 2890829 = 1084061) (by norm_num)
theorem B1927219 : Blo 1925435 1927219 := bstep (se 1 (by rfl) ⟨1445414, by rfl⟩ : syracuseStep 1927219 = 2890829) B2890829
theorem B4336253 : Blo 1925435 4336253 := bbase (se 3 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 4336253 = 1626095) (by norm_num)
theorem B2890835 : Blo 1925435 2890835 := bstep (se 1 (by rfl) ⟨2168126, by rfl⟩ : syracuseStep 2890835 = 4336253) B4336253
theorem B1927223 : Blo 1925435 1927223 := bstep (se 1 (by rfl) ⟨1445417, by rfl⟩ : syracuseStep 1927223 = 2890835) B2890835
theorem B3252197 : Blo 1925435 3252197 := bbase (se 4 (by rfl) ⟨304893, by rfl⟩ : syracuseStep 3252197 = 609787) (by norm_num)
theorem B2168131 : Blo 1925435 2168131 := bstep (se 1 (by rfl) ⟨1626098, by rfl⟩ : syracuseStep 2168131 = 3252197) B3252197
theorem B2890841 : Blo 1925435 2890841 := bstep (se 2 (by rfl) ⟨1084065, by rfl⟩ : syracuseStep 2890841 = 2168131) B2168131
theorem B1927227 : Blo 1925435 1927227 := bstep (se 1 (by rfl) ⟨1445420, by rfl⟩ : syracuseStep 1927227 = 2890841) B2890841
theorem B8790869 : Blo 1925435 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B23442317 : Blo 1925435 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B15628211 : Blo 1925435 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B10418807 : Blo 1925435 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B6945871 : Blo 1925435 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B9261161 : Blo 1925435 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B6174107 : Blo 1925435 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B4116071 : Blo 1925435 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B2744047 : Blo 1925435 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B14634917 : Blo 1925435 14634917 := bstep (se 4 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 14634917 = 2744047) B2744047
theorem B9756611 : Blo 1925435 9756611 := bstep (se 1 (by rfl) ⟨7317458, by rfl⟩ : syracuseStep 9756611 = 14634917) B14634917
theorem B6504407 : Blo 1925435 6504407 := bstep (se 1 (by rfl) ⟨4878305, by rfl⟩ : syracuseStep 6504407 = 9756611) B9756611
theorem B4336271 : Blo 1925435 4336271 := bstep (se 1 (by rfl) ⟨3252203, by rfl⟩ : syracuseStep 4336271 = 6504407) B6504407
theorem B2890847 : Blo 1925435 2890847 := bstep (se 1 (by rfl) ⟨2168135, by rfl⟩ : syracuseStep 2890847 = 4336271) B4336271
theorem B1927231 : Blo 1925435 1927231 := bstep (se 1 (by rfl) ⟨1445423, by rfl⟩ : syracuseStep 1927231 = 2890847) B2890847
theorem B2890853 : Blo 1925435 2890853 := bbase (se 4 (by rfl) ⟨271017, by rfl⟩ : syracuseStep 2890853 = 542035) (by norm_num)
theorem B1927235 : Blo 1925435 1927235 := bstep (se 1 (by rfl) ⟨1445426, by rfl⟩ : syracuseStep 1927235 = 2890853) B2890853
theorem B2506177 : Blo 1925435 2506177 := bbase (se 2 (by rfl) ⟨939816, by rfl⟩ : syracuseStep 2506177 = 1879633) (by norm_num)
theorem B3341569 : Blo 1925435 3341569 := bstep (se 2 (by rfl) ⟨1253088, by rfl⟩ : syracuseStep 3341569 = 2506177) B2506177
theorem B4455425 : Blo 1925435 4455425 := bstep (se 2 (by rfl) ⟨1670784, by rfl⟩ : syracuseStep 4455425 = 3341569) B3341569
theorem B11881133 : Blo 1925435 11881133 := bstep (se 3 (by rfl) ⟨2227712, by rfl⟩ : syracuseStep 11881133 = 4455425) B4455425
theorem B7920755 : Blo 1925435 7920755 := bstep (se 1 (by rfl) ⟨5940566, by rfl⟩ : syracuseStep 7920755 = 11881133) B11881133
theorem B5280503 : Blo 1925435 5280503 := bstep (se 1 (by rfl) ⟨3960377, by rfl⟩ : syracuseStep 5280503 = 7920755) B7920755
theorem B56325365 : Blo 1925435 56325365 := bstep (se 5 (by rfl) ⟨2640251, by rfl⟩ : syracuseStep 56325365 = 5280503) B5280503
theorem B37550243 : Blo 1925435 37550243 := bstep (se 1 (by rfl) ⟨28162682, by rfl⟩ : syracuseStep 37550243 = 56325365) B56325365
theorem B25033495 : Blo 1925435 25033495 := bstep (se 1 (by rfl) ⟨18775121, by rfl⟩ : syracuseStep 25033495 = 37550243) B37550243
theorem B33377993 : Blo 1925435 33377993 := bstep (se 2 (by rfl) ⟨12516747, by rfl⟩ : syracuseStep 33377993 = 25033495) B25033495
theorem B22251995 : Blo 1925435 22251995 := bstep (se 1 (by rfl) ⟨16688996, by rfl⟩ : syracuseStep 22251995 = 33377993) B33377993
theorem B14834663 : Blo 1925435 14834663 := bstep (se 1 (by rfl) ⟨11125997, by rfl⟩ : syracuseStep 14834663 = 22251995) B22251995
theorem B9889775 : Blo 1925435 9889775 := bstep (se 1 (by rfl) ⟨7417331, by rfl⟩ : syracuseStep 9889775 = 14834663) B14834663
theorem B6593183 : Blo 1925435 6593183 := bstep (se 1 (by rfl) ⟨4944887, by rfl⟩ : syracuseStep 6593183 = 9889775) B9889775
theorem B4395455 : Blo 1925435 4395455 := bstep (se 1 (by rfl) ⟨3296591, by rfl⟩ : syracuseStep 4395455 = 6593183) B6593183
theorem B2930303 : Blo 1925435 2930303 := bstep (se 1 (by rfl) ⟨2197727, by rfl⟩ : syracuseStep 2930303 = 4395455) B4395455
theorem B7814141 : Blo 1925435 7814141 := bstep (se 3 (by rfl) ⟨1465151, by rfl⟩ : syracuseStep 7814141 = 2930303) B2930303
theorem B5209427 : Blo 1925435 5209427 := bstep (se 1 (by rfl) ⟨3907070, by rfl⟩ : syracuseStep 5209427 = 7814141) B7814141
theorem B3472951 : Blo 1925435 3472951 := bstep (se 1 (by rfl) ⟨2604713, by rfl⟩ : syracuseStep 3472951 = 5209427) B5209427
theorem B4630601 : Blo 1925435 4630601 := bstep (se 2 (by rfl) ⟨1736475, by rfl⟩ : syracuseStep 4630601 = 3472951) B3472951
theorem B3087067 : Blo 1925435 3087067 := bstep (se 1 (by rfl) ⟨2315300, by rfl⟩ : syracuseStep 3087067 = 4630601) B4630601
theorem B4116089 : Blo 1925435 4116089 := bstep (se 2 (by rfl) ⟨1543533, by rfl⟩ : syracuseStep 4116089 = 3087067) B3087067
theorem B2744059 : Blo 1925435 2744059 := bstep (se 1 (by rfl) ⟨2058044, by rfl⟩ : syracuseStep 2744059 = 4116089) B4116089
theorem B3658745 : Blo 1925435 3658745 := bstep (se 2 (by rfl) ⟨1372029, by rfl⟩ : syracuseStep 3658745 = 2744059) B2744059
theorem B2439163 : Blo 1925435 2439163 := bstep (se 1 (by rfl) ⟨1829372, by rfl⟩ : syracuseStep 2439163 = 3658745) B3658745
theorem B3252217 : Blo 1925435 3252217 := bstep (se 2 (by rfl) ⟨1219581, by rfl⟩ : syracuseStep 3252217 = 2439163) B2439163
theorem B4336289 : Blo 1925435 4336289 := bstep (se 2 (by rfl) ⟨1626108, by rfl⟩ : syracuseStep 4336289 = 3252217) B3252217
theorem B2890859 : Blo 1925435 2890859 := bstep (se 1 (by rfl) ⟨2168144, by rfl⟩ : syracuseStep 2890859 = 4336289) B4336289
theorem B1927239 : Blo 1925435 1927239 := bstep (se 1 (by rfl) ⟨1445429, by rfl⟩ : syracuseStep 1927239 = 2890859) B2890859
theorem B2168149 : Blo 1925435 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B2890865 : Blo 1925435 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1927243 : Blo 1925435 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B2439173 : Blo 1925435 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B6504461 : Blo 1925435 6504461 := bstep (se 3 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 6504461 = 2439173) B2439173
theorem B4336307 : Blo 1925435 4336307 := bstep (se 1 (by rfl) ⟨3252230, by rfl⟩ : syracuseStep 4336307 = 6504461) B6504461
theorem B2890871 : Blo 1925435 2890871 := bstep (se 1 (by rfl) ⟨2168153, by rfl⟩ : syracuseStep 2890871 = 4336307) B4336307
theorem B1927247 : Blo 1925435 1927247 := bstep (se 1 (by rfl) ⟨1445435, by rfl⟩ : syracuseStep 1927247 = 2890871) B2890871
theorem B2890877 : Blo 1925435 2890877 := bbase (se 3 (by rfl) ⟨542039, by rfl⟩ : syracuseStep 2890877 = 1084079) (by norm_num)
theorem B1927251 : Blo 1925435 1927251 := bstep (se 1 (by rfl) ⟨1445438, by rfl⟩ : syracuseStep 1927251 = 2890877) B2890877
theorem B4336325 : Blo 1925435 4336325 := bbase (se 4 (by rfl) ⟨406530, by rfl⟩ : syracuseStep 4336325 = 813061) (by norm_num)
theorem B2890883 : Blo 1925435 2890883 := bstep (se 1 (by rfl) ⟨2168162, by rfl⟩ : syracuseStep 2890883 = 4336325) B4336325
theorem B1927255 : Blo 1925435 1927255 := bstep (se 1 (by rfl) ⟨1445441, by rfl⟩ : syracuseStep 1927255 = 2890883) B2890883
theorem B35163989 : Blo 1925435 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B23442659 : Blo 1925435 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B15628439 : Blo 1925435 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B10418959 : Blo 1925435 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B13891945 : Blo 1925435 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B18522593 : Blo 1925435 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B12348395 : Blo 1925435 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B8232263 : Blo 1925435 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B5488175 : Blo 1925435 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B3658783 : Blo 1925435 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B4878377 : Blo 1925435 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B3252251 : Blo 1925435 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B2168167 : Blo 1925435 2168167 := bstep (se 1 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 2168167 = 3252251) B3252251
theorem B2890889 : Blo 1925435 2890889 := bstep (se 2 (by rfl) ⟨1084083, by rfl⟩ : syracuseStep 2890889 = 2168167) B2168167
theorem B1927259 : Blo 1925435 1927259 := bstep (se 1 (by rfl) ⟨1445444, by rfl⟩ : syracuseStep 1927259 = 2890889) B2890889
theorem B9756773 : Blo 1925435 9756773 := bbase (se 4 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 9756773 = 1829395) (by norm_num)
theorem B6504515 : Blo 1925435 6504515 := bstep (se 1 (by rfl) ⟨4878386, by rfl⟩ : syracuseStep 6504515 = 9756773) B9756773
theorem B4336343 : Blo 1925435 4336343 := bstep (se 1 (by rfl) ⟨3252257, by rfl⟩ : syracuseStep 4336343 = 6504515) B6504515
theorem B2890895 : Blo 1925435 2890895 := bstep (se 1 (by rfl) ⟨2168171, by rfl⟩ : syracuseStep 2890895 = 4336343) B4336343
theorem B1927263 : Blo 1925435 1927263 := bstep (se 1 (by rfl) ⟨1445447, by rfl⟩ : syracuseStep 1927263 = 2890895) B2890895
theorem B2890901 : Blo 1925435 2890901 := bbase (se 6 (by rfl) ⟨67755, by rfl⟩ : syracuseStep 2890901 = 135511) (by norm_num)
theorem B1927267 : Blo 1925435 1927267 := bstep (se 1 (by rfl) ⟨1445450, by rfl⟩ : syracuseStep 1927267 = 2890901) B2890901
theorem B3708725 : Blo 1925435 3708725 := bbase (se 5 (by rfl) ⟨173846, by rfl⟩ : syracuseStep 3708725 = 347693) (by norm_num)
theorem B9889933 : Blo 1925435 9889933 := bstep (se 3 (by rfl) ⟨1854362, by rfl⟩ : syracuseStep 9889933 = 3708725) B3708725
theorem B13186577 : Blo 1925435 13186577 := bstep (se 2 (by rfl) ⟨4944966, by rfl⟩ : syracuseStep 13186577 = 9889933) B9889933
theorem B35164205 : Blo 1925435 35164205 := bstep (se 3 (by rfl) ⟨6593288, by rfl⟩ : syracuseStep 35164205 = 13186577) B13186577
theorem B23442803 : Blo 1925435 23442803 := bstep (se 1 (by rfl) ⟨17582102, by rfl⟩ : syracuseStep 23442803 = 35164205) B35164205
theorem B15628535 : Blo 1925435 15628535 := bstep (se 1 (by rfl) ⟨11721401, by rfl⟩ : syracuseStep 15628535 = 23442803) B23442803
theorem B10419023 : Blo 1925435 10419023 := bstep (se 1 (by rfl) ⟨7814267, by rfl⟩ : syracuseStep 10419023 = 15628535) B15628535
theorem B6946015 : Blo 1925435 6946015 := bstep (se 1 (by rfl) ⟨5209511, by rfl⟩ : syracuseStep 6946015 = 10419023) B10419023
theorem B9261353 : Blo 1925435 9261353 := bstep (se 2 (by rfl) ⟨3473007, by rfl⟩ : syracuseStep 9261353 = 6946015) B6946015
theorem B6174235 : Blo 1925435 6174235 := bstep (se 1 (by rfl) ⟨4630676, by rfl⟩ : syracuseStep 6174235 = 9261353) B9261353
theorem B8232313 : Blo 1925435 8232313 := bstep (se 2 (by rfl) ⟨3087117, by rfl⟩ : syracuseStep 8232313 = 6174235) B6174235
theorem B10976417 : Blo 1925435 10976417 := bstep (se 2 (by rfl) ⟨4116156, by rfl⟩ : syracuseStep 10976417 = 8232313) B8232313
theorem B7317611 : Blo 1925435 7317611 := bstep (se 1 (by rfl) ⟨5488208, by rfl⟩ : syracuseStep 7317611 = 10976417) B10976417
theorem B4878407 : Blo 1925435 4878407 := bstep (se 1 (by rfl) ⟨3658805, by rfl⟩ : syracuseStep 4878407 = 7317611) B7317611
theorem B3252271 : Blo 1925435 3252271 := bstep (se 1 (by rfl) ⟨2439203, by rfl⟩ : syracuseStep 3252271 = 4878407) B4878407
theorem B4336361 : Blo 1925435 4336361 := bstep (se 2 (by rfl) ⟨1626135, by rfl⟩ : syracuseStep 4336361 = 3252271) B3252271
theorem B2890907 : Blo 1925435 2890907 := bstep (se 1 (by rfl) ⟨2168180, by rfl⟩ : syracuseStep 2890907 = 4336361) B4336361
theorem B1927271 : Blo 1925435 1927271 := bstep (se 1 (by rfl) ⟨1445453, by rfl⟩ : syracuseStep 1927271 = 2890907) B2890907
theorem B2168185 : Blo 1925435 2168185 := bbase (se 2 (by rfl) ⟨813069, by rfl⟩ : syracuseStep 2168185 = 1626139) (by norm_num)
theorem B2890913 : Blo 1925435 2890913 := bstep (se 2 (by rfl) ⟨1084092, by rfl⟩ : syracuseStep 2890913 = 2168185) B2168185
theorem B1927275 : Blo 1925435 1927275 := bstep (se 1 (by rfl) ⟨1445456, by rfl⟩ : syracuseStep 1927275 = 2890913) B2890913
theorem B9387749 : Blo 1925435 9387749 := bbase (se 4 (by rfl) ⟨880101, by rfl⟩ : syracuseStep 9387749 = 1760203) (by norm_num)
theorem B25033997 : Blo 1925435 25033997 := bstep (se 3 (by rfl) ⟨4693874, by rfl⟩ : syracuseStep 25033997 = 9387749) B9387749
theorem B16689331 : Blo 1925435 16689331 := bstep (se 1 (by rfl) ⟨12516998, by rfl⟩ : syracuseStep 16689331 = 25033997) B25033997
theorem B22252441 : Blo 1925435 22252441 := bstep (se 2 (by rfl) ⟨8344665, by rfl⟩ : syracuseStep 22252441 = 16689331) B16689331
theorem B29669921 : Blo 1925435 29669921 := bstep (se 2 (by rfl) ⟨11126220, by rfl⟩ : syracuseStep 29669921 = 22252441) B22252441
theorem B19779947 : Blo 1925435 19779947 := bstep (se 1 (by rfl) ⟨14834960, by rfl⟩ : syracuseStep 19779947 = 29669921) B29669921
theorem B13186631 : Blo 1925435 13186631 := bstep (se 1 (by rfl) ⟨9889973, by rfl⟩ : syracuseStep 13186631 = 19779947) B19779947
theorem B8791087 : Blo 1925435 8791087 := bstep (se 1 (by rfl) ⟨6593315, by rfl⟩ : syracuseStep 8791087 = 13186631) B13186631
theorem B11721449 : Blo 1925435 11721449 := bstep (se 2 (by rfl) ⟨4395543, by rfl⟩ : syracuseStep 11721449 = 8791087) B8791087
theorem B31257197 : Blo 1925435 31257197 := bstep (se 3 (by rfl) ⟨5860724, by rfl⟩ : syracuseStep 31257197 = 11721449) B11721449
theorem B20838131 : Blo 1925435 20838131 := bstep (se 1 (by rfl) ⟨15628598, by rfl⟩ : syracuseStep 20838131 = 31257197) B31257197
theorem B13892087 : Blo 1925435 13892087 := bstep (se 1 (by rfl) ⟨10419065, by rfl⟩ : syracuseStep 13892087 = 20838131) B20838131
theorem B9261391 : Blo 1925435 9261391 := bstep (se 1 (by rfl) ⟨6946043, by rfl⟩ : syracuseStep 9261391 = 13892087) B13892087
theorem B12348521 : Blo 1925435 12348521 := bstep (se 2 (by rfl) ⟨4630695, by rfl⟩ : syracuseStep 12348521 = 9261391) B9261391
theorem B8232347 : Blo 1925435 8232347 := bstep (se 1 (by rfl) ⟨6174260, by rfl⟩ : syracuseStep 8232347 = 12348521) B12348521
theorem B5488231 : Blo 1925435 5488231 := bstep (se 1 (by rfl) ⟨4116173, by rfl⟩ : syracuseStep 5488231 = 8232347) B8232347
theorem B7317641 : Blo 1925435 7317641 := bstep (se 2 (by rfl) ⟨2744115, by rfl⟩ : syracuseStep 7317641 = 5488231) B5488231
theorem B4878427 : Blo 1925435 4878427 := bstep (se 1 (by rfl) ⟨3658820, by rfl⟩ : syracuseStep 4878427 = 7317641) B7317641
theorem B6504569 : Blo 1925435 6504569 := bstep (se 2 (by rfl) ⟨2439213, by rfl⟩ : syracuseStep 6504569 = 4878427) B4878427
theorem B4336379 : Blo 1925435 4336379 := bstep (se 1 (by rfl) ⟨3252284, by rfl⟩ : syracuseStep 4336379 = 6504569) B6504569
theorem B2890919 : Blo 1925435 2890919 := bstep (se 1 (by rfl) ⟨2168189, by rfl⟩ : syracuseStep 2890919 = 4336379) B4336379
theorem B1927279 : Blo 1925435 1927279 := bstep (se 1 (by rfl) ⟨1445459, by rfl⟩ : syracuseStep 1927279 = 2890919) B2890919
theorem B2890925 : Blo 1925435 2890925 := bbase (se 3 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 2890925 = 1084097) (by norm_num)
theorem B1927283 : Blo 1925435 1927283 := bstep (se 1 (by rfl) ⟨1445462, by rfl⟩ : syracuseStep 1927283 = 2890925) B2890925
theorem B4336397 : Blo 1925435 4336397 := bbase (se 3 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 4336397 = 1626149) (by norm_num)
theorem B2890931 : Blo 1925435 2890931 := bstep (se 1 (by rfl) ⟨2168198, by rfl⟩ : syracuseStep 2890931 = 4336397) B4336397
theorem B1927287 : Blo 1925435 1927287 := bstep (se 1 (by rfl) ⟨1445465, by rfl⟩ : syracuseStep 1927287 = 2890931) B2890931
theorem B2439229 : Blo 1925435 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B3252305 : Blo 1925435 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B2168203 : Blo 1925435 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B2890937 : Blo 1925435 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B1927291 : Blo 1925435 1927291 := bstep (se 1 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 1927291 = 2890937) B2890937
theorem B7417541 : Blo 1925435 7417541 := bbase (se 4 (by rfl) ⟨695394, by rfl⟩ : syracuseStep 7417541 = 1390789) (by norm_num)
theorem B19780109 : Blo 1925435 19780109 := bstep (se 3 (by rfl) ⟨3708770, by rfl⟩ : syracuseStep 19780109 = 7417541) B7417541
theorem B13186739 : Blo 1925435 13186739 := bstep (se 1 (by rfl) ⟨9890054, by rfl⟩ : syracuseStep 13186739 = 19780109) B19780109
theorem B35164637 : Blo 1925435 35164637 := bstep (se 3 (by rfl) ⟨6593369, by rfl⟩ : syracuseStep 35164637 = 13186739) B13186739
theorem B23443091 : Blo 1925435 23443091 := bstep (se 1 (by rfl) ⟨17582318, by rfl⟩ : syracuseStep 23443091 = 35164637) B35164637
theorem B15628727 : Blo 1925435 15628727 := bstep (se 1 (by rfl) ⟨11721545, by rfl⟩ : syracuseStep 15628727 = 23443091) B23443091
theorem B10419151 : Blo 1925435 10419151 := bstep (se 1 (by rfl) ⟨7814363, by rfl⟩ : syracuseStep 10419151 = 15628727) B15628727
theorem B13892201 : Blo 1925435 13892201 := bstep (se 2 (by rfl) ⟨5209575, by rfl⟩ : syracuseStep 13892201 = 10419151) B10419151
theorem B9261467 : Blo 1925435 9261467 := bstep (se 1 (by rfl) ⟨6946100, by rfl⟩ : syracuseStep 9261467 = 13892201) B13892201
theorem B6174311 : Blo 1925435 6174311 := bstep (se 1 (by rfl) ⟨4630733, by rfl⟩ : syracuseStep 6174311 = 9261467) B9261467
theorem B16464829 : Blo 1925435 16464829 := bstep (se 3 (by rfl) ⟨3087155, by rfl⟩ : syracuseStep 16464829 = 6174311) B6174311
theorem B21953105 : Blo 1925435 21953105 := bstep (se 2 (by rfl) ⟨8232414, by rfl⟩ : syracuseStep 21953105 = 16464829) B16464829
theorem B14635403 : Blo 1925435 14635403 := bstep (se 1 (by rfl) ⟨10976552, by rfl⟩ : syracuseStep 14635403 = 21953105) B21953105
theorem B9756935 : Blo 1925435 9756935 := bstep (se 1 (by rfl) ⟨7317701, by rfl⟩ : syracuseStep 9756935 = 14635403) B14635403
theorem B6504623 : Blo 1925435 6504623 := bstep (se 1 (by rfl) ⟨4878467, by rfl⟩ : syracuseStep 6504623 = 9756935) B9756935
theorem B4336415 : Blo 1925435 4336415 := bstep (se 1 (by rfl) ⟨3252311, by rfl⟩ : syracuseStep 4336415 = 6504623) B6504623
theorem B2890943 : Blo 1925435 2890943 := bstep (se 1 (by rfl) ⟨2168207, by rfl⟩ : syracuseStep 2890943 = 4336415) B4336415
theorem B1927295 : Blo 1925435 1927295 := bstep (se 1 (by rfl) ⟨1445471, by rfl⟩ : syracuseStep 1927295 = 2890943) B2890943
theorem B2890949 : Blo 1925435 2890949 := bbase (se 4 (by rfl) ⟨271026, by rfl⟩ : syracuseStep 2890949 = 542053) (by norm_num)
theorem B1927299 : Blo 1925435 1927299 := bstep (se 1 (by rfl) ⟨1445474, by rfl⟩ : syracuseStep 1927299 = 2890949) B2890949
theorem B3252325 : Blo 1925435 3252325 := bbase (se 4 (by rfl) ⟨304905, by rfl⟩ : syracuseStep 3252325 = 609811) (by norm_num)
theorem B4336433 : Blo 1925435 4336433 := bstep (se 2 (by rfl) ⟨1626162, by rfl⟩ : syracuseStep 4336433 = 3252325) B3252325
theorem B2890955 : Blo 1925435 2890955 := bstep (se 1 (by rfl) ⟨2168216, by rfl⟩ : syracuseStep 2890955 = 4336433) B4336433
theorem B1927303 : Blo 1925435 1927303 := bstep (se 1 (by rfl) ⟨1445477, by rfl⟩ : syracuseStep 1927303 = 2890955) B2890955
theorem B2168221 : Blo 1925435 2168221 := bbase (se 3 (by rfl) ⟨406541, by rfl⟩ : syracuseStep 2168221 = 813083) (by norm_num)
theorem B2890961 : Blo 1925435 2890961 := bstep (se 2 (by rfl) ⟨1084110, by rfl⟩ : syracuseStep 2890961 = 2168221) B2168221
theorem B1927307 : Blo 1925435 1927307 := bstep (se 1 (by rfl) ⟨1445480, by rfl⟩ : syracuseStep 1927307 = 2890961) B2890961
theorem B6504677 : Blo 1925435 6504677 := bbase (se 4 (by rfl) ⟨609813, by rfl⟩ : syracuseStep 6504677 = 1219627) (by norm_num)
theorem B4336451 : Blo 1925435 4336451 := bstep (se 1 (by rfl) ⟨3252338, by rfl⟩ : syracuseStep 4336451 = 6504677) B6504677
theorem B2890967 : Blo 1925435 2890967 := bstep (se 1 (by rfl) ⟨2168225, by rfl⟩ : syracuseStep 2890967 = 4336451) B4336451
theorem B1927311 : Blo 1925435 1927311 := bstep (se 1 (by rfl) ⟨1445483, by rfl⟩ : syracuseStep 1927311 = 2890967) B2890967
theorem B2890973 : Blo 1925435 2890973 := bbase (se 3 (by rfl) ⟨542057, by rfl⟩ : syracuseStep 2890973 = 1084115) (by norm_num)
theorem B1927315 : Blo 1925435 1927315 := bstep (se 1 (by rfl) ⟨1445486, by rfl⟩ : syracuseStep 1927315 = 2890973) B2890973
theorem B4336469 : Blo 1925435 4336469 := bbase (se 9 (by rfl) ⟨12704, by rfl⟩ : syracuseStep 4336469 = 25409) (by norm_num)
theorem B2890979 : Blo 1925435 2890979 := bstep (se 1 (by rfl) ⟨2168234, by rfl⟩ : syracuseStep 2890979 = 4336469) B4336469
theorem B1927319 : Blo 1925435 1927319 := bstep (se 1 (by rfl) ⟨1445489, by rfl⟩ : syracuseStep 1927319 = 2890979) B2890979
theorem B5488357 : Blo 1925435 5488357 := bbase (se 4 (by rfl) ⟨514533, by rfl⟩ : syracuseStep 5488357 = 1029067) (by norm_num)
theorem B7317809 : Blo 1925435 7317809 := bstep (se 2 (by rfl) ⟨2744178, by rfl⟩ : syracuseStep 7317809 = 5488357) B5488357
theorem B4878539 : Blo 1925435 4878539 := bstep (se 1 (by rfl) ⟨3658904, by rfl⟩ : syracuseStep 4878539 = 7317809) B7317809
theorem B3252359 : Blo 1925435 3252359 := bstep (se 1 (by rfl) ⟨2439269, by rfl⟩ : syracuseStep 3252359 = 4878539) B4878539
theorem B2168239 : Blo 1925435 2168239 := bstep (se 1 (by rfl) ⟨1626179, by rfl⟩ : syracuseStep 2168239 = 3252359) B3252359
theorem B2890985 : Blo 1925435 2890985 := bstep (se 2 (by rfl) ⟨1084119, by rfl⟩ : syracuseStep 2890985 = 2168239) B2168239
theorem B1927323 : Blo 1925435 1927323 := bstep (se 1 (by rfl) ⟨1445492, by rfl⟩ : syracuseStep 1927323 = 2890985) B2890985
theorem B4945109 : Blo 1925435 4945109 := bbase (se 7 (by rfl) ⟨57950, by rfl⟩ : syracuseStep 4945109 = 115901) (by norm_num)
theorem B13186957 : Blo 1925435 13186957 := bstep (se 3 (by rfl) ⟨2472554, by rfl⟩ : syracuseStep 13186957 = 4945109) B4945109
theorem B17582609 : Blo 1925435 17582609 := bstep (se 2 (by rfl) ⟨6593478, by rfl⟩ : syracuseStep 17582609 = 13186957) B13186957
theorem B46886957 : Blo 1925435 46886957 := bstep (se 3 (by rfl) ⟨8791304, by rfl⟩ : syracuseStep 46886957 = 17582609) B17582609
theorem B31257971 : Blo 1925435 31257971 := bstep (se 1 (by rfl) ⟨23443478, by rfl⟩ : syracuseStep 31257971 = 46886957) B46886957
theorem B20838647 : Blo 1925435 20838647 := bstep (se 1 (by rfl) ⟨15628985, by rfl⟩ : syracuseStep 20838647 = 31257971) B31257971
theorem B55569725 : Blo 1925435 55569725 := bstep (se 3 (by rfl) ⟨10419323, by rfl⟩ : syracuseStep 55569725 = 20838647) B20838647
theorem B37046483 : Blo 1925435 37046483 := bstep (se 1 (by rfl) ⟨27784862, by rfl⟩ : syracuseStep 37046483 = 55569725) B55569725
theorem B24697655 : Blo 1925435 24697655 := bstep (se 1 (by rfl) ⟨18523241, by rfl⟩ : syracuseStep 24697655 = 37046483) B37046483
theorem B16465103 : Blo 1925435 16465103 := bstep (se 1 (by rfl) ⟨12348827, by rfl⟩ : syracuseStep 16465103 = 24697655) B24697655
theorem B10976735 : Blo 1925435 10976735 := bstep (se 1 (by rfl) ⟨8232551, by rfl⟩ : syracuseStep 10976735 = 16465103) B16465103
theorem B7317823 : Blo 1925435 7317823 := bstep (se 1 (by rfl) ⟨5488367, by rfl⟩ : syracuseStep 7317823 = 10976735) B10976735
theorem B9757097 : Blo 1925435 9757097 := bstep (se 2 (by rfl) ⟨3658911, by rfl⟩ : syracuseStep 9757097 = 7317823) B7317823
theorem B6504731 : Blo 1925435 6504731 := bstep (se 1 (by rfl) ⟨4878548, by rfl⟩ : syracuseStep 6504731 = 9757097) B9757097
theorem B4336487 : Blo 1925435 4336487 := bstep (se 1 (by rfl) ⟨3252365, by rfl⟩ : syracuseStep 4336487 = 6504731) B6504731
theorem B2890991 : Blo 1925435 2890991 := bstep (se 1 (by rfl) ⟨2168243, by rfl⟩ : syracuseStep 2890991 = 4336487) B4336487
theorem B1927327 : Blo 1925435 1927327 := bstep (se 1 (by rfl) ⟨1445495, by rfl⟩ : syracuseStep 1927327 = 2890991) B2890991
theorem B2890997 : Blo 1925435 2890997 := bbase (se 5 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 2890997 = 271031) (by norm_num)
theorem B1927331 : Blo 1925435 1927331 := bstep (se 1 (by rfl) ⟨1445498, by rfl⟩ : syracuseStep 1927331 = 2890997) B2890997
theorem B5209685 : Blo 1925435 5209685 := bbase (se 8 (by rfl) ⟨30525, by rfl⟩ : syracuseStep 5209685 = 61051) (by norm_num)
theorem B3473123 : Blo 1925435 3473123 := bstep (se 1 (by rfl) ⟨2604842, by rfl⟩ : syracuseStep 3473123 = 5209685) B5209685
theorem B9261661 : Blo 1925435 9261661 := bstep (se 3 (by rfl) ⟨1736561, by rfl⟩ : syracuseStep 9261661 = 3473123) B3473123
theorem B12348881 : Blo 1925435 12348881 := bstep (se 2 (by rfl) ⟨4630830, by rfl⟩ : syracuseStep 12348881 = 9261661) B9261661
theorem B8232587 : Blo 1925435 8232587 := bstep (se 1 (by rfl) ⟨6174440, by rfl⟩ : syracuseStep 8232587 = 12348881) B12348881
theorem B5488391 : Blo 1925435 5488391 := bstep (se 1 (by rfl) ⟨4116293, by rfl⟩ : syracuseStep 5488391 = 8232587) B8232587
theorem B3658927 : Blo 1925435 3658927 := bstep (se 1 (by rfl) ⟨2744195, by rfl⟩ : syracuseStep 3658927 = 5488391) B5488391
theorem B4878569 : Blo 1925435 4878569 := bstep (se 2 (by rfl) ⟨1829463, by rfl⟩ : syracuseStep 4878569 = 3658927) B3658927
theorem B3252379 : Blo 1925435 3252379 := bstep (se 1 (by rfl) ⟨2439284, by rfl⟩ : syracuseStep 3252379 = 4878569) B4878569
theorem B4336505 : Blo 1925435 4336505 := bstep (se 2 (by rfl) ⟨1626189, by rfl⟩ : syracuseStep 4336505 = 3252379) B3252379
theorem B2891003 : Blo 1925435 2891003 := bstep (se 1 (by rfl) ⟨2168252, by rfl⟩ : syracuseStep 2891003 = 4336505) B4336505
theorem B1927335 : Blo 1925435 1927335 := bstep (se 1 (by rfl) ⟨1445501, by rfl⟩ : syracuseStep 1927335 = 2891003) B2891003
theorem B2168257 : Blo 1925435 2168257 := bbase (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) (by norm_num)
theorem B2891009 : Blo 1925435 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1927339 : Blo 1925435 1927339 := bstep (se 1 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 1927339 = 2891009) B2891009
theorem B4878589 : Blo 1925435 4878589 := bbase (se 3 (by rfl) ⟨914735, by rfl⟩ : syracuseStep 4878589 = 1829471) (by norm_num)
theorem B6504785 : Blo 1925435 6504785 := bstep (se 2 (by rfl) ⟨2439294, by rfl⟩ : syracuseStep 6504785 = 4878589) B4878589
theorem B4336523 : Blo 1925435 4336523 := bstep (se 1 (by rfl) ⟨3252392, by rfl⟩ : syracuseStep 4336523 = 6504785) B6504785
theorem B2891015 : Blo 1925435 2891015 := bstep (se 1 (by rfl) ⟨2168261, by rfl⟩ : syracuseStep 2891015 = 4336523) B4336523
theorem B1927343 : Blo 1925435 1927343 := bstep (se 1 (by rfl) ⟨1445507, by rfl⟩ : syracuseStep 1927343 = 2891015) B2891015
theorem B2891021 : Blo 1925435 2891021 := bbase (se 3 (by rfl) ⟨542066, by rfl⟩ : syracuseStep 2891021 = 1084133) (by norm_num)
theorem B1927347 : Blo 1925435 1927347 := bstep (se 1 (by rfl) ⟨1445510, by rfl⟩ : syracuseStep 1927347 = 2891021) B2891021
theorem B4336541 : Blo 1925435 4336541 := bbase (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) (by norm_num)
theorem B2891027 : Blo 1925435 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B1927351 : Blo 1925435 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B3252413 : Blo 1925435 3252413 := bbase (se 3 (by rfl) ⟨609827, by rfl⟩ : syracuseStep 3252413 = 1219655) (by norm_num)
theorem B2168275 : Blo 1925435 2168275 := bstep (se 1 (by rfl) ⟨1626206, by rfl⟩ : syracuseStep 2168275 = 3252413) B3252413
theorem B2891033 : Blo 1925435 2891033 := bstep (se 2 (by rfl) ⟨1084137, by rfl⟩ : syracuseStep 2891033 = 2168275) B2168275
theorem B1927355 : Blo 1925435 1927355 := bstep (se 1 (by rfl) ⟨1445516, by rfl⟩ : syracuseStep 1927355 = 2891033) B2891033
theorem B10976917 : Blo 1925435 10976917 := bbase (se 6 (by rfl) ⟨257271, by rfl⟩ : syracuseStep 10976917 = 514543) (by norm_num)
theorem B14635889 : Blo 1925435 14635889 := bstep (se 2 (by rfl) ⟨5488458, by rfl⟩ : syracuseStep 14635889 = 10976917) B10976917
theorem B9757259 : Blo 1925435 9757259 := bstep (se 1 (by rfl) ⟨7317944, by rfl⟩ : syracuseStep 9757259 = 14635889) B14635889
theorem B6504839 : Blo 1925435 6504839 := bstep (se 1 (by rfl) ⟨4878629, by rfl⟩ : syracuseStep 6504839 = 9757259) B9757259
theorem B4336559 : Blo 1925435 4336559 := bstep (se 1 (by rfl) ⟨3252419, by rfl⟩ : syracuseStep 4336559 = 6504839) B6504839
theorem B2891039 : Blo 1925435 2891039 := bstep (se 1 (by rfl) ⟨2168279, by rfl⟩ : syracuseStep 2891039 = 4336559) B4336559
theorem B1927359 : Blo 1925435 1927359 := bstep (se 1 (by rfl) ⟨1445519, by rfl⟩ : syracuseStep 1927359 = 2891039) B2891039
theorem B2891045 : Blo 1925435 2891045 := bbase (se 4 (by rfl) ⟨271035, by rfl⟩ : syracuseStep 2891045 = 542071) (by norm_num)
theorem B1927363 : Blo 1925435 1927363 := bstep (se 1 (by rfl) ⟨1445522, by rfl⟩ : syracuseStep 1927363 = 2891045) B2891045
theorem B2439325 : Blo 1925435 2439325 := bbase (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) (by norm_num)
theorem B3252433 : Blo 1925435 3252433 := bstep (se 2 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 3252433 = 2439325) B2439325
theorem B4336577 : Blo 1925435 4336577 := bstep (se 2 (by rfl) ⟨1626216, by rfl⟩ : syracuseStep 4336577 = 3252433) B3252433
theorem B2891051 : Blo 1925435 2891051 := bstep (se 1 (by rfl) ⟨2168288, by rfl⟩ : syracuseStep 2891051 = 4336577) B4336577
theorem B1927367 : Blo 1925435 1927367 := bstep (se 1 (by rfl) ⟨1445525, by rfl⟩ : syracuseStep 1927367 = 2891051) B2891051
theorem B2168293 : Blo 1925435 2168293 := bbase (se 4 (by rfl) ⟨203277, by rfl⟩ : syracuseStep 2168293 = 406555) (by norm_num)
theorem B2891057 : Blo 1925435 2891057 := bstep (se 2 (by rfl) ⟨1084146, by rfl⟩ : syracuseStep 2891057 = 2168293) B2168293
theorem B1927371 : Blo 1925435 1927371 := bstep (se 1 (by rfl) ⟨1445528, by rfl⟩ : syracuseStep 1927371 = 2891057) B2891057
theorem B2930509 : Blo 1925435 2930509 := bbase (se 3 (by rfl) ⟨549470, by rfl⟩ : syracuseStep 2930509 = 1098941) (by norm_num)
theorem B15629381 : Blo 1925435 15629381 := bstep (se 4 (by rfl) ⟨1465254, by rfl⟩ : syracuseStep 15629381 = 2930509) B2930509
theorem B10419587 : Blo 1925435 10419587 := bstep (se 1 (by rfl) ⟨7814690, by rfl⟩ : syracuseStep 10419587 = 15629381) B15629381
theorem B6946391 : Blo 1925435 6946391 := bstep (se 1 (by rfl) ⟨5209793, by rfl⟩ : syracuseStep 6946391 = 10419587) B10419587
theorem B4630927 : Blo 1925435 4630927 := bstep (se 1 (by rfl) ⟨3473195, by rfl⟩ : syracuseStep 4630927 = 6946391) B6946391
theorem B6174569 : Blo 1925435 6174569 := bstep (se 2 (by rfl) ⟨2315463, by rfl⟩ : syracuseStep 6174569 = 4630927) B4630927
theorem B4116379 : Blo 1925435 4116379 := bstep (se 1 (by rfl) ⟨3087284, by rfl⟩ : syracuseStep 4116379 = 6174569) B6174569
theorem B5488505 : Blo 1925435 5488505 := bstep (se 2 (by rfl) ⟨2058189, by rfl⟩ : syracuseStep 5488505 = 4116379) B4116379
theorem B3659003 : Blo 1925435 3659003 := bstep (se 1 (by rfl) ⟨2744252, by rfl⟩ : syracuseStep 3659003 = 5488505) B5488505
theorem B2439335 : Blo 1925435 2439335 := bstep (se 1 (by rfl) ⟨1829501, by rfl⟩ : syracuseStep 2439335 = 3659003) B3659003
theorem B6504893 : Blo 1925435 6504893 := bstep (se 3 (by rfl) ⟨1219667, by rfl⟩ : syracuseStep 6504893 = 2439335) B2439335
theorem B4336595 : Blo 1925435 4336595 := bstep (se 1 (by rfl) ⟨3252446, by rfl⟩ : syracuseStep 4336595 = 6504893) B6504893
theorem B2891063 : Blo 1925435 2891063 := bstep (se 1 (by rfl) ⟨2168297, by rfl⟩ : syracuseStep 2891063 = 4336595) B4336595
theorem B1927375 : Blo 1925435 1927375 := bstep (se 1 (by rfl) ⟨1445531, by rfl⟩ : syracuseStep 1927375 = 2891063) B2891063
theorem B2891069 : Blo 1925435 2891069 := bbase (se 3 (by rfl) ⟨542075, by rfl⟩ : syracuseStep 2891069 = 1084151) (by norm_num)
theorem B1927379 : Blo 1925435 1927379 := bstep (se 1 (by rfl) ⟨1445534, by rfl⟩ : syracuseStep 1927379 = 2891069) B2891069
theorem B4336613 : Blo 1925435 4336613 := bbase (se 4 (by rfl) ⟨406557, by rfl⟩ : syracuseStep 4336613 = 813115) (by norm_num)
theorem B2891075 : Blo 1925435 2891075 := bstep (se 1 (by rfl) ⟨2168306, by rfl⟩ : syracuseStep 2891075 = 4336613) B4336613
theorem B1927383 : Blo 1925435 1927383 := bstep (se 1 (by rfl) ⟨1445537, by rfl⟩ : syracuseStep 1927383 = 2891075) B2891075
theorem B4878701 : Blo 1925435 4878701 := bbase (se 3 (by rfl) ⟨914756, by rfl⟩ : syracuseStep 4878701 = 1829513) (by norm_num)
theorem B3252467 : Blo 1925435 3252467 := bstep (se 1 (by rfl) ⟨2439350, by rfl⟩ : syracuseStep 3252467 = 4878701) B4878701
theorem B2168311 : Blo 1925435 2168311 := bstep (se 1 (by rfl) ⟨1626233, by rfl⟩ : syracuseStep 2168311 = 3252467) B3252467
theorem B2891081 : Blo 1925435 2891081 := bstep (se 2 (by rfl) ⟨1084155, by rfl⟩ : syracuseStep 2891081 = 2168311) B2168311
theorem B1927387 : Blo 1925435 1927387 := bstep (se 1 (by rfl) ⟨1445540, by rfl⟩ : syracuseStep 1927387 = 2891081) B2891081
theorem B4116413 : Blo 1925435 4116413 := bbase (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) (by norm_num)
theorem B2744275 : Blo 1925435 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B3659033 : Blo 1925435 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B9757421 : Blo 1925435 9757421 := bstep (se 3 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 9757421 = 3659033) B3659033
theorem B6504947 : Blo 1925435 6504947 := bstep (se 1 (by rfl) ⟨4878710, by rfl⟩ : syracuseStep 6504947 = 9757421) B9757421
theorem B4336631 : Blo 1925435 4336631 := bstep (se 1 (by rfl) ⟨3252473, by rfl⟩ : syracuseStep 4336631 = 6504947) B6504947
theorem B2891087 : Blo 1925435 2891087 := bstep (se 1 (by rfl) ⟨2168315, by rfl⟩ : syracuseStep 2891087 = 4336631) B4336631
theorem B1927391 : Blo 1925435 1927391 := bstep (se 1 (by rfl) ⟨1445543, by rfl⟩ : syracuseStep 1927391 = 2891087) B2891087
theorem B2891093 : Blo 1925435 2891093 := bbase (se 11 (by rfl) ⟨2117, by rfl⟩ : syracuseStep 2891093 = 4235) (by norm_num)
theorem B1927395 : Blo 1925435 1927395 := bstep (se 1 (by rfl) ⟨1445546, by rfl⟩ : syracuseStep 1927395 = 2891093) B2891093
theorem B7814789 : Blo 1925435 7814789 := bbase (se 4 (by rfl) ⟨732636, by rfl⟩ : syracuseStep 7814789 = 1465273) (by norm_num)
theorem B5209859 : Blo 1925435 5209859 := bstep (se 1 (by rfl) ⟨3907394, by rfl⟩ : syracuseStep 5209859 = 7814789) B7814789
theorem B3473239 : Blo 1925435 3473239 := bstep (se 1 (by rfl) ⟨2604929, by rfl⟩ : syracuseStep 3473239 = 5209859) B5209859
theorem B4630985 : Blo 1925435 4630985 := bstep (se 2 (by rfl) ⟨1736619, by rfl⟩ : syracuseStep 4630985 = 3473239) B3473239
theorem B3087323 : Blo 1925435 3087323 := bstep (se 1 (by rfl) ⟨2315492, by rfl⟩ : syracuseStep 3087323 = 4630985) B4630985
theorem B2058215 : Blo 1925435 2058215 := bstep (se 1 (by rfl) ⟨1543661, by rfl⟩ : syracuseStep 2058215 = 3087323) B3087323
theorem B5488573 : Blo 1925435 5488573 := bstep (se 3 (by rfl) ⟨1029107, by rfl⟩ : syracuseStep 5488573 = 2058215) B2058215
theorem B7318097 : Blo 1925435 7318097 := bstep (se 2 (by rfl) ⟨2744286, by rfl⟩ : syracuseStep 7318097 = 5488573) B5488573
theorem B4878731 : Blo 1925435 4878731 := bstep (se 1 (by rfl) ⟨3659048, by rfl⟩ : syracuseStep 4878731 = 7318097) B7318097
theorem B3252487 : Blo 1925435 3252487 := bstep (se 1 (by rfl) ⟨2439365, by rfl⟩ : syracuseStep 3252487 = 4878731) B4878731
theorem B4336649 : Blo 1925435 4336649 := bstep (se 2 (by rfl) ⟨1626243, by rfl⟩ : syracuseStep 4336649 = 3252487) B3252487
theorem B2891099 : Blo 1925435 2891099 := bstep (se 1 (by rfl) ⟨2168324, by rfl⟩ : syracuseStep 2891099 = 4336649) B4336649
theorem B1927399 : Blo 1925435 1927399 := bstep (se 1 (by rfl) ⟨1445549, by rfl⟩ : syracuseStep 1927399 = 2891099) B2891099
theorem B2168329 : Blo 1925435 2168329 := bbase (se 2 (by rfl) ⟨813123, by rfl⟩ : syracuseStep 2168329 = 1626247) (by norm_num)
theorem B2891105 : Blo 1925435 2891105 := bstep (se 2 (by rfl) ⟨1084164, by rfl⟩ : syracuseStep 2891105 = 2168329) B2168329
theorem B1927403 : Blo 1925435 1927403 := bstep (se 1 (by rfl) ⟨1445552, by rfl⟩ : syracuseStep 1927403 = 2891105) B2891105
theorem B7417973 : Blo 1925435 7417973 := bbase (se 5 (by rfl) ⟨347717, by rfl⟩ : syracuseStep 7417973 = 695435) (by norm_num)
theorem B4945315 : Blo 1925435 4945315 := bstep (se 1 (by rfl) ⟨3708986, by rfl⟩ : syracuseStep 4945315 = 7417973) B7417973
theorem B6593753 : Blo 1925435 6593753 := bstep (se 2 (by rfl) ⟨2472657, by rfl⟩ : syracuseStep 6593753 = 4945315) B4945315
theorem B4395835 : Blo 1925435 4395835 := bstep (se 1 (by rfl) ⟨3296876, by rfl⟩ : syracuseStep 4395835 = 6593753) B6593753
theorem B23444453 : Blo 1925435 23444453 := bstep (se 4 (by rfl) ⟨2197917, by rfl⟩ : syracuseStep 23444453 = 4395835) B4395835
theorem B15629635 : Blo 1925435 15629635 := bstep (se 1 (by rfl) ⟨11722226, by rfl⟩ : syracuseStep 15629635 = 23444453) B23444453
theorem B20839513 : Blo 1925435 20839513 := bstep (se 2 (by rfl) ⟨7814817, by rfl⟩ : syracuseStep 20839513 = 15629635) B15629635
theorem B27786017 : Blo 1925435 27786017 := bstep (se 2 (by rfl) ⟨10419756, by rfl⟩ : syracuseStep 27786017 = 20839513) B20839513
theorem B18524011 : Blo 1925435 18524011 := bstep (se 1 (by rfl) ⟨13893008, by rfl⟩ : syracuseStep 18524011 = 27786017) B27786017
theorem B24698681 : Blo 1925435 24698681 := bstep (se 2 (by rfl) ⟨9262005, by rfl⟩ : syracuseStep 24698681 = 18524011) B18524011
theorem B16465787 : Blo 1925435 16465787 := bstep (se 1 (by rfl) ⟨12349340, by rfl⟩ : syracuseStep 16465787 = 24698681) B24698681
theorem B10977191 : Blo 1925435 10977191 := bstep (se 1 (by rfl) ⟨8232893, by rfl⟩ : syracuseStep 10977191 = 16465787) B16465787
theorem B7318127 : Blo 1925435 7318127 := bstep (se 1 (by rfl) ⟨5488595, by rfl⟩ : syracuseStep 7318127 = 10977191) B10977191
theorem B4878751 : Blo 1925435 4878751 := bstep (se 1 (by rfl) ⟨3659063, by rfl⟩ : syracuseStep 4878751 = 7318127) B7318127
theorem B6505001 : Blo 1925435 6505001 := bstep (se 2 (by rfl) ⟨2439375, by rfl⟩ : syracuseStep 6505001 = 4878751) B4878751
theorem B4336667 : Blo 1925435 4336667 := bstep (se 1 (by rfl) ⟨3252500, by rfl⟩ : syracuseStep 4336667 = 6505001) B6505001
theorem B2891111 : Blo 1925435 2891111 := bstep (se 1 (by rfl) ⟨2168333, by rfl⟩ : syracuseStep 2891111 = 4336667) B4336667
theorem B1927407 : Blo 1925435 1927407 := bstep (se 1 (by rfl) ⟨1445555, by rfl⟩ : syracuseStep 1927407 = 2891111) B2891111
theorem B2891117 : Blo 1925435 2891117 := bbase (se 3 (by rfl) ⟨542084, by rfl⟩ : syracuseStep 2891117 = 1084169) (by norm_num)
theorem B1927411 : Blo 1925435 1927411 := bstep (se 1 (by rfl) ⟨1445558, by rfl⟩ : syracuseStep 1927411 = 2891117) B2891117
theorem B4336685 : Blo 1925435 4336685 := bbase (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) (by norm_num)
theorem B2891123 : Blo 1925435 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B1927415 : Blo 1925435 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B4945349 : Blo 1925435 4945349 := bbase (se 4 (by rfl) ⟨463626, by rfl⟩ : syracuseStep 4945349 = 927253) (by norm_num)
theorem B3296899 : Blo 1925435 3296899 := bstep (se 1 (by rfl) ⟨2472674, by rfl⟩ : syracuseStep 3296899 = 4945349) B4945349
theorem B4395865 : Blo 1925435 4395865 := bstep (se 2 (by rfl) ⟨1648449, by rfl⟩ : syracuseStep 4395865 = 3296899) B3296899
theorem B5861153 : Blo 1925435 5861153 := bstep (se 2 (by rfl) ⟨2197932, by rfl⟩ : syracuseStep 5861153 = 4395865) B4395865
theorem B3907435 : Blo 1925435 3907435 := bstep (se 1 (by rfl) ⟨2930576, by rfl⟩ : syracuseStep 3907435 = 5861153) B5861153
theorem B5209913 : Blo 1925435 5209913 := bstep (se 2 (by rfl) ⟨1953717, by rfl⟩ : syracuseStep 5209913 = 3907435) B3907435
theorem B3473275 : Blo 1925435 3473275 := bstep (se 1 (by rfl) ⟨2604956, by rfl⟩ : syracuseStep 3473275 = 5209913) B5209913
theorem B4631033 : Blo 1925435 4631033 := bstep (se 2 (by rfl) ⟨1736637, by rfl⟩ : syracuseStep 4631033 = 3473275) B3473275
theorem B12349421 : Blo 1925435 12349421 := bstep (se 3 (by rfl) ⟨2315516, by rfl⟩ : syracuseStep 12349421 = 4631033) B4631033
theorem B8232947 : Blo 1925435 8232947 := bstep (se 1 (by rfl) ⟨6174710, by rfl⟩ : syracuseStep 8232947 = 12349421) B12349421
theorem B5488631 : Blo 1925435 5488631 := bstep (se 1 (by rfl) ⟨4116473, by rfl⟩ : syracuseStep 5488631 = 8232947) B8232947
theorem B3659087 : Blo 1925435 3659087 := bstep (se 1 (by rfl) ⟨2744315, by rfl⟩ : syracuseStep 3659087 = 5488631) B5488631
theorem B2439391 : Blo 1925435 2439391 := bstep (se 1 (by rfl) ⟨1829543, by rfl⟩ : syracuseStep 2439391 = 3659087) B3659087
theorem B3252521 : Blo 1925435 3252521 := bstep (se 2 (by rfl) ⟨1219695, by rfl⟩ : syracuseStep 3252521 = 2439391) B2439391
theorem B2168347 : Blo 1925435 2168347 := bstep (se 1 (by rfl) ⟨1626260, by rfl⟩ : syracuseStep 2168347 = 3252521) B3252521
theorem B2891129 : Blo 1925435 2891129 := bstep (se 2 (by rfl) ⟨1084173, by rfl⟩ : syracuseStep 2891129 = 2168347) B2168347
theorem B1927419 : Blo 1925435 1927419 := bstep (se 1 (by rfl) ⟨1445564, by rfl⟩ : syracuseStep 1927419 = 2891129) B2891129
theorem B1953721 : Blo 1925435 1953721 := bbase (se 2 (by rfl) ⟨732645, by rfl⟩ : syracuseStep 1953721 = 1465291) (by norm_num)
theorem B2604961 : Blo 1925435 2604961 := bstep (se 2 (by rfl) ⟨976860, by rfl⟩ : syracuseStep 2604961 = 1953721) B1953721
theorem B3473281 : Blo 1925435 3473281 := bstep (se 2 (by rfl) ⟨1302480, by rfl⟩ : syracuseStep 3473281 = 2604961) B2604961
theorem B4631041 : Blo 1925435 4631041 := bstep (se 2 (by rfl) ⟨1736640, by rfl⟩ : syracuseStep 4631041 = 3473281) B3473281
theorem B6174721 : Blo 1925435 6174721 := bstep (se 2 (by rfl) ⟨2315520, by rfl⟩ : syracuseStep 6174721 = 4631041) B4631041
theorem B32931845 : Blo 1925435 32931845 := bstep (se 4 (by rfl) ⟨3087360, by rfl⟩ : syracuseStep 32931845 = 6174721) B6174721
theorem B21954563 : Blo 1925435 21954563 := bstep (se 1 (by rfl) ⟨16465922, by rfl⟩ : syracuseStep 21954563 = 32931845) B32931845
theorem B14636375 : Blo 1925435 14636375 := bstep (se 1 (by rfl) ⟨10977281, by rfl⟩ : syracuseStep 14636375 = 21954563) B21954563
theorem B9757583 : Blo 1925435 9757583 := bstep (se 1 (by rfl) ⟨7318187, by rfl⟩ : syracuseStep 9757583 = 14636375) B14636375
theorem B6505055 : Blo 1925435 6505055 := bstep (se 1 (by rfl) ⟨4878791, by rfl⟩ : syracuseStep 6505055 = 9757583) B9757583
theorem B4336703 : Blo 1925435 4336703 := bstep (se 1 (by rfl) ⟨3252527, by rfl⟩ : syracuseStep 4336703 = 6505055) B6505055
theorem B2891135 : Blo 1925435 2891135 := bstep (se 1 (by rfl) ⟨2168351, by rfl⟩ : syracuseStep 2891135 = 4336703) B4336703
theorem B1927423 : Blo 1925435 1927423 := bstep (se 1 (by rfl) ⟨1445567, by rfl⟩ : syracuseStep 1927423 = 2891135) B2891135
theorem B2891141 : Blo 1925435 2891141 := bbase (se 4 (by rfl) ⟨271044, by rfl⟩ : syracuseStep 2891141 = 542089) (by norm_num)
theorem B1927427 : Blo 1925435 1927427 := bstep (se 1 (by rfl) ⟨1445570, by rfl⟩ : syracuseStep 1927427 = 2891141) B2891141
theorem B3252541 : Blo 1925435 3252541 := bbase (se 3 (by rfl) ⟨609851, by rfl⟩ : syracuseStep 3252541 = 1219703) (by norm_num)
theorem B4336721 : Blo 1925435 4336721 := bstep (se 2 (by rfl) ⟨1626270, by rfl⟩ : syracuseStep 4336721 = 3252541) B3252541
theorem B2891147 : Blo 1925435 2891147 := bstep (se 1 (by rfl) ⟨2168360, by rfl⟩ : syracuseStep 2891147 = 4336721) B4336721
theorem B1927431 : Blo 1925435 1927431 := bstep (se 1 (by rfl) ⟨1445573, by rfl⟩ : syracuseStep 1927431 = 2891147) B2891147
theorem B2168365 : Blo 1925435 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B2891153 : Blo 1925435 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B1927435 : Blo 1925435 1927435 := bstep (se 1 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 1927435 = 2891153) B2891153
theorem C0 (j : ℕ) (h1 : 481358 ≤ j) (h2 : j ≤ 481858) : Blo 1925435 (4 * j + 3) := by
  interval_cases j
  · exact B1925435
  · exact B1925439
  · exact B1925443
  · exact B1925447
  · exact B1925451
  · exact B1925455
  · exact B1925459
  · exact B1925463
  · exact B1925467
  · exact B1925471
  · exact B1925475
  · exact B1925479
  · exact B1925483
  · exact B1925487
  · exact B1925491
  · exact B1925495
  · exact B1925499
  · exact B1925503
  · exact B1925507
  · exact B1925511
  · exact B1925515
  · exact B1925519
  · exact B1925523
  · exact B1925527
  · exact B1925531
  · exact B1925535
  · exact B1925539
  · exact B1925543
  · exact B1925547
  · exact B1925551
  · exact B1925555
  · exact B1925559
  · exact B1925563
  · exact B1925567
  · exact B1925571
  · exact B1925575
  · exact B1925579
  · exact B1925583
  · exact B1925587
  · exact B1925591
  · exact B1925595
  · exact B1925599
  · exact B1925603
  · exact B1925607
  · exact B1925611
  · exact B1925615
  · exact B1925619
  · exact B1925623
  · exact B1925627
  · exact B1925631
  · exact B1925635
  · exact B1925639
  · exact B1925643
  · exact B1925647
  · exact B1925651
  · exact B1925655
  · exact B1925659
  · exact B1925663
  · exact B1925667
  · exact B1925671
  · exact B1925675
  · exact B1925679
  · exact B1925683
  · exact B1925687
  · exact B1925691
  · exact B1925695
  · exact B1925699
  · exact B1925703
  · exact B1925707
  · exact B1925711
  · exact B1925715
  · exact B1925719
  · exact B1925723
  · exact B1925727
  · exact B1925731
  · exact B1925735
  · exact B1925739
  · exact B1925743
  · exact B1925747
  · exact B1925751
  · exact B1925755
  · exact B1925759
  · exact B1925763
  · exact B1925767
  · exact B1925771
  · exact B1925775
  · exact B1925779
  · exact B1925783
  · exact B1925787
  · exact B1925791
  · exact B1925795
  · exact B1925799
  · exact B1925803
  · exact B1925807
  · exact B1925811
  · exact B1925815
  · exact B1925819
  · exact B1925823
  · exact B1925827
  · exact B1925831
  · exact B1925835
  · exact B1925839
  · exact B1925843
  · exact B1925847
  · exact B1925851
  · exact B1925855
  · exact B1925859
  · exact B1925863
  · exact B1925867
  · exact B1925871
  · exact B1925875
  · exact B1925879
  · exact B1925883
  · exact B1925887
  · exact B1925891
  · exact B1925895
  · exact B1925899
  · exact B1925903
  · exact B1925907
  · exact B1925911
  · exact B1925915
  · exact B1925919
  · exact B1925923
  · exact B1925927
  · exact B1925931
  · exact B1925935
  · exact B1925939
  · exact B1925943
  · exact B1925947
  · exact B1925951
  · exact B1925955
  · exact B1925959
  · exact B1925963
  · exact B1925967
  · exact B1925971
  · exact B1925975
  · exact B1925979
  · exact B1925983
  · exact B1925987
  · exact B1925991
  · exact B1925995
  · exact B1925999
  · exact B1926003
  · exact B1926007
  · exact B1926011
  · exact B1926015
  · exact B1926019
  · exact B1926023
  · exact B1926027
  · exact B1926031
  · exact B1926035
  · exact B1926039
  · exact B1926043
  · exact B1926047
  · exact B1926051
  · exact B1926055
  · exact B1926059
  · exact B1926063
  · exact B1926067
  · exact B1926071
  · exact B1926075
  · exact B1926079
  · exact B1926083
  · exact B1926087
  · exact B1926091
  · exact B1926095
  · exact B1926099
  · exact B1926103
  · exact B1926107
  · exact B1926111
  · exact B1926115
  · exact B1926119
  · exact B1926123
  · exact B1926127
  · exact B1926131
  · exact B1926135
  · exact B1926139
  · exact B1926143
  · exact B1926147
  · exact B1926151
  · exact B1926155
  · exact B1926159
  · exact B1926163
  · exact B1926167
  · exact B1926171
  · exact B1926175
  · exact B1926179
  · exact B1926183
  · exact B1926187
  · exact B1926191
  · exact B1926195
  · exact B1926199
  · exact B1926203
  · exact B1926207
  · exact B1926211
  · exact B1926215
  · exact B1926219
  · exact B1926223
  · exact B1926227
  · exact B1926231
  · exact B1926235
  · exact B1926239
  · exact B1926243
  · exact B1926247
  · exact B1926251
  · exact B1926255
  · exact B1926259
  · exact B1926263
  · exact B1926267
  · exact B1926271
  · exact B1926275
  · exact B1926279
  · exact B1926283
  · exact B1926287
  · exact B1926291
  · exact B1926295
  · exact B1926299
  · exact B1926303
  · exact B1926307
  · exact B1926311
  · exact B1926315
  · exact B1926319
  · exact B1926323
  · exact B1926327
  · exact B1926331
  · exact B1926335
  · exact B1926339
  · exact B1926343
  · exact B1926347
  · exact B1926351
  · exact B1926355
  · exact B1926359
  · exact B1926363
  · exact B1926367
  · exact B1926371
  · exact B1926375
  · exact B1926379
  · exact B1926383
  · exact B1926387
  · exact B1926391
  · exact B1926395
  · exact B1926399
  · exact B1926403
  · exact B1926407
  · exact B1926411
  · exact B1926415
  · exact B1926419
  · exact B1926423
  · exact B1926427
  · exact B1926431
  · exact B1926435
  · exact B1926439
  · exact B1926443
  · exact B1926447
  · exact B1926451
  · exact B1926455
  · exact B1926459
  · exact B1926463
  · exact B1926467
  · exact B1926471
  · exact B1926475
  · exact B1926479
  · exact B1926483
  · exact B1926487
  · exact B1926491
  · exact B1926495
  · exact B1926499
  · exact B1926503
  · exact B1926507
  · exact B1926511
  · exact B1926515
  · exact B1926519
  · exact B1926523
  · exact B1926527
  · exact B1926531
  · exact B1926535
  · exact B1926539
  · exact B1926543
  · exact B1926547
  · exact B1926551
  · exact B1926555
  · exact B1926559
  · exact B1926563
  · exact B1926567
  · exact B1926571
  · exact B1926575
  · exact B1926579
  · exact B1926583
  · exact B1926587
  · exact B1926591
  · exact B1926595
  · exact B1926599
  · exact B1926603
  · exact B1926607
  · exact B1926611
  · exact B1926615
  · exact B1926619
  · exact B1926623
  · exact B1926627
  · exact B1926631
  · exact B1926635
  · exact B1926639
  · exact B1926643
  · exact B1926647
  · exact B1926651
  · exact B1926655
  · exact B1926659
  · exact B1926663
  · exact B1926667
  · exact B1926671
  · exact B1926675
  · exact B1926679
  · exact B1926683
  · exact B1926687
  · exact B1926691
  · exact B1926695
  · exact B1926699
  · exact B1926703
  · exact B1926707
  · exact B1926711
  · exact B1926715
  · exact B1926719
  · exact B1926723
  · exact B1926727
  · exact B1926731
  · exact B1926735
  · exact B1926739
  · exact B1926743
  · exact B1926747
  · exact B1926751
  · exact B1926755
  · exact B1926759
  · exact B1926763
  · exact B1926767
  · exact B1926771
  · exact B1926775
  · exact B1926779
  · exact B1926783
  · exact B1926787
  · exact B1926791
  · exact B1926795
  · exact B1926799
  · exact B1926803
  · exact B1926807
  · exact B1926811
  · exact B1926815
  · exact B1926819
  · exact B1926823
  · exact B1926827
  · exact B1926831
  · exact B1926835
  · exact B1926839
  · exact B1926843
  · exact B1926847
  · exact B1926851
  · exact B1926855
  · exact B1926859
  · exact B1926863
  · exact B1926867
  · exact B1926871
  · exact B1926875
  · exact B1926879
  · exact B1926883
  · exact B1926887
  · exact B1926891
  · exact B1926895
  · exact B1926899
  · exact B1926903
  · exact B1926907
  · exact B1926911
  · exact B1926915
  · exact B1926919
  · exact B1926923
  · exact B1926927
  · exact B1926931
  · exact B1926935
  · exact B1926939
  · exact B1926943
  · exact B1926947
  · exact B1926951
  · exact B1926955
  · exact B1926959
  · exact B1926963
  · exact B1926967
  · exact B1926971
  · exact B1926975
  · exact B1926979
  · exact B1926983
  · exact B1926987
  · exact B1926991
  · exact B1926995
  · exact B1926999
  · exact B1927003
  · exact B1927007
  · exact B1927011
  · exact B1927015
  · exact B1927019
  · exact B1927023
  · exact B1927027
  · exact B1927031
  · exact B1927035
  · exact B1927039
  · exact B1927043
  · exact B1927047
  · exact B1927051
  · exact B1927055
  · exact B1927059
  · exact B1927063
  · exact B1927067
  · exact B1927071
  · exact B1927075
  · exact B1927079
  · exact B1927083
  · exact B1927087
  · exact B1927091
  · exact B1927095
  · exact B1927099
  · exact B1927103
  · exact B1927107
  · exact B1927111
  · exact B1927115
  · exact B1927119
  · exact B1927123
  · exact B1927127
  · exact B1927131
  · exact B1927135
  · exact B1927139
  · exact B1927143
  · exact B1927147
  · exact B1927151
  · exact B1927155
  · exact B1927159
  · exact B1927163
  · exact B1927167
  · exact B1927171
  · exact B1927175
  · exact B1927179
  · exact B1927183
  · exact B1927187
  · exact B1927191
  · exact B1927195
  · exact B1927199
  · exact B1927203
  · exact B1927207
  · exact B1927211
  · exact B1927215
  · exact B1927219
  · exact B1927223
  · exact B1927227
  · exact B1927231
  · exact B1927235
  · exact B1927239
  · exact B1927243
  · exact B1927247
  · exact B1927251
  · exact B1927255
  · exact B1927259
  · exact B1927263
  · exact B1927267
  · exact B1927271
  · exact B1927275
  · exact B1927279
  · exact B1927283
  · exact B1927287
  · exact B1927291
  · exact B1927295
  · exact B1927299
  · exact B1927303
  · exact B1927307
  · exact B1927311
  · exact B1927315
  · exact B1927319
  · exact B1927323
  · exact B1927327
  · exact B1927331
  · exact B1927335
  · exact B1927339
  · exact B1927343
  · exact B1927347
  · exact B1927351
  · exact B1927355
  · exact B1927359
  · exact B1927363
  · exact B1927367
  · exact B1927371
  · exact B1927375
  · exact B1927379
  · exact B1927383
  · exact B1927387
  · exact B1927391
  · exact B1927395
  · exact B1927399
  · exact B1927403
  · exact B1927407
  · exact B1927411
  · exact B1927415
  · exact B1927419
  · exact B1927423
  · exact B1927427
  · exact B1927431
  · exact B1927435
theorem solution (m : ℕ) (hlo : 1925435 ≤ m) (hhi : m ≤ 1927435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 481358 ≤ j := by omega
    have hj2 : j ≤ 481858 := by omega
    have hb : Blo 1925435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
